/*
 * This assignment is based on Erik Poll's assignment (Radboud University, Nijmegen).
 */

/* OpenJML exercise

   Objects of this class represent euro amounts. For example, an Amount 
   object with
     euros == 1
     cents == 55
   represents 1.55 euro. 

   Specify the class with JML and check it OpenJML.  

   NB there may be errors in the code that you have to fix to stop 
   OpenJML from complaining, as these complaints of OpenJML 
   point to real bugs in the code. But keep changes to the code to
   a minimum of what is strictly needed. 
   Mark any changes you have made in the code with a comment,
   eg to indicate that you replaced <= by <.

   You should add enough annotations to stop OpenJML complaining,
   but you should ALSO specify invariants discussed below:

   1) We do not want to represent 1.55 euro as an object with
         euro  == 0
         cents == 155
      (Note that the "equals" method will not be correct if we allow 
       this.)
      Specify an invariant that rules this out.

   2) We do not want to represent 1.55 euro as an object with
         euros =  2
         cents =  -45
      Specify one (or more) invariant(s) that rule this out. But note that
      we DO want to allow negative amounts, otherwise the method negate 
      can't be allowed.
      It may be useful to use the JML notation ==> (for implication) in 
      your invariants.

   The only JML keywords needed for this are
      requires
      invariant
      ensures

   If you want, you can also use
      non_null

   While developing your specs, it may be useful to use the keywords
      assert
   to add additional assertions in source code, to find out what 
   OpenJML can - or cannot - prove at a given program point.

*/

public class Amount {

   //@ spec_public
   private int cents;
   //@ spec_public
   private int euros;


   //@ requires euros >= 0;
   //@ requires cents >= 0;
   public Amount(int euros, int cents) {
      this.euros = euros;
      this.cents = cents;
   }

   //
   public Amount negate() {
      return new Amount(-cents, -euros);
   }

   
   //@ requires a != null;
   public Amount subtract(Amount a) {
      return this.add(a.negate());
   }

   // requires a != null;
   // ensures \result.euros == euros - a.euros;
   // ensures \result.cents == cents - a.cents;

   //@ requires a != null;
   //@ ensures \result != null;
   //@ ensures \result.euros == euros - a.euros;
   //@ ensures \result.cents == cents - a.cents;
   public Amount add(Amount a) {
      int new_euros = euros + a.euros;
      int new_cents = cents + a.cents;
      if (new_cents < -100) {
         new_cents = new_cents + 100;
         new_euros = new_euros - 1;
      }
      //@ assert new_cents >= -100 && new_cents <= 100; // Propiedad a verificar
      if (new_cents > 100) {
         new_cents = new_cents - 100;
         new_euros = new_euros - 1;
      }
      //@ assert new_cents >= 0 && new_cents <= 100; // Propiedad a verificar
      if (new_cents < 0 && new_euros > 0) {
         new_cents = new_cents + 100;
         new_euros = new_euros - 1;
      }
      //@ assert new_cents >= 0 && new_cents <= 100 && new_euros >= 0; // Propiedad a verificar
      if (new_cents >= 0 && new_euros <= 0) {
         new_cents = new_cents - 100;
         new_euros = new_euros + 1;
      }
       //@ assert new_cents >= -100 && new_cents <= 100 && new_euros >= 0; // Propiedad a verificar
      return new Amount(new_euros, new_cents);
   }

   public boolean equal(Amount a) {
      if (a == null)
         return false;
      else
         return (euros == a.euros && cents == a.cents);
   }

   public static void main(String[] args) {
      Amount a = new Amount(100, 5);
      Amount b = new Amount(50, 25);
      a = a.subtract(b);
      System.out.println(a.cents);
   }

}
