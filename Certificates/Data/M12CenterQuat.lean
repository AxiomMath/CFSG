module

public import Certificates.Data.ExitTwoM12

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.E3S3MC

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.M12

set_option compiler.extract_closed false

@[expose] def six {M : Type*} [Mul M] (u v : M) : List M :=
  [u, u * u * u, v, v * v * v, u * v, u * v * (u * v) * (u * v)]

@[expose] def fix12 (p : Equiv.Perm (Fin 12)) : ℕ :=
  (Finset.univ.filter fun i : Fin 12 => p i = i).card

@[expose] def wOK (r y : Equiv.Perm (Fin 12)) (k : ℕ) (w : Equiv.Perm (Fin 12)) : Bool :=
  decide (w * w = r) && !decide (w * y = 1) && decide (w * y * (w * y) = 1) &&
    fix12 (w * y) == k

@[expose] def pairOK (r y u v : Equiv.Perm (Fin 12)) : Bool :=
  if u * u = r ∧ v * v = r ∧ u * v ≠ v * u then
    (six u v).any (wOK r y 0) && (six u v).any (wOK r y 4)
  else true

@[expose] def quatOK (r y : Equiv.Perm (Fin 12)) (Q : List (Equiv.Perm (Fin 12))) : Bool :=
  decide (y * y = r) && Q.all (fun x => decide (x * y = y * x)) &&
    Q.all fun u => Q.all fun v => pairOK r y u v

@[expose] def chkQuat0 (_ : Unit := ()) : Bool :=
  quatOK m12Rep1 ((quatL1 ()).getD 1 1) (quatL0 ())

@[expose] def chkQuat1 (_ : Unit := ()) : Bool :=
  quatOK m12Rep1 ((quatL0 ()).getD 1 1) (quatL1 ())

@[expose] def chkFix2 (_ : Unit := ()) : Bool := fix12 m12Rep2 == 0

end CFSG.ClassicalInvolution.Q3.TL4.E3S3MC
