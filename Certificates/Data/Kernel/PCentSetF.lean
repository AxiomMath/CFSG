module

public import Certificates.Data.Kernel.PCentSet
public import Certificates.Data.Kernel.BitT

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)
open CFSG.KC.BitT

@[expose] noncomputable def imgMTF (w g m t : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => cond (bitT m i) (Nat.lor acc (Nat.shiftLeft (nat_lit 1) (pg w (mask w) g i)))
      acc) t

theorem imgMTF_eq (w g m t : Nat) : imgMTF w g m t = imgMT w g m t := by
  unfold imgMTF imgMT
  simp only [bitT_eq]

@[expose] noncomputable def setOrbKF (n w : Nat) (G : Nat → Nat) (ngen m : Nat) (R : List Rec) :
    Bool :=
  Nat.blt m (Nat.pow (nat_lit 2) n) && orbRecK (fun k y => imgMTF w (G k) y n) ngen m R

theorem setOrbK_eq_F (n w : Nat) (G : Nat → Nat) (ngen m : Nat) (R : List Rec) :
    setOrbK n w G ngen m R = setOrbKF n w G ngen m R := by
  unfold setOrbK setOrbKF imgM
  simp only [imgMTF_eq]

end CFSG.KC.PCent

end
