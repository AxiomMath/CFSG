module

public import CFSG.Sporadic.Co2Schreier.IndexNineData

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.Co2I301
  CFSG.Sporadic.Co2Schreier.IndexNineData

structure NineSub where
  carrier : Finset (Fin 63)
  deriving DecidableEq, Fintype, Inhabited

instance : Coe NineSub (Finset (Fin 63)) := ⟨NineSub.carrier⟩

instance nineSubMulAction : MulAction (Equiv.Perm (Fin 63)) NineSub where
  smul π S := ⟨S.carrier.image π⟩
  one_smul S := by
    cases S with
    | mk c =>
      show (⟨c.image (1 : Equiv.Perm (Fin 63))⟩ : NineSub) = ⟨c⟩
      rw [show (1 : Equiv.Perm (Fin 63)) = ⇑(Equiv.refl (Fin 63)) from rfl]
      simp
  mul_smul π σ S := by
    cases S with
    | mk c =>
      show (⟨c.image (π * σ)⟩ : NineSub) = ⟨(c.image σ).image π⟩
      rw [Finset.image_image]
      rfl

@[expose] def nineEll : NineSub := ⟨{25, 43, 53}⟩

@[expose] def nineXPos : List ℕ :=
    [1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      0, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 0,
      0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0,
      1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0,
      1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
      0]

@[expose] def nineYPos : List ℕ :=
    [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0,
      0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0,
      0, 1, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 0, 1, 1, 0,
      1, 1, 0, 0, 0, 0, 0, 0]

@[expose] def nineOrbitWords : List (List ℕ) :=
  [
    [],
    [0],
    [1],
    [0, 0],
    [1, 0],
    [0, 1],
    [1, 1],
    [0, 0, 0],
    [1, 0, 0],
    [0, 1, 0],
    [1, 1, 0],
    [0, 0, 1],
    [1, 0, 1],
    [0, 1, 1],
    [1, 1, 1],
    [0, 0, 0, 0],
    [1, 0, 0, 0],
    [0, 1, 0, 0],
    [1, 1, 0, 0],
    [0, 0, 1, 0],
    [1, 0, 1, 0],
    [0, 1, 1, 0],
    [1, 1, 1, 0],
    [0, 0, 0, 1],
    [1, 0, 0, 1],
    [0, 1, 0, 1],
    [1, 1, 0, 1],
    [0, 0, 1, 1],
    [1, 0, 1, 1],
    [0, 1, 1, 1],
    [0, 0, 0, 0, 0],
    [1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0],
    [1, 1, 0, 0, 0],
    [0, 0, 1, 0, 0],
    [1, 0, 1, 0, 0],
    [0, 1, 1, 0, 0],
    [1, 1, 1, 0, 0],
    [1, 0, 0, 1, 0],
    [0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0],
    [0, 0, 1, 1, 0],
    [1, 0, 1, 1, 0],
    [0, 1, 1, 1, 0],
    [0, 0, 0, 0, 1],
    [1, 0, 0, 0, 1],
    [0, 1, 0, 0, 1],
    [1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1],
    [1, 0, 0, 1, 1],
    [0, 1, 0, 1, 1],
    [0, 0, 1, 1, 1],
    [0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 0, 0],
    [1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 0, 0],
    [1, 1, 1, 0, 0, 0],
    [1, 0, 0, 1, 0, 0],
    [0, 1, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0],
    [1, 0, 1, 1, 0, 0],
    [0, 1, 1, 1, 0, 0],
    [0, 1, 0, 0, 1, 0],
    [1, 1, 0, 0, 1, 0],
    [0, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 0],
    [0, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 1, 0],
    [0, 0, 0, 1, 1, 0],
    [1, 0, 0, 1, 1, 0],
    [0, 1, 0, 1, 1, 0],
    [1, 1, 0, 1, 1, 0],
    [0, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 1, 0],
    [0, 0, 0, 0, 0, 1],
    [1, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 1],
    [1, 1, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 1],
    [1, 0, 1, 0, 0, 1],
    [0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1],
    [0, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1],
    [0, 1, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1],
    [1, 1, 0, 0, 1, 1],
    [0, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 1],
    [0, 0, 0, 1, 1, 1],
    [0, 0, 1, 0, 0, 0, 0],
    [1, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0],
    [1, 1, 0, 1, 0, 0, 0],
    [0, 0, 1, 1, 0, 0, 0],
    [1, 0, 1, 1, 0, 0, 0],
    [0, 1, 1, 1, 0, 0, 0],
    [0, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 0, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 0],
    [0, 1, 1, 0, 1, 0, 0],
    [1, 1, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 1, 0, 0],
    [0, 1, 0, 1, 1, 0, 0],
    [0, 0, 1, 1, 1, 0, 0],
    [1, 0, 1, 1, 1, 0, 0],
    [0, 0, 1, 0, 0, 1, 0],
    [1, 0, 1, 0, 0, 1, 0],
    [0, 1, 1, 0, 0, 1, 0],
    [1, 1, 1, 0, 0, 1, 0],
    [0, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 0],
    [0, 0, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 1, 0],
    [0, 0, 0, 0, 1, 1, 0],
    [1, 0, 0, 0, 1, 1, 0],
    [0, 1, 0, 0, 1, 1, 0],
    [1, 1, 0, 0, 1, 1, 0],
    [0, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 1, 0],
    [1, 0, 0, 1, 1, 1, 0],
    [0, 1, 0, 1, 1, 1, 0],
    [1, 1, 0, 1, 1, 1, 0],
    [1, 0, 0, 0, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 1],
    [1, 1, 0, 0, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 1],
    [0, 1, 1, 0, 0, 0, 1],
    [1, 1, 1, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 1],
    [0, 1, 0, 1, 0, 0, 1],
    [1, 1, 0, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 0, 1],
    [0, 0, 0, 1, 1, 0, 1],
    [1, 0, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1],
    [1, 1, 0, 1, 1, 0, 1],
    [0, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 1, 1, 0, 1],
    [1, 0, 1, 0, 0, 1, 1],
    [0, 1, 1, 0, 0, 1, 1],
    [1, 1, 1, 0, 0, 1, 1],
    [0, 0, 0, 1, 0, 1, 1],
    [1, 0, 0, 1, 0, 1, 1],
    [0, 1, 0, 1, 0, 1, 1],
    [0, 0, 0, 0, 1, 1, 1],
    [1, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 0, 0, 0],
    [0, 1, 0, 1, 0, 0, 0, 0],
    [1, 1, 0, 1, 0, 0, 0, 0],
    [0, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0],
    [1, 1, 1, 0, 1, 0, 0, 0],
    [1, 0, 0, 1, 1, 0, 0, 0],
    [0, 1, 0, 1, 1, 0, 0, 0],
    [0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 1, 0, 0, 1, 0, 0],
    [0, 1, 1, 0, 0, 1, 0, 0],
    [0, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 0, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 1, 0, 0],
    [0, 1, 1, 1, 0, 1, 0, 0],
    [0, 1, 0, 0, 1, 1, 0, 0],
    [1, 0, 1, 0, 1, 1, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0],
    [1, 0, 0, 1, 1, 1, 0, 0],
    [0, 1, 0, 1, 1, 1, 0, 0],
    [0, 0, 0, 1, 0, 0, 1, 0],
    [0, 0, 1, 1, 0, 0, 1, 0],
    [1, 0, 1, 1, 0, 0, 1, 0],
    [0, 1, 1, 1, 0, 0, 1, 0],
    [0, 0, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 1, 0],
    [0, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 0, 1, 1, 0, 1, 0],
    [0, 0, 1, 1, 1, 0, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 0],
    [1, 1, 0, 0, 0, 1, 1, 0],
    [1, 0, 1, 0, 0, 1, 1, 0],
    [1, 1, 1, 0, 0, 1, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0],
    [0, 0, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 0, 0, 1, 1, 1, 0],
    [1, 1, 0, 0, 1, 1, 1, 0],
    [1, 0, 1, 0, 0, 0, 0, 1],
    [0, 1, 1, 0, 0, 0, 0, 1],
    [1, 1, 1, 0, 0, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 1],
    [0, 0, 1, 1, 0, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 0, 1],
    [1, 0, 0, 0, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 0, 0, 1],
    [1, 0, 1, 0, 1, 0, 0, 1],
    [0, 1, 1, 0, 1, 0, 0, 1],
    [1, 1, 1, 0, 1, 0, 0, 1],
    [0, 0, 0, 1, 0, 1, 0, 1],
    [1, 1, 0, 1, 0, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 1],
    [0, 0, 0, 0, 1, 1, 0, 1],
    [0, 1, 0, 0, 1, 1, 0, 1],
    [1, 1, 0, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1],
    [0, 0, 0, 1, 1, 1, 0, 1],
    [1, 1, 0, 1, 0, 0, 1, 1],
    [1, 0, 1, 1, 0, 0, 1, 1],
    [0, 1, 1, 1, 0, 0, 1, 1],
    [1, 1, 0, 0, 1, 0, 1, 1],
    [0, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 0, 0, 0, 1, 1, 1],
    [1, 1, 0, 0, 0, 1, 1, 1],
    [1, 0, 1, 0, 1, 0, 0, 0, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 0],
    [1, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 1, 1, 1, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 1, 1, 0, 0, 0],
    [1, 0, 0, 1, 0, 0, 1, 0, 0],
    [0, 0, 1, 1, 0, 0, 1, 0, 0],
    [1, 0, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 0, 1, 0, 1, 0, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 1, 1, 0, 1, 0, 0],
    [1, 0, 1, 1, 1, 0, 1, 0, 0],
    [0, 0, 1, 0, 0, 1, 1, 0, 0],
    [1, 0, 1, 0, 0, 1, 1, 0, 0],
    [0, 1, 0, 1, 0, 1, 1, 0, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 1, 1, 1, 0, 0],
    [1, 0, 1, 0, 1, 1, 1, 0, 0],
    [0, 0, 0, 0, 1, 0, 0, 1, 0],
    [1, 0, 0, 0, 1, 0, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 0, 0, 1, 0, 1, 0],
    [1, 0, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0, 0, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 1, 0, 1, 0],
    [1, 1, 1, 0, 0, 0, 1, 1, 0],
    [0, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 1, 1, 0, 1, 0, 1, 1, 0],
    [0, 0, 1, 1, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 0, 0, 0, 0, 1, 0, 0, 1],
    [1, 0, 0, 0, 0, 1, 0, 0, 1],
    [0, 1, 0, 0, 0, 1, 0, 0, 1],
    [1, 1, 0, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 1, 0, 1, 0, 0, 1],
    [0, 1, 0, 1, 0, 1, 0, 0, 1],
    [0, 0, 1, 1, 0, 1, 0, 0, 1],
    [0, 1, 1, 1, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 0, 1, 1, 0, 1, 0, 1],
    [0, 0, 0, 0, 0, 1, 1, 0, 1],
    [1, 0, 0, 0, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 0, 1, 1, 0, 1],
    [1, 0, 1, 1, 0, 1, 1, 0, 1],
    [0, 1, 1, 0, 1, 0, 0, 1, 1],
    [0, 1, 0, 1, 1, 0, 0, 1, 1],
    [1, 0, 1, 1, 1, 0, 0, 1, 1],
    [1, 1, 1, 0, 0, 1, 0, 1, 1],
    [0, 0, 0, 1, 0, 1, 0, 1, 1],
    [1, 0, 0, 1, 0, 1, 0, 1, 1],
    [0, 0, 1, 1, 0, 1, 0, 0, 0, 0],
    [1, 0, 1, 1, 0, 1, 0, 0, 0, 0],
    [0, 1, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 1, 0, 0, 1, 0, 1, 0, 0, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    [1, 1, 0, 1, 1, 0, 1, 0, 0, 0],
    [0, 0, 1, 1, 1, 0, 1, 0, 0, 0],
    [1, 0, 0, 0, 1, 1, 1, 0, 0, 0],
    [0, 0, 0, 1, 1, 0, 0, 1, 0, 0],
    [1, 1, 0, 1, 1, 1, 0, 1, 0, 0],
    [1, 1, 0, 1, 0, 0, 1, 1, 0, 0],
    [0, 0, 1, 0, 1, 0, 1, 1, 0, 0],
    [0, 1, 1, 0, 1, 0, 1, 1, 0, 0],
    [1, 0, 0, 0, 0, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 0, 1, 0, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 1, 1, 0, 0, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 0, 0, 1, 0, 0, 1],
    [0, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 0, 0, 0, 0, 0, 1, 1, 0, 1],
    [0, 1, 0, 0, 0, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 0, 1, 1],
    [1, 0, 0, 0, 1, 0, 1, 0, 1, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0],
    [1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0],
    [0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0]
  ]

@[expose] def ninePlug (i : ℕ) (p : Fin 63) : Fin 63 :=
  ⟨(witRec.wLocal.sixActionChain.origArrs[i]!)[p.val]! % 63, Nat.mod_lt _ (by norm_num)⟩

@[expose] def ninePt : List ℕ → Fin 63 → Fin 63
  | [], p => p
  | i :: w, p => ninePlug i (ninePt w p)

@[expose] def nineOrbSet (w : List ℕ) : NineSub := ⟨nineEll.carrier.image (ninePt w)⟩

@[expose] def nineSigned : List ℕ → List ℤ
  | [] => []
  | i :: w => ((i + 1 : ℕ) : ℤ) :: nineSigned w

theorem nineLetterValue_map {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : List G) (l : ℤ) :
    f (letterValue gs l) = letterValue (gs.map f) l := by
  have hget : (gs.map f).getD (l.natAbs - 1) 1 = f (gs.getD (l.natAbs - 1) 1) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    cases hh : gs[l.natAbs - 1]? with
    | none => simp [List.getElem?_map, hh]
    | some g => simp [List.getElem?_map, hh]
  rw [letterValue_def, letterValue_def, hget]
  by_cases h : 0 < l <;> simp [h, map_inv]

theorem nineWordValue_map {G H : Type*} [Group G] [Group H] (f : G →* H) (gs : List G)
    (w : List ℤ) : f (wordValue gs w) = wordValue (gs.map f) w := by
  rw [wordValue, wordValue, ← List.prod_hom, List.map_map]
  congr 1
  exact List.map_congr_left fun l _ => nineLetterValue_map f gs l

theorem letterValue_natSucc {G : Type*} [Group G] (gs : List G) (i : ℕ) :
    letterValue gs (((i + 1 : ℕ) : ℤ)) = gs.getD i 1 := by
  rw [letterValue_def, if_pos (by exact_mod_cast Nat.succ_pos i),
    show (((i + 1 : ℕ) : ℤ)).natAbs - 1 = i from by rw [Int.natAbs_natCast]; omega]

theorem wordValue_nineSigned {G : Type*} [Group G] (gs : List G) (w : List ℕ) :
    wordValue gs (nineSigned w) = (w.map fun i => gs.getD i 1).prod := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [nineSigned, wordValue_cons, ih, List.map_cons, List.prod_cons, letterValue_natSucc]

theorem ninePlug_eq (i : ℕ) (hi : i < 2) (p : Fin 63) :
    ninePlug i p = sixPi i p := by
  have hrep : Rep 63 witRec.wLocal.sixActionChain.origArrs[i]! (sixPi i) := rep_sixPi hi
  apply Fin.ext
  change (witRec.wLocal.sixActionChain.origArrs[i]!)[p.val]! % 63 = (sixPi i p).val
  rw [Nat.mod_eq_of_lt (hrep.lt p.2)]
  exact hrep p

theorem sixPi_getD {i : ℕ} (hi : i < 2) : [sixPi 0, sixPi 1].getD i 1 = sixPi i := by
  interval_cases i <;> rfl

theorem ninePt_eq {w : List ℕ} (hw : ∀ i ∈ w, i < 2) (p : Fin 63) :
    (w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod p = ninePt w p := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have hi := hw i List.mem_cons_self
    rw [List.map_cons, List.prod_cons, ninePt]
    show [sixPi 0, sixPi 1].getD i 1 ((w.map fun i => [sixPi 0, sixPi 1].getD i 1).prod p) =
      ninePlug i (ninePt w p)
    rw [ih hw', sixPi_getD hi, ninePlug_eq i hi]


theorem nineOrbitWords_length : nineOrbitWords.length = 315 := by decide +kernel

theorem nineOrbitWords_nodup : (nineOrbitWords.map nineOrbSet).Nodup := by decide +kernel

theorem nineXPos_lt : ∀ i ∈ nineXPos, i < 2 := by decide +kernel

theorem nineYPos_lt : ∀ i ∈ nineYPos, i < 2 := by decide +kernel

theorem nineOrbitWords_lt : ∀ w ∈ nineOrbitWords, ∀ i ∈ w, i < 2 := by decide +kernel

theorem nineX_pt_mem : ∀ p ∈ nineEll.carrier, ninePt nineXPos p ∈ nineEll.carrier := by
  decide +kernel

theorem nineY_pt_mem : ∀ p ∈ nineEll.carrier, ninePt nineYPos p ∈ nineEll.carrier := by
  decide +kernel

theorem nineX_pt_val (p : Fin 63) :
    ninePt nineXPos p =
      ((nineXPos.map fun i => [sixPi 0, sixPi 1].getD i 1).prod) p :=
  (ninePt_eq (w := nineXPos) nineXPos_lt p).symm

theorem nineY_pt_val (p : Fin 63) :
    ninePt nineYPos p =
      ((nineYPos.map fun i => [sixPi 0, sixPi 1].getD i 1).prod) p :=
  (ninePt_eq (w := nineYPos) nineYPos_lt p).symm


theorem nineLettersOK_append {j : ℕ} {a b : List ℤ} (ha : lettersOK j a = true)
    (hb : lettersOK j b = true) : lettersOK j (a ++ b) = true := by
  simp only [lettersOK, List.all_append, Bool.and_eq_true] at ha hb ⊢
  exact ⟨ha, hb⟩

theorem nineLettersOK_signed {w : List ℕ} (hw : ∀ i ∈ w, i < 2) :
    lettersOK 2 (nineSigned w) = true := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    have hi := hw i List.mem_cons_self
    have hw' : ∀ j ∈ w, j < 2 := fun j hj => hw j (List.mem_cons_of_mem _ hj)
    have htail := ih hw'
    simp only [nineSigned, lettersOK, List.all_cons, Bool.and_eq_true]
    refine ⟨?_, htail⟩
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq]
    refine ⟨?_, ?_⟩
    · omega
    · rw [Int.natAbs_natCast]
      omega


@[expose] def nineXSig : List ℤ := nineSigned nineXPos

@[expose] def nineYSig : List ℤ := nineSigned nineYPos

@[expose] def nineX2Sig : List ℤ := nineXSig ++ nineXSig

@[expose] def nineX3Sig : List ℤ := nineX2Sig ++ nineXSig

@[expose] def nineY3Sig : List ℤ := nineYSig ++ nineYSig ++ nineYSig

@[expose] def nineXYSig : List ℤ := nineXSig ++ nineYSig

@[expose] def nineYXSig : List ℤ := nineYSig ++ nineXSig


theorem nineXSigned_letters : lettersOK 2 (nineSigned nineXPos) = true := by decide +kernel

theorem nineYSigned_letters : lettersOK 2 (nineSigned nineYPos) = true := by decide +kernel

theorem nineX2Signed_letters : lettersOK 2 nineX2Sig = true := by
  rw [nineX2Sig]
  exact nineLettersOK_append nineXSigned_letters nineXSigned_letters

theorem nineX3Signed_letters : lettersOK 2 nineX3Sig = true := by
  rw [nineX3Sig]
  exact nineLettersOK_append nineX2Signed_letters nineXSigned_letters

theorem nineY3Signed_letters : lettersOK 2 nineY3Sig = true := by
  rw [nineY3Sig]
  exact nineLettersOK_append (nineLettersOK_append nineYSigned_letters nineYSigned_letters)
    nineYSigned_letters

theorem nineXYSigned_letters : lettersOK 2 nineXYSig = true := by
  rw [nineXYSig]
  exact nineLettersOK_append nineXSigned_letters nineYSigned_letters

theorem nineYXSigned_letters : lettersOK 2 nineYXSig = true := by
  rw [nineYXSig]
  exact nineLettersOK_append nineYSigned_letters nineXSigned_letters


end CFSG.Sporadic.Co2Schreier

end
