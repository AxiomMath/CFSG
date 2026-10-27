module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

section Vocabulary

variable {W : Type*} [CommGroup W]

@[expose] def IsDirSumOver {ι : Type*} (S : Set ι) (U : ι → Subgroup W) : Prop :=
  iSupIndep (fun X : S => U X) ∧ (⨆ X : S, U X) = ⊤

@[expose] def IsNaturalO4Plus (R : Subgroup (MulAut W)) (e : ℕ) : Prop :=
  ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ e ∧
    (FFModel.nat (CFSG.PGLModel.orthogonalPlus 2 K)).Realizes R (commV R) ⊥

end Vocabulary

@[expose] def W4Lem12_8 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y : Subgroup (MulAut W),
      (∀ P : Subgroup (MulAut W), P ≤ Y → (P.subgroupOf Y).Normal → IsPGroup 2 P → P = ⊥) →
      IsBasicModule Y →
      ∀ L : Subgroup (MulAut W), IsComponentOf L Y →
      ∀ H : Subgroup (MulAut W), H = ⨆ X ∈ conjSet L Y, X →
        dMinDeg ↥L ≤ E3.mParam Y ∨
        (IsDirSumOver (conjSet L Y) (fun X => commV (autQuot X (fixV H))) ∧
          ∃ I ∈ irrSet L,
            (E3.mParam (autSub (autQuot Y (fixV H)) (I.map (QuotientGroup.mk' (fixV H)))) : ℚ) *
                ((rk ↥(commV (autQuot L (fixV H))) : ℚ) /
                  (rk ↥(I.map (QuotientGroup.mk' (fixV H))) : ℚ)) ≤
              E3.mParam Y) ∨
        ∃ (R : Subgroup (MulAut W)) (e : ℕ), R ≤ Y ∧ IsDirSumOver (conjSet R Y) commV ∧
          CFSG.Open.IsSubnormal L R ∧ IsNaturalO4Plus R e ∧ E3.mParam Y = e ∧
          dMinDeg ↥L = 2 * e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
