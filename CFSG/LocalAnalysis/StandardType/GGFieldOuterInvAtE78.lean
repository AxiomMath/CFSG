module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvAdjoint

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Open (IsElemAbelian)

theorem ggFieldOuterInvModelAt_E78
    (t : StatedLieTag) (ht : t = .E7 ∨ t = .E8) : GGFieldOuterInvModelAt t := by
  intro n f hadm hrank hF
  obtain ⟨-, hf, -⟩ := hadm
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  rcases ht with rfl | rfl
  · exact ⟨adjointGroup .E7 (GaloisField 2 f), inferInstance,
      CFSG.LieType.Steinberg.Isogeny.e7Isogeny (GaloisField 2 f),
      CFSG.LieType.Steinberg.Isogeny.e7Isogeny_surjective _,
      CFSG.LieType.Steinberg.CentralExt.FieldFour.e7Isogeny_ker_eq_center,
      ggFieldOuterInvModel_adjointGroup (Or.inl rfl) hf (GaloisField 2 f) hK
        (fun h => absurd h (by simp))⟩
  · refine ⟨(ggU .E8 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_,
      ggFieldOuterInvModel_adjointGroup (Or.inr (Or.inl rfl)) hf (GaloisField 2 f) hK
        (fun h => absurd h (by simp))⟩
    rw [MonoidHom.ker_id]
    exact (center_adjointGroup_eq_bot (τ := .E8) (K := GaloisField 2 f)).symm

theorem ggFieldOuterInvAt_E78
    (t : StatedLieTag) (ht : t = .E7 ∨ t = .E8) : GGFieldOuterInvAt t :=
  ggFieldOuterInvAt_of_model (by rcases ht with h | h <;> simp [h])
    (ggFieldOuterInvModelAt_E78 t ht) fun hF4 => by
      rcases ht with h | h <;> (rw [h] at hF4; cases hF4)

end CFSG.StandardType
