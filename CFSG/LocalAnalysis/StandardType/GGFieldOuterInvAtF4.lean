module

public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvAdjoint
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvF4Four
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvF4Odd

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.Open (IsElemAbelian)

theorem ggFieldOuterInvModelAt_F4
    : GGFieldOuterInvModelAt .F4 := by
  intro n f hadm hrank hF
  obtain ⟨-, hf, -⟩ := hadm
  have hfe : Even f := by
    rcases Nat.even_or_odd f with h | h
    · exact h
    · exact absurd ⟨rfl, h⟩ hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨(ggU .F4 n f).K, inferInstance, MonoidHom.id _, Function.surjective_id, ?_, ?_⟩
  · rw [MonoidHom.ker_id]
    exact (center_adjointGroup_eq_bot (τ := .F4) (K := GaloisField 2 f)).symm
  · by_cases h2 : f = 2
    · subst h2
      exact ggFieldOuterInvModel_F4_four
    · refine ggFieldOuterInvModel_adjointGroup (Or.inr (Or.inr rfl)) hf (GaloisField 2 f) hK
        fun _ => ⟨hfe, fun h4 => h2 ?_⟩
      rw [hK] at h4
      exact Nat.pow_right_injective (le_refl 2) (by simpa using h4)

theorem ggFieldOuterInvAt_F4
    : GGFieldOuterInvAt .F4 :=
  ggFieldOuterInvAt_of_model (Or.inr (Or.inl rfl)) ggFieldOuterInvModelAt_F4
    fun _ => ggFieldOuterInvF4Odd_holds

end CFSG.StandardType
