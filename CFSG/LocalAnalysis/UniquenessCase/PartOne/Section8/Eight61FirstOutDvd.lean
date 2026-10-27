module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List863

import CFSG.HardMathSupport.Curtis.Coordinator.ToralThreeReduce
import CFSG.LocalAnalysis.AGLEmbedding.BlockFactReductionsII
import CFSG.Quasithin.Background.A318POutSpor
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterLie
import CFSG.HardMathSupport.Dickson.Sec6.I923Aux.Spor
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ2
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterRu
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterJ4
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.OuterSpor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def ExceptionalOuterCapable (K : Type) [Group K] : Prop :=
  (∃ p f : ℕ, LieModel K .G2 0 p f) ∨ (∃ p f : ℕ, LieModel K .trialityD4 0 p f) ∨
    (∃ f : ℕ, LieModel K .twistedF4 0 2 f)

theorem not_three_dvd_card_outer_of_list857Clause2
    {K : Type} [Group K] [Finite K] (hK : List857Clause2 K) : ¬ 3 ∣ Nat.card (Outer K) := by
  rcases hK with hA6 | hA7 | hM22
  · obtain ⟨hqs, -, hAlt⟩ := hA6
    obtain ⟨e⟩ := hAlt
    have : Group.IsPerfect K := hqs.1
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := hqs.2.1
    exact CFSG.HardMathSupport.Curtis.Coordinator.not_three_dvd_card_outer_of_center_alt e
  · obtain ⟨hqs, -, hAlt⟩ := hA7
    obtain ⟨e⟩ := hAlt
    have : Group.IsPerfect K := hqs.1
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := hqs.2.1
    exact CFSG.HardMathSupport.Curtis.Coordinator.not_three_dvd_card_outer_of_center_alt e
  · obtain ⟨hqs, -, hSpor⟩ := hM22
    obtain ⟨e⟩ := hSpor
    have : Group.IsPerfect K := hqs.1
    intro hdiv
    exact CFSG.Quasithin.A318P.not_dvd_outer_M22 e Nat.prime_three (by norm_num)
      (dvd_trans hdiv (CFSG.AGLEmbedding.card_outer_dvd_card_outer_centerQuotient K))

theorem not_three_dvd_card_outer_of_list857
    {K : Type} [Group K] [Finite K]
    (hK : List857 K) (h1 : ¬ List857Clause1 K) (hE : ¬ ExceptionalOuterCapable K) :
    ¬ 3 ∣ Nat.card (Outer K) := by
  rw [list857_iff_clauses] at hK
  rcases hK with hcl1 | hcl2 | hcl3
  · exact absurd hcl1 h1
  · exact not_three_dvd_card_outer_of_list857Clause2 hcl2
  · rcases hcl3 with hPSL3 | hG2 | hPSU3 | hD4 | hF4 | hTits | hJ2 | hHe | hRu | hJ4 | hM12 |
      hM24
    · exact not_three_dvd_card_outer_of_lieModel_psl3 hPSL3
    · exact absurd (Or.inl hG2) hE
    · exact not_three_dvd_card_outer_of_lieModel_psu3 hPSU3
    · exact absurd (Or.inr (Or.inl hD4)) hE
    · exact absurd (Or.inr (Or.inr hF4)) hE
    · have ht : .Tits ∈ CFSG.Blueprint.reeTitsTags := by decide
      have hRee : CFSG.Blueprint.ReeTitsModel K .Tits 2 1 :=
        (CFSG.Blueprint.LieModel.reeTitsModel hTits ht).2
      exact CFSG.HardMathSupport.Dickson.Sec6.I923.not_three_dvd_card_outer_tits hRee
    · exact not_three_dvd_card_outer_of_isSpor_J2 hJ2
    · obtain ⟨e⟩ := hHe
      rw [CFSG.SignalizerFunctorTheorem.CatalogBridge.card_outer_eq_of_mulEquiv e]
      change ¬ 3 ∣ Nat.card (Outer CFSG.Blueprint.NativeSporadic.He)
      have : Finite CFSG.Blueprint.NativeSporadic.He := inferInstance
      have : Finite (MulAut CFSG.Blueprint.NativeSporadic.He) :=
        Finite.of_injective
          (fun α : MulAut CFSG.Blueprint.NativeSporadic.He =>
            (α : CFSG.Blueprint.NativeSporadic.He → CFSG.Blueprint.NativeSporadic.He))
          DFunLike.coe_injective
      have : Finite (Outer CFSG.Blueprint.NativeSporadic.He) :=
        Finite.of_surjective (QuotientGroup.mk' (inner CFSG.Blueprint.NativeSporadic.He))
          QuotientGroup.mk_surjective
      have : Nonempty (Outer CFSG.Blueprint.NativeSporadic.He) :=
        ⟨QuotientGroup.mk' (inner CFSG.Blueprint.NativeSporadic.He) 1⟩
      intro hdiv
      have h2 : Nat.card (Outer CFSG.Blueprint.NativeSporadic.He) ≤ 2 :=
        CFSG.Sporadic.Schreier.AT_He_Schreier.1
      have h3le : 3 ≤ Nat.card (Outer CFSG.Blueprint.NativeSporadic.He) :=
        Nat.le_of_dvd Nat.card_pos hdiv
      omega
    · exact not_three_dvd_card_outer_of_isSpor_Ru hRu
    · exact not_three_dvd_card_outer_of_isSpor_J4 hJ4
    · exact not_three_dvd_card_outer_of_isSpor_m12 hM12
    · exact not_three_dvd_card_outer_of_isSpor_m24 hM24

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
