module

public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySuzukiNormalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42TypeListAux

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique

namespace B42Vacuous

variable {V : Type} [CommGroup V] [Finite V]

theorem offender_data {G L A : Subgroup (MulAut V)} (hHyp : B4Hyp G L)
    (hA : IsFFStarOffender G A) :
    Nontrivial V ∧ Group.IsPerfect ↥L ∧
      (∀ U : Subgroup V, (∀ g ∈ L, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      A ≤ Subgroup.normalizer (L : Set (MulAut V)) ∧
      Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  obtain ⟨-, hLeq, hq, hirr⟩ := hHyp
  refine ⟨?_, hq.1, Bridge.TypeList.irr_of_isIrrSec hirr, ?_, ?_⟩
  · obtain ⟨x, -, hx⟩ := IsConcreteLE.exists_of_lt hirr.1
    exact ⟨⟨x, 1, fun h1 => hx (by rw [h1]; exact Subgroup.one_mem _)⟩⟩
  · rw [hLeq]
    exact hA.1.trans (le_normalizer_quasithinGenFitting G)
  · have h := hA.2.2.2 ⊥ bot_le
    rwa [B1.card_bot_mul_card_fixV] at h

end B42Vacuous

theorem asB42U3Even_holds
    : AsB42U3Even := by
  intro V _ _ hV G L hHyp hT A hA
  obtain ⟨f, hf, hmodel⟩ := hT
  obtain ⟨hnt, hperf, hirr, hAN, hoff⟩ := B42Vacuous.offender_data hHyp hA
  have hlt := Setup.X5.evenUnitaryThreeNoOffender f hf V
    (fun w => by rw [← pow_two]; exact hV w) hnt L A hperf hirr hmodel hA.2.1 hA.2.2.1 hAN
  exact lt_irrefl _ (hoff.trans_lt hlt)

theorem asB42Sz_holds
    : AsB42Sz := by
  intro V _ _ hV G L hHyp hT A hA
  obtain ⟨f, -, -, -, a, ha, K, _, _, hfa, hK, ⟨α⟩⟩ := hT
  obtain ⟨hnt, hperf, hirr, hAN, hoff⟩ := B42Vacuous.offender_data hHyp hA
  subst hfa
  have hlt := (Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK V
    (fun w => by rw [← pow_two]; exact hV w) L hperf hirr α).2.2.2.2 A hA.2.1 hA.2.2.1 hAN
  exact lt_irrefl _ (hoff.trans_lt hlt)

end CFSG.Quasithin
