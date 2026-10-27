module

public import CFSG.Monster.M.IndexNine
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.OrdinaryProofs.MonsterCarrierSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem sporadicThreePermuting_M_of_co1
    {Δ : Type*} [Group Δ] (eΔ : Δ ≃* CFSG.Blueprint.NativeSporadic.Co1)
    (hΔ : IndexNinePackage Δ)
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal]
    (hS : CFSG.Quasithin.IsSylowIn 2 S ⊤) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.M) :
    ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
      ¬ IsCyclic ↥E ∧ CFSG.LocalAnalysis.UniquenessCase.UC22.Permutes E S := by
  have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M) :=
    CFSG.AGLEmbedding.Norton.OrdinaryProofs.carrier_M_simple
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple
    (T := CFSG.Blueprint.NativeSporadic.Carrier .M) (MulEquiv.refl _)
  exact exists_permutes_of_indexNinePackage (CFSG.Monster.M.gmat_indexNinePackage_of_co1 eΔ hΔ)
    (e.trans ε) hS

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
