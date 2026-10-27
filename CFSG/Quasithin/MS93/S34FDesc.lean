module

public import CFSG.Quasithin.MS93.S34FPar
public import CFSG.Quasithin.MS93.S34EDesc2
public import CFSG.Quasithin.MS93.S34ECrit

public section

namespace CFSG.Quasithin.MS93.S34F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

@[expose] def S34FDesc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    (IsSL3UEven M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4UEven M T L ∧ ¬ IsSp4Full M T L) →
    (∃ θ : MulAut ↥T, ∃ x : ↥T, (x : G) ∈ pCoreOf 2 M ∧ ((θ x : ↥T) : G) ∉ L ⊔ pCoreOf 2 M) →
    (∀ μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ (baseA _) →
      geo (puAmalgam h.le) (baseA _) μ 1 = baseB _ →
      ¬ Qv (puAmalgam h.le) (baseB _) ≤
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) :
          Set (puAmalgam h.le).Universal)) →
    (∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    (∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ L)).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

section Reduction

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_mulAut_not_mem (h : PUHyp M T L) (hmin : PUMin M T L)
    (hc : (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L)) :
    ∃ θ : MulAut ↥T, ∃ x : ↥T, (x : G) ∈ pCoreOf 2 M ∧ ((θ x : ↥T) : G) ∉ L ⊔ pCoreOf 2 M := by
  by_contra hall
  push Not at hall
  apply S34E.not_good_of_nonfull h hmin hc
  exact inf_le_right.trans
    (S34D.pCoreOf_le_charCore_of_mem h fun θ x hx => ⟨(θ x).2, hall θ x hx⟩)

theorem not_le_centralizer_critR (h : PUHyp M T L)
    (hc : (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L))
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo (puAmalgam h.le) (baseA _) μ 1 = baseB _) :
    ¬ Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) :
        Set (puAmalgam h.le).Universal) := by
  intro hR
  rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
  · exact hF (S34E.sl3Full_of_critR_central h hU hcμ hμβ hR)
  · exact hF (S34E.sp4Full_of_critR_central h hU hcμ hμβ hR)

theorem even_of_nonfull (h : PUHyp M T L)
    (hc : (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L)) :
    (IsSL3UEven M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4UEven M T L ∧ ¬ IsSp4Full M T L) := by
  rcases hc with ⟨hU, hF⟩ | ⟨hU, hF⟩
  · exact Or.inl ⟨isSL3UEven_of_nonfull h hU hF, hF⟩
  · exact Or.inr ⟨isSp4UEven_of_nonfull h hU hF, hF⟩

end Reduction

theorem descNP2_of_fDesc (hF : S34FDesc) : S34E.S34EDescNP2 := by
  intro G _ _ M T L h hmin hb hc hflat hinf
  exact hF G M T L h hmin hb (even_of_nonfull h hc) (exists_mulAut_not_mem h hmin hc)
    (fun μ hcμ hμβ => not_le_centralizer_critR h hc hcμ hμβ) hflat hinf

theorem endNL_of_fDesc (hred : PUReduce) (hF : S34FDesc) : S34D.S34DEndNL :=
  S34E.endNL_of_descNP2 hred (descNP2_of_fDesc hF)

end CFSG.Quasithin.MS93.S34F
