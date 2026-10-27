module

public import CFSG.Quasithin.Vol2.Ch11SecB24Three

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ : Subgroup G}

theorem rParam_le24 (hI : In24) (h : Hyp24 T L I n V₁ V₂) :
    E3.rParam (fsuV T I) ≤ (2 * n : ℕ) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨g, hAT, hnc⟩ := exists_conj_le_T (isPGroup_fsuV h.hyp) h.wclos
  apply not_le_normalizer24 hI h hAT hnc
  refine (hI.facts.r2Gen G L (fsuV T I) ⊤ T V₁ V₂ n (h.flag hI) _ (le_ROf hI h hAT)).trans
    (iSup₂_le fun B hB => ?_)
  have hC := centralizer_le_normalizer_of_lt (V := fsuV T I) (B := B) (g := g) hB.1
    (lt_of_le_of_lt (by exact_mod_cast hB.2) hlt)
  exact inf_le_right.trans hC

theorem stmt11_2_4_of (hRP : FactRootPoint) (hPT : FactPointTrans) (hR2 : FactR2)
    (hR2L : FactR2Line) (hR2G : FactR2Gen) (hL2P : FactL2Point) (hS4R : FactSp4Root)
    (hS4N : FactSp4NoTransv) (hNF : NatFacts) (h331 : Stmt3_3_1)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3)
    (h1113 : Stmt11_1_3) (h1122 : Stmt11_2_2) : Stmt11_2_4 := by
  intro G _ _ T L I n V₁ V₂ hyp hV₁ hV₂ hab hW hSL3
  have hI : In24 :=
    ⟨⟨hRP, hPT, hR2, hR2L, hR2G, hL2P, hS4R, hS4N⟩, hNF, h331, h3228, h1102, h1103, h1113,
      h1122⟩
  have h : Hyp24 T L I n V₁ V₂ := ⟨hyp, hV₁, hV₂, hab, hW, hSL3⟩
  exact ⟨wClos_le_ROf hI h, fun g hAT hnc => not_le_normalizer24 hI h hAT hnc,
    rParam_le24 hI h⟩

end CFSG.Quasithin.Vol2.Ch11.SecB
