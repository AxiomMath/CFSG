module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2AAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6AA2AAA2AA_exists_normal_sylow_core
    (D : Data G) (S : s16h_Std D) (hr3 : CFSG.Open.evenRank G = 3) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (hV : IsElemAbelian 2 V) (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V hV L)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V hV L) p)
    (hχ : ¬ ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n)
    (hs2 : s15 D.M V₀ V hV L = 2)
    (hres : ∀ q ∈ D.sig, q = p ∨
      (p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6 ∧ q = 3))
    (hp7 : p = 7) (hm : rk ↥(wTil V₀ V hV L) = 6)
    (hbad : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧
      (P.subgroupOf (Mbar D.M V₀ V hV)).Normal ∧
      IsElemAbelianOfRank 7 3 ↥P ∧
      ¬ 7 ∣ P.relIndex (Mbar D.M V₀ V hV) := by
  obtain ⟨P, hPM, hPn, hPrank, hPrel⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA2AAA_exists_normal_sylow_aux D S hr3 hσ hV h hc hp hLp hχ hs2
      hres hp7 hm hbad
  exact ⟨P, hPM, (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).2 hPn, hPrank, hPrel⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
