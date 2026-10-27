module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2B

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6AA2AAA2_exists_normal_sylow
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
      ¬ 7 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      (∀ Q : Subgroup (MulAut (Vtil V₀ V hV)), Q ≤ Mbar D.M V₀ V hV →
        IsPGroup 7 ↥Q → Q ≤ P) ∧
      Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓
        Mbar D.M V₀ V hV ≤ P := by
  obtain ⟨P, hPM, hnorm, hrk, hrel, hmax⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA2A_exists_normal_sylow_structure D S hr3 hσ hV h hc hp hLp hχ
      hs2 hres hp7 hm hbad
  exact ⟨P, hPM, hnorm, hrk, hrel, hmax,
    s16h_e3_CycTwoP7M6AA2AAA2B_centralizer_le_of_normal_sylow D S hr3 hσ hV h hc hp hLp hχ
      hs2 hres hp7 hm hbad P hPM hnorm hrk hmax⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
