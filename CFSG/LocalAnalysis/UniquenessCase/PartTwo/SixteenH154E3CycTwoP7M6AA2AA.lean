module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_normSylow_selfCent
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
      Mbar D.M V₀ V hV ≤ Subgroup.normalizer (P : Set (MulAut (Vtil V₀ V hV))) ∧
      ¬ 7 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      IsPGroup 7 P ∧
      IsElemAbelianOfRank 7 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤ P := by
  obtain ⟨helem, hcent, hrel⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA_pCore_structure D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm
      hbad
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  exact ⟨pCoreOf 7 (Mbar D.M V₀ V hV),
    CFSG.LieType.BorelTits.pCoreOf_le 7 _,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 7 _,
    hrel,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 7 _,
    helem, hcent⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
