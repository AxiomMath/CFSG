module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AABBA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP3M4AA2AAC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP3M4AA2AA_pCore_structure
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
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    IsElemAbelianOfRank 3 3 ↥(pCoreOf 3 (Mbar D.M V₀ V hV)) ∧
      (Subgroup.centralizer (pCoreOf 3 (Mbar D.M V₀ V hV) : Set (MulAut (Vtil V₀ V hV))) ⊓
        Mbar D.M V₀ V hV ≤ pCoreOf 3 (Mbar D.M V₀ V hV)) ∧
      ¬ 3 ∣ (pCoreOf 3 (Mbar D.M V₀ V hV)).relIndex (Mbar D.M V₀ V hV) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hσ3 : D.sig = {3} :=
    (s16h_e3_CycTwoP3M4AA2AAA_sigma_eq_three D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW).1
  obtain ⟨P, hPle, hPn, hPrel, hPgrp, hPabel⟩ :=
    s16h_e3_CycTwoP3M4AA2AABBA_normal_sylow_elemAbelian D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm
        hW
  have hcent := s16h_e3_CycTwoP3M4AA2AAC_selfCentralizing D S hr3 hσ hV h hc hp hLp hχ hs2 hres
    hp3 hm hW P hPle hPn hPrel hPgrp
  have hle : P ≤ pCoreOf 3 (Mbar D.M V₀ V hV) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 3 hPle hPn hPgrp
  have hge : pCoreOf 3 (Mbar D.M V₀ V hV) ≤ P :=
    CFSG.GroupTheory.pCoreOf_le_of_not_dvd_relIndex hPle hPn hPrel
  have hEq : pCoreOf 3 (Mbar D.M V₀ V hV) = P := le_antisymm hge hle
  refine ⟨?_, ?_, ?_⟩
  · rw [hEq]; exact hPabel
  · rw [hEq]; exact hcent
  · rw [hEq]; exact hPrel

theorem s16h_e3_CycTwoP3M4A_normSylow_selfCent
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
    (hp3 : p = 3) (hm : rk ↥(wTil V₀ V hV L) = 4)
    (hW : ¬ ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G))) :
    ∃ P : Subgroup (MulAut (Vtil V₀ V hV)),
      P ≤ Mbar D.M V₀ V hV ∧
      Mbar D.M V₀ V hV ≤ Subgroup.normalizer (P : Set (MulAut (Vtil V₀ V hV))) ∧
      ¬ 3 ∣ P.relIndex (Mbar D.M V₀ V hV) ∧
      IsPGroup 3 P ∧
      IsElemAbelianOfRank 3 3 ↥P ∧
      Subgroup.centralizer (P : Set (MulAut (Vtil V₀ V hV))) ⊓ Mbar D.M V₀ V hV ≤ P := by
  obtain ⟨helem, hcent, hrel⟩ :=
    s16h_e3_CycTwoP3M4AA2AA_pCore_structure D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp3 hm hW
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨pCoreOf 3 (Mbar D.M V₀ V hV),
    CFSG.LieType.BorelTits.pCoreOf_le 3 _,
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 _,
    hrel,
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 _,
    helem, hcent⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo