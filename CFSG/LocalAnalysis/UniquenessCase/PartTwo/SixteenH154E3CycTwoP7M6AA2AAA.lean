module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA2AAA2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCOdd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6AA2AAA_pCore_structure
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
    IsElemAbelianOfRank 7 3 ↥(pCoreOf 7 (Mbar D.M V₀ V hV)) ∧
      (Subgroup.centralizer (pCoreOf 7 (Mbar D.M V₀ V hV) : Set (MulAut (Vtil V₀ V hV))) ⊓
        Mbar D.M V₀ V hV ≤ pCoreOf 7 (Mbar D.M V₀ V hV)) ∧
      ¬ 7 ∣ (pCoreOf 7 (Mbar D.M V₀ V hV)).relIndex (Mbar D.M V₀ V hV) := by
  obtain ⟨P, hPle, hPnorm, hPrank, hPrel, hPmax, hPcent⟩ :=
    s16h_e3_CycTwoP7M6AA2AAA2_exists_normal_sylow D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm
      hbad
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPp : IsPGroup 7 ↥P := s16c13bc_isPGroup_of_elemAbelianOfRank (by norm_num) hPrank
  have hcore_le : pCoreOf 7 (Mbar D.M V₀ V hV) ≤ P :=
    hPmax _ (CFSG.LieType.BorelTits.pCoreOf_le 7 (Mbar D.M V₀ V hV))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 7 (Mbar D.M V₀ V hV))
  have hP_le_core : P ≤ pCoreOf 7 (Mbar D.M V₀ V hV) :=
    CFSG.LieType.BorelTits.le_pCoreOf (r := 7) hPle hPnorm hPp
  have heq : pCoreOf 7 (Mbar D.M V₀ V hV) = P := le_antisymm hcore_le hP_le_core
  refine ⟨?_, ?_, ?_⟩
  · rw [heq]; exact hPrank
  · rw [heq]; exact hPcent
  · rw [heq]; exact hPrel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
