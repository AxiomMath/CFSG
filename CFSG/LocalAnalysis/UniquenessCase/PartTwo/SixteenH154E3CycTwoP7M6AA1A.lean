module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3CycTwoP7M6AA1AA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.L37Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_pCoreOf_elemAbelian_of_lBar_le
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
      UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)))
    (hLle : lBar V₀ V hV L ≤ pCoreOf 7 (Mbar D.M V₀ V hV)) :
    IsElemAbelianOfRank 7 3 ↥(pCoreOf 7 (Mbar D.M V₀ V hV)) := by
  obtain ⟨P, hPH, hPn, hPrank, hPmax⟩ :=
    s16h_e3_CycTwoP7M6A_exists_normal_sylow_seven D S hr3 hσ hV h hc hp hLp hχ hs2 hres hp7 hm
      hbad hLle
  have hPp : IsPGroup 7 ↥P := by
    obtain ⟨e⟩ := hPrank
    exact (ZModModule.isPGroup_multiplicative (n := 7) (G := Fin 3 → ZMod 7)).of_equiv e.symm
  have hNp : IsPGroup 7 ↥(P.subgroupOf (Mbar D.M V₀ V hV)) :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  have hNmax : ∀ M : Subgroup ↥(Mbar D.M V₀ V hV), M.Normal → IsPGroup 7 M →
      M ≤ P.subgroupOf (Mbar D.M V₀ V hV) := by
    intro M _ hMp x hx
    have hMle : M.map (Mbar D.M V₀ V hV).subtype ≤ P :=
      hPmax (M.map (Mbar D.M V₀ V hV).subtype) (Subgroup.map_subtype_le M) (hMp.map _)
    exact hMle (Subgroup.mem_map_of_mem (Mbar D.M V₀ V hV).subtype hx)
  have hcore : CFSG.pCore 7 ↥(Mbar D.M V₀ V hV) = P.subgroupOf (Mbar D.M V₀ V hV) := by
    letI : (P.subgroupOf (Mbar D.M V₀ V hV)).Normal := hPn
    exact CFSG.OddStandard.SmallF3.HarrisU33.pCore_eq_of_normal _ hNp hNmax
  have heq : pCoreOf 7 (Mbar D.M V₀ V hV) = P := by
    unfold pCoreOf
    rw [hcore]
    exact Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hPH)
  rw [heq]
  exact hPrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
