module

public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem fixV_iSup {ι : Sort*} (X : ι → Subgroup (MulAut V)) : fixV (⨆ i, X i) = ⨅ i, fixV (X i) := by
  ext v
  simp only [mem_fixV, Subgroup.mem_iInf]
  refine ⟨fun h i x hx => h x (Subgroup.mem_iSup_of_mem i hx), fun h x hx => ?_⟩
  refine Subgroup.iSup_induction X (C := fun x => x v = v) hx (fun i x hx => h i x hx) ?_ ?_
  · exact rfl
  · intro a b ha hb
    rw [MulAut.mul_apply, hb, ha]

theorem B2_17_aut [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {ι : Type*} [Fintype ι]
    (X : ι → Subgroup (MulAut V)) {L : Subgroup (MulAut V)} (hL : L ≤ ⨆ i, X i)
    (h : ∑ i, rkIdx (fixV (X i)) ≤ rkIdx (fixV L)) :
    fixV L = fixV (⨆ i, X i) ∧ rkIdx (fixV L) = ∑ i, rkIdx (fixV (X i)) := by
  set I := ⨆ i, X i with hI
  have hplus : rkIdx (fixV I) ≤ ∑ i, rkIdx (fixV (X i)) := by
    have h1 : (⨅ i, fixV (X i)).index ≤ ∏ i, (fixV (X i)).index := Subgroup.index_iInf_le _
    rw [← fixV_iSup, B1.index_eq_two_pow hV] at h1
    simp only [B1.index_eq_two_pow hV, Finset.prod_pow_eq_pow_sum] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hstar : fixV I ≤ fixV L := B1.fixV_le_fixV hL
  have hstarstar : rkIdx (fixV L) ≤ rkIdx (fixV I) := rkIdx_anti hstar
  have h2 : rkIdx (fixV L) = rkIdx (fixV I) := by omega
  refine ⟨?_, by omega⟩
  symm
  refine eq_of_le_of_rk_le hV hstar ?_
  have h3 := rk_add_rkIdx (fixV L)
  have h4 := rk_add_rkIdx (fixV I)
  omega

theorem B2_17 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {G : Type*} [Group G] (ρ : G →* MulAut V)
    {ι : Type*} [Fintype ι] (X : ι → Subgroup G) {L : Subgroup G} (hL : L ≤ ⨆ i, X i)
    (h : ∑ i, rkIdx (fixV ((X i).map ρ)) ≤ rkIdx (fixV (L.map ρ))) :
    fixV (L.map ρ) = fixV ((⨆ i, X i).map ρ) ∧
      rkIdx (fixV (L.map ρ)) = ∑ i, rkIdx (fixV ((X i).map ρ)) := by
  have hmap : (⨆ i, X i).map ρ = ⨆ i, (X i).map ρ := Subgroup.map_iSup _ _
  rw [hmap]
  exact B2_17_aut hV (fun i => (X i).map ρ) (hmap ▸ Subgroup.map_mono hL) h

end CFSG.Quasithin
