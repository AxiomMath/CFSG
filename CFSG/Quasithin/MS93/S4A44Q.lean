module

public import CFSG.Quasithin.MS93.S4A44U

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section Q

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem commutator_conjCl_le_of_le_dloc (hfull : IsSL3Full M T L)
    (hb : 4 < critDist (puAmalgam h.le)) {lam α : Vtx (puAmalgam h.le)}
    (hlam : IsMVtx _ lam) (hd : (puAmalgam h.le).treeGraph.dist lam α = 2)
    {Y : Subgroup (puAmalgam h.le).Universal} (hY : Y ≤ Qv _ lam)
    (hWY : ⁅conjCl (stab _ lam) (ZM (puAmalgam h.le) α), Y⁆ ≤ Dloc h.le L lam) :
    ⁅conjCl (stab _ lam) (ZM (puAmalgam h.le) α), Y⁆ ≤
      ⁅ZM (puAmalgam h.le) α, Qv _ lam⁆ ⊓ Dloc h.le L lam := by
  have hα : IsMVtx (puAmalgam h.le) α := by
    have := (even_dist_iff (puAmalgam h.le) lam α).mp (by rw [hd]; decide)
    exact this.mp hlam
  set ρ := geo (puAmalgam h.le) lam α 1 with hρdef
  have hlamρ : (puAmalgam h.le).treeGraph.Adj lam ρ := by
    have := adj_geo (puAmalgam h.le) (u := lam) (w := α) (i := 0) (by omega)
    rwa [geo_zero] at this
  have hρα : (puAmalgam h.le).treeGraph.Adj ρ α := by
    have := adj_geo (puAmalgam h.le) (u := lam) (w := α) (i := 1) (by omega)
    rwa [geo_of_le _ (by omega : (puAmalgam h.le).treeGraph.dist lam α ≤ 1 + 1)] at this
  set W := conjCl (stab (puAmalgam h.le) lam) (ZM (puAmalgam h.le) α) with hWdef
  set N := ⁅ZM (puAmalgam h.le) α, Qv _ lam⁆ ⊓ Dloc h.le L lam with hNdef
  have hab := vv_comm_eq_bot h hb hlam
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hab
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ lam := by
    rw [← zv_of_isMVtx _ hα]; exact zv_le_vv h hd.le
  have hWV : W ≤ Vv (puAmalgam h.le) lam :=
    conjCl_le_of_le_normalizer hZV (stab_le_normalizer_vv h lam)
  have hQZ : Qv (puAmalgam h.le) lam ≤ Subgroup.normalizer (ZM (puAmalgam h.le) α : Set _) :=
    (qv_le_stab_of_dist_le_two _ h.hyp20 hlam hd.le).trans (stab_le_normalizer_zm _ α)
  have hNV : N ≤ Vv (puAmalgam h.le) lam :=
    inf_le_left.trans ((Subgroup.le_normalizer_iff_commutator_le_left.mp hQZ).trans hZV)
  have hLD := dloc_le_centralizer_ltil h hlam
  rw [Subgroup.commutator_le]
  intro w hw y hy
  let S : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {w | w ∈ W ∧ ⁅w, y⁆ ∈ N}
      mul_mem' := by
        rintro a b ⟨ha, haN⟩ ⟨hb', hbN⟩
        refine ⟨W.mul_mem ha hb', ?_⟩
        have e : ⁅a * b, y⁆ = a * ⁅b, y⁆ * a⁻¹ * ⁅a, y⁆ := by
          simp only [commutatorElement_def]; group
        have hc : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
          have hcomm := Subgroup.mem_centralizer_iff.mp (hab (hWV ha)) _ (hNV hbN)
          rw [← hcomm, mul_inv_cancel_right]
        rw [e, hc]
        exact N.mul_mem hbN haN
      one_mem' := ⟨W.one_mem, by simp [N.one_mem]⟩
      inv_mem' := by
        rintro a ⟨ha, haN⟩
        refine ⟨W.inv_mem ha, ?_⟩
        have e : ⁅a⁻¹, y⁆ = a⁻¹ * (⁅a, y⁆)⁻¹ * a := by
          simp only [commutatorElement_def]; group
        have hc : a⁻¹ * (⁅a, y⁆)⁻¹ * a = (⁅a, y⁆)⁻¹ := by
          have := Subgroup.mem_centralizer_iff.mp (hab (hWV (W.inv_mem ha))) _
            (hNV (N.inv_mem haN))
          rw [← this, inv_mul_cancel_right]
        rw [e, hc]
        exact N.inv_mem haN }
  have hWS : W ≤ S := by
    refine iSup₂_le fun g hg => ?_
    have hnorm : Qv (puAmalgam h.le) lam ≤
        Subgroup.normalizer (Ltil h.le L lam : Set (puAmalgam h.le).Universal) :=
      (qv_le_stab _ lam).trans (stab_le_normalizer_ltil h lam)
    have hg' : g ∈ ((Ltil h.le L lam ⊔ Qv _ lam : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
      rw [← stab_eq_ltil_sup_qv h hfull hlam]
      exact hg
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hnorm] at hg'
    obtain ⟨l, hl, k, hk, rfl⟩ := hg'
    have hkZ : (ZM (puAmalgam h.le) α).map (MulAut.conj k).toMonoidHom = ZM _ α :=
      map_conj_eq_of_mem_normalizer (hQZ hk)
    rintro _ ⟨z, hz, rfl⟩
    have hzk : k * z * k⁻¹ ∈ ZM (puAmalgam h.le) α := by
      rw [← hkZ]; exact ⟨z, hz, rfl⟩
    have hls : l ∈ stab (puAmalgam h.le) lam := ltil_le_stab h lam hl
    set z' := k * z * k⁻¹ with hz'
    have hmem : (MulAut.conj (l * k)).toMonoidHom z = l * z' * l⁻¹ := by
      simp [hz', mul_assoc]
    rw [hmem]
    have hwW : l * z' * l⁻¹ ∈ W :=
      map_conj_le_conjCl hls ⟨z', hzk, rfl⟩
    refine ⟨hwW, ?_⟩
    have hyl : l⁻¹ * y * l ∈ Qv (puAmalgam h.le) lam := by
      have := (stab_le_normalizer_qv _ lam ((stab _ lam).inv_mem hls) y).mp (hY hy)
      simpa using this
    have e1 : ⁅l * z' * l⁻¹, y⁆ = l * ⁅z', l⁻¹ * y * l⁆ * l⁻¹ := by
      simp only [commutatorElement_def]; group
    have hcD : ⁅z', l⁻¹ * y * l⁆ ∈ Dloc h.le L lam := by
      have h1 : ⁅l * z' * l⁻¹, y⁆ ∈ Dloc h.le L lam :=
        hWY (Subgroup.commutator_mem_commutator hwW hy)
      have h2 : l⁻¹ * ⁅l * z' * l⁻¹, y⁆ * l ∈ Dloc h.le L lam := by
        have := (stab_le_normalizer_dloc h lam ((stab _ lam).inv_mem hls) _).mp h1
        simpa using this
      rw [e1] at h2
      simpa [mul_assoc] using h2
    have hcN : ⁅z', l⁻¹ * y * l⁆ ∈ N :=
      ⟨Subgroup.commutator_mem_commutator hzk hyl, hcD⟩
    rw [e1, Subgroup.mem_centralizer_iff.mp (hLD hcD) l hl, mul_inv_cancel_right]
    exact hcN
  exact (hWS hw).2

end Q

end CFSG.Quasithin.MS93.S4A
