module

public import CFSG.Quasithin.MS93.S45IV

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem conjCl_map_conj_of_mem {Γ : Type*} [Group Γ] {H K : Subgroup Γ} {g : Γ} (hg : g ∈ H) :
    conjCl H (K.map (MulAut.conj g).toMonoidHom) = conjCl H K := by
  apply le_antisymm
  · refine iSup₂_le fun t ht => ?_
    rw [Subgroup.map_map]
    have e : (MulAut.conj t).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (t * g)).toMonoidHom := by
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup₂_of_le (f := fun s (_ : s ∈ H) => K.map (MulAut.conj s).toMonoidHom) (t * g)
      (mul_mem ht hg) le_rfl
  · refine iSup₂_le fun t ht => ?_
    have e : K.map (MulAut.conj t).toMonoidHom =
        (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj (t * g⁻¹)).toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x; simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact le_iSup₂_of_le (f := fun s (_ : s ∈ H) =>
      (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj s).toMonoidHom) (t * g⁻¹)
      (mul_mem ht (inv_mem hg)) le_rfl

theorem whv_smul {M T L : Subgroup G} (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (μ : Vtx (puAmalgam h.le)) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) δ) : whv h δ (g • μ) = whv h δ μ := by
  rw [whv, whv, vcirc_smul h, zm_smul, ← Subgroup.map_sup, conjCl_map_conj_of_mem hg]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem critR_le_usup_of_le_normalizer {δ δ' ρ : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) δ δ') (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ)
    (hN : ZM (puAmalgam c.hyp.le) δ' ≤
      Subgroup.normalizer (Usup _ δ ρ : Set (puAmalgam c.hyp.le).Universal)) :
    critR (puAmalgam c.hyp.le) δ δ' ≤ Usup _ δ ρ := by
  have h := c.hyp
  have : CharP F 2 := c.charP
  have hδ := hc.1
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
  have hZs : ZM (puAmalgam h.le) δ' ≤ stab _ δ := zm_le_stab_of_isCritical _ h.hyp20 c.bpos hc
  set E := natImage ψ (ZM (puAmalgam h.le) δ') with hEdef
  have hZab := isElemAbelian_zm _ h.hyp20 c.bpos (c.isCritical_symm hc).1
  have hE2 : ∀ g ∈ E, g * g = 1 := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    rw [← map_mul, ← sq]
    have : a ^ 2 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hZab.2 _ ha)
    rw [this, map_one]
  have hEc : ∀ g ∈ E, ∀ g' ∈ E, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨a, ha, rfl⟩ := mem_natImage.mp hg
    obtain ⟨b, hb, rfl⟩ := mem_natImage.mp hg'
    have hcomm := hZab.1
    rw [isMulCommutative_subgroup_iff] at hcomm
    have : a * b = b * a := Subtype.ext (by
      simp only [Subgroup.coe_mul]; exact hcomm _ ha _ hb)
    rw [← map_mul, ← map_mul, this]
  set H := fixN (natImage ψ (Qv (puAmalgam h.le) ρ)) with hHdef
  have hH2 : Module.finrank F H = 2 := (c.fixN_eq_commN_qv hψ hδ hρ).2
  have hstab := (c.le_normalizer_usup_iff hψ hδ hρ hZs (H := H)
    (fun v => c.mem_usup_iff hψ hδ hρ v)).mp hN
  have hcomm : commN E ≤ H := by
    intro u hu
    by_contra huH
    obtain ⟨e, he, y, hy, hey⟩ :=
      exists_not_mem_of_commN hE2 hEc hu huH (sup_span_eq_top hH2 huH)
    exact hey (hstab e he y hy)
  intro r hr
  have hrU : r ∈ Uloc h.le L δ := c.critR_le_uloc hc hr
  exact (c.mem_usup_iff hψ hδ hρ ⟨r, hrU⟩).mpr (hcomm ((c.mem_critR_iff hc hψ ⟨r, hrU⟩).mp hr))

theorem critR_le_usup_geo {δ δ' : Vtx (puAmalgam c.hyp.le)}
    (hc : IsCritical (puAmalgam c.hyp.le) δ δ') :
    critR (puAmalgam c.hyp.le) δ δ' ≤ Usup _ δ (geo _ δ δ' 1) := by
  have hd := c.dist_of_isCritical hc
  have hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ (geo _ δ δ' 1) := adj_geo_one _ (by omega)
  have hle : ZM (puAmalgam c.hyp.le) δ' ≤ Qv _ (geo _ δ δ' 1) := c.zm_le_qv_geo_one hc
  refine c.critR_le_usup_of_le_normalizer hc hρ (hle.trans ?_)
  intro t ht
  have hts : t ∈ stab (puAmalgam c.hyp.le) δ := qv_le_stab_of_adj _ hρ.symm ht
  rw [Usup, Subgroup.mem_normalizer_iff]
  have key : ∀ s ∈ Qv (puAmalgam c.hyp.le) (geo _ δ δ' 1),
      ⁅Zv (puAmalgam c.hyp.le) δ, Qv _ (geo _ δ δ' 1)⁆.map (MulAut.conj s).toMonoidHom ≤
        ⁅Zv (puAmalgam c.hyp.le) δ, Qv _ (geo _ δ δ' 1)⁆ := by
    intro s hs
    have hss : s ∈ stab (puAmalgam c.hyp.le) δ := qv_le_stab_of_adj _ hρ.symm hs
    rw [Subgroup.map_commutator]
    refine Subgroup.commutator_mono ?_ ?_
    · rw [zv_of_isMVtx _ hc.1]
      exact (map_conj_eq_of_mem_normalizer (stab_le_normalizer_zm _ δ hss)).le
    · exact (map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hs)).le
  intro w
  constructor
  · intro hw
    exact key t ht ⟨w, hw, rfl⟩
  · intro hw
    have := key t⁻¹ (inv_mem ht) ⟨_, hw, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using this

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem not_zm_le_normalizer_rev (hp : IsGoodPath _ p N) {j : ℕ} (hj : Even j) (h12 : 12 ≤ j)
    (hjN : j + 9 ≤ N) :
    ¬ ZM (puAmalgam c.hyp.le) (p (j + 8)) ≤
      Subgroup.normalizer (Usup _ (p j) (p (j - 1)) : Set (puAmalgam c.hyp.le).Universal) := by
  intro hN
  have h := c.hyp
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 12 := ⟨j - 12, by omega⟩
  have hk : Even k := (Nat.even_add.mp hj).mpr (by decide)
  have hc := c.isCritical_of_isGoodPath hp hj (show k + 12 + 8 ≤ N by omega)
  have hadj : (puAmalgam h.le).treeGraph.Adj (p (k + 12)) (p (k + 12 - 1)) := by
    have := hp.adj (k + 11) (by omega)
    rw [show k + 11 + 1 = k + 12 by omega] at this
    rw [show k + 12 - 1 = k + 11 by omega]
    exact this.symm
  have h1 := c.critR_le_usup_of_le_normalizer hc hadj hN
  have h2 : critR (puAmalgam h.le) (p (k + 12)) (p (k + 12 + 8)) ≤
      Usup _ (p (k + 12)) (p (k + 13)) := by
    rw [hp.eq_geo (i := k + 12) (j := k + 12 + 8) (k := k + 13) (by omega) (by omega)
      (by omega), show k + 13 - (k + 12) = 1 by omega]
    exact c.critR_le_usup_geo hc
  have e1 : Usup (puAmalgam h.le) (p (k + 12)) (p (k + 12 - 1)) = Hloc h.le L (p (k + 10)) := by
    have := c.hloc_eq_usup' hp (x := k + 4) (hk.add (by decide)) (by omega) (by omega)
    rw [show k + 4 + 6 = k + 10 by omega, show k + 4 + 8 = k + 12 by omega,
      show k + 4 + 7 = k + 11 by omega] at this
    rw [show k + 12 - 1 = k + 11 by omega]
    exact this.symm
  have e2 : Usup (puAmalgam h.le) (p (k + 12)) (p (k + 13)) = Hloc h.le L (p (k + 14)) := by
    have := c.hloc_eq_usup hp (x := k + 8) (hk.add (by decide)) (by omega) (by omega)
    rw [show k + 8 + 6 = k + 14 by omega, show k + 8 + 4 = k + 12 by omega,
      show k + 8 + 5 = k + 13 by omega] at this
    exact this.symm
  have e3 := (c.commutator_vv_vv hp (x := k + 10) (hk.add (by decide)) (by omega)
    (by omega)).2
  rw [show k + 10 + 4 = k + 14 by omega, show k + 10 - 2 = k + 8 by omega,
    show k + 10 + 6 = k + 16 by omega] at e3
  have hle : critR (puAmalgam h.le) (p (k + 12)) (p (k + 12 + 8)) ≤
      critR _ (p (k + 8)) (p (k + 16)) := by
    rw [← e3]
    exact le_inf (e1 ▸ h1) (e2 ▸ h2)
  have hs8 := c.straight_of_isGoodPath hp (y := k + 8) (hk.add (by decide)) (by omega)
  have hs12 := c.straight_of_isGoodPath hp (y := k + 12) (hk.add (by decide)) (by omega)
  have hg12 := c.zh_ne_of_isGoodPath hp (y := k + 12) (hk.add (by decide)) (by omega)
    (by omega)
  have hg16 := c.zh_ne_of_isGoodPath hp (y := k + 16) (hk.add (by decide)) (by omega)
    (by omega)
  have hc8 := c.isCritical_of_isGoodPath hp (y := k + 8) (hk.add (by decide)) (by omega)
  rw [show k + 8 + 8 = k + 16 by omega] at hc8
  have hcard1 := c.card_critR hp.toIsNBPath (x := k + 12) (by omega) hc
    (by rw [show k + 12 + 2 = k + 14 by omega, show k + 12 + 4 = k + 16 by omega]
        rw [show k + 8 + 2 = k + 10 by omega, show k + 8 + 4 = k + 12 by omega] at hs8
        rw [show k + 12 + 2 = k + 14 by omega, show k + 12 + 4 = k + 16 by omega] at hs12
        exact hs12)
    (by rw [show k + 12 + 3 = k + 15 by omega, show k + 12 + 5 = k + 17 by omega]
        rw [show k + 16 - 1 = k + 15 by omega, show k + 16 + 1 = k + 17 by omega] at hg16
        exact hg16)
  have hcard2 := c.card_critR hp.toIsNBPath (x := k + 8) (by omega) hc8
    (by rw [show k + 8 + 2 = k + 10 by omega, show k + 8 + 4 = k + 12 by omega] at hs8
        exact hs8)
    (by rw [show k + 8 + 3 = k + 11 by omega, show k + 8 + 5 = k + 13 by omega]
        rw [show k + 12 - 1 = k + 11 by omega, show k + 12 + 1 = k + 13 by omega] at hg12
        exact hg12)
  have hfin : Finite ↥(critR (puAmalgam h.le) (p (k + 8)) (p (k + 16))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard2]; exact Fintype.card_ne_zero)
  have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard1, hcard2])
  have hpe := hp.pe (k + 16) (hk.add (by decide)) (by omega) (by omega)
  rw [show k + 16 - 8 = k + 8 by omega, show k + 16 + 1 = k + 17 by omega] at hpe
  have hc12 : IsCritical (puAmalgam h.le) (p (k + 8 + 4)) (p (k + 8 + 12)) := by
    rw [show k + 8 + 4 = k + 12 by omega, show k + 8 + 12 = k + 12 + 8 by omega]; exact hc
  refine c.critR_ne_of_not_le_normalizer hp.toIsNBPath (x := k + 8) (by omega) hc8 hc12 ?_ ?_ ?_
  · rw [show k + 8 + 6 = k + 14 by omega, show k + 8 + 8 = k + 16 by omega,
      show k + 8 + 4 = k + 12 by omega]
    rw [show k + 12 + 2 = k + 14 by omega, show k + 12 + 4 = k + 16 by omega] at hs12
    exact hs12
  · rw [show k + 8 + 8 = k + 16 by omega, show k + 8 + 9 = k + 17 by omega]
    exact hpe
  · rw [show k + 8 + 8 = k + 16 by omega, show k + 8 + 4 = k + 12 by omega,
      show k + 8 + 12 = k + 12 + 8 by omega]
    exact heq.symm

theorem isGoodPath_rev (hp : IsGoodPath _ p N) {m : ℕ} (hm : Even m) (h12 : 12 ≤ m)
    (hmN : m + 1 ≤ N) : IsGoodPath (puAmalgam c.hyp.le) (fun i => p (m - i)) (m - 12) := by
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_⟩, ?_, fun i hi hi8 => ?_, fun i hi h2 hi2 => ?_,
    fun i hi h8 hiN => ?_⟩
  · have := hp.adj (m - i - 1) (by omega)
    rw [show m - i - 1 + 1 = m - i by omega] at this
    rw [show m - (i + 1) = m - i - 1 by omega]
    exact this.symm
  · have := hp.nb (m - i - 2) (by omega)
    rw [show m - i - 2 + 2 = m - i by omega] at this
    rw [show m - (i + 2) = m - i - 2 by omega]
    exact fun h => this h.symm
  · have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := m) (by omega) hp.mvtx hm
    simpa using this
  · obtain ⟨a, rfl⟩ : ∃ a, m = i + 8 + a := ⟨m - i - 8, by omega⟩
    have ha : Even a := by
      rw [show i + 8 + a = i + (8 + a) by omega] at hm
      have := (Nat.even_add.mp hm).mp hi
      exact (Nat.even_add.mp this).mp (by decide)
    have := c.isCritical_symm (hp.crit a ha (by omega))
    rw [show i + 8 + a - (i + 8) = a by omega, show i + 8 + a - i = a + 8 by omega]
    exact this
  · obtain ⟨g, hg, hgx⟩ := hp.straight (m - i) ((Nat.even_sub (by omega)).mpr
      (iff_of_true hm hi)) (by omega) (by omega)
    refine ⟨g⁻¹, inv_mem hg, ?_⟩
    rw [show m - (i + 2) = m - i - 2 by omega, show m - (i - 2) = m - i + 2 by omega, ← hgx,
      inv_smul_smul]
  · have hj : Even (m - i) := (Nat.even_sub (by omega)).mpr (iff_of_true hm hi)
    have := c.not_zm_le_normalizer_rev hp hj (by omega) (by omega)
    rw [show m - (i - 8) = m - i + 8 by omega, show m - (i + 1) = m - i - 1 by omega]
    exact this

theorem whv_eq_of_isGoodPath (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h2 : 2 ≤ a)
    (haN : a + 2 ≤ N) : whv c.hyp (p a) (p (a + 2)) = whv c.hyp (p a) (p (a - 2)) := by
  obtain ⟨g, hg, hgx⟩ := hp.straight a ha h2 haN
  rw [← hgx, whv_smul c.hyp _ hg]

theorem qv_le_whv_sup_qv_right (hZV : c.HZV) (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (h22 : 22 ≤ a) (haN : a + 14 ≤ N) :
    Qv (puAmalgam c.hyp.le) (p (a + 3)) ≤ whv c.hyp (p a) (p (a + 2)) ⊔ Qv _ (p (a + 4)) := by
  have hr := c.isGoodPath_rev hp (m := a + 12) (ha.add (by decide)) (by omega) (by omega)
  have := c.qv_le_whv_sup_qv hZV hr (y := 12) (by decide) le_rfl (by omega)
  rwa [show a + 12 - (12 - 3) = a + 3 by omega, show a + 12 - 12 = a by omega,
    show a + 12 - (12 - 2) = a + 2 by omega, show a + 12 - (12 - 4) = a + 4 by omega] at this

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
