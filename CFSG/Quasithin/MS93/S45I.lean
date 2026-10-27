module

public import CFSG.Quasithin.MS93.S45S1
import CFSG.Quasithin.MS93.S46Loc
import CFSG.Quasithin.MS93.S4AFMain

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem zm_le_vv_of_le {δ μ : Vtx (puAmalgam c.hyp.le)} (hμ : IsMVtx _ μ)
    (hd : (puAmalgam c.hyp.le).treeGraph.dist δ μ ≤ 2) : ZM (puAmalgam c.hyp.le) μ ≤ Vv _ δ := by
  have := zv_le_vi (puAmalgam c.hyp.le) (δ := δ) (ρ := μ) (i := 2) hd
  rwa [zv_of_isMVtx _ hμ] at this

theorem vv_le_vv_of_adj {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β) : Vv (puAmalgam c.hyp.le) β ≤ Vv _ δ := by
  have hβH : ¬ IsMVtx (puAmalgam c.hyp.le) β := by
    rw [← isMVtx_iff_of_adj _ hβ]; exact hδ
  rw [S46.vv_eq_iSup_of_not_isMVtx hβH]
  refine iSup₂_le fun ε hε => ?_
  have hεM : IsMVtx (puAmalgam c.hyp.le) ε := by
    have := isMVtx_iff_of_adj _ hε; tauto
  refine c.zm_le_vv_of_le hεM ?_
  have := dist_triangle (puAmalgam c.hyp.le) δ β ε
  rw [(SimpleGraph.dist_eq_one_iff_adj).mpr hβ, (SimpleGraph.dist_eq_one_iff_adj).mpr
    (show (puAmalgam c.hyp.le).treeGraph.Adj β ε from hε)] at this
  exact this

theorem stab_inf_normalizer_le_normalizer_zm {δ δ' β : Vtx (puAmalgam c.hyp.le)}
    (hδ : IsMVtx _ δ) (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β)
    (hβ' : (puAmalgam c.hyp.le).treeGraph.Adj δ' β)
    (hH : Usup (puAmalgam c.hyp.le) δ β = Hloc c.hyp.le L δ') :
    stab (puAmalgam c.hyp.le) δ' ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) β : Set (puAmalgam c.hyp.le).Universal) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) δ : Set (puAmalgam c.hyp.le).Universal) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hβH : ¬ IsMVtx (puAmalgam h.le) β := by
    rw [← isMVtx_iff_of_adj _ hβ]; exact hδ
  set N := stab (puAmalgam h.le) δ' ⊓
    Subgroup.normalizer (Qv (puAmalgam h.le) β : Set (puAmalgam h.le).Universal) with hNdef
  set V₀ := conjCl N (ZM (puAmalgam h.le) δ) with hV₀
  have hNV : N ≤ Subgroup.normalizer (Vv (puAmalgam h.le) β : Set _) :=
    inf_le_right.trans (S46.normalizer_qv_le_normalizer_vv h hβH)
  have hV₀β : V₀ ≤ Vv (puAmalgam h.le) β :=
    iSup₂_le fun _ hg => (Subgroup.map_mono (S46.zm_le_vv_of_adj hβ.symm hδ)).trans
      (map_conj_eq_of_mem_normalizer (hNV hg)).le
  have hV₀δ : V₀ ≤ Vv (puAmalgam h.le) δ := hV₀β.trans (c.vv_le_vv_of_adj hδ hβ)
  have hV₀Q : V₀ ≤ Qv (puAmalgam h.le) δ := hV₀δ.trans (c.vv_le_qv' hδ)
  have hHn : N ≤ Subgroup.normalizer (Hloc h.le L δ' : Set _) :=
    inf_le_left.trans (c.stab_le_normalizer_hloc δ')
  have hVT : ⁅V₀, Qv (puAmalgam h.le) β⁆ ≤ Hloc h.le L δ' := by
    refine S4A.commutator_conjCl_le hHn inf_le_right ?_ ?_
    · exact (zm_le_qv_self _ hδ h.critDist_pos).trans ((qv_le_qv _ h20 hδ hβ).trans
        ((qv_le_stab_of_adj _ hβ'.symm).trans (c.stab_le_normalizer_hloc δ')))
    · rw [← hH, Usup, zv_of_isMVtx _ hδ]
  have hVQ : ⁅V₀, Qv (puAmalgam h.le) δ⁆ = ⊥ := by
    rw [eq_bot_iff]
    obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hδ
    have h1 : ⁅V₀, Qv (puAmalgam h.le) δ⁆ ≤ Usup (puAmalgam h.le) δ β := by
      rw [hH]
      exact (Subgroup.commutator_mono le_rfl (qv_le_qv _ h20 hδ hβ)).trans hVT
    have h2 : ⁅V₀, Qv (puAmalgam h.le) δ⁆ ≤ Zloc h.le L δ :=
      (Subgroup.commutator_mono hV₀δ le_rfl).trans (c.commutator_vv_qv_le_zloc hδ)
    have h3 : Usup (puAmalgam h.le) δ β ≤ Uloc h.le L δ := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hδ hβ]; exact inf_le_left
    rw [← uloc_inf_zloc h c.full δ]
    exact le_inf (h1.trans h3) h2
  have hV₀Z : V₀ ≤ ZM (puAmalgam h.le) δ := by
    rw [← xm_eq_zm h c.full hδ, XM, omegaOneCenterOf, omegaOneOf]
    intro v hv
    refine Subgroup.subset_closure ⟨⟨hV₀Q hv, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩, ?_⟩
    · have := Subgroup.commutator_mem_commutator hv hq
      rw [hVQ, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    · exact (isElemAbelian_vi _ h20 c.bpos (by rw [c.b8]; norm_num)).2 v (hV₀δ hv)
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hmem : ∀ m ∈ N, ∀ z ∈ ZM (puAmalgam h.le) δ, m * z * m⁻¹ ∈ ZM (puAmalgam h.le) δ := by
    intro m hm z hz
    have hle : (ZM (puAmalgam h.le) δ).map (MulAut.conj m).toMonoidHom ≤ V₀ :=
      le_iSup₂_of_le (f := fun g (_ : g ∈ N) =>
        (ZM (puAmalgam h.le) δ).map (MulAut.conj g).toMonoidHom) m hm le_rfl
    exact hV₀Z (hle ⟨z, hz, rfl⟩)
  refine ⟨hmem n hn z, fun hz => ?_⟩
  have := hmem n⁻¹ (inv_mem hn) _ hz
  simpa [mul_assoc] using this

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem normalizer_zm_right (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 12 ≤ N) :
    stab (puAmalgam c.hyp.le) (p (x + 6)) ⊓
        Subgroup.normalizer (Qv (puAmalgam c.hyp.le) (p (x + 7)) : Set _) ≤
      Subgroup.normalizer (ZM (puAmalgam c.hyp.le) (p (x + 8)) : Set _) := by
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam c.hyp.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  exact c.stab_inf_normalizer_le_normalizer_zm (hM (x + 8) (by omega) (hx.add (by decide)))
    (hp.adj (x + 7) (by omega)).symm
    (hp.adj (x + 6) (by omega)) (c.hloc_eq_usup' hp hx h4 hxN).symm

theorem vv_inf_qv_le (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 12 ≤ N) :
    Vv (puAmalgam c.hyp.le) (p x) ⊓ Qv _ (p (x + 6)) ≤ ZM _ (p x) ⊔ Qv _ (p (x + 8)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hc := c.isCritical_of_isGoodPath hp hx (by omega)
  have hM0 := hM x (by omega) hx
  have hM4 := hM (x + 4) (by omega) (hx.add (by decide))
  have hM6 := hM (x + 6) (by omega) (hx.add (by decide))
  have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
  have ha67 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have ha78 : (puAmalgam h.le).treeGraph.Adj (p (x + 7)) (p (x + 8)) := hp.adj (x + 7) (by omega)
  set Y := Vv (puAmalgam h.le) (p x) ⊓ Qv _ (p (x + 6)) with hYdef
  have hYT : Y ≤ Qv (puAmalgam h.le) (p (x + 7)) := inf_le_right.trans (qv_le_qv _ h20 hM6 ha67)
  have hYs : Y ≤ stab (puAmalgam h.le) (p (x + 8)) := hYT.trans (qv_le_stab_of_adj _ ha78)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  set E := natImage ψ Y with hEdef
  have hET : E ≤ natImage ψ (Qv (puAmalgam h.le) (p (x + 7))) := natImage_mono hYT
  have hT := c.fixN_eq_commN_qv hψ hM8 ha78.symm
  have hEq : Nat.card ↥E ≤ Fintype.card F := by
    by_contra hlt
    push Not at hlt
    have hE : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hlt
      have := Fintype.one_lt_card (α := F)
      omega
    have hfix : Module.finrank F ↥(fixN E) = 2 := by
      have h1 : 2 ≤ Module.finrank F ↥(fixN E) := hT.2 ▸ Submodule.finrank_mono (fixN_anti hET)
      have h2 : Module.finrank F ↥(fixN E) < 3 := by
        have := Submodule.finrank_lt (fixN_ne_top hE)
        rwa [Module.finrank_fin_fun] at this
      omega
    have hcomm : commN E = fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 7)))) := by
      have hle : commN E ≤ fixN (natImage ψ (Qv (puAmalgam h.le) (p (x + 7)))) :=
        hT.1 ▸ commN_mono hET
      refine Submodule.eq_of_le_of_finrank_le hle ?_
      rw [hT.2]
      by_contra hlt2
      push Not at hlt2
      have hb := card_le_pow_finrank E
      rw [hfix, show 3 - 2 = 1 by rfl, one_mul, Nat.card_eq_fintype_card (α := F)] at hb
      have : Fintype.card F ^ Module.finrank F ↥(commN E) ≤ Fintype.card F ^ 1 :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      rw [pow_one] at this
      omega
    have hW : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) ≤ Vv _ (p x) := by
      intro w hw
      have hwU : w ∈ Uloc h.le L (p (x + 8)) := by
        rw [c.usup_eq_uloc_inf_centralizer hψ hM8 ha78.symm] at hw; exact hw.1
      have h1 : w ∈ ⁅Uloc h.le L (p (x + 8)), Y⁆ := by
        refine (S4A.mem_commutator_iff_natVec hψ hYs ⟨w, hwU⟩).mpr ?_
        rw [← hEdef, hcomm]
        exact (c.mem_usup_iff hψ hM8 ha78.symm ⟨w, hwU⟩).mp hw
      have hUn : Uloc h.le L (p (x + 8)) ≤
          Subgroup.normalizer (Vv (puAmalgam h.le) (p x) : Set _) :=
        (uloc_le_zm h c.full hM8).trans ((c.zm_le_qv_geo_one hc).trans
          ((qv_le_stab_of_adj _ (adj_geo_one _ (by rw [c.dist_of_isCritical hc]; omega)).symm).trans
            (stab_le_normalizer_vv h _)))
      have h2 : ⁅Uloc h.le L (p (x + 8)), Y⁆ ≤ Vv (puAmalgam h.le) (p x) := by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
          (Subgroup.le_normalizer_iff_commutator_le_left.mp hUn)
      exact h2 h1
    have hS := c.commutator_zm_qv_of_isGoodPath hp hx h4 hxN
    have hW' : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 5)) ≤ Vv _ (p x) := hS.2.2.2 ▸ hW
    have hx4' : Even (x - 4) := by obtain ⟨k, hk⟩ := hx; exact ⟨k - 2, by omega⟩
    have hMm := hM (x - 4) (by omega) hx4'
    have hcen : Vv (puAmalgam h.le) (p x) ≤
        Subgroup.centralizer (ZM (puAmalgam h.le) (p (x - 4)) : Set _) :=
      c.vi_le_centralizer_zm hMm (by rw [tdist_comm, hd (x - 4) x (by omega) (by omega)]; omega)
    have hc4 : IsCritical (puAmalgam h.le) (p (x + 4)) (p (x - 4)) := by
      have := hp.crit (x - 4) hx4' (by omega)
      rwa [show x - 4 + 8 = x + 4 by omega] at this
    obtain ⟨ψ₄, -, hψ₄⟩ := exists_natural_Uloc h c.via hM4
    have hg : geo (puAmalgam h.le) (p (x + 4)) (p (x - 4)) 1 = p (x + 3) := by
      rw [hp.eq_geo_rev (i := x - 4) (j := x + 4) (k := x + 3) (by omega) (by omega) (by omega),
        show x + 4 - (x + 3) = 1 by omega]
    have hfix4 := c.fixN_natImage_zm hc4 hψ₄
    rw [hg] at hfix4
    have hZs : ZM (puAmalgam h.le) (p (x - 4)) ≤ stab _ (p (x + 4)) :=
      zm_le_stab_of_isCritical _ h20 c.bpos hc4
    have ha3 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 3)) :=
      (hp.adj (x + 3) (by omega)).symm
    have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
    have hsub : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 5)) ≤ Usup _ (p (x + 4)) (p (x + 3)) := by
      intro w hw
      have hwU : w ∈ Uloc h.le L (p (x + 4)) := by
        rw [c.usup_eq_uloc_inf_centralizer hψ₄ hM4 ha5] at hw; exact hw.1
      have h1 := (S4A.mem_centralizer_iff_natVec hψ₄ hZs ⟨w, hwU⟩).mp (hcen (hW' hw))
      rw [hfix4] at h1
      exact (c.mem_usup_iff hψ₄ hM4 ha3 ⟨w, hwU⟩).mpr h1
    have hcard3 := c.card_usup hψ₄ hM4 ha3
    have hfin3 : Finite ↥(Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3))) :=
      Nat.finite_of_card_ne_zero (by rw [hcard3]; exact pow_ne_zero _ Fintype.card_ne_zero)
    have heq : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 5)) = Usup _ (p (x + 4)) (p (x + 3)) :=
      Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard3, c.card_usup hψ₄ hM4 ha5])
    have hgpd := c.zh_ne_of_isGoodPath hp (y := x + 4) (hx.add (by decide)) (by omega) (by omega)
    rw [show x + 4 - 1 = x + 3 by omega, show x + 4 + 1 = x + 5 by omega] at hgpd
    exact hgpd ((c.usup_eq_iff_zh_eq hψ₄ hM4 ha3 ha5).mp heq.symm)
  have hY0 : ZM (puAmalgam h.le) (p x) ≤ Y :=
    le_inf (zm_le_vv h hM0) (zm_le_qv_of_dist_lt _ hM0
      (by rw [hd x (x + 6) (by omega) (by omega), c.b8]; omega))
  have hZE : natImage ψ (ZM (puAmalgam h.le) (p x)) ≤ E := natImage_mono hY0
  have hcardZ : Nat.card ↥(natImage ψ (ZM (puAmalgam h.le) (p x))) = Fintype.card F :=
    c.card_natImage_zm (c.isCritical_symm hc) hψ
  have hfinE : Finite ↥E := Nat.finite_of_card_ne_zero (by
    have := Nat.card_pos (α := ↥(natImage ψ (ZM (puAmalgam h.le) (p x))))
    have := Subgroup.card_le_of_le hZE
    omega)
  have hEeq : E = natImage ψ (ZM (puAmalgam h.le) (p x)) :=
    (Subgroup.eq_of_le_of_card_ge hZE (by rw [hcardZ]; exact hEq)).symm
  intro y hy
  have hyE : toSL3 ψ ⟨y, hYs hy⟩ ∈ natImage ψ (ZM (puAmalgam h.le) (p x)) :=
    hEeq ▸ mem_natImage.mpr ⟨⟨y, hYs hy⟩, hy, rfl⟩
  obtain ⟨z, hz, hzy⟩ := mem_natImage.mp hyE
  have hk : toSL3 ψ (z⁻¹ * ⟨y, hYs hy⟩) = 1 := by rw [map_mul, map_inv, hzy, inv_mul_cancel]
  rw [toSL3_eq_one_iff hψ] at hk
  have hq : (z : (puAmalgam h.le).Universal)⁻¹ * y ∈ Qv (puAmalgam h.le) (p (x + 8)) := by
    rw [← S4A.stab_inf_centralizer_uloc h c.via hM8]
    refine ⟨(z⁻¹ * ⟨y, hYs hy⟩ : ↥(stab _ _)).2, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 := hk v hv
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    calc v * ((z : (puAmalgam h.le).Universal)⁻¹ * y) =
        ((z : (puAmalgam h.le).Universal)⁻¹ * y * v * ((z : (puAmalgam h.le).Universal)⁻¹ * y)⁻¹) *
          ((z : (puAmalgam h.le).Universal)⁻¹ * y) := by rw [h1]
      _ = (z : (puAmalgam h.le).Universal)⁻¹ * y * v := by group
  have e : y = (z : (puAmalgam h.le).Universal) * ((z : (puAmalgam h.le).Universal)⁻¹ * y) := by
    group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hq)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
