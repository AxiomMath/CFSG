module

public import CFSG.Quasithin.MS93.S45X1
public import CFSG.Quasithin.MS93.S45FF

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem critR_ne_bot_of_isGoodPath (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h10 : 10 ≤ a)
    (haN : a + 8 ≤ N) : critR (puAmalgam c.hyp.le) (p (a - 2)) (p (a + 6)) ≠ ⊥ := by
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc := c.isCritical_of_isGoodPath hp ha2 (show a - 2 + 8 ≤ N by omega)
  have hs := c.straight_of_isGoodPath hp ha2 (show a - 2 + 4 ≤ N by omega)
  have hg := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
  have hcard := c.card_critR hp.toIsNBPath (x := a - 2) (by omega) hc hs
    (by rw [show a - 2 + 3 = a + 2 - 1 by omega, show a - 2 + 5 = a + 2 + 1 by omega]; exact hg)
  rw [show a - 2 + 8 = a + 6 by omega] at hcard
  intro hb
  rw [hb, Subgroup.card_bot] at hcard
  have := Fintype.one_lt_card (α := F)
  omega

theorem isC1_top (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N) :
    IsC1 c.hyp.le L (Fintype.card F) (p a)
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
        whv c.hyp (p a) (p (a + 2))) (whv c.hyp (p a) (p (a + 2))) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hβγ : (puAmalgam h.le).treeGraph.Adj (p (a + 1)) (p (a + 2)) := hp.adj (a + 1) (by omega)
  have hγ3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
  have h3μ : (puAmalgam h.le).treeGraph.Adj (p (a + 3)) (p (a + 4)) := hp.adj (a + 3) (by omega)
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set X := conjCl (stab (puAmalgam h.le) (p a)) (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
    Wh with hX
  set Y := whv h (p (a + 4)) (p (a + 2)) with hY
  set Nn := (X ⊓ Qv (puAmalgam h.le) (p (a + 2))) ⊔ Wh with hNn
  have hQs : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hQn : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hWhn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hμQ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ Qv (puAmalgam h.le) (p a) :=
    (c.vhat_le_vv hμ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]; omega))
  have hWhQ : Wh ≤ Qv (puAmalgam h.le) (p a) :=
    conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ (by
      rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega), c.b8]
      omega))) hQn
  have hXQ : X ≤ Qv (puAmalgam h.le) (p a) := sup_le (conjCl_le_of_le_normalizer hμQ hQn) hWhQ
  have hXs : X ≤ stab (puAmalgam h.le) (p a) := hXQ.trans hQs
  have hXn : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hWhn
  have hμγ : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ whv h (p (a + 2)) (p a) := by
    have e := c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega, show a + 2 - 2 = a by omega] at e
    rw [← e]
    exact c.vhat_le_whv_self
  have hγγ : Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2)) ≤ whv h (p (a + 2)) (p a) := by
    have e := c.whv_eq_of_isGoodPath hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 - 2 = a by omega] at e
    rw [← e]
    exact c.vhat_le_whv' hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
  have hXV6 : X ≤ conjCl (stab (puAmalgam h.le) (p a)) (whv h (p (a + 2)) (p a)) :=
    sup_le (conjCl_mono hμγ) (conjCl_mono hγγ)
  have hAc : ⁅X, X⁆ ≤ Wh :=
    (Subgroup.commutator_mono hXV6 hXV6).trans (c.commutator_vsix_le hZV hQ4 hp ha h34 (by omega))
  have hA2 : ∀ x ∈ X, x ^ 2 ∈ Wh := by
    have hXWn : X ≤ Subgroup.normalizer (Wh : Set _) := hXs.trans hWhn
    have hab := isElemAbelian_vi _ h20 c.bpos (δ := p (a + 4)) (i := 2)
      (by rw [c.b8]; norm_num)
    have hle : X ≤ sqSub' X Wh hAc hXWn := by
      refine sup_le (iSup₂_le fun g hg => le_sqSub' ?_ ?_) (le_sqSub' le_sup_right
        fun w hw => Subgroup.pow_mem _ hw 2)
      · exact (le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam h.le) (p a)) =>
          (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))).map (MulAut.conj g).toMonoidHom) g hg
          le_rfl).trans le_sup_left
      · rintro _ ⟨z, hz, rfl⟩
        have hz2 : z ^ 2 = 1 := hab.2 z (c.vhat_le_vv hμ hz)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_pow, hz2, mul_one, mul_inv_cancel]
        exact Wh.one_mem
    exact fun x hx => (hle hx).2
  have hYT : Y ≤ Qv (puAmalgam h.le) (p (a + 1)) := by
    have := c.whv_le_qv hp (y := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rwa [show a + 4 - 2 = a + 2 by omega, show a + 4 - 3 = a + 1 by omega] at this
  have hYs : Y ≤ stab (puAmalgam h.le) (p a) := hYT.trans (qv_le_stab_of_adj _ hαβ.symm)
  have hYQμ : Y ≤ Qv (puAmalgam h.le) (p (a + 4)) := c.whv_le_qv_of_dist hγ
    (by rw [tdist_comm, hp.dist_eq' (i := a + 2) (j := a + 4) (by omega) (by omega)]; omega)
    (by simp)
  have hYZ : ⁅Y, Qv (puAmalgam h.le) (p (a + 4))⁆ ≤ ZM _ (p (a + 4)) := by
    have := c.commutator_whv_qv_le hZV hp (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rwa [show a + 4 - 2 = a + 2 by omega] at this
  have hZμQ : ZM (puAmalgam h.le) (p (a + 4)) ≤ Qv _ (p a) := zm_le_qv_of_dist_lt _ hμ (by
    rw [tdist_comm, hp.dist_eq' (i := a) (j := a + 4) (by omega) (by omega), c.b8]; omega)
  have hYc : ⁅Y, Y⁆ ≤ Qv (puAmalgam h.le) (p a) :=
    ((Subgroup.commutator_mono le_rfl hYQμ).trans hYZ).trans hZμQ
  have hY2 : ∀ y ∈ Y, y ^ 2 ∈ Qv (puAmalgam h.le) (p a) := by
    have hYYZ : ⁅Y, Y⁆ ≤ ZM (puAmalgam h.le) (p (a + 4)) :=
      (Subgroup.commutator_mono le_rfl hYQμ).trans hYZ
    have hZc : ZM (puAmalgam h.le) (p (a + 4)) ≤ Subgroup.centralizer (Y : Set _) :=
      (zm_le_centralizer_qv _ h20 hμ).trans (Subgroup.centralizer_le hYQμ)
    have hab := isElemAbelian_vi _ h20 c.bpos (δ := p (a + 2)) (i := 2)
      (by rw [c.b8]; norm_num)
    have hle : Y ≤ sqSub Y (ZM (puAmalgam h.le) (p (a + 4))) hYYZ hZc := by
      refine iSup₂_le fun g hg => le_sqSub ?_ ?_
      · exact le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam h.le) (p (a + 4))) =>
          (Vcirc h.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))).map (MulAut.conj g).toMonoidHom) g hg
          le_rfl
      · rintro _ ⟨z, hz, rfl⟩
        have hz2 : z ^ 2 = 1 := hab.2 z (c.vhat_le_vv hγ hz)
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_pow, hz2, mul_one, mul_inv_cancel]
    exact fun y hy => hZμQ (hle hy).2
  have hYq : Fintype.card F ≤ (Qv (puAmalgam h.le) (p a)).relIndex Y := by
    have hT := c.qv_le_whv_sup_qv hZV hp (y := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rw [show a + 4 - 3 = a + 1 by omega, show a + 4 - 2 = a + 2 by omega,
      show a + 4 - 4 = a by omega] at hT
    have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
    have hfin : Finite ↥(Y ⊔ Qv (puAmalgam h.le) (p a)) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hYs hQs))
    have hq2 := c.relIndex_qv hα hαβ
    have h1 : (Qv (puAmalgam h.le) (p a)).relIndex (Qv _ (p (a + 1))) ≤
        (Qv (puAmalgam h.le) (p a)).relIndex (Y ⊔ Qv _ (p a)) :=
      Subgroup.relIndex_le_of_le_right hT (by
        rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
    rw [relIndex_sup_eq (hYs.trans hQn), hq2] at h1
    exact le_trans (Nat.le_self_pow two_ne_zero _) h1
  have hNA : Nn ≤ X := sup_le inf_le_left le_sup_right
  have hWhQ3 : Wh ≤ Qv (puAmalgam h.le) (p (a + 3)) := c.whv_le_qv_right hp ha (by omega) (by omega)
  have hQ4n : Wh ≤ Subgroup.normalizer (Qv (puAmalgam h.le) (p (a + 4)) : Set _) :=
    hWhQ3.trans ((qv_le_stab_of_adj _ h3μ).trans (stab_le_normalizer_qv _ _))
  have hT3 := c.qv_le_whv_sup_qv_right hZV hp ha (by omega) (by omega)
  have hNY : ⁅Nn, Y⁆ ≤ Wh := by
    refine S46.commutator_sup_le_of_le_normalizer hWhn (inf_le_left.trans hXs)
      (hWhQ.trans hQs) ?_ (Subgroup.le_normalizer_iff_commutator_le_left.mp (hYs.trans hWhn))
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hx3 : x ∈ Qv (puAmalgam h.le) (p (a + 3)) := qv_le_qv _ h20 hγ hγ3 hx.2
    have hx' := hT3 hx3
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hQ4n] at hx'
    obtain ⟨w, hw, q, hq, rfl⟩ := hx'
    rw [S46.commutatorElement_mul_left_conj]
    have hqy : ⁅q, y⁆ ∈ Wh := by
      have h1 : ⁅q, y⁆ ∈ ⁅Y, Qv (puAmalgam h.le) (p (a + 4))⁆ := by
        rw [Subgroup.commutator_comm]; exact Subgroup.commutator_mem_commutator hq hy
      exact c.zm_le_whv_right hZV hp ha (by omega) (by omega) (hYZ h1)
    have hwy : ⁅w, y⁆ ∈ Wh := by
      have e : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact Wh.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hWhn (hYs hy)) _).mp (Wh.inv_mem hw))
    exact Wh.mul_mem (Wh.mul_mem (Wh.mul_mem hw hqy) (Wh.inv_mem hw)) hwy
  have hNidx : Nn.relIndex X ≤ Fintype.card F := by
    have hle := c.relIndex_top_le hp ha (by omega) (by omega)
    rw [← hX] at hle
    have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
    have : Finite ↥X := Finite.of_injective _ (Subgroup.inclusion_injective hXs)
    refine le_trans (Subgroup.relIndex_le_of_le_left (le_sup_left : X ⊓ _ ≤ Nn) ?_) ?_
    · rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite
    · rw [Subgroup.inf_relIndex_left]
      exact hle
  have hC1 := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  rw [← hX] at hC1
  have hXV := c.commutator_top_vv_le hp ha (by omega) (by omega)
  rw [← hX] at hXV
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hc2 := c.isCritical_of_isGoodPath hp ha2 (show a - 2 + 8 ≤ N by omega)
  rw [show a - 2 + 8 = a + 6 by omega] at hc2
  have hg2 : geo (puAmalgam h.le) (p (a - 2)) (p (a + 6)) 2 = p a := by
    rw [hp.eq_geo (i := a - 2) (j := a + 6) (k := a) (by omega) (by omega) (by omega),
      show a - (a - 2) = 2 by omega]
  have hRZ : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ≤ Zloc h.le L (p a) := by
    have := c.critR_le_zloc hc2
    rwa [hg2] at this
  have hnt : ¬ ⁅X, Ltil h.le L (p a)⁆ ≤ ⁅X, Qv (puAmalgam h.le) (p a)⁆ ⊔ Wh := by
    intro hcon
    rw [sup_eq_right.mpr hC1] at hcon
    apply c.critR_ne_bot_of_isGoodPath hp ha (by omega) (by omega)
    rw [eq_bot_iff, critR, Subgroup.commutator_le]
    intro z hz x hx
    have hμ6 : ZM (puAmalgam h.le) (p (a + 6)) ≤ X := by
      have := c.zm_le_vhat_right hZV hp (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
      rw [show a + 4 + 2 = a + 6 by omega] at this
      exact (this.trans (S4A.le_conjCl _ _)).trans le_sup_left
    have hxX := hμ6 hx
    have hcomm := c.commute_vhat_of_comm hp ha (by omega) (hXQ hxX)
      (fun v hv => hRZ (hXV (Subgroup.commutator_mem_commutator hxX hv)))
      (fun l hl => hcon (Subgroup.commutator_mem_commutator hxX hl)) z
      (c.zm_le_vhat_left' hZV hp ha (by omega) (by omega) hz)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
    exact hcomm.symm
  exact isC1_of_offender h h14 hSQ c.via hα hXs hXn le_sup_right hWhn hAc hA2 hYs hY2 hYc hYq
    le_sup_right hNA hNY hNidx hnt

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
