module

public import CFSG.Quasithin.MS93.S45M0
public import CFSG.Quasithin.MS93.S45DL
public import CFSG.Quasithin.MS93.S45Q4

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

theorem mid_isSum (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h24 : 24 ≤ a) (haN : a + 24 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1)
    (hT : natImage ψ (Qv (puAmalgam c.hyp.le) (p (a + 1))) = rootGroup 1 0 ⊔ rootGroup 2 0) :
    IsSumOfNaturalModulesVia (stab _ (p a))
      (conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)))
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ψ true 1 := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  obtain ⟨n, hn⟩ := c.via.1
  have hsq := S4A.sqtkGroup_SL3_of_sqtkQuot h hSQ c.via
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have : Finite ↥(stab (puAmalgam h.le) (p a)) := S4A.finite_stab h hα
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  set C := conjCl (stab (puAmalgam h.le) (p a)) (ZM (puAmalgam h.le) (p (a + 4))) with hC
  set W := C ⊔ Vh with hW
  set Y := ZM (puAmalgam h.le) (p (a + 4)) ⊔ Vh with hY
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Wμ := whv h (p (a + 4)) (p (a + 2)) with hWμ
  have hKVh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKC : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (C : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hKW : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (W : Set _) :=
    le_normalizer_sup hKC hKVh
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hQK : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_qv _ _
  have hZμQ : ZM (puAmalgam h.le) (p (a + 4)) ≤ Qv _ (p a) := zm_le_qv_of_dist_lt _ hμ (by
    rw [tdist_comm, hd a (a + 4) (by omega) (by omega), c.b8]; omega)
  have hVhQ : Vh ≤ Qv (puAmalgam h.le) (p a) := (c.vhat_le_vv hα).trans (c.vv_le_qv' hα)
  have hCQ : C ≤ Qv (puAmalgam h.le) (p a) := conjCl_le_of_le_normalizer hZμQ hKQ
  have hWQ : W ≤ Qv (puAmalgam h.le) (p a) := sup_le hCQ hVhQ
  have hWK : W ≤ stab (puAmalgam h.le) (p a) := hWQ.trans hQK
  have hZμWh : ZM (puAmalgam h.le) (p (a + 4)) ≤ Wh :=
    c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hCWh : C ≤ Wh := conjCl_le_of_le_normalizer hZμWh hKWh
  have hWWh : W ≤ Wh := sup_le hCWh hVhWh
  have hWhQ : ⁅Wh, Qv (puAmalgam h.le) (p a)⁆ ≤ ZM _ (p a) :=
    c.commutator_whv_qv_le' hZV hp ha (by omega) (by omega)
  have hZαVh : ZM (puAmalgam h.le) (p a) ≤ Vh := le_sup_right
  have hWWZ : ⁅W, W⁆ ≤ ZM (puAmalgam h.le) (p a) :=
    (Subgroup.commutator_mono hWWh hWQ).trans hWhQ
  have hNN : ⁅W, W⁆ ≤ Vh := hWWZ.trans hZαVh
  have hNQ : ⁅W, Qv (puAmalgam h.le) (p a)⁆ ≤ Vh :=
    ((Subgroup.commutator_mono hWWh le_rfl).trans hWhQ).trans hZαVh
  have hN2 : ∀ x ∈ W, x ^ 2 ∈ Vh := by
    have hZc : ZM (puAmalgam h.le) (p a) ≤ Subgroup.centralizer (W : Set _) :=
      (zm_le_centralizer_qv _ h20 hα).trans (Subgroup.centralizer_le hWQ)
    have hZab := isElemAbelian_zm _ h20 c.bpos hμ
    have hVab := isElemAbelian_vi _ h20 c.bpos (δ := p a) (i := 2) (by rw [c.b8]; norm_num)
    have hle : W ≤ sqSub W (ZM (puAmalgam h.le) (p a)) hWWZ hZc := by
      refine sup_le (iSup₂_le fun g hg => le_sqSub ?_ ?_) (le_sqSub le_sup_right ?_)
      · exact (le_iSup₂_of_le (f := fun g (_ : g ∈ stab (puAmalgam h.le) (p a)) =>
          (ZM (puAmalgam h.le) (p (a + 4))).map (MulAut.conj g).toMonoidHom) g hg le_rfl).trans
          le_sup_left
      · rintro _ ⟨z, hz, rfl⟩
        have hz2 : z ^ 2 = 1 := hZab.2 z hz
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [conj_pow, hz2, mul_one, mul_inv_cancel]
      · intro v hv
        exact hVab.2 v (c.vhat_le_vv hα hv)
    intro x hx
    exact hZαVh (hle hx).2
  have hQT : Qv (puAmalgam h.le) (p a) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hα hαβ
  have hTK : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab (puAmalgam h.le) (p a) :=
    qv_le_stab_of_adj _ hαβ.symm
  have hker : ∀ k : ↥(stab (puAmalgam h.le) (p a)),
      toSL3 ψ k = 1 ↔ (k : (puAmalgam h.le).Universal) ∈ Qv _ (p a) := by
    intro k
    rw [← MonoidHom.mem_ker, c.ker_toSL3_eq hα hψ, Subgroup.mem_subgroupOf]
  have hYW : Y ≤ W := sup_le ((S4A.le_conjCl _ _).trans le_sup_left) le_sup_right
  have hYK : Y ≤ stab (puAmalgam h.le) (p a) := hYW.trans hWK
  have hZγVh : ZM (puAmalgam h.le) (p (a + 2)) ≤ Vh :=
    c.zm_le_vhat_right hZV hp ha (by omega) (by omega)
  have hYZ : Vh.relIndex Y ≤ Fintype.card F := by
    rw [hY, relIndex_sup_eq ((hZμQ.trans hQK).trans hKVh)]
    have hμ3 : (puAmalgam h.le).treeGraph.Adj (p (a + 4)) (p (a + 3)) :=
      (hp.adj (a + 3) (by omega)).symm
    have hγ3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
    have hq := c.relIndex_zh hμ hμ3
    have hZH : ZH (puAmalgam h.le) (p (a + 3)) ≤ Vh := (zh_le_zm _ hγ3).trans hZγVh
    rw [← hq]
    exact Subgroup.relIndex_le_of_le_left hZH (by rw [hq]; exact Fintype.card_ne_zero)
  have hYT : ⁅Y, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ Vh := by
    refine S46.commutator_sup_le_of_le_normalizer hKVh (hZμQ.trans hQK) (hVhQ.trans hQK) ?_
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hTK.trans hKVh))
    have h1 := c.commutator_vhat_qv_le_left hZV hp ha (by omega) (by omega)
    have h2 := c.zm_le_vhat_right hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega] at h2
    exact (Subgroup.commutator_mono h2 le_rfl).trans (h1.trans (sup_le hZαVh hZγVh))
  have hTWQ : Qv (puAmalgam h.le) (p (a + 1)) ≤ Wμ ⊔ Qv _ (p a) := by
    have := c.qv_le_whv_sup_qv hZV hp (y := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rwa [show a + 4 - 3 = a + 1 by omega, show a + 4 - 2 = a + 2 by omega,
      show a + 4 - 4 = a by omega] at this
  have hWμT : Wμ ≤ Qv (puAmalgam h.le) (p (a + 1)) := by
    have := c.whv_le_qv hp (y := a + 4) (ha.add (by decide)) (by omega) (by omega)
    rwa [show a + 4 - 2 = a + 2 by omega, show a + 4 - 3 = a + 1 by omega] at this
  have hTY : Qv (puAmalgam h.le) (p (a + 1)) ≤ Subgroup.normalizer (Y : Set _) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr (hYT.trans le_sup_right)
  have hWQμ : W ≤ Qv (puAmalgam h.le) (p (a + 4)) := by
    refine sup_le (iSup₂_le fun g hg => ?_) ?_
    · rw [← zm_smul]
      exact hQ4 p N hp a ha h24 haN g hg
    · exact (c.vhat_le_vv hα).trans (vi_le_qv _ (by
        rw [hd a (a + 4) (by omega) (by omega), c.b8]; omega))
  have hWμQμ : ⁅Wμ, Qv (puAmalgam h.le) (p (a + 4))⁆ ≤ ZM _ (p (a + 4)) := by
    have := c.commutator_whv_qv_le hZV hp (a := a + 4) (ha.add (by decide)) (by omega)
      (by omega)
    rwa [show a + 4 - 2 = a + 2 by omega] at this
  have hNTY : ⁅W, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ Y := by
    rw [Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono hTWQ le_rfl).trans ?_
    refine S46.commutator_sup_le_of_le_normalizer hTY hWμT hQT ?_ ?_
    · exact (Subgroup.commutator_mono le_rfl hWQμ).trans (hWμQμ.trans le_sup_left)
    · rw [Subgroup.commutator_comm]
      exact hNQ.trans le_sup_right
  have hNTZ : ¬ ⁅W, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ Vh := by
    intro hle
    have hcm : ∀ x ∈ W, ∀ g ∈ stab (puAmalgam h.le) (p a), ⁅x, g⁆ ∈ Vh := fun x hx g hg =>
      commutator_mem_of_natImage hψs hker hQK hKVh hKW hTK hT hNQ hle hx hg
    have hWhc : Wh ≤ Subgroup.centralizer (Vv (puAmalgam h.le) (p a) : Set _) :=
      c.whv_le_centralizer_vv hγ (by rw [hd a (a + 2) (by omega) (by omega)]; omega)
    set S := ⁅Wh, ZM (puAmalgam h.le) (p (a + 4))⁆ with hS
    have hSn : ∀ g ∈ stab (puAmalgam h.le) (p a), ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
      intro g hg s hs
      have hmap : S.map (MulAut.conj g).toMonoidHom ≤ S := by
        rw [hS, Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hKWh hg),
          Subgroup.commutator_le]
        intro w hw z' hz'
        obtain ⟨z, hz, rfl⟩ := hz'
        have hzW : z ∈ W := hYW (Subgroup.mem_sup_left hz)
        have hv : ⁅z⁻¹, g⁆ ∈ Vh := hcm z⁻¹ (W.inv_mem hzW) g hg
        have e1 : (MulAut.conj g).toMonoidHom z = z * ⁅z⁻¹, g⁆ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            commutatorElement_def]
          group
        have hwv : ⁅w, ⁅z⁻¹, g⁆⁆ = 1 := by
          rw [commutatorElement_eq_one_iff_commute]
          exact ((Subgroup.mem_centralizer_iff.mp (hWhc hw)) _ (c.vhat_le_vv hα hv)).symm
        rw [e1, S46.commutatorElement_mul_right_conj, hwv, mul_one, mul_inv_cancel, mul_one]
        exact Subgroup.commutator_mem_commutator hw hz
      exact hmap ⟨s, hs, rfl⟩
    have hSU : S ≤ Usup (puAmalgam h.le) (p a) (p (a + 1)) := by
      have h1 : S ≤ Usup (puAmalgam h.le) (p (a + 4)) (p (a + 3)) := by
        rw [hS, Usup, zv_of_isMVtx _ hμ, Subgroup.commutator_comm]
        exact Subgroup.commutator_mono le_rfl (c.whv_le_qv_right hp ha (by omega) (by omega))
      have hx : Even (a - 4) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
      have e1 := c.hloc_eq_usup' hp hx (by omega) (by omega)
      have e2 := c.hloc_eq_usup hp hx (by omega) (by omega)
      rw [show a - 4 + 6 = a + 2 by omega, show a - 4 + 8 = a + 4 by omega,
        show a - 4 + 7 = a + 3 by omega] at e1
      rw [show a - 4 + 6 = a + 2 by omega, show a - 4 + 4 = a by omega,
        show a - 4 + 5 = a + 1 by omega] at e2
      rw [← e2, e1]
      exact h1
    have hx : Even (a - 4) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
    have hc4 := c.isCritical_of_isGoodPath hp hx (show a - 4 + 8 ≤ N by omega)
    have hs4 := c.straight_of_isGoodPath hp hx (show a - 4 + 4 ≤ N by omega)
    have hg4 := c.zh_ne_of_isGoodPath hp ha (by omega) (by omega)
    have hcard := c.card_critR hp.toIsNBPath (x := a - 4) (by omega) hc4 hs4
      (by rw [show a - 4 + 3 = a - 1 by omega, show a - 4 + 5 = a + 1 by omega]; exact hg4)
    rw [show a - 4 + 8 = a + 4 by omega] at hcard
    have hRS : critR (puAmalgam h.le) (p (a - 4)) (p (a + 4)) ≤ S :=
      Subgroup.commutator_mono (c.zm_le_whv_left hZV hp ha (by omega) (by omega)) le_rfl
    have hRne : critR (puAmalgam h.le) (p (a - 4)) (p (a + 4)) ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hcard
      have := Fintype.one_lt_card (α := F)
      omega
    obtain ⟨⟨r, hrR⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRne
    have hr1' : r ≠ 1 := fun h1 => hr1 (Subtype.ext h1)
    have hUs : Usup (puAmalgam h.le) (p a) (p (a + 1)) ≤ Uloc h.le L (p a) := by
      rw [c.usup_eq_uloc_inf_centralizer hψ hα hαβ]; exact inf_le_left
    have hUS := (NatSec.ofIsSum hψ).le_of_invariant hψs (fun l s hs => hSn l l.2 s hs)
      (hRS hrR) (hUs (hSU (hRS hrR))) hr1'
    have hfin : Finite ↥(Usup (puAmalgam h.le) (p a) (p (a + 1))) := Nat.finite_of_card_ne_zero
      (by rw [c.card_usup hψ hα hαβ]; exact pow_ne_zero _ Fintype.card_ne_zero)
    have hle' := Subgroup.card_le_of_le (hUS.trans hSU)
    rw [(NatSec.ofIsSum hψ).card_eq, c.card_usup hψ hα hαβ, Nat.card_eq_fintype_card] at hle'
    have hq1 := Fintype.one_lt_card (α := F)
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq1 (by norm_num)
    omega
  have hgen : W ≤ conjCl (stab (puAmalgam h.le) (p a)) Y ⊔ Vh :=
    sup_le ((conjCl_mono le_sup_left).trans le_sup_left) le_sup_right
  exact isSum_dual_of_offender h14 hSQ hsq hn hψs hker hKVh hKW le_sup_right hWK hNN hNQ hN2 hQT
    hTK hT le_sup_right hYK hYZ hYT hNTY hNTZ hgen

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
