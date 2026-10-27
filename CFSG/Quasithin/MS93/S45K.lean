module

public import CFSG.Quasithin.MS93.S45M3

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

theorem commutator_mid_le (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N) {a : ℕ}
    (ha : Even a) (h24 : 24 ≤ a) (haN : a + 24 ≤ N) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (ZM _ (p (a + 4))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)), Qv (puAmalgam c.hyp.le) (p (a + 1))⁆ ≤
      ZM _ (p (a + 4)) ⊔ (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  set C := conjCl (stab (puAmalgam h.le) (p a)) (ZM (puAmalgam h.le) (p (a + 4))) with hC
  set W := C ⊔ Vh with hW
  set Y := ZM (puAmalgam h.le) (p (a + 4)) ⊔ Vh with hY
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Wμ := whv h (p (a + 4)) (p (a + 2)) with hWμ
  have hKVh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hQK : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hZμQ : ZM (puAmalgam h.le) (p (a + 4)) ≤ Qv _ (p a) := zm_le_qv_of_dist_lt _ hμ (by
    rw [tdist_comm, hd a (a + 4) (by omega) (by omega), c.b8]; omega)
  have hVhQ : Vh ≤ Qv (puAmalgam h.le) (p a) := (c.vhat_le_vv hα).trans (c.vv_le_qv' hα)
  have hTK : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab (puAmalgam h.le) (p a) :=
    qv_le_stab_of_adj _ hαβ.symm
  have hQT : Qv (puAmalgam h.le) (p a) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hα hαβ
  have hZμWh : ZM (puAmalgam h.le) (p (a + 4)) ≤ Wh :=
    c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hVhWh : Vh ≤ Wh := c.vhat_le_whv' hZV hp ha (by omega) (by omega)
  have hWWh : W ≤ Wh := sup_le (conjCl_le_of_le_normalizer hZμWh hKWh) hVhWh
  have hWhQ : ⁅Wh, Qv (puAmalgam h.le) (p a)⁆ ≤ ZM _ (p a) :=
    c.commutator_whv_qv_le' hZV hp ha (by omega) (by omega)
  have hNQ : ⁅W, Qv (puAmalgam h.le) (p a)⁆ ≤ Vh :=
    ((Subgroup.commutator_mono hWWh le_rfl).trans hWhQ).trans le_sup_right
  have hZγVh : ZM (puAmalgam h.le) (p (a + 2)) ≤ Vh :=
    c.zm_le_vhat_right hZV hp ha (by omega) (by omega)
  have hYT : ⁅Y, Qv (puAmalgam h.le) (p (a + 1))⁆ ≤ Vh := by
    refine S46.commutator_sup_le_of_le_normalizer hKVh (hZμQ.trans hQK) (hVhQ.trans hQK) ?_
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hTK.trans hKVh))
    have h1 := c.commutator_vhat_qv_le_left hZV hp ha (by omega) (by omega)
    have h2 := c.zm_le_vhat_right hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rw [show a + 2 + 2 = a + 4 by omega] at h2
    exact (Subgroup.commutator_mono h2 le_rfl).trans (h1.trans (sup_le le_sup_right hZγVh))
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
  rw [Subgroup.commutator_comm]
  refine (Subgroup.commutator_mono hTWQ le_rfl).trans ?_
  refine S46.commutator_sup_le_of_le_normalizer hTY hWμT hQT ?_ ?_
  · exact (Subgroup.commutator_mono le_rfl hWQμ).trans (hWμQμ.trans le_sup_left)
  · rw [Subgroup.commutator_comm]
    exact hNQ.trans le_sup_right

theorem commutator_whv_qv_le_vhat (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N)
    {a : ℕ} (ha : Even a) (h24 : 24 ≤ a) (haN : a + 24 ≤ N) :
    ⁅whv c.hyp (p a) (p (a + 2)), Qv (puAmalgam c.hyp.le) (p (a + 1))⁆ ≤
      (Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) ⊔
        (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) := by
  have h := c.hyp
  have h20 := h.hyp20
  obtain ⟨p', hp', hpp', hU1, hU3⟩ := c.exists_branch hp ha (by omega) (by omega)
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa1 : p' (a + 1) = p (a + 1) := hpp' (a + 1) (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) (by omega)
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hαβ : (puAmalgam h.le).treeGraph.Adj (p a) (p (a + 1)) := hp.adj a (by omega)
  have hγβ : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
    (hp.adj (a + 1) (by omega)).symm
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  set Vγ := Vcirc h.le L (p (a + 2)) ⊔ ZM (puAmalgam h.le) (p (a + 2)) with hVγ
  have h₁ := c.commutator_mid_le hZV hQ4 hp ha h24 haN
  have h₂ := c.commutator_mid_le hZV hQ4 hp' ha h24 haN
  rw [hpa, hpa1] at h₂
  have hsup := c.whv_le_sup_of_branch hZV hp ha h24 haN hp' hpp' hU1 hU3
  have hTα : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab (puAmalgam h.le) (p a) :=
    qv_le_stab_of_adj _ hαβ.symm
  have hTγ : Qv (puAmalgam h.le) (p (a + 1)) ≤ stab (puAmalgam h.le) (p (a + 2)) :=
    qv_le_stab_of_adj _ hγβ.symm
  have hTn : Qv (puAmalgam h.le) (p (a + 1)) ≤ Subgroup.normalizer ((Vγ ⊔ Vh : Subgroup _) :
      Set (puAmalgam h.le).Universal) :=
    le_normalizer_sup (hTγ.trans (le_normalizer_sup (c.stab_le_normalizer_vcirc _)
      (stab_le_normalizer_zm _ _))) (hTα.trans (le_normalizer_sup (c.stab_le_normalizer_vcirc _)
        (stab_le_normalizer_zm _ _)))
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    stab_le_normalizer_qv _ _
  have hVhQ : Vh ≤ Qv (puAmalgam h.le) (p a) := (c.vhat_le_vv hα).trans (c.vv_le_qv' hα)
  have hQT : Qv (puAmalgam h.le) (p a) ≤ Qv _ (p (a + 1)) := qv_le_qv _ h20 hα hαβ
  have hW₁T : conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p (a + 4))) ⊔ Vh ≤
      Qv (puAmalgam h.le) (p (a + 1)) := by
    have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
    refine (sup_le (conjCl_le_of_le_normalizer (zm_le_qv_of_dist_lt _ hμ ?_) hKQ) hVhQ).trans hQT
    rw [tdist_comm, hp.dist_eq' (by omega) (by omega), c.b8]; omega
  have hW₂T : conjCl (stab (puAmalgam h.le) (p a)) (ZM _ (p' (a + 4))) ⊔ Vh ≤
      Qv (puAmalgam h.le) (p (a + 1)) := by
    have hμ := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
    refine (sup_le (conjCl_le_of_le_normalizer (zm_le_qv_of_dist_lt _ hμ ?_) hKQ) hVhQ).trans hQT
    rw [← hpa, tdist_comm, hp'.dist_eq' (by omega) (by omega), c.b8]; omega
  have hZ₁ : ZM (puAmalgam h.le) (p (a + 4)) ≤ Vγ := by
    have := c.zm_le_vhat_right hZV hp (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rwa [show a + 2 + 2 = a + 4 by omega] at this
  have hZ₂ : ZM (puAmalgam h.le) (p' (a + 4)) ≤ Vγ := by
    have := c.zm_le_vhat_right hZV hp' (a := a + 2) (ha.add even_two) (by omega) (by omega)
    rwa [show a + 2 + 2 = a + 4 by omega, hpa2] at this
  refine (Subgroup.commutator_mono hsup le_rfl).trans ?_
  refine S46.commutator_sup_le_of_le_normalizer hTn hW₁T hW₂T ?_ ?_
  · exact h₁.trans (sup_le (hZ₁.trans le_sup_left) le_sup_right)
  · exact h₂.trans (sup_le (hZ₂.trans le_sup_left) le_sup_right)

theorem commutator_whv_qv_le_vhat_left (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N)
    {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 27 ≤ N) :
    ⁅whv c.hyp (p (a + 2)) (p a), Qv (puAmalgam c.hyp.le) (p (a + 1))⁆ ≤
      (Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)) ⊔
        (Vcirc c.hyp.le L (p (a + 2)) ⊔ ZM _ (p (a + 2))) := by
  have hr := c.isGoodPath_rev hp (m := a + 26) (ha.add (by decide)) (by omega) (by omega)
  have := c.commutator_whv_qv_le_vhat hZV hQ4 hr (a := 24) (by decide) le_rfl (by omega)
  rwa [show a + 26 - 24 = a + 2 by omega, show a + 26 - (24 + 2) = a by omega,
    show a + 26 - (24 + 1) = a + 1 by omega] at this

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
