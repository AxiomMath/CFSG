module

public import CFSG.Quasithin.MS93.S45C1
import CFSG.Quasithin.MS93.S4A431
public import CFSG.Quasithin.MS93.S45Gp

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

theorem stab_le_normalizer_vcirc (δ : Vtx (puAmalgam c.hyp.le)) :
    stab (puAmalgam c.hyp.le) δ ≤
      Subgroup.normalizer (Vcirc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) :=
  stab_le_normalizer_of_smul _ (vcirc_smul c.hyp) δ

theorem stab_le_normalizer_hloc (δ : Vtx (puAmalgam c.hyp.le)) :
    stab (puAmalgam c.hyp.le) δ ≤
      Subgroup.normalizer (Hloc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) :=
  stab_le_normalizer_of_smul _ (hloc_smul c.hyp) δ

theorem vcirc_le_vv (δ : Vtx (puAmalgam c.hyp.le)) :
    Vcirc c.hyp.le L δ ≤ Vv (puAmalgam c.hyp.le) δ :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((ltil_le_stab c.hyp δ).trans (stab_le_normalizer_vv c.hyp δ))

theorem vi_le_centralizer_zm {β μ : Vtx (puAmalgam c.hyp.le)} {i : ℕ} (hμ : IsMVtx _ μ)
    (hd : i + (puAmalgam c.hyp.le).treeGraph.dist β μ < 8) :
    Vi (puAmalgam c.hyp.le) β i ≤
      Subgroup.centralizer (ZM (puAmalgam c.hyp.le) μ : Set (puAmalgam c.hyp.le).Universal) := by
  refine (vi_le_centralizer_vi _ c.hyp.hyp20 c.bpos (i := i) (j := 0) (δ' := μ)
    (by rw [c.b8]; omega)).trans (Subgroup.centralizer_le ?_)
  rw [← zv_of_isMVtx _ hμ]
  exact zv_le_vi _ (by simp)

theorem commutator_vv_le_hloc {δ β : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hβ : (puAmalgam c.hyp.le).treeGraph.Adj δ β) {A : Subgroup (puAmalgam c.hyp.le).Universal}
    (hA : A ≤ Qv _ δ)
    (hcen : Vi (puAmalgam c.hyp.le) β 1 ≤ Subgroup.centralizer (A : Set _)) :
    ⁅Vv (puAmalgam c.hyp.le) δ, A⁆ ≤ Hloc c.hyp.le L δ := by
  have h := c.hyp
  have hVs : Vv (puAmalgam h.le) δ ≤ stab _ δ := (c.vv_le_qv' hδ).trans (qv_le_stab _ δ)
  have hVi : Vi (puAmalgam h.le) β 1 ≤ Vv _ δ :=
    vi_le_vi _ (by rw [tdist_comm, (SimpleGraph.dist_eq_one_iff_adj).mpr hβ])
  have hHn := c.stab_le_normalizer_hloc δ
  refine (Subgroup.commutator_mono (S4A.vv_le_vi_sup_commutator h c.full hδ hβ) le_rfl).trans ?_
  refine commutator_sup_left_le ((hVi.trans hVs).trans hHn)
    (((c.vcirc_le_vv δ).trans hVs).trans hHn) ?_ ?_
  · rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen]
    exact bot_le
  · exact Subgroup.commutator_mono le_rfl hA

section GoodPath

variable {p : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem isCritical_of_isGoodPath (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y)
    (hyN : y + 8 ≤ N) : IsCritical (puAmalgam c.hyp.le) (p y) (p (y + 8)) :=
  c.isCritical_symm (hp.crit y hy hyN)

theorem straight_of_isGoodPath (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y)
    (hyN : y + 4 ≤ N) :
    ∃ g ∈ stab (puAmalgam c.hyp.le) (p (y + 2)), g • p (y + 4) = p y := by
  obtain ⟨g, hg, hgx⟩ := hp.straight (y + 2) (hy.add even_two) (by omega) (by omega)
  refine ⟨g, hg, ?_⟩
  rw [show y + 2 + 2 = y + 4 by omega, show y + 2 - 2 = y by omega] at hgx
  exact hgx

theorem zh_ne_of_isGoodPath (hp : IsGoodPath _ p N) {y : ℕ} (hy : Even y) (h8 : 8 ≤ y)
    (hyN : y < N) : ZH (puAmalgam c.hyp.le) (p (y - 1)) ≠ ZH _ (p (y + 1)) := by
  intro heq
  have h := c.hyp
  obtain ⟨x, rfl⟩ : ∃ x, y = x + 8 := ⟨y - 8, by omega⟩
  have hx : Even x := (Nat.even_add.mp hy).mpr (by decide)
  have hc : IsCritical (puAmalgam h.le) (p x) (p (x + 8)) :=
    c.isCritical_of_isGoodPath hp hx (by omega)
  have hM8 := (c.isCritical_symm hc).1
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM8
  have ha7 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 7)) :=
    (hp.adj (x + 7) (by omega)).symm
  have ha9 : (puAmalgam h.le).treeGraph.Adj (p (x + 8)) (p (x + 9)) := hp.adj (x + 8) (by omega)
  have hW : Usup (puAmalgam h.le) (p (x + 8)) (p (x + 7)) = Usup _ (p (x + 8)) (p (x + 9)) := by
    rw [c.usup_eq_iff_zh_eq hψ hM8 ha7 ha9]
    rw [show x + 8 - 1 = x + 7 by omega, show x + 8 + 1 = x + 9 by omega] at heq
    exact heq
  have g6 : geo (puAmalgam h.le) (p (x + 8)) (p x) 2 = p (x + 6) := by
    rw [hp.eq_geo_rev (i := x) (j := x + 8) (k := x + 6) (by omega) (by omega) (by omega),
      show x + 8 - (x + 6) = 2 by omega]
  have hM6 := c.isMVtx_add hp.toIsNBPath (k := 6) (by omega) hc.1 (by decide)
  have ha67 : (puAmalgam h.le).treeGraph.Adj (p (x + 6)) (p (x + 7)) := hp.adj (x + 6) (by omega)
  have hR : critR (puAmalgam h.le) (p x) (p (x + 8)) ≤ Usup _ (p (x + 8)) (p (x + 7)) := by
    have hZ6 := c.critR_le_zloc' hc
    rw [g6] at hZ6
    rw [← c.uloc_inf_zh hψ hM8 ha7]
    exact le_inf (c.critR_le_uloc' hc) (hZ6.trans (zloc_le_zh h c.full hM6 ha67))
  rw [hW] at hR
  have hpe := hp.pe (x + 8) hy (by omega) hyN
  rw [show x + 8 - 8 = x by omega, show x + 8 + 1 = x + 9 by omega] at hpe
  apply hpe
  rw [Subgroup.le_normalizer_iff_commutator_le_right]
  refine (Subgroup.commutator_mono le_rfl ?_).trans hR
  rw [c.usup_eq_uloc_inf_centralizer hψ hM8 ha9]
  exact inf_le_left.trans (uloc_le_zm h c.full hM8)

theorem commutator_zm_qv_of_isGoodPath (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x)
    (h4 : 4 ≤ x) (hxN : x + 12 ≤ N) :
    critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ⊔ critR _ (p (x + 4)) (p (x + 12)) =
        Usup _ (p (x + 4)) (p (x + 5)) ∧
      ⁅ZM (puAmalgam c.hyp.le) (p (x + 4)), Qv _ (p (x + 6))⁆ = Usup _ (p (x + 4)) (p (x + 5)) ∧
      Usup (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 5)) ≤ Zloc c.hyp.le L (p (x + 6)) ∧
      Usup (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 5)) = Usup _ (p (x + 8)) (p (x + 7)) := by
  have hx4 : Even (x + 4) := hx.add (by decide)
  have hx8 : Even (x + 8) := hx.add (by decide)
  have hc0 := c.isCritical_of_isGoodPath hp hx (by omega)
  have hc4 : IsCritical (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 12)) := by
    have := c.isCritical_of_isGoodPath hp hx4 (by omega)
    rwa [show x + 4 + 8 = x + 12 by omega] at this
  have hs2 := c.straight_of_isGoodPath hp hx (by omega)
  have hs6 : ∃ g ∈ stab (puAmalgam c.hyp.le) (p (x + 6)), g • p (x + 8) = p (x + 4) := by
    have := c.straight_of_isGoodPath hp hx4 (by omega)
    rwa [show x + 4 + 2 = x + 6 by omega, show x + 4 + 4 = x + 8 by omega] at this
  have hgpd4 : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5)) := by
    have := c.zh_ne_of_isGoodPath hp hx4 (by omega) (by omega)
    rwa [show x + 4 - 1 = x + 3 by omega, show x + 4 + 1 = x + 5 by omega] at this
  have hgpd8 : ZH (puAmalgam c.hyp.le) (p (x + 7)) ≠ ZH _ (p (x + 9)) := by
    have := c.zh_ne_of_isGoodPath hp hx8 (by omega) (by omega)
    rwa [show x + 8 - 1 = x + 7 by omega, show x + 8 + 1 = x + 9 by omega] at this
  have hne : critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) ≠ critR _ (p (x + 4)) (p (x + 12)) := by
    refine c.critR_ne_of_not_le_normalizer hp.toIsNBPath (by omega) hc0 hc4 hs6 ?_
    have := hp.pe (x + 8) hx8 (by omega) (by omega)
    rwa [show x + 8 - 8 = x by omega, show x + 8 + 1 = x + 9 by omega] at this
  have h1 := c.commutator_zm_qv_eq_usup hp.toIsNBPath hxN hc0 hc4 hs2 hs6 hgpd4 hgpd8 hne
  exact ⟨h1.1, h1.2, c.usup_le_zloc hp.toIsNBPath hxN hc0 hc4 hs2 hs6 hgpd4 hgpd8 hne,
    c.usup_eq_usup hp.toIsNBPath hxN hc0 hc4 hs2 hs6 hgpd4 hgpd8 hne⟩

theorem critR_eq_usup_inf (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 8 ≤ N) :
    critR (puAmalgam c.hyp.le) (p x) (p (x + 8)) =
      Usup _ (p (x + 4)) (p (x + 3)) ⊓ Usup _ (p (x + 4)) (p (x + 5)) := by
  have h := c.hyp
  have hx4 : Even (x + 4) := hx.add (by decide)
  have hc0 := c.isCritical_of_isGoodPath hp hx (by omega)
  have hs2 := c.straight_of_isGoodPath hp hx (by omega)
  have hgpd4 : ZH (puAmalgam c.hyp.le) (p (x + 3)) ≠ ZH _ (p (x + 5)) := by
    have := c.zh_ne_of_isGoodPath hp hx4 (by omega) (by omega)
    rwa [show x + 4 - 1 = x + 3 by omega, show x + 4 + 1 = x + 5 by omega] at this
  have hM4 := c.isMVtx_add hp.toIsNBPath (k := 4) (by omega) hc0.1 (by decide)
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  have ha3 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 3)) :=
    (hp.adj (x + 3) (by omega)).symm
  have ha5 : (puAmalgam h.le).treeGraph.Adj (p (x + 4)) (p (x + 5)) := hp.adj (x + 4) (by omega)
  have hne35 : Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ≠ Usup _ (p (x + 4)) (p (x + 5)) :=
    fun heq => hgpd4 ((c.usup_eq_iff_zh_eq hψ hM4 ha3 ha5).mp heq)
  have hcard35 := c.card_usup_inf_usup hψ hM4 ha3 ha5 hne35
  have hfin35 : Finite ↥(Usup (puAmalgam h.le) (p (x + 4)) (p (x + 3)) ⊓
      Usup _ (p (x + 4)) (p (x + 5))) := Nat.finite_of_card_ne_zero (by
        rw [hcard35]; exact Fintype.card_ne_zero)
  exact Subgroup.eq_of_le_of_card_ge (c.critR_le_usup_inf hp.toIsNBPath hxN hc0 hs2)
    (by rw [hcard35, c.card_critR hp.toIsNBPath hxN hc0 hs2 hgpd4])

theorem hloc_eq_usup (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 12 ≤ N) :
    Hloc c.hyp.le L (p (x + 6)) = Usup (puAmalgam c.hyp.le) (p (x + 4)) (p (x + 5)) := by
  have h := c.hyp
  have hS := c.commutator_zm_qv_of_isGoodPath hp hx h4 hxN
  have hM0 : IsMVtx (puAmalgam h.le) (p 0) := hp.mvtx
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hM4 := hM (x + 4) (by omega) (hx.add (by decide))
  have hM6 := hM (x + 6) (by omega) (hx.add (by decide))
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  apply le_antisymm
  ·
    rw [← hS.2.1]
    have hc : IsCritical (puAmalgam h.le) (p (x + 6)) (p (x - 2)) := by
      have := hp.crit (x - 2) (by
        obtain ⟨k, hk⟩ := hx; exact ⟨k - 1, by omega⟩) (by omega)
      rwa [show x - 2 + 8 = x + 6 by omega] at this
    have hg : geo (puAmalgam h.le) (p (x + 6)) (p (x - 2)) 2 = p (x + 4) := by
      rw [hp.eq_geo_rev (i := x - 2) (j := x + 6) (k := x + 4) (by omega) (by omega) (by omega),
        show x + 6 - (x + 4) = 2 by omega]
    have hB := c.not_zm_le_bloc hc
    rw [hg] at hB
    exact c.hloc_le_commutator hM6 hM4
      (by rw [tdist_comm, hd (x + 4) (x + 6) (by omega) (by omega)]; omega) hB
  · rw [← hS.1]
    refine sup_le ?_ ?_
    ·
      rw [critR, Subgroup.commutator_comm]
      have hM8 := hM (x + 8) (by omega) (hx.add (by decide))
      have hM0' := hM x (by omega) hx
      refine (Subgroup.commutator_mono (c.zm_le_vv_of_dist hM8
        (by rw [hd (x + 6) (x + 8) (by omega) (by omega)]; omega)) le_rfl).trans ?_
      refine c.commutator_vv_le_hloc hM6 (β := p (x + 5)) (hp.adj (x + 5) (by omega)).symm ?_ ?_
      · exact zm_le_qv_of_dist_lt _ hM0' (by rw [hd x (x + 6) (by omega) (by omega), c.b8]; omega)
      · exact c.vi_le_centralizer_zm hM0'
          (by rw [tdist_comm, hd x (x + 5) (by omega) (by omega)]; omega)
    ·
      rw [critR]
      have hM12 := hM (x + 12) (by omega) (hx.add (by decide))
      refine (Subgroup.commutator_mono (c.zm_le_vv_of_dist hM4
        (by rw [tdist_comm, hd (x + 4) (x + 6) (by omega) (by omega)]; omega)) le_rfl).trans ?_
      refine c.commutator_vv_le_hloc hM6 (β := p (x + 7)) (hp.adj (x + 6) (by omega)) ?_ ?_
      · exact zm_le_qv_of_dist_lt _ hM12
          (by rw [tdist_comm, hd (x + 6) (x + 12) (by omega) (by omega), c.b8]; omega)
      · exact c.vi_le_centralizer_zm hM12 (by rw [hd (x + 7) (x + 12) (by omega) (by omega)]; omega)

theorem hloc_eq_usup' (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 12 ≤ N) :
    Hloc c.hyp.le L (p (x + 6)) = Usup (puAmalgam c.hyp.le) (p (x + 8)) (p (x + 7)) := by
  rw [c.hloc_eq_usup hp hx h4 hxN, (c.commutator_zm_qv_of_isGoodPath hp hx h4 hxN).2.2.2]

theorem card_hloc (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h4 : 4 ≤ x)
    (hxN : x + 12 ≤ N) : Nat.card ↥(Hloc c.hyp.le L (p (x + 6))) = Fintype.card F ^ 2 := by
  have h := c.hyp
  have hM4 : IsMVtx (puAmalgam h.le) (p (x + 4)) := by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := x + 4) (by omega) hp.mvtx
      (hx.add (by decide))
    rwa [zero_add] at this
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h c.via hM4
  rw [c.hloc_eq_usup hp hx h4 hxN]
  exact c.card_usup hψ hM4 (hp.adj (x + 4) (by omega))

theorem commutator_vv_vv (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h10 : 10 ≤ x)
    (hxN : x + 10 ≤ N) :
    ⁅Vv (puAmalgam c.hyp.le) (p x), Vv _ (p (x + 4))⁆ = critR _ (p (x - 2)) (p (x + 6)) ∧
      Hloc c.hyp.le L (p x) ⊓ Hloc c.hyp.le L (p (x + 4)) = critR _ (p (x - 2)) (p (x + 6)) := by
  have h := c.hyp
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hx2 : Even (x - 2) := by obtain ⟨k, hk⟩ := hx; exact ⟨k - 1, by omega⟩
  have hx4 : Even (x - 4) := by obtain ⟨k, hk⟩ := hx; exact ⟨k - 2, by omega⟩
  have hM0 := hM x (by omega) hx
  have hM4 := hM (x + 4) (by omega) (hx.add (by decide))
  have hH0 : Hloc c.hyp.le L (p x) = Usup (puAmalgam h.le) (p (x + 2)) (p (x + 1)) := by
    have := c.hloc_eq_usup' hp (x := x - 6) (by obtain ⟨k, hk⟩ := hx; exact ⟨k - 3, by omega⟩)
      (by omega) (by omega)
    rwa [show x - 6 + 6 = x by omega, show x - 6 + 8 = x + 2 by omega,
      show x - 6 + 7 = x + 1 by omega] at this
  have hH4 : Hloc c.hyp.le L (p (x + 4)) = Usup (puAmalgam h.le) (p (x + 2)) (p (x + 3)) := by
    have := c.hloc_eq_usup hp (x := x - 2) hx2 (by omega) (by omega)
    rwa [show x - 2 + 6 = x + 4 by omega, show x - 2 + 4 = x + 2 by omega,
      show x - 2 + 5 = x + 3 by omega] at this
  have hR : critR (puAmalgam h.le) (p (x - 2)) (p (x + 6)) =
      Usup (puAmalgam h.le) (p (x + 2)) (p (x + 1)) ⊓ Usup _ (p (x + 2)) (p (x + 3)) := by
    have := c.critR_eq_usup_inf hp (x := x - 2) hx2 (by omega) (by omega)
    rwa [show x - 2 + 8 = x + 6 by omega, show x - 2 + 4 = x + 2 by omega,
      show x - 2 + 3 = x + 1 by omega, show x - 2 + 5 = x + 3 by omega] at this
  have hHH : Hloc c.hyp.le L (p x) ⊓ Hloc c.hyp.le L (p (x + 4)) =
      critR (puAmalgam h.le) (p (x - 2)) (p (x + 6)) := by
    rw [hH0, hH4, hR]
  refine ⟨le_antisymm ?_ ?_, hHH⟩
  · rw [← hHH]
    refine le_inf ?_ ?_
    · refine c.commutator_vv_le_hloc hM0 (β := p (x + 1)) (hp.adj x (by omega)) ?_ ?_
      · exact vi_le_qv _ (by rw [tdist_comm, hd x (x + 4) (by omega) (by omega), c.b8]; omega)
      · exact vi_le_centralizer_vi _ h.hyp20 c.bpos
          (by rw [hd (x + 1) (x + 4) (by omega) (by omega), c.b8]; omega)
    · rw [Subgroup.commutator_comm]
      refine c.commutator_vv_le_hloc hM4 (β := p (x + 3)) (hp.adj (x + 3) (by omega)).symm ?_ ?_
      · exact vi_le_qv _ (by rw [hd x (x + 4) (by omega) (by omega), c.b8]; omega)
      · exact vi_le_centralizer_vi _ h.hyp20 c.bpos
          (by rw [tdist_comm, hd x (x + 3) (by omega) (by omega), c.b8]; omega)
  · rw [critR]
    exact Subgroup.commutator_mono
      (c.zm_le_vv_of_dist (hM (x - 2) (by omega) hx2)
        (by rw [tdist_comm, hd (x - 2) x (by omega) (by omega)]; omega))
      (c.zm_le_vv_of_dist (hM (x + 6) (by omega) (hx.add (by decide)))
        (by rw [hd (x + 4) (x + 6) (by omega) (by omega)]; omega))

theorem commutator_vv_zm (hp : IsGoodPath _ p N) {x : ℕ} (hx : Even x) (h10 : 10 ≤ x)
    (hxN : x + 10 ≤ N) :
    ⁅Vv (puAmalgam c.hyp.le) (p x), ZM _ (p (x + 6))⁆ = critR _ (p (x - 2)) (p (x + 6)) := by
  have h := c.hyp
  have hM : ∀ k, k ≤ N → Even k → IsMVtx (puAmalgam h.le) (p k) := fun k hk hev => by
    have := c.isMVtx_add hp.toIsNBPath (x := 0) (k := k) (by omega) hp.mvtx hev
    rwa [zero_add] at this
  have hd : ∀ i j, i ≤ j → j ≤ N → (puAmalgam h.le).treeGraph.dist (p i) (p j) = j - i :=
    fun i j hij hj => hp.dist_eq' hij hj
  have hx2 : Even (x - 2) := by obtain ⟨k, hk⟩ := hx; exact ⟨k - 1, by omega⟩
  apply le_antisymm
  · rw [← (c.commutator_vv_vv hp hx h10 hxN).1]
    refine Subgroup.commutator_mono le_rfl ?_
    have := zv_le_vi (puAmalgam h.le) (δ := p (x + 4)) (ρ := p (x + 6)) (i := 2)
      (by rw [hd (x + 4) (x + 6) (by omega) (by omega)]; omega)
    rwa [zv_of_isMVtx _ (hM (x + 6) (by omega) (hx.add (by decide)))] at this
  · rw [critR]
    exact Subgroup.commutator_mono
      (c.zm_le_vv_of_dist (hM (x - 2) (by omega) hx2)
        (by rw [tdist_comm, hd (x - 2) x (by omega) (by omega)]; omega)) le_rfl

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
