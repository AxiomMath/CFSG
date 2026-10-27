module

public import CFSG.Quasithin.MS93.S45Phi3
public import CFSG.Quasithin.MS93.S45Cen

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

variable {p p' : ℕ → Vtx (puAmalgam c.hyp.le)} {N : ℕ}

theorem commutator_vhat_le_of_le (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a)
    (haN : a + 2 ≤ N) {X : Subgroup (puAmalgam c.hyp.le).Universal}
    (hX : X ≤ ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊔
      whv c.hyp (p a) (p (a + 2))) :
    ⁅X, Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)⁆ ≤
      ⁅⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
        ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆⁆ := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  have hQs : Qv (puAmalgam h.le) (p a) ≤ stab (puAmalgam h.le) (p a) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hVQ : ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ ≤ Qv (puAmalgam h.le) (p a) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h _).trans hKQ)
  have hKWh : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (whv h (p a) (p (a + 2)) : Set _) := S4A.le_normalizer_conjCl _ _
  have hWhC : whv h (p a) (p (a + 2)) ≤ Subgroup.centralizer
      ((Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) : Subgroup _) : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVcV : Vcirc h.le L (p a) ≤ ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ :=
    Subgroup.commutator_mono (c.vv_le_qv' hα) le_rfl
  have hZn : Vcirc h.le L (p a) ≤ Subgroup.normalizer (ZM (puAmalgam h.le) (p a) : Set _) :=
    (hVcV.trans (hVQ.trans hQs)).trans (stab_le_normalizer_zm _ _)
  have hZc : ZM (puAmalgam h.le) (p a) ≤ Subgroup.centralizer (Qv (puAmalgam h.le) (p a) : Set _) :=
    zm_le_centralizer_qv _ h20 hα
  rw [Subgroup.commutator_le]
  intro x hx u hu
  have hx' := hX hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((hVQ.trans hQs).trans hKWh)] at hx'
  obtain ⟨v, hv, w, hw, rfl⟩ := hx'
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZn] at hu
  obtain ⟨u₀, hu₀, z, hz, rfl⟩ := hu
  have hu₀V : u₀ ∈ Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) := Subgroup.mem_sup_left hu₀
  have hzV : z ∈ Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) := Subgroup.mem_sup_right hz
  have hwu : ⁅w, u₀ * z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp (hWhC hw) _ (Subgroup.mul_mem _ hu₀V hzV)).symm
  have hvz : ⁅v, z⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_centralizer_iff.mp (hZc hz) v (hVQ hv))
  rw [S46.commutatorElement_mul_left_conj, hwu, mul_one, mul_inv_cancel, one_mul,
    S46.commutatorElement_mul_right_conj, hvz, mul_one, mul_inv_cancel, mul_one]
  exact Subgroup.commutator_mem_commutator hv (hVcV hu₀)

theorem commutator_top_vhat_eq {μ : Vtx (puAmalgam c.hyp.le)} (hp : IsGoodPath _ p N) {a : ℕ}
    (ha : Even a) (h10 : 10 ≤ a) (haN : a + 10 ≤ N)
    (hμs : Vcirc c.hyp.le L μ ⊔ ZM _ μ ≤ stab (puAmalgam c.hyp.le) (p a))
    (hμQ : Vcirc c.hyp.le L μ ⊔ ZM _ μ ≤ Qv (puAmalgam c.hyp.le) (p a))
    {R : Subgroup (puAmalgam c.hyp.le).Universal}
    (hRc : R ≤ stabCenter (puAmalgam c.hyp.le) (p a))
    (hμ : ⁅Vcirc c.hyp.le L μ ⊔ ZM _ μ, Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)⁆ ≤ R) :
    ⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔
        whv c.hyp (p a) (p (a + 2)), Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)⁆ ≤
      ⁅⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L μ ⊔ ZM _ μ) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2)), Vcirc c.hyp.le L (p a) ⊔ ZM _ (p a)⁆ := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 10 := ⟨a - 10, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 4) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  set Vh := Vcirc h.le L (p (k + 10)) ⊔ ZM (puAmalgam h.le) (p (k + 10)) with hVh
  set Wh := whv h (p (k + 10)) (p (k + 10 + 2)) with hWh
  set X := conjCl (stab (puAmalgam h.le) (p (k + 10))) (Vcirc h.le L μ ⊔ ZM _ μ) ⊔ Wh with hX
  have hKVh : stab (puAmalgam h.le) (p (k + 10)) ≤ Subgroup.normalizer (Vh : Set _) :=
    le_normalizer_sup (c.stab_le_normalizer_vcirc _) (stab_le_normalizer_zm _ _)
  have hKWh : stab (puAmalgam h.le) (p (k + 10)) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hKX : stab (puAmalgam h.le) (p (k + 10)) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hKWh
  have hWhQ : Wh ≤ Qv (puAmalgam h.le) (p (k + 10)) := c.whv_le_qv_of_dist hγ hd2 (by simp)
  have hXQ : X ≤ Qv (puAmalgam h.le) (p (k + 10)) :=
    sup_le (conjCl_le_of_le_normalizer hμQ (stab_le_normalizer_qv _ _)) hWhQ
  have hXs : X ≤ stab (puAmalgam h.le) (p (k + 10)) := hXQ.trans (qv_le_stab _ _)
  have hVhs : Vh ≤ stab (puAmalgam h.le) (p (k + 10)) :=
    (c.vhat_le_vv hα).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _))
  have hP : ⁅X, Vh⁆ ≤ R := c.commutator_conjCl_sup_vhat_le hα hγ hd2 hμs
    (c.stab_le_normalizer_of_le_stabCenter hRc) hμ
  have hZc := zm_le_centralizer_qv _ h20 hα
  have hcov : Vh ≤ ⁅stab (puAmalgam h.le) (p (k + 10)), Vh⁆ ⊔ ZM _ (p (k + 10)) := by
    have hVL : stab (puAmalgam h.le) (p (k + 10)) ≤
        Subgroup.normalizer ((⁅Vh, Ltil h.le L (p (k + 10))⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hKVh (stab_le_normalizer_ltil h _)
    calc Vh = (⁅Vh, Ltil h.le L (p (k + 10))⁆ ⊓ Vh) ⊔ ZM _ (p (k + 10)) :=
          (c.sup_inf_eq_of_dual hα hψs hψ hd hVL le_rfl).symm
      _ ≤ ⁅stab (puAmalgam h.le) (p (k + 10)), Vh⁆ ⊔ ZM _ (p (k + 10)) := by
          refine sup_le_sup_right (inf_le_left.trans ?_) _
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mono (ltil_le_stab h _) le_rfl
  refine commutator_le_of_trivial_top le_sup_left
    (sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hKX) le_sup_right) hKVh hcov
    le_sup_right ?_ ?_ le_rfl
  · intro x hx z hz
    rw [commutatorElement_eq_one_iff_commute]
    exact Subgroup.mem_centralizer_iff.mp (hZc hz) x (hXQ hx)
  · intro x hx u hu g hg
    have hgs : g ∈ stab (puAmalgam h.le) (p (k + 10)) :=
      (sup_le (sup_le le_rfl hXs) hVhs) hg
    exact c.commute_of_mem_stabCenter (hRc (hP (Subgroup.commutator_mem_commutator hx hu))) hgs

theorem hloc_le_commutator_qv_ltil (hZV : c.HZV) (hQ4 : c.HQ4) (hp : IsGoodPath _ p N)
    (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    Hloc c.hyp.le L (p a) ≤
      ⁅⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
        ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆⁆ := by
  have h := c.hyp
  have h20 := h.hyp20
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hμ := c.isMVtx_of_isGoodPath hp (k := a + 4) (by omega) (ha.add (by decide))
  have hμ' := c.isMVtx_of_isGoodPath hp' (k := a + 4) (by omega) (ha.add (by decide))
  have ha2 : Even (a - 2) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have ha6 : Even (a - 6) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hpa : p' a = p a := hpp' a (by omega)
  have hpa1 : p' (a + 1) = p (a + 1) := hpp' (a + 1) (by omega)
  have hpa2 : p' (a + 2) = p (a + 2) := hpp' (a + 2) le_rfl
  have hpam : p' (a - 2) = p (a - 2) := hpp' (a - 2) (by omega)
  have hF8 := c.sup_whv_eq hZV hQ4 hp hp' ha h34 haN hpp' hU3
  have hXQ := c.top_le_qv hp hp' ha (by omega) hpp'
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hvv₁ := c.commutator_vv_vv hp (x := a) ha (by omega) (by omega)
  have hvv₂ := c.commutator_vv_vv hp' (x := a) ha (by omega) (by omega)
  rw [hpa, hpam] at hvv₂
  have hHc : Hloc h.le L (p a) ≤ stabCenter (puAmalgam h.le) (p a) :=
    (Subgroup.commutator_mono (c.vcirc_le_vv _) le_rfl).trans
      (c.commutator_vv_qv_le_stabCenter hα)
  have hR₁H : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ≤ Hloc h.le L (p a) := by
    rw [← hvv₁.2]; exact inf_le_left
  have hR₂H : critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) ≤ Hloc h.le L (p a) := by
    rw [← hvv₂.2]; exact inf_le_left
  have hμs : Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) ≤ Qv (puAmalgam h.le) (p a) :=
    (S4A.le_conjCl _ _).trans (le_sup_left.trans (le_sup_left.trans hXQ))
  have hμs' : Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4)) ≤ Qv (puAmalgam h.le) (p a) :=
    (S4A.le_conjCl _ _).trans (le_sup_left.trans (le_sup_right.trans hXQ))
  have hvhat : ZM (puAmalgam h.le) (p (a - 2)) ≤ Vcirc h.le L (p a) ⊔ ZM _ (p a) :=
    c.zm_le_vhat_left' hZV hp ha (by omega) (by omega)
  have hR₁V : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ≤
      ⁅⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆,
        ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆⁆ := by
    have hZ6 : ZM (puAmalgam h.le) (p (a + 6)) ≤ Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4)) := by
      have := c.zm_le_vhat_right hZV hp (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
      rwa [show a + 4 + 2 = a + 6 by omega] at this
    have hZX : ZM (puAmalgam h.le) (p (a + 6)) ≤ conjCl (stab (puAmalgam h.le) (p a))
        (Vcirc h.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔ whv h (p a) (p (a + 2)) :=
      hZ6.trans ((S4A.le_conjCl _ _).trans le_sup_left)
    rw [critR, Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono hZX hvhat).trans ?_
    refine (c.commutator_top_vhat_eq hp ha (by omega) (by omega) (hμs.trans (qv_le_stab _ _))
      hμs (hR₁H.trans hHc) ((Subgroup.commutator_mono (c.vhat_le_vv hμ) (c.vhat_le_vv hα)).trans
        (by rw [Subgroup.commutator_comm, hvv₁.1]))).trans ?_
    exact c.commutator_vhat_le_of_le hp ha (by omega) (hF8 ▸ le_sup_left)
  have hR₂V : critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) ≤
      ⁅⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆,
        ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆⁆ := by
    have hZ6 : ZM (puAmalgam h.le) (p' (a + 6)) ≤
        Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4)) := by
      have := c.zm_le_vhat_right hZV hp' (a := a + 4) (ha.add (by decide)) (by omega) (by omega)
      rwa [show a + 4 + 2 = a + 6 by omega] at this
    have hZX : ZM (puAmalgam h.le) (p' (a + 6)) ≤ conjCl (stab (puAmalgam h.le) (p a))
        (Vcirc h.le L (p' (a + 4)) ⊔ ZM _ (p' (a + 4))) ⊔ whv h (p a) (p (a + 2)) :=
      hZ6.trans ((S4A.le_conjCl _ _).trans le_sup_left)
    rw [critR, Subgroup.commutator_comm]
    refine (Subgroup.commutator_mono hZX hvhat).trans ?_
    refine (c.commutator_top_vhat_eq hp ha (by omega) (by omega) (hμs'.trans (qv_le_stab _ _))
      hμs' (hR₂H.trans hHc) ((Subgroup.commutator_mono (c.vhat_le_vv hμ') (c.vhat_le_vv hα)).trans
        (by rw [Subgroup.commutator_comm, hvv₂.1]))).trans ?_
    exact c.commutator_vhat_le_of_le hp ha (by omega) (hF8 ▸ le_sup_right)
  have hRR : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ⊓
      critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) = ⊥ := by
    have e₁ := c.critR_eq_usup_inf hp (x := a - 2) ha2 (by omega) (by omega)
    have e₂ := c.critR_eq_usup_inf hp' (x := a - 2) ha2 (by omega) (by omega)
    rw [show a - 2 + 8 = a + 6 by omega, show a - 2 + 4 = a + 2 by omega,
      show a - 2 + 3 = a + 1 by omega, show a - 2 + 5 = a + 3 by omega] at e₁ e₂
    rw [hpam, hpa2, hpa1] at e₂
    have hadj1 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 1)) :=
      (hp.adj (a + 1) (by omega)).symm
    have hadj3 : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p (a + 3)) := hp.adj (a + 2) (by omega)
    have hadj3' : (puAmalgam h.le).treeGraph.Adj (p (a + 2)) (p' (a + 3)) := by
      have := hp'.adj (a + 2) (by omega)
      rwa [hpa2] at this
    obtain ⟨ψγ, -, hψγ⟩ := exists_natural_Uloc h c.via hγ
    have h13 : Usup (puAmalgam h.le) (p (a + 2)) (p (a + 1)) ≠ Usup _ (p (a + 2)) (p (a + 3)) := by
      rw [Ne, c.usup_eq_iff_zh_eq hψγ hγ hadj1 hadj3]
      have := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
      rwa [show a + 2 - 1 = a + 1 by omega, show a + 2 + 1 = a + 3 by omega] at this
    have hb := c.usup_inf_inf_eq_bot hγ hadj1 hadj3 hadj3' h13 (Ne.symm hU1) hU3
    rw [eq_bot_iff, ← hb, e₁, e₂]
    exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (inf_le_right.trans inf_le_right)
  have hcard₁ : Nat.card ↥(critR (puAmalgam h.le) (p (a - 2)) (p (a + 6))) = Fintype.card F := by
    have := c.card_critR hp.toIsNBPath (x := a - 2) (by omega)
      (c.isCritical_of_isGoodPath hp ha2 (by omega)) (c.straight_of_isGoodPath hp ha2 (by omega))
      (by
        have := c.zh_ne_of_isGoodPath hp (y := a + 2) (ha.add even_two) (by omega) (by omega)
        rwa [show a + 2 - 1 = a - 2 + 3 by omega, show a + 2 + 1 = a - 2 + 5 by omega] at this)
    rwa [show a - 2 + 8 = a + 6 by omega] at this
  have hcard₂ : Nat.card ↥(critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6))) = Fintype.card F := by
    have := c.card_critR hp'.toIsNBPath (x := a - 2) (by omega)
      (c.isCritical_of_isGoodPath hp' ha2 (by omega))
      (c.straight_of_isGoodPath hp' ha2 (by omega))
      (by
        have := c.zh_ne_of_isGoodPath hp' (y := a + 2) (ha.add even_two) (by omega) (by omega)
        rwa [show a + 2 - 1 = a - 2 + 3 by omega, show a + 2 + 1 = a - 2 + 5 by omega] at this)
    rwa [show a - 2 + 8 = a + 6 by omega, hpam] at this
  have hcardH : Nat.card ↥(Hloc h.le L (p a)) = Fintype.card F ^ 2 := by
    have := c.card_hloc hp (x := a - 6) ha6 (by omega) (by omega)
    rwa [show a - 6 + 6 = a by omega] at this
  have hab : critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) ≤
      Subgroup.centralizer (critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) : Set _) := by
    intro r₂ hr₂
    rw [Subgroup.mem_centralizer_iff]
    intro r₁ hr₁
    obtain ⟨r₁', -, rfl⟩ := hHc (hR₁H hr₁)
    exact c.commute_of_mem_stabCenter (hHc (hR₂H hr₂)) r₁'.2
  have hfin : Finite ↥(Hloc h.le L (p a)) := Nat.finite_of_card_ne_zero (by
    rw [hcardH]; exact pow_ne_zero _ Fintype.card_ne_zero)
  have hHeq : critR (puAmalgam h.le) (p (a - 2)) (p (a + 6)) ⊔
      critR (puAmalgam h.le) (p (a - 2)) (p' (a + 6)) = Hloc h.le L (p a) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hR₁H hR₂H) (by
      rw [card_sup_of_commute hab hRR, hcard₁, hcard₂, hcardH, sq])
  rw [← hHeq]
  exact sup_le hR₁V hR₂V

theorem uloc_le_commutator_qv_ltil (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1))) :
    Uloc c.hyp.le L (p a) ≤
      ⁅⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆,
        ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆⁆ := by
  have h := c.hyp
  have hα := c.isMVtx_of_isGoodPath hp (k := a) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := a + 2) (by omega) (ha.add even_two)
  have hd2 : (puAmalgam h.le).treeGraph.dist (p a) (p (a + 2)) = 2 := by
    rw [hp.dist_eq' (i := a) (j := a + 2) (by omega) (by omega)]; omega
  have ha4 : Even (a - 4) := (Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))
  have hF9 := c.inf_whv_sup_vhat h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  set V := ⁅Qv (puAmalgam h.le) (p a), Ltil h.le L (p a)⁆ with hV
  set Wh := whv h (p a) (p (a + 2)) with hWh
  set Vh := Vcirc h.le L (p a) ⊔ ZM (puAmalgam h.le) (p a) with hVh
  have hKQ : stab (puAmalgam h.le) (p a) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p a) : Set _) := stab_le_normalizer_qv _ _
  have hKV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ (stab_le_normalizer_ltil h _)
  have hKWh : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hWhC : Wh ≤ Subgroup.centralizer (Vh : Set _) :=
    (c.whv_le_centralizer_vv hγ hd2).trans (Subgroup.centralizer_le (c.vhat_le_vv hα))
  have hVhs : Vh ≤ stab (puAmalgam h.le) (p a) :=
    (c.vhat_le_vv hα).trans ((c.vv_le_qv' hα).trans (qv_le_stab _ _))
  set R := critR (puAmalgam h.le) (p (a - 4)) (p (a + 4)) with hR
  have hRne : R ≠ ⊥ := by
    have := c.critR_ne_bot_of_isGoodPath hp (a := a - 2)
      ((Nat.even_sub (by omega)).mpr (iff_of_true ha (by decide))) (by omega) (by omega)
    rwa [show a - 2 - 2 = a - 4 by omega, show a - 2 + 6 = a + 4 by omega] at this
  have hRU : R ≤ Uloc h.le L (p a) := by
    have e := c.critR_eq_usup_inf hp (x := a - 4) ha4 (by omega) (by omega)
    rw [show a - 4 + 8 = a + 4 by omega, show a - 4 + 4 = a by omega,
      show a - 4 + 5 = a + 1 by omega] at e
    rw [hR, e]
    refine inf_le_right.trans ?_
    rw [c.usup_eq_uloc_inf_centralizer hψ hα (hp.adj a (by omega))]
    exact inf_le_left
  have hZ₁ : ZM (puAmalgam h.le) (p (a - 4)) ≤ Wh :=
    c.zm_le_whv_left hZV hp ha (by omega) (by omega)
  have hZ₂ : ZM (puAmalgam h.le) (p (a + 4)) ≤ Wh :=
    c.zm_le_whv_right hZV hp ha (by omega) (by omega)
  have hdec : ∀ z ∈ Wh, ∃ v ∈ V ⊓ Wh, ∃ u ∈ Vh, v * u = z := by
    intro z hz
    rw [← hF9, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      (hVhs.trans (le_normalizer_inf hKV hKWh))] at hz
    obtain ⟨v, hv, u, hu, rfl⟩ := hz
    exact ⟨v, hv, u, hu, rfl⟩
  have hRV : R ≤ ⁅V, V⁆ := by
    rw [hR, critR, Subgroup.commutator_le]
    intro z hz z' hz'
    obtain ⟨v, hv, u, hu, rfl⟩ := hdec z (hZ₁ hz)
    obtain ⟨v', hv', u', hu', rfl⟩ := hdec z' (hZ₂ hz')
    have h1 : ⁅u, v' * u'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_centralizer_iff.mp (hWhC (Wh.mul_mem (Subgroup.mem_inf.mp hv').2
        (c.vhat_le_whv' hZV hp ha (by omega) (by omega) hu'))) u hu)
    have h2 : ⁅v, u'⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_centralizer_iff.mp (hWhC (Subgroup.mem_inf.mp hv).2) u' hu').symm
    rw [S46.commutatorElement_mul_left_conj, h1, mul_one, mul_inv_cancel, one_mul,
      S46.commutatorElement_mul_right_conj, h2, mul_one, mul_inv_cancel, mul_one]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp hv).1 (Subgroup.mem_inf.mp hv').1
  obtain ⟨⟨r, hr⟩, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hRne
  have hKVV : stab (puAmalgam h.le) (p a) ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup _) : Set _) :=
    le_normalizer_commutator hKV hKV
  have hle := (NatSec.ofIsSum hψ).le_of_invariant hψs (H := ⁅V, V⁆ ⊓ Uloc h.le L (p a))
    (fun k y hy => Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp (hKVV k.2) y).mp (Subgroup.mem_inf.mp hy).1,
        (Subgroup.mem_normalizer_iff.mp (hψ.1 k.2) y).mp (Subgroup.mem_inf.mp hy).2⟩)
    (Subgroup.mem_inf.mpr ⟨hRV hr, hRU hr⟩) (hRU hr) (fun h1 => hr1 (Subtype.ext h1))
  exact hle.trans inf_le_left

theorem frattiniIn_eq_vcirc (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) (hp' : IsGoodPath _ p' N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a)
    (haN : a + 30 ≤ N) (hpp' : ∀ i, i ≤ a + 2 → p' i = p i)
    (hU1 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ≠ Usup _ (p (a + 2)) (p (a + 1)))
    (hU3 : Usup (puAmalgam c.hyp.le) (p (a + 2)) (p' (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)) ≠
      Usup _ (p (a + 2)) (p (a + 3)) ⊓ Usup _ (p (a + 2)) (p (a + 1)))
    (hC1 : ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓ Zloc c.hyp.le L (p a) ≤
      Hloc c.hyp.le L (p a))
    (hC4 : ¬ frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ≤
      Uloc c.hyp.le L (p a) ⊔ Hloc c.hyp.le L (p a)) :
    frattiniIn ⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ = Vcirc c.hyp.le L (p a) := by
  have h := c.hyp
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  have hle := c.frattiniIn_le_vcirc h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU3 hC1
  have hU := c.uloc_le_commutator_qv_ltil h14 hSQ hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  have hH := c.hloc_le_commutator_qv_ltil hZV hQ4 hp hp' ha h34 haN hpp' hU1 hU3
  obtain ⟨hV2, hVf⟩ := c.isPGroup_commutator_qv_ltil hα
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h c.via hα
  obtain ⟨d, hd⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ hdB
  subst hdt
  set Qα := Qv (puAmalgam h.le) (p (k + 34)) with hQα
  set Lt := Ltil h.le L (p (k + 34)) with hLt
  set V := ⁅Qα, Lt⁆ with hV
  set U := Uloc h.le L (p (k + 34)) with hUdef
  set H := Hloc h.le L (p (k + 34)) with hHdef
  set Z := ZM (puAmalgam h.le) (p (k + 34)) with hZ
  set Vc := Vcirc h.le L (p (k + 34)) with hVc
  have hΦUH : U ⊔ H ≤ frattiniIn V :=
    sup_le (hU.trans (commutator_le_frattiniIn hV2)) (hH.trans (commutator_le_frattiniIn hV2))
  have hQs : Qα ≤ stab (puAmalgam h.le) (p (k + 34)) := qv_le_stab _ _
  have hKQ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Qα : Set _) :=
    stab_le_normalizer_qv _ _
  have hLs : Lt ≤ stab (puAmalgam h.le) (p (k + 34)) := ltil_le_stab h _
  have hKV : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (V : Set _) :=
    le_normalizer_commutator hKQ (stab_le_normalizer_ltil h _)
  have hVQ : V ≤ Qα := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hKQ)
  have hKZ : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Z : Set _) :=
    stab_le_normalizer_zm _ _
  have hVcV : Vc ≤ V := Subgroup.commutator_mono (c.vv_le_qv' hα) le_rfl
  have hUZ : U ≤ Z := uloc_le_zm h c.full hα
  have hZQ : Z ≤ Qα := zm_le_qv_of_dist_lt _ hα (by simp [c.b8])
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hUL : ⁅U, Lt⁆ = U := c.commutator_uloc_ltil hα
  have hUV : U ≤ V := by
    rw [← hUL]
    exact Subgroup.commutator_mono (hUZ.trans hZQ) le_rfl
  have hUn : U ≤ Subgroup.normalizer (Zloc h.le L (p (k + 34)) : Set _) :=
    (hUZ.trans (hZQ.trans hQs)).trans (c.stab_le_normalizer_of_le_centralizer hZc)
  have hZV' : Z ⊓ V ≤ U ⊔ H := by
    have e := zm_eq_uloc_sup_zloc h c.full hα
    calc Z ⊓ V = (U ⊔ Zloc h.le L (p (k + 34))) ⊓ V := by rw [hZ, e]
      _ = U ⊔ (Zloc h.le L (p (k + 34)) ⊓ V) := sup_inf_eq_of_le hUV hUn
      _ ≤ U ⊔ H := sup_le_sup_left (by rw [inf_comm]; exact hC1) _
  have hΦZ : ¬ frattiniIn V ≤ Z := fun hΦ =>
    hC4 ((le_inf hΦ (hle.trans hVcV)).trans hZV')
  obtain ⟨x, hxΦ, hxZ⟩ := Set.not_subset.mp hΦZ
  have hKΦ := le_normalizer_frattiniIn hV2 hKV
  have hcov : Vc ⊔ Z ≤ frattiniIn V ⊔ Z := by
    intro v hv
    obtain ⟨w, hwH, -, hwv⟩ := (NatSec.ofIsSum hd).exists_inv_mul_mem_of_invariant hψs
      (H := frattiniIn V ⊔ Z) (fun k y hy =>
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_sup hKΦ hKZ k.2) y).mp hy)
      (Subgroup.mem_sup_left hxΦ) (Subgroup.mem_sup_left (hle hxΦ)) hxZ hv
    have e : v = w * (w⁻¹ * v) := by group
    rw [e]
    exact Subgroup.mul_mem _ hwH (Subgroup.mem_sup_right hwv)
  refine le_antisymm hle ?_
  have hΦn : frattiniIn V ≤ Subgroup.normalizer (Z : Set _) :=
    (hle.trans (hVcV.trans (hVQ.trans hQs))).trans hKZ
  calc Vc ≤ (frattiniIn V ⊔ Z) ⊓ Vc := le_inf (le_sup_left.trans hcov) le_rfl
    _ = frattiniIn V ⊔ (Z ⊓ Vc) := sup_inf_eq_of_le hle hΦn
    _ ≤ frattiniIn V := sup_le le_rfl (((inf_le_inf_left _ hVcV).trans hZV').trans hΦUH)

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
