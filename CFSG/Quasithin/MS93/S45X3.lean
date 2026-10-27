module

public import CFSG.Quasithin.MS93.S45X2
public import CFSG.Quasithin.MS93.ML3AutBridge
public import CFSG.Quasithin.MS93.S45Pair

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

theorem top_isSum (h14 : MS14AS) (hSQ : SQTKQuot) (hZV : c.HZV) (hQ4 : c.HQ4)
    (hp : IsGoodPath _ p N) {a : ℕ} (ha : Even a) (h34 : 34 ≤ a) (haN : a + 30 ≤ N)
    {ψ : ↥(stab (puAmalgam c.hyp.le) (p a)) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ (p a)) (Uloc c.hyp.le L (p a)) ⊥ ψ false 1) :
    IsSumOfNaturalModulesVia (stab _ (p a))
      (⁅conjCl (stab (puAmalgam c.hyp.le) (p a)) (Vcirc c.hyp.le L (p (a + 4)) ⊔ ZM _ (p (a + 4))) ⊔
          whv c.hyp (p a) (p (a + 2)), stab (puAmalgam c.hyp.le) (p a)⁆ ⊔
        whv c.hyp (p a) (p (a + 2))) (whv c.hyp (p a) (p (a + 2))) ψ false 1 := by
  have h := c.hyp
  have h20 := h.hyp20
  have : CharP F 2 := c.charP
  obtain ⟨n, hn⟩ := c.via.1
  obtain ⟨k, rfl⟩ : ∃ k, a = k + 34 := ⟨a - 34, by omega⟩
  have hk : Even k := (Nat.even_add.mp ha).mpr (by decide)
  have hα := c.isMVtx_of_isGoodPath hp (k := k + 34) (by omega) ha
  have hγ := c.isMVtx_of_isGoodPath hp (k := k + 36) (by omega) (hk.add (by decide))
  set Wh := whv h (p (k + 34)) (p (k + 34 + 2)) with hWh
  set X := conjCl (stab (puAmalgam h.le) (p (k + 34)))
    (Vcirc h.le L (p (k + 34 + 4)) ⊔ ZM _ (p (k + 34 + 4))) ⊔ Wh with hX
  have hC1 := c.commutator_top_qv_le hZV hQ4 hp ha h34 (by omega)
  rw [← hX] at hC1
  have hXV := c.commutator_top_vv_le hp ha (by omega) (by omega)
  rw [← hX] at hXV
  obtain ⟨-, C, hCle, hCX, hCG, hsupC, -, F', iF', fF', ψ', hF'card, hψ's, hψ'⟩ :=
    c.isC1_top h14 hSQ hZV hQ4 hp ha h34 haN
  rw [← hWh, ← hX] at hCle hCX hCG hsupC hψ'
  have hQW : ⁅X, Qv (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh = Wh := sup_eq_right.mpr hC1
  rw [hQW] at hψ' hCG
  have : CharP F' 2 := charP_two_of_card_eq_two_pow (hF'card.trans hn)
  have hQs : Qv (puAmalgam h.le) (p (k + 34)) ≤ stab (puAmalgam h.le) (p (k + 34)) :=
    qv_le_stab _ _
  have hQn : stab (puAmalgam h.le) (p (k + 34)) ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) (p (k + 34)) : Set _) := stab_le_normalizer_qv _ _
  have hWhn : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (Wh : Set _) :=
    S4A.le_normalizer_conjCl _ _
  have hμ := c.isMVtx_of_isGoodPath hp (k := k + 38) (by omega) (hk.add (by decide))
  have hXQ : X ≤ Qv (puAmalgam h.le) (p (k + 34)) := by
    refine sup_le (conjCl_le_of_le_normalizer ((c.vhat_le_vv hμ).trans (vi_le_qv _ ?_)) hQn)
      (conjCl_le_of_le_normalizer ((c.vhat_le_vv hγ).trans (vi_le_qv _ ?_)) hQn)
    · rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 38) (by omega) (by omega), c.b8]
      omega
    · rw [tdist_comm, hp.dist_eq' (i := k + 34) (j := k + 36) (by omega) (by omega), c.b8]
      omega
  have hXn : stab (puAmalgam h.le) (p (k + 34)) ≤ Subgroup.normalizer (X : Set _) :=
    le_normalizer_sup (S4A.le_normalizer_conjCl _ _) hWhn
  have hX'X : ⁅X, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh ≤ X :=
    sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hXn) le_sup_right
  have hker : ψ.ker ≤ ψ'.ker := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have h1 : toSL3 ψ g = 1 := (toSL3_eq_one_iff' ψ g).mpr hg
    have hgQ : (g : (puAmalgam h.le).Universal) ∈ Qv (puAmalgam h.le) (p (k + 34)) := by
      have h2 : g ∈ (toSL3 ψ).ker := h1
      rw [c.ker_toSL3_eq hα hψ, Subgroup.mem_subgroupOf] at h2
      exact h2
    refine (toSL3_eq_one_iff' ψ' g).mp (toSL3_eq_one_of_conj hψ' g fun v hv => ?_)
    have hvX := hX'X hv
    have e : v⁻¹ * ((g : (puAmalgam h.le).Universal) * v * (g : (puAmalgam h.le).Universal)⁻¹) =
        ⁅v⁻¹, (g : (puAmalgam h.le).Universal)⁆ := by
      rw [commutatorElement_def]; group
    rw [e]
    exact hC1 (Subgroup.commutator_mem_commutator (X.inv_mem hvX) hgQ)
  obtain ⟨d, hd⟩ := isSumOfNaturalModulesVia_of_surj hψs hψ's hker hψ'
  cases d with
  | false => exact hd
  | true =>
  exfalso
  obtain ⟨d', hd'⟩ := c.exists_isSum_vhat hα hψs hψ
  have hdB := c.isSum_bloc hα hd'
  have hdt := c.dual_eq_true hp (x := k + 28) (hk.add (by decide)) (by omega) (by omega) hψs hψ
    hdB
  subst hdt
  have ha2 : Even (k + 32) := hk.add (by decide)
  have hc2 := c.isCritical_of_isGoodPath hp ha2 (show k + 32 + 8 ≤ N by omega)
  have hg2 : geo (puAmalgam h.le) (p (k + 32)) (p (k + 32 + 8)) 2 = p (k + 34) := by
    rw [hp.eq_geo (i := k + 32) (j := k + 32 + 8) (k := k + 34) (by omega) (by omega)
      (by omega), show k + 34 - (k + 32) = 2 by omega]
  have hRZ : critR (puAmalgam h.le) (p (k + 32)) (p (k + 32 + 8)) ≤ Zloc h.le L (p (k + 34)) := by
    have := c.critR_le_zloc hc2
    rwa [hg2] at this
  rw [show k + 34 - 2 = k + 32 by omega, show k + 34 + 6 = k + 32 + 8 by omega] at hXV
  have hZc := zloc_le_centralizer_stab h c.full hα
  have hVs : Vcirc h.le L (p (k + 34)) ⊔ ZM _ (p (k + 34)) ≤ stab (puAmalgam h.le) (p (k + 34)) :=
    (c.vhat_le_vv hα).trans ((c.vv_le_qv' hα).trans hQs)
  have hWc := c.whv_le_centralizer_vv hγ (by
    rw [hp.dist_eq' (i := k + 34) (j := k + 36) (by omega) (by omega)]; omega)
  have hbot := commutator_eq_bot_of_isSum hψs hd hd'
    (fun x hx v hv g hg => by
      have hr := hRZ (hXV (Subgroup.commutator_mem_commutator (hX'X hx) (c.vhat_le_vv hα hv)))
      have hgs : g ∈ stab (puAmalgam h.le) (p (k + 34)) :=
        sup_le (sup_le le_rfl (hX'X.trans (hXQ.trans hQs))) hVs hg
      exact (Subgroup.mem_centralizer_iff.mp (hZc hr) g hgs))
    (fun z hz v hv => by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_centralizer_iff.mp (hWc hz) v (c.vhat_le_vv hα hv)).symm)
    (fun x hx z hz => by
      rw [commutatorElement_eq_one_iff_commute]
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hα hz) x
        (hXQ (hX'X hx))))
  have hCV : ∀ x ∈ C, ∀ u ∈ Vcirc h.le L (p (k + 34)) ⊔ ZM _ (p (k + 34)), x * u = u * x :=
    fun x hx => c.commute_vhat_of_comm hp ha (by omega) (hXQ (hCX hx))
      (fun v hv => hRZ (hXV (Subgroup.commutator_mem_commutator (hCX hx) hv)))
      (fun l hl => hCG (Subgroup.commutator_mem_commutator hx (ltil_le_stab h _ hl)))
  apply c.critR_ne_bot_of_isGoodPath hp ha (by omega) (by omega)
  rw [show k + 34 - 2 = k + 32 by omega, show k + 34 + 6 = k + 32 + 8 by omega, eq_bot_iff,
    critR, Subgroup.commutator_le]
  intro z hz x hx
  have hμ6 : ZM (puAmalgam h.le) (p (k + 32 + 8)) ≤ X := by
    have := c.zm_le_vhat_right hZV hp (a := k + 38) (hk.add (by decide)) (by omega) (by omega)
    exact (this.trans (S4A.le_conjCl _ _)).trans le_sup_left
  have hzV : z ∈ Vcirc h.le L (p (k + 34)) ⊔ ZM _ (p (k + 34)) :=
    c.zm_le_vhat_left' hZV hp ha (by omega) (by omega) hz
  have hxX := hμ6 hx
  rw [← hsupC] at hxX
  have hCn : ⁅X, stab (puAmalgam h.le) (p (k + 34))⁆ ⊔ Wh ≤ Subgroup.normalizer (C : Set _) :=
    (hX'X.trans (hXQ.trans hQs)).trans (Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (hCG.trans (le_sup_right.trans hCle)))
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hCn] at hxX
  obtain ⟨x', hx', c', hc', rfl⟩ := hxX
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
  have h1 : x' * z = z * x' := by
    have := (Subgroup.commutator_le.mp hbot.le) x' hx' z hzV
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute] at this
    exact this
  have h2 : c' * z = z * c' := hCV c' hc' z hzV
  show z * (x' * c') = x' * c' * z
  calc z * (x' * c') = (z * x') * c' := by group
    _ = (x' * z) * c' := by rw [h1]
    _ = x' * (z * c') := by group
    _ = x' * (c' * z) := by rw [h2]
    _ = x' * c' * z := by group

end GoodPath

end Ctx

end CFSG.Quasithin.MS93.S45
