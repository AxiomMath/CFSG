module

import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec11.Item116TheoremOCor

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace P2Proof

section General

variable {G : Type} [Group G]

theorem conj_sq_eq_of_conj_mem_zpowers {h y : G} (hy3 : y ^ 3 = 1)
    (hhy : h * y * h⁻¹ ∈ Subgroup.zpowers y) : (h * h) * y * (h * h)⁻¹ = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hhy
  have hy3' : y ^ (3 : ℤ) = 1 := by exact_mod_cast hy3
  have key : (h * h) * y * (h * h)⁻¹ = y ^ (k * k) := by
    calc (h * h) * y * (h * h)⁻¹ = h * (h * y * h⁻¹) * h⁻¹ := by group
      _ = h * y ^ k * h⁻¹ := by rw [hk]
      _ = (h * y * h⁻¹) ^ k := by rw [conj_zpow]
      _ = (y ^ k) ^ k := by rw [hk]
      _ = y ^ (k * k) := by rw [← zpow_mul]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · have hy1 : h * y * h⁻¹ = 1 := by rw [← hk, zpow_eq_zpow_emod k hy3', h0, zpow_zero]
    have hy : y = 1 := by
      calc y = h⁻¹ * (h * y * h⁻¹) * h := by group
        _ = 1 := by rw [hy1]; group
    rw [hy]
    group
  · rw [key, zpow_eq_zpow_emod _ hy3', Int.mul_emod, h1]
    norm_num
  · rw [key, zpow_eq_zpow_emod _ hy3', Int.mul_emod, h2]
    norm_num

theorem false_of_mulEquiv_of_mul_self {S X : Type*} [Group S] [Group X] (e : S ≃* X)
    (hS : ∀ s : S, s * s = 1) {x : X} (hx : x * x ≠ 1) : False := by
  apply hx
  have h1 : e.symm (x * x) = 1 := by
    rw [map_mul]
    exact hS (e.symm x)
  simpa using congrArg e h1

theorem mul_self_eq_one_of_mem_autIn {A Y : Subgroup G} {c a d : G}
    (hA : A = Subgroup.closure {c, a, d}) (hexp : ∀ x ∈ A, x ^ 3 = 1)
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    (hfix : ∀ w ∈ Subgroup.normalizer (A : Set G), w * a * w⁻¹ = a →
      w * c * w⁻¹ ∈ Subgroup.zpowers c ∧ w * d * w⁻¹ ∈ Subgroup.zpowers d)
    {σ : MulAut A} (hσ : σ ∈ Sec4.autIn Y A) : σ * σ = 1 := by
  obtain ⟨h, hN, hhY, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  have hha : h * a * h⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hYa hhY), mul_inv_cancel_right]
  obtain ⟨hhc, hhd⟩ := hfix h hN hha
  have hcA : c ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := hA ▸ Subgroup.subset_closure (by simp)
  have hAC : A ≤ Subgroup.centralizer ({h * h} : Set G) := by
    rw [hA, Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have key : (h * h) * y * (h * h)⁻¹ = y := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact conj_sq_eq_of_conj_mem_zpowers (hexp _ hcA) hhc
      · rw [show (h * h) * y * (h * h)⁻¹ = h * (h * y * h⁻¹) * h⁻¹ by group, hha, hha]
      · exact conj_sq_eq_of_conj_mem_zpowers (hexp _ hdA) hhd
    calc y * (h * h) = ((h * h) * y * (h * h)⁻¹) * (h * h) := by rw [key]
      _ = (h * h) * y := by group
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [MulAut.mul_apply, MulAut.one_apply, Sec4.normalizerMonoidHom_apply_coe,
    Sec4.normalizerMonoidHom_apply_coe]
  have hx : (x : G) * (h * h) = (h * h) * x := Subgroup.mem_centralizer_singleton_iff.mp (hAC x.2)
  calc h * (h * (x : G) * h⁻¹) * h⁻¹ = (h * h) * x * (h * h)⁻¹ := by group
    _ = x * (h * h) * (h * h)⁻¹ := by rw [hx]
    _ = x := mul_inv_cancel_right _ _

end General

section Certified

variable {G : Type} [Group G] [Finite G]

theorem eq_sec11K_sup_theta_of_ne (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    {A : Subgroup G} {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G}
    (h : Sec11Std G A c L a R Y) {d : G} (hdL : A ⊓ L = Subgroup.zpowers d)
    (hdc : d ∉ Subgroup.zpowers c) {n : G} (hnd : n * d * n⁻¹ ∈ Subgroup.zpowers c)
    (hna : n * a * n⁻¹ ∈ Subgroup.zpowers a) (hYn : Y.map (MulAut.conj n).toMonoidHom ≠ Y) :
    Y = sec11K L a ⊔ inSubgroup (aschbacherSolvableCore 3) Y := by
  have hAe := h.mem_partTwoF.1
  have hexp : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have haA := h.a_mem
  have hcYn := TheoremO.mem_map_conj_of_conj_mem_zpowers h45 h hdL hdc hnd
  have hna1 : n * a * n⁻¹ ≠ 1 := fun h1 => h.a_ne_one (by
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h1]; group)
  have hYnL : Y.map (MulAut.conj n).toMonoidHom ∈ thetaComponentsAt 3 a := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj n) h.mem_thetaComponentsAt_Y
    rwa [MulAut.conj_apply, TheoremO.thetaComponentsAt_eq_of_zpowers_eq
      (TheoremO.zpowers_eq_of_mem_of_ne_one (hexp a haA) hna hna1)] at h1
  have hcomm := Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt
    h.mem_thetaComponentsAt_Y hYnL (Ne.symm hYn)
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.a_mem h.a_ne_one Y
      h.mem_thetaComponentsAt_Y h.mem_A
  have hcC : c ∈ Sec4.thetaQuotCentralizer Y := by
    refine Sec6.mem_thetaQuotCentralizer_iff.mpr ⟨hcN, fun l hl => ?_⟩
    rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y]
    refine Subgroup.mem_inf.mpr
      ⟨Y.mul_mem (Y.inv_mem hl) ((Subgroup.mem_normalizer_iff.mp hcN l).mp hl), ?_⟩
    have h1 := hcomm (Subgroup.commutator_mem_commutator (Y.inv_mem hl) hcYn)
    have e : l⁻¹ * (c * l * c⁻¹) = ⁅l⁻¹, c⁆ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact h1
  have hD3 := Sec6.isPGroup_zpowers_of_pow_three (hexp c h.mem_A)
  have hDC : Subgroup.zpowers c ≤ Sec4.thetaQuotCentralizer Y := Subgroup.zpowers_le.mpr hcC
  have hcov := Sec6.le_residual_inf_centralizer_sup_theta
    (Sec6.isPerfect_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y) hD3 hDC
  rw [Sec6.centralizer_zpowers_eq] at hcov
  set X := inSubgroup perfectResidual (Y ⊓ Subgroup.centralizer ({c} : Set G)) with hX
  obtain ⟨J, hJ, hXJ⟩ := Sec6.exists_mem_thetaComponentsAt_residual_le h48 h.toPartTwoStanding
    h.mem_partTwoF haA h.a_ne_one h.mem_A h.ne_one h.mem_thetaComponentsAt_Y hcC
  have hXJ' : X ≤ J := (Sec6.inSubgroup_perfectResidual_mono le_sup_left).trans hXJ
  have hdK := TheoremO.mem_sec11K_d h45 h hdL hdc
  have hd1 : d ≠ 1 := fun h1 => hdc (by rw [h1]; exact Subgroup.one_mem _)
  have hK1 : sec11K L a ≠ ⊥ := fun hK0 => hd1 (by rwa [hK0, Subgroup.mem_bot] at hdK)
  have hKp : Group.IsPerfect (sec11K L a) := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hKX : sec11K L a ≤ X := Sec6.le_inSubgroup_perfectResidual_of_isPerfect hKp
    (le_inf h.sec11K_le ((sec11K_le L a).trans hLc))
  have hJL : J = L := Sec6.eq_of_mem_thetaComponentsIn_of_le hJ h.mem_thetaComponentsAt hKp hK1
    (hKX.trans hXJ') (sec11K_le L a)
  have hYa := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  have hXY : X ≤ Y := (Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left
  have hXK : X ≤ sec11K L a := Sec6.le_inSubgroup_perfectResidual_of_isPerfect
    (Sec6.isPerfect_inSubgroup_perfectResidual _) (le_inf (hXJ'.trans hJL.le) (hXY.trans hYa))
  exact le_antisymm (hcov.trans (sup_le_sup_right hXK _)) (sup_le h.sec11K_le (Sec6.theta_le Y))

end Certified

end P2Proof

section Main

theorem item116P2c_of (hP2b : Item116P2b) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) :
    Item116P2c := by
  intro G _ _ A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna
  refine P2Proof.eq_sec11K_sup_theta_of_ne h45 h48 h hdL hdc hnd ?_
    (hP2b G A c L a R Y h d hdL hWB hirr hRG hdc hD8 n hnW hnc hnd hna)
  rw [hna]
  exact Subgroup.inv_mem _ (Subgroup.mem_zpowers a)

end Main

end CFSG.RankThree.PartTwo.Sec11
