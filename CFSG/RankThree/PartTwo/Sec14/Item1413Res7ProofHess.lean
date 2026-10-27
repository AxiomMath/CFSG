module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res8ProofHessConj
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projImage)

namespace Proof1413Res7

open Sec17.Proof17Res7 Res8Hess

section Model

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem exists_tM_mem_thetaC_model (hK : PiField π p f K) (hp2 : p ≠ 2)
    (hq : ModThree π (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    (hdc : dM * cM = cM * dM) (hdo : orderOf dM = 3) (hco : orderOf cM = 3)
    (hcd : cM ∉ Subgroup.zpowers dM) :
    ∃ b ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM, b ≠ 1 ∧
      tM hK hp2 _ isTInv_tOne ∈ thetaC b := by
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  set t₁ := tM hK hp2 _ isTInv_tOne with ht₁def
  set t₂ := tM hK hp2 _ isTInv_tTwo with ht₂def
  have h12 : t₁ * t₂ = tM hK hp2 _ isTInv_tThree := tM_one_mul_tM_two hK hp2
  have hT₁ : t₁ ∈ torusM hK hp2 := tM_mem_torusM hK hp2 isTInv_tOne
  have hT₂ : t₂ ∈ torusM hK hp2 := tM_mem_torusM hK hp2 isTInv_tTwo
  have hc12 : t₁ * t₂ = t₂ * t₁ := torusM_comm hK hp2 hT₁ hT₂
  have ht₁ : t₁ ^ 2 = 1 := tM_sq hK hp2 isTInv_tOne
  have ht₂ : t₂ ^ 2 = 1 := tM_sq hK hp2 isTInv_tTwo
  set R := Subgroup.zpowers t₁ ⊔ Subgroup.zpowers t₂ with hR
  have ht₁R : t₁ ∈ R := Subgroup.mem_sup_left (Subgroup.mem_zpowers t₁)
  have ht₂R : t₂ ∈ R := Subgroup.mem_sup_right (Subgroup.mem_zpowers t₂)
  have hsq : ∀ x ∈ R, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hc12 hx
    rw [(Commute.zpow_zpow hc12 i j).mul_pow, ← zpow_natCast, ← zpow_natCast,
      ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm i, mul_comm j, _root_.zpow_mul,
      _root_.zpow_mul, zpow_natCast, zpow_natCast, ht₁, ht₂, _root_.one_zpow, _root_.one_zpow,
      one_mul]
  have hR3 : ¬ 3 ∣ Nat.card R := by
    intro h3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) 3 h3
    have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq x hx)
    rw [← Subgroup.orderOf_mk x hx, hxo] at h1
    omega
  have hRT : R ≤ torusM hK hp2 := sup_le (Subgroup.zpowers_le.mpr hT₁) (Subgroup.zpowers_le.mpr hT₂)
  have hdN : dM ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : x * dM = dM * x := commute_dM_of_mem_torusM hK hp2 hτ hdM (hRT hx)
    have h2 : dM * x * dM⁻¹ = x := by rw [← h1, mul_inv_cancel_right]
    rw [SetLike.mem_coe, h2]
    exact hx
  obtain ⟨hc1, hc2, -⟩ := cM_conj_tM hK hp2 hcM
  have hcN : cM ∈ Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨i, j, rfl⟩ := exists_zpow_mul_of_mem_sup hc12 hx
    have e : cM * (t₁ ^ i * t₂ ^ j) * cM⁻¹ = (cM * t₁ * cM⁻¹) ^ i * (cM * t₂ * cM⁻¹) ^ j := by
      simp only [← MulAut.conj_apply, map_mul, map_zpow]
    rw [SetLike.mem_coe, e, hc1, hc2, ← h12]
    exact mul_mem (zpow_mem ht₂R i) (zpow_mem (mul_mem ht₁R ht₂R) j)
  have hER : Subgroup.zpowers dM ⊔ Subgroup.zpowers cM ≤
      Subgroup.normalizer (R : Set (projImage (slPi π 3 (p ^ f) K))) :=
    sup_le (Subgroup.zpowers_le.mpr hdN) (Subgroup.zpowers_le.mpr hcN)
  obtain ⟨b, hb, hb1, hRb⟩ := le_thetaC_model hK hp2 hτ hτ1 hq hdM hcM hdc hdo hco hcd hR3 hER
  exact ⟨b, hb, hb1, hRb ht₁R⟩

theorem exists_eq_of_commute_model {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {dM cM : projImage (slPi π 3 (p ^ f) K)}
    (hdM : (dM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (diagTau hτ))
    (hcM : (cM : ProjGenLinGroup (Fin 3) K) = ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))
    {y : projImage (slPi π 3 (p ^ f) K)} (hyd : y * dM = dM * y) (hyc : y * cM = cM * y) :
    ∃ m j : ℕ, y = dM ^ m * cM ^ j := by
  obtain ⟨B, -, hB⟩ := exists_lift y
  have h1 : ProjGenLinGroup.mk B * ProjGenLinGroup.mk (diagTau hτ) =
      ProjGenLinGroup.mk (diagTau hτ) * ProjGenLinGroup.mk B := by
    rw [hB, ← hdM]
    exact congrArg Subtype.val hyd
  have h2 : ProjGenLinGroup.mk B * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) =
      ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk B := by
    rw [hB, ← hcM]
    exact congrArg Subtype.val hyc
  obtain ⟨u, hu⟩ := exists_conj_of_mk_comm h1
  obtain ⟨v, hv⟩ := exists_conj_of_mk_comm h2
  obtain ⟨s, m, j, hBs⟩ := exists_eq_of_conj_hessian hτ hτ1 hu hv
  refine ⟨m, j, Subtype.ext ?_⟩
  have hs : ProjGenLinGroup.mk (GeneralLinearGroup.scalar (Fin 3) s) = 1 := by
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨s, rfl⟩
  rw [← hB, hBs, map_mul, map_mul, hs, one_mul, map_pow, map_pow, Subgroup.coe_mul,
    Subgroup.coe_pow, Subgroup.coe_pow, hdM, hcM]

end Model

variable {X : Type} [Group X] [Finite X] {p e : ℕ} [Fact p.Prime]

theorem exists_orderOf_two_mem_thetaC (he : 1 ≤ e) (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) : ∃ z ∈ thetaC x, orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    exists_hessian_equiv he hiso hEe hE9 htr
  have := hK.finite
  have : Finite (ProjGenLinGroup (Fin 3) K) := by
    unfold ProjGenLinGroup
    infer_instance
  obtain ⟨b, hb, hb1, hz⟩ := exists_tM_mem_thetaC_model hK hp2 hq hτ hτ1 hdM hcM hdc hdo hco hcd
  have hz2 : orderOf (tM hK hp2 _ isTInv_tOne) = 2 :=
    orderOf_eq_prime (tM_sq hK hp2 isTInv_tOne) (tM_ne_one hK hp2 isTInv_tOne)
  have hx₀E : Φ b ∈ E := hΦE ▸ ⟨b, hb, rfl⟩
  have hx₀1 : Φ b ≠ 1 := fun h => hb1 (Φ.injective (by rw [h, map_one]))
  obtain ⟨w, -, hw⟩ := htr _ hx₀E hx₀1 x hx hx1
  refine ⟨w * Φ (tM hK hp2 _ isTInv_tOne) * w⁻¹, (mem_thetaC_iff_conj hw _).mp ?_, ?_⟩
  · rw [← thetaC_map_equiv Φ b]
    exact ⟨_, hz, rfl⟩
  · rw [orderOf_conj_eq, MulEquiv.orderOf_eq, hz2]

theorem mem_of_commute_hessian (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {y : X} (hyE : ∀ b ∈ E, y * b = b * y) : y ∈ E := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, -, -, -, -, Φ, hΦE⟩ :=
    exists_hessian_equiv he hiso hEe hE9 htr
  have hdÊ : dM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers dM)
  have hcÊ : cM ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers cM)
  have hdE : Φ dM ∈ E := hΦE ▸ ⟨dM, hdÊ, rfl⟩
  have hcE : Φ cM ∈ E := hΦE ▸ ⟨cM, hcÊ, rfl⟩
  set y' := Φ.symm y with hy'
  have hd : y' * dM = dM * y' := Φ.injective (by
    rw [map_mul, map_mul, hy', MulEquiv.apply_symm_apply]
    exact hyE _ hdE)
  have hc : y' * cM = cM * y' := Φ.injective (by
    rw [map_mul, map_mul, hy', MulEquiv.apply_symm_apply]
    exact hyE _ hcE)
  obtain ⟨m, j, hmj⟩ := exists_eq_of_commute_model hτ hτ1 hdM hcM hd hc
  have hy'E : y' ∈ Subgroup.zpowers dM ⊔ Subgroup.zpowers cM := by
    rw [hmj]
    exact mul_mem (pow_mem hdÊ m) (pow_mem hcÊ j)
  have h1 : Φ y' ∈ E := hΦE ▸ ⟨y', hy'E, rfl⟩
  rwa [hy', MulEquiv.apply_symm_apply] at h1

theorem eq_one_of_commute_hessian (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {y : X} (hy3 : Nat.Coprime 3 (orderOf y)) (hyE : ∀ b ∈ E, y * b = b * y) : y = 1 := by
  have h3 : y ^ 3 = 1 := hEe.2 y (mem_of_commute_hessian he hiso hEe hE9 htr hyE)
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hy3 (orderOf_dvd_of_pow_eq_one h3) dvd_rfl)

theorem mem_zpowers_of_mem_thetaC (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi X p e)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {x : X} (hx : x ∈ E) (hx1 : x ≠ 1) {y : X} (hy : y ∈ thetaC x) (hy1 : y ≠ 1) {b : X}
    (hb : b ∈ E) (hyb : y * b = b * y) : b ∈ Subgroup.zpowers x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hbx
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbx (Subgroup.one_mem _)
  have hxo : orderOf x = 3 := orderOf_eq_prime (hEe.2 x hx) hx1
  have hbo : orderOf b = 3 := orderOf_eq_prime (hEe.2 b hb) hb1
  have hxb : x * b = b * x := congrArg Subtype.val (hEe.1.is_comm.comm ⟨x, hx⟩ ⟨b, hb⟩)
  have hEeq : E = Subgroup.zpowers x ⊔ Subgroup.zpowers b :=
    eq_sup_zpowers_of_card_nine hE9 hx hb hbo hbx hxb hxo
  have hyx : y ∈ Subgroup.centralizer ({x} : Set X) := inSubgroup_theta_le _ hy
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers b ≤ Subgroup.centralizer ({y} : Set X) := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hyx).symm
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hyb.symm
  apply hy1
  refine eq_one_of_commute_hessian he hiso hEe hE9 htr
    (coprime_orderOf_of_mem (not_dvd_card_inSubgroup_theta _) hy) fun c hc => ?_
  rw [hEeq] at hc
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hc)).symm

end Proof1413Res7

end CFSG.RankThree.PartTwo.Sec14
