module

public import CFSG.Quasithin.EmptyFaithful.S146zLCent

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Pi

variable {G : Type} [Group G] (H : Subgroup G)

instance zrNormalPCore : ((pCoreOf 2 H).subgroupOf H).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr (le_normalizer_pCoreOf 2 H)

@[expose] def piQ : ↥H →* ↥H ⧸ (pCoreOf 2 H).subgroupOf H := QuotientGroup.mk' _

theorem piQ_eq_one_iff (x : ↥H) : piQ H x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  show (QuotientGroup.mk x : ↥H ⧸ (pCoreOf 2 H).subgroupOf H) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

variable {H}

theorem cent_iff {x a : G} (hx : x ∈ H) (ha : a ∈ H) :
    x * a * x⁻¹ * a⁻¹ ∈ pCoreOf 2 H ↔
      piQ H ⟨x, hx⟩ * piQ H ⟨a, ha⟩ * (piQ H ⟨x, hx⟩)⁻¹ = piQ H ⟨a, ha⟩ := by
  have hm : x * a * x⁻¹ * a⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hx ha) (H.inv_mem hx)) (H.inv_mem ha)
  have e : (⟨x * a * x⁻¹ * a⁻¹, hm⟩ : ↥H) = ⟨x, hx⟩ * ⟨a, ha⟩ * ⟨x, hx⟩⁻¹ * ⟨a, ha⟩⁻¹ := rfl
  rw [← piQ_eq_one_iff H ⟨_, hm⟩, e, map_mul, map_mul, map_mul, map_inv, map_inv]
  constructor
  · intro h1
    exact mul_inv_eq_one.mp h1
  · intro h1
    rw [h1]
    exact mul_inv_cancel _

theorem inv_iff {x a : G} (hx : x ∈ H) (ha : a ∈ H) :
    x * a * x⁻¹ * a ∈ pCoreOf 2 H ↔
      piQ H ⟨x, hx⟩ * piQ H ⟨a, ha⟩ * (piQ H ⟨x, hx⟩)⁻¹ = (piQ H ⟨a, ha⟩)⁻¹ := by
  have hm : x * a * x⁻¹ * a ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem hx ha) (H.inv_mem hx)) ha
  have e : (⟨x * a * x⁻¹ * a, hm⟩ : ↥H) = ⟨x, hx⟩ * ⟨a, ha⟩ * ⟨x, hx⟩⁻¹ * ⟨a, ha⟩ := rfl
  rw [← piQ_eq_one_iff H ⟨_, hm⟩, e, map_mul, map_mul, map_mul, map_inv]
  constructor
  · intro h1
    exact eq_inv_of_mul_eq_one_left h1
  · intro h1
    rw [h1]
    exact inv_mul_cancel _

end Pi

section Sign

variable {K : Type*} [Group K]

theorem same_sign_cent {X Y A : K} (hX : X * A * X⁻¹ = A ∨ X * A * X⁻¹ = A⁻¹)
    (hY : Y * A * Y⁻¹ = A ∨ Y * A * Y⁻¹ = A⁻¹)
    (hsame : X * A * X⁻¹ = A ↔ Y * A * Y⁻¹ = A) :
    (X⁻¹ * Y) * A * (X⁻¹ * Y)⁻¹ = A := by
  by_cases h : X * A * X⁻¹ = A
  · have hy := hsame.mp h
    have e : X⁻¹ * A * X = A := by
      have := congrArg (fun z => X⁻¹ * z * X) h
      simpa [mul_assoc] using this.symm
    calc (X⁻¹ * Y) * A * (X⁻¹ * Y)⁻¹ = X⁻¹ * (Y * A * Y⁻¹) * X := by group
      _ = X⁻¹ * A * X := by rw [hy]
      _ = A := e
  · have hx : X * A * X⁻¹ = A⁻¹ := hX.resolve_left h
    have hy : Y * A * Y⁻¹ = A⁻¹ := hY.resolve_left (fun h' => h (hsame.mpr h'))
    have e : X⁻¹ * A⁻¹ * X = A := by
      have := congrArg (fun z => X⁻¹ * z * X) hx
      simpa [mul_assoc] using this.symm
    calc (X⁻¹ * Y) * A * (X⁻¹ * Y)⁻¹ = X⁻¹ * (Y * A * Y⁻¹) * X := by group
      _ = X⁻¹ * A⁻¹ * X := by rw [hy]
      _ = A := e

theorem conj_inv_of_inv {R A : K} (h : R * A * R⁻¹ = A⁻¹) : R⁻¹ * A * R = A⁻¹ := by
  have h1 : A = R⁻¹ * A⁻¹ * R := by
    have := congrArg (fun z => R⁻¹ * z * R) h
    simpa [mul_assoc] using this
  calc R⁻¹ * A * R = (R⁻¹ * A⁻¹ * R)⁻¹ := by group
    _ = A⁻¹ := by rw [← h1]

theorem conj_inv_of_cent {R A : K} (h : R * A * R⁻¹ = A) : R⁻¹ * A * R = A := by
  have := congrArg (fun z => R⁻¹ * z * R) h
  simpa [mul_assoc] using this.symm

end Sign

section Dih

theorem dih_refl_conj_rot {p : ℕ} [NeZero p] (c : ZMod p) :
    DihedralGroup.sr c * DihedralGroup.r 1 * (DihedralGroup.sr c)⁻¹ * DihedralGroup.r 1 =
      (1 : DihedralGroup p) := by
  rw [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr,
    DihedralGroup.r_mul_r, DihedralGroup.one_def]
  congr 1
  ring

end Dih


section Types

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.mem_pCore_of_same_type (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {x y : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hz2 : (x⁻¹ * y) * (x⁻¹ * y) = 1)
    (hx₁ : x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ∨ x * (a₁ : G) * x⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hy₁ : y * (a₁ : G) * y⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ∨ y * (a₁ : G) * y⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hs₁ : x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ↔ y * (a₁ : G) * y⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H)
    (hx₂ : x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H ∨ x * (a₂ : G) * x⁻¹ * (a₂ : G) ∈ pCoreOf 2 H)
    (hy₂ : y * (a₂ : G) * y⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H ∨ y * (a₂ : G) * y⁻¹ * (a₂ : G) ∈ pCoreOf 2 H)
    (hs₂ : x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H ↔ y * (a₂ : G) * y⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H) :
    x⁻¹ * y ∈ pCoreOf 2 H := by
  have ha₁H : (a₁ : G) ∈ H := h.le (h.le₁ a₁.2)
  have ha₂H : (a₂ : G) ∈ H := h.le (h.le₂ a₂.2)
  have hzH : x⁻¹ * y ∈ H := H.mul_mem (H.inv_mem hxH) hyH
  have e : (⟨x⁻¹ * y, hzH⟩ : ↥H) = ⟨x, hxH⟩⁻¹ * ⟨y, hyH⟩ := rfl
  refine h.mem_pCore_of_centralizes S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hzH hz2 ?_ ?_
  · rw [cent_iff hzH ha₁H, e, map_mul, map_inv]
    refine same_sign_cent ?_ ?_ ?_
    · rcases hx₁ with h1 | h1
      · exact Or.inl ((cent_iff hxH ha₁H).mp h1)
      · exact Or.inr ((inv_iff hxH ha₁H).mp h1)
    · rcases hy₁ with h1 | h1
      · exact Or.inl ((cent_iff hyH ha₁H).mp h1)
      · exact Or.inr ((inv_iff hyH ha₁H).mp h1)
    · rw [← cent_iff hxH ha₁H, ← cent_iff hyH ha₁H]
      exact hs₁
  · rw [cent_iff hzH ha₂H, e, map_mul, map_inv]
    refine same_sign_cent ?_ ?_ ?_
    · rcases hx₂ with h1 | h1
      · exact Or.inl ((cent_iff hxH ha₂H).mp h1)
      · exact Or.inr ((inv_iff hxH ha₂H).mp h1)
    · rcases hy₂ with h1 | h1
      · exact Or.inl ((cent_iff hyH ha₂H).mp h1)
      · exact Or.inr ((inv_iff hyH ha₂H).mp h1)
    · rw [← cent_iff hxH ha₂H, ← cent_iff hyH ha₂H]
      exact hs₂

end Types


section Refl

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.mem_H₁_of_inv_cent (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) (hs₁ : Function.Surjective φ₁)
    {a₁ : ↥H₁} (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {w : G} (hwH : w ∈ H) (hw2 : w * w = 1)
    (hw₁ : w * (a₁ : G) * w⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hw₂ : w * (a₂ : G) * w⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H) : w ∈ H₁ := by
  classical
  have hp : p.Prime := hred.prime
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have ha₁H : (a₁ : G) ∈ H := h.le (h.le₁ a₁.2)
  have ha₂H : (a₂ : G) ∈ H := h.le (h.le₂ a₂.2)
  obtain ⟨r₁, hr₁⟩ := hs₁ (DihedralGroup.sr 0)
  have hr₁H : (r₁ : G) ∈ H := h.le (h.le₁ r₁.2)
  have hr₁a₁ : (r₁ : G) * (a₁ : G) * (r₁ : G)⁻¹ * (a₁ : G) ∈ pCoreOf 2 H := by
    have h1 : φ₁ (r₁ * a₁ * r₁⁻¹ * a₁) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, hr₁, ha₁]
      exact dih_refl_conj_rot 0
    simpa using (hker₁ _).mp h1
  have hr₁a₂ : (r₁ : G) * (a₂ : G) * (r₁ : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
    h.comm (Subgroup.commutator_mem_commutator r₁.2 a₂.2)
  have hr₁r₁ : (r₁ : G) * (r₁ : G) ∈ pCoreOf 2 H := by
    have h1 : φ₁ (r₁ * r₁) = 1 := by
      rw [map_mul, hr₁]
      exact DihedralGroup.sr_mul_self 0
    simpa using (hker₁ _).mp h1
  have ha₁a₂ : (a₁ : G) * (a₂ : G) * (a₁ : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H :=
    h.comm (Subgroup.commutator_mem_commutator a₁.2 a₂.2)
  have ha₂p : (a₂ : G) ^ p ∈ pCoreOf 2 H := by
    have h1 : φ₂ (a₂ ^ p) = 1 := by rw [map_pow, ha₂]; exact DihedralGroup.r_one_pow_n
    simpa using (hker₂ _).mp h1
  have ha₂Q : (a₂ : G) ∉ pCoreOf 2 H := fun hQ => by
    have := (hker₂ a₂).mpr hQ
    rw [ha₂] at this
    have h1 : (DihedralGroup.r (1 : ZMod p)) = DihedralGroup.r 0 := this
    exact one_ne_zero (DihedralGroup.r.inj h1)
  set A₁ := piQ H ⟨(a₁ : G), ha₁H⟩ with hA₁
  set A₂ := piQ H ⟨(a₂ : G), ha₂H⟩ with hA₂
  set R := piQ H ⟨(r₁ : G), hr₁H⟩ with hR
  set W := piQ H ⟨w, hwH⟩ with hW
  have hW₁ : W * A₁ * W⁻¹ = A₁⁻¹ := (inv_iff hwH ha₁H).mp hw₁
  have hW₂ : W * A₂ * W⁻¹ = A₂ := (cent_iff hwH ha₂H).mp hw₂
  have hR₁ : R * A₁ * R⁻¹ = A₁⁻¹ := (inv_iff hr₁H ha₁H).mp hr₁a₁
  have hR₂ : R * A₂ * R⁻¹ = A₂ := (cent_iff hr₁H ha₂H).mp hr₁a₂
  have hA₁A₂ : A₁ * A₂ = A₂ * A₁ := by
    have := (cent_iff ha₁H ha₂H).mp ha₁a₂
    exact mul_inv_eq_iff_eq_mul.mp this
  have hRR : R * R = 1 := by
    rw [← map_mul]
    exact (piQ_eq_one_iff H _).mpr hr₁r₁
  have hWW : W * W = 1 := by
    rw [← map_mul]
    refine (piQ_eq_one_iff H _).mpr ?_
    show w * w ∈ pCoreOf 2 H
    rw [hw2]
    exact (pCoreOf 2 H).one_mem
  have hA₂p : A₂ ^ p = 1 := by
    rw [← map_pow]
    exact (piQ_eq_one_iff H _).mpr (by simpa using ha₂p)
  have hA₂ne : A₂ ≠ 1 := fun e => ha₂Q ((piQ_eq_one_iff H _).mp e)
  have hyH : w * (r₁ : G)⁻¹ ∈ H := H.mul_mem hwH (H.inv_mem hr₁H)
  have hY : piQ H ⟨w * (r₁ : G)⁻¹, hyH⟩ = W * R⁻¹ := by
    have e : (⟨w * (r₁ : G)⁻¹, hyH⟩ : ↥H) = ⟨w, hwH⟩ * ⟨(r₁ : G), hr₁H⟩⁻¹ := rfl
    rw [e, map_mul, map_inv]
  have hRi₁ : R⁻¹ * A₁ * R = A₁⁻¹ := conj_inv_of_inv hR₁
  have hRi₂ : R⁻¹ * A₂ * R = A₂ := conj_inv_of_cent hR₂
  have hy₁ : (w * (r₁ : G)⁻¹) * (a₁ : G) * (w * (r₁ : G)⁻¹)⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H := by
    rw [cent_iff hyH ha₁H, hY]
    calc (W * R⁻¹) * A₁ * (W * R⁻¹)⁻¹ = W * (R⁻¹ * A₁ * R) * W⁻¹ := by group
      _ = W * A₁⁻¹ * W⁻¹ := by rw [hRi₁]
      _ = (W * A₁ * W⁻¹)⁻¹ := by group
      _ = A₁ := by rw [hW₁, inv_inv]
  have hy₂ : (w * (r₁ : G)⁻¹) * (a₂ : G) * (w * (r₁ : G)⁻¹)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H := by
    rw [cent_iff hyH ha₂H, hY]
    calc (W * R⁻¹) * A₂ * (W * R⁻¹)⁻¹ = W * (R⁻¹ * A₂ * R) * W⁻¹ := by group
      _ = W * A₂ * W⁻¹ := by rw [hRi₂]
      _ = A₂ := hW₂
  have hyPQ : w * (r₁ : G)⁻¹ ∈ PQ :=
    h.mem_pq_of_centralizes S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hyH hy₁ hy₂
  obtain ⟨i, j, hij⟩ := h.pq_rot_K S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ _ hyPQ
  have hYe : W * R⁻¹ = A₁ ^ i * A₂ ^ j := by rw [← hY]; exact hij
  have hWe : W = (A₁ ^ i * A₂ ^ j) * R := by
    rw [← hYe]
    group
  have hc : A₁ ^ i * A₂ ^ j = A₂ ^ j * A₁ ^ i := (Commute.pow_pow hA₁A₂ i j).eq
  have hconjR : R * (A₁ ^ i * A₂ ^ j) * R⁻¹ = (A₁ ^ i)⁻¹ * A₂ ^ j := by
    have e1 : R * A₁ ^ i * R⁻¹ = (A₁⁻¹) ^ i := by rw [← conj_pow, hR₁]
    have e2 : R * A₂ ^ j * R⁻¹ = A₂ ^ j := by rw [← conj_pow, hR₂]
    calc R * (A₁ ^ i * A₂ ^ j) * R⁻¹ = (R * A₁ ^ i * R⁻¹) * (R * A₂ ^ j * R⁻¹) := by group
      _ = (A₁ ^ i)⁻¹ * A₂ ^ j := by rw [e1, e2, inv_pow]
  have hW2j : A₂ ^ j * A₂ ^ j = 1 := by
    have h1 : W * W = (A₁ ^ i * A₂ ^ j) * (R * (A₁ ^ i * A₂ ^ j) * R⁻¹) * (R * R) := by
      rw [hWe]
      group
    rw [hWW, hconjR, hRR, mul_one, hc] at h1
    have h2 : A₂ ^ j * A₁ ^ i * ((A₁ ^ i)⁻¹ * A₂ ^ j) = A₂ ^ j * A₂ ^ j := by group
    rw [h2] at h1
    exact h1.symm
  have hA₂j : A₂ ^ j = 1 := by
    have h1 : A₂ ^ (j + j) = 1 := by rw [pow_add]; exact hW2j
    have hord : orderOf A₂ = p := by
      have hd : orderOf A₂ ∣ p := orderOf_dvd_of_pow_eq_one hA₂p
      rcases (Nat.dvd_prime hp).mp hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hA₂ne
      · exact h1
    have hd2 : p ∣ j + j := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one h1
    have hd3 : p ∣ j := by
      have : p ∣ 2 * j := by rwa [two_mul]
      rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2) hred.odd
      · exact h2
    rw [← hord] at hd3
    exact orderOf_dvd_iff_pow_eq_one.mp hd3
  have hYa : piQ H ⟨w * (r₁ : G)⁻¹, hyH⟩ = piQ H ⟨(a₁ : G) ^ i, H.pow_mem ha₁H i⟩ := by
    have e : (⟨(a₁ : G) ^ i, H.pow_mem ha₁H i⟩ : ↥H) = ⟨(a₁ : G), ha₁H⟩ ^ i := rfl
    rw [e, map_pow, hY, hYe, hA₂j, mul_one]
  have hq : ((⟨w * (r₁ : G)⁻¹, hyH⟩ : ↥H)⁻¹ * ⟨(a₁ : G) ^ i, H.pow_mem ha₁H i⟩ : ↥H) ∈
      (pCoreOf 2 H).subgroupOf H :=
    QuotientGroup.eq.mp hYa
  have hqQ : (w * (r₁ : G)⁻¹)⁻¹ * (a₁ : G) ^ i ∈ pCoreOf 2 H := hq
  have hyH₁ : w * (r₁ : G)⁻¹ ∈ H₁ := by
    have e : w * (r₁ : G)⁻¹ = (a₁ : G) ^ i * ((w * (r₁ : G)⁻¹)⁻¹ * (a₁ : G) ^ i)⁻¹ := by group
    rw [e]
    exact H₁.mul_mem (H₁.pow_mem a₁.2 i) (H₁.inv_mem (h.Q₁ hqQ))
  have e : w = (w * (r₁ : G)⁻¹) * (r₁ : G) := by group
  rw [e]
  exact H₁.mul_mem hyH₁ r₁.2

end Refl


section Count

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDecP.relIndex_le_four (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {B : Subgroup G} (hBH : B ≤ H) (hBab : IsElemAbelian 2 B)
    (hB₁ : ∀ x ∈ B, x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ∨
      x * (a₁ : G) * x⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hB₂ : ∀ x ∈ B, x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H ∨
      x * (a₂ : G) * x⁻¹ * (a₂ : G) ∈ pCoreOf 2 H) :
    (B ⊓ pCoreOf 2 H).relIndex B ≤ 4 := by
  classical
  unfold Subgroup.relIndex
  let N : Subgroup ↥B := (B ⊓ pCoreOf 2 H).subgroupOf B
  let g : (↥B ⧸ N) → Bool × Bool := fun q =>
    (decide ((q.out : G) * (a₁ : G) * (q.out : G)⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H),
      decide ((q.out : G) * (a₂ : G) * (q.out : G)⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H))
  have hinj : Function.Injective g := by
    intro q q' hqq
    have hs₁ := decide_eq_decide.mp (congrArg Prod.fst hqq)
    have hs₂ := decide_eq_decide.mp (congrArg Prod.snd hqq)
    set x : ↥B := q.out with hx
    set y : ↥B := q'.out with hy
    have hxH : (x : G) ∈ H := hBH x.2
    have hyH : (y : G) ∈ H := hBH y.2
    have hz : (x : G)⁻¹ * (y : G) ∈ B := B.mul_mem (B.inv_mem x.2) y.2
    have hz2 : ((x : G)⁻¹ * (y : G)) * ((x : G)⁻¹ * (y : G)) = 1 := by
      have := isElemAbelian_pow_eq_one hBab hz
      simpa [pow_two] using this
    have hzQ : (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 H :=
      h.mem_pCore_of_same_type S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hxH hyH hz2 (hB₁ _ x.2)
        (hB₁ _ y.2) hs₁ (hB₂ _ x.2) (hB₂ _ y.2) hs₂
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ⟨hz, hzQ⟩)
  calc Subgroup.index N = Nat.card (↥B ⧸ N) := rfl
    _ ≤ Nat.card (Bool × Bool) := Nat.card_le_card_of_injective g hinj
    _ = 4 := by simp


theorem IsDecP.relIndex_le_two_of_cent (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) (φ₁ : ↥H₁ →* DihedralGroup p)
    (hker₁ : ∀ y : ↥H₁, φ₁ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₁ : ↥H₁}
    (ha₁ : φ₁ a₁ = DihedralGroup.r 1) (φ₂ : ↥H₂ →* DihedralGroup p)
    (hker₂ : ∀ y : ↥H₂, φ₂ y = 1 ↔ (y : G) ∈ pCoreOf 2 H) {a₂ : ↥H₂}
    (ha₂ : φ₂ a₂ = DihedralGroup.r 1) {B : Subgroup G} (hBH : B ≤ H) (hBab : IsElemAbelian 2 B)
    (hB₁ : ∀ x ∈ B, x * (a₁ : G) * x⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H ∨
      x * (a₁ : G) * x⁻¹ * (a₁ : G) ∈ pCoreOf 2 H)
    (hB₂ : ∀ x ∈ B, x * (a₂ : G) * x⁻¹ * (a₂ : G)⁻¹ ∈ pCoreOf 2 H) :
    (B ⊓ pCoreOf 2 H).relIndex B ≤ 2 := by
  classical
  unfold Subgroup.relIndex
  let N : Subgroup ↥B := (B ⊓ pCoreOf 2 H).subgroupOf B
  let g : (↥B ⧸ N) → Bool := fun q =>
    decide ((q.out : G) * (a₁ : G) * (q.out : G)⁻¹ * (a₁ : G)⁻¹ ∈ pCoreOf 2 H)
  have hinj : Function.Injective g := by
    intro q q' hqq
    have hs₁ := decide_eq_decide.mp hqq
    set x : ↥B := q.out with hx
    set y : ↥B := q'.out with hy
    have hxH : (x : G) ∈ H := hBH x.2
    have hyH : (y : G) ∈ H := hBH y.2
    have hz : (x : G)⁻¹ * (y : G) ∈ B := B.mul_mem (B.inv_mem x.2) y.2
    have hz2 : ((x : G)⁻¹ * (y : G)) * ((x : G)⁻¹ * (y : G)) = 1 := by
      have := isElemAbelian_pow_eq_one hBab hz
      simpa [pow_two] using this
    have hzQ : (x : G)⁻¹ * (y : G) ∈ pCoreOf 2 H :=
      h.mem_pCore_of_same_type S hred φ₁ hker₁ ha₁ φ₂ hker₂ ha₂ hxH hyH hz2 (hB₁ _ x.2)
        (hB₁ _ y.2) hs₁ (Or.inl (hB₂ _ x.2)) (Or.inl (hB₂ _ y.2))
        ⟨fun _ => hB₂ _ y.2, fun _ => hB₂ _ x.2⟩
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
    exact QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ⟨hz, hzQ⟩)
  calc Subgroup.index N = Nat.card (↥B ⧸ N) := rfl
    _ ≤ Nat.card Bool := Nat.card_le_card_of_injective g hinj
    _ = 2 := by simp

end Count

end CFSG.Quasithin
