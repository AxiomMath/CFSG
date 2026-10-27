module

public import CFSG.Walter.Bender1970.S3.Involution
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G]

open scoped commutatorElement

@[expose] def IsT (S : Subgroup G) (y₀ : G) (r : ℕ) (t : G) : Prop :=
  t ∈ S ∧ t ^ r = 1 ∧ ∀ s ∈ S, s * t * s⁻¹ * t⁻¹ ∈ Subgroup.zpowers y₀

namespace IsT

variable {S : Subgroup G} {y₀ : G} {r : ℕ}

theorem comm_of_mem_zpowers (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) {c s : G}
    (hc : c ∈ Subgroup.zpowers y₀) (hs : s ∈ S) : c * s = s * c := by
  have : Subgroup.zpowers y₀ ≤ Subgroup.centralizer (S : Set G) := Subgroup.zpowers_le.mpr hyC
  exact (Subgroup.mem_centralizer_iff.mp (this hc) s hs).symm

theorem pow_eq_one_of_mem_zpowers (hyr : y₀ ^ r = 1) {c : G} (hc : c ∈ Subgroup.zpowers y₀) :
    c ^ r = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hyr, one_zpow]

theorem one : IsT S y₀ r 1 :=
  ⟨S.one_mem, one_pow r, fun s _ => by
    rw [mul_one, mul_inv_cancel, inv_one, mul_one]
    exact Subgroup.one_mem _⟩

theorem mul (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) (hyr : y₀ ^ r = 1) (hr : Odd r)
    {t₁ t₂ : G} (h₁ : IsT S y₀ r t₁) (h₂ : IsT S y₀ r t₂) : IsT S y₀ r (t₁ * t₂) := by
  obtain ⟨h₁S, h₁r, h₁c⟩ := h₁
  obtain ⟨h₂S, h₂r, h₂c⟩ := h₂
  refine ⟨S.mul_mem h₁S h₂S, ?_, fun s hs => ?_⟩
  · have hc := h₁c t₂ h₂S
    have hx : Commute ⁅t₂, t₁⁆ t₁ := comm_of_mem_zpowers hyC hc h₁S
    have hy : Commute ⁅t₂, t₁⁆ t₂ := comm_of_mem_zpowers hyC hc h₂S
    rw [mul_pow_of_commute_commutator hx hy r, h₁r, h₂r, one_mul, one_mul,
      Nat.choose_two_right]
    obtain ⟨m, hm⟩ := hr
    have e : r * (r - 1) / 2 = r * m := by
      rw [show r - 1 = 2 * m by omega, ← mul_assoc, mul_comm r 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by norm_num)]
    have hc' : ⁅t₂, t₁⁆ ^ r = 1 := pow_eq_one_of_mem_zpowers hyr hc
    rw [e, pow_mul, hc', one_pow]
  · have e : s * (t₁ * t₂) * s⁻¹ * (t₁ * t₂)⁻¹ =
        (s * t₁ * s⁻¹ * t₁⁻¹) * (t₁ * (s * t₂ * s⁻¹ * t₂⁻¹) * t₁⁻¹) := by group
    rw [e, ← comm_of_mem_zpowers hyC (h₂c s hs) h₁S, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (h₁c s hs) (h₂c s hs)

theorem inv (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) {t : G} (h : IsT S y₀ r t) :
    IsT S y₀ r t⁻¹ := by
  obtain ⟨hS, hr, hc⟩ := h
  refine ⟨S.inv_mem hS, by rw [inv_pow, hr, inv_one], fun s hs => ?_⟩
  have e : s * t⁻¹ * s⁻¹ * t⁻¹⁻¹ = t⁻¹ * (s * t * s⁻¹ * t⁻¹)⁻¹ * t := by group
  rw [e, ← comm_of_mem_zpowers hyC (Subgroup.inv_mem _ (hc s hs)) (S.inv_mem hS),
    inv_mul_cancel_right]
  exact Subgroup.inv_mem _ (hc s hs)

theorem pow (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) (hyr : y₀ ^ r = 1) (hr : Odd r)
    {t : G} (h : IsT S y₀ r t) (n : ℕ) : IsT S y₀ r (t ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact one
  | succ n ih => rw [pow_succ]; exact mul hyC hyr hr ih h

theorem conj {J : G} (hJ : J ∈ Subgroup.normalizer (S : Set G)) (hJy : J * y₀ * J⁻¹ = y₀⁻¹)
    {t : G} (h : IsT S y₀ r t) : IsT S y₀ r (J * t * J⁻¹) := by
  obtain ⟨hS, hr, hc⟩ := h
  refine ⟨(Subgroup.mem_normalizer_iff.mp hJ t).mp hS, by rw [conj_pow, hr]; group,
    fun s hs => ?_⟩
  have hs' : J⁻¹ * s * J ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hJ) s).mp hs
    simpa using this
  have e : s * (J * t * J⁻¹) * s⁻¹ * (J * t * J⁻¹)⁻¹ =
      J * ((J⁻¹ * s * J) * t * (J⁻¹ * s * J)⁻¹ * t⁻¹) * J⁻¹ := by group
  rw [e]
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc _ hs')
  rw [← hk, ← conj_zpow, hJy]
  exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y₀)) k

theorem conj_pow (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) {t : G} (h : IsT S y₀ r t)
    {a : G} (ha : a ∈ S) (n : ℕ) : a ^ n * t * (a ^ n)⁻¹ * t⁻¹ = (a * t * a⁻¹ * t⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) * t * (a ^ (n + 1))⁻¹ * t⁻¹ =
        a * (a ^ n * t * (a ^ n)⁻¹ * t⁻¹) * a⁻¹ * (a * t * a⁻¹ * t⁻¹) := by
      rw [pow_succ']
      group
    have hcm : (a * t * a⁻¹ * t⁻¹) ^ n ∈ Subgroup.zpowers y₀ :=
      Subgroup.pow_mem _ (h.2.2 a ha) n
    rw [e, ih, ← comm_of_mem_zpowers hyC hcm ha, mul_inv_cancel_right, pow_succ]

theorem comm_of_inv (hyC : y₀ ∈ Subgroup.centralizer (S : Set G)) (hyr : y₀ ^ r = 1)
    (hr : Odd r) {J : G} (hJy : J * y₀ * J⁻¹ = y₀⁻¹) {t : G} (h : IsT S y₀ r t)
    (htJ : J * t * J⁻¹ = t⁻¹) {s : G} (hs : s ∈ S) (hsJ : J * s * J⁻¹ = s⁻¹) :
    s * t = t * s := by
  set c := s * t * s⁻¹ * t⁻¹ with hc
  have hcY : c ∈ Subgroup.zpowers y₀ := h.2.2 s hs
  have h1 : J * c * J⁻¹ = c := by
    have e1 : J * c * J⁻¹ = (J * s * J⁻¹) * (J * t * J⁻¹) * (J * s * J⁻¹)⁻¹ *
        (J * t * J⁻¹)⁻¹ := by rw [hc]; group
    have e2 : s⁻¹ * t⁻¹ * s⁻¹⁻¹ * t⁻¹⁻¹ = (s⁻¹ * t⁻¹) * c * (s⁻¹ * t⁻¹)⁻¹ := by
      rw [hc]; group
    have hst : s⁻¹ * t⁻¹ ∈ S := S.mul_mem (S.inv_mem hs) (S.inv_mem h.1)
    rw [e1, hsJ, htJ, e2, ← comm_of_mem_zpowers hyC hcY hst, mul_inv_cancel_right]
  have h2 : J * c * J⁻¹ = c⁻¹ := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcY
    rw [← hk, ← conj_zpow, hJy, inv_zpow]
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    calc c * c = c * (J * c * J⁻¹) := by rw [h1]
      _ = 1 := by rw [h2, mul_inv_cancel]
  have hc1 : c = 1 := by
    have hcr := pow_eq_one_of_mem_zpowers hyr hcY
    have hd : orderOf c ∣ Nat.gcd 2 r := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2)
      (orderOf_dvd_of_pow_eq_one hcr)
    rw [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.mpr hr), Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact hd
  rw [hc] at hc1
  calc s * t = s * t * s⁻¹ * t⁻¹ * t * s := by group
    _ = t * s := by rw [hc1, one_mul]

end IsT

end CFSG.Walter.W67.Sec6
