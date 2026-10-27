module

public import CFSG.Walter.W67.Section6.Core62L

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

omit [Finite G] in
theorem exists_pow_eq_mul {b a : G} (hb : b ∈ P₁) (ha : a ∈ P₀) (n : ℕ) :
    ∃ b' ∈ P₁, (b * a) ^ n = b' * a ^ n := by
  induction n with
  | zero => exact ⟨1, P₁.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨b', hb', e⟩ := ih
    refine ⟨b' * (a ^ n * b * (a ^ n)⁻¹), P₁.mul_mem hb'
      ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ (h.P₀_le_N ha) n) b).mp hb), ?_⟩
    rw [pow_succ, e, pow_succ]
    group

theorem conj_mul_inv_mem_V {g y : G} (hg : g ∈ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) :
    Set G)) (hy : y ∈ P₁) (hgy : g * y ^ r * g⁻¹ = y ^ r) : g * y * g⁻¹ * y⁻¹ ∈ Vsub x₀ y₀ := by
  have hu : g * y * g⁻¹ ∈ P₀ ⊔ P₁ :=
    (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_sup_right hy)
  obtain ⟨b, hb, a, ha, hba⟩ := h.mem_P.mp hu
  have hpow : (b * a) ^ r = y ^ r := by rw [hba, conj_pow, hgy]
  obtain ⟨b', hb', e⟩ := h.exists_pow_eq_mul hb ha r
  have har : a ^ r = 1 := by
    have h1 : a ^ r = b'⁻¹ * y ^ r := by rw [← hpow, e]; group
    have h2 : a ^ r ∈ P₀ ⊓ P₁ :=
      Subgroup.mem_inf.mpr ⟨P₀.pow_mem ha r, h1 ▸ P₁.mul_mem (P₁.inv_mem hb') (P₁.pow_mem hy r)⟩
    rwa [h.inf_eq_bot, Subgroup.mem_bot] at h2
  have haX := h.mem_X_of_pow ha har
  have haV : a ∈ Vsub x₀ y₀ := Subgroup.mem_sup_left haX
  have hab : b * a = a * b :=
    (Subgroup.mem_centralizer_iff.mp (h.V_le_center haV) b (Subgroup.mem_sup_right hb))
  have hay : y * a = a * y :=
    (Subgroup.mem_centralizer_iff.mp (h.V_le_center haV) y (Subgroup.mem_sup_right hy))
  have hby : (b * y⁻¹) ^ r = 1 := by
    have h1 : (b * a) ^ r = b ^ r := by rw [(show Commute b a from hab).mul_pow, har, mul_one]
    rw [(show Commute b y⁻¹ from h.P₁_comm b hb _ (P₁.inv_mem hy)).mul_pow, ← h1, hpow, inv_pow,
      mul_inv_cancel]
  have hbyY := h.mem_Y_of_pow (P₁.mul_mem hb (P₁.inv_mem hy)) hby
  have e2 : g * y * g⁻¹ * y⁻¹ = a * (b * y⁻¹) := by
    rw [← hba, hab]
    group
  rw [e2]
  exact (Vsub x₀ y₀).mul_mem haV (Subgroup.mem_sup_right hbyY)

section Detector

variable {S : Subgroup G} (c : CaseB r J x₀ y₀ P₀ P₁ S) {z : G} (hz : z ∈ S)
include c hz

theorem D_mem_Y {v : G} (hv : v ∈ Vsub x₀ y₀) : z * v * z⁻¹ * v⁻¹ ∈ Subgroup.zpowers y₀ := by
  have hyC := h.caseB_yC c
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_V_iff.mp hv
  obtain ⟨k, rfl⟩ := (isOfFinOrder_of_finite x₀).mem_powers_iff_mem_zpowers.mpr ha
  have h1 := (c.hx.pow hyC h.y₀_pow h.r_odd k).2.2 z hz
  have hbz : z * b = b * z := (IsT.comm_of_mem_zpowers hyC hb hz).symm
  have e : z * (x₀ ^ k * b) * z⁻¹ * (x₀ ^ k * b)⁻¹ = z * x₀ ^ k * z⁻¹ * (x₀ ^ k)⁻¹ := by
    calc z * (x₀ ^ k * b) * z⁻¹ * (x₀ ^ k * b)⁻¹
        = z * x₀ ^ k * (z⁻¹ * (z * b * z⁻¹) * b⁻¹) * (x₀ ^ k)⁻¹ := by group
      _ = z * x₀ ^ k * z⁻¹ * (x₀ ^ k)⁻¹ := by rw [hbz]; group
  rw [e]
  exact h1

theorem D_mul {v₁ v₂ : G} (hv₁ : v₁ ∈ Vsub x₀ y₀) (hv₂ : v₂ ∈ Vsub x₀ y₀) :
    z * (v₁ * v₂) * z⁻¹ * (v₁ * v₂)⁻¹ = (z * v₁ * z⁻¹ * v₁⁻¹) * (z * v₂ * z⁻¹ * v₂⁻¹) := by
  have hyC := h.caseB_yC c
  have hD := h.D_mem_Y c hz hv₂
  have hv₁S : v₁ ∈ S := c.hPS (h.V_le_P hv₁)
  have e : z * (v₁ * v₂) * z⁻¹ * (v₁ * v₂)⁻¹ =
      (z * v₁ * z⁻¹ * v₁⁻¹) * (v₁ * (z * v₂ * z⁻¹ * v₂⁻¹) * v₁⁻¹) := by group
  rw [e, ← IsT.comm_of_mem_zpowers hyC hD hv₁S, mul_inv_cancel_right]

theorem D_Y {u : G} (hu : u ∈ Subgroup.zpowers y₀) : z * u * z⁻¹ * u⁻¹ = 1 := by
  rw [← IsT.comm_of_mem_zpowers (h.caseB_yC c) hu hz, mul_inv_cancel_right, mul_inv_cancel]

theorem D_conj {v : G} (hv : v ∈ Vsub x₀ y₀) :
    z * (z * v * z⁻¹) * z⁻¹ * (z * v * z⁻¹)⁻¹ = z * v * z⁻¹ * v⁻¹ := by
  have hD := h.D_mem_Y c hz hv
  calc z * (z * v * z⁻¹) * z⁻¹ * (z * v * z⁻¹)⁻¹
      = z * ((z * v * z⁻¹ * v⁻¹) * v) * z⁻¹ * ((z * v * z⁻¹ * v⁻¹) * v)⁻¹ := by group
    _ = (z * (z * v * z⁻¹ * v⁻¹) * z⁻¹ * (z * v * z⁻¹ * v⁻¹)⁻¹) * (z * v * z⁻¹ * v⁻¹) :=
        h.D_mul c hz (Subgroup.mem_sup_right hD) hv
    _ = z * v * z⁻¹ * v⁻¹ := by rw [h.D_Y c hz hD, one_mul]

theorem D_pow {v : G} (hv : v ∈ Vsub x₀ y₀) (k : ℕ) :
    z * v ^ k * z⁻¹ * (v ^ k)⁻¹ = (z * v * z⁻¹ * v⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.D_mul c hz (Subgroup.pow_mem _ hv k) hv, ih, pow_succ]

omit c hz in
theorem phi_pow {y : G} (hy : y ∈ P₀ ⊔ P₁) (hφ : z * y * z⁻¹ * y⁻¹ ∈ Vsub x₀ y₀) (k : ℕ) :
    z * y ^ k * z⁻¹ * (y ^ k)⁻¹ = (z * y * z⁻¹ * y⁻¹) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc := Subgroup.mem_centralizer_iff.mp (h.V_le_center hφ) _ (Subgroup.pow_mem _ hy k)
    have e : z * y ^ (k + 1) * z⁻¹ * (y ^ (k + 1))⁻¹ =
        (z * y ^ k * z⁻¹ * (y ^ k)⁻¹) * (y ^ k * (z * y * z⁻¹ * y⁻¹) * (y ^ k)⁻¹) := by
      rw [pow_succ]
      group
    rw [e, ih, hc, mul_inv_cancel_right, pow_succ]

theorem phi_zpow {y : G} (hφ : z * y * z⁻¹ * y⁻¹ ∈ Vsub x₀ y₀) (n : ℕ) :
    z ^ n * y * (z ^ n)⁻¹ * y⁻¹ ∈ Vsub x₀ y₀ ∧
      z * (z ^ n * y * (z ^ n)⁻¹ * y⁻¹) * z⁻¹ * (z ^ n * y * (z ^ n)⁻¹ * y⁻¹)⁻¹ =
        (z * (z * y * z⁻¹ * y⁻¹) * z⁻¹ * (z * y * z⁻¹ * y⁻¹)⁻¹) ^ n := by
  have hzV : z ∈ Subgroup.normalizer ((Vsub x₀ y₀ : Subgroup G) : Set G) :=
    h.normalizer_le (h.le_normalizer_of_isT c.hS c.hPS c.hx hz)
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hV, hD⟩ := ih
    have e : z ^ (n + 1) * y * (z ^ (n + 1))⁻¹ * y⁻¹ =
        (z * (z ^ n * y * (z ^ n)⁻¹ * y⁻¹) * z⁻¹) * (z * y * z⁻¹ * y⁻¹) := by
      rw [pow_succ']
      group
    have hzw : z * (z ^ n * y * (z ^ n)⁻¹ * y⁻¹) * z⁻¹ ∈ Vsub x₀ y₀ :=
      (Subgroup.mem_normalizer_iff.mp hzV _).mp hV
    refine ⟨by rw [e]; exact (Vsub x₀ y₀).mul_mem hzw hφ, ?_⟩
    rw [e, h.D_mul c hz hzw hφ, h.D_conj c hz hV, hD, pow_succ]

end Detector

section Zeta

variable {S : Subgroup G} (c : CaseB r J x₀ y₀ P₀ P₁ S) {z : G} (hz : z ∈ S)
  (hzJ : J * z * J⁻¹ = z⁻¹) (hzx : z * x₀ * z⁻¹ * x₀⁻¹ ≠ 1)
  (hnz : ¬ ∀ y ∈ P₁, z * y = y * z)
include c hz hzJ hzx hnz

omit [Finite G] c hz hzJ hzx in
theorem exists_y₁ : ∃ y₁ ∈ P₁, z * y₁ ≠ y₁ * z ∧ z * y₁ ^ r = y₁ ^ r * z := by
  classical
  obtain ⟨⟨g₁, hg₁⟩, hg₁gen⟩ := h.P₁_cyc.exists_generator
  have hP₁g : P₁ ≤ Subgroup.zpowers g₁ := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg₁gen ⟨a, ha⟩)
    have : g₁ ^ k = a := congrArg Subtype.val hk
    rw [← this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers g₁) k
  have hg₁z : z * g₁ ≠ g₁ * z := by
    intro hc
    apply hnz
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hP₁g hy)
    exact (Commute.zpow_right (show Commute z g₁ from hc) k).eq
  obtain ⟨β, hβ⟩ := (IsPGroup.iff_orderOf.mp h.P₁_r) ⟨g₁, hg₁⟩
  rw [Subgroup.orderOf_mk] at hβ
  have hex : ∃ i : ℕ, z * g₁ ^ (r ^ i) = g₁ ^ (r ^ i) * z :=
    ⟨β, by rw [← hβ, pow_orderOf_eq_one, mul_one, one_mul]⟩
  have hi₀ := Nat.find_spec hex
  have hi₀0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hi₀
    exact hg₁z hi₀
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  refine ⟨g₁ ^ (r ^ j), P₁.pow_mem hg₁ _, Nat.find_min hex (by omega), ?_⟩
  rw [← pow_mul, ← pow_succ, ← hj]
  exact hi₀

theorem false_of_caseB_zeta : False := by
  have hyC := h.caseB_yC c
  have hSN := h.le_normalizer_of_isT c.hS c.hPS c.hx
  have hzN := hSN hz
  have : Fact (1 < r) := ⟨(Fact.out : r.Prime).one_lt⟩
  obtain ⟨y₁, hy₁, hy₁z, hy₁r⟩ := h.exists_y₁ hnz
  have hy₁r' : z * y₁ ^ r * z⁻¹ = y₁ ^ r := by rw [hy₁r, mul_inv_cancel_right]
  have hφV := h.conj_mul_inv_mem_V hzN hy₁ hy₁r'
  have hy₁P : y₁ ∈ P₀ ⊔ P₁ := Subgroup.mem_sup_right hy₁
  obtain ⟨a₁, ha₁, b₁, hb₁, hφab⟩ := h.mem_V_iff.mp hφV
  have ha₁1 : a₁ ≠ 1 := by
    intro h1
    apply hy₁z
    refine h.caseB_comm_of_mem c hz hzJ hy₁ ?_
    have e : z * y₁ * z⁻¹ = (z * y₁ * z⁻¹ * y₁⁻¹) * y₁ := by group
    rw [e, ← hφab, h1, one_mul]
    exact P₁.mul_mem ((Subgroup.zpowers_le.mpr h.y₀_mem) hb₁) hy₁
  set t₀ := z * (z * y₁ * z⁻¹ * y₁⁻¹) * z⁻¹ * (z * y₁ * z⁻¹ * y₁⁻¹)⁻¹ with ht₀
  have ht₀a : t₀ = z * a₁ * z⁻¹ * a₁⁻¹ := by
    rw [ht₀, ← hφab, h.D_mul c hz (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right hb₁),
      h.D_Y c hz hb₁, mul_one]
  have ht₀Y : t₀ ∈ Subgroup.zpowers y₀ := h.D_mem_Y c hz hφV
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    rw [ht₀a] at h1
    apply hzx
    have hza : z * a₁ = a₁ * z := by
      calc z * a₁ = z * a₁ * z⁻¹ * a₁⁻¹ * a₁ * z := by group
        _ = a₁ * z := by rw [h1, one_mul]
    have ha₁P₀ : a₁ ∈ P₀ := (Subgroup.zpowers_le.mpr h.x₀_mem) ha₁
    have ha₁r : a₁ ^ r = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha₁
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_x₀,
        pow_orderOf_eq_one, one_zpow]
    have hzz := zpowers_eq_of_cyclic h.P₀_cyc ha₁P₀ h.x₀_mem
      (by rw [orderOf_eq_prime ha₁r ha₁1, h.orderOf_x₀])
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hzz ▸ Subgroup.mem_zpowers x₀)
    rw [← hk, (Commute.zpow_right (show Commute z a₁ from hza) k).eq, mul_inv_cancel_right,
      mul_inv_cancel]
  have ht₀o : orderOf t₀ = r :=
    orderOf_eq_prime (IsT.pow_eq_one_of_mem_zpowers h.y₀_pow ht₀Y) ht₀1
  obtain ⟨d', hd'S, hd'P, hd'J, hd'x, ⟨m, hd'y, hm1⟩, hd'o⟩ :=
    h.exists_d' c.hS c.hScard c.hPS c.hJS c.hSP c.hx
  have hd'Y : ∀ u ∈ Subgroup.zpowers y₀, d' * u * d'⁻¹ = u ^ m := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [← conj_zpow, hd'y, ← zpow_natCast, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hd'x' : d'⁻¹ * x₀ * d' = x₀ := by
    calc d'⁻¹ * x₀ * d' = d'⁻¹ * (d' * x₀ * d'⁻¹) * d' := by rw [hd'x]
      _ = x₀ := by group
  have hd'X : ∀ a ∈ Subgroup.zpowers x₀, d' * a * d'⁻¹ = a := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, hd'x]
  have hz'S : d' * z * d'⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hd'S z).mp hz
  have hzNP : Subgroup.zpowers z ≤ Subgroup.normalizer ((P₀ ⊔ P₁ : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hzN
  obtain ⟨p, hp, e₁, he₁, hpe⟩ :=
    (mem_sup_iff_of_le_normalizer hzNP).mp (h.caseB_sup c hz hzx hz'S)
  obtain ⟨a, rfl⟩ := (isOfFinOrder_of_finite z).mem_powers_iff_mem_zpowers.mpr he₁
  have hc₀Y : z * x₀ * z⁻¹ * x₀⁻¹ ∈ Subgroup.zpowers y₀ := c.hx.2.2 z hz
  have hc₀o : orderOf (z * x₀ * z⁻¹ * x₀⁻¹) = r :=
    orderOf_eq_prime (IsT.pow_eq_one_of_mem_zpowers h.y₀_pow hc₀Y) hzx
  have hpx : p * x₀ * p⁻¹ * x₀⁻¹ = 1 := by
    rw [Subgroup.mem_centralizer_iff.mp h.x₀_mem_center p hp, mul_inv_cancel_right,
      mul_inv_cancel]
  have hA : (z * x₀ * z⁻¹ * x₀⁻¹) ^ m = (z * x₀ * z⁻¹ * x₀⁻¹) ^ a := by
    have h1 : (d' * z * d'⁻¹) * x₀ * (d' * z * d'⁻¹)⁻¹ * x₀⁻¹ = (z * x₀ * z⁻¹ * x₀⁻¹) ^ m := by
      rw [← hd'Y _ hc₀Y]
      calc (d' * z * d'⁻¹) * x₀ * (d' * z * d'⁻¹)⁻¹ * x₀⁻¹
          = d' * (z * (d'⁻¹ * x₀ * d') * z⁻¹ * (d'⁻¹ * x₀ * d')⁻¹) * d'⁻¹ := by group
        _ = d' * (z * x₀ * z⁻¹ * x₀⁻¹) * d'⁻¹ := by rw [hd'x']
    have h2 : (p * z ^ a) * x₀ * (p * z ^ a)⁻¹ * x₀⁻¹ = (z * x₀ * z⁻¹ * x₀⁻¹) ^ a := by
      rw [IsT.conj_mul hyC c.hx (c.hPS hp) (S.pow_mem hz a), c.hx.conj_pow hyC hz a, hpx, one_mul]
    rw [← h1, ← h2, ← hpe]
  have hd'P₁ : d' * y₁ * d'⁻¹ ∈ P₁ := by
    apply h.mem_P₁_of_inv ((Subgroup.mem_normalizer_iff.mp hd'P y₁).mp hy₁P)
    calc J * (d' * y₁ * d'⁻¹) * J⁻¹ = (J * d') * y₁ * (J * d')⁻¹ := by group
      _ = (d' * J) * y₁ * (d' * J)⁻¹ := by rw [hd'J]
      _ = d' * (J * y₁ * J⁻¹) * d'⁻¹ := by group
      _ = (d' * y₁ * d'⁻¹)⁻¹ := by rw [h.P₁_inv y₁ hy₁]; group
  have hzz := zpowers_eq_of_cyclic h.P₁_cyc hd'P₁ hy₁ (orderOf_conj_mul d' y₁)
  obtain ⟨b, hb⟩ := (isOfFinOrder_of_finite y₁).mem_powers_iff_mem_zpowers.mpr
    (hzz ▸ Subgroup.mem_zpowers (d' * y₁ * d'⁻¹))
  have hb' : y₁ ^ b = d' * y₁ * d'⁻¹ := hb
  have hy₁1 : y₁ ≠ 1 := fun h1 => hy₁z (by rw [h1]; group)
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, y₁ ^ n = y₀ := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h.P₁_r) ⟨y₁, hy₁⟩
    rw [Subgroup.orderOf_mk] at hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hy₁1 hk
    have hdvd : r ∣ orderOf y₁ := by rw [hk]; exact dvd_pow_self r hk0
    have ho := orderOf_pow_orderOf_div (orderOf_pos y₁).ne' hdvd
    have hz' := zpowers_eq_of_cyclic h.P₁_cyc (P₁.pow_mem hy₁ _) h.y₀_mem
      (by rw [ho, h.orderOf_y₀])
    obtain ⟨k', hk'⟩ := (isOfFinOrder_of_finite _).mem_powers_iff_mem_zpowers.mpr
      (hz' ▸ Subgroup.mem_zpowers y₀)
    exact ⟨orderOf y₁ / r * k', by rw [pow_mul]; exact hk'⟩
  have hB : y₀ ^ b = y₀ ^ m := by
    rw [← hd'y, ← hn₀, ← conj_pow, ← hb', ← pow_mul, ← pow_mul, mul_comm]
  have hd'V : d' ∈ Subgroup.normalizer ((Vsub x₀ y₀ : Subgroup G) : Set G) := h.normalizer_le hd'P
  have hC1 : d' * (z * y₁ * z⁻¹ * y₁⁻¹) * d'⁻¹ =
      (p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹ := by
    rw [hpe, hb']
    group
  have hC2 : z * (d' * (z * y₁ * z⁻¹ * y₁⁻¹) * d'⁻¹) * z⁻¹ *
      (d' * (z * y₁ * z⁻¹ * y₁⁻¹) * d'⁻¹)⁻¹ = t₀ := by
    have hb₁' : d' * b₁ * d'⁻¹ ∈ Subgroup.zpowers y₀ := by
      rw [hd'Y b₁ hb₁]
      exact Subgroup.pow_mem _ hb₁ m
    have e : d' * (z * y₁ * z⁻¹ * y₁⁻¹) * d'⁻¹ = a₁ * (d' * b₁ * d'⁻¹) := by
      rw [← hφab, show d' * (a₁ * b₁) * d'⁻¹ = (d' * a₁ * d'⁻¹) * (d' * b₁ * d'⁻¹) by group,
        hd'X a₁ ha₁]
    rw [e, h.D_mul c hz (Subgroup.mem_sup_left ha₁) (Subgroup.mem_sup_right hb₁'),
      h.D_Y c hz hb₁', mul_one, ht₀a]
  have hφb : z * y₁ ^ b * z⁻¹ * (y₁ ^ b)⁻¹ = (z * y₁ * z⁻¹ * y₁⁻¹) ^ b := h.phi_pow hy₁P hφV b
  have hφbV : z * y₁ ^ b * z⁻¹ * (y₁ ^ b)⁻¹ ∈ Vsub x₀ y₀ := by
    rw [hφb]
    exact Subgroup.pow_mem _ hφV b
  obtain ⟨hVa, hDa⟩ := h.phi_zpow c hz hφbV a
  have hDb : z * (z * y₁ ^ b * z⁻¹ * (y₁ ^ b)⁻¹) * z⁻¹ * (z * y₁ ^ b * z⁻¹ * (y₁ ^ b)⁻¹)⁻¹ =
      t₀ ^ b := by
    rw [hφb, h.D_pow c hz hφV b]
  have hpV : p * (z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹) * p⁻¹ =
      z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹ := by
    rw [Subgroup.mem_centralizer_iff.mp (h.V_le_center hVa) p hp, mul_inv_cancel_right]
  have e3 : (p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹ =
      (z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹) * (p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹) := by
    rw [← hpV]
    group
  have hw₂V : p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹ ∈ Vsub x₀ y₀ := by
    have h1 : (p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹ ∈ Vsub x₀ y₀ := by
      rw [← hC1]
      exact (Subgroup.mem_normalizer_iff.mp hd'V _).mp hφV
    have e4 : p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹ = (z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹)⁻¹ *
        ((p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹) := by
      rw [e3]
      group
    rw [e4]
    exact (Vsub x₀ y₀).mul_mem ((Vsub x₀ y₀).inv_mem hVa) h1
  have hw₂P : p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹ ∈ P₁ :=
    P₁.mul_mem ((Subgroup.mem_normalizer_iff.mp ((sup_le h.P₀_le_N Subgroup.le_normalizer) hp)
      _).mp (P₁.pow_mem hy₁ b)) (P₁.inv_mem (P₁.pow_mem hy₁ b))
  have hw₂Y := h.mem_Y_of_pow hw₂P (h.V_pow hw₂V)
  have hD : t₀ = t₀ ^ (b * a) := by
    calc t₀ = z * ((p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹) * z⁻¹ *
          ((p * z ^ a) * y₁ ^ b * (p * z ^ a)⁻¹ * (y₁ ^ b)⁻¹)⁻¹ := by rw [← hC1, hC2]
      _ = (z * (z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹) * z⁻¹ *
            (z ^ a * y₁ ^ b * (z ^ a)⁻¹ * (y₁ ^ b)⁻¹)⁻¹) *
          (z * (p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹) * z⁻¹ * (p * y₁ ^ b * p⁻¹ * (y₁ ^ b)⁻¹)⁻¹) := by
          rw [e3, h.D_mul c hz hVa hw₂V]
      _ = (t₀ ^ b) ^ a := by rw [h.D_Y c hz hw₂Y, mul_one, hDa, hDb]
      _ = t₀ ^ (b * a) := by rw [← pow_mul]
  have hab : ((b * a : ℕ) : ZMod r) = 1 := by
    have h1 : t₀ ^ (b * a) = t₀ ^ 1 := by rw [← hD, pow_one]
    rw [pow_eq_pow_iff_modEq, ht₀o] at h1
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h1
    rw [this, Nat.cast_one]
  have hma : (m : ZMod r) = a := by
    rw [pow_eq_pow_iff_modEq, hc₀o] at hA
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hA
  have hmb : (m : ZMod r) = b := by
    rw [pow_eq_pow_iff_modEq, h.orderOf_y₀] at hB
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).mpr hB).symm
  have hm2 : (m : ZMod r) ^ 2 = 1 := by
    rw [pow_two]
    calc (m : ZMod r) * m = (b : ZMod r) * a := by rw [← hmb, ← hma]
      _ = 1 := by rw [← Nat.cast_mul]; exact hab
  have hmo : (m : ZMod r) ^ orderOf d' = 1 := by
    have h1 := conj_pow_eq_pow_pow hd'y (orderOf d')
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h1
    have h2 : y₀ ^ (m ^ orderOf d') = y₀ ^ 1 := by rw [← h1, pow_one]
    rw [pow_eq_pow_iff_modEq, h.orderOf_y₀] at h2
    have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2
    push_cast at this
    exact this
  apply hm1
  have hcop : Nat.Coprime 2 (orderOf d') := Nat.coprime_two_left.mpr hd'o
  have := (pow_gcd_eq_one (a := (m : ZMod r))).mpr ⟨hm2, hmo⟩
  rwa [hcop.gcd_eq_one, pow_one] at this

end Zeta

theorem false_of_caseB {S : Subgroup G} (c : CaseB r J x₀ y₀ P₀ P₁ S) : False := by
  obtain ⟨z, hz, hzJ, hzx⟩ := h.caseB_exists_z c
  by_cases hzP₁ : ∀ y ∈ P₁, z * y = y * z
  · exact h.false_of_caseB_eps c hz hzJ hzx hzP₁
  · exact h.false_of_caseB_zeta c hz hzJ hzx hzP₁

theorem elim : False := by
  obtain ⟨S, hPS, hS, hScard, hJS⟩ := h.exists_sylow
  by_cases hSP : S ≤ P₀ ⊔ P₁
  · have hPeq : P₀ ⊔ P₁ = S := le_antisymm hPS hSP
    exact h.false_of_card_P (by rw [hPeq]; exact hScard)
  · obtain ⟨w, hw, hwY, hwJ | hwJ⟩ := h.exists_w hS hPS hJS hSP
    · exact h.false_of_caseC ⟨hS, hPS, hJS, hSP, hw, hwY, hwJ⟩ hScard
    · exact h.false_of_caseB ⟨hS, hScard, hPS, hJS, hSP, h.isT_x₀ hS hPS hJS hSP hw hwY hwJ⟩

end Hyp62

end CFSG.Walter.W67.Sec6
