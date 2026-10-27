module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1120V1Proof

open Subgroup
open scoped commutatorElement

section Chain

variable {G : Type*} [Group G]

theorem zpowers_chain {r : G} (hr : ∃ n : ℕ, r ^ 3 ^ n = 1) (i j : ℤ) :
    zpowers (r ^ i) ≤ zpowers (r ^ j) ∨ zpowers (r ^ j) ≤ zpowers (r ^ i) := by
  obtain ⟨n, hn⟩ := hr
  have hord : orderOf r ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  rw [zpowers_le_zpowers_iff, zpowers_le_zpowers_iff]
  have hi : i.gcd (orderOf r) ∣ 3 ^ n := (Nat.gcd_dvd_right _ _).trans hord
  have hj : j.gcd (orderOf r) ∣ 3 ^ n := (Nat.gcd_dvd_right _ _).trans hord
  obtain ⟨p, -, hp⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hi
  obtain ⟨q, -, hq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hj
  rw [hp, hq]
  rcases le_total p q with h | h
  · exact Or.inr (pow_dvd_pow 3 h)
  · exact Or.inl (pow_dvd_pow 3 h)

end Chain

section E

variable {G : Type*} [Group G] {B R : Subgroup G} {r a x : G}

theorem exists_zpow_mul_of_mem_sup {a z : G} (haB : a ∈ normalizer (B : Set G))
    (hz : z ∈ zpowers a ⊔ B) : ∃ i : ℤ, ∃ b ∈ B, z = a ^ i * b := by
  have hle : zpowers a ≤ normalizer (B : Set G) := zpowers_le.mpr haB
  have hz' : z ∈ ((zpowers a ⊔ B : Subgroup G) : Set G) := hz
  rw [coe_mul_of_left_le_normalizer_right _ _ hle] at hz'
  obtain ⟨u, hu, b, hb, rfl⟩ := Set.mem_mul.mp hz'
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
  exact ⟨i, b, hb, rfl⟩

theorem zpow_eq_one_of_commute {a x : G} (ha3 : a ^ 3 = 1) (hax : a * x ≠ x * a) (i : ℤ)
    (h : a ^ i * x = x * a ^ i) : a ^ i = 1 := by
  have hi : a ^ i = a ^ (i % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv i 3]
    rw [zpow_add, zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ha3, one_zpow,
      mul_one]
  have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · rw [hi, h0, zpow_zero]
  · exfalso
    rw [hi, h1, zpow_one] at h
    exact hax h
  · exfalso
    rw [hi, h2] at h
    have ha2 : a ^ (2 : ℤ) = a⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_add_one, show (2 : ℤ) + 1 = 3 by norm_num,
        show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, ha3]
    rw [ha2] at h
    apply hax
    calc a * x = a * (x * a⁻¹) * a := by group
      _ = a * (a⁻¹ * x) * a := by rw [h]
      _ = x * a := by group

theorem centralizer_le_B (hr3 : ∃ n : ℕ, r ^ 3 ^ n = 1)
    (hrB : r ∈ normalizer (B : Set G)) (haB : a ∈ normalizer (B : Set G))
    (hxB : x ∈ B) (hBc : ∀ u ∈ B, ∀ v ∈ B, u * v = v * u)
    (ha3 : a ^ 3 = 1) (hax : a * x ≠ x * a)
    (hRdec : ∀ y ∈ R, ∃ k : ℤ, ∃ b ∈ B, y = r ^ k * b) (haR : a ∈ R)
    {y : G} (hyR : y ∈ R) (hyx : y * x = x * y) : y ∈ B := by
  obtain ⟨k, b, hb, rfl⟩ := hRdec y hyR
  obtain ⟨κ, ba, hba, hae⟩ := hRdec a haR
  have hrk : r ^ k * x = x * r ^ k := by
    have h1 : (r ^ k * b) * x = x * (r ^ k * b) := hyx
    have hbx : b * x = x * b := hBc b hb x hxB
    have : r ^ k * x * b = x * r ^ k * b := by
      calc r ^ k * x * b = r ^ k * (x * b) := by rw [mul_assoc]
        _ = r ^ k * (b * x) := by rw [hbx]
        _ = (r ^ k * b) * x := by rw [mul_assoc]
        _ = x * (r ^ k * b) := h1
        _ = x * r ^ k * b := by rw [mul_assoc]
    exact mul_right_cancel this
  rcases zpowers_chain hr3 k κ with hle | hle
  ·
    have h1 : r ^ k ∈ zpowers (r ^ κ) := hle (mem_zpowers _)
    have hrκ : r ^ κ ∈ zpowers a ⊔ B := by
      have e : r ^ κ = a * ba⁻¹ := by rw [hae]; group
      rw [e]
      exact mul_mem ((le_sup_left : zpowers a ≤ zpowers a ⊔ B) (mem_zpowers a))
        ((le_sup_right : B ≤ zpowers a ⊔ B) (B.inv_mem hba))
    have hy : r ^ k * b ∈ zpowers a ⊔ B :=
      mul_mem (zpowers_le.mpr hrκ h1) ((le_sup_right : B ≤ zpowers a ⊔ B) hb)
    obtain ⟨i, b', hb', he⟩ := exists_zpow_mul_of_mem_sup haB hy
    have hb'x : b' * x = x * b' := hBc b' hb' x hxB
    have hai : a ^ i * x = x * a ^ i := by
      have h2 : (a ^ i * b') * x = x * (a ^ i * b') := by rw [← he]; exact hyx
      have : a ^ i * x * b' = x * a ^ i * b' := by
        calc a ^ i * x * b' = a ^ i * (x * b') := by rw [mul_assoc]
          _ = a ^ i * (b' * x) := by rw [hb'x]
          _ = (a ^ i * b') * x := by rw [mul_assoc]
          _ = x * (a ^ i * b') := h2
          _ = x * a ^ i * b' := by rw [mul_assoc]
      exact mul_right_cancel this
    have h1' := zpow_eq_one_of_commute ha3 hax i hai
    rw [he, h1', one_mul]
    exact hb'
  ·
    exfalso
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hle (mem_zpowers _))
    have hκx : r ^ κ * x = x * r ^ κ := by
      rw [← hm]
      exact ((Commute.zpow_left (show Commute (r ^ k) x from hrk) m)).eq
    apply hax
    have hbax : ba * x = x * ba := hBc ba hba x hxB
    rw [hae]
    calc r ^ κ * ba * x = r ^ κ * (ba * x) := by rw [mul_assoc]
      _ = r ^ κ * (x * ba) := by rw [hbax]
      _ = (r ^ κ * x) * ba := by rw [mul_assoc]
      _ = (x * r ^ κ) * ba := by rw [hκx]
      _ = x * (r ^ κ * ba) := by rw [mul_assoc]

theorem pow_three_mem_of_mul_mem {u b : G} (hu : u ∈ normalizer (B : Set G)) (hb : b ∈ B)
    (h : (u * b) ^ 3 ∈ B) : u ^ 3 ∈ B := by
  have hu' : u⁻¹ ∈ normalizer (B : Set G) := inv_mem hu
  have h1 : u⁻¹ * b * u ∈ B := by
    have := (mem_normalizer_iff.mp hu' b).mp hb
    simpa using this
  have h2 : (u⁻¹ * u⁻¹) * b * (u⁻¹ * u⁻¹)⁻¹ ∈ B :=
    (mem_normalizer_iff.mp (mul_mem hu' hu') b).mp hb
  have e : u ^ 3 = ((u * b) * (u * b) * (u * b)) *
      (((u⁻¹ * u⁻¹) * b * (u⁻¹ * u⁻¹)⁻¹) * (u⁻¹ * b * u) * b)⁻¹ := by
    group
  have h3 : (u * b) ^ 3 = (u * b) * (u * b) * (u * b) := pow_three' _
  rw [e]
  rw [h3] at h
  exact B.mul_mem h (B.inv_mem (B.mul_mem (B.mul_mem h2 h1) hb))

theorem mem_sup_zpowers_of_pow_three_mem {u : G} (hu3 : u ^ 3 ∈ B) {m : ℤ}
    (hm : ¬ (3 : ℤ) ∣ m) : u ∈ zpowers (u ^ m) ⊔ B := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, m = 3 * q + 1 ∨ m = 3 * q + 2 := ⟨m / 3, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j : ℤ, m * m = 1 + 3 * j := by
    rcases hq with h | h
    · exact ⟨3 * q * q + 2 * q, by rw [h]; ring⟩
    · exact ⟨3 * q * q + 4 * q + 1, by rw [h]; ring⟩
  have e : u = (u ^ m) ^ m * ((u ^ 3) ^ j)⁻¹ := by
    rw [← zpow_mul, hj, zpow_add, zpow_one]
    have : (u ^ 3) ^ j = u ^ (3 * j) := by
      rw [zpow_mul]
      norm_cast
    rw [this]
    group
  have hmem : (u ^ m) ^ m * ((u ^ 3) ^ j)⁻¹ ∈ zpowers (u ^ m) ⊔ B := by
    refine mul_mem ?_ ?_
    · exact (le_sup_left : zpowers (u ^ m) ≤ zpowers (u ^ m) ⊔ B) (zpow_mem (mem_zpowers _) m)
    · exact (le_sup_right : B ≤ zpowers (u ^ m) ⊔ B) (B.inv_mem (zpow_mem hu3 j))
  rwa [← e] at hmem

theorem mem_sup_of_pow_three_mem_B (hr3 : ∃ n : ℕ, r ^ 3 ^ n = 1)
    (hrB : r ∈ normalizer (B : Set G)) (haB' : a ∉ B)
    (hRdec : ∀ y ∈ R, ∃ k : ℤ, ∃ b ∈ B, y = r ^ k * b) (haR : a ∈ R)
    {y : G} (hyR : y ∈ R) (hy3 : y ^ 3 ∈ B) : y ∈ zpowers a ⊔ B := by
  obtain ⟨k, b, hb, rfl⟩ := hRdec y hyR
  obtain ⟨κ, ba, hba, hae⟩ := hRdec a haR
  have hrκ : r ^ κ ∈ zpowers a ⊔ B := by
    have e : r ^ κ = a * ba⁻¹ := by rw [hae]; group
    rw [e]
    exact mul_mem ((le_sup_left : zpowers a ≤ zpowers a ⊔ B) (mem_zpowers a))
      ((le_sup_right : B ≤ zpowers a ⊔ B) (B.inv_mem hba))
  have hu : r ^ k ∈ normalizer (B : Set G) := zpow_mem hrB k
  have hu3 : (r ^ k) ^ 3 ∈ B := pow_three_mem_of_mul_mem hu hb hy3
  have hbS : b ∈ zpowers a ⊔ B := (le_sup_right : B ≤ zpowers a ⊔ B) hb
  rcases zpowers_chain hr3 k κ with hle | hle
  · exact mul_mem (zpowers_le.mpr hrκ (hle (mem_zpowers _))) hbS
  · obtain ⟨m, hm⟩ := mem_zpowers_iff.mp (hle (mem_zpowers _))
    by_cases h3 : (3 : ℤ) ∣ m
    · exfalso
      obtain ⟨t, rfl⟩ := h3
      have : r ^ κ ∈ B := by
        rw [← hm, zpow_mul]
        have : (r ^ k) ^ (3 : ℤ) = (r ^ k) ^ 3 := zpow_ofNat _ 3
        rw [this]
        exact zpow_mem hu3 t
      apply haB'
      rw [hae]
      exact B.mul_mem this hba
    · have h1 := mem_sup_zpowers_of_pow_three_mem (B := B) hu3 h3
      rw [hm] at h1
      have h2 : zpowers (r ^ κ) ⊔ B ≤ zpowers a ⊔ B :=
        sup_le (zpowers_le.mpr hrκ) le_sup_right
      exact mul_mem (h2 h1) hbS

end E

section Comm

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_comm' {Y A N : Subgroup G}
    (hY : ∀ u ∈ Y, ∀ v ∈ Y, u * v = v * u) (hAY : A ≤ normalizer (Y : Set G))
    (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    (hAN : ∀ α ∈ A, ∀ y ∈ Y, α * y * α⁻¹ * y⁻¹ ∈ N) :
    ⁅Y ⊔ A, Y ⊔ A⁆ ≤ N := by
  have hset := coe_mul_of_right_le_normalizer_left Y A hAY
  rw [commutator_le]
  intro u hu v hv
  have hu' : u ∈ ((Y ⊔ A : Subgroup G) : Set G) := hu
  have hv' : v ∈ ((Y ⊔ A : Subgroup G) : Set G) := hv
  rw [hset] at hu' hv'
  obtain ⟨y₁, hy₁, a₁, ha₁, rfl⟩ := Set.mem_mul.mp hu'
  obtain ⟨y₂, hy₂, a₂, ha₂, rfl⟩ := Set.mem_mul.mp hv'
  have hc : a₂ * a₁⁻¹ = a₁⁻¹ * a₂ := by
    have h12 := hA a₁ ha₁ a₂ ha₂
    calc a₂ * a₁⁻¹ = a₁⁻¹ * (a₁ * a₂) * a₁⁻¹ := by group
      _ = a₁⁻¹ * (a₂ * a₁) * a₁⁻¹ := by rw [h12]
      _ = a₁⁻¹ * a₂ := by group
  have e : ⁅y₁ * a₁, y₂ * a₂⁆ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by
    calc ⁅y₁ * a₁, y₂ * a₂⁆ = y₁ * a₁ * y₂ * (a₂ * a₁⁻¹) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = y₁ * a₁ * y₂ * (a₁⁻¹ * a₂) * y₁⁻¹ * a₂⁻¹ * y₂⁻¹ := by rw [hc]
      _ = y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ := by group
  have hp : a₁ * y₂ * a₁⁻¹ ∈ Y := (mem_normalizer_iff.mp (hAY ha₁) y₂).mp hy₂
  have hq : a₂ * y₁⁻¹ * a₂⁻¹ ∈ Y := (mem_normalizer_iff.mp (hAY ha₂) y₁⁻¹).mp (Y.inv_mem hy₁)
  have hswap : (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) = (a₂ * y₁⁻¹ * a₂⁻¹) * (a₁ * y₂ * a₁⁻¹) :=
    hY _ hp _ hq
  have e2 : y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹ =
      (y₁ * (a₂ * y₁⁻¹ * a₂⁻¹)) * ((a₁ * y₂ * a₁⁻¹) * y₂⁻¹) := by
    calc y₁ * (a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹) * y₂⁻¹
        = y₁ * ((a₁ * y₂ * a₁⁻¹) * (a₂ * y₁⁻¹ * a₂⁻¹)) * y₂⁻¹ := by group
      _ = y₁ * ((a₂ * y₁⁻¹ * a₂⁻¹) * (a₁ * y₂ * a₁⁻¹)) * y₂⁻¹ := by rw [hswap]
      _ = (y₁ * (a₂ * y₁⁻¹ * a₂⁻¹)) * ((a₁ * y₂ * a₁⁻¹) * y₂⁻¹) := by group
  rw [e, e2]
  refine N.mul_mem ?_ ?_
  · have h1 := hAN a₂ ha₂ y₁ hy₁
    have e3 : y₁ * (a₂ * y₁⁻¹ * a₂⁻¹) = (a₂ * y₁ * a₂⁻¹ * y₁⁻¹)⁻¹ := by group
    rw [e3]
    exact N.inv_mem h1
  · exact hAN a₁ ha₁ y₂ hy₂

end Comm

section Normalizer

variable {G : Type*} [Group G] [Finite G]

theorem mem_normalizer_closure_of_conj_mem {t : G} {S : Set G}
    (hS : ∀ w ∈ S, t * w * t⁻¹ ∈ closure S) :
    t ∈ normalizer ((closure S : Subgroup G) : Set G) := by
  refine mem_normalizer_fintype fun w hw => ?_
  have hle : closure S ≤ (closure S).comap (MulAut.conj t).toMonoidHom := by
    rw [closure_le]
    intro y hy
    rw [SetLike.mem_coe, mem_comap]
    exact hS y hy
  exact hle hw

end Normalizer

section CenMod

variable {G : Type*} [Group G]

@[expose] def cenMod (P V0 D : Subgroup G) (hD : ∀ q ∈ P, ∀ z ∈ D, q * z = z * q) : Subgroup G where
  carrier := {y | y ∈ P ∧ ∀ w ∈ V0, y * w * y⁻¹ * w⁻¹ ∈ D}
  one_mem' := ⟨P.one_mem, fun w _ => by simpa using D.one_mem⟩
  mul_mem' := by
    rintro y z ⟨hyP, hy⟩ ⟨hzP, hz⟩
    refine ⟨P.mul_mem hyP hzP, fun w hw => ?_⟩
    have e : y * z * w * (y * z)⁻¹ * w⁻¹ =
        (y * (z * w * z⁻¹ * w⁻¹) * y⁻¹) * (y * w * y⁻¹ * w⁻¹) := by group
    have hc : y * (z * w * z⁻¹ * w⁻¹) = (z * w * z⁻¹ * w⁻¹) * y := hD y hyP _ (hz w hw)
    have e2 : y * (z * w * z⁻¹ * w⁻¹) * y⁻¹ = z * w * z⁻¹ * w⁻¹ := by
      rw [hc]; group
    rw [e, e2]
    exact D.mul_mem (hz w hw) (hy w hw)
  inv_mem' := by
    rintro y ⟨hyP, hy⟩
    refine ⟨P.inv_mem hyP, fun w hw => ?_⟩
    have hc : y * (y * w * y⁻¹ * w⁻¹) = (y * w * y⁻¹ * w⁻¹) * y := hD y hyP _ (hy w hw)
    have e : y⁻¹ * w * y⁻¹⁻¹ * w⁻¹ = (y⁻¹ * (y * w * y⁻¹ * w⁻¹) * y)⁻¹ := by group
    have e2 : y⁻¹ * (y * w * y⁻¹ * w⁻¹) * y = y * w * y⁻¹ * w⁻¹ := by
      calc y⁻¹ * (y * w * y⁻¹ * w⁻¹) * y = y⁻¹ * ((y * w * y⁻¹ * w⁻¹) * y) := by group
        _ = y⁻¹ * (y * (y * w * y⁻¹ * w⁻¹)) := by rw [← hc]
        _ = y * w * y⁻¹ * w⁻¹ := by group
    rw [e, e2]
    exact D.inv_mem (hy w hw)

theorem conj_mem_cenMod {P V0 D : Subgroup G} {hD : ∀ q ∈ P, ∀ z ∈ D, q * z = z * q}
    (hPV : P ≤ normalizer (V0 : Set G)) {p y : G} (hp : p ∈ P) (hy : y ∈ cenMod P V0 D hD) :
    p * y * p⁻¹ ∈ cenMod P V0 D hD := by
  obtain ⟨hyP, hy⟩ := hy
  refine ⟨P.mul_mem (P.mul_mem hp hyP) (P.inv_mem hp), fun w hw => ?_⟩
  have hw' : p⁻¹ * w * p ∈ V0 := by
    have := (mem_normalizer_iff.mp (hPV (P.inv_mem hp)) w).mp hw
    simpa using this
  have e : p * y * p⁻¹ * w * (p * y * p⁻¹)⁻¹ * w⁻¹ =
      p * (y * (p⁻¹ * w * p) * y⁻¹ * (p⁻¹ * w * p)⁻¹) * p⁻¹ := by group
  rw [e]
  have h1 := hy _ hw'
  have hc := hD p hp _ h1
  have e2 : p * (y * (p⁻¹ * w * p) * y⁻¹ * (p⁻¹ * w * p)⁻¹) * p⁻¹ =
      y * (p⁻¹ * w * p) * y⁻¹ * (p⁻¹ * w * p)⁻¹ := by
    rw [hc]; group
  rw [e2]
  exact h1

theorem mem_of_zpow_mem_of_pow_three {g : G} {N : Subgroup G} (hg3 : g ^ 3 = 1) {k : ℤ}
    (hk : ¬ (3 : ℤ) ∣ k) (h : g ^ k ∈ N) : g ∈ N := by
  have hz : ∀ q : ℤ, g ^ (3 * q) = 1 := by
    intro q
    rw [zpow_mul, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg3, one_zpow]
  obtain ⟨q, hq⟩ : ∃ q : ℤ, k = 3 * q + 1 ∨ k = 3 * q + 2 := ⟨k / 3, by omega⟩
  rcases hq with hq | hq
  · have : g ^ k = g := by rw [hq, zpow_add, hz, one_mul, zpow_one]
    rwa [this] at h
  · have e : g ^ k = g ^ (2 : ℤ) := by
      rw [hq, zpow_add, hz, one_mul]
    have e2 : g = (g ^ k) ^ (2 : ℤ) := by
      rw [e, ← zpow_mul, show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
        show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast, hg3, one_mul]
    rw [e2]
    exact N.zpow_mem h 2

end CenMod

end Item1120V1Proof

end CFSG.RankThree.PartTwo.Sec11
