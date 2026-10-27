module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Group.Commute.Basic
public import Mathlib.Data.Nat.Prime.Int
public import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Conj
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Zify

public section

namespace CFSG.RankThree.PartOne.SP4GA

variable {G : Type*} [Group G]

@[expose] def kap (c u : G) : G := u * c * u⁻¹ * c⁻¹

section Comb

variable {g h : G}

theorem comb_mul (hgh : g * h = h * g) (i j i' j' : ℤ) :
    (g ^ i * h ^ j) * (g ^ i' * h ^ j') = g ^ (i + i') * h ^ (j + j') := by
  have hc : Commute (h ^ j) (g ^ i') := Commute.zpow_zpow (show Commute h g from hgh.symm) j i'
  calc (g ^ i * h ^ j) * (g ^ i' * h ^ j') = g ^ i * ((h ^ j * g ^ i') * h ^ j') := by
        simp only [mul_assoc]
    _ = g ^ i * ((g ^ i' * h ^ j) * h ^ j') := by rw [hc.eq]
    _ = g ^ (i + i') * h ^ (j + j') := by rw [zpow_add, zpow_add]; simp only [mul_assoc]

theorem comb_zpow (hgh : g * h = h * g) (i j k : ℤ) :
    (g ^ i * h ^ j) ^ k = g ^ (i * k) * h ^ (j * k) := by
  have hc : Commute (g ^ i) (h ^ j) := Commute.zpow_zpow (show Commute g h from hgh) i j
  rw [hc.mul_zpow, ← zpow_mul, ← zpow_mul]

theorem comb_inv (hgh : g * h = h * g) (i j : ℤ) : (g ^ i * h ^ j)⁻¹ = g ^ (-i) * h ^ (-j) := by
  have := comb_zpow hgh i j (-1)
  rw [zpow_neg_one] at this
  rw [this]
  congr 1 <;> simp

end Comb

section Kap

variable {P B : Subgroup G} {c : G}

theorem conj_c (c u : G) : u * c * u⁻¹ = kap c u * c := by unfold kap; group

theorem kap_one : kap c (1 : G) = 1 := by unfold kap; group

theorem kap_mul (hBP : ∀ β ∈ B, ∀ u ∈ P, u * β * u⁻¹ = β) (hkap : ∀ u ∈ P, kap c u ∈ B)
    (hBc : ∀ β ∈ B, ∀ β' ∈ B, β * β' = β' * β) {u v : G} (hu : u ∈ P) (hv : v ∈ P) :
    kap c (u * v) = kap c u * kap c v := by
  have h1 : u * kap c v * u⁻¹ = kap c v := hBP _ (hkap v hv) u hu
  have h2 : kap c v * kap c u = kap c u * kap c v := hBc _ (hkap v hv) _ (hkap u hu)
  have h3 : kap c (u * v) = kap c v * kap c u := by
    calc kap c (u * v) = (u * kap c v * u⁻¹) * (u * c * u⁻¹ * c⁻¹) := by unfold kap; group
      _ = kap c v * kap c u := by rw [h1]; rfl
  rw [h3, h2]

theorem kap_inv (hBP : ∀ β ∈ B, ∀ u ∈ P, u * β * u⁻¹ = β) (hkap : ∀ u ∈ P, kap c u ∈ B)
    (hBc : ∀ β ∈ B, ∀ β' ∈ B, β * β' = β' * β) {u : G} (hu : u ∈ P) :
    kap c u⁻¹ = (kap c u)⁻¹ := by
  have h := kap_mul hBP hkap hBc (P.inv_mem hu) hu
  rw [inv_mul_cancel, kap_one] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem kap_zpow (hBP : ∀ β ∈ B, ∀ u ∈ P, u * β * u⁻¹ = β) (hkap : ∀ u ∈ P, kap c u ∈ B)
    (hBc : ∀ β ∈ B, ∀ β' ∈ B, β * β' = β' * β) {u : G} (hu : u ∈ P) (k : ℤ) :
    kap c (u ^ k) = (kap c u) ^ k := by
  induction k using Int.induction_on with
  | zero => simp [kap_one]
  | succ k ih =>
    rw [zpow_add_one, kap_mul hBP hkap hBc (P.zpow_mem hu k) hu, ih, zpow_add_one]
  | pred k ih =>
    rw [zpow_sub_one, kap_mul hBP hkap hBc (P.zpow_mem hu _) (P.inv_mem hu), ih,
      kap_inv hBP hkap hBc hu, zpow_sub_one]

theorem conj_c_zpow {u : G} (hcomm : kap c u * c = c * kap c u) (k : ℤ) :
    u * c ^ k * u⁻¹ = (kap c u) ^ k * c ^ k := by
  rw [← conj_zpow, conj_c, Commute.mul_zpow (show Commute (kap c u) c from hcomm)]

theorem kap_c_pow_mul {u β₀ : G} (hcomm : kap c u * c = c * kap c u)
    (hβ : u * β₀ * u⁻¹ = β₀) (k : ℤ) :
    u * (c ^ k * β₀) * u⁻¹ * (c ^ k * β₀)⁻¹ = (kap c u) ^ k := by
  calc u * (c ^ k * β₀) * u⁻¹ * (c ^ k * β₀)⁻¹
      = (u * c ^ k * u⁻¹) * (u * β₀ * u⁻¹) * β₀⁻¹ * (c ^ k)⁻¹ := by group
    _ = ((kap c u) ^ k * c ^ k) * β₀ * β₀⁻¹ * (c ^ k)⁻¹ := by
        rw [conj_c_zpow hcomm k, hβ]
    _ = (kap c u) ^ k := by group

end Kap

structure Setup (p e : ℕ) (P B : Subgroup G) (c x y βK βb : G) : Prop where
  hp : p.Prime
  hp2 : p ≠ 2
  he : 1 ≤ e
  c_mem : c ∈ P
  x_mem : x ∈ P
  y_mem : y ∈ P
  B_central : ∀ β ∈ B, ∀ u ∈ P, u * β * u⁻¹ = β
  B_comm : ∀ β ∈ B, ∀ β' ∈ B, β * β' = β' * β
  kap_mem : ∀ u ∈ P, kap c u ∈ B
  xy : x * y = y * x
  βK_def : βK = x ^ (p ^ (e - 1))
  βb_def : βb = y ^ (p ^ (e - 1))
  βK_mem : βK ∈ B
  βb_mem : βb ∈ B
  βK_p : βK ^ p = 1
  βb_p : βb ^ p = 1
  indep : ∀ i j : ℤ, βK ^ i * βb ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j

theorem zpow_eq_one_of_dvd {p : ℕ} {g : G} (hg : g ^ p = 1) {i : ℤ} (hi : (p : ℤ) ∣ i) :
    g ^ i = 1 := by
  obtain ⟨k, rfl⟩ := hi
  rw [zpow_mul, zpow_natCast, hg, one_zpow]

namespace Setup

variable {p e : ℕ} {P B : Subgroup G} {c x y βK βb : G} (S : Setup p e P B c x y βK βb)

include S

theorem βKβb : βK * βb = βb * βK := S.B_comm _ S.βK_mem _ S.βb_mem

theorem comb_eq_of_eq {i₁ j₁ i₂ j₂ : ℤ} (h : βK ^ i₁ * βb ^ j₁ = βK ^ i₂ * βb ^ j₂) :
    (p : ℤ) ∣ i₁ - i₂ ∧ (p : ℤ) ∣ j₁ - j₂ := by
  apply S.indep
  have h1 : (βK ^ i₁ * βb ^ j₁) * (βK ^ i₂ * βb ^ j₂)⁻¹ = 1 := by rw [h]; group
  rw [comb_inv S.βKβb, comb_mul S.βKβb] at h1
  simpa [sub_eq_add_neg] using h1

theorem not_dvd_one : ¬ (p : ℤ) ∣ 1 := by
  intro h1
  have hp1 := S.hp.one_lt
  have : p ∣ 1 := by exact_mod_cast h1
  exact absurd (Nat.le_of_dvd one_pos this) (by omega)

theorem βK_ne_one : βK ≠ 1 := by
  intro h
  exact S.not_dvd_one (S.indep 1 0 (by simp [h])).1

theorem βb_ne_one : βb ≠ 1 := by
  intro h
  exact S.not_dvd_one (S.indep 0 1 (by simp [h])).2

theorem βK_not_mem_zpowers : βK ∉ Subgroup.zpowers βb := by
  intro h
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
  exact S.not_dvd_one (S.indep 1 (-j) (by rw [zpow_one, zpow_neg, hj]; exact mul_inv_cancel βK)).1

theorem conj_βK {n : G} {a a' : ℤ} (hx : n * x * n⁻¹ = x ^ a * y ^ a') :
    n * βK * n⁻¹ = βK ^ a * βb ^ a' := by
  have h1 : n * βK * n⁻¹ = (n * x * n⁻¹) ^ (p ^ (e - 1)) := by
    rw [S.βK_def, conj_pow]
  rw [h1, hx, ← zpow_natCast, comb_zpow S.xy, mul_comm a, mul_comm a', zpow_mul, zpow_mul,
    zpow_natCast, ← S.βK_def, zpow_natCast, ← S.βb_def]

theorem conj_βb {n : G} {a a' : ℤ} (hy : n * y * n⁻¹ = x ^ a * y ^ a') :
    n * βb * n⁻¹ = βK ^ a * βb ^ a' := by
  have h1 : n * βb * n⁻¹ = (n * y * n⁻¹) ^ (p ^ (e - 1)) := by
    rw [S.βb_def, conj_pow]
  rw [h1, hy, ← zpow_natCast, comb_zpow S.xy, mul_comm a, mul_comm a', zpow_mul, zpow_mul,
    zpow_natCast, ← S.βK_def, zpow_natCast, ← S.βb_def]

theorem hcomm_c : ∀ u ∈ P, kap c u * c = c * kap c u := by
  intro u hu
  have := S.B_central _ (S.kap_mem u hu) c S.c_mem
  calc kap c u * c = (c * kap c u * c⁻¹) * c := by rw [this]
    _ = c * kap c u := by group

theorem relations {n β₀ : G} {μ r r' : ℤ} (hβ₀ : β₀ ∈ B) (hnc : n * c * n⁻¹ = c ^ μ * β₀)
    (hnP : ∀ u ∈ P, n * u * n⁻¹ ∈ P) (hr : kap c x = βK ^ r) (hr' : kap c y = βb ^ r')
    {a a' b₁ b₂ : ℤ} (hx : n * x * n⁻¹ = x ^ a * y ^ a')
    (hy : n * y * n⁻¹ = x ^ b₁ * y ^ b₂) :
    (p : ℤ) ∣ r * a * (1 - μ) ∧ (p : ℤ) ∣ a' * (r - r' * μ) ∧
      (p : ℤ) ∣ b₁ * (r' - r * μ) ∧ (p : ℤ) ∣ r' * b₂ * (1 - μ) := by
  have hkey : ∀ u ∈ P, n * kap c u * n⁻¹ = (kap c (n * u * n⁻¹)) ^ μ := by
    intro u hu
    have hu' := hnP u hu
    calc n * kap c u * n⁻¹
        = (n * u * n⁻¹) * (n * c * n⁻¹) * (n * u * n⁻¹)⁻¹ * (n * c * n⁻¹)⁻¹ := by
          unfold kap; group
      _ = (n * u * n⁻¹) * (c ^ μ * β₀) * (n * u * n⁻¹)⁻¹ * (c ^ μ * β₀)⁻¹ := by rw [hnc]
      _ = (kap c (n * u * n⁻¹)) ^ μ :=
          kap_c_pow_mul (S.hcomm_c _ hu') (S.B_central β₀ hβ₀ _ hu') μ
  have hxP : ∀ k : ℤ, x ^ k ∈ P := fun k => P.zpow_mem S.x_mem k
  have hyP : ∀ k : ℤ, y ^ k ∈ P := fun k => P.zpow_mem S.y_mem k
  have hkx : ∀ s t : ℤ, kap c (x ^ s * y ^ t) = (βK ^ r) ^ s * (βb ^ r') ^ t := by
    intro s t
    rw [kap_mul S.B_central S.kap_mem S.B_comm (hxP s) (hyP t),
      kap_zpow S.B_central S.kap_mem S.B_comm S.x_mem,
      kap_zpow S.B_central S.kap_mem S.B_comm S.y_mem, hr, hr']
  have hcomb : ∀ s t : ℤ, ((βK ^ r) ^ s * (βb ^ r') ^ t) ^ μ =
      βK ^ (r * s * μ) * βb ^ (r' * t * μ) := by
    intro s t
    rw [← zpow_mul, ← zpow_mul, comb_zpow S.βKβb]
  have hx1 : n * kap c x * n⁻¹ = βK ^ (a * r) * βb ^ (a' * r) := by
    rw [hr, ← conj_zpow, S.conj_βK hx, comb_zpow S.βKβb]
  have hx2 := hkey x S.x_mem
  rw [hx, hkx, hcomb, hx1] at hx2
  have hy1 : n * kap c y * n⁻¹ = βK ^ (b₁ * r') * βb ^ (b₂ * r') := by
    rw [hr', ← conj_zpow, S.conj_βb hy, comb_zpow S.βKβb]
  have hy2 := hkey y S.y_mem
  rw [hy, hkx, hcomb, hy1] at hy2
  obtain ⟨h1, h2⟩ := S.comb_eq_of_eq hx2
  obtain ⟨h3, h4⟩ := S.comb_eq_of_eq hy2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e1 : r * a * (1 - μ) = a * r - r * a * μ := by ring
    rw [e1]; exact h1
  · have e1 : a' * (r - r' * μ) = a' * r - r' * a' * μ := by ring
    rw [e1]; exact h2
  · have e1 : b₁ * (r' - r * μ) = b₁ * r' - r * b₁ * μ := by ring
    rw [e1]; exact h3
  · have e1 : r' * b₂ * (1 - μ) = b₂ * r' - r' * b₂ * μ := by ring
    rw [e1]; exact h4

theorem contradiction_of_lifts {r r' : ℤ} (hrp : ¬ (p : ℤ) ∣ r)
    (hr : kap c x = βK ^ r) (hr' : kap c y = βb ^ r')
    {n₁ β₁ : G} (hβ₁ : β₁ ∈ B) (hn₁c : n₁ * c * n₁⁻¹ = c * β₁)
    (hn₁P : ∀ u ∈ P, n₁ * u * n₁⁻¹ ∈ P)
    {a₁ a₁' b₁ b₁' : ℤ} (hx₁ : n₁ * x * n₁⁻¹ = x ^ a₁ * y ^ a₁')
    (hy₁ : n₁ * y * n₁⁻¹ = x ^ b₁ * y ^ b₁')
    (hnot : n₁ * βb * n₁⁻¹ ∉ Subgroup.zpowers βb)
    {n₂ β₂ : G} (hβ₂ : β₂ ∈ B) (hn₂c : n₂ * c * n₂⁻¹ = c⁻¹ * β₂)
    (hn₂P : ∀ u ∈ P, n₂ * u * n₂⁻¹ ∈ P)
    {a₂ a₂' b₂ b₂' : ℤ} (hx₂ : n₂ * x * n₂⁻¹ = x ^ a₂ * y ^ a₂')
    (hy₂ : n₂ * y * n₂⁻¹ = x ^ b₂ * y ^ b₂') : False := by
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp S.hp
  have hp2' : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact S.hp2 ((Nat.prime_dvd_prime_iff_eq S.hp Nat.prime_two).1 h')
  have hc1 : n₁ * c * n₁⁻¹ = c ^ (1 : ℤ) * β₁ := by rw [zpow_one]; exact hn₁c
  obtain ⟨-, -, h3, -⟩ := S.relations hβ₁ hc1 hn₁P hr hr' hx₁ hy₁
  have hb1 : ¬ (p : ℤ) ∣ b₁ := by
    intro h
    apply hnot
    rw [S.conj_βb hy₁, zpow_eq_one_of_dvd S.βK_p h, one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers βb) _
  have hrr : (p : ℤ) ∣ r' - r := by
    have h3' : (p : ℤ) ∣ b₁ * (r' - r) := by simpa using h3
    rcases hpz.dvd_or_dvd h3' with h | h
    · exact absurd h hb1
    · exact h
  have hc2 : n₂ * c * n₂⁻¹ = c ^ (-1 : ℤ) * β₂ := by rw [zpow_neg_one]; exact hn₂c
  obtain ⟨h7, h8, -, -⟩ := S.relations hβ₂ hc2 hn₂P hr hr' hx₂ hy₂
  have h7' : (p : ℤ) ∣ 2 * (r * a₂) := by
    have e : r * a₂ * (1 - (-1)) = 2 * (r * a₂) := by ring
    rwa [e] at h7
  have ha₂ : (p : ℤ) ∣ a₂ := by
    rcases hpz.dvd_or_dvd h7' with h | h
    · exact absurd h hp2'
    · rcases hpz.dvd_or_dvd h with h | h
      · exact absurd h hrp
      · exact h
  have hν₂ : n₂ * βK * n₂⁻¹ = βK ^ a₂ * βb ^ a₂' := S.conj_βK hx₂
  rw [zpow_eq_one_of_dvd S.βK_p ha₂, one_mul] at hν₂
  have ha₂' : ¬ (p : ℤ) ∣ a₂' := by
    intro h
    rw [zpow_eq_one_of_dvd S.βb_p h] at hν₂
    have h1 : βK = 1 := by
      calc βK = n₂⁻¹ * (n₂ * βK * n₂⁻¹) * n₂ := by group
        _ = 1 := by rw [hν₂]; group
    exact S.βK_ne_one h1
  have h8' : (p : ℤ) ∣ r + r' := by
    have h8'' : (p : ℤ) ∣ a₂' * (r + r') := by
      have e : a₂' * (r - r' * (-1)) = a₂' * (r + r') := by ring
      rwa [e] at h8
    rcases hpz.dvd_or_dvd h8'' with h | h
    · exact absurd h ha₂'
    · exact h
  have h2r : (p : ℤ) ∣ 2 * r := by
    have h9 := dvd_sub h8' hrr
    have e : r + r' - (r' - r) = 2 * r := by ring
    rwa [e] at h9
  rcases hpz.dvd_or_dvd h2r with h | h
  · exact hp2' h
  · exact hrp h

end Setup

end CFSG.RankThree.PartOne.SP4GA
