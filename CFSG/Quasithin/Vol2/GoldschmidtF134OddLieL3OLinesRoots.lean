module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLift
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OTorusDef
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Roots

variable {K : Type} [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime]

theorem exists_orderOf_eq (hpq : p ∣ Nat.card K - 1) : ∃ ζ : Kˣ, orderOf ζ = p := by
  apply exists_prime_orderOf_dvd_card' p
  rwa [Nat.card_units]

theorem card_rootsOfUnity_eq (hpq : p ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity p K) = p := by
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq hpq
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : IsPrimitiveRoot ζ p := hζ ▸ IsPrimitiveRoot.orderOf ζ
  exact this.card_rootsOfUnity'

theorem exists_ne_one (hpq : p ∣ Nat.card K - 1) : ∃ ζ : Kˣ, ζ ^ p = 1 ∧ ζ ≠ 1 := by
  obtain ⟨ζ, hζ⟩ := exists_orderOf_eq hpq
  refine ⟨ζ, hζ ▸ pow_orderOf_eq_one ζ, ?_⟩
  rintro rfl
  rw [orderOf_one] at hζ
  exact hp.out.one_lt.ne hζ

end Roots

theorem eq_one_of_pow_eq_one_of_prime {G : Type*} [Group G] {a : G} {p q : ℕ} [hp : Fact p.Prime]
    (hq : q.Prime) (hpq : p ≠ q) (hp1 : a ^ p = 1) (hq1 : a ^ q = 1) : a = 1 := by
  have := pow_gcd_eq_one.2 ⟨hp1, hq1⟩
  rwa [((Nat.coprime_primes hp.out hq).2 hpq).gcd_eq_one, pow_one] at this

section Torus

variable {K : Type} [Field K] {p : ℕ}

theorem mem_torusSL {x : SL(3, K)} :
    x ∈ torusSL K p ↔ ∃ a b : Kˣ, a ^ p = 1 ∧ b ^ p = 1 ∧ diagHom (a, b) = x := by
  simp only [torusSL, Subgroup.mem_map, Subgroup.mem_prod, mem_rootsOfUnity, Prod.exists]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, h⟩
    exact ⟨a, b, ha, hb, h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨a, b, ⟨ha, hb⟩, h⟩

theorem mem_torusP {y : projectiveSL 3 K} :
    y ∈ torusP K p ↔ ∃ a b : Kˣ, a ^ p = 1 ∧ b ^ p = 1 ∧ proj 3 K (diagHom (a, b)) = y := by
  simp only [torusP, Subgroup.mem_map, mem_torusSL]
  constructor
  · rintro ⟨x, ⟨a, b, ha, hb, rfl⟩, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨_, ⟨a, b, ha, hb, rfl⟩, rfl⟩

theorem diagHom_injective : Function.Injective (diagHom : Kˣ × Kˣ →* SL(3, K)) := by
  intro x y h
  have h1 := congrArg (fun g : SL(3, K) => ((g : Matrix (Fin 3) (Fin 3) K) 0 0)) h
  have h2 := congrArg (fun g : SL(3, K) => ((g : Matrix (Fin 3) (Fin 3) K) 1 1)) h
  simp [diagMat] at h1 h2
  exact Prod.ext (Units.ext h1) (Units.ext h2)

end Torus

section Lift

variable {K : Type} [Field K] {p : ℕ} [hp : Fact p.Prime]

theorem commute_of_proj_commute (hp3 : p ≠ 3) {g d : SL(3, K)} (hd : d ^ p = 1)
    (h : proj 3 K g * proj 3 K d = proj 3 K d * proj 3 K g) : g * d = d * g := by
  set z : SL(3, K) := g * d * g⁻¹ * d⁻¹ with hz
  have hz1 : proj 3 K z = 1 := by
    simp only [hz, map_mul, map_inv]
    rw [h]
    group
  have hzs : z ∈ scalars 3 K := proj_eq_one_iff.1 hz1
  have hz3 : z ^ 3 = 1 := pow_three_eq_one_of_mem_scalars hzs
  have hzc : Commute z d :=
    (Subgroup.mem_center_iff.1 (scalars_le_center 3 K hzs) d).symm
  have hzd : z * d = g * d * g⁻¹ := by
    rw [hz]
    group
  have hzp : (z * d) ^ p = 1 := by
    rw [hzd, conj_pow, hd]
    group
  rw [hzc.mul_pow, hd, mul_one] at hzp
  have hz0 : z = 1 := eq_one_of_pow_eq_one_of_prime Nat.prime_three hp3 hzp hz3
  rw [hz, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hz0
  exact hz0

theorem proj_commute_iff (hp3 : p ≠ 3) {g d : SL(3, K)} (hd : d ^ p = 1) :
    proj 3 K g * proj 3 K d = proj 3 K d * proj 3 K g ↔ g * d = d * g :=
  ⟨commute_of_proj_commute hp3 hd, fun h => by rw [← map_mul, ← map_mul, h]⟩

theorem eq_one_of_proj_diagHom_eq_one (hp3 : p ≠ 3) {a b : Kˣ} (ha : a ^ p = 1) (hb : b ^ p = 1)
    (h : proj 3 K (diagHom (a, b)) = 1) : a = 1 ∧ b = 1 := by
  have h3 : (diagHom (a, b) : SL(3, K)) ^ 3 = 1 :=
    pow_three_eq_one_of_mem_scalars (proj_eq_one_iff.1 h)
  rw [← map_pow, ← map_one diagHom] at h3
  have h4 := diagHom_injective h3
  simp only [Prod.pow_def, Prod.mk_eq_one] at h4
  exact ⟨eq_one_of_pow_eq_one_of_prime Nat.prime_three hp3 ha h4.1,
    eq_one_of_pow_eq_one_of_prime Nat.prime_three hp3 hb h4.2⟩

end Lift

end CFSG.Quasithin.H13.NQCore.L3Odd
