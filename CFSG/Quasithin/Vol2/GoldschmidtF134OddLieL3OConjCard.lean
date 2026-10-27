module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OConjSylow
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieL3OLift

public section

namespace CFSG.Quasithin.H13.NQCore.L3Odd

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

section Torus

variable {K : Type} [Field K]

theorem mem_torusSL_iff_exists {p : ℕ} {z : SL(3, K)} :
    z ∈ torusSL K p ↔ ∃ y : Kˣ × Kˣ, y.1 ^ p = 1 ∧ y.2 ^ p = 1 ∧ diagHom y = z := by
  rw [torusSL, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_prod, mem_rootsOfUnity, mem_rootsOfUnity] at hy
    exact ⟨y, hy.1, hy.2, rfl⟩
  · rintro ⟨y, h1, h2, rfl⟩
    refine ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_prod, mem_rootsOfUnity, mem_rootsOfUnity]
    exact ⟨h1, h2⟩

theorem pow_eq_one_of_mem_torusSL {p : ℕ} {z : SL(3, K)} (hz : z ∈ torusSL K p) : z ^ p = 1 := by
  obtain ⟨y, h1, h2, rfl⟩ := mem_torusSL_iff_exists.1 hz
  rw [← map_pow]
  have : y ^ p = 1 := Prod.ext h1 h2
  rw [this, map_one]

theorem mem_torusSL_of_pow_eq_one {p : ℕ} {y : Kˣ × Kˣ} (h : diagHom y ^ p = 1) :
    diagHom y ∈ torusSL K p := by
  rw [← map_pow, ← map_one diagHom] at h
  have := injective_diagHom h
  exact mem_torusSL_iff_exists.2 ⟨y, congrArg Prod.fst this, congrArg Prod.snd this, rfl⟩

theorem eq_one_of_mem_scalars_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {x : SL(3, K)} (hx : x ∈ scalars 3 K) (hxp : x ^ p = 1) : x = 1 := by
  have h3 := pow_three_eq_one_of_mem_scalars hx
  have := pow_gcd_eq_one.2 ⟨hxp, h3⟩
  have hg : Nat.gcd p 3 = 1 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  rwa [hg, pow_one] at this

theorem proj_injOn_torusSL {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {x y : SL(3, K)}
    (hx : x ∈ torusSL K p) (hy : y ∈ torusSL K p) (h : proj 3 K x = proj 3 K y) : x = y := by
  have hm : x⁻¹ * y ∈ scalars 3 K := proj_eq_proj_iff.mp h
  have hm' : x⁻¹ * y ∈ torusSL K p := (torusSL K p).mul_mem ((torusSL K p).inv_mem hx) hy
  have := eq_one_of_mem_scalars_of_pow_eq_one hp hp3 hm (pow_eq_one_of_mem_torusSL hm')
  rwa [inv_mul_eq_one] at this

variable [Finite K]

theorem card_rootsOfUnity_of_dvd {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ Nat.card K - 1) :
    Nat.card (rootsOfUnity p K) = p := by
  have h : p ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p h
  have : NeZero p := ⟨hp.out.ne_zero⟩
  exact (IsPrimitiveRoot.iff_orderOf.2 hζ).card_rootsOfUnity'

theorem card_torusSL {p : ℕ} [hp : Fact p.Prime] (hpq : p ∣ Nat.card K - 1) :
    Nat.card (torusSL K p) = p ^ 2 := by
  rw [torusSL, Subgroup.card_map_of_injective injective_diagHom,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    card_rootsOfUnity_of_dvd hpq, sq]

theorem card_torusP {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1) :
    Nat.card (torusP K p) = p ^ 2 := by
  have hbij : Function.Bijective ((proj 3 K).subgroupMap (torusSL K p)) := by
    refine ⟨fun a b hab => ?_, (proj 3 K).subgroupMap_surjective _⟩
    exact Subtype.ext (proj_injOn_torusSL hp.out (by omega) a.2 b.2 (congrArg Subtype.val hab))
  rw [torusP, ← Nat.card_congr (MulEquiv.ofBijective _ hbij).toEquiv, card_torusSL hpq]

end Torus

end CFSG.Quasithin.H13.NQCore.L3Odd
