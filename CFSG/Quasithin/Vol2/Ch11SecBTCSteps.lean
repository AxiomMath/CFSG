module

public import CFSG.Quasithin.Background.E2Two

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

theorem eq_one_of_mem_of_commutator_eq_bot {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hZ : Subgroup.center ↥A = ⊥) (hBA : ⁅B, A⁆ = ⊥) {w : Γ} (hwA : w ∈ A) (hwB : w ∈ B) :
    w = 1 := by
  have hc : (⟨w, hwA⟩ : ↥A) ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro a
    have := Subgroup.commutator_mem_commutator hwB a.2
    rw [hBA, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact Subtype.ext this.symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact congrArg Subtype.val hc

theorem eq_one_of_pow_two_pow_of_pow_prime {Γ : Type*} [Group Γ] {x : Γ} {a p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h1 : x ^ 2 ^ a = 1) (h2 : x ^ p = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ a) p :=
    Nat.Coprime.pow_left a ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rwa [hcop, pow_one] at this

theorem mem_of_pow_two_pow_mem {Γ : Type*} [Group Γ] {E : Subgroup Γ} {x : Γ} {a : ℕ}
    (hodd : Odd (orderOf x)) (h : x ^ 2 ^ a ∈ E) : x ∈ E := by
  have hcop : Nat.Coprime (2 ^ a) (orderOf x) :=
    Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact E.pow_mem h m

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_star_of_mem_sup {H X K : Subgroup G} (hXH : X ≤ H) (hKH : K ≤ H) {x : G}
    (hx : x ∈ K ⊔ kerIn X H) (hxH : x ∈ H) :
    QuotientGroup.mk' ((kerIn X H).subgroupOf H) ⟨x, hxH⟩ ∈ E2.star X H K := by
  have hKJ : K ≤ Subgroup.normalizer (kerIn X H : Set G) := hKH.trans (le_normalizer_kerIn X H)
  have hx' : x ∈ ((kerIn X H : Set G) * (K : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left (kerIn X H) K hKJ, sup_comm]
    exact hx
  obtain ⟨j, hj, k, hk, rfl⟩ := hx'
  have hjH : j ∈ H := kerIn_le.trans hXH hj
  refine ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : ((⟨k, hKH hk⟩ : ↥H)⁻¹ * ⟨j * k, hxH⟩ : ↥H) = (k⁻¹ * j * k : G) := by
    simp [mul_assoc]
  rw [this]
  have := (Subgroup.mem_normalizer_iff.mp (hKJ (K.inv_mem hk)) j).mp hj
  simpa [mul_assoc] using this

end CFSG.Quasithin.Vol2.Ch11.SecB
