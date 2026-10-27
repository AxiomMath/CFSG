module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

def conjOn (K : Subgroup G) (x : G) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) : Function.End K :=
  fun k => ⟨x * (k : G) * x⁻¹, hxK k k.2⟩

theorem conjOn_pow_coe (K : Subgroup G) (x : G) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) (n : ℕ)
    (k : K) : (((conjOn K x hxK) ^ n) k : G) = x ^ n * (k : G) * (x ^ n)⁻¹ := by
  induction n generalizing k with
  | zero =>
    show (k : G) = x ^ 0 * (k : G) * (x ^ 0)⁻¹
    group
  | succ n ih =>
    rw [pow_succ]
    show (((conjOn K x hxK ^ n) (conjOn K x hxK k) : K) : G) = _
    rw [ih]
    show x ^ n * (x * (k : G) * x⁻¹) * (x ^ n)⁻¹ = x ^ (n + 1) * (k : G) * (x ^ (n + 1))⁻¹
    group

theorem card_modEq_card_centralizer (K : Subgroup G) [Finite K] {x : G} (hx : orderOf x = 5)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    Nat.card K ≡ Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K) [MOD 5] := by
  let _ : DecidableEq K := Classical.decEq K
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite K
  have hf : (conjOn K x hxK) ^ 5 ^ 1 = 1 := by
    funext k
    apply Subtype.ext
    rw [pow_one, conjOn_pow_coe, ← hx, pow_orderOf_eq_one]
    simp
    rfl
  have h := Equiv.Perm.card_fixedPoints_modEq (α := K) hf
  simp only [Fintype.card_eq_nat_card] at h
  refine h.trans ?_
  have e : (Function.fixedPoints (conjOn K x hxK)) ≃
      ((Subgroup.centralizer ({x} : Set G)).subgroupOf K) :=
    { toFun := fun k => ⟨k.1, by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have := congrArg Subtype.val k.2
        exact mul_inv_eq_iff_eq_mul.1 this⟩
      invFun := fun k => ⟨k.1, by
        have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_subgroupOf.1 k.2) x rfl
        apply Subtype.ext
        show x * (k.1 : G) * x⁻¹ = k.1
        rw [mul_inv_eq_iff_eq_mul]
        exact this⟩
      left_inv := fun k => rfl
      right_inv := fun k => rfl }
  rw [Nat.card_congr e]

theorem relIndex_centralizer_modEq (K : Subgroup G) [Finite K] (hK : IsPGroup 2 K) {x : G}
    (hx : orderOf x = 5) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    (Subgroup.centralizer ({x} : Set G)).relIndex K ≡ 1 [MOD 5] := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have h1 := Subgroup.index_mul_card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K)
  have h2 := card_modEq_card_centralizer K hx hxK
  have hcop : Nat.gcd 5 (Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K)) = 1 := by
    have hdvd : Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K) ∣ 2 ^ n :=
      hn ▸ Subgroup.card_subgroup_dvd_card _
    have h5 : Nat.Coprime 5 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
    exact Nat.Coprime.coprime_dvd_right hdvd h5
  have h3 : ((Subgroup.centralizer ({x} : Set G)).subgroupOf K).index *
      Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K) ≡
      1 * Nat.card ((Subgroup.centralizer ({x} : Set G)).subgroupOf K) [MOD 5] := by
    rw [h1, one_mul]
    exact h2
  exact Nat.ModEq.cancel_right_of_coprime hcop h3

theorem relIndex_centralizer_eq_one_or (K : Subgroup G) [Finite K] (hK : IsPGroup 2 K) {x : G}
    (hx : orderOf x = 5) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    (Subgroup.centralizer ({x} : Set G)).relIndex K = 1 ∨
      16 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex K := by
  obtain ⟨k, hk⟩ := hK.index ((Subgroup.centralizer ({x} : Set G)).subgroupOf K)
  have hmod := relIndex_centralizer_modEq K hK hx hxK
  have hk' : (Subgroup.centralizer ({x} : Set G)).relIndex K = 2 ^ k := hk
  rw [hk'] at hmod ⊢
  by_cases h4 : k < 4
  · interval_cases k
    · left
      norm_num
    all_goals exact absurd hmod (by norm_num [Nat.ModEq])
  · right
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

end CFSG.Quasithin.Fan86
