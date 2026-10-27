module

public import CFSG.RankThree.PartTwo.Sec21.Hering214Lin2

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.Open (IsElemAbelian)

variable {K : Type} [Field K] [Finite K]

section Closure

variable {G : Type} [Group G]

private theorem pow_eq_pow_mod_three {a : G} (ha3 : a ^ 3 = 1) (i : ℕ) :
    a ^ i = a ^ (i % 3) := by
  conv_lhs => rw [← Nat.div_add_mod i 3]
  rw [pow_add, pow_mul, ha3, one_pow, one_mul]

private theorem pow_three_eq_one_of_mem_closure_pair {a b : G} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hab : a * b = b * a) {x : G}
    (hx : x ∈ Subgroup.closure ({a, b} : Set G)) : x ^ 3 = 1 := by
  have hc : Commute a b := hab
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure ha3 hb3 hab hx
  rw [Commute.mul_pow (hc.pow_pow i j), ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
    pow_mul, pow_mul, ha3, hb3, one_pow, one_pow, one_mul]

private theorem mul_comm_of_mem_closure_pair {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) {x y : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G))
    (hy : y ∈ Subgroup.closure ({a, b} : Set G)) : x * y = y * x := by
  have hc : Commute a b := hab
  obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure ha3 hb3 hab hx
  obtain ⟨k, l, rfl⟩ := exists_pow_mul_pow_of_mem_closure ha3 hb3 hab hy
  have h1 : Commute (a ^ i) (a ^ k) := (Commute.refl a).pow_pow i k
  have h2 : Commute (a ^ i) (b ^ l) := hc.pow_pow i l
  have h3 : Commute (b ^ j) (a ^ k) := hc.symm.pow_pow j k
  have h4 : Commute (b ^ j) (b ^ l) := (Commute.refl b).pow_pow j l
  exact (Commute.mul_left (Commute.mul_right h1 h2) (Commute.mul_right h3 h4)).eq

private theorem closure_pair_eq_range {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a) :
    ((Subgroup.closure ({a, b} : Set G) : Subgroup G) : Set G) =
      Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := exists_pow_mul_pow_of_mem_closure ha3 hb3 hab hx
    refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
    show a ^ (i % 3) * b ^ (j % 3) = a ^ i * b ^ j
    rw [pow_eq_pow_mod_three ha3 i, pow_eq_pow_mod_three hb3 j]
  · rintro ⟨p, rfl⟩
    show a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ) ∈ Subgroup.closure ({a, b} : Set G)
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _
        (Set.mem_singleton _))) _)

theorem card_closure_pair_three {a b : G} (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l) :
    Nat.card (Subgroup.closure ({a, b} : Set G)) = 9 := by
  have hf : Function.Injective (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ)) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    obtain ⟨rfl, rfl⟩ := hdist i j k l h
    rfl
  have h9 : Nat.card (Set.range (fun p : Fin 3 × Fin 3 => a ^ (p.1 : ℕ) * b ^ (p.2 : ℕ))) = 9 := by
    rw [Nat.card_range_of_injective hf]
    simp [Nat.card_prod]
  have hcard := congrArg (fun T : Set G => Nat.card T)
    (closure_pair_eq_range ha3 hb3 hab)
  exact hcard.trans h9

private theorem mem_closure_pair_of_four4 {u₁ u₂ t : G} (ht : Four4 u₁ u₂ t) :
    t ∈ Subgroup.closure ({u₁, u₂} : Set G) := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem conj_mem_closure_pair {u₁ u₂ g : G} (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1)
    (hu : u₁ * u₂ = u₂ * u₁) (h₁ : g * u₁ * g⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G))
    (h₂ : g * u₂ * g⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G)) {w : G}
    (hw : w ∈ Subgroup.closure ({u₁, u₂} : Set G)) :
    g * w * g⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) := by
  rcases klein_closure hu₁ hu₂ hu w hw with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · exact h₁
  · exact h₂
  · have e : g * (u₁ * u₂) * g⁻¹ = (g * u₁ * g⁻¹) * (g * u₂ * g⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ h₁ h₂

private theorem mem_normalizer_closure_pair {u₁ u₂ g : G} (hu₁ : u₁ * u₁ = 1)
    (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hg : g ^ 3 = 1)
    (h₁ : g * u₁ * g⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G))
    (h₂ : g * u₂ * g⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) := by
  have hg' : g * g * g = 1 := by
    rw [← pow_three']
    exact hg
  have hid : ∀ x : G, g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = x := by
    intro x
    have e : g * (g * (g * x * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * x * (g * g * g)⁻¹ := by
      group
    rw [e, hg', one_mul, inv_one, mul_one]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_closure_pair hu₁ hu₂ hu h₁ h₂ hx
  · intro hx
    have c₁ := conj_mem_closure_pair hu₁ hu₂ hu h₁ h₂ hx
    have c₂ := conj_mem_closure_pair hu₁ hu₂ hu h₁ h₂ c₁
    rwa [hid x] at c₂

end Closure

section Core

variable {G : Type} [Group G]

private theorem exists_e9_normalizing_four_group {P : Type} [Group P] (φ : G →* P)
    (hφ : Function.Injective φ) {a b u₁ u₂ va₁ va₂ vb₁ vb₂ : G} (ha3 : a ^ 3 = 1)
    (hb3 : b ^ 3 = 1) (hab : a * b = b * a)
    (hdist : ∀ i j k l : Fin 3, a ^ (i : ℕ) * b ^ (j : ℕ) = a ^ (k : ℕ) * b ^ (l : ℕ) →
      i = k ∧ j = l)
    (hu₁ : u₁ * u₁ = 1) (hu₂ : u₂ * u₂ = 1) (hu : u₁ * u₂ = u₂ * u₁) (hu₁1 : u₁ ≠ 1)
    (hva₁ : Four4 u₁ u₂ va₁) (hva₂ : Four4 u₁ u₂ va₂) (hvb₁ : Four4 u₁ u₂ vb₁)
    (hvb₂ : Four4 u₁ u₂ vb₂) (ha₁ : a * u₁ = va₁ * a) (ha₂ : a * u₂ = va₂ * a)
    (hb₁ : b * u₁ = vb₁ * b) (hb₂ : b * u₂ = vb₂ * b) :
    ∃ E V : Subgroup P, IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧
      IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set P) := by
  have hconj : ∀ (g t v : G), g * t = v * g → g * t * g⁻¹ = v := fun g t v h => by
    rw [h, mul_assoc, mul_inv_cancel, mul_one]
  have hA1 : a * u₁ * a⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) :=
    mem_closure_pair_of_four4 (by rw [hconj a u₁ va₁ ha₁]; exact hva₁)
  have hA2 : a * u₂ * a⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) :=
    mem_closure_pair_of_four4 (by rw [hconj a u₂ va₂ ha₂]; exact hva₂)
  have hB1 : b * u₁ * b⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) :=
    mem_closure_pair_of_four4 (by rw [hconj b u₁ vb₁ hb₁]; exact hvb₁)
  have hB2 : b * u₂ * b⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) :=
    mem_closure_pair_of_four4 (by rw [hconj b u₂ vb₂ hb₂]; exact hvb₂)
  have hNa : a ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) :=
    mem_normalizer_closure_pair hu₁ hu₂ hu ha3 hA1 hA2
  have hNb : b ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) :=
    mem_normalizer_closure_pair hu₁ hu₂ hu hb3 hB1 hB2
  have hE₀N : Subgroup.closure ({a, b} : Set G) ≤
      Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hNa
    · exact hNb
  refine ⟨(Subgroup.closure ({a, b} : Set G)).map φ,
    (Subgroup.closure ({u₁, u₂} : Set G)).map φ, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · show x * y = y * x
      obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨q, hq, hqy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hpx, ← hqy, ← map_mul, ← map_mul,
        mul_comm_of_mem_closure_pair ha3 hb3 hab hp hq]
    · obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, pow_three_eq_one_of_mem_closure_pair ha3 hb3 hab hp, map_one]
  · rw [Subgroup.card_map_of_injective hφ]
    exact card_closure_pair_three ha3 hb3 hab hdist
  · intro hV
    have hmem : φ u₁ ∈ (Subgroup.closure ({u₁, u₂} : Set G)).map φ :=
      Subgroup.mem_map_of_mem φ (Subgroup.subset_closure (Set.mem_insert _ _))
    rw [hV, Subgroup.mem_bot] at hmem
    exact hu₁1 (hφ (by rw [hmem, map_one]))
  · have hsq : ∀ y : ↥((Subgroup.closure ({u₁, u₂} : Set G)).map φ), y ^ 2 = 1 := by
      intro y
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← hwy, ← map_pow, sq,
        mul_self_eq_one_of_mem_closure_pair hu₁ hu₂ hu hw, map_one]
    exact fun y => ⟨1, by simpa using hsq y⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hx
    have hpN : p ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) :=
      hE₀N hp
    have hpinv : p⁻¹ ∈ Subgroup.normalizer (Subgroup.closure ({u₁, u₂} : Set G) : Set G) :=
      Subgroup.inv_mem _ hpN
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hh
      have e : φ p * φ w * (φ p)⁻¹ = φ (p * w * p⁻¹) := by
        simp only [map_mul, map_inv]
      rw [e]
      exact Subgroup.mem_map_of_mem φ ((Subgroup.mem_normalizer_iff.mp hpN w).mp hw)
    · intro hh
      obtain ⟨w', hw', hweq⟩ := Subgroup.mem_map.mp hh
      have hconjw : p⁻¹ * w' * p⁻¹⁻¹ ∈ Subgroup.closure ({u₁, u₂} : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hpinv w').mp hw'
      refine Subgroup.mem_map.mpr ⟨p⁻¹ * w' * p⁻¹⁻¹, hconjw, ?_⟩
      simp only [map_mul, map_inv, inv_inv]
      rw [hweq]
      group

end Core

theorem exists_e9_normalizing_two_projectiveSL (hK : Nat.card K = 2) {n : ℕ}
    (hn : n = 4 ∨ n = 5) :
    ∃ E V : Subgroup (projectiveSL n K), IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ V ≠ ⊥ ∧
      IsPGroup 2 V ∧ E ≤ Subgroup.normalizer (V : Set (projectiveSL n K)) := by
  haveI := charP_two_of_natCard_eq_two hK
  rcases hn with rfl | rfl
  · exact exists_e9_normalizing_four_group (embedTwo K 4)
      (embedTwo_injective hK (by norm_num))
      (a := sA4) (b := sB4) (u₁ := sU4) (u₂ := sV4) (va₁ := sV4)
      (va₂ := sU4 * sV4) (vb₁ := sU4 * sV4) (vb₂ := sU4)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
      (Four4.right _ _) (Four4.mul _ _) (Four4.mul _ _) (Four4.left _ _)
      (by decide) (by decide) (by decide) (by decide)
  · exact exists_e9_normalizing_four_group (embedTwo K 5)
      (embedTwo_injective hK (by norm_num))
      (a := sA5) (b := sB5) (u₁ := sU5) (u₂ := sV5) (va₁ := sV5)
      (va₂ := sU5 * sV5) (vb₁ := sU5 * sV5) (vb₂ := sU5)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)
      (Four4.right _ _) (Four4.mul _ _) (Four4.mul _ _) (Four4.left _ _)
      (by decide) (by decide) (by decide) (by decide)

end CFSG.RankThree.PartTwo.Sec21.Hering214
