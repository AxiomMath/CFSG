module

public import CFSG.Timmesfeld.Orders.ClassicalHypSum
public import CFSG.Timmesfeld.Orders.ClassicalAnisotropic
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.Timmesfeld.ClassicalOrders

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module

variable (K : Type*) [Field K]

@[expose] noncomputable def plusSplit (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) → K) ≃ₗ[K] (K × K) × (Fin m ⊕ Fin m → K) where
  toFun v := ((v (.inl 0), v (.inr 0)), fun s => v (Sum.map Fin.succ Fin.succ s))
  invFun p := Sum.elim (Fin.cons p.1.1 fun i => p.2 (.inl i))
    (Fin.cons p.1.2 fun i => p.2 (.inr i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext s
    rcases s with i | i <;> refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv p := Prod.ext rfl (funext fun s => by rcases s with i | i <;> rfl)

@[expose] noncomputable def plusIsometry (m : ℕ) :
    (quadPlus (m + 1) K).IsometryEquiv (hypSum (quadPlus m K)) :=
  { plusSplit K m with
    map_app' := fun v => by
      change hypSum (quadPlus m K) (plusSplit K m v) = quadPlus (m + 1) K v
      rw [hypSum_apply, quadPlus_apply, quadPlus_apply, Fin.sum_univ_succ]
      rfl }

@[expose] noncomputable def minusSplit (m : ℕ) :
    (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → K) ≃ₗ[K] (K × K) × (Fin m ⊕ Fin m ⊕ Fin 2 → K) where
  toFun v := ((v (.inl 0), v (.inr (.inl 0))),
    fun s => v (Sum.map Fin.succ (Sum.map Fin.succ id) s))
  invFun p := Sum.elim (Fin.cons p.1.1 fun i => p.2 (.inl i))
    (Sum.elim (Fin.cons p.1.2 fun i => p.2 (.inr (.inl i))) fun k => p.2 (.inr (.inr k)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv v := by
    funext s
    rcases s with i | i | k
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · refine Fin.cases ?_ (fun j => ?_) i <;> rfl
    · rfl
  right_inv p := Prod.ext rfl (funext fun s => by rcases s with i | i | k <;> rfl)

@[expose] noncomputable def minusIsometry (m : ℕ) (b c : K) :
    (quadMinus (m + 1 + 1) K b c).IsometryEquiv (hypSum (quadMinus (m + 1) K b c)) :=
  { minusSplit K m with
    map_app' := fun (v : Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → K) => by
      change hypSum (quadMinus (m + 1) K b c) (minusSplit K m v) = quadMinus (m + 1 + 1) K b c v
      have hsum : ∑ i : Fin (m + 1), v (.inl i) * v (.inr (.inl i)) =
          v (.inl 0) * v (.inr (.inl 0)) + ∑ i : Fin m, v (.inl i.succ) * v (.inr (.inl i.succ)) :=
        Fin.sum_univ_succ _
      rw [hypSum_apply, quadMinus_apply, quadMinus_apply]
      change v (.inl 0) * v (.inr (.inl 0)) + (∑ i : Fin m, v (.inl i.succ) * v (.inr (.inl i.succ))
        + v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2) = ∑ i : Fin (m + 1), v (.inl i) * v (.inr (.inl i)) +
        v (.inr (.inr 0)) ^ 2 + b * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        c * v (.inr (.inr 1)) ^ 2
      rw [hsum]
      ring }

variable {K}

section Congr

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
  {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}

theorem card_singular_congr (e : Q₁.IsometryEquiv Q₂) :
    Nat.card {v // Q₁ v = 0} = Nat.card {v // Q₂ v = 0} :=
  Nat.card_congr (Equiv.subtypeEquiv e.toLinearEquiv.toEquiv fun v => by
    change _ ↔ Q₂ (e v) = 0
    rw [e.map_app])

theorem card_orthogonalGroup_congr (e : Q₁.IsometryEquiv Q₂) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₁) =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q₂) :=
  Nat.card_congr (TauCeti.QuadraticMap.orthogonalGroupCongr e).toEquiv

end Congr

theorem one_le_card_singular {V : Type*} [AddCommGroup V] [Module K V] [Finite V]
    (Q : QuadraticForm K V) : 1 ≤ Nat.card {v // Q v = 0} :=
  have : Nonempty {v // Q v = 0} := ⟨⟨0, QuadraticMap.map_zero Q⟩⟩
  Nat.card_pos

theorem card_singular_and_orthogonalGroup_of_subsingleton {V : Type*} [AddCommGroup V]
    [Module K V] [Subsingleton V] (Q : QuadraticForm K V) :
    Nat.card {v // Q v = 0} = 1 ∧ Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 1 := by
  have : Subsingleton (V ≃ₗ[K] V) := ⟨fun a b => LinearEquiv.ext fun x => Subsingleton.elim _ _⟩
  refine ⟨Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩,
    ⟨⟨0, QuadraticMap.map_zero Q⟩⟩⟩, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩⟩

theorem card_coord_fun {α : Type*} (ι : Type*) [Fintype ι] :
    Nat.card (ι → α) = Nat.card α ^ Fintype.card ι := by
  rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]

variable [Finite K] [CharP K 2]

theorem card_step {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [Finite W] {Q : QuadraticForm K V} {Q' : QuadraticForm K W} (e : Q.IsometryEquiv (hypSum Q'))
    (hQ' : (polarBilin Q').Nondegenerate) :
    Nat.card {v // Q v = 0} =
        Nat.card K * Nat.card {w // Q' w = 0} + (Nat.card K - 1) * Nat.card W ∧
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) =
        (Nat.card {v // Q v = 0} - 1) * Nat.card W *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q') := by
  rw [card_singular_congr e, card_orthogonalGroup_congr e]
  exact ⟨card_singular_hypSum Q', card_orthogonalGroup_hypSum hQ' CharTwo.two_eq_zero⟩

theorem card_quadPlus (m : ℕ) :
    (Nat.card {v // quadPlus (m + 1) K v = 0} : ℤ) =
        1 + ((Nat.card K : ℤ) ^ (m + 1) - 1) * ((Nat.card K : ℤ) ^ m + 1) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadPlus (m + 1) K)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hW : ∀ m, Nat.card (Fin m ⊕ Fin m → K) = Nat.card K ^ (2 * m) := fun m => by
    rw [card_coord_fun, Fintype.card_sum, Fintype.card_fin, two_mul]
  induction m with
  | zero =>
    obtain ⟨hS, hO⟩ := card_step (plusIsometry K 0) (nondegenerate_polarBilin_quadPlus 0 K)
    obtain ⟨hS0, hO0⟩ := card_singular_and_orthogonalGroup_of_subsingleton (quadPlus 0 K)
    rw [hS0, hW 0] at hS
    rw [hW 0, hO0, hS] at hO
    simp only [mul_one] at hS hO
    have h1 : 1 ≤ Nat.card K + (Nat.card K - 1) := by omega
    constructor
    · rw [hS]
      push_cast [hq]
      ring
    · rw [hO]
      push_cast [hq, h1]
      simp
      ring
  | succ m ih =>
    obtain ⟨hS, hO⟩ := card_step (plusIsometry K (m + 1))
      (nondegenerate_polarBilin_quadPlus (m + 1) K)
    have hS1 := one_le_card_singular (quadPlus (m + 1 + 1) K)
    rw [hW] at hS hO
    obtain ⟨ihS, ihO⟩ := ih
    constructor
    · rw [hS]
      push_cast [hq]
      rw [ihS]
      ring
    · rw [hO]
      push_cast [hS1]
      rw [ihO, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), hS]
      push_cast [hq]
      rw [ihS]
      ring

theorem card_quadMinus (m : ℕ) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card {v // quadMinus (m + 1) K b c v = 0} : ℤ) =
        1 + ((Nat.card K : ℤ) ^ (m + 1) + 1) * ((Nat.card K : ℤ) ^ m - 1) ∧
      (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus (m + 1) K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) + 1) *
          ∏ i ∈ Finset.Icc 1 m, ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  have hq : 1 ≤ Nat.card K := Nat.one_le_iff_ne_zero.mpr Finite.card_pos.ne'
  have hW : ∀ k, Nat.card (Fin k ⊕ Fin k ⊕ Fin 2 → K) = Nat.card K ^ (2 * k + 2) := fun k => by
    rw [card_coord_fun, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    ring_nf
  induction m with
  | zero =>
    have hani : ∀ v, v ≠ 0 → quadMinus 1 K b c v ≠ 0 := by
      intro v hv h0
      apply hv
      rw [quadMinus_apply, Finset.sum_eq_zero (fun i _ => (i : Fin 0).elim0), zero_add] at h0
      obtain ⟨hu, hw⟩ := binary_eq_zero_of_irreducible hirr h0
      funext k
      rcases k with i | i | j
      · exact i.elim0
      · exact i.elim0
      · fin_cases j
        · exact hu
        · exact hw
    have hA : finrank K (Fin (1 - 1) ⊕ Fin (1 - 1) ⊕ Fin 2 → K) = 2 := by simp
    have hS0 : Nat.card {v // quadMinus 1 K b c v = 0} = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨⟨fun x y => Subtype.ext (by
        rw [of_not_not fun h => hani x.1 h x.2, of_not_not fun h => hani y.1 h y.2])⟩,
        ⟨⟨0, QuadraticMap.map_zero _⟩⟩⟩
    constructor
    · rw [hS0]
      simp
    · rw [card_orthogonalGroup_of_anisotropic hA hani]
      push_cast
      simp
  | succ m ih =>
    obtain ⟨hS, hO⟩ := card_step (minusIsometry K m b c)
      (nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hirr)
    have hS1 := one_le_card_singular (quadMinus (m + 1 + 1) K b c)
    have hWm : Nat.card (Fin (m + 1 - 1) ⊕ Fin (m + 1 - 1) ⊕ Fin 2 → K) =
        Nat.card K ^ (2 * (m + 1)) := by
      rw [hW, Nat.add_sub_cancel]
      ring_nf
    rw [hWm] at hS hO
    obtain ⟨ihS, ihO⟩ := ih
    constructor
    · rw [hS]
      push_cast [hq]
      rw [ihS]
      ring
    · rw [hO]
      push_cast [hS1]
      rw [ihO, Finset.prod_Icc_succ_top (by omega : 1 ≤ m + 1), hS]
      push_cast [hq]
      rw [ihS]
      ring

end CFSG.Timmesfeld.ClassicalOrders
