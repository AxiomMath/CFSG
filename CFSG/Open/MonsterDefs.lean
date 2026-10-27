module

public import CFSG.Open.Defs

public section

namespace CFSG.Open
open Matrix

@[expose] def monsterOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

@[expose] def monsterBabyOrder : ℕ := 2 ^ 41 * 3 ^ 13 * 5 ^ 6 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 31 * 47

@[expose] def monsterCo2Order : ℕ := 2 ^ 18 * 3 ^ 6 * 5 ^ 3 * 7 * 11 * 23

@[expose] def monsterFi23Order : ℕ := 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23

@[expose] def monsterFi22Order : ℕ := 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13

@[expose] def monsterThOrder : ℕ := 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31

@[expose] def monsterHNOrder : ℕ := 2 ^ 14 * 3 ^ 6 * 5 ^ 6 * 7 * 11 * 19

@[expose] def monsterMcLOrder : ℕ := 2 ^ 7 * 3 ^ 6 * 5 ^ 3 * 7 * 11


@[expose] def monsterGolayGen (k : Fin 12) (i : Fin 24) : ZMod 2 :=
  if (i : ℕ) = 23 then 1
  else if (k : ℕ) ≤ i ∧ (i : ℕ) - k ∈ ({0, 2, 4, 5, 6, 10, 11} : Finset ℕ) then 1 else 0

@[expose] noncomputable def monsterGolayCode : Submodule (ZMod 2) (Fin 24 → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range monsterGolayGen)

@[expose] def MonsterIsLeechVector (x : Fin 24 → ℤ) : Prop :=
  ∃ m : ℤ, (∀ i, x i ≡ m [ZMOD 2]) ∧
    (∀ k : ℤ, (fun i => if x i ≡ k [ZMOD 4] then (1 : ZMod 2) else 0) ∈ monsterGolayCode) ∧
    ∑ i, x i ≡ 4 * m [ZMOD 8]

@[expose] def monsterLeech : AddSubgroup (Fin 24 → ℤ) := AddSubgroup.closure {x | MonsterIsLeechVector x}

@[expose] def monsterLeechNorm (v : monsterLeech) : ℤ := ∑ i, ((v : Fin 24 → ℤ) i) ^ 2

@[expose] def monsterCo0 : Subgroup (monsterLeech ≃ₗ[ℤ] monsterLeech) where
  carrier := {e | ∀ v, monsterLeechNorm (e v) = monsterLeechNorm v}
  mul_mem' := by
    intro e f he hf v
    show monsterLeechNorm ((e * f) v) = monsterLeechNorm v
    rw [LinearEquiv.mul_apply, he, hf]
  one_mem' := fun _ => rfl
  inv_mem' := by
    intro e he v
    have h := he (e⁻¹ v)
    rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h
    exact h.symm

abbrev MonsterCo1 : Type := monsterCo0 ⧸ Subgroup.center monsterCo0

@[expose] noncomputable def monsterHerm (x y : Fin 6 → GaloisField 2 2) : GaloisField 2 2 :=
  ∑ i, x i * y i ^ 2

@[expose] noncomputable def monsterSU62 : Subgroup (GL (Fin 6) (GaloisField 2 2)) :=
  Subgroup.closure {A | (A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)).det = 1 ∧
    ∀ x y, monsterHerm ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ x)
      ((A : Matrix (Fin 6) (Fin 6) (GaloisField 2 2)) *ᵥ y) = monsterHerm x y}

abbrev MonsterU62 : Type := monsterSU62 ⧸ Subgroup.center monsterSU62

@[expose] def MonsterIsExtraspecial (P : Type*) [Group P] : Prop :=
  Nat.card (Subgroup.center P) = 2 ∧ commutator P = Subgroup.center P ∧
    ∀ x : P, x ^ 2 ∈ Subgroup.center P

@[expose] def MonsterHasShape {G : Type*} [Group G] (H : Subgroup G) (k n : ℕ) : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), Nat.card N = 2 ^ k ∧ IsSimpleGroup (H ⧸ N) ∧
    Nat.card (H ⧸ N) = n

@[expose] def MonsterHasLongTriangleShape {G : Type*} [Group G] (H : Subgroup G) : Prop :=
  ∃ (N : Subgroup H) (_ : N.Normal), Nat.card N = 2 ^ 23 ∧ Nonempty (H ⧸ N ≃* MonsterU62)

@[expose] def MonsterIsDoubleBabyCentralizer {G : Type*} [Group G] (a : G) : Prop :=
  commutator (Subgroup.centralizer ({a} : Set G)) = ⊤ ∧
    (Subgroup.center (Subgroup.centralizer ({a} : Set G))).map
      (Subgroup.centralizer ({a} : Set G)).subtype = Subgroup.zpowers a ∧
    IsSimpleGroup (Subgroup.centralizer ({a} : Set G) ⧸
      Subgroup.center (Subgroup.centralizer ({a} : Set G))) ∧
    Nat.card (Subgroup.centralizer ({a} : Set G) ⧸
      Subgroup.center (Subgroup.centralizer ({a} : Set G))) = monsterBabyOrder

@[expose] def MonsterIsLeechCentralizerType (H : Type*) [Group H] : Prop :=
  ∃ (Q : Subgroup H) (_ : Q.Normal), Nat.card Q = 2 ^ 25 ∧ MonsterIsExtraspecial Q ∧
    Subgroup.centralizer (Q : Set H) ≤ Q ∧ Nonempty (H ⧸ Q ≃* MonsterCo1)

@[expose] def MonsterIsF1Type {G : Type*} [Group G] (a z : G) : Prop :=
  orderOf a = 2 ∧ orderOf z = 2 ∧ MonsterIsDoubleBabyCentralizer a ∧
    MonsterIsLeechCentralizerType (Subgroup.centralizer ({z} : Set G))

@[expose] def monsterCent2 {G : Type*} [Group G] (α β : G) : Subgroup G :=
  Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({β} : Set G)

@[expose] def monsterSuborbitElementOrder : Fin 9 → ℕ := ![1, 2, 2, 3, 3, 4, 4, 5, 6]

@[expose] def monsterSuborbitTwoExponent : Fin 9 → ℕ := ![1, 2, 24, 0, 0, 23, 1, 0, 1]

@[expose] def monsterSuborbitSimpleOrder : Fin 9 → ℕ :=
  ![monsterBabyOrder, ordTwistedE6 2, monsterCo2Order, monsterFi23Order, monsterThOrder,
    monsterMcLOrder, ordF4 2, monsterHNOrder, monsterFi22Order]

@[expose] def MonsterTwoAGraphData {G : Type*} [Group G] (a z : G) : Prop :=
  (∀ β, IsConj a β → ∀ β', IsConj a β' → IsConj (a * β) (a * β') →
    ∃ g ∈ Subgroup.centralizer ({a} : Set G), g * β * g⁻¹ = β') ∧
  ∃ β : Fin 9 → G, (∀ i, IsConj a (β i)) ∧ β 0 = a ∧
    (∀ i j, IsConj (a * β i) (a * β j) → i = j) ∧
    (∀ γ, IsConj a γ → ∃ i, IsConj (a * γ) (a * β i)) ∧
    IsConj a (a * β 1) ∧ IsConj z (a * β 2) ∧
    (∀ i, orderOf (a * β i) = monsterSuborbitElementOrder i) ∧
    (∀ i, MonsterHasShape (monsterCent2 a (β i)) (monsterSuborbitTwoExponent i)
      (monsterSuborbitSimpleOrder i)) ∧
    (∀ β', IsConj a β' → IsConj (a * β') (a * β 3) →
      {γ | IsConj a γ ∧ IsConj (a * γ) (a * β 3) ∧ IsConj a (β' * γ)}.Nonempty ∧
      (∀ γ γ', IsConj a γ ∧ IsConj (a * γ) (a * β 3) ∧ IsConj a (β' * γ) →
        IsConj a γ' ∧ IsConj (a * γ') (a * β 3) ∧ IsConj a (β' * γ') →
        ∃ g ∈ monsterCent2 a β', g * γ * g⁻¹ = γ') ∧
      ∀ γ, IsConj a γ ∧ IsConj (a * γ) (a * β 3) ∧ IsConj a (β' * γ) →
        Nonempty (↥(monsterCent2 a β' ⊓ Subgroup.centralizer ({γ} : Set G)) ≃*
          Matrix.symplecticGroup (Fin 4) (ZMod 2))) ∧
    (∀ β', IsConj a β' → IsConj (a * β') (a * β 6) →
      ¬ IsConj a (a * β') ∧ ∃! γ, IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ)) ∧
    (∀ β', IsConj a β' → IsConj (a * β') (a * β 3) →
      (∃ D : Set ↥(monsterCent2 a β'),
        (Finite ↥(monsterCent2 a β') ∧ (∃ e : ↥(monsterCent2 a β'), D = {x | IsConj e x}) ∧
          (∀ e ∈ D, orderOf e = 2) ∧
          (∀ e ∈ D, ∀ f ∈ D, orderOf (e * f) ∈ ({1, 2, 3} : Set ℕ)) ∧
          Subgroup.closure D = ⊤) ∧
        {γ | IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ)} = Subtype.val '' D ∧
        ∀ γ ∈ D, Nat.card ↥(Subgroup.centralizer ({γ} : Set ↥(monsterCent2 a β'))) =
          2 ^ 18 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13) ∧
      Set.ncard {γ | IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ)} = 31671) ∧
    (∀ β', IsConj a β' → IsConj a (a * β') →
      Set.ncard {γ | IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ)} = 3968056 ∧
      (∀ γ γ', IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ) ∧ γ ≠ a * β' →
        IsConj a γ' ∧ IsConj a (a * γ') ∧ IsConj a (β' * γ') ∧ γ' ≠ a * β' →
        ∃ g ∈ monsterCent2 a β', g * γ * g⁻¹ = γ') ∧
      (∀ γ, IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ) ∧ γ ≠ a * β' →
        MonsterHasLongTriangleShape (monsterCent2 a β' ⊓ Subgroup.centralizer ({γ} : Set G))) ∧
      ∃ γ δ, (IsConj a γ ∧ IsConj a (a * γ) ∧ IsConj a (β' * γ) ∧ γ ≠ a * β') ∧
        IsConj a δ ∧ IsConj (a * δ) (a * β 3) ∧ IsConj (β' * δ) (a * β 3) ∧
        (monsterCent2 a β' ⊓ Subgroup.centralizer ({γ} : Set G)) ⊔
          (monsterCent2 a β' ⊓ Subgroup.centralizer ({δ} : Set G)) = monsterCent2 a β' ∧
        Nonempty (↥(monsterCent2 a β' ⊓ Subgroup.centralizer ({δ} : Set G)) ≃*
          Matrix.symplecticGroup (Fin 4) (ZMod 2)))

end CFSG.Open