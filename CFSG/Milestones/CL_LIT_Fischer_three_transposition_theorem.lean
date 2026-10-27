module

public import CFSG.Fischer.Classification.Final
public import CFSG.Fischer.Classification.PartII.O2G.ThreeFinal
public import CFSG.Fischer.Classification.Recognition.Classical
public import CFSG.Fischer.Classification.Milestone

public section

universe u v w

namespace CFSG.Open

open Matrix in
theorem _root_.CFSG.Milestones.cl_lit_fischer_three_transposition_theorem
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hsimple : IsSimpleGroup (commutator G)) :
    (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
    (∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) ∨
    (Nat.card G = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 ∧ Nat.card D = 3510) ∨
    (Nat.card G = 2 ^ 18 * 3 ^ 13 * 5 ^ 2 * 7 * 11 * 13 * 17 * 23 ∧ Nat.card D = 31671) ∨
    (Nat.card G = 2 ^ 22 * 3 ^ 16 * 5 ^ 2 * 7 ^ 3 * 11 * 13 * 17 * 23 * 29 ∧
      Nat.card D = 306936) :=
  CFSG.Fischer.Classification.milestone_of_statement
    (CFSG.Fischer.Classification.statement_of_twinFour
      CFSG.Fischer.Classification.o2TwinFourInput)
    G D hclass hinv hprod hgen hcenter hsimple


open Matrix in
theorem _root_.CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hsimple : IsSimpleGroup (commutator G)) :
    (∃ m : ℕ, (m = 3 ∨ 5 ≤ m) ∧
      ∃ φ : G ≃* Equiv.Perm (Fin m), ∀ g : G, g ∈ D ↔ (φ g).IsSwap) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 2 ≤ m ∧ ∃ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) ∧
      (m = 2 → ¬ ∃ W : Submodule (ZMod 2) (Fin (2 * m) → ZMod 2),
        Module.finrank (ZMod 2) W = 2 ∧ ∀ w ∈ W, Q w = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x)
        (fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1)) ∨
    (∃ m : ℕ, 4 ≤ m ∧
      fischerCentralQuotientModel D
        (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
        (fischerTransvections (fischerHermitianF4 m)
          fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1)) ∨
    (∃ φ : G ≃* Blueprint.NativeSporadic.Fi22, Blueprint.Fischer.Pair _ (φ '' D) ∧
      ∀ E : Set Blueprint.NativeSporadic.Fi22, Blueprint.Fischer.Pair _ E → E = φ '' D) ∨
    (∃ φ : G ≃* Blueprint.NativeSporadic.Fi23, Blueprint.Fischer.Pair _ (φ '' D) ∧
      ∀ E : Set Blueprint.NativeSporadic.Fi23, Blueprint.Fischer.Pair _ E → E = φ '' D) ∨
    (∃ φ : G ≃* MulAut Blueprint.NativeSporadic.Fi24prime, Blueprint.Fischer.Pair _ (φ '' D) ∧
      ∀ E : Set (MulAut Blueprint.NativeSporadic.Fi24prime),
        Blueprint.Fischer.Pair _ E → E = φ '' D) := by
  have h := CFSG.Fischer.Classification.pinned_of_statement
    (CFSG.Fischer.Classification.statement_of_twinFour CFSG.Fischer.Classification.o2TwinFourInput)
    (G := G) (D := D) ⟨⟨inferInstance, hclass, hinv, hprod, hgen⟩, hcenter, hsimple⟩
  rcases h with h | h
  · rcases h with h1 | h2 | h3 | h4 | h5
    · exact Or.inl h1
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h4)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

theorem _root_.CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hprod : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ))
    (hgen : Subgroup.closure D = ⊤)
    (hcenter : Subgroup.center G = ⊥)
    (hsimple : IsSimpleGroup (commutator G))
    (d : G) (hd : d ∈ D) :
    let C := Subgroup.centralizer ({d} : Set G)
    (Nonempty (G ≃* Blueprint.NativeSporadic.Fi22) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        Blueprint.LieModel (K ⧸ Subgroup.center K) .PSU 6 2 1) ∧
    (Nonempty (G ≃* Blueprint.NativeSporadic.Fi23) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* Blueprint.NativeSporadic.Fi22)) ∧
    (Nonempty (G ≃* MulAut Blueprint.NativeSporadic.Fi24prime) ↔
      ∃ K : Subgroup G, IsComponentOf K C ∧
        Nonempty ((K ⧸ Subgroup.center K) ≃* Blueprint.NativeSporadic.Fi23)) ∧
    (Nonempty (G ≃* Blueprint.NativeSporadic.Fi22) →
      commutator C = ⊤ ∧ (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧
        Nat.card (Subgroup.center C) = 2 ∧
        Blueprint.LieModel (C ⧸ Subgroup.center C) .PSU 6 2 1) ∧
    (Nonempty (G ≃* Blueprint.NativeSporadic.Fi23) →
      commutator C = ⊤ ∧ (Subgroup.center C).map C.subtype = Subgroup.zpowers d ∧
        Nat.card (Subgroup.center C) = 2 ∧
        Nonempty ((C ⧸ Subgroup.center C) ≃* Blueprint.NativeSporadic.Fi22)) ∧
    (Nonempty (G ≃* MulAut Blueprint.NativeSporadic.Fi24prime) →
      ∃ K : Subgroup G, Nonempty (K ≃* Blueprint.NativeSporadic.Fi23) ∧
        C = Subgroup.zpowers d ⊔ K ∧ Subgroup.zpowers d ⊓ K = ⊥ ∧
        Subgroup.zpowers d ≤ Subgroup.centralizer (K : Set G)) :=
  CFSG.Fischer.Classification.Recognition.recognition_of_statement
    CFSG.Fischer.Classification.Recognition.classicalComponentOrders
    (CFSG.Fischer.Classification.statement_of_twinFour CFSG.Fischer.Classification.o2TwinFourInput)
    ⟨⟨inferInstance, hclass, hinv, hprod, hgen⟩, hcenter, hsimple⟩ hd

end CFSG.Open
