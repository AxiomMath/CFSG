module

public import CFSG.Open.FischerThreeTranspositionMilestoneDefs

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Open

theorem fischerSymNotPerfect : ∀ m : ℕ, 2 ≤ m → ¬ Group.IsPerfect (Equiv.Perm (Fin m)) := by
  intro m hm hP
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
  have : Group.IsPerfect ℤˣ := Group.IsPerfect.ofSurjective (Equiv.Perm.sign_surjective (Fin m))
  have : Subsingleton ℤˣ := Group.IsPerfect.subsingleton_of_isMulCommutative
  exact absurd (Subsingleton.elim (1 : ℤˣ) (-1)) (by decide)

@[expose] def FischerSpCard : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, b x x = 0) → (∀ x, (∀ y, b x y = 0) → x = 0) →
    Group.IsPerfect (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) →
    45 ≤ Nat.card {g : fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) //
      (g : GL (Fin (2 * m)) (ZMod 2)) ∈ fischerTransvections (fun x y => b x y) fun v => v ≠ 0}

@[expose] def FischerOrthCard : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) →
    Group.IsPerfect (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) →
    45 ≤ Nat.card {g : fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x) //
      (g : GL (Fin (2 * m)) (ZMod 2)) ∈ fischerTransvections (QuadraticMap.polar Q)
        fun v => Q v = 1}

@[expose] def FischerSpClique : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, b x x = 0) → (∀ x, (∀ y, b x y = 0) → x = 0) →
    Group.IsPerfect (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y) →
    ∃ s : Fin 6 → fischerMatrixGroup (fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y),
      Function.Injective s ∧
      (∀ i, (s i : GL (Fin (2 * m)) (ZMod 2)) ∈
        fischerTransvections (fun x y => b x y) fun v => v ≠ 0) ∧
      ∀ i j, s i * s j = s j * s i

@[expose] def FischerOrthClique : Prop :=
  ∀ (m : ℕ), 2 ≤ m → ∀ Q : QuadraticForm (ZMod 2) (Fin (2 * m) → ZMod 2),
    (∀ x, (∀ y, QuadraticMap.polar Q x y = 0) → x = 0) →
    Group.IsPerfect (fischerMatrixGroup fun A => ∀ x, Q (A *ᵥ x) = Q x) →
    ∃ s : Fin 6 → fischerMatrixGroup (fun A => ∀ x, Q (A *ᵥ x) = Q x),
      Function.Injective s ∧
      (∀ i, (s i : GL (Fin (2 * m)) (ZMod 2)) ∈
        fischerTransvections (QuadraticMap.polar Q) fun v => Q v = 1) ∧
      ∀ i j, s i * s j = s j * s i

@[expose] def FischerUnitaryCard : Prop :=
  ∀ m : ℕ, 4 ≤ m →
    45 ≤ Nat.card {q : (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) ⧸
        Subgroup.center (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y) //
      ∃ h : (fischerMatrixGroup fun A => A.det = 1 ∧
          ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y),
        (h : GL (Fin m) (GaloisField 2 2)) ∈ fischerTransvections (fischerHermitianF4 m)
          (fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0) ∧
        q = (QuotientGroup.mk h : _ ⧸ Subgroup.center _)}

@[expose] def FischerReflectionCard : Prop :=
  ∀ (m : ℕ), 5 ≤ m → ∀ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
    (∀ x y, f x y = f y x) → (∀ x, (∀ y, f x y = 0) → x = 0) →
    Group.IsPerfect ((Subgroup.closure (fischerTransvections (fun x y => f x y)
        fun v => f v v = 1)) ⧸ Subgroup.center (Subgroup.closure (fischerTransvections
          (fun x y => f x y) fun v => f v v = 1))) →
    45 ≤ Nat.card {q : (Subgroup.closure (fischerTransvections (fun x y => f x y)
        fun v => f v v = 1)) ⧸ Subgroup.center (Subgroup.closure (fischerTransvections
          (fun x y => f x y) fun v => f v v = 1)) //
      ∃ h : Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1),
        (h : GL (Fin m) (ZMod 3)) ∈ fischerTransvections (fun x y => f x y)
          (fun v => f v v = 1) ∧
        q = (QuotientGroup.mk h : _ ⧸ Subgroup.center _)}

end CFSG.RankThree.SubgroupLists
