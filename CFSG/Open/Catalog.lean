module

public import Mathlib
public import CFSG.Foundations.MaxCardThompson
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open Matrix
open scoped MatrixGroups

universe u

@[expose] noncomputable def PSU3 (p k : ℕ) [Fact p.Prime] :
    Subgroup (ProjGenLinGroup (Fin 3) (GaloisField p (2 * k))) :=
  (Subgroup.closure {A : GL (Fin 3) (GaloisField p (2 * k)) |
      (Matrix.of fun i j =>
          (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) j i ^ (p ^ k)) *
        !![0, 0, 1; 0, 1, 0; 1, 0, 0] *
        (A : Matrix (Fin 3) (Fin 3) (GaloisField p (2 * k))) =
      !![0, 0, 1; 0, 1, 0; 1, 0, 0] ∧
    GeneralLinearGroup.det A = 1}).map ProjGenLinGroup.mk

@[expose] def SzGenerators (n : ℕ) : Set (Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1))) :=
  {M | (∃ a b, M = !![1, a, b, a ^ (2 + 2 ^ (n + 1)) + a * b + b ^ (2 ^ (n + 1));
                      0, 1, a ^ (2 ^ (n + 1)), a ^ (1 + 2 ^ (n + 1)) + b;
                      0, 0, 1, a;
                      0, 0, 0, 1]) ∨
       (∃ x : (GaloisField 2 (2 * n + 1))ˣ,
          M = !![(x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n), 0, 0, 0;
                 0, (x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n), 0, 0;
                 0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (2 ^ n))⁻¹, 0;
                 0, 0, 0, ((x : GaloisField 2 (2 * n + 1)) ^ (1 + 2 ^ n))⁻¹]) ∨
       M = !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0]}

@[expose] noncomputable def Sz (n : ℕ) : Subgroup (GL (Fin 4) (GaloisField 2 (2 * n + 1))) :=
  Subgroup.closure {A | (A : Matrix (Fin 4) (Fin 4) (GaloisField 2 (2 * n + 1))) ∈
    SzGenerators n}

@[expose] def semidihedralRels (n : ℕ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of 0 ^ (2 ^ (n - 1)), FreeGroup.of 1 ^ 2,
    FreeGroup.of 1 * FreeGroup.of 0 * (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0 ^ (2 ^ (n - 2) - 1))⁻¹}

abbrev SemidihedralGroup (n : ℕ) : Type := PresentedGroup (semidihedralRels n)

abbrev WreathedTwoGroup (n : ℕ) : Type :=
  Multiplicative (ZMod (2 ^ n)) ≀ᵣ Multiplicative (ZMod 2)

@[expose] def M11 : Subgroup (Equiv.Perm (Fin 11)) :=
  Subgroup.closure
    {List.formPerm [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
      List.formPerm [2, 6, 10, 7] * List.formPerm [3, 9, 4, 5]}

@[expose, reducible] def thompsonSubgroup {G : Type*} [Group G] (S : Subgroup G) : Subgroup G :=
  ambientMaxCardThompson S

theorem thompsonSubgroup_eq_iSup {G : Type*} [Group G] (S : Subgroup G) :
    thompsonSubgroup S = ⨆ (A : Subgroup G) (_ : A ≤ S) (_ : IsMulCommutative A)
      (_ : ∀ B : Subgroup G, B ≤ S → IsMulCommutative B → Nat.card B ≤ Nat.card A), A := by
  apply le_antisymm
  · exact sSup_le fun A hA => le_iSup_of_le A (le_iSup_of_le hA.1 (le_iSup_of_le hA.2.1
      (le_iSup_of_le hA.2.2 le_rfl)))
  · exact iSup_le fun A => iSup_le fun hAS => iSup_le fun hAc => iSup_le fun hAm =>
      le_sSup ⟨hAS, hAc, hAm⟩

@[expose] def IsPStable (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ P : Subgroup G, IsPGroup p P →
    ∀ x ∈ Subgroup.normalizer (P : Set G), (∃ k : ℕ, x ^ p ^ k = 1) →
      (∀ y ∈ P, (y * x * y⁻¹ * x⁻¹) * x = x * (y * x * y⁻¹ * x⁻¹)) →
      ∃ K : Subgroup G, K ≤ Subgroup.normalizer (P : Set G) ∧
        (K.subgroupOf (Subgroup.normalizer (P : Set G))).Normal ∧
        Subgroup.centralizer (P : Set G) ≤ K ∧ x ∈ K ∧
        ∀ y ∈ K, ∃ k : ℕ, y ^ p ^ k ∈ Subgroup.centralizer (P : Set G)

structure IsSolvableSignalizerFunctor (p : ℕ) {G : Type*} [Group G] (A : Subgroup G)
    (θ : G → Subgroup G) : Prop where
  le_centralizer : ∀ a ∈ A, a ≠ 1 → θ a ≤ Subgroup.centralizer {a}
  coprime : ∀ a ∈ A, a ≠ 1 → Nat.Coprime p (Nat.card (θ a))
  invariant : ∀ a ∈ A, a ≠ 1 → ∀ x ∈ A, (θ a).map (MulAut.conj x).toMonoidHom = θ a
  balance : ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 → θ a ⊓ Subgroup.centralizer {b} ≤ θ b
  solvable : ∀ a ∈ A, a ≠ 1 → Group.IsSolvable (θ a)

end CFSG.Open