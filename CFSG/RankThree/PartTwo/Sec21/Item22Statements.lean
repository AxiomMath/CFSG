module

public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.PartTwo.Sec21.MonomialCoords
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLSingularPlaneRoots

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions)
open Matrix

abbrev SL3 (n : ℕ) : Type := Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 n)

@[expose] noncomputable def SU3 (n : ℕ) : Subgroup (GL (Fin 3) (GaloisField 2 (2 * n))) :=
  Subgroup.closure {A : GL (Fin 3) (GaloisField 2 (2 * n)) |
    Matrix.GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))).map (· ^ (2 ^ n)))ᵀ *
      (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 (2 * n))) = 1}

variable {G : Type} [Group G]

@[expose] def dStarIn (A : Subgroup G) : Set (Subgroup.closure (dStar A)) :=
  {x | (x : MulAut A) ∈ dStar A}

@[expose] def Item2131 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      (∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
          (wStar A).map (coordGL f) ≤ KFacts.KP14.monomial ∧
          ∃ G₀ : Subgroup (MulAut A), G₀ ≤ wStar A ∧
            Nonempty (G₀ ≃* alternatingGroup (Fin 4))) ∧
      ((∃ n : ℕ, 0 < n ∧ Even n ∧ (Nonempty (lBar L ≃* projSp 2 (GaloisField 2 n)) ∨
          Nonempty (lBar L ≃* projSU 4 2 n) ∨ Nonempty (lBar L ≃* SL3 n))) ∨
        Nonempty (lBar L ≃* projSU 5 2 2))

@[expose] def Item2131One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∃ f : Multiplicative (Fin 3 → ZMod 3) ≃* A,
          (wStar A).map (coordGL f) ≤ KFacts.KP14.monomial ∧
          ∃ G₀ : Subgroup (MulAut A), G₀ ≤ wStar A ∧
            Nonempty (G₀ ≃* alternatingGroup (Fin 4))

@[expose] def Item221 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
      (Nat.card A = 3 ^ 4 ∧ ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n)) ∨
      (Nat.card A = 3 ^ 3 ∧
        ((∃ n : ℕ, 0 < n ∧ Even n ∧ (Nonempty (L ≃* projSp 2 (GaloisField 2 n)) ∨
            Nonempty (L ≃* projSU 4 2 n) ∨ Nonempty (L ≃* SL3 n))) ∨
          Nonempty (L ≃* projSU 5 2 2) ∨
          (Nonempty (lBar L ≃* SL3 2) ∧ ∀ a ∈ A, a ∉ Subgroup.zpowers c →
            inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≠ ⊥ →
            Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {a}) ≃*
              projSL 2 (GaloisField 2 2)))))

@[expose] def Case222 (A L K : Subgroup G) : Prop :=
  (Nat.card A = 3 ^ 3 ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (lBar L ≃* SL3 n) ∧
      Nonempty (K ≃* projSL 2 (GaloisField 2 n)) ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 3))) ∨
    (Nat.card A = 3 ^ 3 ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧
      Nonempty (L ≃* projSp 2 (GaloisField 2 n)) ∧ Nonempty (K ≃* projSL 2 (GaloisField 2 n)) ∧
      Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
    (Nat.card A = 3 ^ 3 ∧ ∃ n : ℕ, 0 < n ∧ Even n ∧ Nonempty (L ≃* projSU 4 2 n) ∧
      (Nonempty (K ≃* projSL 2 (GaloisField 2 n)) ∨
        Nonempty (K ≃* projSL 2 (GaloisField 2 (2 * n)))) ∧
      Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
    (Nat.card A = 3 ^ 3 ∧ Nonempty (L ≃* projSU 5 2 2) ∧
      (Nonempty (K ≃* projSL 2 (GaloisField 2 2)) ∨
        Nonempty (K ≃* projSL 2 (GaloisField 2 4))) ∧
      Nonempty (starOf A L ≃* DihedralGroup 4)) ∨
    (Nat.card A = 3 ^ 4 ∧ ∃ n : ℕ, 1 < n ∧ Odd n ∧ Nonempty (L ≃* projSU 4 2 n) ∧
      Nonempty (K ≃* projSL 2 (GaloisField 2 n)) ∧
      Nonempty (starOf A L ≃* Equiv.Perm (Fin 4)))

@[expose] def Item222 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L →
      starOf A L = Subgroup.closure ((starOf A L : Set (MulAut A)) ∩ dStar A) ∧
      ((starOf A L : Set (MulAut A)) ∩ dStar A).Nonempty ∧
      ∀ φ ∈ starOf A L, φ ∈ dStar A → Case222 A L (kOf A φ)

@[expose] def Item223 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 → ∀ n : ℕ, Nonempty (L ≃* projSU 4 2 n) →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A,
        (∀ X ∈ lStar A, kOf A φ ≤ X → Nonempty (X ≃* projSU 4 2 n)) ∧
        (ψ ≠ φ → ψ * φ = φ * ψ → ⁅kOf A φ, kOf A ψ⁆ = ⊥) ∧
        (ψ * φ ≠ φ * ψ → Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* SU3 n) ∧
          Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))

@[expose] def Item223Print : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A,
        (∀ X ∈ lStar A, kOf A φ ≤ X → ∃ m : ℕ, 1 < m ∧ Odd m ∧
            Nonempty (X ≃* projSU 4 2 m) ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m))) ∧
        (ψ ≠ φ → ψ * φ = φ * ψ → ⁅kOf A φ, kOf A ψ⁆ = ⊥) ∧
        (ψ * φ ≠ φ * ψ →
          (∃ m : ℕ, Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
            Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* SU3 m)) ∧
          Nonempty (Subgroup.closure {φ, ψ} ≃* Equiv.Perm (Fin 3)))

@[expose] def Item224 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Odd (Nat.card (Subgroup.centralizer (A : Set G)))

@[expose] def Item225 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nonempty (lBar L ≃* SL3 2) →
      inSubgroup (aschbacherSolvableCore 3) L = ⊥

@[expose] def Item226 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 4 →
      Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 5)) ∧
      Nonempty (iGroup A ≃* projSU 5 2 3)

@[expose] def Item228 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ →
        (∀ X ∈ lStar A, kOf A φ ≤ X → ∃ m : ℕ, 0 < m ∧ Even m ∧
            Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
            (Nonempty (X ≃* SL3 m) ∨ Nonempty (X ≃* projSp 2 (GaloisField 2 m)) ∨
              Nonempty (X ≃* projSU 4 2 m) ∨
              (m % 4 = 0 ∧ Nonempty (X ≃* projSU 4 2 (m / 2))) ∨
              ((m = 2 ∨ m = 4) ∧ Nonempty (X ≃* projSU 5 2 2)))) ∧
        (ψ * φ = φ * ψ →
          ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨
          (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ ∃ m : ℕ, 0 < m ∧ m % 4 = 0 ∧
            Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
            Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 (m / 2)) ∧
            ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ) ∨
          (Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 4)) ∧
            Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 4)) ∧
            Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
            (∃ X ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X ∧ Nonempty (X ≃* projSU 5 2 2)) ∧
            ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ)) ∧
        (ψ * φ ≠ φ * ψ →
          (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ Case222 A (kOf A φ ⊔ kOf A ψ) (kOf A φ) ∧
            IsEmpty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 5 2 2)) ∨
          (Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
            ∃ X ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X ∧ Nonempty (X ≃* projSU 5 2 2)))

@[expose] def Item229 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      (Nonempty (Subgroup.closure (dStar A) ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (iGroup A ≃* projSL 4 (GaloisField 2 2))) ∨
        (wStar A = Subgroup.closure (dStar A) ∧
          Nonempty (wStar A ≃* (ℤˣ × Equiv.Perm (Fin 4))) ∧
          Nonempty (iGroup A ≃* projSp 3 (GaloisField 2 2)))

end CFSG.RankThree.PartTwo.Sec21
