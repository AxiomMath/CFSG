module

public import CFSG.LocalAnalysis.StandardType.GGKD2Leaves1615
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagProj
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryAlgebra
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel

public section

namespace S2MathAs3_1624

open CFSG CFSG.Assembly CFSG.StandardType
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
open scoped MatrixGroups

noncomputable section

@[expose] def IsCubicExtension (K : Type) [Field K] (E : Type) [Field E] [Algebra K E] : Prop :=
  FiniteDimensional K E ∧ Module.finrank K E = 3 ∧ Nat.card E = Nat.card K ^ 3

theorem noncube_units_iff_field {K : Type} [Field K] (κ : Kˣ) :
    (∀ c : Kˣ, c ^ 3 ≠ κ) ↔ (∀ c : K, c ^ 3 ≠ (κ : K)) := by
  constructor
  · intro h c hc
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact κ.ne_zero (by simpa using hc.symm)
    exact h (Units.mk0 c hc0)
      (Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0]; exact hc))
  · intro h c hc
    exact h (c : K) (by rw [← Units.val_pow_eq_pow_val]; exact congrArg Units.val hc)

@[expose] def CubicFieldBlockContract : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E),
      1 ≤ m ∧ d = 3 * m ∧
      IsCubicExtension K E ∧
      Irreducible (Polynomial.X ^ 3 - Polynomial.C (κ : K)) ∧
      ∃ α : E,
        α ^ 3 = algebraMap K E (κ : K) ∧
        Algebra.adjoin K ({α} : Set E) = ⊤ ∧
        ∃ b : (Fin d → K) ≃ₗ[K] (Fin m → E),
          ∀ v : Fin d → K,
            b ((S : Matrix (Fin d) (Fin d) K).mulVec v) = α • b v

@[expose] def LinearFullCentralizerContract : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    ∀ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E),
      d = 3 * m → IsCubicExtension K E →
      ∀ (α : E), α ^ 3 = algebraMap K E (κ : K) →
      ∀ b : (Fin d → K) ≃ₗ[K] (Fin m → E),
        (∀ v : Fin d → K,
          b ((S : Matrix (Fin d) (Fin d) K).mulVec v) = α • b v) →
        ∃ Φ : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K))) ≃* GL (Fin m) E,
          ∀ (g : ↥(Subgroup.centralizer ({S} : Set (GL (Fin d) K)))) (v : Fin d → K),
            b (((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).mulVec v) =
              ((Φ g : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).mulVec (b v)

@[expose] def LinearComponentContract : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hSnorm : S ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∀ J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      CFSG.Assembly.IsComponentOf J
        (ggFixSub (TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨S, hSnorm⟩)) →
      ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E),
        2 ≤ m ∧ d = 3 * m ∧ IsCubicExtension K E ∧
        Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
          ↥(LargeEvenSLGroup (Fin m) E) ⧸
            Subgroup.center ↥(LargeEvenSLGroup (Fin m) E))

@[expose] def UnitaryPrimaryBlockContract : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (h : UnitaryFieldData 2 n K)
    (d : ℕ) (hd : 2 ≤ d) (M : primeFormUnitary h (idGram K d)) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    (M : GL (Fin d) K) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    ∃ a : primaryFactors ((toLinU h d M : LinearMap.GeneralLinearGroup K (Fin d → K)) :
        Module.End K (Fin d → K)),
      (a : Polynomial K) = Polynomial.X ^ 3 - Polynomial.C (κ : K) ∧
      primaryComponent ((toLinU h d M : LinearMap.GeneralLinearGroup K (Fin d → K)) :
          Module.End K (Fin d → K)) (a : Polynomial K) = ⊤ ∧
      d = 3 * primaryMultiplicity ((toLinU h d M : LinearMap.GeneralLinearGroup K (Fin d → K)) :
          Module.End K (Fin d → K)) (a : Polynomial K) ∧
      SelfDualPrimaryBlock h (idForm h d) (toLinU h d M) a ∧
      ∀ b : primaryFactors ((toLinU h d M : LinearMap.GeneralLinearGroup K (Fin d → K)) :
          Module.End K (Fin d → K)), b = a

@[expose] def UnitaryComponentShapeAt (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ)
    (_ : UnitaryFieldData 2 n K) (d : ℕ) (S : GL (Fin d) K)
    (hSnorm : S ∈ Subgroup.normalizer
      ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K)))
    (J : Subgroup (LargeEvenProj (unitarySU 2 n K d))) : Prop :=
  CFSG.Assembly.IsComponentOf J
    (ggFixSub (TableB.projConj (unitarySU 2 n K d) ⟨S, hSnorm⟩)) →
  3 ∣ 2 ^ n + 1 ∧
  ∃ (m : ℕ) (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Finite E)
    (_ : UnitaryFieldData 2 (3 * n) E),
    2 ≤ m ∧ d = 3 * m ∧ IsCubicExtension K E ∧
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      ↥(unitarySU 2 (3 * n) E m) ⧸
        Subgroup.center ↥(unitarySU 2 (3 * n) E m))

@[expose] def UnitaryComponentContract : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (h : UnitaryFieldData 2 n K)
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ∈ primeFormUnitary h (idGram K d) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hSnorm : S ∈ Subgroup.normalizer
      ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∀ J : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
      UnitaryComponentShapeAt K n h d S hSnorm J

@[expose] def UnitaryComponentContractSimilitude : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (h : UnitaryFieldData 2 n K)
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ∈ LargeEvenGUSet (Fin d) K (2 ^ n) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hSnorm : S ∈ Subgroup.normalizer
      ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∀ J : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
      UnitaryComponentShapeAt K n h d S hSnorm J

@[expose] def UnitarySimilitudeNormalisation : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (h : UnitaryFieldData 2 n K)
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ∈ LargeEvenGUSet (Fin d) K (2 ^ n) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hS : S ∈ Subgroup.normalizer
      ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∃ (c : Kˣ) (κ' : Kˣ)
      (_ : Matrix.GeneralLinearGroup.scalar (Fin d) c * S ∈ primeFormUnitary h (idGram K d))
      (hS' : Matrix.GeneralLinearGroup.scalar (Fin d) c * S ∈ Subgroup.normalizer
        ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))),
      (∀ e : Kˣ, e ^ 3 ≠ κ') ∧
      (Matrix.GeneralLinearGroup.scalar (Fin d) c * S) ^ 3 =
        Matrix.GeneralLinearGroup.scalar (Fin d) κ' ∧
      TableB.projConj (unitarySU 2 n K d) ⟨S, hS⟩ =
        TableB.projConj (unitarySU 2 n K d)
          ⟨Matrix.GeneralLinearGroup.scalar (Fin d) c * S, hS'⟩

@[expose] def LinearA1EightImpossible : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (d : ℕ) (hd : 2 ≤ d)
    (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hS : S ∈ Subgroup.normalizer
      ((LargeEvenSLGroup (Fin d) K : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∀ J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin d) K)),
      CFSG.Assembly.IsComponentOf J
        (ggFixSub (TableB.projConj (LargeEvenSLGroup (Fin d) K) ⟨S, hS⟩)) →
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) → False

@[expose] def UnitaryA1EightForcesSixOne : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) (h : UnitaryFieldData 2 n K)
    (d : ℕ) (hd : 2 ≤ d) (S : GL (Fin d) K) (κ : Kˣ),
    (∀ c : Kˣ, c ^ 3 ≠ κ) →
    S ∈ LargeEvenGUSet (Fin d) K (2 ^ n) →
    S ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin d) κ →
    (hS : S ∈ Subgroup.normalizer
      ((unitarySU 2 n K d : Subgroup (GL (Fin d) K)) : Set (GL (Fin d) K))) →
    ∀ J : Subgroup (LargeEvenProj (unitarySU 2 n K d)),
      CFSG.Assembly.IsComponentOf J
        (ggFixSub (TableB.projConj (unitarySU 2 n K d) ⟨S, hS⟩)) →
      GGHasLabel (⟨.A, 1, 3⟩ : LargeEvenLabel) (↥J ⧸ Subgroup.center ↥J) →
      d = 6 ∧ n = 1

theorem leaf6LabelFromD3_holds :
    ∀ (lab : LargeEvenLabel) (d n : ℕ),
      lab.tag = .twA → lab.rank + 1 = d → lab.n = n → d = 6 → n = 1 →
      lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) := by
  rintro lab d n htag hrank hn hd hn1
  rcases lab with ⟨t, r, e⟩
  simp only [LargeEvenLabel.mk.injEq] at htag hrank hn
  simp only [LargeEvenLabel.mk.injEq]
  exact ⟨htag, by omega, by omega⟩

theorem twA_label_of_d6_n1 {lab : LargeEvenLabel} {d : ℕ}
    (htag : lab.tag = .twA) (hrank : lab.rank + 1 = d) (hd : d = 6) (hn : lab.n = 1) :
    lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) :=
  leaf6LabelFromD3_holds lab d 1 htag hrank hn hd rfl

theorem card_cubic_of_unitary {K E : Type} [Field K] [Field E] {n : ℕ}
    (h : UnitaryFieldData 2 n K) (hE : UnitaryFieldData 2 (3 * n) E) :
    Nat.card E = Nat.card K ^ 3 := by
  rw [hE.card, h.card, ← pow_mul]
  congr 1
  ring

end

end S2MathAs3_1624

end
