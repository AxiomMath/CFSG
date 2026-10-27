module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryBasic

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

abbrev PSUg (n : ℕ) (K : Type) [Field K] (q : ℕ) : Type :=
  LargeEvenProj (LargeEvenSUGroup (Fin n) K q)

@[expose] def IsConjBy {n : ℕ} {K : Type} [Field K] {q : ℕ} (d : GL (Fin n) K) (δ' : MulAut (PSUg n K q)) : Prop :=
  LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q))
    (fun h h' => (h' : GL (Fin n) K) = d * h * d⁻¹) δ'

structure UniLift (n q : ℕ) (K : Type) [Field K] (Ā : Subgroup (MulAut (PSUg n K q)))
    (Ahat : Subgroup (GL (Fin n) K)) : Prop where
  iso : ∀ g ∈ Ahat, IsHermIsometry q (g : Matrix (Fin n) (Fin n) K)
  scalars : ∀ c : Kˣ, c ^ (q + 1) = 1 → Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ Ahat
  induces : ∀ g ∈ Ahat, ∃ a ∈ Ā, IsConjBy g a
  onto : ∀ a ∈ Ā, ∃ g ∈ Ahat, IsConjBy g a
  ker : ∀ g ∈ Ahat, IsConjBy g (1 : MulAut (PSUg n K q)) →
    ∃ c : Kˣ, c ^ (q + 1) = 1 ∧ g = Matrix.GeneralLinearGroup.scalar (Fin n) c

@[expose] def Uni6KG7OnR : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (q : ℕ), Nat.card K = q ^ 2 → 3 ∣ q + 1 →
    ∀ (Ā : Subgroup (MulAut (PSUg 6 K q))) (δ' : MulAut (PSUg 6 K q)) (J' : Subgroup (PSUg 6 K q)),
      RDatum Ā δ' J' → Nat.card Ā = 3 ^ 3 →
      (∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K q))
        (LargeEvenGUSet (Fin 6) K q)) →
      (∃ (F : Type) (_ : Field F) (_ : Finite F), 4 ≤ Nat.card F ∧
        Nonempty (J' ⧸ Subgroup.center J' ≃* LargeEvenProj (LargeEvenSLGroup (Fin 2) F))) →
      ¬ ∃ U : Subgroup (MulAut (PSUg 6 K q)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ a ∈ Ā, ∀ u ∈ U, a * u * a⁻¹ ∈ U

@[expose] def Uni5KG7OnR : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (q : ℕ), Nat.card K = q ^ 2 → 3 ∣ q + 1 →
    ∀ (Ā : Subgroup (MulAut (PSUg 5 K q))) (δ' : MulAut (PSUg 5 K q)) (J' : Subgroup (PSUg 5 K q)),
      RDatum Ā δ' J' → Nat.card Ā = 3 ^ 3 →
      (∀ a ∈ Ā, a ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 5) K q))
        (LargeEvenGUSet (Fin 5) K q)) →
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (q' : ℕ), Nat.card F = q' ^ 2 ∧ 4 ≤ q' ∧
        Nonempty (J' ⧸ Subgroup.center J' ≃* LargeEvenProj (LargeEvenSUGroup (Fin 3) F q'))) →
      ¬ ∃ U : Subgroup (MulAut (PSUg 5 K q)), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ a ∈ Ā, ∀ u ∈ U, a * u * a⁻¹ ∈ U

end CFSG.StandardType.TablePThreeKG

end
