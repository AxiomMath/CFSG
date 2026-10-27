module

public import CFSG.Quasithin.Background.F6SQTK
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (CoverOf)
open CFSG.Blueprint (LieModel)
open scoped MatrixGroups

section Vocabulary

variable {Q : Type} [Group Q] {V : Type} [CommGroup V]

@[expose] def IsQuadraticOn (ρ : Q →* MulAut V) (A : Subgroup Q) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹

@[expose] def fixedIn (ρ : Q →* MulAut V) (L : Subgroup Q) (I : Subgroup V) : Subgroup V where
  carrier := {i | i ∈ I ∧ ∀ l ∈ L, ρ l i = i}
  mul_mem' := fun {a b} ha hb =>
    ⟨I.mul_mem ha.1 hb.1, fun l hl => by rw [map_mul, ha.2 l hl, hb.2 l hl]⟩
  one_mem' := ⟨I.one_mem, fun l _ => map_one _⟩
  inv_mem' := fun {a} ha => ⟨I.inv_mem ha.1, fun l hl => by rw [map_inv, ha.2 l hl]⟩

@[expose] def IsIrr (ρ : Q →* MulAut V) (L : Subgroup Q) (I : Subgroup V) : Prop :=
  I ≠ ⊥ ∧ I = Subgroup.closure {x : V | ∃ i ∈ I, ∃ l ∈ L, x = ρ l i * i⁻¹} ∧
    ∀ J : Subgroup V, J ≤ I → (∀ l ∈ L, ∀ j ∈ J, ρ l j ∈ J) → fixedIn ρ L I ≤ J →
      J = fixedIn ρ L I ∨ J = I

theorem IsIrr.map_mem {ρ : Q →* MulAut V} {L : Subgroup Q} {I : Subgroup V} (h : IsIrr ρ L I)
    {l : Q} (hl : l ∈ L) {i : V} (hi : i ∈ I) : ρ l i ∈ I := by
  have h1 : ρ l i * i⁻¹ ∈ I := by
    rw [h.2.1]
    exact Subgroup.subset_closure ⟨i, hi, l, hl, rfl⟩
  simpa using I.mul_mem h1 hi

@[expose] def IsNaturalL3Two (ρ : Q →* MulAut V) (L : Subgroup Q) (I : Subgroup V) : Prop :=
  ∃ (e : ↥L ≃* GL (Fin 3) (ZMod 2)) (φ : ↥I ≃* Multiplicative (Fin 3 → ZMod 2)),
    ∀ (l : ↥L) (i j : ↥I), (j : V) = ρ (l : Q) (i : V) →
      Multiplicative.toAdd (φ j) =
        Matrix.mulVec ((e l : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
          (Multiplicative.toAdd (φ i))

@[expose] def IsDualPairing (ρ : Q →* MulAut V) (L : Subgroup Q) (I J : Subgroup V) : Prop :=
  ∃ β : V → V → ZMod 2,
    (∀ i₁ ∈ I, ∀ i₂ ∈ I, ∀ j ∈ J, β (i₁ * i₂) j = β i₁ j + β i₂ j) ∧
    (∀ i ∈ I, ∀ j₁ ∈ J, ∀ j₂ ∈ J, β i (j₁ * j₂) = β i j₁ + β i j₂) ∧
    (∀ i ∈ I, (∀ j ∈ J, β i j = 0) → i = 1) ∧
    (∀ j ∈ J, (∀ i ∈ I, β i j = 0) → j = 1) ∧
    ∀ l ∈ L, ∀ i ∈ I, ∀ j ∈ J, β (ρ l i) (ρ l j) = β i j

end Vocabulary

@[expose] def Hyp66Shape (Q : Type) [Group Q] (L : Subgroup Q) : Prop :=
  (∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 9 < p ^ e ∧ F6.IsL2 p e ↥L) ∨
    (∃ (p e : ℕ) (Y : Type) (_ : Group Y), p.Prime ∧ p ≠ 2 ∧ 3 < p ^ e ∧
      ((Odd e ∧ LieModel Y .PSL 3 p e) ∨ LieModel Y .PSU 3 p e) ∧ CoverOf ↥L Y) ∨
    F6.IsPGL2 7 Q

@[expose] def Asch6_6 : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ ρ : Q →* MulAut V, Function.Injective ρ →
    ∀ (L A : Subgroup Q), genFittingFStar Q = L → Nat.card A = 4 → IsElemAbelian 2 A →
      IsQuadraticOn ρ A → Hyp66Shape Q L →
      F6.IsL2 7 1 ↥L ∧ A ≤ L ∧
        ∀ I : Subgroup V, IsIrr ρ L I → IsNaturalL3Two ρ L I ∧
          ∀ g : Q, g ∉ L →
            (⨆ y : Q, I.map (ρ y).toMonoidHom) = I ⊔ I.map (ρ g).toMonoidHom ∧
              Disjoint I (I.map (ρ g).toMonoidHom) ∧
              IsDualPairing ρ L I (I.map (ρ g).toMonoidHom)

end CFSG.LocalAnalysis.WeakClosure81

end
