module

public import CFSG.LocalAnalysis.ZStar.ClassSums

public section

namespace CFSG

namespace ZStar.ClassProductValue

open ZStar.ClassSums

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Fintype G]

local instance : DecidableEq G := Classical.decEq G

@[expose] noncomputable def coefficientAugmentation (R : Type v) [CommSemiring R] :
    MonoidAlgebra R G →ₐ[R] R :=
  (MonoidAlgebra.lift R R G) (1 : G →* R)

@[simp]
theorem coefficientAugmentation_single (R : Type v) [CommSemiring R]
    (g : G) (r : R) :
    coefficientAugmentation (G := G) R (MonoidAlgebra.single g r) = r := by
  simp [coefficientAugmentation]

@[simp]
theorem coefficientAugmentation_classSum (R : Type v) [CommSemiring R]
    (C : ConjClasses G) :
    coefficientAugmentation (G := G) R (classSum R C) = (classSize C : R) := by
  simp [classSum, classSize]

theorem sum_structureConstant_mul_classSize (C D : ConjClasses G) :
    (∑ E : ConjClasses G, structureConstant C D E * classSize E) =
      classSize C * classSize D := by
  have h := congrArg (coefficientAugmentation (G := G) ℕ) (classSum_mul ℕ C D)
  simpa [map_mul, map_sum, map_smul, nsmul_eq_mul] using h.symm

section Character

variable {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [Representation.IsIrreducible ρ]

private theorem classProduct_character_identity (C D : ConjClasses G) :
    (classSize C : k) * (classSize D : k) *
        (ρ.character (classRep C) * ρ.character (classRep D)) =
      (Module.finrank k V : k) *
        ∑ E : ConjClasses G,
          (structureConstant C D E : k) * (classSize E : k) *
            ρ.character (classRep E) := by
  let degree : k := Module.finrank k V
  have hC := omega_mul_degree ρ C
  have hD := omega_mul_degree ρ D
  have hproduct := omega_product ρ C D
  have hweighted :
      (∑ E : ConjClasses G,
          (structureConstant C D E : k) * omega ρ E) * degree =
        ∑ E : ConjClasses G,
          (structureConstant C D E : k) * (classSize E : k) *
            ρ.character (classRep E) := by
    calc
      (∑ E : ConjClasses G,
          (structureConstant C D E : k) * omega ρ E) * degree =
          ∑ E : ConjClasses G,
            ((structureConstant C D E : k) * omega ρ E) * degree := by
        rw [Finset.sum_mul]
      _ = ∑ E : ConjClasses G,
            (structureConstant C D E : k) * (omega ρ E * degree) := by
        apply Finset.sum_congr rfl
        intro E _
        ring
      _ = ∑ E : ConjClasses G,
            (structureConstant C D E : k) * (classSize E : k) *
              ρ.character (classRep E) := by
        apply Finset.sum_congr rfl
        intro E _
        rw [show omega ρ E * degree =
            (classSize E : k) * ρ.character (classRep E) by
          exact omega_mul_degree ρ E]
        ring
  calc
    (classSize C : k) * (classSize D : k) *
        (ρ.character (classRep C) * ρ.character (classRep D)) =
        (omega ρ C * degree) * (omega ρ D * degree) := by
      rw [show omega ρ C * degree =
          (classSize C : k) * ρ.character (classRep C) by exact hC]
      rw [show omega ρ D * degree =
          (classSize D : k) * ρ.character (classRep D) by exact hD]
      ring
    _ = degree * ((omega ρ C * omega ρ D) * degree) := by ring
    _ = degree *
        ((∑ E : ConjClasses G,
          (structureConstant C D E : k) * omega ρ E) * degree) := by
      rw [hproduct]
    _ = (Module.finrank k V : k) *
        ∑ E : ConjClasses G,
          (structureConstant C D E : k) * (classSize E : k) *
            ρ.character (classRep E) := by
      rw [hweighted]

theorem character_mul_eq_degree_mul_of_constant_on_product
    (C D : ConjClasses G) (a : k)
    (hchar : ∀ E : ConjClasses G, structureConstant C D E ≠ 0 →
      ρ.character (classRep E) = a) :
    ρ.character (classRep C) * ρ.character (classRep D) =
      (Module.finrank k V : k) * a := by
  have hmassCast :
      (∑ E : ConjClasses G,
        (structureConstant C D E : k) * (classSize E : k)) =
          (classSize C : k) * (classSize D : k) := by
    exact_mod_cast sum_structureConstant_mul_classSize (G := G) C D
  have hsum :
      (∑ E : ConjClasses G,
        (structureConstant C D E : k) * (classSize E : k) *
          ρ.character (classRep E)) =
        (classSize C : k) * (classSize D : k) * a := by
    calc
      (∑ E : ConjClasses G,
        (structureConstant C D E : k) * (classSize E : k) *
          ρ.character (classRep E)) =
          ∑ E : ConjClasses G,
            (structureConstant C D E : k) * (classSize E : k) * a := by
        apply Finset.sum_congr rfl
        intro E _
        by_cases hE : structureConstant C D E = 0
        · simp [hE]
        · rw [hchar E hE]
      _ = (∑ E : ConjClasses G,
          (structureConstant C D E : k) * (classSize E : k)) * a := by
        rw [Finset.sum_mul]
      _ = (classSize C : k) * (classSize D : k) * a := by rw [hmassCast]
  have hid := classProduct_character_identity ρ C D
  rw [hsum] at hid
  have hCpos : 0 < classSize C :=
    Finset.card_pos.mpr ⟨classRep C, classRep_mem_classFinset C⟩
  have hDpos : 0 < classSize D :=
    Finset.card_pos.mpr ⟨classRep D, classRep_mem_classFinset D⟩
  have hCne : (classSize C : k) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCpos)
  have hDne : (classSize D : k) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hDpos)
  apply mul_left_cancel₀ (mul_ne_zero hCne hDne)
  calc
    ((classSize C : k) * (classSize D : k)) *
        (ρ.character (classRep C) * ρ.character (classRep D)) =
        (Module.finrank k V : k) *
          ((classSize C : k) * (classSize D : k) * a) := hid
    _ = ((classSize C : k) * (classSize D : k)) *
        ((Module.finrank k V : k) * a) := by ring

end Character

end

end ZStar.ClassProductValue

end CFSG
