module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.JacobsonDensity
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke

namespace CFSG
end CFSG
open CFSG

/-!
# Degree bounds for finite-group representations

This file contains the `Representation`-level degree estimates used in
Peterfalvi, Section 1, Proposition (1.8).  The central ingredient is the
standard Burnside/Jacobson-density argument behind Isaacs, Corollary 2.30:
if an irreducible complex representation is scalar on a subgroup `D`, then
the full endomorphism algebra is spanned by representatives for the cosets of
`D`, hence `dim V ^ 2 ≤ [G : D]`.
-/

noncomputable section

open scoped BigOperators commutatorElement

namespace CFSG.Theory.Character

open _root_.Representation
open Theory.Representation

attribute [local instance] Fintype.ofFinite

variable {G V : Type*} [Group G] [Finite G]
variable [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Direct commutator form of the condition `D/B ≤ Z(G/B)`.

This avoids quotient notation in later statements while remaining equivalent
to the book condition when `B` is normal and `B ≤ D`. -/
@[expose] public def IsCentralModulo (B D : Subgroup G) : Prop :=
  ∀ ⦃d : G⦄, d ∈ D → ∀ c : G, ⁅d, c⁆ ∈ B

private abbrev DegreeRightCosets (D : Subgroup G) :=
  Quotient (QuotientGroup.rightRel D)

private def degreeRightCosetOut (D : Subgroup G) (g : G) : G :=
  Quotient.out (Quotient.mk (QuotientGroup.rightRel D) g)

omit [Finite G] in
private theorem degreeRightCosetOut_spec (D : Subgroup G) (g : G) :
    g * (degreeRightCosetOut D g)⁻¹ ∈ D := by
  simpa [degreeRightCosetOut, QuotientGroup.rightRel_apply] using
    (Quotient.mk_out (s := QuotientGroup.rightRel D) g)

omit [Finite G] in
private theorem degreeRightCosetOut_eq_of_mk_eq (D : Subgroup G) {g h : G}
    (eq : Quotient.mk (QuotientGroup.rightRel D) g =
      Quotient.mk (QuotientGroup.rightRel D) h) :
    degreeRightCosetOut D g = degreeRightCosetOut D h :=
  congrArg Quotient.out eq

private def degreeRightCosetCorrection (D : Subgroup G) (g : G) : D :=
  ⟨g * (degreeRightCosetOut D g)⁻¹, degreeRightCosetOut_spec D g⟩

omit [Finite G] in
private theorem degreeRightCosetCorrection_mul_out (D : Subgroup G) (g : G) :
    ((degreeRightCosetCorrection D g : D) : G) * degreeRightCosetOut D g = g := by
  simp [degreeRightCosetCorrection, degreeRightCosetOut, mul_assoc]

omit [Finite G] in
private lemma degreeRightCosets_nat_card_eq_index (D : Subgroup G) :
    Nat.card (DegreeRightCosets D) = D.index := by
  classical
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel D)

omit [Finite G] in
private theorem span_range_eq_top_of_irreducible_isAlgClosed
    (ρ : Representation ℂ G V) [IsIrreducible ρ] :
    Submodule.span ℂ (Set.range (ρ : G → Module.End ℂ V)) = ⊤ := by
  have htop :
      Algebra.adjoin ℂ (Set.range (ρ : G → Module.End ℂ V)) = ⊤ :=
    jacobson_density_surjective_isAlgClosed_rep ρ
  have hspan :
      Subalgebra.toSubmodule
          (Algebra.adjoin ℂ (Set.range (ρ : G → Module.End ℂ V))) =
        Submodule.span ℂ (Set.range (ρ : G → Module.End ℂ V)) := by
    simpa [MonoidHom.mclosure_range (ρ : G →* Module.End ℂ V), MonoidHom.coe_mrange] using
      (Algebra.adjoin_eq_span (R := ℂ) (s := Set.range (ρ : G → Module.End ℂ V)))
  calc
    Submodule.span ℂ (Set.range (ρ : G → Module.End ℂ V))
        = Subalgebra.toSubmodule
            (Algebra.adjoin ℂ (Set.range (ρ : G → Module.End ℂ V))) := by
          simpa using hspan.symm
    _ = ⊤ := by simp [htop]

omit [Finite G] [FiniteDimensional ℂ V] in
private lemma mem_span_coset_representatives_of_scalar_on_subgroup
    (ρ : Representation ℂ G V) (D : Subgroup G)
    (hDscalar : ∀ d : D, ∃ a : ℂ, ρ d = a • (1 : Module.End ℂ V))
    (g : G) :
    ρ g ∈
      Submodule.span ℂ
        (Set.range fun q : DegreeRightCosets D =>
          ρ (degreeRightCosetOut D (Quotient.out q))) := by
  classical
  let q : DegreeRightCosets D := Quotient.mk (QuotientGroup.rightRel D) g
  let d : D := degreeRightCosetCorrection D g
  obtain ⟨a, ha⟩ := hDscalar d
  have hg : (d : G) * degreeRightCosetOut D g = g :=
    degreeRightCosetCorrection_mul_out D g
  have hqout : degreeRightCosetOut D (Quotient.out q) = degreeRightCosetOut D g := by
    exact degreeRightCosetOut_eq_of_mk_eq D (by simp [q])
  have hrange :
      ρ (degreeRightCosetOut D g) ∈
        Set.range fun q : DegreeRightCosets D =>
          ρ (degreeRightCosetOut D (Quotient.out q)) := by
    refine ⟨q, ?_⟩
    simp [hqout]
  have hmem :
      ρ (degreeRightCosetOut D g) ∈
        Submodule.span ℂ
          (Set.range fun q : DegreeRightCosets D =>
            ρ (degreeRightCosetOut D (Quotient.out q))) :=
    Submodule.subset_span hrange
  have hρeq : ρ g = a • ρ (degreeRightCosetOut D g) := by
    calc
      ρ g = ρ ((d : G) * degreeRightCosetOut D g) := by rw [hg]
      _ = ρ d * ρ (degreeRightCosetOut D g) := by simp
      _ = (a • (1 : Module.End ℂ V)) * ρ (degreeRightCosetOut D g) := by rw [ha]
      _ = a • ρ (degreeRightCosetOut D g) := by
        ext v
        simp
  rw [hρeq]
  exact Submodule.smul_mem _ a hmem

/-- If an irreducible complex representation is scalar on `D`, then
`dim V ^ 2 ≤ [G : D]`. -/
public theorem irreducible_finrank_sq_le_index_of_scalar_on_subgroup
    (ρ : Representation ℂ G V) [IsIrreducible ρ] (D : Subgroup G)
    (hDscalar : ∀ d : D, ∃ a : ℂ, ρ d = a • (1 : Module.End ℂ V)) :
    Module.finrank ℂ V ^ 2 ≤ D.index := by
  classical
  let reps : DegreeRightCosets D → Module.End ℂ V :=
    fun q => ρ (degreeRightCosetOut D (Quotient.out q))
  have hburnside :
      Submodule.span ℂ (Set.range (ρ : G → Module.End ℂ V)) = ⊤ :=
    span_range_eq_top_of_irreducible_isAlgClosed (ρ := ρ)
  have hspan_le :
      Submodule.span ℂ (Set.range (ρ : G → Module.End ℂ V)) ≤
        Submodule.span ℂ (Set.range reps) := by
    refine Submodule.span_le.mpr ?_
    intro f hf
    rcases hf with ⟨g, rfl⟩
    exact mem_span_coset_representatives_of_scalar_on_subgroup
      (ρ := ρ) D hDscalar g
  have hreps_top :
      Submodule.span ℂ (Set.range reps) = (⊤ : Submodule ℂ (Module.End ℂ V)) := by
    exact top_unique (by simpa [hburnside] using hspan_le)
  have hfin_span :
      Module.finrank ℂ (Submodule.span ℂ (Set.range reps)) ≤ Nat.card (DegreeRightCosets D) := by
    have h₁ :
        Module.finrank ℂ (Submodule.span ℂ (Set.range reps)) ≤
          (Finset.univ.image reps).card := by
      simpa [Set.toFinset_range] using
        (finrank_span_le_card (R := ℂ) (s := Set.range reps))
    exact h₁.trans (by
      simpa [Nat.card_eq_fintype_card] using
        (Finset.card_image_le (f := reps) (s := Finset.univ)))
  have hend :
      Module.finrank ℂ (Module.End ℂ V) = Module.finrank ℂ V * Module.finrank ℂ V := by
    simpa [Module.End] using
      (Module.finrank_linearMap (R := ℂ) (S := ℂ) (M := V) (N := V))
  calc
    Module.finrank ℂ V ^ 2 = Module.finrank ℂ V * Module.finrank ℂ V := by
      rw [pow_two]
    _ = Module.finrank ℂ (Module.End ℂ V) := hend.symm
    _ = Module.finrank ℂ (Submodule.span ℂ (Set.range reps)) := by
      rw [hreps_top]
      exact (finrank_top ℂ (Module.End ℂ V)).symm
    _ ≤ Nat.card (DegreeRightCosets D) := hfin_span
    _ = D.index := degreeRightCosets_nat_card_eq_index D

omit [Finite G] [FiniteDimensional ℂ V] in
private lemma commute_of_commutator_mem_kernel
    (ρ : Representation ℂ G V) (B : Subgroup G)
    (hBker : ∀ b : B, ρ b = (1 : Module.End ℂ V))
    {d c : G} (hcomm : ⁅d, c⁆ ∈ B) :
    ρ d * ρ c = ρ c * ρ d := by
  have hcomm_image : ρ ⁅d, c⁆ = (1 : Module.End ℂ V) :=
    hBker ⟨⁅d, c⁆, hcomm⟩
  have hmul :
      ρ d * ρ c * ρ d⁻¹ * ρ c⁻¹ = (1 : Module.End ℂ V) := by
    simpa [commutatorElement_def, map_mul] using hcomm_image
  calc
    ρ d * ρ c =
        (ρ d * ρ c * ρ d⁻¹ * ρ c⁻¹) * (ρ c * ρ d) := by
          ext v
          simp [Module.End.mul_apply, mul_assoc]
    _ = ρ c * ρ d := by rw [hmul, one_mul]

omit [Finite G] in
private lemma scalar_on_subgroup_of_centralModulo_kernel
    (ρ : Representation ℂ G V) [IsIrreducible ρ] (B D : Subgroup G)
    (hBker : ∀ b : B, ρ b = (1 : Module.End ℂ V))
    (hcentral : IsCentralModulo B D) (d : D) :
    ∃ a : ℂ, ρ d = a • (1 : Module.End ℂ V) := by
  classical
  let φ : IntertwiningMap ρ ρ :=
    { toLinearMap := ρ d
      isIntertwining' := by
        intro c
        exact LinearMap.ext fun v =>
          congrArg (fun f : Module.End ℂ V => f v)
            (commute_of_commutator_mem_kernel
              (ρ := ρ) B hBker (hcentral d.2 c)) }
  obtain ⟨a, ha⟩ :=
    (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := ρ)).surjective φ
  refine ⟨a, ?_⟩
  have hlin : ((algebraMap ℂ (Representation.IntertwiningMap ρ ρ) a :
      Representation.IntertwiningMap ρ ρ) : Module.End ℂ V) =
      (φ : Module.End ℂ V) :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => (f : Module.End ℂ V)) ha
  have halg : ((algebraMap ℂ (Representation.IntertwiningMap ρ ρ) a :
      Representation.IntertwiningMap ρ ρ) : Module.End ℂ V) =
      ((a • (1 : Representation.IntertwiningMap ρ ρ)) : Representation.IntertwiningMap ρ ρ) :=
    congrArg (fun f : Representation.IntertwiningMap ρ ρ => (f : Module.End ℂ V))
      (Representation.IntertwiningMap.algebraMap_apply ρ a)
  calc
    (ρ d : Module.End ℂ V) = (φ : Module.End ℂ V) := rfl
    _ = ((algebraMap ℂ (Representation.IntertwiningMap ρ ρ) a :
        Representation.IntertwiningMap ρ ρ) : Module.End ℂ V) := hlin.symm
    _ = ((a • (1 : Representation.IntertwiningMap ρ ρ)) :
        Representation.IntertwiningMap ρ ρ) := halg
    _ = a • (1 : Module.End ℂ V) := by
      ext v
      simp [LinearMap.smul_apply]

/-- Isaacs, Corollary 2.30 in the direct commutator form used by Peterfalvi
(1.8): if `D/B` is central and `B` is in the kernel of an irreducible
character, then the degree squared is at most `[G : D]`. -/
public theorem irreducible_finrank_sq_le_index_of_centralModulo_kernel
    (ρ : Representation ℂ G V) [IsIrreducible ρ] (B D : Subgroup G)
    (hBker : ∀ b : B, ρ b = (1 : Module.End ℂ V))
    (hcentral : IsCentralModulo B D) :
    Module.finrank ℂ V ^ 2 ≤ D.index := by
  exact irreducible_finrank_sq_le_index_of_scalar_on_subgroup
    (ρ := ρ) D (scalar_on_subgroup_of_centralModulo_kernel
      (ρ := ρ) B D hBker hcentral)

end CFSG.Theory.Character
