module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Init
public import CFSG.LocalAnalysis.ZStar.CharacterContradiction

public section

namespace CFSG

namespace ZStar.ClassSums

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Fintype G]

local instance : DecidableEq G := Classical.decEq G

@[expose] noncomputable def classRep (C : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective C)

omit [Fintype G] in
@[simp] theorem mk_classRep (C : ConjClasses G) : ConjClasses.mk (classRep C) = C :=
  Classical.choose_spec (ConjClasses.mk_surjective C)

@[expose] noncomputable def classFinset (C : ConjClasses G) : Finset G :=
  by
    classical
    exact C.carrier.toFinset

@[simp]
theorem mem_classFinset {C : ConjClasses G} {x : G} :
    x ∈ classFinset C ↔ ConjClasses.mk x = C := by
  classical
  simp [classFinset, ConjClasses.mem_carrier_iff_mk_eq]

@[simp]
theorem classRep_mem_classFinset (C : ConjClasses G) : classRep C ∈ classFinset C := by
  simp

@[expose] noncomputable def classSize (C : ConjClasses G) : ℕ :=
  (classFinset C).card

theorem classSize_eq_natCard_carrier (C : ConjClasses G) :
    classSize C = Nat.card C.carrier := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [classSize, classFinset]

@[expose] noncomputable def classSum (R : Type v) [Semiring R] (C : ConjClasses G) :
    MonoidAlgebra R G :=
  ∑ x ∈ classFinset C, MonoidAlgebra.single x 1

@[simp]
theorem classSum_coeff (R : Type v) [Semiring R] (C : ConjClasses G) (x : G) :
    (classSum R C).coeff x = if ConjClasses.mk x = C then 1 else 0 := by
  classical
  simp [classSum, Finsupp.finsetSum_apply, Finsupp.single_apply,
    mem_classFinset]

theorem classSum_coeff_of_mem (R : Type v) [Semiring R]
    {C : ConjClasses G} {x : G} (hx : ConjClasses.mk x = C) :
    (classSum R C).coeff x = 1 := by
  simp [hx]

theorem classSum_coeff_of_not_mem (R : Type v) [Semiring R]
    {C : ConjClasses G} {x : G} (hx : ConjClasses.mk x ≠ C) :
    (classSum R C).coeff x = 0 := by
  simp [hx]

private theorem classSum_commute_single (R : Type v) [CommSemiring R]
    (C : ConjClasses G) (g : G) :
    MonoidAlgebra.single g 1 * classSum R C =
      classSum R C * MonoidAlgebra.single g 1 := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one, classSum_coeff]
  have hmk : ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨g, ?_⟩
    group
  rw [hmk]

theorem classSum_mem_center (R : Type v) [CommSemiring R] (C : ConjClasses G) :
    classSum R C ∈ Submonoid.center (MonoidAlgebra R G) := by
  classical
  rw [Submonoid.mem_center_iff]
  intro z
  induction z using MonoidAlgebra.induction_on with
  | of g =>
      simpa only [MonoidAlgebra.of_apply] using classSum_commute_single R C g
  | add x y hx hy =>
      simp only [add_mul, mul_add, hx, hy]
  | smul r x hx =>
      simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using congrArg (r • ·) hx

theorem classSum_commute (R : Type v) [CommSemiring R]
    (C : ConjClasses G) (z : MonoidAlgebra R G) :
    z * classSum R C = classSum R C * z :=
  (Submonoid.mem_center_iff.mp (classSum_mem_center R C)) z

omit [Fintype G] in
theorem coeff_eq_of_isConj (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G))
    {a b : G} (hab : IsConj a b) : z.coeff a = z.coeff b := by
  classical
  rw [isConj_iff] at hab
  obtain ⟨g, rfl⟩ := hab
  have hcomm := (Submonoid.mem_center_iff.mp hz) (MonoidAlgebra.single g 1)
  have hcoeff := congrArg (fun w : MonoidAlgebra R G => w.coeff (g * a)) hcomm
  simpa using hcoeff

private theorem coeff_eq_classRep (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G))
    (x : G) : z.coeff x = z.coeff (classRep (ConjClasses.mk x)) := by
  apply coeff_eq_of_isConj R hz
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  simp

theorem central_eq_sum_classSums (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G)) :
    z = ∑ C : ConjClasses G, z.coeff (classRep C) • classSum R C := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, classSum_coeff]
  rw [Finset.sum_eq_single (ConjClasses.mk x)]
  · simp [coeff_eq_classRep R hz x]
  · intro C _ hC
    simp [Ne.symm hC]
  · simp

@[expose] noncomputable def structureConstant (C D E : ConjClasses G) : ℕ :=
  ((classFinset C ×ˢ classFinset D).filter
    (fun p : G × G => p.1 * p.2 = classRep E)).card

private theorem classSum_mul_coeff_classRep (R : Type v) [CommSemiring R]
    (C D E : ConjClasses G) :
    (classSum R C * classSum R D).coeff (classRep E) =
      (structureConstant C D E : R) := by
  classical
  rw [structureConstant]
  simp [classSum, Finset.sum_mul, Finset.mul_sum, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  rw [Finset.natCast_card_filter
    (fun p : G × G => p.1 * p.2 = classRep E)
    (classFinset C ×ˢ classFinset D)]
  rw [Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.natCast_card_filter
    (fun x : G => x * y = classRep E) (classFinset C)

theorem classSum_mul (R : Type v) [CommSemiring R] (C D : ConjClasses G) :
    classSum R C * classSum R D =
      ∑ E : ConjClasses G, (structureConstant C D E : R) • classSum R E := by
  calc
    classSum R C * classSum R D =
        ∑ E : ConjClasses G,
          (classSum R C * classSum R D).coeff (classRep E) • classSum R E :=
      central_eq_sum_classSums R
        ((Submonoid.center (MonoidAlgebra R G)).mul_mem
          (classSum_mem_center R C) (classSum_mem_center R D))
    _ = ∑ E : ConjClasses G,
          (structureConstant C D E : R) • classSum R E := by
      apply Finset.sum_congr rfl
      intro E _
      rw [classSum_mul_coeff_classRep]

section Schur

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [Representation.IsIrreducible ρ]

omit [Fintype G] in
theorem scalarAlgebraMap_bijective :
    Function.Bijective (algebraMap k (ρ.IntertwiningMap ρ)) :=
  Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)

@[expose] noncomputable def centralScalar {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) : k :=
  Classical.choose ((scalarAlgebraMap_bijective ρ).surjective
    (Representation.IntertwiningMap.centralAlgebraMul ρ hz))

private theorem algebraMap_centralScalar {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) :
    algebraMap k (ρ.IntertwiningMap ρ) (centralScalar ρ hz) =
      Representation.IntertwiningMap.centralAlgebraMul ρ hz :=
  Classical.choose_spec ((scalarAlgebraMap_bijective ρ).surjective
    (Representation.IntertwiningMap.centralAlgebraMul ρ hz))

theorem centralScalar_action {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) (v : V) :
    ρ.asAlgebraHom z v = centralScalar ρ hz • v := by
  have h := congrArg (fun f : ρ.IntertwiningMap ρ => f v)
    (algebraMap_centralScalar ρ hz)
  simpa [Representation.IntertwiningMap.algebraMap_apply] using h.symm

theorem centralScalar_unique {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) (a : k)
    (ha : ∀ v : V, ρ.asAlgebraHom z v = a • v) :
    centralScalar ρ hz = a := by
  apply (scalarAlgebraMap_bijective ρ).injective
  rw [algebraMap_centralScalar]
  ext v
  simpa [Representation.IntertwiningMap.algebraMap_apply] using ha v

private theorem centralScalar_mul {z w : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G))
    (hw : w ∈ Submonoid.center (MonoidAlgebra k G)) :
    centralScalar ρ
        ((Submonoid.center (MonoidAlgebra k G)).mul_mem hz hw) =
      centralScalar ρ hz * centralScalar ρ hw := by
  apply centralScalar_unique ρ
  intro v
  simp only [map_mul, Module.End.mul_apply]
  rw [centralScalar_action ρ hw]
  rw [map_smul, centralScalar_action ρ hz, smul_smul]
  simp only [mul_comm]

@[expose] noncomputable def omega (C : ConjClasses G) : k :=
  centralScalar ρ (classSum_mem_center k C)

theorem omega_action (C : ConjClasses G) (v : V) :
    ρ.asAlgebraHom (classSum k C) v = omega ρ C • v :=
  centralScalar_action ρ (classSum_mem_center k C) v

private theorem omega_unique (C : ConjClasses G) (a : k)
    (ha : ∀ v : V, ρ.asAlgebraHom (classSum k C) v = a • v) :
    omega ρ C = a :=
  centralScalar_unique ρ (classSum_mem_center k C) a ha

theorem existsUnique_omega (C : ConjClasses G) :
    ∃! a : k, ∀ v : V, ρ.asAlgebraHom (classSum k C) v = a • v := by
  refine ⟨omega ρ C, omega_action ρ C, ?_⟩
  intro a ha
  exact (omega_unique ρ C a ha).symm

theorem omega_mul (C D : ConjClasses G) :
    centralScalar ρ
        ((Submonoid.center (MonoidAlgebra k G)).mul_mem
          (classSum_mem_center k C) (classSum_mem_center k D)) =
      omega ρ C * omega ρ D :=
  centralScalar_mul ρ (classSum_mem_center k C) (classSum_mem_center k D)

theorem omega_product (C D : ConjClasses G) :
    omega ρ C * omega ρ D =
      ∑ E : ConjClasses G, (structureConstant C D E : k) * omega ρ E := by
  let hp := (Submonoid.center (MonoidAlgebra k G)).mul_mem
    (classSum_mem_center k C) (classSum_mem_center k D)
  calc
    omega ρ C * omega ρ D = centralScalar ρ hp := (omega_mul ρ C D).symm
    _ = ∑ E : ConjClasses G,
          (structureConstant C D E : k) * omega ρ E := by
      apply centralScalar_unique ρ
      intro v
      rw [classSum_mul k C D]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      simp_rw [omega_action ρ]
      simp only [smul_smul, Finset.sum_smul]

omit [IsAlgClosed k] [FiniteDimensional k V] [Representation.IsIrreducible ρ] in
private theorem character_eq_classRep (C : ConjClasses G) {x : G}
    (hx : x ∈ classFinset C) :
    ρ.character x = ρ.character (classRep C) := by
  have hconj : IsConj x (classRep C) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    rw [mem_classFinset.mp hx, mk_classRep]
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  calc
    ρ.character x = ρ.character (g * x * g⁻¹) :=
      (Representation.char_conj ρ x g).symm
    _ = ρ.character (classRep C) := by rw [hg]

private theorem trace_classSum (C : ConjClasses G) :
    LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) =
      (classSize C : k) * ρ.character (classRep C) := by
  calc
    LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) =
        ∑ x ∈ classFinset C, ρ.character x := by
      simp [classSum, Representation.character]
    _ = ∑ _x ∈ classFinset C, ρ.character (classRep C) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact character_eq_classRep ρ C hx
    _ = (classSize C : k) * ρ.character (classRep C) := by
      simp [classSize]

theorem trace_centralScalar {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) :
    LinearMap.trace k V (ρ.asAlgebraHom z) =
      centralScalar ρ hz * (Module.finrank k V : k) := by
  have hmap : ρ.asAlgebraHom z =
      centralScalar ρ hz • (1 : Module.End k V) := by
    ext v
    simp [centralScalar_action ρ hz]
  rw [hmap]
  simp

theorem omega_mul_degree (C : ConjClasses G) :
    omega ρ C * (Module.finrank k V : k) =
      (classSize C : k) * ρ.character (classRep C) := by
  calc
    omega ρ C * (Module.finrank k V : k) =
        LinearMap.trace k V (ρ.asAlgebraHom (classSum k C)) :=
      (trace_centralScalar ρ (classSum_mem_center k C)).symm
    _ = (classSize C : k) * ρ.character (classRep C) := trace_classSum ρ C

theorem omega_eq_classSize_mul_character_div_degree [CharZero k]
    (C : ConjClasses G) :
    omega ρ C =
      (classSize C : k) * ρ.character (classRep C) /
        (Module.finrank k V : k) := by
  let _ : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra k G) ρ.asModule
  have hn : Module.finrank k V ≠ 0 := Nat.ne_of_gt Module.finrank_pos
  have hk : (Module.finrank k V : k) ≠ 0 := by
    exact_mod_cast hn
  apply (eq_div_iff hk).mpr
  exact omega_mul_degree ρ C

end Schur

end

end ZStar.ClassSums

end CFSG
