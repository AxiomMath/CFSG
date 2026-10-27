module

public import CFSG.LocalAnalysis.ZStar.PadicTrace
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG

namespace ZStar.OddFourierProjectors

noncomputable section

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
  [CommRing R] [Group G] [AddCommGroup V] [Module R V]

@[expose] def scalarTwist (rho : Representation R G V) (chi : G →* R) :
    Representation R G V where
  toFun g := chi g • rho g
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp only [map_mul]
    change (chi g * chi h) • rho g (rho h x) =
      chi g • rho g (chi h • rho h x)
    rw [map_smul, smul_smul]

@[simp]
theorem scalarTwist_apply (rho : Representation R G V) (chi : G →* R)
    (g : G) (x : V) :
    scalarTwist rho chi g x = chi g • rho g x :=
  rfl

section Cyclic

variable {m : ℕ} [NeZero m]

abbrev NonzeroFourierSector (m : ℕ) := {s : ZMod m // s ≠ 0}

@[expose] def fourierCharacter (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    AddChar (ZMod m) R :=
  (AddChar.zmodChar m hz).mulShift (-s)

@[simp]
theorem fourierCharacter_apply (z : R) (hz : z ^ m = 1)
    (s a : ZMod m) :
    fourierCharacter z hz s a = z ^ ((-s * a).val) := by
  rw [fourierCharacter, AddChar.mulShift_apply, AddChar.zmodChar_apply]

@[expose] def fourierTwist
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    Representation R (Multiplicative (ZMod m)) V :=
  scalarTwist rho (fourierCharacter z hz s).toMonoidHom

@[simp]
theorem fourierTwist_apply
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s a : ZMod m) (x : V) :
    fourierTwist rho z hz s (Multiplicative.ofAdd a) x =
      fourierCharacter z hz s a • rho (Multiplicative.ofAdd a) x :=
  rfl

@[expose, instance_reducible]
noncomputable def cyclicCardInvertible [Invertible (m : R)] :
    Invertible
      (Fintype.card (Multiplicative (ZMod m)) : R) :=
  Invertible.copy (inferInstance : Invertible (m : R)) _ (by
    rw [Fintype.card_multiplicative, ZMod.card])

def fourierProjector [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) : Module.End R V := by
  letI := cyclicCardInvertible (R := R) (m := m)
  exact (fourierTwist rho z hz s).averageMap

private theorem fourierProjector_eq_sum [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    fourierProjector rho z hz s =
      ⅟(m : R) • ∑ a : Multiplicative (ZMod m),
        fourierCharacter z hz s a.toAdd • rho a := by
  let := cyclicCardInvertible (R := R) (m := m)
  have hcard :
      (Fintype.card (Multiplicative (ZMod m)) : R) = (m : R) := by
    rw [Fintype.card_multiplicative, ZMod.card]
  have hinv :
      ⅟(Fintype.card (Multiplicative (ZMod m)) : R) = ⅟(m : R) :=
    invertible_unique _ _ hcard
  rw [fourierProjector, Representation.averageMap, GroupAlgebra.average,
    map_smul, map_sum, hinv]
  apply congrArg (⅟(m : R) • ·)
  apply Finset.sum_congr rfl
  intro a _
  rw [MonoidAlgebra.of_apply,
    Representation.asAlgebraHom_single_one]
  rfl

private theorem fourierProjector_idempotent [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    fourierProjector rho z hz s * fourierProjector rho z hz s =
      fourierProjector rho z hz s := by
  let := cyclicCardInvertible (R := R) (m := m)
  exact (fourierTwist rho z hz s).isProj_averageMap.isIdempotentElem.eq

private theorem sum_fourierCharacter [IsDomain R]
    (z : R) (hz : IsPrimitiveRoot z m) (a : ZMod m) :
    (∑ s : ZMod m, fourierCharacter z hz.pow_eq_one s a) =
      if a = 0 then (m : R) else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [fourierCharacter, ZMod.card]
  · rw [ite_eq_right ha]
    let psi : AddChar (ZMod m) R := AddChar.zmodChar m hz.pow_eq_one
    have hpsi : psi.IsPrimitive :=
      AddChar.zmodChar_primitive_of_primitive_root m hz
    have hne : psi.mulShift (-a) ≠ 1 := by
      intro heq
      have hone : psi (-a) = 1 := by
        have happ := congrArg (fun q : AddChar (ZMod m) R ↦ q 1) heq
        simpa [AddChar.mulShift_apply] using happ
      have hnega : -a = 0 :=
        (hpsi.zmod_char_eq_one_iff m (-a)).mp hone
      exact ha (neg_eq_zero.mp hnega)
    have hsum := AddChar.sum_eq_zero_of_ne_one hne
    simpa [fourierCharacter, psi, AddChar.mulShift_apply, mul_comm]
      using hsum

private theorem sum_fourierProjector [IsDomain R] [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : IsPrimitiveRoot z m) :
    (∑ s : ZMod m, fourierProjector rho z hz.pow_eq_one s) = 1 := by
  classical
  simp_rw [fourierProjector_eq_sum]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_fourierCharacter z hz]
  simp

private theorem fourierProjector_generator_relation [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    fourierCharacter z hz s 1 •
        (rho (Multiplicative.ofAdd 1) * fourierProjector rho z hz s) =
      fourierProjector rho z hz s := by
  let := cyclicCardInvertible (R := R) (m := m)
  apply LinearMap.ext
  intro x
  change fourierCharacter z hz s 1 •
      rho (Multiplicative.ofAdd 1)
        ((fourierTwist rho z hz s).averageMap x) =
    (fourierTwist rho z hz s).averageMap x
  exact (Representation.mem_invariants _ _).mp
    ((fourierTwist rho z hz s).averageMap_invariant x)
    (Multiplicative.ofAdd 1)

theorem generator_mul_fourierProjector [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    rho (Multiplicative.ofAdd 1) * fourierProjector rho z hz s =
      z ^ s.val • fourierProjector rho z hz s := by
  let lambda := AddChar.zmodChar m hz s
  have hlambda : lambda = z ^ s.val := by
    simp [lambda, AddChar.zmodChar_apply]
  have hunit :
      lambda * fourierCharacter z hz s 1 = 1 := by
    rw [fourierCharacter, AddChar.mulShift_apply]
    change (AddChar.zmodChar m hz) s *
      (AddChar.zmodChar m hz) (-s * 1) = 1
    rw [mul_one, ← (AddChar.zmodChar m hz).map_add_eq_mul,
      add_neg_cancel, AddChar.map_zero_eq_one]
  have hsector := fourierProjector_generator_relation rho z hz s
  calc
    rho (Multiplicative.ofAdd 1) * fourierProjector rho z hz s =
        (1 : R) • (rho (Multiplicative.ofAdd 1) *
          fourierProjector rho z hz s) := by simp
    _ = (lambda * fourierCharacter z hz s 1) •
        (rho (Multiplicative.ofAdd 1) *
          fourierProjector rho z hz s) := by rw [hunit]
    _ = lambda • (fourierCharacter z hz s 1 •
        (rho (Multiplicative.ofAdd 1) *
          fourierProjector rho z hz s)) := by rw [mul_smul]
    _ = lambda • fourierProjector rho z hz s := by rw [hsector]
    _ = z ^ s.val • fourierProjector rho z hz s := by rw [hlambda]

private theorem commute_fourierProjector [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m)
    (T : Module.End R V) (hT : ∀ a, Commute T (rho a)) :
    Commute T (fourierProjector rho z hz s) := by
  rw [fourierProjector_eq_sum]
  exact (Commute.sum_right Finset.univ _ T (fun a _ ↦
    (hT a).smul_right (fourierCharacter z hz s a.toAdd))).smul_right _

private theorem generator_sub_one_eq_sum [IsDomain R] [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : IsPrimitiveRoot z m) :
    rho (Multiplicative.ofAdd 1) - 1 =
      ∑ s : ZMod m, (z ^ s.val - 1) •
        fourierProjector rho z hz.pow_eq_one s := by
  classical
  calc
    rho (Multiplicative.ofAdd 1) - 1 =
        (rho (Multiplicative.ofAdd 1) - 1) * 1 := by rw [mul_one]
    _ = (rho (Multiplicative.ofAdd 1) - 1) *
        (∑ s : ZMod m, fourierProjector rho z hz.pow_eq_one s) := by
      rw [sum_fourierProjector rho z hz]
    _ = ∑ s : ZMod m, (rho (Multiplicative.ofAdd 1) - 1) *
        fourierProjector rho z hz.pow_eq_one s := by rw [Finset.mul_sum]
    _ = ∑ s : ZMod m, (z ^ s.val - 1) •
        fourierProjector rho z hz.pow_eq_one s := by
      apply Finset.sum_congr rfl
      intro s _
      rw [sub_mul, one_mul,
        generator_mul_fourierProjector rho z hz.pow_eq_one s,
        sub_smul, one_smul]

private theorem generator_sub_one_eq_sum_nonzero
    [IsDomain R] [Invertible (m : R)]
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : IsPrimitiveRoot z m) :
    rho (Multiplicative.ofAdd 1) - 1 =
      ∑ s : NonzeroFourierSector m, (z ^ s.1.val - 1) •
        fourierProjector rho z hz.pow_eq_one s.1 := by
  classical
  let f : ZMod m → Module.End R V := fun s ↦
    (z ^ s.val - 1) • fourierProjector rho z hz.pow_eq_one s
  have hsubset :
      (Finset.univ.filter fun s : ZMod m ↦ s ≠ 0) ⊆ Finset.univ :=
    Finset.filter_subset _ _
  have hzero :
      ∀ s ∈ (Finset.univ : Finset (ZMod m)),
        s ∉ Finset.univ.filter (fun t : ZMod m ↦ t ≠ 0) → f s = 0 := by
    intro s _ hs
    have hs0 : s = 0 := by simpa using hs
    subst s
    simp [f]
  have hall :
      (∑ s ∈ (Finset.univ.filter fun s : ZMod m ↦ s ≠ 0), f s) =
        ∑ s : ZMod m, f s :=
    Finset.sum_subset hsubset hzero
  have hsubtype :
      (∑ s ∈ (Finset.univ.filter fun s : ZMod m ↦ s ≠ 0), f s) =
        ∑ s : NonzeroFourierSector m, f s.1 :=
    Finset.sum_subtype _ (by simp) f
  calc
    rho (Multiplicative.ofAdd 1) - 1 = ∑ s : ZMod m, f s := by
      simpa only [f] using generator_sub_one_eq_sum rho z hz
    _ = ∑ s ∈ (Finset.univ.filter fun s : ZMod m ↦ s ≠ 0), f s :=
      hall.symm
    _ = ∑ s : NonzeroFourierSector m, f s.1 := hsubtype
    _ = ∑ s : NonzeroFourierSector m, (z ^ s.1.val - 1) •
        fourierProjector rho z hz.pow_eq_one s.1 := by rfl

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

@[expose] def fourierProjectorMatrix [Invertible (m : R)]
    (b : Module.Basis n R V)
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) : Matrix n n R :=
  LinearMap.toMatrix b b (fourierProjector rho z hz s)

theorem fourierProjectorMatrix_idempotent [Invertible (m : R)]
    (b : Module.Basis n R V)
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m) :
    fourierProjectorMatrix b rho z hz s *
        fourierProjectorMatrix b rho z hz s =
      fourierProjectorMatrix b rho z hz s := by
  rw [fourierProjectorMatrix, ← LinearMap.toMatrix_mul,
    fourierProjector_idempotent]

theorem fourierProjectorMatrix_commute [Invertible (m : R)]
    (b : Module.Basis n R V)
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : z ^ m = 1) (s : ZMod m)
    (T : Module.End R V) (hT : ∀ a, Commute T (rho a)) :
    fourierProjectorMatrix b rho z hz s * LinearMap.toMatrix b b T =
      LinearMap.toMatrix b b T * fourierProjectorMatrix b rho z hz s := by
  have h := (commute_fourierProjector rho z hz s T hT).eq.symm
  simpa only [fourierProjectorMatrix, LinearMap.toMatrix_mul] using
    congrArg (LinearMap.toMatrix b b) h

theorem generatorMatrix_sub_one_eq_sum_nonzero
    [IsDomain R] [Invertible (m : R)]
    (b : Module.Basis n R V)
    (rho : Representation R (Multiplicative (ZMod m)) V)
    (z : R) (hz : IsPrimitiveRoot z m) :
    LinearMap.toMatrix b b (rho (Multiplicative.ofAdd 1)) - 1 =
      ∑ s : NonzeroFourierSector m, (z ^ s.1.val - 1) •
        fourierProjectorMatrix b rho z hz.pow_eq_one s.1 := by
  have h := congrArg (LinearMap.toMatrix b b)
    (generator_sub_one_eq_sum_nonzero rho z hz)
  simpa only [map_sub, LinearMap.toMatrix_one, map_sum, map_smul,
    fourierProjectorMatrix] using h

end Matrix

end Cyclic

end

end ZStar.OddFourierProjectors

end CFSG
