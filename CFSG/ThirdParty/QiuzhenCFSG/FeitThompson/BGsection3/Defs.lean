module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.lemma_1_22
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.CyclicQuotientExtension
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SolvableDimension
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.PrimitiveRootEigenspaces
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtraspecialFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.CoprimeHall
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.CentralizerControl
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Faithful
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.CompleteReducibility
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.kerRepresentation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

namespace CFSG
end CFSG
open CFSG

open scoped FixedPoints TensorProduct Pointwise

/-! # Statements from BG Section 3 -/

namespace Subgroup

/-- The conjugate of a subgroup by an element. -/
@[expose] public def conjBy {G : Type*} [Group G] (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

end Subgroup

/-- The centralizer of a subgroup `S` inside a subgroup `H`. -/
@[expose] public def CFSG.subgroupCentralizerIn {G : Type*} [Group G] (H S : Subgroup G) : Subgroup G :=
  H ⊓ Subgroup.centralizer (S : Set G)

/-- The centralizer of an element `x` inside a subgroup `H`. -/
@[expose] public def CFSG.elementCentralizerIn {G : Type*} [Group G] (H : Subgroup G) (x : G) : Subgroup G :=
  H ⊓ Subgroup.centralizer ({x} : Set G)

namespace Representation

/-- The fixed-point subspace of a subgroup under a representation. -/
@[expose] public noncomputable def fixedSubspace {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (H : Subgroup G) : Submodule F V :=
  Representation.invariants (ρ.comp H.subtype)

/-- The subgroup of `H` acting trivially under a representation. -/
@[expose] public def centralizerIn {F G V : Type*} [Field F] [Group G] [AddCommGroup V]
    [Module F V]
    (ρ : Representation F G V) (H : Subgroup G) : Subgroup G :=
  H ⊓ ρ.ker

end Representation

/-- The subgroup of `H` fixing every element of the acted-on group. -/
@[expose] public def CFSG.actionCentralizerIn {A G : Type*} [Group A] [Group G] [MulAction A G]
    (H : Subgroup A) : Subgroup A := by
  let _ := (inferInstance : Group G)
  exact H ⊓ fixingSubgroupOf A G Set.univ

/-- A Frobenius group with kernel `K` and complement `R`. -/
@[expose] public def CFSG.IsFrobeniusGroupWithKernelComplement {G : Type*} [Group G]
    (K R : Subgroup G) : Prop :=
  K.Normal ∧ K.IsComplement' R ∧
    (∀ g : G, g ∉ R → Disjoint R (R.conjBy g)) ∧
      K ≠ ⊥ ∧ R ≠ ⊥

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.normal {G : Type*} [Group G]
    {K R : Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    K.Normal :=
  hfrob.1

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.isComplement' {G : Type*} [Group G]
    {K R : Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    K.IsComplement' R :=
  hfrob.2.1

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.disjoint_conjBy {G : Type*} [Group G]
    {K R : Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    ∀ g : G, g ∉ R → Disjoint R (R.conjBy g) :=
  hfrob.2.2.1

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.kernel_ne_bot {G : Type*} [Group G]
    {K R : Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    K ≠ ⊥ :=
  hfrob.2.2.2.1

public theorem CFSG.IsFrobeniusGroupWithKernelComplement.complement_ne_bot {G : Type*} [Group G]
    {K R : Subgroup G} (hfrob : IsFrobeniusGroupWithKernelComplement K R) :
    R ≠ ⊥ :=
  hfrob.2.2.2.2


/-- Transport a Frobenius kernel/complement decomposition across a group
equivalence. -/
public theorem CFSG.IsFrobeniusGroupWithKernelComplement.map_mulEquiv
    {A B : Type*} [Group A] [Group B]
    {K R : Subgroup A}
    (hFrob : IsFrobeniusGroupWithKernelComplement K R)
    (e : A ≃* B) :
    IsFrobeniusGroupWithKernelComplement
      (K.map e.toMonoidHom) (R.map e.toMonoidHom) := by
  rcases hFrob with ⟨hKnorm, hComp, hDisj, hKne, hRne⟩
  have hKmap_ne : K.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hKne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := e.toMonoidHom) e.injective).1 hbot)
  have hRmap_ne : R.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    exact hRne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := R) (f := e.toMonoidHom) e.injective).1 hbot)
  have hKmap_norm : (K.map e.toMonoidHom).Normal :=
    hKnorm.map e.toMonoidHom e.surjective
  have hCompMap :
      (K.map e.toMonoidHom).IsComplement' (R.map e.toMonoidHom) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxK hxR
      rcases Subgroup.mem_map.mp hxK with ⟨k, hkK, hkx⟩
      rcases Subgroup.mem_map.mp hxR with ⟨r, hrR, hrx⟩
      have hkr : k = r := e.injective (hkx.trans hrx.symm)
      have hkbot : k ∈ (⊥ : Subgroup A) :=
        hComp.disjoint.le_bot ⟨hkK, by simpa [hkr] using hrR⟩
      have hxone : x = 1 := by
        rw [← hkx]
        simpa using congrArg e hkbot
      simp [hxone]
    · rw [Set.eq_univ_iff_forall]
      intro b
      let a : A := e.symm b
      rcases hComp.2 a with ⟨kr, hkr⟩
      rcases kr with ⟨k, r⟩
      rcases k with ⟨k, hkK⟩
      rcases r with ⟨r, hrR⟩
      refine ⟨e k, Subgroup.mem_map.mpr ⟨k, hkK, rfl⟩,
        e r, Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩, ?_⟩
      calc
        e k * e r = e (k * r) := (e.map_mul k r).symm
        _ = e a := by
          have hkrA : k * r = a := by simpa using hkr
          rw [hkrA]
        _ = b := e.apply_symm_apply b
  have hDisjMap :
      ∀ b : B, b ∉ R.map e.toMonoidHom →
        Disjoint (R.map e.toMonoidHom)
          ((R.map e.toMonoidHom).conjBy b) := by
    intro b hb
    let a : A := e.symm b
    have ha : a ∉ R := by
      intro haR
      apply hb
      exact Subgroup.mem_map.mpr ⟨a, haR, e.apply_symm_apply b⟩
    rw [Subgroup.disjoint_def]
    intro x hxR hxConj
    rcases Subgroup.mem_map.mp hxR with ⟨r, hrR, hrx⟩
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxConj
    rcases hxConj with ⟨y, hyR, hyx⟩
    rcases Subgroup.mem_map.mp hyR with ⟨s, hsR, hsy⟩
    have hrs : r = a * s * a⁻¹ := by
      apply e.injective
      calc
        e r = x := hrx
        _ = b * y * b⁻¹ := by
          simpa [MulAut.conj_apply] using hyx.symm
        _ = e a * e s * (e a)⁻¹ := by
          have hmapped :=
            congrArg (fun z : B => b * z * b⁻¹) hsy.symm
          simpa only [a, e.apply_symm_apply, MulEquiv.coe_toMonoidHom] using hmapped
        _ = e (a * s * a⁻¹) := by simp
    have hrConj : r ∈ R.conjBy a := by
      rw [Subgroup.conjBy, Subgroup.mem_map]
      exact ⟨s, hsR, by simpa [MulAut.conj_apply] using hrs.symm⟩
    have hrBot : r ∈ (⊥ : Subgroup A) :=
      (Subgroup.disjoint_def.mp (hDisj a ha)) hrR hrConj
    have hrOne : r = 1 := by simpa using hrBot
    have hxOne : x = 1 := by
      rw [← hrx, hrOne]
      simp
    simp [hxOne]
  exact ⟨hKmap_norm, hCompMap, hDisjMap, hKmap_ne, hRmap_ne⟩

/-- An action is regular if every nonidentity actor has trivial fixed-point subgroup. -/
@[expose] public def CFSG.ActsRegularly (A G : Type*) [Group A] [Group G]
    [MulDistribMulAction A G] : Prop :=
  ∀ a : A, a ≠ 1 → fixedPointSubgroup (↥(Subgroup.zpowers a)) G = ⊥
