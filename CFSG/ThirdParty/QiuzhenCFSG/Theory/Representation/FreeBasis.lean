module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.RepresentationTheory.Equiv
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

/-!
# Bases of free representations

This file gives the canonical basis of Representation.free and records that
the basis indices are permuted freely by the represented group.
-/

noncomputable section

namespace CFSG.Theory.Representation

open _root_.Representation

/-- The group acts on the second coordinate of the canonical basis index for a
free representation. -/
@[reducible] public def freeBasisIndexMulAction (G alpha : Type*)
    [Group G] : MulAction G (alpha × G) where
  smul g x := (x.1, g * x.2)
  one_smul x := by
    rcases x with ⟨i, h⟩
    change (i, 1 * h) = (i, h)
    rw [one_mul]
  mul_smul g h x := by
    rcases x with ⟨i, k⟩
    change (i, (g * h) * k) = (i, g * (h * k))
    rw [mul_assoc]

/-- The canonical K-basis of a free representation, indexed by a free
G-set. -/
public noncomputable def freeBasis
    (K G alpha : Type*) [Field K] [Group G] :
    Module.Basis (alpha × G) K (alpha →₀ MonoidAlgebra K G) :=
  (Finsupp.basisSingleOne : Module.Basis (alpha × G) K ((alpha × G) →₀ K)).map
    ((Finsupp.curryLinearEquiv K).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv K).symm))

@[simp]
public theorem freeBasis_apply
    (K G alpha : Type*) [Field K] [Group G] (x : alpha × G) :
    freeBasis K G alpha x =
      Finsupp.single x.1 (MonoidAlgebra.single x.2 (1 : K)) := by
  ext i g
  simp [freeBasis, Finsupp.curryLinearEquiv]

/-- The free representation permutes its canonical basis through left
multiplication on the group coordinate. -/
public theorem free_apply_freeBasis
    (K G alpha : Type*) [Field K] [Group G] (g : G) (x : alpha × G) :
    letI : MulAction G (alpha × G) := freeBasisIndexMulAction G alpha
    free K G alpha g (freeBasis K G alpha x) =
      freeBasis K G alpha (g • x) := by
  let : MulAction G (alpha × G) := freeBasisIndexMulAction G alpha
  rcases x with ⟨i, h⟩
  change Representation.free K G alpha g (freeBasis K G alpha (i, h)) =
    freeBasis K G alpha (i, g * h)
  simp

/-- Explicit pair form of the free-basis action theorem. -/
@[simp]
public theorem free_apply_freeBasis_pair
  (K G alpha : Type*) [Field K] [Group G] (g h : G) (a : alpha) :
    free K G alpha g (freeBasis K G alpha (a, h)) =
      freeBasis K G alpha (a, g * h) := by
  convert free_apply_freeBasis K G alpha g (a, h) using 1 <;> rfl


/-- A representation equivalent to a finite-rank free representation has a
basis permuted freely by the represented group. -/
public theorem exists_freeOrbitBasis_of_repEquiv_free
    {K G V : Type*} {alpha : Type} [Field K] [Group G] [Finite G] [Finite alpha]
    [AddCommGroup V] [Module K V]
    (rho : Representation K G V) (e : rho ≃ₗ Representation.free K G alpha) :
    exists (iota : Type) (instFintype : Fintype iota)
      (instAction : MulAction G iota),
      letI : Fintype iota := instFintype
      letI : MulAction G iota := instAction
      exists b : Module.Basis iota K V,
        (forall g : G, forall i : iota, rho g (b i) = b (g • i)) ∧
          (forall i : iota, Nat.card (MulAction.orbit G i) = Nat.card G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fintype alpha := Fintype.ofFinite alpha
  let : MulAction G (alpha × G) := freeBasisIndexMulAction G alpha
  let q : (alpha × G) ≃ Fin (Fintype.card (alpha × G)) :=
    Fintype.equivFin (alpha × G)
  let smallAction : MulAction G (Fin (Fintype.card (alpha × G))) := {
    smul g i := q (g • q.symm i)
    one_smul i := by
      change q (1 • q.symm i) = i
      simp
    mul_smul g h i := by
      change q ((g * h) • q.symm i) = q (g • q.symm (q (h • q.symm i)))
      simp [q.symm_apply_apply, mul_smul] }
  refine ⟨Fin (Fintype.card (alpha × G)), inferInstance, smallAction, ?_⟩
  let : MulAction G (Fin (Fintype.card (alpha × G))) := smallAction
  let b : Module.Basis (Fin (Fintype.card (alpha × G))) K V :=
    ((freeBasis K G alpha).reindex q).map e.toLinearEquiv.symm
  refine ⟨b, ?_, ?_⟩
  · intro g i
    simp only [b, Module.Basis.map_apply, Module.Basis.reindex_apply]
    change rho g (e.symm (freeBasis K G alpha (q.symm i))) =
      e.symm (freeBasis K G alpha (q.symm (g • i)))
    change rho g (e.symm (freeBasis K G alpha (q.symm i))) =
      e.symm (freeBasis K G alpha (q.symm (q (g • q.symm i))))
    simp only [q.symm_apply_apply]
    rw [← free_apply_freeBasis]
    exact (e.symm.isIntertwining g (freeBasis K G alpha (q.symm i))).symm
  · intro i
    let : Finite (MulAction.orbit G i) := by
      simpa [Set.finite_coe_iff] using
        (Finite.finite_mulAction_orbit (M := G) i)
    let : Fintype (MulAction.orbit G i) := Fintype.ofFinite _
    let : Fintype (MulAction.stabilizer G i) := Fintype.ofFinite _
    have hstabilizer : MulAction.stabilizer G i = ⊥ := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_bot]
      change q (g • q.symm i) = i ↔ g = 1
      constructor
      · intro hg
        let x : alpha × G := q.symm i
        have hx : g • x = x := by
          apply q.injective
          dsimp only [x]
          simpa using hg
        rcases x with ⟨j, h⟩
        change (j, g * h) = (j, h) at hx
        apply mul_right_cancel (b := h)
        simpa using congrArg Prod.snd hx
      · intro hg
        subst g
        simp
    have horbit :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group G i
    simpa [Nat.card_eq_fintype_card, hstabilizer] using horbit
end CFSG.Theory.Representation


