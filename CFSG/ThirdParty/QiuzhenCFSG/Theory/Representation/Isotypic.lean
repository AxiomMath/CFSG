module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.Length
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.RepEquiv

namespace CFSG
end CFSG
open CFSG

/-!
# The isotypic (homogeneous) component

The homogeneous component `M(V)` (Isaacs, *Character Theory of Finite Groups*,
Definition 1.12): the sum of all submodules of `V` isomorphic to `M`; and
(Isaacs Lemma 1.13) its invariance under endomorphisms, its description as the
sum of the summands isomorphic to `M` in a direct-sum decomposition into
irreducible submodules, and the independence of the multiplicity of the
isomorphism class from the chosen decomposition.
-/

noncomputable section

open scoped DirectSum
namespace CFSG.Theory.Representation

open _root_.Representation


/-- Isaacs, Definition 1.12: the `M`-homogeneous part of `V`. -/
@[expose] public def homogeneousComponent
    (A V M : Type*) [Semiring A]
    [AddCommMonoid V] [Module A V]
    [AddCommMonoid M] [Module A M] : Submodule A V :=
  sSup {W : Submodule A V | Nonempty (W ≃ₗ[A] M)}


private theorem simple_submodule_le_selected
    {A V M : Type*} [Ring A]
    [AddCommGroup V] [Module A V]
    [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι -> Submodule A V)
    (hW_internal : DirectSum.IsInternal W)
    (hW_irreducible : forall i : ι, IsSimpleModule A (W i))
    (S : Submodule A V) [IsSimpleModule A S]
    (hSM : Nonempty (S ≃ₗ[A] M)) :
    S <= iSup (fun i : Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M)) => W i.1) := by
  classical
  let selected : Submodule A V :=
    iSup (fun i : Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M)) => W i.1)
  let e := LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW_internal
  have hsum : forall x : V, x = ∑ i : ι, ((e.symm x i : W i) : V) := by
    intro x
    calc
      x = DirectSum.coeLinearMap W (e.symm x) := by
        change x = e (e.symm x)
        exact (e.apply_symm_apply x).symm
      _ = ∑ i : ι, ((e.symm x i : W i) : V) := by
        change DFinsupp.sumAddHom (fun i => (W i).subtype.toAddMonoidHom) (e.symm x) = _
        rw [DFinsupp.sumAddHom_apply]
        rw [DFinsupp.sum_eq_sum_fintype]
        · simp
        · intro i
          rfl
  intro x hx
  rw [hsum x]
  refine Submodule.sum_mem selected ?_
  intro i _
  by_cases hi : Nonempty ((W i) ≃ₗ[A] M)
  · exact (le_iSup (fun j : Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M)) => W j.1)
      ⟨i, hi⟩) (e.symm x i).2
  · have : IsSimpleModule A (W i) := hW_irreducible i
    let coord : S →ₗ[A] W i :=
      (DirectSum.component A ι (fun i => W i) i) ∘ₗ e.symm.toLinearMap ∘ₗ S.subtype
    have hcoord_zero : coord = 0 := by
      by_contra hcoord_ne
      have hbij : Function.Bijective coord := LinearMap.bijective_of_ne_zero hcoord_ne
      let isoSW : S ≃ₗ[A] W i := LinearEquiv.ofBijective coord hbij
      exact hi ⟨isoSW.symm.trans hSM.some⟩
    have hcoord_apply : coord ⟨x, hx⟩ = e.symm x i := rfl
    have hzero : e.symm x i = 0 := by
      simpa [hcoord_apply] using congrArg (fun f : S →ₗ[A] W i => f ⟨x, hx⟩) hcoord_zero
    simp [hzero]

private theorem homogeneousComponent_eq_selected_sum
    {A V M : Type*} [Ring A]
    [AddCommGroup V] [Module A V]
    [AddCommGroup M] [Module A M]
    (hM : IsSimpleModule A M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι -> Submodule A V)
    (hW_internal : DirectSum.IsInternal W)
    (hW_irreducible : forall i : ι, IsSimpleModule A (W i)) :
    homogeneousComponent A V M =
      iSup (fun i : Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M)) => W i.1) := by
  have : IsSimpleModule A M := hM
  apply le_antisymm
  · rw [homogeneousComponent]
    refine sSup_le ?_
    intro S hS
    have : IsSimpleModule A S := IsSimpleModule.congr hS.some
    exact simple_submodule_le_selected W hW_internal hW_irreducible S hS
  · refine iSup_le ?_
    intro i
    rw [homogeneousComponent]
    exact le_sSup i.2

private theorem selected_length_eq_card
    {A V M : Type*} [Ring A]
    [AddCommGroup V] [Module A V]
    [AddCommGroup M] [Module A M]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι -> Submodule A V)
    (hW_internal : DirectSum.IsInternal W)
    (hW_irreducible : forall i : ι, IsSimpleModule A (W i)) :
    Module.length A
        ((iSup (fun i : Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M)) => W i.1) :
          Submodule A V)) =
      (Nat.card (Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M))) : ENat) := by
  classical
  let p : ι -> Prop := fun i => Nonempty ((W i) ≃ₗ[A] M)
  let J := {i : ι // p i}
  let selected : Submodule A V := ⨆ i, ⨆ (_ : p i), W i
  have hselected_eq : selected = iSup (fun i : J => W i.1) := by
    simp [selected, J, p, iSup_subtype']
  let Wsel : J -> Submodule A selected := fun i => (W i.1).comap selected.subtype
  have hle (i : J) : W i.1 <= selected := by
    change W i.1 <= (⨆ j, ⨆ (_ : p j), W j)
    exact le_iSup₂ (f := fun j (_ : p j) => W j) i.1 i.2
  have hWsel_equiv (i : J) : Wsel i ≃ₗ[A] W i.1 :=
    (W i.1).comapSubtypeEquivOfLe (hle i)
  have hWsel_simple (i : J) : IsSimpleModule A (Wsel i) := by
    exact IsSimpleModule.congr (hWsel_equiv i)
  have hWsel_internal : DirectSum.IsInternal Wsel := by
    change DirectSum.IsInternal (fun i : J => (W i.1).comap selected.subtype)
    exact DirectSum.isInternal_biSup_submodule_of_iSupIndep
      (A := W) ({i : ι | p i})
      (hW_internal.submodule_iSupIndep.comp Subtype.val_injective)
  let e : (⨁ i : J, Wsel i) ≃ₗ[A] selected :=
    LinearEquiv.ofBijective (DirectSum.coeLinearMap Wsel) hWsel_internal
  rw [← hselected_eq]
  calc
    Module.length A selected = Module.length A (⨁ i : J, Wsel i) := by
      exact e.symm.length_eq
    _ = Module.length A (∀ i : J, (Wsel i : Type _)) := by
      exact (DirectSum.linearEquivFunOnFintype A J (fun i : J => (Wsel i : Type _))).length_eq
    _ = ∑ i : J, Module.length A (Wsel i) := by
      exact Module.length_pi_of_fintype A (fun i : J => (Wsel i : Type _))
    _ = ∑ _i : J, (1 : ENat) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have : IsSimpleModule A (Wsel i) := hWsel_simple i
      simp
    _ = (Nat.card J : ENat) := by
      simp [J, Nat.card_eq_fintype_card]

/-- Isaacs, Character Theory of Finite Groups, Lemma 1.13. -/
public theorem isaacs_lemma_1_13
    {A V M : Type*} [Ring A]
    [AddCommGroup V] [Module A V]
    [AddCommGroup M] [Module A M]
    (hM : IsSimpleModule A M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι -> Submodule A V)
    (hW_internal : DirectSum.IsInternal W)
    (hW_irreducible : forall i : ι, IsSimpleModule A (W i)) :
    (forall f : Module.End A V,
        Submodule.map f (homogeneousComponent A V M) <= homogeneousComponent A V M) ∧
      homogeneousComponent A V M =
        iSup (fun i : {i : ι // Nonempty ((W i) ≃ₗ[A] M)} => W i.1) ∧
      (forall {κ : Type*} [Fintype κ] [DecidableEq κ] (U : κ -> Submodule A V),
        DirectSum.IsInternal U ->
          (forall k : κ, IsSimpleModule A (U k)) ->
            Nat.card {i : ι // Nonempty ((W i) ≃ₗ[A] M)} =
              Nat.card {k : κ // Nonempty ((U k) ≃ₗ[A] M)}) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro f
    exact Submodule.map_le_iff_le_comap.mpr (by
      simpa [homogeneousComponent, isotypicComponent] using
        (LinearMap.le_comap_isotypicComponent (R := A) (M := V) (N := V) (S := M) (f := f)))
  · exact homogeneousComponent_eq_selected_sum hM W hW_internal hW_irreducible
  · intro κ _hκ _hκdec U hU_internal hU_irreducible
    let JW := Subtype (fun i : ι => Nonempty ((W i) ≃ₗ[A] M))
    let JU := Subtype (fun k : κ => Nonempty ((U k) ≃ₗ[A] M))
    have hWlen := selected_length_eq_card (M := M) W hW_internal hW_irreducible
    have hUlen := selected_length_eq_card (M := M) U hU_internal hU_irreducible
    have hWeq := homogeneousComponent_eq_selected_sum (M := M) hM W hW_internal hW_irreducible
    have hUeq := homogeneousComponent_eq_selected_sum (M := M) hM U hU_internal hU_irreducible
    have hWcard : (Nat.card JW : ENat) = Module.length A (homogeneousComponent A V M) := by
      rw [← hWlen, hWeq]
    have hUcard : (Nat.card JU : ENat) = Module.length A (homogeneousComponent A V M) := by
      rw [← hUlen, hUeq]
    apply ENat.natCast_inj.mp
    change (Nat.card JW : ENat) = (Nat.card JU : ENat)
    exact hWcard.trans hUcard.symm

end CFSG.Theory.Representation
