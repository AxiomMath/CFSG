module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.problem_7_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.XV.lemma_15_15
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.FreeOrbitQuotient
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.FreeBasis
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.PermutationBasisOrbits
public import Mathlib.FieldTheory.AlgebraicClosure

namespace CFSG
end CFSG
open CFSG

open scoped TensorProduct

/-!
# Isaacs Theorem 15.16

A source-faithful statement of Isaacs, *Character Theory of Finite Groups*,
Theorem 15.16. The theorem is stated directly in terms of a Frobenius kernel
`N`, a Frobenius complement `H`, a `K[G]`-module represented by `rho`, the
fixed-space condition `C_V(N)=0`, an `H`-permuted basis, and the fixed-space
formula for subgroups of `H`.
-/

noncomputable section

namespace CFSG.BenderSuzuki
namespace External
namespace Isaacs
namespace XV

attribute [local instance] Representation.instModuleAsModule
  Representation.instModuleMonoidAlgebraAsModule

private theorem isaacs_15_16_fixedSpace_of_freePermutationBasis
    {G K V iota : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V] [Finite iota]
    (rho : Representation K G V) [MulAction G iota] [IsCancelSMul G iota]
    (b : Module.Basis iota K V)
    (hb : forall g : G, forall i : iota, rho g (b i) = b (g • i)) :
    forall H0 : Subgroup G,
      Module.finrank K (Representation.fixedSubspace rho H0) =
        H0.index * Module.finrank K rho.invariants := by
  intro H0
  have hb0 :
      forall h : H0, forall i : iota,
        (rho.comp H0.subtype) h (b i) = b (h • i) := by
    intro h i
    simpa [MulAction.subgroup_smul_def] using hb (h : G) i
  calc
    Module.finrank K (Representation.fixedSubspace rho H0) =
        Module.finrank K (Representation.invariants (rho.comp H0.subtype : Representation K H0 V)) := rfl
    _ = Nat.card (MulAction.orbitRel.Quotient H0 iota) :=
      Theory.Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
        (rho.comp H0.subtype) b hb0
    _ = H0.index * Nat.card (MulAction.orbitRel.Quotient G iota) :=
      MulAction.natCard_orbitRelQuotient_subgroup H0
    _ = H0.index * Module.finrank K rho.invariants := by
      rw [Theory.Representation.permutedBasis_fixedSubspace_finrank_eq_orbitQuotient_card
        rho b hb]
private theorem isaacs_15_16_of_repEquiv_free
    {G K V : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V]
    (rho : Representation K G V) {alpha : Type} [Finite alpha]
    (e : rho ≃ₗ Representation.free K G alpha) :
    (exists (iota : Type) (instFintype : Fintype iota)
        (instAction : MulAction G iota),
      letI : Fintype iota := instFintype
      letI : MulAction G iota := instAction
      exists b : Module.Basis iota K V,
        (forall g : G, forall i : iota, rho g (b i) = b (g • i)) ∧
          (forall i : iota, Nat.card (MulAction.orbit G i) = Nat.card G)) ∧
      (forall H0 : Subgroup G,
        Module.finrank K (Representation.fixedSubspace rho H0) =
          H0.index * Module.finrank K rho.invariants) := by
  constructor
  · exact Theory.Representation.exists_freeOrbitBasis_of_repEquiv_free rho e
  · letI : Fintype G := Fintype.ofFinite G
    letI : Fintype alpha := Fintype.ofFinite alpha
    letI : MulAction G (alpha × G) := {
      smul g x := (x.1, g * x.2)
      one_smul x := by
        rcases x with ⟨i, k⟩
        change (i, 1 * k) = (i, k)
        rw [one_mul]
      mul_smul g h x := by
        rcases x with ⟨i, k⟩
        change (i, (g * h) * k) = (i, g * (h * k))
        rw [mul_assoc] }
    letI : IsCancelSMul G (alpha × G) := {
      toIsLeftCancelSMul := inferInstance
      right_cancel' g h x eq := by
        rcases x with ⟨i, k⟩
        change (i, g * k) = (i, h * k) at eq
        exact mul_right_cancel (congrArg Prod.snd eq) }
    let b : Module.Basis (alpha × G) K V :=
      (Theory.Representation.freeBasis K G alpha).map e.toLinearEquiv.symm
    have hb :
        forall g : G, forall i : alpha × G,
          rho g (b i) = b (g • i) := by
      intro g i
      have hfree :
          Representation.free K G alpha g (Theory.Representation.freeBasis K G alpha i) =
            Theory.Representation.freeBasis K G alpha (g • i) := by
        rcases i with ⟨j, k⟩
        change Representation.free K G alpha g
            (Theory.Representation.freeBasis K G alpha (j, k)) =
          Theory.Representation.freeBasis K G alpha (j, g * k)
        simp
      change rho g (e.symm (Theory.Representation.freeBasis K G alpha i)) =
        e.symm (Theory.Representation.freeBasis K G alpha (g • i))
      rw [← hfree]
      exact (e.symm.isIntertwining g
        (Theory.Representation.freeBasis K G alpha i)).symm
    exact isaacs_15_16_fixedSpace_of_freePermutationBasis rho b hb

private noncomputable def isaacs_15_16_extendScalars_free_equiv
    {K E G alpha : Type*} [Field K] [Field E] [Algebra K E] [Group G] :
    Theory.Representation.extendScalars (F := K) (G := G) E (Representation.free K G alpha) ≃ₗ
      Representation.free E G alpha := by
  let bK := (Theory.Representation.freeBasis K G alpha).baseChange E
  let bE := Theory.Representation.freeBasis E G alpha
  let e : (E ⊗[K] (alpha →₀ MonoidAlgebra K G)) ≃ₗ[E]
      (alpha →₀ MonoidAlgebra E G) := bK.equiv bE (Equiv.refl (alpha × G))
  refine Theory.Representation.RepEquiv.mk e ?_
  intro g
  apply Module.Basis.ext bK
  intro i
  have heval (j : alpha × G) : e (bK j) = bE j := by
    simp [e]
  rcases i with ⟨a, h⟩
  simp only [LinearMap.comp_apply, Theory.Representation.extendScalars_apply]
  dsimp only [bK]
  rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul,
    Theory.Representation.free_apply_freeBasis_pair, ← Module.Basis.baseChange_apply,
    ← Module.Basis.baseChange_apply]
  have heval1 :
      (e : E ⊗[K] (alpha →₀ MonoidAlgebra K G) → alpha →₀ MonoidAlgebra E G)
          ((Theory.Representation.freeBasis K G alpha).baseChange E (a, g * h)) =
        bE (a, g * h) := by
    simpa only [bK] using heval (a, g * h)
  have heval2 :
      (e : E ⊗[K] (alpha →₀ MonoidAlgebra K G) → alpha →₀ MonoidAlgebra E G)
          ((Theory.Representation.freeBasis K G alpha).baseChange E (a, h)) =
        bE (a, h) := by
    simpa only [bK] using heval (a, h)
  change e ((Theory.Representation.freeBasis K G alpha).baseChange E (a, g * h)) =
    Representation.free E G alpha g
      (e ((Theory.Representation.freeBasis K G alpha).baseChange E (a, h)))
  rw [heval1, heval2]
  simpa only [bE] using
    (Theory.Representation.free_apply_freeBasis_pair E G alpha g h a).symm
private theorem isaacs_15_16_extendScalars_equiv_free
    {K E G V alpha : Type*} [Field K] [Field E] [Algebra K E]
    [Group G] [AddCommGroup V] [Module K V]
    (rho : Representation K G V)
    (e : Theory.Representation.extendScalars (F := K) (G := G) (V := V) E rho ≃ₗ
      Representation.free E G alpha) :
    Nonempty
      (Theory.Representation.extendScalars (F := K) (G := G) (V := V) E rho ≃ₗ
        Theory.Representation.extendScalars (F := K) (G := G) E (Representation.free K G alpha)) :=
  ⟨e.trans (isaacs_15_16_extendScalars_free_equiv
    (K := K) (E := E) (G := G) (alpha := alpha)).symm⟩
private theorem isaacs_15_16_repEquiv_of_extendScalars
    {F E G V W : Type*} [Field F] [Field E] [Algebra F E] [Group G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (rho : Representation F G V) (sigma : Representation F G W)
    (hE : Nonempty (Theory.Representation.extendScalars E rho ≃ₗ
      Theory.Representation.extendScalars E sigma)) :
    Nonempty (rho ≃ₗ sigma) :=
  Theory.Representation.repEquiv_of_extendScalars rho sigma hE
set_option backward.isDefEq.respectTransparency false in
private theorem isaacs_15_16_descend_equiv_free
    {K E G V alpha : Type*} [Field K] [Field E] [Algebra K E]
    [Group G] [Finite G] [Finite alpha]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K G V)
    (e : Theory.Representation.extendScalars (F := K) (G := G) (V := V) E rho ≃ₗ
      Representation.free E G alpha) :
    Nonempty (rho ≃ₗ Representation.free K G alpha) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype alpha := Fintype.ofFinite alpha
  refine isaacs_15_16_repEquiv_of_extendScalars
    (F := K) (E := E) (G := G) (V := V)
    (W := alpha →₀ MonoidAlgebra K G) rho (Representation.free K G alpha) ?_
  exact isaacs_15_16_extendScalars_equiv_free
    (K := K) (E := E) (G := G) (V := V) (alpha := alpha) rho e
private noncomputable def isaacs_15_16_repEquiv_asModule
    {F G V W : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {rho : Representation F G V} {sigma : Representation F G W}
    (e : rho ≃ₗ sigma) :
    rho.asModule ≃ₗ[MonoidAlgebra F G] sigma.asModule :=
  LinearEquiv.ofBijective
    (Theory.Representation.RepMap.equivLinearMapAsModule rho sigma e.toRepMap)
    e.bijective

private noncomputable def isaacs_15_16_ofSubmodule'_repEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V)
    {U W : Submodule (MonoidAlgebra F G) rho.asModule}
    (e : U ≃ₗ[MonoidAlgebra F G] W) :
    (Subrepresentation.ofSubmodule' U).toRepresentation ≃ₗ
      (Subrepresentation.ofSubmodule' W).toRepresentation := by
  refine Theory.Representation.RepEquiv.mk (e.restrictScalars F) ?_
  intro g
  apply LinearMap.ext
  intro v
  let v' : U := ⟨v.1, v.2⟩
  apply Subtype.ext
  calc
    rho.asModuleEquiv ↑(e (((Subrepresentation.ofSubmodule' U).toRepresentation g) v)) =
        rho.asModuleEquiv ↑(e ((MonoidAlgebra.single g (1 : F)) • v')) := by
      have hv' :
          (((Subrepresentation.ofSubmodule' U).toRepresentation g) v) =
            ((MonoidAlgebra.single g (1 : F)) • v' : U) := by
        have hsingle :
            ((MonoidAlgebra.single g (1 : F)) • v' : U) =
              (Subrepresentation.ofSubmodule' U).toRepresentation g v' := by
          apply Subtype.ext
          simp only [SetLike.val_smul, Representation.single_smul, one_smul]
          rfl
        rw [hsingle]
        rfl
      exact congrArg (fun z => rho.asModuleEquiv ↑(e z)) hv'
    _ = rho.asModuleEquiv ↑((MonoidAlgebra.single g (1 : F)) • e v') := by
      exact congrArg (fun z => rho.asModuleEquiv (Subtype.val z))
        (e.map_smul (MonoidAlgebra.single g (1 : F)) v')
    _ = rho g (rho.asModuleEquiv ↑(e v')) := by
      simp only [SetLike.val_smul, Representation.single_smul, one_smul]
      rfl
    _ = rho g (rho.asModuleEquiv ↑(e v)) := by rfl

set_option backward.isDefEq.respectTransparency false

private noncomputable def isaacs_15_16_subrepresentation_repEquiv_asSubmodule
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    {rho : Representation F G V} {U W : Subrepresentation rho}
    (e : U.toRepresentation ≃ₗ W.toRepresentation) :
    U.asSubmodule ≃ₗ[MonoidAlgebra F G] W.asSubmodule := by
  let eMod := isaacs_15_16_repEquiv_asModule e
  let f : U.asSubmodule →ₗ[MonoidAlgebra F G] W.asSubmodule := {
    toFun v := ⟨(e ⟨v.1, v.2⟩).1, (e ⟨v.1, v.2⟩).2⟩
    map_add' x y := by
      apply Subtype.ext
      exact congrArg Subtype.val (e.map_add (⟨x.1, x.2⟩ : U) (⟨y.1, y.2⟩ : U))
    map_smul' a x := by
      induction a using MonoidAlgebra.induction_linear with
      | zero =>
          apply Subtype.ext
          exact congrArg Subtype.val e.map_zero
      | add a b ha hb =>
          let xa : U := ⟨(a • x).1, (a • x).2⟩
          let xb : U := ⟨(b • x).1, (b • x).2⟩
          have headd := congrArg Subtype.val (e.map_add xa xb)
          have hsum := congrArg₂ (· + ·) (congrArg Subtype.val ha)
            (congrArg Subtype.val hb)
          simp only [RingHom.id_apply, add_smul]
          apply Subtype.ext
          exact headd.trans hsum
      | single g r =>
          let x' : U.toRepresentation.asModule := ⟨x.1, x.2⟩
          have hm := eMod.map_smul (MonoidAlgebra.single g r) x'
          apply Subtype.ext
          simp only [RingHom.id_apply, SetLike.val_smul,
            Representation.single_smul] at hm ⊢
          exact congrArg Subtype.val hm }
  refine LinearEquiv.ofBijective f ?_
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply congrArg Subtype.val
    apply e.injective
    apply Subtype.ext
    exact congrArg Subtype.val hxy
  · intro y
    obtain ⟨x, hx⟩ := e.surjective (⟨y.1, y.2⟩ : W)
    refine ⟨⟨x.1, x.2⟩, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hx
private noncomputable def isaacs_15_16_componentOrderIso
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal] (g : G) :
    Submodule (MonoidAlgebra F N)
        (Representation.asModule (rho.comp N.subtype : Representation F N V)) ≃o
      Submodule (MonoidAlgebra F N)
        (Representation.asModule (rho.comp N.subtype : Representation F N V)) := by
  let rhoN : Representation F N V := rho.comp N.subtype
  exact
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := rhoN)).symm |>.trans
      ((Theory.Representation.conjugateSubrepresentationOrderIso rho N g).trans
        (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := rhoN)))

@[simp]
private theorem isaacs_15_16_componentOrderIso_one
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (W : Submodule (MonoidAlgebra F N)
      (Representation.asModule (rho.comp N.subtype : Representation F N V))) :
    isaacs_15_16_componentOrderIso rho N 1 W = W := by
  simp only [isaacs_15_16_componentOrderIso, Subrepresentation.subrepresentationSubmoduleOrderIso,
    OrderIso.symm_mk, OrderIso.trans_apply, RelIso.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Theory.Representation.conjugateSubrepresentationOrderIso_apply,
    Theory.Representation.conjugateSubrepresentation, inv_one, map_one, Equiv.coe_fn_mk,
    Subrepresentation.asSubmodule]
  congr
  ext
  simp only [Submodule.mem_toAddSubmonoid, Submodule.mem_map, Module.End.one_apply, exists_eq_right]
  rfl

@[simp]
private theorem isaacs_15_16_componentOrderIso_mul
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (g k : G)
    (W : Submodule (MonoidAlgebra F N)
      (Representation.asModule (rho.comp N.subtype : Representation F N V))) :
    isaacs_15_16_componentOrderIso rho N (g * k) W =
      isaacs_15_16_componentOrderIso rho N g
        (isaacs_15_16_componentOrderIso rho N k W) := by
  change
    (Theory.Representation.conjugateSubrepresentationOrderIso rho N (g * k)
      (Subrepresentation.ofSubmodule' W)).asSubmodule =
    (Theory.Representation.conjugateSubrepresentationOrderIso rho N g
      (Theory.Representation.conjugateSubrepresentationOrderIso rho N k
        (Subrepresentation.ofSubmodule' W))).asSubmodule
  exact congrArg Subrepresentation.asSubmodule
    (Theory.Representation.conjugateSubrepresentationOrderIso_mul rho N g k
      (Subrepresentation.ofSubmodule' W))

private theorem isaacs_15_16_componentOrderIso_restrictScalars
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (g : G)
    (W : Submodule (MonoidAlgebra F N)
      (Representation.asModule (rho.comp N.subtype : Representation F N V))) :
    (isaacs_15_16_componentOrderIso rho N g W).restrictScalars F =
      Submodule.map (rho g) (W.restrictScalars F) := by
  change
    ((Theory.Representation.conjugateSubrepresentationOrderIso rho N g
      (Subrepresentation.ofSubmodule' W)).asSubmodule).restrictScalars F =
      Submodule.map (rho g) (W.restrictScalars F)
  exact congrArg (Submodule.restrictScalars F)
    (Theory.Representation.conjugateSubrepresentationOrderIso_toSubmodule rho N g
      (Subrepresentation.ofSubmodule' W))
private noncomputable def isaacs_15_16_componentOrderIso_linearEquiv
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    {U W : Submodule (MonoidAlgebra F N)
      (Representation.asModule (rho.comp N.subtype : Representation F N V))}
    (e : U ≃ₗ[MonoidAlgebra F N] W) (g : G) :
    isaacs_15_16_componentOrderIso rho N g U ≃ₗ[MonoidAlgebra F N]
      isaacs_15_16_componentOrderIso rho N g W := by
  let rhoN : Representation F N V := rho.comp N.subtype
  let eRep := isaacs_15_16_ofSubmodule'_repEquiv rhoN e
  let eConj :=
    Theory.Representation.conjugateSubrepresentationOrderIsoRepEquiv rho N eRep g
  change
    (Theory.Representation.conjugateSubrepresentationOrderIso rho N g
        (Subrepresentation.ofSubmodule' U)).asSubmodule ≃ₗ[MonoidAlgebra F N]
      (Theory.Representation.conjugateSubrepresentationOrderIso rho N g
        (Subrepresentation.ofSubmodule' W)).asSubmodule
  exact isaacs_15_16_subrepresentation_repEquiv_asSubmodule eConj

private theorem isaacs_15_16_componentOrderIso_isotypicComponent_le
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (g : G)
    (S :
      letI : Module (MonoidAlgebra F N) V :=
        Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
      Submodule (MonoidAlgebra F N) V) :
    letI : Module (MonoidAlgebra F N)
        V :=
      Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
    isaacs_15_16_componentOrderIso rho N g
        (isotypicComponent (MonoidAlgebra F N)
          V S) <=
      isotypicComponent (MonoidAlgebra F N)
        V
        (isaacs_15_16_componentOrderIso rho N g S) := by
  letI : Module (MonoidAlgebra F N)
      V :=
    Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
  unfold isotypicComponent
  calc
    isaacs_15_16_componentOrderIso rho N g
        (sSup {U : Submodule (MonoidAlgebra F N) V |
          Nonempty (U ≃ₗ[MonoidAlgebra F N] S)}) =
      ⨆ U ∈ {U : Submodule (MonoidAlgebra F N) V |
          Nonempty (U ≃ₗ[MonoidAlgebra F N] S)},
        isaacs_15_16_componentOrderIso rho N g U :=
      (isaacs_15_16_componentOrderIso rho N g).map_sSup _
    _ <= sSup {U : Submodule (MonoidAlgebra F N) V | Nonempty
        (U ≃ₗ[MonoidAlgebra F N]
          isaacs_15_16_componentOrderIso rho N g S)} := by
      refine iSup₂_le ?_
      intro U hU
      exact le_sSup
        (show Nonempty
            (isaacs_15_16_componentOrderIso rho N g U ≃ₗ[MonoidAlgebra F N]
              isaacs_15_16_componentOrderIso rho N g S) from
          ⟨isaacs_15_16_componentOrderIso_linearEquiv rho N hU.some g⟩)

private theorem isaacs_15_16_componentOrderIso_isotypicComponent_eq
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (g : G)
    (S :
      letI : Module (MonoidAlgebra F N) V :=
        Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
      Submodule (MonoidAlgebra F N) V) :
    letI : Module (MonoidAlgebra F N)
        V :=
      Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
    isaacs_15_16_componentOrderIso rho N g
        (isotypicComponent (MonoidAlgebra F N)
          V S) =
      isotypicComponent (MonoidAlgebra F N)
        V
        (isaacs_15_16_componentOrderIso rho N g S) := by
  letI : Module (MonoidAlgebra F N)
      V :=
    Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
  apply le_antisymm
  · exact isaacs_15_16_componentOrderIso_isotypicComponent_le rho N g S
  · have hback :=
      isaacs_15_16_componentOrderIso_isotypicComponent_le rho N g⁻¹
        (isaacs_15_16_componentOrderIso rho N g S)
    have hforward :=
      (isaacs_15_16_componentOrderIso rho N g).monotone hback
    have hcancel :
        isaacs_15_16_componentOrderIso rho N g⁻¹
            (isaacs_15_16_componentOrderIso rho N g S) = S := by
      rw [← isaacs_15_16_componentOrderIso_mul, inv_mul_cancel,
        isaacs_15_16_componentOrderIso_one]
    rw [hcancel] at hforward
    have hcancelLeft :
        isaacs_15_16_componentOrderIso rho N g
            (isaacs_15_16_componentOrderIso rho N g⁻¹
              (isotypicComponent (MonoidAlgebra F N) V
                (isaacs_15_16_componentOrderIso rho N g S))) =
          isotypicComponent (MonoidAlgebra F N) V
            (isaacs_15_16_componentOrderIso rho N g S) := by
      rw [← isaacs_15_16_componentOrderIso_mul, mul_inv_cancel,
        isaacs_15_16_componentOrderIso_one]
    exact hcancelLeft ▸ hforward

private theorem isaacs_15_16_componentOrderIso_mem_isotypicComponents
    {F G V : Type*} [Field F] [Group G]
    [AddCommGroup V] [Module F V]
    (rho : Representation F G V) (N : Subgroup G) [N.Normal]
    (g : G)
    (c :
      letI : Module (MonoidAlgebra F N)
          V :=
        Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
      isotypicComponents (MonoidAlgebra F N)
        V) :
    letI : Module (MonoidAlgebra F N)
        V :=
      Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
    isaacs_15_16_componentOrderIso rho N g c.1 ∈
      isotypicComponents (MonoidAlgebra F N)
        V := by
  letI : Module (MonoidAlgebra F N)
      V :=
    Representation.instModuleMonoidAlgebraAsModule (rho.comp N.subtype)
  rcases c with ⟨c, S, hS, rfl⟩
  refine ⟨isaacs_15_16_componentOrderIso rho N g S, ?_, ?_⟩
  · rw [isSimpleModule_iff_isAtom]
    exact ((isaacs_15_16_componentOrderIso rho N g).isAtom_iff S).mpr
      (isSimpleModule_iff_isAtom.mp hS)
  · exact isaacs_15_16_componentOrderIso_isotypicComponent_eq rho N g S

private theorem isaacs_15_16_cast_apply
    {X V : Type*} (D : X -> Type*) (f : (x : X) -> D x -> V)
    {a b : X} (p : a = b) (i : D b) :
    f a (cast (congrArg D p.symm) i) = f b i := by
  cases p
  rfl
private theorem isaacs_15_16_repEquiv_free_of_component_action_aux
    {H E V C Q : Type*} [Group H] [Fintype H] [Field E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Fintype C] [DecidableEq C] [Fintype Q]
    [MulAction H C] [IsCancelSMul H C]
    (rho : Representation E H V) (A : C -> Submodule E V)
    (hInternal : DirectSum.IsInternal A)
    (hmap : forall h : H, forall c : C,
      Submodule.map (rho h) (A c) = A (h • c))
    (out : Q -> C) (eC : Q × H ≃ C)
    (heC : forall q : Q, forall h : H, eC (q, h) = h • out q) :
    exists (alpha : Type) (_ : Finite alpha),
      Nonempty (rho ≃ₗ Representation.free E H alpha) := by
  classical
  letI (c : C) : FiniteDimensional E (A c) :=
    FiniteDimensional.of_injective (A c).subtype Subtype.val_injective
  let eH (h : H) : V ≃ₗ[E] V :=
    LinearEquiv.ofBijective (rho h) (Representation.apply_bijective rho h)
  let eSub (h : H) (c : C) : A c ≃ₗ[E] A (h • c) :=
    ((eH h).submoduleMap (A c)).trans
      (LinearEquiv.ofEq _ _ (hmap h c))
  let bC (c : C) :
      Module.Basis
        (Fin (Module.finrank E (A (out (eC.symm c).1)))) E (A c) := by
    let qh := eC.symm c
    have hc : qh.2 • out qh.1 = c := by
      calc
        qh.2 • out qh.1 = eC qh := (heC qh.1 qh.2).symm
        _ = c := eC.apply_symm_apply c
    exact (Module.finBasis E (A (out qh.1))).map
      ((eSub qh.2 (out qh.1)).trans
        (LinearEquiv.ofEq _ _ (congrArg A hc)))
  let bAll :
      Module.Basis
        (Sigma fun c : C =>
          Fin (Module.finrank E (A (out (eC.symm c).1)))) E V :=
    hInternal.collectedBasis bC
  let alpha := Sigma fun q : Q => Fin (Module.finrank E (A (out q)))
  let reassoc :
      alpha × H ≃
        (Sigma fun qh : Q × H => Fin (Module.finrank E (A (out qh.1)))) := {
    toFun x := ⟨(x.1.1, x.2), x.1.2⟩
    invFun x := (⟨x.1.1, x.2⟩, x.1.2)
    left_inv x := rfl
    right_inv x := rfl }
  let sigmaE :
      (Sigma fun qh : Q × H => Fin (Module.finrank E (A (out qh.1)))) ≃
        (Sigma fun c : C =>
          Fin (Module.finrank E (A (out (eC.symm c).1)))) :=
    (Equiv.sigmaCongrRight (fun qh =>
      Equiv.cast (congrArg
        (fun r : Q × H => Fin (Module.finrank E (A (out r.1))))
        (eC.symm_apply_apply qh).symm))).trans
      (Equiv.sigmaCongrLeft
        (β := fun c : C =>
          Fin (Module.finrank E (A (out (eC.symm c).1)))) eC)
  let idx :
      alpha × H ≃
        (Sigma fun c : C =>
          Fin (Module.finrank E (A (out (eC.symm c).1)))) :=
    reassoc.trans sigmaE
  have heC_symm (q : Q) (h : H) : eC.symm (h • out q) = (q, h) := by
    rw [← heC q h]
    exact eC.symm_apply_apply (q, h)
  let b : Module.Basis (alpha × H) E V := bAll.reindex idx.symm
  have hbBase (q : Q) (i : Fin (Module.finrank E (A (out q)))) (h : H) :
      b (⟨q, i⟩, h) = rho h ((Module.finBasis E (A (out q))) i) := by
    simp [b, idx, reassoc, sigmaE,
      Equiv.sigmaCongrRight_apply, Equiv.sigmaCongrLeft_apply, bAll, bC, eSub, eH,
      DirectSum.IsInternal.collectedBasis_coe, heC, heC_symm]
    let hp := eC.symm_apply_apply (q, h)
    let D : Q × H -> Type _ := fun r =>
      Fin (Module.finrank E (A (out r.1)))
    exact isaacs_15_16_cast_apply D
      (fun r j => rho h ((Module.finBasis E (A (out r.1)) j).1)) hp i
  have hb (g : H) (x : alpha × H) :
      rho g (b x) = b (x.1, g * x.2) := by
    rcases x with ⟨⟨q, i⟩, h⟩
    rw [hbBase, hbBase]
    simp [map_mul, Module.End.mul_eq_comp]
  let alpha0 := Fin (Fintype.card alpha)
  let qAlpha : alpha ≃ alpha0 := Fintype.equivFin alpha
  let b0 : Module.Basis (alpha0 × H) E V :=
    b.reindex (qAlpha.prodCongr (Equiv.refl H))
  have hb0 (g : H) (x : alpha0 × H) :
      rho g (b0 x) = b0 (x.1, g * x.2) := by
    rcases x with ⟨i, h⟩
    simp only [b0, Module.Basis.reindex_apply]
    change rho g (b (qAlpha.symm i, h)) = b (qAlpha.symm i, g * h)
    exact hb g (qAlpha.symm i, h)
  let eLin :=
    b0.equiv (Theory.Representation.freeBasis E H alpha0) (Equiv.refl (alpha0 × H))
  refine ⟨alpha0, inferInstance, ⟨Theory.Representation.RepEquiv.mk eLin ?_⟩⟩
  intro g
  apply b0.ext
  intro x
  change eLin (rho g (b0 x)) =
    Representation.free E H alpha0 g (eLin (b0 x))
  rw [hb0]
  rw [Module.Basis.equiv_apply, Module.Basis.equiv_apply]
  exact (Theory.Representation.free_apply_freeBasis_pair E H alpha0 g x.2 x.1).symm

private theorem isaacs_15_16_repEquiv_free_of_component_action
    {H E V C : Type*} [Group H] [Finite H] [Field E]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    [Finite C] [DecidableEq C] [MulAction H C] [IsCancelSMul H C]
    (rho : Representation E H V) (A : C -> Submodule E V)
    (hInternal : DirectSum.IsInternal A)
    (hmap : forall h : H, forall c : C,
      Submodule.map (rho h) (A c) = A (h • c)) :
    exists (alpha : Type) (_ : Finite alpha),
      Nonempty (rho ≃ₗ Representation.free E H alpha) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype C := Fintype.ofFinite C
  let Q := MulAction.orbitRel.Quotient H C
  letI : Fintype Q := Fintype.ofFinite Q
  let eC : Q × H ≃ C := Equiv.ofBijective
    (fun qh => qh.2 • Quotient.out qh.1) (by
      constructor
      · rintro ⟨q, h⟩ ⟨r, k⟩ heq
        have hqRel : MulAction.orbitRel H C (h • Quotient.out q) (Quotient.out q) := by
          exact ⟨h, rfl⟩
        have hrRel : MulAction.orbitRel H C (k • Quotient.out r) (Quotient.out r) := by
          exact ⟨k, rfl⟩
        have hq : Quotient.mk'' (h • Quotient.out q) = q :=
          (Quotient.sound hqRel).trans (Quotient.out_eq' q)
        have hr : Quotient.mk'' (k • Quotient.out r) = r :=
          (Quotient.sound hrRel).trans (Quotient.out_eq' r)
        have hqr : q = r := hq.symm.trans ((congrArg Quotient.mk'' heq).trans hr)
        subst r
        have hhk : h = k :=
          IsCancelSMul.right_cancel h k (Quotient.out q) heq
        exact Prod.ext rfl hhk
      · intro c
        let q : Q := Quotient.mk'' c
        have hc : c ∈ MulAction.orbit H (Quotient.out q) := by
          rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q Quotient.out_eq']
          exact MulAction.orbitRel.Quotient.mem_orbit.mpr rfl
        rcases hc with ⟨h, hh⟩
        exact ⟨(q, h), hh⟩)
  exact isaacs_15_16_repEquiv_free_of_component_action_aux
    rho A hInternal hmap (fun q : Q => Quotient.out q) eC (by
      intro q h
      rfl)
private theorem isaacs_15_16_isotypic_internal
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [IsSemisimpleModule R M] [DecidableEq (isotypicComponents R M)] :
    DirectSum.IsInternal
      (fun c : isotypicComponents R M => (c.1 : Submodule R M)) := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact (sSupIndep_iff _).mp (sSupIndep_isotypicComponents R M)
  · exact (sSup_eq_iSup' _).symm.trans (sSup_isotypicComponents R M)

private theorem isaacs_15_16_fixedSubspace_extendScalars_eq_bot
    {G K V : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V]
    (N : Subgroup G) (rho : Representation K G V)
    (hchar : ¬ ringChar K ∣ Nat.card N)
    (hfixedN : rho.fixedSubspace N = (⊥ : Submodule K V)) :
    (Theory.Representation.extendScalars (AlgebraicClosure K) rho).fixedSubspace N =
      (⊥ : Submodule (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] V)) := by
  have hcardK : (Nat.card N : K) ≠ 0 := by
    intro hzero
    exact hchar ((ringChar.spec K (Nat.card N)).mp hzero)
  have hcardE : (Nat.card N : AlgebraicClosure K) ≠ 0 := by
    intro hzero
    apply hchar
    have hdiv :
        ringChar (AlgebraicClosure K) ∣ Nat.card N :=
      (ringChar.spec (AlgebraicClosure K) (Nat.card N)).mp hzero
    simpa [Algebra.ringChar_eq K (AlgebraicClosure K)] using hdiv
  dsimp [Representation.fixedSubspace]
  change Representation.invariants
      (Theory.Representation.extendScalars (AlgebraicClosure K)
        (rho.comp N.subtype : Representation K N V)) = ⊥
  have hInv :
      Representation.invariants
          (rho.comp N.subtype : Representation K N V) = ⊥ := by
    simpa [Representation.fixedSubspace] using hfixedN
  rw [Theory.Representation.invariants_extendScalars_eq_baseChange_of_card_ne_zero
      (ρ := (rho.comp N.subtype : Representation K N V)) hcardK hcardE,
    hInv, Submodule.baseChange_bot]

private theorem isaacs_15_16_algebraicClosure_restrict_equiv_free
    {G K V : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (N H : Subgroup G) (rho : Representation K G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement N H)
    (hchar : ¬ ringChar K ∣ Nat.card N)
    (hfixedN : rho.fixedSubspace N = (⊥ : Submodule K V)) :
    exists (alpha : Type) (_ : Finite alpha),
      Nonempty
        (Theory.Representation.extendScalars (AlgebraicClosure K)
            (rho.comp H.subtype : Representation K H V) ≃ₗ
          Representation.free (AlgebraicClosure K) H alpha) := by
  classical
  let E := AlgebraicClosure K
  let : CharP E (ringChar E) := ringChar.charP E
  let rhoE : Representation E G (E ⊗[K] V) :=
    Theory.Representation.extendScalars E rho
  let : FiniteDimensional E (E ⊗[K] V) :=
    Theory.Representation.extendScalars_finite_dimensional E rho
  have hfixedE : rhoE.fixedSubspace N =
      (⊥ : Submodule E (E ⊗[K] V)) := by
    simpa [E, rhoE] using
      isaacs_15_16_fixedSubspace_extendScalars_eq_bot N rho hchar hfixedN
  have hcharE : ¬ ringChar E ∣ Nat.card N := by
    simpa [E, Algebra.ringChar_eq K (AlgebraicClosure K)] using hchar
  have hmaschke :
      ringChar E = 0 ∨
        (Nat.Prime (ringChar E) ∧ Nat.Coprime (ringChar E) (Nat.card N)) := by
    by_cases hzero : ringChar E = 0
    · exact Or.inl hzero
    · have hprime : Nat.Prime (ringChar E) :=
        (CharP.char_is_prime_or_zero E (ringChar E)).resolve_right hzero
      exact Or.inr ⟨hprime, hprime.coprime_iff_not_dvd.mpr hcharE⟩
  let psiN : Representation E N (E ⊗[K] V) := rhoE.comp N.subtype
  let : AddCommGroup (Representation.asModule psiN) :=
    Representation.instAddCommGroupAsModule psiN
  let : Module (MonoidAlgebra E N) (E ⊗[K] V) :=
    Representation.instModuleMonoidAlgebraAsModule psiN
  let : Module (MonoidAlgebra E N) (Representation.asModule psiN) :=
    Representation.instModuleMonoidAlgebraAsModule psiN
  let : IsScalarTower E (MonoidAlgebra E N) (E ⊗[K] V) :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule (ρ := psiN)
  let : Module.Finite E (E ⊗[K] V) := inferInstance
  let : Module.Finite (MonoidAlgebra E N) (E ⊗[K] V) :=
    Module.Finite.of_restrictScalars_finite E (MonoidAlgebra E N) (E ⊗[K] V)
  let hsemi :
      IsSemisimpleModule (MonoidAlgebra E N) (E ⊗[K] V) :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      psiN hmaschke
  let : DecidableEq (isotypicComponents (MonoidAlgebra E N) (E ⊗[K] V)) :=
    Classical.decEq _
  have hInternal :
      DirectSum.IsInternal
        (fun c : isotypicComponents (MonoidAlgebra E N) (E ⊗[K] V) =>
          (c.1 : Submodule (MonoidAlgebra E N) (E ⊗[K] V))) :=
    isaacs_15_16_isotypic_internal
  let : N.Normal := hfrob.normal
  let C := isotypicComponents (MonoidAlgebra E N) (E ⊗[K] V)
  let componentAction : MulAction H C := {
    smul h c :=
      ⟨isaacs_15_16_componentOrderIso rhoE N (h : G) c.1,
        isaacs_15_16_componentOrderIso_mem_isotypicComponents
          rhoE N (h : G) c⟩
    one_smul c := by
      apply Subtype.ext
      exact isaacs_15_16_componentOrderIso_one rhoE N c.1
    mul_smul h k c := by
      apply Subtype.ext
      change isaacs_15_16_componentOrderIso rhoE N (((h * k : H) : H) : G) c.1 =
        isaacs_15_16_componentOrderIso rhoE N (h : G)
          (isaacs_15_16_componentOrderIso rhoE N (k : G) c.1)
      exact isaacs_15_16_componentOrderIso_mul rhoE N (h : G) (k : G) c.1 }
  let : MulAction H C := componentAction
  let A : C -> Submodule E (E ⊗[K] V) :=
    fun c => c.1.restrictScalars E
  have hInternalE : DirectSum.IsInternal A := by
    have h_same : (DirectSum.coeAddMonoidHom A :
        DirectSum (Subtype C) (fun (c : Subtype C) => A c) → (E ⊗[K] V)) =
        (DirectSum.coeAddMonoidHom
          (fun (c : C) => (c.1 : Submodule (MonoidAlgebra E N) (E ⊗[K] V)))) ∘
        (DirectSum.map (fun (c : C) =>
          (Submodule.restrictScalarsEquiv E (MonoidAlgebra E N) (E ⊗[K] V)
            c.1).toAddMonoidHom) : DirectSum (Subtype C) (fun c => A c) →
          DirectSum (Subtype C) (fun c => (c.1 : Submodule (MonoidAlgebra E N) (E ⊗[K] V)))) := by
      ext x
      induction x using DirectSum.induction_on with
      | zero => simp [A]
      | of c x => rfl
      | add x y hx hy => simp [hx, hy, A]
    unfold DirectSum.IsInternal
    rw [h_same]
    have he_bijective : Function.Bijective (DirectSum.map (fun (c : C) =>
      (Submodule.restrictScalarsEquiv E (MonoidAlgebra E N) (E ⊗[K] V)
        c.1).toAddMonoidHom) : DirectSum (Subtype C) (fun c => A c) →
      DirectSum (Subtype C) (fun c => (c.1 : Submodule (MonoidAlgebra E N) (E ⊗[K] V)))) := by
      have hinj : ∀ (c : C), Function.Injective
        ((Submodule.restrictScalarsEquiv E (MonoidAlgebra E N) (E ⊗[K] V)
          c.1).toAddMonoidHom) := by
        intro c; exact AddEquiv.injective _
      have hsurj : ∀ (c : C), Function.Surjective
        ((Submodule.restrictScalarsEquiv E (MonoidAlgebra E N) (E ⊗[K] V)
          c.1).toAddMonoidHom) := by
        intro c; exact AddEquiv.surjective _
      exact ⟨(DirectSum.map_injective _).mpr hinj, (DirectSum.map_surjective _).mpr hsurj⟩
    exact hInternal.comp he_bijective
  have hmap : forall h : H, forall c : C,
      Submodule.map ((rhoE.comp H.subtype) h) (A c) = A (h • c) := by
    intro h c
    have htemp := (isaacs_15_16_componentOrderIso_restrictScalars rhoE N (h : G) c.1).symm
    change Submodule.map (rhoE (h : G)) (c.1.restrictScalars E) =
      (isaacs_15_16_componentOrderIso rhoE N (h : G) c.1).restrictScalars E
    exact htemp
  have h71 := VII.isaacs_problem_7_1 N H hfrob.kernel_ne_bot
    hfrob.complement_ne_bot hfrob.isComplement'.sup_eq_top
    hfrob.isComplement'.disjoint
  have hB : forall n : N, n ≠ 1 -> forall h : H,
      (h : G) * (n : G) = (n : G) * (h : G) -> h = 1 :=
    h71.1.mp (h71.2.2.2.2.mpr hfrob)
  have hfixedConj : forall n : N, n ≠ 1 -> forall h : H,
      h • n = n -> h = 1 := by
    intro n hn h hfix
    apply hB n hn h
    apply mul_inv_eq_iff_eq_mul.mp
    simpa [Subgroup.conjMulDistribMulActionOfNormal_smul_coe] using
      congrArg Subtype.val hfix
  let : IsCancelSMul H C := {
    toIsLeftCancelSMul := inferInstance
    right_cancel' h k c hhk := by
      have hcne : c.1 ≠ (⊥ : Submodule (MonoidAlgebra E N) (E ⊗[K] V)) :=
        (bot_lt_isotypicComponents (show c.1 ∈
          isotypicComponents (MonoidAlgebra E N) (E ⊗[K] V) from c.2)).ne'
      obtain ⟨S, hSc, hSsimple⟩ :=
        (IsSemisimpleModule.eq_bot_or_exists_simple_le c.1).resolve_left hcne
      let : IsSimpleModule (MonoidAlgebra E N) S := hSsimple
      let Srep := Subrepresentation.ofSubmodule' (ρ := psiN) S
      let sigma := Srep.toRepresentation
      let : FiniteDimensional E Srep.toSubmodule :=
        FiniteDimensional.of_injective Srep.toSubmodule.subtype
          Subtype.val_injective
      have hirr := irreducible_subrepresentation_of_simple_asModuleSubmodule psiN hSsimple
      have hnonprincipal :
          ¬ Nonempty (sigma ≃ₗ Representation.trivial E N E) := by
        rintro ⟨e⟩
        let v := e.symm 1
        have hvne : v ≠ 0 := by
          intro hv
          have hev := congrArg e hv
          have hev1 : (1 : E) = e 0 := by simpa [v] using hev
          have he0 : e 0 = 0 := e.map_zero
          exact one_ne_zero (hev1.trans he0)
        have hvfixed : (v.1 : E ⊗[K] V) ∈ rhoE.fixedSubspace N := by
          change forall n : N, rhoE (n : G) v.1 = v.1
          intro n
          have hsig : sigma n v = v := by
            apply e.injective
            simpa using e.isIntertwining n v
          exact congrArg Subtype.val hsig
        have hvzero : (v.1 : E ⊗[K] V) = 0 := by
          rw [hfixedE] at hvfixed
          simpa using hvfixed
        apply hvne
        apply Subtype.ext
        exact hvzero
      let psiConj (h : H) : Representation E N Srep.toSubmodule :=
        Theory.Representation.conjugateRep
          (F := E) (G := G) (V := Srep.toSubmodule) (H := N) sigma (h : G)⁻¹
      have hpsiConj : forall h : H, forall n : N,
          psiConj h (h • n) = sigma n := by
        intro h n
        ext v
        simp [psiConj, Theory.Representation.conjugateRep_apply, mul_assoc]
      have hcomp :
          isaacs_15_16_componentOrderIso rhoE N (h : G) c.1 =
            isaacs_15_16_componentOrderIso rhoE N (k : G) c.1 := by
        exact congrArg Subtype.val hhk
      let Sh := isaacs_15_16_componentOrderIso rhoE N (h : G) S
      let Sk := isaacs_15_16_componentOrderIso rhoE N (k : G) S
      have hShsimple : IsSimpleModule (MonoidAlgebra E N) Sh := by
        apply isSimpleModule_iff_isAtom.mpr
        change IsAtom (isaacs_15_16_componentOrderIso rhoE N (h : G) S)
        exact ((isaacs_15_16_componentOrderIso rhoE N (h : G)).isAtom_iff S).mpr
          (isSimpleModule_iff_isAtom.mp hSsimple)
      have hSksimple : IsSimpleModule (MonoidAlgebra E N) Sk := by
        apply isSimpleModule_iff_isAtom.mpr
        change IsAtom (isaacs_15_16_componentOrderIso rhoE N (k : G) S)
        exact ((isaacs_15_16_componentOrderIso rhoE N (k : G)).isAtom_iff S).mpr
          (isSimpleModule_iff_isAtom.mp hSsimple)
      let : IsSimpleModule (MonoidAlgebra E N) Sh := hShsimple
      let : IsSimpleModule (MonoidAlgebra E N) Sk := hSksimple
      have hShc : Sh <=
          isaacs_15_16_componentOrderIso rhoE N (h : G) c.1 :=
        (isaacs_15_16_componentOrderIso rhoE N (h : G)).monotone hSc
      have hSkc : Sk <=
          isaacs_15_16_componentOrderIso rhoE N (h : G) c.1 := by
        rw [hcomp]
        exact (isaacs_15_16_componentOrderIso rhoE N (k : G)).monotone hSc
      have hcH :=
        isaacs_15_16_componentOrderIso_mem_isotypicComponents
          rhoE N (h : G) c
      rcases hcH with ⟨T, hTsimple, hcT⟩
      let : IsSimpleModule (MonoidAlgebra E N) T := hTsimple
      have htype : IsIsotypicOfType (MonoidAlgebra E N)
          (isaacs_15_16_componentOrderIso rhoE N (h : G) c.1) T := by
        rw [hcT]
        exact IsIsotypicOfType.isotypicComponent
          (MonoidAlgebra E N) (E ⊗[K] V) T
      have eShT : Nonempty (Sh ≃ₗ[MonoidAlgebra E N] T) :=
        (isIsotypicOfType_submodule_iff.mp htype) Sh hShc
      have eSkT : Nonempty (Sk ≃ₗ[MonoidAlgebra E N] T) :=
        (isIsotypicOfType_submodule_iff.mp htype) Sk hSkc
      let eShSk : Sh ≃ₗ[MonoidAlgebra E N] Sk :=
        eShT.some.trans eSkT.some.symm
      let eTrans :
          (Subrepresentation.ofSubmodule' Sh).toRepresentation ≃ₗ
            (Subrepresentation.ofSubmodule' Sk).toRepresentation :=
        isaacs_15_16_ofSubmodule'_repEquiv psiN eShSk
      have hSbase :
          (Subrepresentation.subrepresentationSubmoduleOrderIso
            (ρ := psiN)).symm S =
            Srep := rfl
      have hShEq :
          Subrepresentation.ofSubmodule' Sh =
            Theory.Representation.conjugateSubrepresentation rhoE N
              Srep (h : G)⁻¹ := by
        change
          (Subrepresentation.subrepresentationSubmoduleOrderIso
            (ρ := psiN)).symm
              ((Theory.Representation.conjugateSubrepresentationOrderIso rhoE N (h : G)
                ((Subrepresentation.subrepresentationSubmoduleOrderIso
                  (ρ := psiN)).symm S)).asSubmodule) = _
        rw [← Subrepresentation.subrepresentationSubmoduleOrderIso_apply]
        rw [OrderIso.symm_apply_apply]
        rw [Theory.Representation.conjugateSubrepresentationOrderIso_apply]
        exact congrArg
          (fun W : Subrepresentation psiN =>
            Theory.Representation.conjugateSubrepresentation rhoE N W (h : G)⁻¹)
          hSbase
      have hSkEq :
          Subrepresentation.ofSubmodule' Sk =
            Theory.Representation.conjugateSubrepresentation rhoE N
              Srep (k : G)⁻¹ := by
        change
          (Subrepresentation.subrepresentationSubmoduleOrderIso
            (ρ := psiN)).symm
              ((Theory.Representation.conjugateSubrepresentationOrderIso rhoE N (k : G)
                ((Subrepresentation.subrepresentationSubmoduleOrderIso
                  (ρ := psiN)).symm S)).asSubmodule) = _
        rw [← Subrepresentation.subrepresentationSubmoduleOrderIso_apply]
        rw [OrderIso.symm_apply_apply]
        rw [Theory.Representation.conjugateSubrepresentationOrderIso_apply]
        exact congrArg
          (fun W : Subrepresentation psiN =>
            Theory.Representation.conjugateSubrepresentation rhoE N W (k : G)⁻¹)
          hSbase
      let eH :
          (Subrepresentation.ofSubmodule' Sh).toRepresentation ≃ₗ psiConj h := by
        rw [hShEq]
        simpa [psiConj, sigma] using
          (Theory.Representation.conjugateSubrepresentationEquiv rhoE N
            Srep (h : G)⁻¹)
      let eK :
          (Subrepresentation.ofSubmodule' Sk).toRepresentation ≃ₗ psiConj k := by
        rw [hSkEq]
        simpa [psiConj, sigma] using
          (Theory.Representation.conjugateSubrepresentationEquiv rhoE N
            Srep (k : G)⁻¹)
      have hequiv : Nonempty (psiConj h ≃ₗ psiConj k) :=
        ⟨eH.symm.trans (eTrans.trans eK)⟩
      exact isaacs_lemma_15_15
        (E := E) (H := H) (N := N) (V := Srep.toSubmodule)
        sigma hcharE hfixedConj hirr hnonprincipal psiConj hpsiConj h k hequiv }
  obtain ⟨alpha, hfinite, ⟨e⟩⟩ :=
    isaacs_15_16_repEquiv_free_of_component_action
      (rhoE.comp H.subtype) A hInternalE hmap
  exact ⟨alpha, hfinite, ⟨e⟩⟩

private theorem isaacs_15_16_restrict_equiv_free
    {G K V : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (N H : Subgroup G) (rho : Representation K G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement N H)
    (hchar : ¬ ringChar K ∣ Nat.card N)
    (hfixedN : rho.fixedSubspace N = (⊥ : Submodule K V)) :
    exists (alpha : Type) (_ : Finite alpha),
      Nonempty
        ((rho.comp H.subtype : Representation K H V) ≃ₗ
          Representation.free K H alpha) := by
  obtain ⟨alpha, hfinite, ⟨hE⟩⟩ :=
    isaacs_15_16_algebraicClosure_restrict_equiv_free
      N H rho hfrob hchar hfixedN
  letI : Finite alpha := hfinite
  refine ⟨alpha, hfinite, ?_⟩
  exact isaacs_15_16_descend_equiv_free
    (E := AlgebraicClosure K) (rho.comp H.subtype) hE
/-- Isaacs, Character Theory of Finite Groups, Theorem 15.16. -/
public theorem isaacs_theorem_15_16
    {G K V : Type*} [Group G] [Finite G] [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (N H : Subgroup G) (rho : Representation K G V)
    (hfrob : IsFrobeniusGroupWithKernelComplement N H)
    (hchar : ¬ ringChar K ∣ Nat.card N)
    (hfixedN : rho.fixedSubspace N = (⊥ : Submodule K V)) :
    (exists (iota : Type) (instFintype : Fintype iota) (instAction : MulAction H iota),
      letI : Fintype iota := instFintype
      letI : MulAction H iota := instAction
      exists b : Module.Basis iota K V,
        (forall h : H, forall i : iota, rho (h : G) (b i) = b (h • i)) ∧
          (forall i : iota, Nat.card (MulAction.orbit H i) = Nat.card H)) ∧
      (forall H0 : Subgroup H,
        Module.finrank K (Representation.fixedSubspace (rho.comp H.subtype) H0) =
          H0.index * Module.finrank K (rho.fixedSubspace H)) := by
  obtain ⟨alpha, hfinite, ⟨e⟩⟩ :=
    isaacs_15_16_restrict_equiv_free N H rho hfrob hchar hfixedN
  letI : Finite alpha := hfinite
  simpa [Representation.fixedSubspace] using
    (isaacs_15_16_of_repEquiv_free (rho.comp H.subtype) e)

end XV
end Isaacs
end External
end CFSG.BenderSuzuki
