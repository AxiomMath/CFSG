/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import CFSG.LieType.AlgebraicGroups.CommutativeReductiveDiagonalizable
public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple
public import TauCeti.Algebra.AlgebraicGroup.Representation.JordanDecomposition.Commuting
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Basic
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Image.Smooth
public import TauCeti.Algebra.Bialgebra.GroupLike.Torsion
public import TauCeti.Algebra.AlgebraicGroup.Solvable.LieKolchin
public import TauCeti.LinearAlgebra.Eigenspace.JointEigenvector.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Weight.Vector
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointSeparation
public import TauCeti.Algebra.AlgebraicGroup.Torus.Maximal
public import TauCeti.Algebra.AlgebraicGroup.Torus.AlgebraicallyClosed
public import TauCeti.Algebra.AlgebraicGroup.Torus.Characterization

/-!
# Semisimple points of connected commutative affine groups

The semisimple Jordan projection of a reduced commutative affine group is a regular
Hopf endomorphism. Its image is a torus when the group is connected, and contains the
original semisimple points. It is the unique maximal torus.

The construction of the regular endomorphism and its closed image is adapted from
TauCeti commit `c160684bdc6e37018f3010604f9c0837be53d574`, Apache-2.0, files
`Representation/JordanDecomposition/{Commutative,ClosedFactors,MaximalTorus}.lean`.
The weight calculation is replaced by the existing repository result
`CommutativeReductive.exists_groupLike_eval`, so no weight-space theory is duplicated.
At the CFSG pin, point precomposition uses `TauCeti.AlgHom.mapDomain`; image connectedness
uses the injective image factor, and torus recognition uses the existing torsion-free
character-group equivalence. The kernel/image construction and the original point are
unchanged mathematically.

The shared `RegularJordan` lemmas require actual coordinate regularity and multiplicativity
of the semisimple map. `CommutativeJordan` proves these in the commutative case, preserving
its original theorem types. `CentralJordan` proves them for a connected solvable group whose
semisimple parts are central; `NilpotentSemisimple` supplies that centrality unconditionally
for connected nilpotent groups. The generalized image proofs are shared rather than copied.

This is the commutative case used in the connected-solvable step of semisimple point
containment (Springer 6.3.5(i), then 6.4.5(ii)). It supplies the commutative branch of
native Borel maximal-torus conjugacy; general point containment remains separate.

## References

* T. A. Springer, *Linear Algebraic Groups*, 2nd ed. (1998), Theorem 3.1.1,
  Corollary 3.1.2 and Theorem 6.3.5(i).
* A. Borel, *Linear Algebraic Groups*, 2nd ed. (1991), Theorem 4.7.
-/

public noncomputable section
open TauCeti WithConv
open scoped TensorProduct
open scoped commutatorElement
namespace CFSG.ThirdParty.TauCeti.CommutativeJordan
universe u
variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]

omit [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H] in
/-- A coordinate character has the same value on a point and its semisimple part. -/
theorem semisimplePart_apply_of_isGroupLikeElem (g : WithConv (H →ₐ[k] k)) {c : H}
    (hc : IsGroupLikeElem k c) :
    (HopfAlgebra.Point.semisimplePart k H k g).ofConv c = g.ofConv c := by
  have h := HopfAlgebra.Point.semisimplePart_mapDomain
    (TauCeti.GroupLike.evaluationBialgHom k H) g
  rw [DiagonalizableGroup.semisimplePart_eq_self] at h
  have h' := congrArg (fun p ↦ p.ofConv
    (MonoidAlgebra.single (⟨c, hc⟩ : GroupLike k H) (1 : k) : MonoidAlgebra k (GroupLike k H))) h
  simp only [TauCeti.AlgHom.mapDomain_apply, ofConv_toConv, AlgHom.comp_apply] at h'
  simpa [TauCeti.GroupLike.evaluationBialgHom_single] using h'.symm

/-- Every coordinate function on semisimple parts is a finite linear combination of characters. -/
theorem exists_mem_groupLikeSetSpan_forall_apply_eq (a : H) :
    ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
      ∀ g : WithConv (H →ₐ[k] k),
        g.ofConv h = (HopfAlgebra.Point.semisimplePart k H k g).ofConv a := by
  obtain ⟨N, hNfin, ha⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) a
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let _ : Module.Finite k N := hNfin
  have hv : (⟨a, ha⟩ : N) ∈ ⨆ χ,
      CFSG.LieType.AlgebraicGroups.CommutativeReductive.genWeightSpace (K := k) (B := H) (V := N) χ := by
    rw [CFSG.LieType.AlgebraicGroups.CommutativeReductive.iSup_genWeightSpace]
    exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun v : N ↦
      ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
        ∀ g : WithConv (H →ₐ[k] k),
          g.ofConv h = (HopfAlgebra.Point.semisimplePart k H k g).ofConv (v : H))
    hv (fun χ v hv ↦ ?_) ⟨0, zero_mem _, fun g ↦ by simp⟩
    (fun v w ⟨a, ha, hga⟩ ⟨b, hb, hgb⟩ ↦
      ⟨a + b, add_mem ha hb, fun g ↦ by simp [hga, hgb]⟩)
  obtain ⟨c, hc, heval⟩ := CFSG.LieType.AlgebraicGroups.CommutativeReductive.exists_groupLike_eval N χ
  refine ⟨(1 : WithConv (H →ₐ[k] k)).ofConv (v : H) • c,
    Submodule.smul_mem _ _ (Subcoalgebra.groupLike_mem_groupLikeSetSpan
      (R := k) (C := H) (Set.mem_univ (⟨c, hc⟩ : GroupLike k H))), fun g ↦ ?_⟩
  have hsem := heval (HopfAlgebra.Point.semisimplePart k H k g) v hv
  have hu : HopfAlgebra.Point.unipotentPart k H k
      (HopfAlgebra.Point.semisimplePart k H k g) = 1 :=
    HopfAlgebra.Point.unipotentPart_eq_one_of_isSemisimple k H k
      (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k H k g)
  rw [hu, semisimplePart_apply_of_isGroupLikeElem g hc] at hsem
  simpa [mul_comm] using hsem.symm


end CFSG.ThirdParty.TauCeti.CommutativeJordan

namespace CFSG.ThirdParty.TauCeti.CentralJordan
universe u
variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]

omit [IsAlgClosed k] in
/-- A semisimple point acts semisimply on the original base-field comodule. -/
theorem isSemisimple_basePointsRepresentation
    (g : WithConv (H →ₐ[k] k)) (hg : HopfAlgebra.IsSemisimplePoint g)
    (V : Type u) [AddCommGroup V] [Module k V] [Comodule k H V] [Module.Finite k V] :
    (Comodule.basePointsRepresentation (R := k) (H := H) V g).IsSemisimple := by
  have hs := (HopfAlgebra.isSemisimplePoint_iff_forall_isSemisimple_endOfPoint g).mp hg
    (FGComoduleCat.of (R := k) (C := H) V)
  let e := TensorProduct.lid k V
  have hcomm : e.symm.toLinearMap ∘ₗ Comodule.basePointsRepresentation (R := k) (H := H) V g =
      Comodule.endOfPoint V g.ofConv ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    dsimp only [e]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.lid_symm_apply]
    rw [Comodule.endOfPoint_tmul, one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]

  exact (LinearEquiv.isSemisimple_iff
    (Comodule.basePointsRepresentation (R := k) (H := H) V g)
    (Comodule.endOfPoint V g.ofConv) e.symm hcomm).mpr hs

section CentralParts
variable [Algebra.FiniteType k H] [IsReduced H] [ConnectedSpace (PrimeSpectrum H)]
  [Group.IsSolvable (WithConv (H →ₐ[k] k))]

/-- Central semisimple parts act on each common eigenspace through a coordinate character. -/
theorem iSup_iInf_eigenspace_semisimplePart_eq_top
    (hcentral : ∀ g x : WithConv (H →ₐ[k] k),
      Commute (HopfAlgebra.Point.semisimplePart k H k g) x)
    (V : Type u) [AddCommGroup V] [Module k V] [Comodule k H V] [Module.Finite k V] :
    (⨆ c : GroupLike k H, ⨅ g : WithConv (H →ₐ[k] k),
      (Comodule.basePointsRepresentation (R := k) (H := H) V
        (HopfAlgebra.Point.semisimplePart k H k g)).eigenspace (g.ofConv c)) = ⊤ := by
  classical
  let ρ := Comodule.basePointsRepresentation (R := k) (H := H) V
  let F := fun g : WithConv (H →ₐ[k] k) ↦ ρ (HopfAlgebra.Point.semisimplePart k H k g)
  have hss : ∀ g, (F g).IsSemisimple := fun g ↦ isSemisimple_basePointsRepresentation _
    ((HopfAlgebra.isSemisimplePoint_def _).mpr
      (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k H k g)) V
  rw [eq_top_iff, ← TauCeti.iSup_iInf_eigenspace_eq_top_of_isSemisimple F
    (fun g h _ ↦ (hcentral g (HopfAlgebra.Point.semisimplePart k H k h)).map ρ) hss]
  refine iSup_le fun χ ↦ ?_
  by_cases hbot : (⨅ g, (F g).eigenspace (χ g)) = ⊥
  · rw [hbot]; exact bot_le
  set E := ⨅ g, (F g).eigenspace (χ g)
  have hstable : ∀ x : WithConv (H →ₐ[k] k), ∀ v ∈ E, ρ x v ∈ E := by
    intro x v hv
    simp only [E,Submodule.mem_iInf,Module.End.mem_eigenspace_iff] at hv ⊢
    intro g
    calc F g (ρ x v) = ρ x (F g v) := LinearMap.congr_fun ((hcentral g x).map ρ).eq v
      _ = χ g • ρ x v := by rw [hv g,map_smul]
  let W : Subcomodule k H V := Subcomodule.ofEndOfPointStable (K := k) E (by
    intro g v hv
    rw [Comodule.endOfPoint_tmul,one_smul,
      Comodule.endOfPoint_one_tmul_eq_one_tmul_basePointsRepresentation]
    exact Submodule.tmul_mem_baseChange_of_mem _ (hstable (toConv g) v hv))
  have hW : W.toSubmodule = E := Subcomodule.ofEndOfPointStable_toSubmodule _ _
  let : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k W := Module.Finite.of_injective (SMulMemClass.subtype W)
    (fun a b h ↦ Subtype.ext h)
  let : Nontrivial W := by
    obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hvW : v ∈ W := by change v ∈ W.toSubmodule; rw [hW]; exact hv
    exact ⟨⟨⟨v,hvW⟩,0,fun h ↦ hv0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨w,c,hw,hc,hcoact⟩ := TauCeti.Comodule.hasNonzeroWeightVector_iff.mp
    (TauCeti.Comodule.hasNonzeroWeightVector_of_isSolvable (k := k) (H := H) (M := W))
  have hwV : (w : V) ≠ 0 := fun h ↦ hw (Subtype.ext h)
  have hweight (g : WithConv (H →ₐ[k] k)) : ρ g w = g.ofConv c • (w : V) := by
    rw [← CFSG.LieType.AlgebraicGroups.CommutativeReductive.coe_basePointsRepresentation_subcomodule,
      CFSG.LieType.AlgebraicGroups.CommutativeReductive.basePointsRepresentation_eq_smul_of_coact_eq_tmul g hcoact]
    rfl
  have heigen (g : WithConv (H →ₐ[k] k)) : F g w = χ g • (w : V) := by
    have hwE : (w : V) ∈ E := by
      rw [← hW]; exact w.2
    exact Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hwE g)
  have hχ (g : WithConv (H →ₐ[k] k)) : χ g = g.ofConv c := by
    have h := hweight (HopfAlgebra.Point.semisimplePart k H k g)
    rw [CommutativeJordan.semisimplePart_apply_of_isGroupLikeElem g hc] at h
    exact smul_left_injective k hwV ((heigen g).symm.trans h)
  refine le_trans ?_ (le_iSup _ (⟨c,hc⟩ : GroupLike k H))
  simp only [hχ,E,F,ρ,le_refl]
/-- If semisimple parts are central in a connected solvable group, their coordinate functions are regular combinations of characters. -/
theorem exists_mem_groupLikeSetSpan_forall_apply_eq
    (hcentral : ∀ g x : WithConv (H →ₐ[k] k),
      Commute (HopfAlgebra.Point.semisimplePart k H k g) x)
    (a : H) :
    ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
      ∀ g : WithConv (H →ₐ[k] k), g.ofConv h = (HopfAlgebra.Point.semisimplePart k H k g).ofConv a := by
  have hcoeff : ∀ (V : Type u) [AddCommGroup V] [Module k V] [Comodule k H V] [Module.Finite k V]
      (φ : Module.Dual k V) (v : V),
      ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
        ∀ g : WithConv (H →ₐ[k] k), g.ofConv h =
          (HopfAlgebra.Point.semisimplePart k H k g).ofConv (Comodule.matrixCoefficient (C := H) φ v) := by
    intro V _ _ _ _ φ v
    have hv : v ∈ ⨆ c : GroupLike k H, ⨅ g : WithConv (H →ₐ[k] k),
        (Comodule.basePointsRepresentation (R := k) (H := H) V
          (HopfAlgebra.Point.semisimplePart k H k g)).eigenspace (g.ofConv c) := by
      rw [iSup_iInf_eigenspace_semisimplePart_eq_top hcentral]; exact Submodule.mem_top
    refine Submodule.iSup_induction _ (motive := fun x ↦
      ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
        ∀ g : WithConv (H →ₐ[k] k), g.ofConv h =
          (HopfAlgebra.Point.semisimplePart k H k g).ofConv (Comodule.matrixCoefficient (C := H) φ x))
      hv (fun c x hx ↦ ?_) ⟨0,zero_mem _,fun g ↦ by simp⟩
      (fun x y ⟨a,ha,hxa⟩ ⟨b,hb,hyb⟩ ↦ ⟨a+b,add_mem ha hb,fun g ↦ by simp [hxa,hyb]⟩)
    refine ⟨φ x • (c : H),Submodule.smul_mem _ _
      (Subcoalgebra.groupLike_mem_groupLikeSetSpan (Set.mem_univ c)),fun g ↦ ?_⟩
    rw [Comodule.apply_matrixCoefficient,
      Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp hx g)]
    simp [mul_comm]
  obtain ⟨N,hNfin,ha⟩ := Subcomodule.exists_finite_subcomodule_mem (R := k) (C := H) (M := H) a
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup k
  let : Module.Finite k N := hNfin
  simpa only [Comodule.matrixCoefficient_counit_comp_subtype] using hcoeff N
    ((Coalgebra.counit (R := k) (A := H)).comp (SMulMemClass.subtype N)) ⟨a,ha⟩

/-- The regular semisimple-part map with central image is multiplicative, since characters distinguish its values. -/
theorem semisimplePart_mul_of_central_parts
    (hcentral : ∀ g x : WithConv (H →ₐ[k] k),
      Commute (HopfAlgebra.Point.semisimplePart k H k g) x)
    (g h : WithConv (H →ₐ[k] k)) :
    HopfAlgebra.Point.semisimplePart k H k (g*h) =
      HopfAlgebra.Point.semisimplePart k H k g * HopfAlgebra.Point.semisimplePart k H k h := by
  let sg := HopfAlgebra.Point.semisimplePart k H k g
  let sh := HopfAlgebra.Point.semisimplePart k H k h
  have hssg : HopfAlgebra.IsSemisimplePoint sg := (HopfAlgebra.isSemisimplePoint_def _).mpr
    (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k H k g)
  have hssh : HopfAlgebra.IsSemisimplePoint sh := (HopfAlgebra.isSemisimplePoint_def _).mpr
    (HopfAlgebra.Point.isSemisimple_pointsAction_semisimplePart k H k h)
  have hss : HopfAlgebra.IsSemisimplePoint (sg*sh) := hssg.mul_of_commute hssh (hcentral g sh)
  let π := TauCeti.AlgHom.mapDomain (A := k) (TauCeti.GroupLike.evaluationBialgHom k H)
  have hgπ : π sg = π g := by
    exact (HopfAlgebra.Point.semisimplePart_mapDomain
      (TauCeti.GroupLike.evaluationBialgHom k H) g).symm.trans
      (DiagonalizableGroup.semisimplePart_eq_self (π g))
  have hhπ : π sh = π h := by
    exact (HopfAlgebra.Point.semisimplePart_mapDomain
      (TauCeti.GroupLike.evaluationBialgHom k H) h).symm.trans
      (DiagonalizableGroup.semisimplePart_eq_self (π h))
  have hπ : π (sg*sh) = π (g*h) := by rw [map_mul,map_mul,hgπ,hhπ]
  have hchar (c : GroupLike k H) : (sg*sh).ofConv c = (g*h).ofConv c := by
    have h := congrArg (fun p ↦ p.ofConv (MonoidAlgebra.single c (1 : k))) hπ
    simpa [π,TauCeti.AlgHom.mapDomain_apply,TauCeti.GroupLike.evaluationBialgHom_single] using h
  apply WithConv.ext
  ext a
  obtain ⟨b,hb,hval⟩ := exists_mem_groupLikeSetSpan_forall_apply_eq hcentral a
  have hbval : (sg*sh).ofConv b = (g*h).ofConv b := by
    rw [Subcoalgebra.mem_groupLikeSetSpan] at hb
    refine LinearMap.eqOn_span (f := (sg*sh).ofConv.toLinearMap)
      (g := (g*h).ofConv.toLinearMap) ?_ hb
    rintro _ ⟨c,_,rfl⟩
    exact hchar c
  have hfix : HopfAlgebra.Point.semisimplePart k H k (sg*sh) = sg*sh :=
    HopfAlgebra.Point.semisimplePart_eq_self k H k ((HopfAlgebra.isSemisimplePoint_def _).mp hss)
  rw [← hval (g*h),← hbval,hval (sg*sh),hfix]


end CentralParts

end CFSG.ThirdParty.TauCeti.CentralJordan

namespace CFSG.ThirdParty.TauCeti.RegularJordan
universe u
variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H]

variable
    (hregular : ∀ a : H,
      ∃ h ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ,
        ∀ g : WithConv (H →ₐ[k] k),
          g.ofConv h = (HopfAlgebra.Point.semisimplePart k H k g).ofConv a)
    (hmul : ∀ g h : WithConv (H →ₐ[k] k),
      HopfAlgebra.Point.semisimplePart k H k (g * h) =
        HopfAlgebra.Point.semisimplePart k H k g * HopfAlgebra.Point.semisimplePart k H k h)

private def semisimplePartFun (a : H) : H :=
  (hregular a).choose

omit [Algebra.FiniteType k H] [IsReduced H] hmul in
private theorem apply_semisimplePartFun (g : WithConv (H →ₐ[k] k)) (a : H) :
    g.ofConv (semisimplePartFun (k := k) hregular a) = (HopfAlgebra.Point.semisimplePart k H k g).ofConv a :=
  (hregular a).choose_spec.2 g

private def semisimplePartAlgHom : H →ₐ[k] H where
  toFun := semisimplePartFun (k := k) hregular
  map_one' := eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ by
    rw [apply_semisimplePartFun hregular (toConv g), map_one, map_one]
  map_mul' a b := eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ by
    rw [apply_semisimplePartFun hregular (toConv g), map_mul, map_mul,
      apply_semisimplePartFun hregular (toConv g), apply_semisimplePartFun hregular (toConv g)]
  map_zero' := eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ by
    rw [apply_semisimplePartFun hregular (toConv g), map_zero, map_zero]
  map_add' a b := eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ by
    rw [apply_semisimplePartFun hregular (toConv g), map_add, map_add,
      apply_semisimplePartFun hregular (toConv g), apply_semisimplePartFun hregular (toConv g)]
  commutes' r := eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ by
    rw [apply_semisimplePartFun hregular (toConv g), AlgHom.commutes, AlgHom.commutes]

private theorem toConv_comp_semisimplePartAlgHom (g : WithConv (H →ₐ[k] k)) :
    toConv (g.ofConv.comp (semisimplePartAlgHom (k := k) (H := H) hregular)) =
      HopfAlgebra.Point.semisimplePart k H k g := by
  apply WithConv.ofConv_injective
  ext a
  exact apply_semisimplePartFun hregular g a

/-- The regular semisimple Jordan projection of a reduced affine affine group. -/
def semisimplePartBialgHom : H →ₐc[k] H :=
  BialgHom.ofAlgHom (semisimplePartAlgHom (k := k) (H := H) hregular)
    (by
      ext a
      have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv a)
        (toConv_comp_semisimplePartAlgHom (k := k) (H := H) hregular 1)
      simpa [HopfAlgebra.Point.semisimplePart_one] using h)
    (by
      ext a
      let _ : Algebra.FiniteType k (H ⊗[k] H) :=
        FiniteTypeCommHopfAlgCat.tensorProduct_finiteType (R := k) H H
      refine eq_of_forall_algHom_apply_eq (k := k) (A := H ⊗[k] H) (K := k) fun φ ↦ ?_
      let g : WithConv (H →ₐ[k] k) := toConv (φ.comp Algebra.TensorProduct.includeLeft)
      let h : WithConv (H →ₐ[k] k) := toConv (φ.comp Algebra.TensorProduct.includeRight)
      have hφ : φ = Algebra.TensorProduct.lift g.ofConv h.ofConv (fun _ _ ↦ .all _ _) :=
        Algebra.TensorProduct.ext (by ext; simp [g]) (by ext; simp [h])
      have hσ : φ.comp (Algebra.TensorProduct.map (semisimplePartAlgHom (k := k) (H := H) hregular) (semisimplePartAlgHom (k := k) (H := H) hregular)) =
          Algebra.TensorProduct.lift (g.ofConv.comp (semisimplePartAlgHom (k := k) (H := H) hregular))
            (h.ofConv.comp (semisimplePartAlgHom (k := k) (H := H) hregular)) (fun _ _ ↦ .all _ _) :=
        Algebra.TensorProduct.ext (by ext; simp [g]) (by ext; simp [h])
      have hl : φ (Algebra.TensorProduct.map (semisimplePartAlgHom (k := k) (H := H) hregular) (semisimplePartAlgHom (k := k) (H := H) hregular)
          (Coalgebra.comul (R := k) a)) =
          (HopfAlgebra.Point.semisimplePart k H k (g * h)).ofConv a := by
        rw [hmul g h,
          ← toConv_comp_semisimplePartAlgHom hregular, ← toConv_comp_semisimplePartAlgHom hregular,
          AlgHom.convMul_apply, ← hσ, AlgHom.comp_apply]
      have hr : φ (Coalgebra.comul (R := k) (semisimplePartAlgHom (k := k) hregular a)) =
          (HopfAlgebra.Point.semisimplePart k H k (g * h)).ofConv a := by
        change φ (Coalgebra.comul (R := k) (semisimplePartFun (k := k) hregular a)) = _
        rw [← apply_semisimplePartFun (k := k) hregular, AlgHom.convMul_apply, ← hφ]
      simpa [Bialgebra.comulAlgHom_apply] using hl.trans hr.symm)

/-- The regular projection sends each base-field point to its original semisimple part. -/
theorem mapDomain_semisimplePartBialgHom (g : WithConv (H →ₐ[k] k)) :
    TauCeti.AlgHom.mapDomain (semisimplePartBialgHom (k := k) (H := H) hregular hmul) g =
      HopfAlgebra.Point.semisimplePart k H k g := by
  exact toConv_comp_semisimplePartAlgHom hregular g

/-- The regular projection takes values in the span of the coordinate characters. -/
theorem semisimplePartBialgHom_mem_groupLikeSetSpan (a : H) :
    semisimplePartBialgHom (k := k) (H := H) hregular hmul a ∈
      Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ :=
  (hregular a).choose_spec.1

/-- The regular projection fixes every character. -/
theorem semisimplePartBialgHom_apply_of_isGroupLikeElem {c : H} (hc : IsGroupLikeElem k c) :
    semisimplePartBialgHom (k := k) (H := H) hregular hmul c = c := by
  refine eq_of_forall_algHom_apply_eq (k := k) (K := k) fun g ↦ ?_
  exact (apply_semisimplePartFun hregular (toConv g) c).trans
    (CFSG.ThirdParty.TauCeti.CommutativeJordan.semisimplePart_apply_of_isGroupLikeElem (toConv g) hc)

/-- The regular projection fixes the whole span of characters. -/
theorem semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan {a : H}
    (ha : a ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ) :
    semisimplePartBialgHom (k := k) (H := H) hregular hmul a = a := by
  rw [Subcoalgebra.mem_groupLikeSetSpan] at ha
  refine LinearMap.eqOn_span
    (f := (semisimplePartBialgHom (k := k) (H := H) hregular hmul : H →ₗ[k] H)) (g := LinearMap.id) ?_ ha
  rintro _ ⟨c, -, rfl⟩
  exact semisimplePartBialgHom_apply_of_isGroupLikeElem hregular hmul c.isGroupLikeElem_val

/-- The regular semisimple projection is idempotent. -/
theorem semisimplePartBialgHom_comp_self :
    (semisimplePartBialgHom (k := k) (H := H) hregular hmul).comp (semisimplePartBialgHom (k := k) (H := H) hregular hmul) =
      semisimplePartBialgHom (k := k) (H := H) hregular hmul := by
  ext a
  exact semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan hregular hmul
    (semisimplePartBialgHom_mem_groupLikeSetSpan hregular hmul a)

open CategoryTheory
/-- The actual closed image of the regular semisimple projection. -/
abbrev semisimpleImage : _root_.CommHopfAlgCat.{u} k :=
  TauCeti.CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom
    (semisimplePartBialgHom (k := k) (H := H) hregular hmul))

/-- Characters span the coordinate ring of the actual semisimple image. -/
theorem groupLikeSetSpan_semisimpleImage_eq_top :
    Subcoalgebra.groupLikeSetSpan (R := k) (C := semisimpleImage (k := k) (H := H) hregular hmul) Set.univ = ⊤ := by
  let Q := semisimpleImage (k := k) (H := H) hregular hmul
  let f := _root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom (k := k) (H := H) hregular hmul)
  let q := TauCeti.CommHopfAlgCat.mkImage f
  have hqi (a : H) :
      (TauCeti.CommHopfAlgCat.imageι f).hom
        (q.hom (semisimplePartBialgHom (k := k) (H := H) hregular hmul a)) =
      (TauCeti.CommHopfAlgCat.imageι f).hom (q.hom a) := by
    rw [TauCeti.CommHopfAlgCat.imageι_mkImage_apply,
      TauCeti.CommHopfAlgCat.imageι_mkImage_apply]
    exact DFunLike.congr_fun (semisimplePartBialgHom_comp_self (k := k) (H := H) hregular hmul) a
  have hqa (a : H) : q.hom (semisimplePartBialgHom (k := k) (H := H) hregular hmul a) = q.hom a :=
    TauCeti.CommHopfAlgCat.imageι_injective f (hqi a)
  apply top_unique
  intro x hx
  obtain ⟨a, rfl⟩ := TauCeti.CommHopfAlgCat.mkImage_surjective f x
  rw [← hqa a]
  have ha := semisimplePartBialgHom_mem_groupLikeSetSpan (k := k) (H := H) hregular hmul a
  rw [Subcoalgebra.mem_groupLikeSetSpan] at ha ⊢
  simp only [Set.image_univ] at ha ⊢
  refine Submodule.span_induction (p := fun y _ ↦ q.hom y ∈
    Submodule.span k (Set.range (_root_.GroupLike.val (R := k) (A := Q))))
    (fun y hy ↦ ?_) (by simp) (fun y z _ _ hy hz ↦ by simpa using Submodule.add_mem _ hy hz)
    (fun r y _ hy ↦ by simpa using Submodule.smul_mem _ r hy) ha
  obtain ⟨c, rfl⟩ := hy
  exact Submodule.subset_span ⟨⟨q.hom c, c.isGroupLikeElem_val.map q.hom⟩, rfl⟩

/-- The semisimple image of a connected affine affine group is a torus. -/
theorem torus_semisimpleImage
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k
      (semisimpleImage (k := k) (H := H) hregular hmul)) := by
  let Q := FiniteTypeCommHopfAlgCat.of k (semisimpleImage (k := k) (H := H) hregular hmul)
  let f := _root_.CommHopfAlgCat.ofHom (semisimplePartBialgHom (k := k) (H := H) hregular hmul)
  have hQ : geometricallyConnectedCommHopfAlgProperty k Q.obj :=
    geometricallyConnectedCommHopfAlgProperty.of_injective
      (TauCeti.CommHopfAlgCat.imageι f).hom.toAlgHom
      (TauCeti.CommHopfAlgCat.imageι_injective f) hc
  have hsm : smoothCommHopfAlgProperty k Q.obj := smoothCommHopfAlgProperty.image f
    (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k (_root_.CommHopfAlgCat.of k H))
  let : IsReduced Q := ((smoothCommHopfAlgProperty_iff_isReduced_of_isAlgClosed k Q.obj).mp hsm)
  let : ConnectedSpace (PrimeSpectrum Q) := hQ.connectedSpace k Q.obj
  let : Group.FG (_root_.GroupLike k Q) :=
    TauCeti.GroupLike.fg_of_finiteType_of_groupLikeSetSpan_eq_top k Q
      inferInstance (groupLikeSetSpan_semisimpleImage_eq_top (k := k) (H := H) hregular hmul)
  let : IsMulTorsionFree (_root_.GroupLike k Q) :=
    isMulTorsionFree_groupLike_of_isReduced_of_connectedSpace k Q
  let G := FGCommGrpCat.of (_root_.GroupLike k Q)
  have hspan := (Subcoalgebra.groupLikeSetSpan_eq_top_iff_span_eq_top (R := k) (C := Q)).mp
    (groupLikeSetSpan_semisimpleImage_eq_top (k := k) (H := H) hregular hmul)
  let e : (DiagonalizableGroup.coordinateRing k G).obj ≅ Q.obj :=
    _root_.CommHopfAlgCat.isoMk (TauCeti.GroupLike.evaluationBialgEquiv k Q hspan) ≪≫
      _root_.CommHopfAlgCat.ofIsoSelf Q.obj
  exact splitTorusCommHopfAlgProperty.torus k Q
    ((splitTorusCommHopfAlgProperty k).prop_of_iso
      (ObjectProperty.isoMk (finiteTypeCommHopfAlgProperty k) e)
      (splitTorusCommHopfAlgProperty_coordinateRing k G))

/-- Each original semisimple point lies in the actual closed semisimple image. -/
theorem semisimplePoint_mem_semisimpleImage (g : WithConv (H →ₐ[k] k))
    (hg : HopfAlgebra.IsSemisimplePoint g) :
    g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H) hregular hmul)) (CommAlgCat.of k k) := by
  apply (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
  intro a ha
  have hgfix : TauCeti.AlgHom.mapDomain (semisimplePartBialgHom (k := k) (H := H) hregular hmul) g = g := by
    rw [mapDomain_semisimplePartBialgHom hregular hmul]
    exact HopfAlgebra.Point.semisimplePart_eq_self k H k ((HopfAlgebra.isSemisimplePoint_def g).mp hg)
  rw [HopfIdeal.mem_ker] at ha
  have h := congrArg (fun p : WithConv (H →ₐ[k] k) ↦ p.ofConv a) hgfix
  simpa [TauCeti.AlgHom.mapDomain_apply, ha] using h.symm

include hregular hmul in
/-- A semisimple point of a connected affine group lies in a torus of that same group. -/
theorem exists_torus_of_regular_semisimplePart
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (g : WithConv (H →ₐ[k] k)) (hg : HopfAlgebra.IsSemisimplePoint g) :
    ∃ J : HopfIdeal k H,
      torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k H) J) ∧
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        J (CommAlgCat.of k k) :=
  ⟨_, torus_semisimpleImage hregular hmul hc, semisimplePoint_mem_semisimpleImage hregular hmul g hg⟩

/-- Every torus closed subgroup is contained in the actual semisimple image. -/
theorem ker_semisimplePartBialgHom_le_of_torus {J : HopfIdeal k H}
    (hJ : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) J)) :
    HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H) hregular hmul) ≤ J := by
  let Q := FiniteTypeCommHopfAlgCat.quotient (FiniteTypeCommHopfAlgCat.of k H) J
  let : IsReduced Q := hJ.geometricallyReduced.isReduced
  intro a ha
  change a ∈ J.toIdeal
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply eq_of_forall_algHom_apply_eq (k := k) (K := k)
  intro g
  have hg : HopfAlgebra.IsSemisimplePoint (toConv g) := by
    obtain ⟨n, ⟨e⟩⟩ := (splitTorusCommHopfAlgProperty_iff k Q).mp (hJ.split k Q)
    let b := _root_.CommHopfAlgCat.ofIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u,u} k) (_root_.CommHopfAlgCat.{u} k)).mapIso e)
    let z := TauCeti.AlgHom.mapDomain (A := k) b.toBialgHom (toConv g)
    have hz : TauCeti.AlgHom.mapDomain (A := k) b.symm.toBialgHom z = toConv g := by
      apply WithConv.ext
      ext a
      exact congrArg g (b.apply_symm_apply a)
    rw [← hz]
    exact (DiagonalizableGroup.isSemisimplePoint z).mapDomain b.symm.toBialgHom
  have h := semisimplePoint_mem_semisimpleImage hregular hmul
    (TauCeti.CommHopfAlgCat.quotientPointsHom (_root_.CommHopfAlgCat.of k H) J
      (CommAlgCat.of k k) (toConv g))
    (hg.mapDomain (TauCeti.CommHopfAlgCat.mkQuotient (_root_.CommHopfAlgCat.of k H) J).hom)
  have hz := (TauCeti.CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mp h a ha
  change g (Ideal.Quotient.mk J.toIdeal a) = 0 at hz
  simpa using hz

/-- The semisimple image is a maximal torus of the original connected affine group. -/
theorem isMaximalTorus_semisimpleImage
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H) hregular hmul)) := by
  exact (HopfIdeal.isMaximalTorus_iff k _ _).mpr
    ⟨torus_semisimpleImage hregular hmul hc, fun J hJ _ ↦ ker_semisimplePartBialgHom_le_of_torus hregular hmul hJ⟩

/-- The semisimple image is the unique maximal torus of a connected affine group. -/
theorem isMaximalTorus_iff_eq_ker_semisimplePartBialgHom
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (J : HopfIdeal k H) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J ↔
      J = HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H) hregular hmul) := by
  refine ⟨fun hJ ↦ ?_, fun heq ↦ heq ▸ isMaximalTorus_semisimpleImage hregular hmul hc⟩
  obtain ⟨hT, hmax⟩ := (HopfIdeal.isMaximalTorus_iff k _ _).mp hJ
  have hle := ker_semisimplePartBialgHom_le_of_torus hregular hmul hT
  exact le_antisymm (hmax _ (torus_semisimpleImage hregular hmul hc) hle) hle

include hregular hmul in
/-- A semisimple point of a connected affine group lies in its unique maximal torus. -/
theorem exists_isMaximalTorus_of_regular_semisimplePart
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (g : WithConv (H →ₐ[k] k)) (hg : HopfAlgebra.IsSemisimplePoint g) :
    ∃ J : HopfIdeal k H,
      HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J ∧
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        J (CommAlgCat.of k k) :=
  ⟨_, isMaximalTorus_semisimpleImage hregular hmul hc, semisimplePoint_mem_semisimpleImage hregular hmul g hg⟩


end CFSG.ThirdParty.TauCeti.RegularJordan


namespace CFSG.ThirdParty.TauCeti.CommutativeJordan
universe u
variable {k H : Type u} [Field k] [IsAlgClosed k] [CommRing H] [_root_.HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H] [Coalgebra.IsCocomm k H]

omit [Algebra.FiniteType k H] [IsReduced H] in
private theorem semisimplePart_mul (g h : WithConv (H →ₐ[k] k)) :
    HopfAlgebra.Point.semisimplePart k H k (g * h) =
      HopfAlgebra.Point.semisimplePart k H k g * HopfAlgebra.Point.semisimplePart k H k h :=
  HopfAlgebra.Point.semisimplePart_mul_of_commute k H k (Commute.all g h)

/-- The regular semisimple Jordan projection of a reduced commutative affine group. -/
def semisimplePartBialgHom : H →ₐc[k] H :=
  RegularJordan.semisimplePartBialgHom
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H))

/-- The regular projection sends each point to its original semisimple part. -/
theorem mapDomain_semisimplePartBialgHom (g : WithConv (H →ₐ[k] k)) :
    TauCeti.AlgHom.mapDomain (semisimplePartBialgHom (k := k) (H := H)) g =
      HopfAlgebra.Point.semisimplePart k H k g :=
  RegularJordan.mapDomain_semisimplePartBialgHom
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) g

/-- The regular projection takes values in the span of characters. -/
theorem semisimplePartBialgHom_mem_groupLikeSetSpan (a : H) :
    semisimplePartBialgHom (k := k) (H := H) a ∈
      Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ :=
  RegularJordan.semisimplePartBialgHom_mem_groupLikeSetSpan
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) a

/-- The regular projection fixes every character. -/
theorem semisimplePartBialgHom_apply_of_isGroupLikeElem {c : H} (hc : IsGroupLikeElem k c) :
    semisimplePartBialgHom (k := k) (H := H) c = c :=
  RegularJordan.semisimplePartBialgHom_apply_of_isGroupLikeElem
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc

/-- The regular projection fixes the span of characters. -/
theorem semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan {a : H}
    (ha : a ∈ Subcoalgebra.groupLikeSetSpan (R := k) (C := H) Set.univ) :
    semisimplePartBialgHom (k := k) (H := H) a = a :=
  RegularJordan.semisimplePartBialgHom_apply_of_mem_groupLikeSetSpan
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) ha

/-- The regular semisimple projection is idempotent. -/
theorem semisimplePartBialgHom_comp_self :
    (semisimplePartBialgHom (k := k) (H := H)).comp
      (semisimplePartBialgHom (k := k) (H := H)) = semisimplePartBialgHom :=
  RegularJordan.semisimplePartBialgHom_comp_self
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H))

/-- The actual closed image of the semisimple projection. -/
abbrev semisimpleImage : _root_.CommHopfAlgCat.{u} k :=
  TauCeti.CommHopfAlgCat.image (_root_.CommHopfAlgCat.ofHom
    (semisimplePartBialgHom (k := k) (H := H)))
/-- Characters span the coordinate ring of the actual semisimple image. -/
theorem groupLikeSetSpan_semisimpleImage_eq_top :
    Subcoalgebra.groupLikeSetSpan (R := k)
      (C := semisimpleImage (k := k) (H := H)) Set.univ = ⊤ :=
  RegularJordan.groupLikeSetSpan_semisimpleImage_eq_top
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H))

/-- The semisimple image of a connected commutative group is a torus. -/
theorem torus_semisimpleImage
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.of k
      (semisimpleImage (k := k) (H := H))) :=
  RegularJordan.torus_semisimpleImage
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc

/-- Each original semisimple point lies in the actual semisimple image. -/
theorem semisimplePoint_mem_semisimpleImage (g : WithConv (H →ₐ[k] k))
    (hg : HopfAlgebra.IsSemisimplePoint g) :
    g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H))) (CommAlgCat.of k k) :=
  RegularJordan.semisimplePoint_mem_semisimpleImage
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) g hg

/-- A semisimple point of a connected commutative group lies in a torus of that group. -/
theorem exists_torus_of_isSemisimplePoint_of_isCocomm
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (g : WithConv (H →ₐ[k] k)) (hg : HopfAlgebra.IsSemisimplePoint g) :
    ∃ J : HopfIdeal k H,
      torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
        (FiniteTypeCommHopfAlgCat.of k H) J) ∧
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        J (CommAlgCat.of k k) :=
  RegularJordan.exists_torus_of_regular_semisimplePart
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc g hg

/-- Every torus closed subgroup lies in the semisimple image. -/
theorem ker_semisimplePartBialgHom_le_of_torus {J : HopfIdeal k H}
    (hJ : torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.quotient
      (FiniteTypeCommHopfAlgCat.of k H) J)) :
    HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H)) ≤ J :=
  RegularJordan.ker_semisimplePartBialgHom_le_of_torus
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hJ

/-- The semisimple image is a maximal torus. -/
theorem isMaximalTorus_semisimpleImage
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H)) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H)
      (HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H))) :=
  RegularJordan.isMaximalTorus_semisimpleImage
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc

/-- The semisimple image is the unique maximal torus. -/
theorem isMaximalTorus_iff_eq_ker_semisimplePartBialgHom
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (J : HopfIdeal k H) :
    HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J ↔
      J = HopfIdeal.ker (semisimplePartBialgHom (k := k) (H := H)) :=
  RegularJordan.isMaximalTorus_iff_eq_ker_semisimplePartBialgHom
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc J

/-- A semisimple point lies in the unique maximal torus of the original connected group. -/
theorem exists_isMaximalTorus_of_isSemisimplePoint_of_isCocomm
    (hc : geometricallyConnectedCommHopfAlgProperty k (_root_.CommHopfAlgCat.of k H))
    (g : WithConv (H →ₐ[k] k)) (hg : HopfAlgebra.IsSemisimplePoint g) :
    ∃ J : HopfIdeal k H,
      HopfIdeal.IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) J ∧
      g ∈ TauCeti.CommHopfAlgCat.quotientPointsSubgroup (_root_.CommHopfAlgCat.of k H)
        J (CommAlgCat.of k k) :=
  RegularJordan.exists_isMaximalTorus_of_regular_semisimplePart
    (exists_mem_groupLikeSetSpan_forall_apply_eq (k := k) (H := H))
    (semisimplePart_mul (k := k) (H := H)) hc g hg

end CFSG.ThirdParty.TauCeti.CommutativeJordan
