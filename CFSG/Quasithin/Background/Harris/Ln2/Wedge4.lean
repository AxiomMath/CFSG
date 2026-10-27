module

public import CFSG.Quasithin.Background.Harris.Ln2.Basic
public import CFSG.Quasithin.Background.Harris.Ln2.Wedge4Quad
public import CFSG.Quasithin.Background.P4InspOrthA8
public import CFSG.Quasithin.Background.SmithB42LnL4Models
public import CFSG.Quasithin.Background.G116IISL42
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Quasithin.Background.G116IIInputs
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.OneCompActions
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Base
public import CFSG.Quasithin.Background.SmithB42LnBase
public import CFSG.Quasithin.Background.SmithB51LnSub
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.G11.Harris.Ln2

open Matrix CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42Ln CFSG.Quasithin.G11
  CFSG.Quasithin.G11.P4InspOrth

section Transport

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2))

@[expose] def wq (v : V) : ZMod 2 := q6 (β v)

@[expose] def wf : LinearMap.BilinForm (ZMod 2) V :=
  f6.compl₁₂ β.toLinearMap β.toLinearMap

theorem wf_apply (v w : V) : wf β v w = f6 (β v) (β w) := rfl

theorem wq_add (x y : V) : wq β (x + y) = wq β x + wq β y + wf β x y := by
  simp only [wq, wf_apply, map_add]
  exact q6_add _ _

theorem wf_isSymplectic : IsSymplectic (wf β) := by
  refine ⟨fun x => f6_self _, fun x hx => ?_⟩
  apply β.injective
  rw [map_zero]
  apply f6_left_nondeg
  intro y
  simpa [wf_apply] using hx (β.symm y)

theorem finrank_wedge (β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) :
    Module.finrank (ZMod 2) V = 6 := by
  rw [LinearEquiv.finrank_eq β, Module.finrank_fin_fun]

@[expose] def inc36 : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  LinearMap.pi fun i : Fin 6 => if h : i.val < 3 then LinearMap.proj ⟨i, h⟩ else 0

theorem inc36_injective : Function.Injective inc36 := by
  intro x y hxy
  ext ⟨k, hk⟩
  have := congrFun hxy ⟨k, by omega⟩
  simpa [inc36, hk] using this

theorem q6_inc36 (y : Fin 3 → ZMod 2) : q6 (inc36 y) = 0 := by
  simp [q6, inc36]

theorem isPlusType_wq [Finite V] :
    CFSG.GroupTheory.WeirSylow.IsPlusType (p4insporth_quad (f := wf β) (wq_add β)) := by
  refine ⟨Submodule.map β.symm.toLinearMap (LinearMap.range inc36), ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq, LinearMap.finrank_range_of_inj inc36_injective,
      finrank_wedge β, Module.finrank_fin_fun]
  · rintro x ⟨w, ⟨y, rfl⟩, rfl⟩
    show q6 (β (β.symm (inc36 y))) = 0
    rw [LinearEquiv.apply_symm_apply]
    exact q6_inc36 y

end Transport

section Main

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {L : Subgroup (GLV V)}
  {θ : ↥L ≃* CFSG.Quasithin.B42Ln.G4} {β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)}

theorem wedge_apply (h : ActsAs L θ CFSG.Quasithin.B42Ln.wedgeRep4' β) (l : ↥L) (v : V) :
    β ((l : GLV V) v) = wedgeMat4 ((θ l : G4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ β v :=
  h l v

theorem le_orthSub_wq (h : ActsAs L θ CFSG.Quasithin.B42Ln.wedgeRep4' β) : L ≤ orthSub (wq β) := by
  intro g hg x
  show q6 (β (g x)) = q6 (β x)
  rw [wedge_apply h ⟨g, hg⟩ x]
  exact q6_wedgeMat4 _ (Matrix.SpecialLinearGroup.det_coe _) _

noncomputable def mulEquivA8 (θ : ↥L ≃* G4) : ↥L ≃* ↥(alternatingGroup (Fin 8)) :=
  θ.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 4 (ZMod 2)).trans
    sl42IsoA8.some)

theorem isPerfect_of_equivA8 (e : ↥L ≃* ↥(alternatingGroup (Fin 8))) : Group.IsPerfect ↥L := by
  have : Group.IsPerfect ↥(alternatingGroup (Fin 8)) :=
    Group.isPerfect_def.mpr (commutator_alternatingGroup_eq_top (by simp))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

theorem eq_commutator_orthSub (h : ActsAs L θ CFSG.Quasithin.B42Ln.wedgeRep4' β) {φ : ↥⁅orthSub (wq β), orthSub (wq β)⁆
    ≃* ↥(alternatingGroup (Fin 8))} : L = ⁅orthSub (wq β), orthSub (wq β)⁆ := by
  have hle : L ≤ ⁅orthSub (wq β), orthSub (wq β)⁆ :=
    p4insporth_perfect_le (le_orthSub_wq h) (isPerfect_of_equivA8 (mulEquivA8 θ))
  have : Finite ↥⁅orthSub (wq β), orthSub (wq β)⁆ := Finite.of_equiv _ φ.symm.toEquiv
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_congr φ.toEquiv, Nat.card_congr (mulEquivA8 θ).toEquiv]

theorem selfDual_wedge (h : ActsAs L θ CFSG.Quasithin.B42Ln.wedgeRep4' β) :
    SelfDual L ⊤ := by
  have hsymp := wf_isSymplectic β
  have key : ∀ x : ↥(⊤ : Submodule (ZMod 2) V), (∀ y : ↥(⊤ : Submodule (ZMod 2) V), wf β x y = 0) →
      x = 0 := fun x hx =>
    Subtype.ext (hsymp.2 x fun y => hx ⟨y, trivial⟩)
  refine ⟨(wf β).compl₁₂ (Submodule.subtype ⊤) (Submodule.subtype ⊤), ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    exact key x hx
  · intro y hy
    refine key y fun x => ?_
    have := hy x
    simpa [wf_apply, f6_comm] using this
  · intro k hk i j i' j' hi hj
    show wf β (i' : V) (j' : V) = wf β (i : V) (j : V)
    rw [wf_apply, wf_apply, ← hi, ← hj, wedge_apply h ⟨k, hk⟩, wedge_apply h ⟨k, hk⟩]
    exact f6_wedgeMat4 _ (Matrix.SpecialLinearGroup.det_coe _) _ _

end Main

set_option linter.unusedVariables false in
theorem wedge4_concl {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {L : Subgroup (GLV V)} (hL : IsIrr L ⊤) (θ : ↥L ≃* CFSG.Quasithin.B42Ln.G4)
    (β : V ≃ₗ[ZMod 2] (Fin 6 → ZMod 2)) (h : ActsAs L θ CFSG.Quasithin.B42Ln.wedgeRep4' β) :
    IsPermCoreModule L (alternatingGroup (Fin 8)) ∧ SelfDual L ⊤ := by
  refine ⟨?_, selfDual_wedge h⟩
  have hcore := (p4insporth_plus_six (wf_isSymplectic β) (wq_add β) (finrank_wedge β)
    (isPlusType_wq β)).2
  obtain ⟨φ, -⟩ := id hcore
  rw [eq_commutator_orthSub h (φ := φ)]
  exact hcore

end CFSG.Quasithin.G11.Harris.Ln2
