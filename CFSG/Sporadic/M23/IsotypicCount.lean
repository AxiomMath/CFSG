module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG

namespace M23

open scoped MonoidAlgebra

section IsotypicCount

variable {I R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

private theorem two_le_ncard_isotypicComponents (S T : Submodule R M)
    [IsSimpleModule R S] [IsSimpleModule R T]
    [Finite (isotypicComponents R M)]
    (hne : ¬ Nonempty (S ≃ₗ[R] T)) :
    2 ≤ (isotypicComponents R M).ncard := by
  rw [show 2 ≤ (isotypicComponents R M).ncard ↔
    1 < (isotypicComponents R M).ncard by omega, Set.one_lt_ncard]
  refine ⟨isotypicComponent R M S, ⟨S, inferInstance, rfl⟩,
    isotypicComponent R M T, ⟨T, inferInstance, rfl⟩, ?_⟩
  intro heq
  apply hne
  have hle : S ≤ isotypicComponent R M S := S.le_isotypicComponent
  exact isIsotypicOfType_submodule_iff.mp
    (IsIsotypicOfType.isotypicComponent R M T) S (hle.trans_eq heq)

end IsotypicCount

section EndRankFour

variable {K R M : Type*} [Field K] [IsAlgClosed K] [Ring R] [Algebra K R]
  [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M]

private theorem finrank_end_simple_eq_one (S : Submodule R M) [IsSimpleModule R S]
    [FiniteDimensional K S] : Module.finrank K (Module.End R S) = 1 := by
  rw [LinearEquiv.finrank_eq
    (LinearEquiv.ofBijective (Algebra.linearMap K (Module.End R S))
      (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed K)).symm]
  exact CommSemiring.finrank_self K

private theorem exists_finrank_end_eq_sum_sq [FiniteDimensional K M]
    [Module.Finite R M] [IsSemisimpleModule R M]
    [Fintype (isotypicComponents R M)] :
    ∃ d : isotypicComponents R M → ℕ,
      (∀ c, 0 < d c) ∧
      Module.finrank K (Module.End R M) = ∑ c, (d c) ^ 2 := by
  classical
  choose d pos S hle simple e using fun c : isotypicComponents R M ↦
    (IsIsotypic.isotypicComponents c.2).submodule_linearEquiv_fun
  let E : Module.End R M ≃ₐ[K]
      Π c, Matrix (Fin (d c)) (Fin (d c)) (Module.End R (S c)) :=
    (IsSemisimpleModule.endAlgEquiv K R M).trans <|
      AlgEquiv.piCongrRight fun c ↦
        ((e c).some.conjAlgEquiv K).trans (endVecAlgEquivMatrixEnd ..)
  refine ⟨d, fun c ↦ Nat.pos_of_ne_zero (pos c).out, ?_⟩
  rw [E.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro c _
  let : FiniteDimensional K (S c) :=
    FiniteDimensional.of_injective ((S c).subtype.restrictScalars K)
      (S c).subtype_injective
  rw [Module.finrank_matrix, finrank_end_simple_eq_one]
  simp [pow_two]

private theorem ncard_isotypicComponents_eq_four [FiniteDimensional K M]
    [Module.Finite R M] [IsSemisimpleModule R M]
    (hrank : Module.finrank K (Module.End R M) = 4)
    (htwo : 2 ≤ (isotypicComponents R M).ncard) :
    (isotypicComponents R M).ncard = 4 := by
  classical
  let := Fintype.ofFinite (isotypicComponents R M)
  obtain ⟨d, hd, hsum⟩ := exists_finrank_end_eq_sum_sq (K := K) (R := R) (M := M)
  have hcard : 2 ≤ Fintype.card (isotypicComponents R M) := by
    calc
      2 ≤ Nat.card (isotypicComponents R M) := by
        simpa only [Nat.card_coe_set_eq] using htwo
      _ = Fintype.card (isotypicComponents R M) := Nat.card_eq_fintype_card
  have hd_one : ∀ c, d c = 1 := by
    intro c
    obtain ⟨c', hc'⟩ := Fintype.exists_ne_of_one_lt_card (by omega : 1 <
      Fintype.card (isotypicComponents R M)) c
    have hpair : d c ^ 2 + d c' ^ 2 ≤ ∑ x, d x ^ 2 := by
      have hsubset : {c, c'} ⊆ (Finset.univ : Finset (isotypicComponents R M)) :=
        Finset.subset_univ _
      have h := Finset.sum_le_sum_of_subset hsubset (f := fun x ↦ d x ^ 2)
      rw [Finset.sum_pair hc'.symm] at h
      exact h
    rw [← hsum, hrank] at hpair
    have hcpos := hd c
    have hc'pos := hd c'
    nlinarith
  calc
    (isotypicComponents R M).ncard = Fintype.card (isotypicComponents R M) := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_eq_fintype_card
    _ = ∑ c : isotypicComponents R M, d c ^ 2 := by simp [hd_one]
    _ = 4 := hsum.symm.trans hrank

end EndRankFour

section FinrankBridge

variable {K G V : Type*} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V]

private theorem finrank_end_asModule_eq_intertwiningMap (rho : Representation K G V) :
    Module.finrank K (Module.End K[G] rho.asModule) =
      Module.finrank K (rho.IntertwiningMap rho) :=
  (Representation.IntertwiningMap.equivAlgEnd rho).toLinearEquiv.finrank_eq.symm

end FinrankBridge

section InvariantConstituent

variable {K G V : Type*} [Field K] [Group G] [Finite G]
  [NeZero (Nat.card G : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem two_le_ncard_isotypicComponents_of_finrank_invariants_eq_one
    (rho : Representation K G V)
    (hinv : Module.finrank K rho.invariants = 1)
    (hdim : 1 < Module.finrank K V) :
    2 ≤ (isotypicComponents K[G] rho.asModule).ncard := by
  let := Module.Finite.right K K[G] rho.asModule
  let invSubrep : Subrepresentation rho :=
    { toSubmodule := rho.invariants
      apply_mem_toSubmodule := fun g v hv ↦ by simpa only [hv g] using hv }
  let I : Submodule K[G] rho.asModule := invSubrep.asSubmodule
  let IK : Submodule K rho.asModule := I.restrictScalars K
  have hmap : Submodule.map rho.asModuleEquiv.toLinearMap IK = rho.invariants := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subrepresentation.mem_asSubmodule_iff.mp hy
    · intro hx
      refine ⟨rho.asModuleEquiv.symm x, ?_, by simp⟩
      exact Subrepresentation.mem_asSubmodule_iff.mpr hx
  let eIK : IK ≃ₗ[K] rho.invariants :=
    (rho.asModuleEquiv.submoduleMap IK).trans (LinearEquiv.ofEq _ _ hmap)
  let eI : I ≃ₗ[K] rho.invariants := eIK
  have hIfin : Module.finrank K I = 1 := eI.finrank_eq.trans hinv
  let : IsSimpleOrder (Submodule K[G] I) :=
    is_simple_module_of_finrank_eq_one hIfin
  let : IsSimpleModule K[G] I := IsSimpleModule.mk
  obtain ⟨C, hIC⟩ := MonoidAlgebra.Submodule.exists_isCompl I
  have hCne : C ≠ ⊥ := by
    intro hC
    have hItop : I = ⊤ := by simpa [hC] using hIC.sup_eq_top
    have hVone : Module.finrank K V = 1 := by
      calc
        Module.finrank K V = Module.finrank K rho.asModule :=
          rho.asModuleEquiv.finrank_eq.symm
        _ = Module.finrank K I :=
          ((LinearEquiv.ofTop I hItop).restrictScalars K).finrank_eq.symm
        _ = 1 := hIfin
    omega
  obtain hCbot | ⟨S, hSC, hSsimple⟩ :=
    IsSemisimpleModule.eq_bot_or_exists_simple_le C
  · exact (hCne hCbot).elim
  let : IsSimpleModule K[G] S := hSsimple
  apply two_le_ncard_isotypicComponents I S
  rintro ⟨e⟩
  have hSI : S ≤ I := by
    intro y hy
    let ys : S := ⟨y, hy⟩
    let x : I := e.symm ys
    have hxmem : rho.asModuleEquiv x ∈ rho.invariants := (eI x).property
    have hx (g : G) : rho g (rho.asModuleEquiv x) = rho.asModuleEquiv x :=
      (rho.mem_invariants _).mp hxmem g
    have hxsmul (g : G) : MonoidAlgebra.single g (1 : K) • x = x := by
      have hM : (show rho.asModule from rho g (rho.asModuleEquiv x)) =
          (x : rho.asModule) := rho.asModuleEquiv.injective (hx g)
      apply Subtype.ext
      change MonoidAlgebra.single g (1 : K) • (x : rho.asModule) = x
      rw [Representation.single_smul]
      simpa only [one_smul] using hM
    have hyinv : rho.asModuleEquiv y ∈ rho.invariants := by
      rw [rho.mem_invariants]
      intro g
      have heq := e.map_smul (MonoidAlgebra.single g (1 : K)) x
      rw [hxsmul g, e.apply_symm_apply ys] at heq
      have heqv := congrArg (fun z : S ↦ (z : rho.asModule)) heq
      have hM : (show rho.asModule from rho g (rho.asModuleEquiv y)) = y := by
        simpa only [Submodule.coe_smul, Representation.single_smul, one_smul]
          using heqv.symm
      change rho g (rho.asModuleEquiv y) = rho.asModuleEquiv y at hM
      exact hM
    let z : I := eI.symm ⟨rho.asModuleEquiv y, hyinv⟩
    have hz : (z : rho.asModule) = y := by rfl
    rw [← hz]
    exact z.property
  have hSbot : S = ⊥ := by
    apply le_bot_iff.mp
    rw [← hIC.inf_eq_bot]
    exact le_inf hSI hSC
  exact (Submodule.nontrivial_iff_ne_bot.mp (IsSimpleModule.nontrivial K[G] S)) hSbot

end InvariantConstituent

section FiniteGroupRepresentation

variable {K G V : Type*} [Field K] [IsAlgClosed K] [Group G]
  [AddCommGroup V] [Module K V] [Finite G] [NeZero (Nat.card G : K)]
  [FiniteDimensional K V]

theorem ncard_isotypicComponents_asModule_eq_four
    (rho : Representation K G V)
    (hrank : Module.finrank K (rho.IntertwiningMap rho) = 4)
    (htwo : 2 ≤ (isotypicComponents K[G] rho.asModule).ncard) :
    (isotypicComponents K[G] rho.asModule).ncard = 4 := by
  let := Module.Finite.right K K[G] rho.asModule
  apply ncard_isotypicComponents_eq_four (K := K) (R := K[G])
  · rwa [finrank_end_asModule_eq_intertwiningMap]
  · exact htwo

end FiniteGroupRepresentation

section SimpleFDRep

universe u v

open CategoryTheory CategoryTheory.Limits

variable {K : Type u} {G : Type v} {V : Type u} [Field K] [Monoid G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem simple_fdrep_isIrreducible (rho : Representation K G V)
    [Simple (FDRep.of rho)] : rho.IsIrreducible := by
  let F := forget₂ (FDRep K G) (Rep K G)
  have hV : ¬ Subsingleton V := by
    intro h
    have hz : IsZero (F.obj (FDRep.of rho)) := (Rep.isZero_iff K G _).2 h
    exact Simple.not_isZero (FDRep.of rho)
      (IsZero.of_full_of_faithful_of_isZero F _ hz)
  let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  let : Nontrivial (Subrepresentation rho) := ⟨⟨⊥, ⊤, fun h ↦
    (bot_ne_top : (⊥ : Submodule K V) ≠ ⊤) (congrArg Subrepresentation.toSubmodule h)⟩⟩
  refine IsSimpleOrder.mk fun S ↦ ?_
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  let source : FDRep K G := FDRep.of S.toRepresentation
  let target : FDRep K G := FDRep.of rho
  let iRep : F.obj source ⟶ F.obj target := Rep.ofHom
    ⟨S.toSubmodule.subtype, fun g ↦ by ext; rfl⟩
  let i : source ⟶ target := F.preimage iRep
  have : Mono iRep := (Rep.mono_iff_injective iRep).2 S.toSubmodule.subtype_injective
  have : Mono i := Functor.mono_of_mono_map F <| by
    have hm : F.map i = iRep := by simp [i]
    exact hm.symm ▸ (inferInstance : Mono iRep)
  have hi : i ≠ 0 := by
    intro hi
    have hiRep : iRep = 0 := by
      rw [← F.map_preimage iRep]
      simp [i, hi]
    apply hS
    apply Subrepresentation.toSubmodule_injective
    apply (Submodule.eq_bot_iff S.toSubmodule).mpr
    intro x hx
    have hx0 := congr_fun (congrArg (fun f ↦ f.hom) hiRep) ⟨x, hx⟩
    change x = 0 at hx0
    exact hx0
  have : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 hi
  have : IsIso iRep := by
    rw [← F.map_preimage iRep]
    infer_instance
  have hsurj : Function.Surjective iRep.hom := (Rep.epi_iff_surjective iRep).1 inferInstance
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.eq_top_iff'.mpr
  intro x
  obtain ⟨y, hy⟩ := hsurj x
  rw [← hy]
  exact y.property

end SimpleFDRep

end M23

end CFSG
