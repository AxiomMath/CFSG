module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Induction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.SimpleCriteria
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.CharacterValues

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.5)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_5.tex`.

Current scope discipline:

* Only Mathlib modules and `PFtest/PFsection1_1.lean` are imported.
* No Lean files outside `PFtest` are imported or read.
* This file currently contains honest class-function infrastructure and
  theorem-local helper lemmas for Proposition (1.5).
* The book-facing declarations are the public canonical split nodes below;
  theorem-local proof helpers remain private. The `r = 1` consequence in (b)
  is recorded using the character-theoretic norm-one criterion for
  irreducibility.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1

universe v
universe u

/-! ## Basic notation for Proposition (1.5) -/

@[expose] public def supportedOnSubgroup {G : Type*} [Group G]
    (phi : ClassFunction G) (H : Subgroup G) : Prop :=
  ∀ g : G, g ∉ H → phi g = 0

@[expose] public def orthogonal (G : Type*) [Finite G] (phi psi : ClassFunction G) : Prop :=
  scalarProduct G phi psi = 0

@[expose] public def IsIrreducibleCharacter {G : Type*} [Finite G]
    (phi : ClassFunction G) : Prop :=
  scalarProduct G phi phi = 1

@[expose] public def subgroupRestriction {G : Type*} [Group G] (H : Subgroup G)
    (phi : ClassFunction G) : ClassFunction H :=
  fun h => phi h

@[expose] public def inducedClassFunction {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) : ClassFunction G :=
  by
    classical
    intro g
    exact (Nat.card H : ℂ)⁻¹ * ∑ x : G,
      if hx : x * g * x⁻¹ ∈ H then
        theta ⟨x * g * x⁻¹, hx⟩
      else
        0

public abbrev inducedCF {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) : ClassFunction G :=
  inducedClassFunction H theta

public theorem inducedCF_eq_representation_character_pf15
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S : Subgroup G) [Finite S] (rho : Representation ℂ S V) :
    inducedCF S rho.character = (Representation.ind S.subtype rho).character := by
  classical
  ext g
  rw [Theory.Representation.induced_character_formula S rho g]
  rfl

public theorem inducedCF_eq_representation_character
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (S : Subgroup G) [Finite S] (rho : Representation ℂ S V) :
    inducedCF S rho.character = (Representation.ind S.subtype rho).character :=
  inducedCF_eq_representation_character_pf15 S rho

@[expose] public def conjugateOnNormal {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (theta : ClassFunction H) (g : G) : ClassFunction H :=
  fun h => theta ⟨g * h.1 * g⁻¹, hH.conj_mem h.1 h.2 g⟩

@[expose] public def inertiaSubgroup {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (theta : ClassFunction H) : Subgroup G where
  carrier := {g | conjugateOnNormal H theta g = theta}
  one_mem' := by
    funext h
    simp [conjugateOnNormal]
  mul_mem' := by
    intro a b ha hb
    funext h
    have ha' := congrArg
      (fun f => f ⟨b * h.1 * b⁻¹, hH.conj_mem h.1 h.2 b⟩) ha
    have hb' := congrArg (fun f => f h) hb
    simpa [conjugateOnNormal, mul_assoc] using ha'.trans hb'
  inv_mem' := by
    intro a ha
    funext h
    have hmem : a⁻¹ * h.1 * a ∈ H := by
      simpa using hH.conj_mem h.1 h.2 a⁻¹
    have ha' := congrArg
      (fun f => f ⟨a⁻¹ * h.1 * a, hmem⟩) ha
    simpa [conjugateOnNormal, mul_assoc] using ha'.symm

/-! ## Honest helper lemmas used in the proof pattern of Proposition (1.5) -/

private lemma scalarProduct_zero_left
    {G : Type*} [Finite G] (phi : ClassFunction G) :
    scalarProduct G 0 phi = 0 := by
  simp [scalarProduct]


public lemma scalarProduct_add_left
    {G : Type*} [Finite G] (phi1 phi2 psi : ClassFunction G) :
    scalarProduct G (phi1 + phi2) psi =
      scalarProduct G phi1 psi + scalarProduct G phi2 psi := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib, right_distrib]

public lemma scalarProduct_smul_left
    {G : Type*} [Finite G] (z : ℂ) (phi psi : ClassFunction G) :
    scalarProduct G (z • phi) psi = z * scalarProduct G phi psi := by
  calc
    scalarProduct G (z • phi) psi
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, z * (phi g * star (psi g)) := by
            simp [scalarProduct, mul_assoc]
    _ = (Nat.card G : ℂ)⁻¹ * (z * ∑ g : G, phi g * star (psi g)) := by
          rw [← Finset.mul_sum]
    _ = z * scalarProduct G phi psi := by
          simp [scalarProduct, mul_left_comm]


private lemma eq_of_eqOn_subgroup_and_supportedOnSubgroup
    {G : Type*} [Group G]
    (H : Subgroup G) (phi psi : ClassFunction G)
    (hEq : ∀ h : H, phi h = psi h)
    (hphi : supportedOnSubgroup phi H)
    (hpsi : supportedOnSubgroup psi H) :
    phi = psi := by
  funext g
  by_cases hg : g ∈ H
  · exact hEq ⟨g, hg⟩
  · rw [hphi g hg, hpsi g hg]


lemma representationCharacter_isClassFunction
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    IsClassFunction ρ.character := by
  intro x g
  simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x

@[expose] public def conjugateSubgroupMulEquiv
    {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal] (g : G) :
    H ≃* H where
  toFun h := ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.2 g⟩
  invFun h :=
    ⟨g⁻¹ * (h : G) * g, by simpa using hH.conj_mem (h : G) h.2 g⁻¹⟩
  left_inv h := by
    ext
    simp [mul_assoc]
  right_inv h := by
    ext
    simp [mul_assoc]
  map_mul' a b := by
    ext
    simp [mul_assoc]

public abbrev conjugateRepresentation
    {G V : Type*} [Group G] (H : Subgroup G) [H.Normal]
    [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (g : G) : Representation ℂ H V :=
  ρ.comp (conjugateSubgroupMulEquiv H g).toMonoidHom

public lemma representationCharacter_conjugateRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (ρ : Representation ℂ H V) (g : G) :
    (conjugateRepresentation H ρ g).character =
      conjugateOnNormal H ρ.character g := by
  funext h
  let hc : H := ⟨g * (h : G) * g⁻¹, hH.conj_mem (h : G) h.2 g⟩
  change ρ.character hc = ρ.character hc
  rfl

/-- Transport class functions across a multiplicative equivalence by
precomposition with the inverse equivalence. -/
@[expose] public noncomputable def classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) :
    ClassFunction A ≃ₗ[ℂ] ClassFunction B where
  toFun φ := fun b => φ (e.symm b)
  invFun ψ := fun a => ψ (e a)
  left_inv φ := by
    ext a
    simp
  right_inv ψ := by
    ext b
    simp
  map_add' φ ψ := by
    ext b
    rfl
  map_smul' c φ := by
    ext b
    rfl

public theorem classFunctionLinearEquivOfMulEquiv_apply
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) (φ : ClassFunction A) (b : B) :
    classFunctionLinearEquivOfMulEquiv e φ b = φ (e.symm b) := rfl


public theorem conjugateCharacter_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) (φ : ClassFunction A) :
    classFunctionLinearEquivOfMulEquiv e (conjugateCharacter φ) =
      conjugateCharacter (classFunctionLinearEquivOfMulEquiv e φ) := by
  ext b
  rfl

public theorem isClassFunction_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) {φ : ClassFunction A}
    (hφ : IsClassFunction φ) :
    IsClassFunction (classFunctionLinearEquivOfMulEquiv e φ) := by
  intro x g
  simpa [classFunctionLinearEquivOfMulEquiv, mul_assoc] using
    hφ (e.symm x) (e.symm g)

public theorem scalarProduct_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (φ ψ : ClassFunction A) :
    scalarProduct B (classFunctionLinearEquivOfMulEquiv e φ)
        (classFunctionLinearEquivOfMulEquiv e ψ) =
      scalarProduct A φ ψ := by
  unfold scalarProduct
  have hcard : Nat.card B = Nat.card A := Nat.card_congr e.symm.toEquiv
  have hsum :
      (∑ b : B, φ (e.symm b) * star (ψ (e.symm b))) =
        ∑ a : A, φ a * star (ψ a) := by
    simpa using (e.symm.sum_comp (fun a : A => φ a * star (ψ a)))
  rw [hcard]
  simpa [classFunctionLinearEquivOfMulEquiv, hsum]

public theorem degree_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) (φ : ClassFunction A) :
    degree (classFunctionLinearEquivOfMulEquiv e φ) = degree φ := by
  simp [degree, classFunctionLinearEquivOfMulEquiv]

public theorem principalCharacter_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) :
    classFunctionLinearEquivOfMulEquiv e (principalCharacter A) =
      principalCharacter B := by
  ext b
  simp [classFunctionLinearEquivOfMulEquiv, principalCharacter]

def subrepresentationOrderIso_compMulEquivDomain
    {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ A W) (e : B ≃* A) :
    Subrepresentation rho ≃o Subrepresentation (rho.comp e.toMonoidHom) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro b v hv
        exact S.apply_mem_toSubmodule (e b) hv }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := by
        intro a v hv
        have hmem := T.apply_mem_toSubmodule (e.symm a) hv
        simpa using hmem }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

public lemma irreducible_compMulEquivDomain
    {A B W : Type*} [Group A] [Group B] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ A W) (e : B ≃* A)
    [Representation.IsIrreducible rho] :
    Representation.IsIrreducible (rho.comp e.toMonoidHom) := by
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_compMulEquivDomain rho e)).mp inferInstance

public theorem isIrreducibleCharacterOnGroup_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) {φ : ClassFunction A}
    (hφ : IsIrreducibleCharacterOnGroup φ) :
    IsIrreducibleCharacterOnGroup (classFunctionLinearEquivOfMulEquiv e φ) := by
  rcases hφ with ⟨n, ρ, hρ, hφeq⟩
  refine ⟨n, ρ.comp e.symm.toMonoidHom, irreducible_compMulEquivDomain ρ e.symm, ?_⟩
  ext b
  simp [classFunctionLinearEquivOfMulEquiv, hφeq, Representation.character]

public theorem virtualCharacter_classFunctionLinearEquivOfMulEquiv
    {A : Type*} {B : Type*} [Group A] [Group B]
    (e : A ≃* B) {φ : ClassFunction A}
    (hφ : Theory.Character.IsVirtualCharacter φ) :
    Theory.Character.IsVirtualCharacter (classFunctionLinearEquivOfMulEquiv e φ) := by
  rcases hφ with ⟨r, m, n, ρ, hφeq⟩
  refine ⟨r, m, n, fun i => (ρ i).comp e.symm.toMonoidHom, ?_⟩
  ext b
  simp [classFunctionLinearEquivOfMulEquiv, hφeq,
    Theory.Character.virtualCharacterOfRepresentations, Representation.character]

def subrepresentationOrderIso_compMulEquiv
    {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H W) (e : H ≃* H) :
    Subrepresentation rho ≃o Subrepresentation (rho.comp e.toMonoidHom) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        exact S.apply_mem_toSubmodule (e h) hv }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := by
        intro h v hv
        have hmem := T.apply_mem_toSubmodule (e.symm h) hv
        simpa using hmem }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

lemma irreducible_compMulEquiv
    {H W : Type*} [Group H] [AddCommGroup W] [Module ℂ W]
    (rho : Representation ℂ H W) (e : H ≃* H)
    [Representation.IsIrreducible rho] :
    Representation.IsIrreducible (rho.comp e.toMonoidHom) := by
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_compMulEquiv rho e)).mp inferInstance

public lemma irreducible_conjugateRepresentation
    {G V : Type*} [Group G]
    (H : Subgroup G) [Finite H] [H.Normal]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (g : G)
    [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (conjugateRepresentation H ρ g) := by
  have hcomp :
      Representation.IsIrreducible
        (ρ.comp (conjugateSubgroupMulEquiv H g).toMonoidHom) :=
    irreducible_compMulEquiv ρ (conjugateSubgroupMulEquiv H g)
  simpa [conjugateRepresentation] using hcomp

def dualCoannihilatorSubrepresentation
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V)
    (S : Subrepresentation rho.dual) : Subrepresentation rho where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have hS : rho.dual g⁻¹ f ∈ S.toSubmodule :=
      S.apply_mem_toSubmodule g⁻¹ hf
    have hvzero := hv (rho.dual g⁻¹ f) hS
    rw [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply] at hvzero
    exact hvzero

lemma dualCoannihilatorSubrepresentation_eq_top_of_eq_bot
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation rho (⊥ : Subrepresentation rho.dual) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊤ : Submodule ℂ V)
  simp

lemma dualCoannihilatorSubrepresentation_eq_bot_of_eq_top
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation rho (⊤ : Subrepresentation rho.dual) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊤ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator =
    (⊥ : Submodule ℂ V)
  simp

public theorem representation_dual_irreducible
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V)
    [Representation.IsIrreducible rho] :
    Representation.IsIrreducible rho.dual := by
  refine
    { exists_pair_ne := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro hbotTop
    have hcong := congrArg (dualCoannihilatorSubrepresentation rho) hbotTop
    have htop : (⊤ : Subrepresentation rho) = ⊥ := by
      rw [dualCoannihilatorSubrepresentation_eq_top_of_eq_bot rho,
        dualCoannihilatorSubrepresentation_eq_bot_of_eq_top rho] at hcong
      exact hcong
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation rho) htop.symm
  · intro S
    have hN := eq_bot_or_eq_top (dualCoannihilatorSubrepresentation rho S)
    rcases hN with hNbot | hNtop
    · right
      apply Subrepresentation.toSubmodule_injective
      have hdual :
          S.toSubmodule.dualCoannihilator.dualAnnihilator = S.toSubmodule :=
        Subspace.dualCoannihilator_dualAnnihilator_eq
      have hNsub : S.toSubmodule.dualCoannihilator = ⊥ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNbot
        change S.toSubmodule.dualCoannihilator = (⊥ : Submodule ℂ V) at htmp
        exact htmp
      rw [hNsub] at hdual
      calc
        S.toSubmodule =
            (⊥ : Submodule ℂ V).dualAnnihilator := hdual.symm
        _ = ⊤ := by simp
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm ?_ bot_le
      intro f hf
      rw [Submodule.mem_bot]
      ext v
      have hNsub : S.toSubmodule.dualCoannihilator = ⊤ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNtop
        change S.toSubmodule.dualCoannihilator = (⊤ : Submodule ℂ V) at htmp
        exact htmp
      have hv : v ∈ S.toSubmodule.dualCoannihilator := by
        rw [hNsub]
        exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator v).mp hv f hf

public theorem representation_dual_irreducible_of
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible ρ.dual := by
  letI : Representation.IsIrreducible ρ := hρ
  exact representation_dual_irreducible ρ

public lemma conjugateOnNormal_one
    {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (theta : ClassFunction H) :
    conjugateOnNormal H theta 1 = theta := by
  funext h
  simp [conjugateOnNormal]

@[expose] public def conjugateOrbitSetoid
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) : Setoid G where
  r x y := conjugateOnNormal H theta x = conjugateOnNormal H theta y
  iseqv := by
    constructor
    · intro x
      rfl
    · intro x y hxy
      exact hxy.symm
    · intro x y z hxy hyz
      exact hxy.trans hyz

public abbrev conjugateOrbitIndex
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) :=
  Quotient (conjugateOrbitSetoid H theta)

@[expose] public def conjugateOrbitFiber
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (x : G) : conjugateOrbitIndex H theta :=
  Quotient.mk (conjugateOrbitSetoid H theta) x

@[expose] public def conjugateOrbitConj
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) : conjugateOrbitIndex H theta → ClassFunction H :=
  Quotient.lift (fun x : G => conjugateOnNormal H theta x)
    (by
      intro x y hxy
      exact hxy)

lemma conjugateOrbit_hfiber
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (x : G) :
    conjugateOnNormal H theta x =
      conjugateOrbitConj H theta (conjugateOrbitFiber H theta x) := by
  rfl

private lemma conjugateOrbit_base_eq_theta
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) :
    conjugateOrbitConj H theta (conjugateOrbitFiber H theta 1) = theta := by
  exact conjugateOnNormal_one H theta

lemma conjugateOrbit_eq_base_of_conj_eq_theta
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (i : conjugateOrbitIndex H theta)
    (hi : conjugateOrbitConj H theta i = theta) :
    i = conjugateOrbitFiber H theta 1 := by
  revert hi
  refine Quotient.inductionOn i ?_
  intro x hx
  apply Quotient.sound
  change conjugateOnNormal H theta x = conjugateOnNormal H theta 1
  exact hx.trans (conjugateOnNormal_one H theta).symm

lemma conjugateOrbit_conj_ne_theta_of_ne_base
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (i : conjugateOrbitIndex H theta)
    (hi : i ≠ conjugateOrbitFiber H theta 1) :
    conjugateOrbitConj H theta i ≠ theta := by
  intro htheta
  exact hi (conjugateOrbit_eq_base_of_conj_eq_theta H theta i htheta)

private lemma degree_conjugateOnNormal
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (g : G) :
    degree (conjugateOnNormal H theta g) = degree theta := by
  unfold degree conjugateOnNormal
  exact congrArg theta (Subtype.ext (by simp))

lemma degree_conjugateOrbitConj
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (i : conjugateOrbitIndex H theta) :
    degree (conjugateOrbitConj H theta i) = degree theta := by
  refine Quotient.inductionOn i ?_
  intro g
  exact degree_conjugateOnNormal H theta g

@[expose] public def conjugateOrbitRepresentation
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (ρ : Representation ℂ H V) :
    conjugateOrbitIndex H ρ.character → Representation ℂ H V :=
  fun i => conjugateRepresentation H ρ (Quotient.out i)

public lemma conjugateOrbitConj_representationCharacter
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (ρ : Representation ℂ H V)
    (i : conjugateOrbitIndex H ρ.character) :
    conjugateOrbitConj H ρ.character i =
      (conjugateOrbitRepresentation H ρ i).character := by
  let g : G := Quotient.out i
  have hout :
      conjugateOrbitFiber H ρ.character g = i :=
    Quotient.out_eq i
  change conjugateOrbitConj H ρ.character i =
    (conjugateRepresentation H ρ g).character
  rw [representationCharacter_conjugateRepresentation H ρ g, ← hout]
  rfl

lemma conjugateOrbitRepresentation_irreducible
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (ρ : Representation ℂ H V) (hρ : Representation.IsIrreducible ρ) :
    ∀ i : conjugateOrbitIndex H ρ.character,
      Representation.IsIrreducible (conjugateOrbitRepresentation H ρ i) := by
  letI : Representation.IsIrreducible ρ := hρ
  intro i
  exact irreducible_conjugateRepresentation H ρ (Quotient.out i)

lemma mem_inertiaSubgroup_iff
    {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (theta : ClassFunction H) (g : G) :
    g ∈ inertiaSubgroup H theta ↔ conjugateOnNormal H theta g = theta := by
  rfl

lemma orthogonal_iff
    {G : Type*} [Finite G] (phi psi : ClassFunction G) :
    orthogonal G phi psi ↔ scalarProduct G phi psi = 0 := by
  rfl

private lemma mem_subgroup_iff_conj_mem
    {G : Type*} [Group G] (H : Subgroup G) [hH : H.Normal]
    (x g : G) :
    x * g * x⁻¹ ∈ H ↔ g ∈ H := by
  constructor
  · intro hx
    have hx' : x⁻¹ * (x * g * x⁻¹) * x ∈ H := by
      simpa [mul_assoc] using hH.conj_mem (x * g * x⁻¹) hx x⁻¹
    simpa [mul_assoc] using hx'
  · intro hg
    simpa using hH.conj_mem g hg x

private lemma inducedClassFunction_formula_on_subgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) (h : H) :
    inducedClassFunction H theta h =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        theta ⟨x * h.1 * x⁻¹, hH.conj_mem h.1 h.2 x⟩ := by
  classical
  unfold inducedClassFunction
  refine congrArg ((Nat.card H : ℂ)⁻¹ * ·) ?_
  refine Finset.sum_congr rfl ?_
  intro x hx
  have hxtrue : x * h.1 * x⁻¹ ∈ H := hH.conj_mem h.1 h.2 x
  simp [hxtrue]

private lemma inducedClassFunction_eq_zero_of_not_mem
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) {g : G} (hg : g ∉ H) :
    inducedClassFunction H theta g = 0 := by
  classical
  unfold inducedClassFunction
  have hsum : ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxfalse : ¬ x * g * x⁻¹ ∈ H := by
      rw [mem_subgroup_iff_conj_mem H x g]
      exact hg
    simp [hxfalse]
  rw [hsum]
  simp

private lemma inducedClassFunction_supportedOnSubgroup
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) :
    supportedOnSubgroup (inducedClassFunction H theta) H := by
  intro g hg
  exact inducedClassFunction_eq_zero_of_not_mem H theta hg

public lemma inducedClassFunction_eq_zero_of_not_mem_of_normal
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) {g : G} (hg : g ∉ H) :
    inducedClassFunction H theta g = 0 :=
  inducedClassFunction_eq_zero_of_not_mem H theta hg


lemma inducedClassFunction_conjugateOnNormal
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) (g : G) :
    inducedClassFunction H (conjugateOnNormal H theta g) = inducedClassFunction H theta := by
  classical
  funext y
  let f : G → ℂ := fun z =>
    if hz : z * y * z⁻¹ ∈ H then
      theta ⟨z * y * z⁻¹, hz⟩
    else
      0
  unfold inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0) =
        ∑ x : G, f (g * x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hmem :
        x * y * x⁻¹ ∈ H ↔ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
      simpa [mul_assoc] using (mem_subgroup_iff_conj_mem H g (x * y * x⁻¹)).symm
    by_cases hxH : x * y * x⁻¹ ∈ H
    · have hgxH : g * x * y * (x⁻¹ * g⁻¹) ∈ H := hmem.mp hxH
      have hxH' : x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [conjugateOnNormal, hxH', hgxH', mul_assoc]
    · have hgxH : ¬ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
        exact fun h => hxH (hmem.mpr h)
      have hxH' : ¬ x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : ¬ g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [hxH', hgxH', mul_assoc]
  calc
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0)
        =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, f (g * x) := by
          rw [hsum]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ z : G, f z := by
          congr 1
          simpa using (Equiv.sum_comp (Equiv.mulLeft g) f)
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ z : G,
          (if hz : z * y * z⁻¹ ∈ H then
            theta ⟨z * y * z⁻¹, hz⟩
          else
            0) := by
          rfl

lemma inducedCF_conjugateOnNormal
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : ClassFunction H) (g : G) :
    inducedCF H (conjugateOnNormal H theta g) = inducedCF H theta := by
  exact inducedClassFunction_conjugateOnNormal H theta g

public lemma inducedClassFunction_isClassFunction
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) :
    IsClassFunction (inducedClassFunction H theta) := by
  classical
  intro y g
  let f : G → ℂ := fun z =>
    if hz : z * g * z⁻¹ ∈ H then theta ⟨z * g * z⁻¹, hz⟩ else 0
  unfold inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * (y * g * y⁻¹) * x⁻¹ ∈ H then
            theta ⟨x * (y * g * y⁻¹) * x⁻¹, hx⟩
          else
            0) =
        ∑ x : G, f (x * y) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    have hcalc : x * (y * g * y⁻¹) * x⁻¹ = (x * y) * g * (x * y)⁻¹ := by
      group
    by_cases hxmem : x * (y * g * y⁻¹) * x⁻¹ ∈ H
    · have hxmem' : (x * y) * g * (x * y)⁻¹ ∈ H := by
        simpa [hcalc] using hxmem
      simp [f, hcalc]
    · have hxmem' : ¬ (x * y) * g * (x * y)⁻¹ ∈ H := by
        simpa [hcalc] using hxmem
      simp [f, hcalc]
  calc
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * (y * g * y⁻¹) * x⁻¹ ∈ H then
            theta ⟨x * (y * g * y⁻¹) * x⁻¹, hx⟩
          else
            0)
        =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, f (x * y) := by
        rw [hsum]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ z : G, f z := by
        congr 1
        simpa using (Equiv.sum_comp (Equiv.mulRight y) f)
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ z : G,
          (if hz : z * g * z⁻¹ ∈ H then theta ⟨z * g * z⁻¹, hz⟩ else 0) := by
        rfl

public lemma inducedCF_isClassFunction
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) :
    IsClassFunction (inducedCF H theta) :=
  inducedClassFunction_isClassFunction H theta


public lemma inducedClassFunction_add
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (theta phi : ClassFunction H) :
    inducedClassFunction H (theta + phi) =
      inducedClassFunction H theta + inducedClassFunction H phi := by
  classical
  funext g
  unfold inducedClassFunction
  have hsplit :
      ∑ x : G,
        (if hx : x * g * x⁻¹ ∈ H then (theta + phi) ⟨x * g * x⁻¹, hx⟩ else 0) =
      ∑ x : G,
        ((if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) +
         (if hx : x * g * x⁻¹ ∈ H then phi ⟨x * g * x⁻¹, hx⟩ else 0)) := by
    · refine Finset.sum_congr rfl ?_
      intro x hx
      by_cases hmem : x * g * x⁻¹ ∈ H
      · simp [hmem]
      · simp [hmem]
  rw [hsplit, Finset.sum_add_distrib, mul_add]
  rfl

public lemma inducedClassFunction_smul
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (z : ℂ) (theta : ClassFunction H) :
    inducedClassFunction H (z • theta) = z • inducedClassFunction H theta := by
  classical
  funext g
  unfold inducedClassFunction
  have hsum :
      ∑ x : G,
        (if hx : x * g * x⁻¹ ∈ H then (z • theta) ⟨x * g * x⁻¹, hx⟩ else 0) =
      ∑ x : G, z * (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    by_cases hmem : x * g * x⁻¹ ∈ H
    · simp [hmem]
    · simp [hmem]
  rw [hsum, ← Finset.mul_sum]
  simp [smul_eq_mul, mul_left_comm, mul_assoc]

public lemma degree_inducedClassFunction
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] (theta : ClassFunction H) :
    degree (inducedClassFunction H theta) = (Subgroup.index H : ℂ) * degree theta := by
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hindex : (Subgroup.index H : ℂ) * Nat.card H = Nat.card G := by
    exact_mod_cast H.index_mul_card
  calc
    degree (inducedClassFunction H theta)
        = (Nat.card H : ℂ)⁻¹ * ∑ x : G, theta 1 := by
            unfold degree inducedClassFunction
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            have hone : (⟨(1 : G), H.one_mem⟩ : H) = 1 := rfl
            simp [hone]
    _ = (Nat.card H : ℂ)⁻¹ * ((Nat.card G : ℂ) * degree theta) := by
          rw [show (∑ x : G, theta (1 : H)) = (Nat.card G : ℂ) * theta (1 : H) by
            simp [Finset.card_univ]]
          rfl
    _ = ((Nat.card H : ℂ)⁻¹ * (Nat.card G : ℂ)) * degree theta := by ring
    _ = (Subgroup.index H : ℂ) * degree theta := by
          apply congrArg (fun z => z * degree theta)
          have hindex' : (Nat.card G : ℂ) = (Subgroup.index H : ℂ) * Nat.card H := by
            simpa [mul_comm] using hindex.symm
          rw [hindex']
          field_simp [hcardH]

public lemma scalarProduct_smul_right
    {G : Type*} [Finite G] (z : ℂ) (phi psi : ClassFunction G) :
    scalarProduct G phi (z • psi) = star z * scalarProduct G phi psi := by
  calc
    scalarProduct G phi (z • psi)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, star z * (phi g * star (psi g)) := by
            simp [scalarProduct, mul_left_comm]
    _ = (Nat.card G : ℂ)⁻¹ * (star z * ∑ g : G, phi g * star (psi g)) := by
          rw [← Finset.mul_sum]
    _ = star z * scalarProduct G phi psi := by
          simp [scalarProduct, mul_left_comm]

public lemma scalarProduct_star_swap
    {G : Type*} [Finite G] (phi psi : ClassFunction G) :
    star (scalarProduct G psi phi) = scalarProduct G phi psi := by
  simp [scalarProduct, mul_comm]

public lemma scalarProduct_ne_zero_swap
    {G : Type*} [Finite G] (phi psi : ClassFunction G) :
    scalarProduct G phi psi ≠ 0 ↔ scalarProduct G psi phi ≠ 0 := by
  constructor
  · intro h hzero
    apply h
    rw [← scalarProduct_star_swap phi psi]
    simp [hzero]
  · intro h hzero
    apply h
    rw [← scalarProduct_star_swap psi phi]
    simp [hzero]

public lemma scalarProduct_fintype_sum_left
    {G ι : Type*} [Finite G] [Fintype ι]
    (Phi : ι → ClassFunction G) (psi : ClassFunction G) :
    scalarProduct G (fun g => ∑ i, Phi i g) psi =
      ∑ i, scalarProduct G (Phi i) psi := by
  unfold scalarProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, (∑ i : ι, Phi i g) * star (psi g)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ∑ i : ι, Phi i g * star (psi g) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            rw [Finset.sum_mul]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i : ι, ∑ g : G, Phi i g * star (psi g) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : ι, (Nat.card G : ℂ)⁻¹ * ∑ g : G, Phi i g * star (psi g) := by
          rw [Finset.mul_sum]
    _ = ∑ i : ι, scalarProduct G (Phi i) psi := by
          rfl

public lemma scalarProduct_fintype_sum_right
    {G ι : Type*} [Finite G] [Fintype ι]
    (phi : ClassFunction G) (Psi : ι → ClassFunction G) :
    scalarProduct G phi (fun g => ∑ i, Psi i g) =
      ∑ i, scalarProduct G phi (Psi i) := by
  unfold scalarProduct
  calc
    (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (∑ i : ι, Psi i g)
        = (Nat.card G : ℂ)⁻¹ * ∑ g : G, ∑ i : ι, phi g * star (Psi i g) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            calc
              phi g * star (∑ i : ι, Psi i g) = phi g * ∑ i : ι, star (Psi i g) := by
                simp
              _ = ∑ i : ι, phi g * star (Psi i g) := by
                rw [Finset.mul_sum]
    _ = (Nat.card G : ℂ)⁻¹ * ∑ i : ι, ∑ g : G, phi g * star (Psi i g) := by
          congr 1
          rw [Finset.sum_comm]
    _ = ∑ i : ι, (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (Psi i g) := by
          rw [Finset.mul_sum]
    _ = ∑ i : ι, scalarProduct G phi (Psi i) := by
          rfl

lemma sum_eq_sum_subgroup_of_supported
    {G M : Type*} [Group G] [Finite G] [AddCommMonoid M]
    (H : Subgroup G) (f : G → M)
    (hzero : ∀ g : G, g ∉ H → f g = 0) :
    ∑ g : G, f g = ∑ h : H, f h := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let s : Finset G := Finset.univ.filter fun g : G => g ∈ H
  have hs : ∀ g : G, g ∈ s ↔ g ∈ H := by
    intro g
    simp [s]
  have hsub : ∑ g ∈ s, f g = ∑ h : H, f h :=
    Finset.sum_subtype (s := s) (p := fun g : G => g ∈ H) hs f
  calc
    ∑ g : G, f g = ∑ g : G, if g ∈ H then f g else 0 := by
      refine Finset.sum_congr rfl ?_
      intro g _hg
      by_cases hgH : g ∈ H
      · simp [hgH]
      · simp [hgH, hzero g hgH]
    _ = ∑ g ∈ s, f g := by
      simpa [s] using
        (Finset.sum_filter (s := (Finset.univ : Finset G))
          (p := fun g : G => g ∈ H) f).symm
    _ = ∑ h : H, f h := hsub


public lemma inducedClassFunction_frobenius_general
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (phi : ClassFunction H) (mu : ClassFunction G)
    (hmu : IsClassFunction mu) :
    scalarProduct G (inducedCF H phi) mu =
      scalarProduct H phi (subgroupRestriction H mu) := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  let cG : ℂ := Nat.card G
  let cH : ℂ := Nat.card H
  let S : ℂ := ∑ h : H, phi h * star (mu h)
  let term : G → G → ℂ := fun x g =>
    if hxg : x * g * x⁻¹ ∈ H then phi ⟨x * g * x⁻¹, hxg⟩ else 0
  have hcardG : cG ≠ 0 := by
    dsimp [cG]
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  have hinner : ∀ x : G, ∑ g : G, term x g * star (mu g) = S := by
    intro x
    let conj : G ≃ G :=
      { toFun := fun y => x⁻¹ * y * x
        invFun := fun y => x * y * x⁻¹
        left_inv := by
          intro y
          dsimp
          group
        right_inv := by
          intro y
          dsimp
          group }
    calc
      ∑ g : G, term x g * star (mu g)
          = ∑ y : G, term x (x⁻¹ * y * x) * star (mu (x⁻¹ * y * x)) := by
            simpa [conj] using
              (Equiv.sum_comp conj (fun g : G => term x g * star (mu g))).symm
      _ = ∑ y : G, (if hy : y ∈ H then phi ⟨y, hy⟩ else 0) * star (mu y) := by
            refine Finset.sum_congr rfl ?_
            intro y _hy
            have hclass : mu (x⁻¹ * y * x) = mu y := by
              simpa using hmu x⁻¹ y
            by_cases hyH : y ∈ H
            · have hxy : x * (x⁻¹ * y * x) * x⁻¹ ∈ H := by
                convert hyH using 1
                group
              dsimp [term]
              change
                (if h : x * (x⁻¹ * y * x) * x⁻¹ ∈ H then
                    phi ⟨x * (x⁻¹ * y * x) * x⁻¹, h⟩
                  else 0) * star (mu (x⁻¹ * y * x)) =
                  (if h : y ∈ H then phi ⟨y, h⟩ else 0) * star (mu y)
              rw [hclass, dif_pos hxy, dif_pos hyH]
              congr 1
              apply congrArg phi
              apply Subtype.ext
              dsimp
              group
            · have hxy : ¬ x * (x⁻¹ * y * x) * x⁻¹ ∈ H := by
                intro hmem
                apply hyH
                convert hmem using 1
                group
              dsimp [term]
              change
                (if h : x * (x⁻¹ * y * x) * x⁻¹ ∈ H then
                    phi ⟨x * (x⁻¹ * y * x) * x⁻¹, h⟩
                  else 0) * star (mu (x⁻¹ * y * x)) =
                  (if h : y ∈ H then phi ⟨y, h⟩ else 0) * star (mu y)
              rw [hclass, dif_neg hxy, dif_neg hyH]
      _ = ∑ h : H, phi h * star (mu h) := by
            have hreduce := sum_eq_sum_subgroup_of_supported H
              (fun y : G => (if hy : y ∈ H then phi ⟨y, hy⟩ else 0) * star (mu y))
              (by
                intro y hyH
                simp [hyH])
            simpa using hreduce
      _ = S := rfl
  have hswap :
      ∑ g : G, (∑ x : G, term x g) * star (mu g) =
        (Nat.card G : ℂ) * S := by
    calc
      ∑ g : G, (∑ x : G, term x g) * star (mu g)
          = ∑ g : G, ∑ x : G, term x g * star (mu g) := by
            refine Finset.sum_congr rfl ?_
            intro g _hg
            rw [Finset.sum_mul]
      _ = ∑ x : G, ∑ g : G, term x g * star (mu g) := by
            rw [Finset.sum_comm]
      _ = ∑ _x : G, S := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            exact hinner x
      _ = (Nat.card G : ℂ) * S := by
            simp [Finset.card_univ]
  unfold scalarProduct inducedCF inducedClassFunction
  calc
    (Nat.card G : ℂ)⁻¹ *
        ∑ g : G, ((Nat.card H : ℂ)⁻¹ * ∑ x : G, term x g) * star (mu g)
        =
      (Nat.card G : ℂ)⁻¹ *
        ((Nat.card H : ℂ)⁻¹ *
          ∑ g : G, (∑ x : G, term x g) * star (mu g)) := by
          congr 1
          calc
            ∑ g : G, ((Nat.card H : ℂ)⁻¹ * ∑ x : G, term x g) * star (mu g)
                =
              ∑ g : G, (Nat.card H : ℂ)⁻¹ * ((∑ x : G, term x g) * star (mu g)) := by
                refine Finset.sum_congr rfl ?_
                intro g _hg
                ring
            _ = (Nat.card H : ℂ)⁻¹ *
                  ∑ g : G, (∑ x : G, term x g) * star (mu g) := by
                rw [Finset.mul_sum]
    _ = (Nat.card G : ℂ)⁻¹ * ((Nat.card H : ℂ)⁻¹ * ((Nat.card G : ℂ) * S)) := by
          rw [hswap]
    _ = (Nat.card H : ℂ)⁻¹ * S := by
          field_simp [hcardG]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ h : H, phi h * star (subgroupRestriction H mu h) := by
          simp [S, subgroupRestriction]

public lemma inducedClassFunction_frobenius
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [_hH : H.Normal]
    (phi : ClassFunction H) (mu : ClassFunction G)
    (hmu : IsClassFunction mu) :
    scalarProduct G (inducedCF H phi) mu =
      scalarProduct H phi (subgroupRestriction H mu) := by
  exact inducedClassFunction_frobenius_general H phi mu hmu

public lemma inducedClassFunction_frobenius_right
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H]
    (phi : ClassFunction H) (mu : ClassFunction G)
    (hmu : IsClassFunction mu) :
    scalarProduct G mu (inducedCF H phi) =
      scalarProduct H (subgroupRestriction H mu) phi := by
  have hleft := inducedClassFunction_frobenius_general H phi mu hmu
  have hswapG :
      star (scalarProduct G mu (inducedCF H phi)) =
        scalarProduct H phi (subgroupRestriction H mu) := by
    rw [scalarProduct_star_swap (inducedCF H phi) mu]
    exact hleft
  have hstar := congrArg star hswapG
  simpa [scalarProduct_star_swap (subgroupRestriction H mu) phi] using hstar

lemma scalarProduct_conjs_with_base
    {H ι : Type*} [Finite H] [Fintype ι] [DecidableEq ι]
    (base : ι) (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (hbase : conjs base = theta)
    (hself : scalarProduct H theta theta = 1)
    (horthDistinct :
      ∀ i : ι, i ≠ base → scalarProduct H (conjs i) theta = 0) :
    ∀ i : ι, scalarProduct H (conjs i) theta = if i = base then 1 else 0 := by
  intro i
  by_cases hi : i = base
  · subst hi
    simp [hbase, hself]
  · simp [hi, horthDistinct i hi]

/-! ## Proposition (1.5): currently formalized theorem-local nodes -/

lemma proposition_1_5_part_a
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [hH : H.Normal] (theta : ClassFunction H) (fiber : G → ι)
    (conjs : ι → ClassFunction H) (r : ℕ) (chi : ClassFunction G)
    (hchi : ∀ h : H,
      chi h = (Nat.card H : ℂ)⁻¹ * ∑ x : G,
        conjugateOnNormal H theta x h)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r) :
    subgroupRestriction H chi = fun h => (r : ℂ) * ∑ i : ι, conjs i h := by
  funext h
  let _ : Fintype H := Fintype.ofFinite H
  have hcardH : (Nat.card H : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := H)).ne'
  have hsum1 :
      ∑ x : G, conjugateOnNormal H theta x h = ∑ x : G, conjs (fiber x) h := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    simp [hfiber]
  have hsum2 :
      ∑ x : G, conjs (fiber x) h = ∑ i : ι, ∑ _x : {x // fiber x = i}, conjs i h := by
    symm
    simpa using (Fintype.sum_fiberwise' fiber (fun i : ι => conjs i h))
  have hsum3 :
      ∑ i : ι, ∑ _x : {x // fiber x = i}, conjs i h =
        ∑ i : ι, ((Nat.card H * r : ℕ) : ℂ) * conjs i h := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    calc
      (∑ _x : {x // fiber x = i}, conjs i h)
          = (Nat.card {x // fiber x = i} : ℂ) * conjs i h := by
              simp
      _ = ((Nat.card H * r : ℕ) : ℂ) * conjs i h := by
          rw [hcount i, Nat.cast_mul]
  calc
    subgroupRestriction H chi h =
        (Nat.card H : ℂ)⁻¹ * ∑ x : G, conjugateOnNormal H theta x h := hchi h
    _ = (Nat.card H : ℂ)⁻¹ * ∑ x : G, conjs (fiber x) h := by rw [hsum1]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ i : ι, ∑ _x : {x // fiber x = i}, conjs i h := by rw [hsum2]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ i : ι, ((Nat.card H * r : ℕ) : ℂ) * conjs i h := by rw [hsum3]
    _ = (Nat.card H : ℂ)⁻¹ * (((Nat.card H * r : ℕ) : ℂ) * ∑ i : ι, conjs i h) := by
          congr 1
          rw [Finset.mul_sum]
    _ = (r : ℂ) * ∑ i : ι, conjs i h := by
          rw [Nat.cast_mul]
          ring_nf
          field_simp [hcardH]

lemma proposition_1_5_part_b
    {G H ι : Type*} [Finite G] [Finite H] [Fintype ι] [DecidableEq ι]
    (base : ι) (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (r : ℕ) (chi : ClassFunction G) (chiRes : ClassFunction H)
    (hbase : conjs base = theta)
    (hFR : scalarProduct G chi chi = scalarProduct H chiRes (conjs base))
    (hres : chiRes = fun h => (r : ℂ) * ∑ i : ι, conjs i h)
    (hself : scalarProduct H (conjs base) (conjs base) = 1)
    (horthDistinct :
      ∀ i : ι, i ≠ base → scalarProduct H (conjs i) theta = 0) :
    scalarProduct G chi chi = r := by
  have hFRTheta : scalarProduct G chi chi = scalarProduct H chiRes theta := by
    simpa [hbase] using hFR
  have hselfTheta : scalarProduct H theta theta = 1 := by
    simpa [hbase] using hself
  have horth :
      ∀ i : ι, scalarProduct H (conjs i) theta = if i = base then 1 else 0 :=
    scalarProduct_conjs_with_base base theta conjs hbase hselfTheta horthDistinct
  have hsum : (∑ i : ι, scalarProduct H (conjs i) theta) = 1 := by
    calc
      (∑ i : ι, scalarProduct H (conjs i) theta)
          = ∑ i : ι, if i = base then 1 else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [horth i]
      _ = 1 := by simp
  calc
    scalarProduct G chi chi = scalarProduct H chiRes theta := hFRTheta
    _ = scalarProduct H (fun h => (r : ℂ) * ∑ i : ι, conjs i h) theta := by rw [hres]
    _ = scalarProduct H ((r : ℂ) • fun h => ∑ i : ι, conjs i h) theta := by rfl
    _ = (r : ℂ) * scalarProduct H (fun h => ∑ i : ι, conjs i h) theta := by
          rw [scalarProduct_smul_left]
    _ = (r : ℂ) * ∑ i : ι, scalarProduct H (conjs i) theta := by
          rw [scalarProduct_fintype_sum_left]
    _ = (r : ℂ) * 1 := by rw [hsum]
    _ = r := by simp

lemma proposition_1_5_part_d
    {G H ι : Type*} [Finite G] [Finite H] [Fintype ι] [One G] [One H]
    (n r : ℕ) (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (chi : ClassFunction G) (chiRes : ClassFunction H) (base : ι)
    (hbase : conjs base = theta)
    (hdeg : ∀ i : ι, degree (conjs i) = degree (conjs base))
    (hchi1 : degree chi = (n : ℂ) * degree (conjs base))
    (hres : chiRes = fun h => (r : ℂ) * ∑ i : ι, conjs i h)
    (hnorm : scalarProduct G chi chi = r)
    (hr : r ≠ 0) :
    ((degree chi) / scalarProduct G chi chi) • chiRes =
      (n : ℂ) • fun h => ∑ i : ι, degree (conjs i) * conjs i h := by
  have hdegTheta : ∀ i : ι, degree (conjs i) = degree theta := by
    intro i
    rw [hdeg i, hbase]
  have hchiTheta : degree chi = (n : ℂ) * degree theta := by
    rw [hchi1, hbase]
  ext h
  have hrC : (r : ℂ) ≠ 0 := by
    exact_mod_cast hr
  calc
    (((degree chi) / scalarProduct G chi chi) • chiRes) h
        = ((degree chi) / scalarProduct G chi chi) * ((r : ℂ) * ∑ i : ι, conjs i h) := by
            simp [hres]
    _ = (((n : ℂ) * degree theta) / (r : ℂ)) * ((r : ℂ) * ∑ i : ι, conjs i h) := by
          rw [hchiTheta, hnorm]
    _ = (n : ℂ) * (degree theta * ∑ i : ι, conjs i h) := by
          field_simp [hrC]
    _ = (n : ℂ) * ∑ i : ι, degree theta * conjs i h := by
          congr 1
          rw [Finset.mul_sum]
    _ = (n : ℂ) * ∑ i : ι, degree (conjs i) * conjs i h := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hdegTheta i]


lemma proposition_1_5_part_c_orthogonal
    {G H ι : Type*} [Finite G] [Finite H] [Fintype ι]
    (phi : ClassFunction H) (conjs : ι → ClassFunction H)
    (r : ℕ) (indPhi chi : ClassFunction G) (chiRes : ClassFunction H)
    (hFR : scalarProduct G indPhi chi = scalarProduct H phi chiRes)
    (hres : chiRes = fun h => (r : ℂ) * ∑ i : ι, conjs i h)
    (horth : ∀ i : ι, scalarProduct H phi (conjs i) = 0) :
    scalarProduct G indPhi chi = 0 := by
  calc
    scalarProduct G indPhi chi = scalarProduct H phi chiRes := hFR
    _ = scalarProduct H phi (fun h => (r : ℂ) * ∑ i : ι, conjs i h) := by rw [hres]
    _ = scalarProduct H phi ((r : ℂ) • fun h => ∑ i : ι, conjs i h) := by rfl
    _ = star (r : ℂ) * scalarProduct H phi (fun h => ∑ i : ι, conjs i h) := by
          rw [scalarProduct_smul_right]
    _ = star (r : ℂ) * ∑ i : ι, scalarProduct H phi (conjs i) := by
          rw [scalarProduct_fintype_sum_right]
    _ = star (r : ℂ) * 0 := by
          congr 1
          refine Finset.sum_eq_zero ?_
          intro i hi
          exact horth i
    _ = 0 := by simp


lemma proposition_1_5_part_c_nonconjugate
    {G H ι : Type*} [Finite G] [Finite H] [Fintype ι]
    (phi : ClassFunction H) (conjs : ι → ClassFunction H)
    (r : ℕ) (indPhi chi : ClassFunction G) (chiRes : ClassFunction H)
    (hFR : scalarProduct G indPhi chi = scalarProduct H phi chiRes)
    (hres : chiRes = fun h => (r : ℂ) * ∑ i : ι, conjs i h)
    (hnotConj : ∀ i : ι, phi ≠ conjs i)
    (horthDistinct :
      ∀ i : ι, phi ≠ conjs i → scalarProduct H phi (conjs i) = 0) :
    scalarProduct G indPhi chi = 0 := by
  have horth : ∀ i : ι, scalarProduct H phi (conjs i) = 0 := by
    intro i
    exact horthDistinct i (hnotConj i)
  exact proposition_1_5_part_c_orthogonal phi conjs r indPhi chi chiRes hFR hres horth


lemma proposition_1_5_part_c_conjugate_induced_of_eq
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (g : G)
    (hphi : phi = conjugateOnNormal H theta g) :
    inducedCF H phi = inducedCF H theta := by
  rw [hphi]
  exact inducedCF_conjugateOnNormal H theta g

lemma proposition_1_5_part_c_conjugate_induced_of_fiber
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta phi : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (i : ι) (g : G)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hgi : fiber g = i)
    (hphi : phi = conjs i) :
    inducedCF H phi = inducedCF H theta := by
  have hconj : phi = conjugateOnNormal H theta g := by
    rw [hphi]
    have hgfiber := hfiber g
    rw [hgi] at hgfiber
    exact hgfiber.symm
  exact proposition_1_5_part_c_conjugate_induced_of_eq H phi theta g hconj

lemma proposition_1_5_part_c_conjugate_induced_of_exists
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta phi : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (i : ι)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hphi : phi = conjs i)
    (hexists : ∃ g : G, fiber g = i) :
    inducedCF H phi = inducedCF H theta := by
  rcases hexists with ⟨g, hgi⟩
  exact proposition_1_5_part_c_conjugate_induced_of_fiber
    H theta phi conjs fiber i g hfiber hgi hphi

lemma fiber_exists_of_count
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    (H : Subgroup G) [Finite H]
    (fiber : G → ι) (r : ℕ)
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hr : r ≠ 0) (i : ι) :
    ∃ g : G, fiber g = i := by
  have hHpos : 0 < Nat.card H := Finite.card_pos_iff.mpr ⟨(1 : H)⟩
  have hfiberPos : 0 < Nat.card {x // fiber x = i} := by
    rw [hcount i]
    exact Nat.mul_pos hHpos (Nat.pos_of_ne_zero hr)
  haveI : Nonempty {x // fiber x = i} := Finite.card_pos_iff.mp hfiberPos
  let g0 : {x // fiber x = i} := Classical.choice inferInstance
  exact ⟨g0.1, g0.2⟩

lemma proposition_1_5_part_c_nonconjugate_induced
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hnotConj : ∀ i : ι, phi ≠ conjs i)
    (horthDistinct :
      ∀ i : ι, phi ≠ conjs i → scalarProduct H phi (conjs i) = 0) :
    scalarProduct G (inducedCF H phi) (inducedCF H theta) = 0 := by
  have hFR :
      scalarProduct G (inducedCF H phi) (inducedCF H theta) =
        scalarProduct H phi (subgroupRestriction H (inducedCF H theta)) :=
    inducedClassFunction_frobenius H phi (inducedCF H theta)
      (inducedCF_isClassFunction H theta)
  have hchi_formula :
      ∀ h : H,
        inducedCF H theta h = (Nat.card H : ℂ)⁻¹ * ∑ x : G, conjugateOnNormal H theta x h := by
    intro h
    rw [inducedCF, inducedClassFunction_formula_on_subgroup H theta h]
    simp [conjugateOnNormal]
  have hparta :
      subgroupRestriction H (inducedCF H theta) = fun h => (r : ℂ) * ∑ i : ι, conjs i h :=
    proposition_1_5_part_a H theta fiber conjs r (inducedCF H theta) hchi_formula hfiber hcount
  exact proposition_1_5_part_c_nonconjugate phi conjs r (inducedCF H phi) (inducedCF H theta)
    (subgroupRestriction H (inducedCF H theta)) hFR hparta hnotConj horthDistinct


lemma proposition_1_5_part_c_exists_of_nonzero'
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (horthDistinct :
      ∀ i : ι, phi ≠ conjs i → scalarProduct H phi (conjs i) = 0)
    (hcases :
      (∃ i : ι, phi = conjs i) ∨
        (∀ i : ι, phi ≠ conjs i))
    (hne : scalarProduct G (inducedCF H phi) (inducedCF H theta) ≠ 0) :
    ∃ i : ι, phi = conjs i := by
  rcases hcases with hconj | hnotConj
  · exact hconj
  · exfalso
    exact hne <| proposition_1_5_part_c_nonconjugate_induced
      H phi theta conjs fiber r hfiber hcount hnotConj horthDistinct

lemma conjugateOnNormal_mul
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (a b : G) :
    conjugateOnNormal H theta (a * b) =
      conjugateOnNormal H (conjugateOnNormal H theta a) b := by
  funext h
  simp [conjugateOnNormal, mul_assoc]

lemma conjugateOnNormal_conjugateCharacter
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (g : G) :
    conjugateOnNormal H (conjugateCharacter theta) g =
      conjugateCharacter (conjugateOnNormal H theta g) := by
  funext h
  rfl

lemma exists_sq_pow_eq_self_of_odd_natCard
    {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (g : G) :
    ∃ n : ℕ, (g * g) ^ n = g := by
  have hodd_order : Odd (orderOf g) :=
    Odd.of_dvd_nat hodd (orderOf_dvd_natCard g)
  rcases hodd_order with ⟨m, hm⟩
  use m + 1
  have hpow : (g * g) ^ (m + 1) = g ^ (2 * (m + 1)) := by
    rw [show g * g = g ^ 2 by simp [pow_succ]]
    rw [← pow_mul]
  calc
    (g * g) ^ (m + 1) = g ^ (2 * (m + 1)) := hpow
    _ = g ^ (orderOf g + 1) := by
      congr 1
      omega
    _ = g := by
      rw [pow_add, pow_orderOf_eq_one]
      simp

lemma conjugateOnNormal_pow_eq_self
    {G : Type*} [Group G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) {a : G}
    (ha : conjugateOnNormal H theta a = theta) :
    ∀ n : ℕ, conjugateOnNormal H theta (a ^ n) = theta
  | 0 => by
      simpa using conjugateOnNormal_one H theta
  | n + 1 => by
      rw [pow_succ, conjugateOnNormal_mul]
      rw [conjugateOnNormal_pow_eq_self H theta ha n, ha]

lemma odd_conjugate_eq_conjugateCharacter
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    {i : ι} (hi : conjs i = conjugateCharacter theta) :
    theta = conjugateCharacter theta := by
  rcases fiber_exists_of_count H fiber r hcount hr i with ⟨g, hgi⟩
  have hgbar : conjugateOnNormal H theta g = conjugateCharacter theta := by
    rw [hfiber g, hgi, hi]
  have hg2 : conjugateOnNormal H theta (g * g) = theta := by
    rw [conjugateOnNormal_mul]
    rw [hgbar]
    rw [conjugateOnNormal_conjugateCharacter]
    rw [hgbar]
    ext h
    simp [conjugateCharacter]
  rcases exists_sq_pow_eq_self_of_odd_natCard hodd g with ⟨n, hn⟩
  have hfixg : conjugateOnNormal H theta g = theta := by
    rw [← hn]
    exact conjugateOnNormal_pow_eq_self H theta hg2 n
  exact hfixg.symm.trans hgbar

lemma proposition_1_5_part_e
    {K G ι : Type*} [Finite K] [Finite G] [Fintype ι]
    (theta : ClassFunction K) (conjs : ι → ClassFunction K) (chi : ClassFunction G)
    (hpartc :
      scalarProduct G chi (conjugateCharacter chi) ≠ 0 →
        ∃ i : ι, conjs i = conjugateCharacter theta)
    (hoddstep :
      ∀ i : ι, conjs i = conjugateCharacter theta →
        theta = conjugateCharacter theta)
    (hexclude : theta ≠ conjugateCharacter theta) :
    orthogonal G chi (conjugateCharacter chi) := by
  rw [orthogonal_iff]
  by_contra hne
  rcases hpartc hne with ⟨i, hi⟩
  exact hexclude (hoddstep i hi)

public theorem conjugateCharacter_inducedCF
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) :
    conjugateCharacter (inducedCF H theta) = inducedCF H (conjugateCharacter theta) := by
  classical
  funext g
  unfold conjugateCharacter inducedCF inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0))
        =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by
          simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
          rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then (conjugateCharacter theta) ⟨x * g * x⁻¹, hx⟩ else 0) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hmem : x * g * x⁻¹ ∈ H
          · simp [hmem]
            rfl
          · simp [hmem]

lemma proposition_1_5_part_c_bar_of_nonzero
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (horthDistinct_bar :
      ∀ i : ι, conjugateCharacter theta ≠ conjs i →
        scalarProduct H (conjugateCharacter theta) (conjs i) = 0)
    (hne :
      scalarProduct G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) ≠ 0) :
    ∃ i : ι, conjs i = conjugateCharacter theta := by
  have hcases_bar :
      (∃ i : ι, conjugateCharacter theta = conjs i) ∨
        (∀ i : ι, conjugateCharacter theta ≠ conjs i) := by
    classical
    by_cases h : ∃ i : ι, conjugateCharacter theta = conjs i
    · exact Or.inl h
    · exact Or.inr (by intro i hi; exact h ⟨i, hi⟩)
  have hne' : scalarProduct G (inducedCF H (conjugateCharacter theta)) (inducedCF H theta) ≠ 0 := by
    have hne'' : scalarProduct G (inducedCF H theta) (inducedCF H (conjugateCharacter theta)) ≠ 0 := by
      simpa [conjugateCharacter_inducedCF H theta] using hne
    exact (scalarProduct_ne_zero_swap (inducedCF H theta)
      (inducedCF H (conjugateCharacter theta))).mp hne''
  rcases proposition_1_5_part_c_exists_of_nonzero'
      H (conjugateCharacter theta) theta conjs fiber r hfiber hcount
      horthDistinct_bar hcases_bar hne' with ⟨i, hi⟩
  exact ⟨i, hi.symm⟩

lemma proposition_1_5_part_e_induced
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (horthDistinct_bar :
      ∀ i : ι, conjugateCharacter theta ≠ conjs i →
        scalarProduct H (conjugateCharacter theta) (conjs i) = 0)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    (hexclude : theta ≠ conjugateCharacter theta) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) := by
  apply proposition_1_5_part_e theta conjs (inducedCF H theta)
  · intro hne
    exact proposition_1_5_part_c_bar_of_nonzero
      H theta conjs fiber r hfiber hcount horthDistinct_bar hne
  · intro i hi
    exact odd_conjugate_eq_conjugateCharacter H theta conjs fiber r
      hfiber hcount hr hodd hi
  · exact hexclude

lemma odd_natCard_subgroup_of_odd
    {G : Type*} [Group G] [Finite G] (H : Subgroup G)
    (hodd : Odd (Nat.card G)) :
    Odd (Nat.card H) :=
  Odd.of_dvd_nat hodd H.card_subgroup_dvd_card

open scoped Classical in
public lemma scalarProduct_representation_char_eq_orthonormal
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ] :
    scalarProduct G ρ.character σ.character =
      if Nonempty (Representation.Equiv σ ρ) then (1 : ℂ) else 0 := by
  classical
  have hcard : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := G)).ne'
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard
  calc
    scalarProduct G ρ.character σ.character =
        (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * σ.character g⁻¹ := by
          unfold scalarProduct
          congr 1
          refine Finset.sum_congr rfl ?_
          intro g _hg
          rw [representation_character_inv_eq_star_character σ g]
    _ = if Nonempty (Representation.Equiv σ ρ) then (1 : ℂ) else 0 := by
          simpa using (Representation.char_orthonormal (ρ := ρ) (σ := σ))

public lemma scalarProduct_representation_char_eq_zero_of_ne
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    [Representation.IsIrreducible ρ] [Representation.IsIrreducible σ]
    (hne : ρ.character ≠ σ.character) :
    scalarProduct G ρ.character σ.character = 0 := by
  classical
  rw [scalarProduct_representation_char_eq_orthonormal ρ σ]
  by_cases hIso : Nonempty (Representation.Equiv σ ρ)
  · rcases hIso with ⟨e⟩
    have hchars : ρ.character = σ.character := (Representation.char_iso e).symm
    exact False.elim (hne hchars)
  · simp [hIso]

public lemma scalarProduct_representation_char_self
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    scalarProduct G ρ.character ρ.character = 1 := by
  classical
  letI : Representation.IsIrreducible ρ := hρ
  have horth := scalarProduct_representation_char_eq_orthonormal ρ ρ
  have hnonempty : Nonempty (Representation.Equiv ρ ρ) :=
    ⟨Representation.Equiv.refl ρ⟩
  simpa [hnonempty] using horth

/-- Two pairs are conjugate exactly when their respective components are
conjugate. -/
public theorem isConj_prod_iff
    {G H : Type*} [Group G] [Group H] (x y : G × H) :
    IsConj x y ↔ IsConj x.1 y.1 ∧ IsConj x.2 y.2 := by
  constructor
  · intro hxy
    rcases (isConj_iff.mp hxy) with ⟨z, hz⟩
    constructor
    · exact isConj_iff.mpr ⟨z.1, congrArg Prod.fst hz⟩
    · exact isConj_iff.mpr ⟨z.2, congrArg Prod.snd hz⟩
  · rintro ⟨hx, hy⟩
    rcases (isConj_iff.mp hx) with ⟨z, hz⟩
    rcases (isConj_iff.mp hy) with ⟨w, hw⟩
    exact isConj_iff.mpr ⟨(z, w), Prod.ext hz hw⟩

/-- Conjugacy classes of a direct product are pairs of conjugacy classes. -/
public def conjClassesProdEquiv
    (G H : Type*) [Group G] [Group H] :
    ConjClasses (G × H) ≃ ConjClasses G × ConjClasses H :=
  (Quotient.congrRight (r := IsConj.setoid (G × H))
      (r' := (IsConj.setoid G).prod (IsConj.setoid H))
      (isConj_prod_iff (G := G) (H := H))).trans
    (Setoid.prodQuotientEquiv
      (IsConj.setoid G) (IsConj.setoid H)).symm


public lemma conjugateCharacter_representationCharacter_eq_dual
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    conjugateCharacter ρ.character = ρ.dual.character := by
  funext g
  calc
    conjugateCharacter ρ.character g =
        star (ρ.character g) := by
          simp [conjugateCharacter]
    _ = ρ.character g⁻¹ :=
          (representation_character_inv_eq_star_character ρ g).symm
    _ = ρ.dual.character g := by
          rw [Representation.char_dual]

public theorem isIrreducibleCharacterOnGroup_conjugateCharacter
    {G : Type u} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ) :
    IsIrreducibleCharacterOnGroup (conjugateCharacter χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨Module.finrank ℂ (Module.Dual ℂ (Fin n → ℂ)),
    standardizeRepresentation ρ.dual, ?_, ?_⟩
  · exact standardizeRepresentation_irreducible ρ.dual
      (representation_dual_irreducible_of ρ hρirr)
  · calc
      conjugateCharacter χ = conjugateCharacter ρ.character := by rw [hχchar]
      _ = ρ.dual.character := conjugateCharacter_representationCharacter_eq_dual ρ
      _ = (standardizeRepresentation ρ.dual).character := by
            ext g
            exact (standardizeRepresentation_character ρ.dual g).symm

public theorem conjugateCharacter_principalCharacter
    {G : Type u} [Group G] :
    conjugateCharacter (principalCharacter G) = principalCharacter G := by
  ext g
  simp [conjugateCharacter, principalCharacter]


public lemma scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (phi psi : ClassFunction G)
    (phiRep : Representation ℂ G V) (psiRep : Representation ℂ G W)
    (hphi : phi = phiRep.character)
    (hpsi : psi = psiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hpsi_irreducible : Representation.IsIrreducible psiRep)
    (hne : phi ≠ psi) :
    scalarProduct G phi psi = 0 := by
  have hne' : phiRep.character ≠ psiRep.character := by
    intro hchars
    apply hne
    rw [hphi, hpsi]
    exact hchars
  rw [hphi, hpsi]
  letI : Representation.IsIrreducible phiRep := hphi_irreducible
  letI : Representation.IsIrreducible psiRep := hpsi_irreducible
  exact scalarProduct_representation_char_eq_zero_of_ne
    phiRep psiRep hne'

set_option backward.isDefEq.respectTransparency false in
public theorem scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne
    {G : Type*} [Group G] [Finite G]
    {χ : ClassFunction G}
    (hχ : IsIrreducibleCharacterOnGroup χ)
    (hne : χ ≠ principalCharacter G) :
    scalarProduct G χ (principalCharacter G) = 0 := by
  rcases hχ with ⟨_n, ρ, hρ, hχeq⟩
  have htrivChar :
      principalCharacter G = (Representation.trivial ℂ G ℂ).character := by
    ext g
    simp [principalCharacter, Representation.character, Representation.trivial]
  have htrivIrred :
      Representation.IsIrreducible (Representation.trivial ℂ G ℂ) := by
    rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
    exact is_simple_module_of_finrank_eq_one
      (K := ℂ) (A := MonoidAlgebra ℂ G)
      (V := (Representation.trivial ℂ G ℂ).asModule) (CommSemiring.finrank_self ℂ)
  exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    χ (principalCharacter G) ρ (Representation.trivial ℂ G ℂ)
    hχeq htrivChar hρ htrivIrred hne

theorem proposition_1_5_a
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r) :
    subgroupRestriction H (inducedCF H theta) = fun h => (r : ℂ) * ∑ i : ι, conjs i h := by
  have hchi_formula :
      ∀ h : H,
        inducedCF H theta h = (Nat.card H : ℂ)⁻¹ * ∑ x : G, conjugateOnNormal H theta x h := by
    intro h
    rw [inducedCF, inducedClassFunction_formula_on_subgroup H theta h]
    simp [conjugateOnNormal]
  exact proposition_1_5_part_a H theta fiber conjs r
    (inducedCF H theta) hchi_formula hfiber hcount

theorem proposition_1_5_b
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal] (base : ι)
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hbase : conjs base = theta)
    (hself : scalarProduct H (conjs base) (conjs base) = 1)
    (horth_theta :
      ∀ i : ι, i ≠ base → scalarProduct H (conjs i) theta = 0) :
    scalarProduct G (inducedCF H theta) (inducedCF H theta) = r := by
  have hparta := proposition_1_5_a H theta conjs fiber r hfiber hcount
  have hFR_chi :
      scalarProduct G (inducedCF H theta) (inducedCF H theta) =
        scalarProduct H (subgroupRestriction H (inducedCF H theta)) (conjs base) := by
    have hFR :=
      inducedClassFunction_frobenius_right H theta (inducedCF H theta)
        (inducedCF_isClassFunction H theta)
    simpa [hbase] using hFR
  exact proposition_1_5_part_b base theta conjs r (inducedCF H theta)
    (subgroupRestriction H (inducedCF H theta))
    hbase hFR_chi hparta hself horth_theta


theorem proposition_1_5_b_rep
    {G ι V : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal] (base : ι)
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : ι → Representation ℂ H V)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hbase : conjs base = theta)
    (htheta : theta = thetaRep.character)
    (hconjs : ∀ i : ι, conjs i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible : ∀ i : ι, Representation.IsIrreducible (conjRep i))
    (hdistinct : ∀ i : ι, i ≠ base → conjs i ≠ theta) :
    scalarProduct G (inducedCF H theta) (inducedCF H theta) = r := by
  have hself : scalarProduct H (conjs base) (conjs base) = 1 := by
    rw [hbase, htheta]
    exact scalarProduct_representation_char_self thetaRep htheta_irreducible
  have horth_theta :
      ∀ i : ι, i ≠ base → scalarProduct H (conjs i) theta = 0 := by
    intro i hi
    exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      (conjs i) theta (conjRep i) thetaRep
      (hconjs i) htheta (hconj_irreducible i) htheta_irreducible
      (hdistinct i hi)
  exact proposition_1_5_b H base theta conjs fiber r
    hfiber hcount hbase hself horth_theta


theorem proposition_1_5_d
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal] (base : ι)
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hbase : conjs base = theta)
    (hself : scalarProduct H (conjs base) (conjs base) = 1)
    (horth_theta :
      ∀ i : ι, i ≠ base → scalarProduct H (conjs i) theta = 0)
    (hdeg : ∀ i : ι, degree (conjs i) = degree (conjs base))
    (hr : r ≠ 0) :
    (((degree (inducedCF H theta)) /
        scalarProduct G (inducedCF H theta) (inducedCF H theta)) •
        subgroupRestriction H (inducedCF H theta)) =
      (Subgroup.index H : ℂ) • fun h => ∑ i : ι, degree (conjs i) * conjs i h := by
  have hparta := proposition_1_5_a H theta conjs fiber r hfiber hcount
  have hpartb := proposition_1_5_b H base theta conjs fiber r
    hfiber hcount hbase hself horth_theta
  have hchi1 : degree (inducedCF H theta) = (Subgroup.index H : ℂ) * degree (conjs base) := by
    rw [degree_inducedClassFunction H theta, ← hbase]
  exact proposition_1_5_part_d (Subgroup.index H) r theta conjs
    (inducedCF H theta) (subgroupRestriction H (inducedCF H theta))
    base hbase hdeg hchi1 hparta hpartb hr

theorem proposition_1_5_d_rep
    {G ι V : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal] (base : ι)
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : ι → Representation ℂ H V)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hbase : conjs base = theta)
    (htheta : theta = thetaRep.character)
    (hconjs : ∀ i : ι, conjs i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible : ∀ i : ι, Representation.IsIrreducible (conjRep i))
    (hdistinct : ∀ i : ι, i ≠ base → conjs i ≠ theta)
    (hdeg : ∀ i : ι, degree (conjs i) = degree (conjs base))
    (hr : r ≠ 0) :
    (((degree (inducedCF H theta)) /
        scalarProduct G (inducedCF H theta) (inducedCF H theta)) •
        subgroupRestriction H (inducedCF H theta)) =
      (Subgroup.index H : ℂ) • fun h => ∑ i : ι, degree (conjs i) * conjs i h := by
  have hparta := proposition_1_5_a H theta conjs fiber r hfiber hcount
  have hpartb := proposition_1_5_b_rep H base theta conjs fiber r
    thetaRep conjRep hfiber hcount hbase htheta hconjs
    htheta_irreducible hconj_irreducible hdistinct
  have hchi1 : degree (inducedCF H theta) = (Subgroup.index H : ℂ) * degree (conjs base) := by
    rw [degree_inducedClassFunction H theta, ← hbase]
  exact proposition_1_5_part_d (Subgroup.index H) r theta conjs
    (inducedCF H theta) (subgroupRestriction H (inducedCF H theta))
    base hbase hdeg hchi1 hparta hpartb hr

theorem proposition_1_5_c_conjugate
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (theta phi : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (i : ι)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hphi : phi = conjs i)
    (hexists : ∃ g : G, fiber g = i) :
    inducedCF H phi = inducedCF H theta :=
  proposition_1_5_part_c_conjugate_induced_of_exists
    H theta phi conjs fiber i hfiber hphi hexists


theorem proposition_1_5_c_nonconjugate
    {G ι : Type*} [Group G] [Finite G] [Fintype ι]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hnotConj : ∀ i : ι, phi ≠ conjs i)
    (horthDistinct :
      ∀ i : ι, phi ≠ conjs i → scalarProduct H phi (conjs i) = 0) :
    scalarProduct G (inducedCF H phi) (inducedCF H theta) = 0 :=
  proposition_1_5_part_c_nonconjugate_induced
    H phi theta conjs fiber r hfiber hcount hnotConj horthDistinct

theorem proposition_1_5_c_nonconjugate_rep
    {G ι V W : Type*} [Group G] [Finite G] [Fintype ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    [DecidableEq ι] (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (conjs : ι → ClassFunction H)
    (fiber : G → ι) (r : ℕ)
    (phiRep : Representation ℂ H V)
    (conjRep : ι → Representation ℂ H W)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hphi : phi = phiRep.character)
    (hconjs : ∀ i : ι, conjs i = (conjRep i).character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hconj_irreducible : ∀ i : ι, Representation.IsIrreducible (conjRep i))
    (hnotConj : ∀ i : ι, phi ≠ conjs i) :
    scalarProduct G (inducedCF H phi) (inducedCF H theta) = 0 := by
  have horthDistinct :
      ∀ i : ι, phi ≠ conjs i → scalarProduct H phi (conjs i) = 0 := by
    intro i hne
    exact scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
      phi (conjs i) phiRep (conjRep i)
      hphi (hconjs i) hphi_irreducible (hconj_irreducible i) hne
  exact proposition_1_5_c_nonconjugate
    H phi theta conjs fiber r hfiber hcount hnotConj horthDistinct

theorem proposition_1_5_e
    {G ι : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    (horthDistinct_bar :
      ∀ i : ι, conjugateCharacter theta ≠ conjs i →
        scalarProduct H (conjugateCharacter theta) (conjs i) = 0)
    (hexclude : theta ≠ conjugateCharacter theta) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) :=
  proposition_1_5_part_e_induced H theta conjs fiber r hfiber hcount
    horthDistinct_bar hr hodd hexclude

theorem proposition_1_5_e_rep
    {G ι V : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (ρ : Representation ℂ H V)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    (horthDistinct_bar :
      ∀ i : ι, conjugateCharacter theta ≠ conjs i →
        scalarProduct H (conjugateCharacter theta) (conjs i) = 0)
    (htheta : theta = ρ.character)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hne_principal : ρ.character ≠ principalCharacter H) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) := by
  have hoddH : Odd (Nat.card H) := odd_natCard_subgroup_of_odd H hodd
  have hexclude : theta ≠ conjugateCharacter theta := by
    rw [htheta]
    exact proposition_1_1 hoddH ρ hρ_irreducible hne_principal
  exact proposition_1_5_e H theta conjs fiber r hfiber hcount
    hr hodd horthDistinct_bar hexclude


theorem proposition_1_5_e_rep_dual_family
    {G ι V : Type*} [Group G] [Finite G] [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (conjs : ι → ClassFunction H) (fiber : G → ι)
    (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : ι → Representation ℂ H V)
    (hfiber : ∀ x : G, conjugateOnNormal H theta x = conjs (fiber x))
    (hcount : ∀ i : ι, Nat.card {x // fiber x = i} = Nat.card H * r)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    (htheta : theta = thetaRep.character)
    (hconjs : ∀ i : ι, conjs i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible : ∀ i : ι, Representation.IsIrreducible (conjRep i))
    (hne_principal : thetaRep.character ≠ principalCharacter H) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) := by
  have hbar :
      conjugateCharacter theta = thetaRep.dual.character := by
    rw [htheta]
    exact conjugateCharacter_representationCharacter_eq_dual thetaRep
  have horthDistinct_bar :
      ∀ i : ι, conjugateCharacter theta ≠ conjs i →
        scalarProduct H (conjugateCharacter theta) (conjs i) = 0 := by
    intro i hne
    have hθ_irreducible : Representation.IsIrreducible thetaRep.dual :=
      representation_dual_irreducible_of thetaRep htheta_irreducible
    letI : Representation.IsIrreducible thetaRep.dual := hθ_irreducible
    letI : Representation.IsIrreducible (conjRep i) := hconj_irreducible i
    have hne_rep : thetaRep.dual.character ≠ (conjRep i).character := by
      intro hchars
      apply hne
      rw [hbar, hconjs i]
      exact hchars
    have hzero := scalarProduct_representation_char_eq_zero_of_ne
      thetaRep.dual (conjRep i) hne_rep
    rw [hbar, hconjs i]
    exact hzero
  exact proposition_1_5_e_rep H theta conjs fiber r thetaRep
    hfiber hcount hr hodd horthDistinct_bar htheta htheta_irreducible hne_principal

public lemma conjugateOrbit_exists_fiber
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (i : conjugateOrbitIndex H theta) :
    ∃ x : G, conjugateOrbitFiber H theta x = i := by
  refine Quotient.inductionOn i ?_
  intro x
  exact ⟨x, rfl⟩

public def conjugateOrbitFiberEquivInertia
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (a : G) :
    {x : G // conjugateOrbitFiber H theta x = conjugateOrbitFiber H theta a} ≃
      inertiaSubgroup H theta where
  toFun x := by
    refine ⟨x.1 * a⁻¹, ?_⟩
    have hx :
        conjugateOnNormal H theta x.1 = conjugateOnNormal H theta a :=
      Quotient.exact x.2
    change conjugateOnNormal H theta (x.1 * a⁻¹) = theta
    calc
      conjugateOnNormal H theta (x.1 * a⁻¹) =
          conjugateOnNormal H (conjugateOnNormal H theta x.1) a⁻¹ := by
            rw [conjugateOnNormal_mul]
      _ = conjugateOnNormal H (conjugateOnNormal H theta a) a⁻¹ := by
            rw [hx]
      _ = conjugateOnNormal H theta (a * a⁻¹) := by
            rw [conjugateOnNormal_mul]
      _ = theta := by
            simpa using conjugateOnNormal_one H theta
  invFun y := by
    refine ⟨y.1 * a, ?_⟩
    apply Quotient.sound
    change conjugateOnNormal H theta (y.1 * a) = conjugateOnNormal H theta a
    calc
      conjugateOnNormal H theta (y.1 * a) =
          conjugateOnNormal H (conjugateOnNormal H theta y.1) a := by
            rw [conjugateOnNormal_mul]
      _ = conjugateOnNormal H theta a := by
            rw [y.2]
  left_inv x := by
    apply Subtype.ext
    dsimp
    group
  right_inv y := by
    apply Subtype.ext
    dsimp
    group

public lemma conjugateOrbit_fiber_card_eq_inertia
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (a : G) :
    Nat.card {x : G // conjugateOrbitFiber H theta x = conjugateOrbitFiber H theta a} =
      Nat.card (inertiaSubgroup H theta) :=
  Nat.card_congr (conjugateOrbitFiberEquivInertia H theta a)

public lemma conjugateOrbit_fiber_count_of_inertia_card
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (r : ℕ)
    (hcardI : Nat.card (inertiaSubgroup H theta) = Nat.card H * r) :
    ∀ i : conjugateOrbitIndex H theta,
      Nat.card {x : G // conjugateOrbitFiber H theta x = i} = Nat.card H * r := by
  intro i
  rcases conjugateOrbit_exists_fiber H theta i with ⟨a, rfl⟩
  rw [conjugateOrbit_fiber_card_eq_inertia H theta a, hcardI]


lemma subgroup_le_inertia_of_isClassFunction
    {G : Type*} [Group G] (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    H ≤ inertiaSubgroup H theta := by
  intro x hx
  rw [mem_inertiaSubgroup_iff]
  funext h
  change theta ⟨x * (h : G) * x⁻¹, _⟩ = theta h
  exact hclass ⟨x, hx⟩ h

lemma inertia_card_eq_card_mul_relIndex
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H)
    (hHleI : H ≤ inertiaSubgroup H theta) :
    Nat.card (inertiaSubgroup H theta) =
      Nat.card H * H.relIndex (inertiaSubgroup H theta) := by
  let I := inertiaSubgroup H theta
  let K : Subgroup I := H.subgroupOf I
  have hidx : K.index * Nat.card K = Nat.card I := K.index_mul_card
  have hcardK : Nat.card K = Nat.card H := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleI).toEquiv
  calc
    Nat.card I = K.index * Nat.card K := hidx.symm
    _ = H.relIndex I * Nat.card H := by
          change K.index * Nat.card K = K.index * Nat.card H
          rw [hcardK]
    _ = Nat.card H * H.relIndex I := by
          rw [Nat.mul_comm]

lemma inertia_card_eq_card_mul_relIndex_of_isClassFunction
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    Nat.card (inertiaSubgroup H theta) =
      Nat.card H * H.relIndex (inertiaSubgroup H theta) :=
  inertia_card_eq_card_mul_relIndex H theta
    (subgroup_le_inertia_of_isClassFunction H theta hclass)

lemma conjugateOrbit_fiber_count_of_relIndex
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    ∀ i : conjugateOrbitIndex H theta,
      Nat.card {x : G // conjugateOrbitFiber H theta x = i} =
        Nat.card H * H.relIndex (inertiaSubgroup H theta) :=
  conjugateOrbit_fiber_count_of_inertia_card H theta
    (H.relIndex (inertiaSubgroup H theta))
    (inertia_card_eq_card_mul_relIndex_of_isClassFunction H theta hclass)

private lemma relIndex_inertia_ne_zero
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (theta : ClassFunction H) :
    H.relIndex (inertiaSubgroup H theta) ≠ 0 :=
by
  rw [Subgroup.relIndex]
  exact Subgroup.index_ne_zero_of_finite

theorem proposition_1_5_a_orbit
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (r : ℕ)
    (hcount :
      ∀ i : conjugateOrbitIndex H theta,
        Nat.card {x // conjugateOrbitFiber H theta x = i} = Nat.card H * r) :
    subgroupRestriction H (inducedCF H theta) =
      fun h => (r : ℂ) * ∑ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i h := by
  classical
  letI : Fintype (conjugateOrbitIndex H theta) := Fintype.ofFinite _
  exact proposition_1_5_a H theta (conjugateOrbitConj H theta)
    (conjugateOrbitFiber H theta) r (conjugateOrbit_hfiber H theta) hcount

theorem proposition_1_5_b_rep_orbit
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (hcount :
      ∀ i : conjugateOrbitIndex H theta,
        Nat.card {x // conjugateOrbitFiber H theta x = i} = Nat.card H * r)
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i)) :
    scalarProduct G (inducedCF H theta) (inducedCF H theta) = r := by
  classical
  exact proposition_1_5_b_rep H (conjugateOrbitFiber H theta 1) theta
    (conjugateOrbitConj H theta) (conjugateOrbitFiber H theta) r
    thetaRep conjRep (conjugateOrbit_hfiber H theta) hcount
    (conjugateOrbit_base_eq_theta H theta) htheta hconjs
    htheta_irreducible hconj_irreducible
    (by
      intro i hi
      exact conjugateOrbit_conj_ne_theta_of_ne_base H theta i hi)

theorem proposition_1_5_c_conjugate_orbit
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta phi : ClassFunction H) (i : conjugateOrbitIndex H theta)
    (hphi : phi = conjugateOrbitConj H theta i) :
    inducedCF H phi = inducedCF H theta := by
  classical
  exact proposition_1_5_c_conjugate H theta phi
    (conjugateOrbitConj H theta) (conjugateOrbitFiber H theta) i
    (conjugateOrbit_hfiber H theta) hphi
    (conjugateOrbit_exists_fiber H theta i)

theorem proposition_1_5_c_nonconjugate_rep_orbit
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H) (r : ℕ)
    (phiRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H W)
    (hcount :
      ∀ i : conjugateOrbitIndex H theta,
        Nat.card {x // conjugateOrbitFiber H theta x = i} = Nat.card H * r)
    (hphi : phi = phiRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i))
    (hnotConj : ∀ i : conjugateOrbitIndex H theta, phi ≠ conjugateOrbitConj H theta i) :
    scalarProduct G (inducedCF H phi) (inducedCF H theta) = 0 := by
  classical
  exact proposition_1_5_c_nonconjugate_rep H phi theta
    (conjugateOrbitConj H theta) (conjugateOrbitFiber H theta) r
    phiRep conjRep (conjugateOrbit_hfiber H theta) hcount
    hphi hconjs hphi_irreducible hconj_irreducible hnotConj

theorem proposition_1_5_d_rep_orbit
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (hcount :
      ∀ i : conjugateOrbitIndex H theta,
        Nat.card {x // conjugateOrbitFiber H theta x = i} = Nat.card H * r)
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i))
    (hr : r ≠ 0) :
    (((degree (inducedCF H theta)) /
        scalarProduct G (inducedCF H theta) (inducedCF H theta)) •
        subgroupRestriction H (inducedCF H theta)) =
      (Subgroup.index H : ℂ) • fun h =>
        ∑ i : conjugateOrbitIndex H theta,
          degree (conjugateOrbitConj H theta i) * conjugateOrbitConj H theta i h := by
  classical
  letI : Fintype (conjugateOrbitIndex H theta) := Fintype.ofFinite _
  exact proposition_1_5_d_rep H (conjugateOrbitFiber H theta 1) theta
    (conjugateOrbitConj H theta) (conjugateOrbitFiber H theta) r
    thetaRep conjRep (conjugateOrbit_hfiber H theta) hcount
    (conjugateOrbit_base_eq_theta H theta) htheta hconjs
    htheta_irreducible hconj_irreducible
    (by
      intro i hi
      exact conjugateOrbit_conj_ne_theta_of_ne_base H theta i hi)
    (by
      intro i
      rw [degree_conjugateOrbitConj H theta i,
        degree_conjugateOrbitConj H theta (conjugateOrbitFiber H theta 1)])
    hr

theorem proposition_1_5_e_rep_dual_orbit
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (r : ℕ)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (hcount :
      ∀ i : conjugateOrbitIndex H theta,
        Nat.card {x // conjugateOrbitFiber H theta x = i} = Nat.card H * r)
    (hr : r ≠ 0)
    (hodd : Odd (Nat.card G))
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i))
    (hne_principal : thetaRep.character ≠ principalCharacter H) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) := by
  classical
  exact proposition_1_5_e_rep_dual_family H theta (conjugateOrbitConj H theta)
    (conjugateOrbitFiber H theta) r thetaRep conjRep
    (conjugateOrbit_hfiber H theta) hcount hr hodd htheta hconjs
    htheta_irreducible hconj_irreducible hne_principal


theorem proposition_1_5_a_orbit_relIndex
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (hclass : IsClassFunction theta) :
    subgroupRestriction H (inducedCF H theta) =
      fun h => (H.relIndex (inertiaSubgroup H theta) : ℂ) *
        ∑ i : conjugateOrbitIndex H theta, conjugateOrbitConj H theta i h :=
  proposition_1_5_a_orbit H theta (H.relIndex (inertiaSubgroup H theta))
    (conjugateOrbit_fiber_count_of_relIndex H theta hclass)

theorem proposition_1_5_b_rep_orbit_relIndex
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i)) :
    scalarProduct G (inducedCF H theta) (inducedCF H theta) =
      H.relIndex (inertiaSubgroup H theta) :=
by
  have hclass : IsClassFunction theta := by
    rw [htheta]
    exact representationCharacter_isClassFunction thetaRep
  exact proposition_1_5_b_rep_orbit H theta (H.relIndex (inertiaSubgroup H theta))
    thetaRep conjRep (conjugateOrbit_fiber_count_of_relIndex H theta hclass)
    htheta hconjs htheta_irreducible hconj_irreducible

theorem proposition_1_5_c_nonconjugate_rep_orbit_relIndex
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (phi theta : ClassFunction H)
    (phiRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H W)
    (hphi : phi = phiRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i))
    (hnotConj : ∀ i : conjugateOrbitIndex H theta, phi ≠ conjugateOrbitConj H theta i) :
    scalarProduct G (inducedCF H phi) (inducedCF H theta) = 0 :=
by
  let base : conjugateOrbitIndex H theta := conjugateOrbitFiber H theta 1
  have htheta :
      theta = (conjRep base).character := by
    rw [← conjugateOrbit_base_eq_theta H theta]
    exact hconjs base
  have hclass : IsClassFunction theta := by
    rw [htheta]
    exact representationCharacter_isClassFunction (conjRep base)
  exact proposition_1_5_c_nonconjugate_rep_orbit H phi theta
    (H.relIndex (inertiaSubgroup H theta)) phiRep conjRep
    (conjugateOrbit_fiber_count_of_relIndex H theta hclass)
    hphi hconjs hphi_irreducible hconj_irreducible hnotConj

theorem proposition_1_5_d_rep_orbit_relIndex
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i)) :
    (((degree (inducedCF H theta)) /
        scalarProduct G (inducedCF H theta) (inducedCF H theta)) •
        subgroupRestriction H (inducedCF H theta)) =
      (Subgroup.index H : ℂ) • fun h =>
        ∑ i : conjugateOrbitIndex H theta,
          degree (conjugateOrbitConj H theta i) * conjugateOrbitConj H theta i h :=
by
  have hclass : IsClassFunction theta := by
    rw [htheta]
    exact representationCharacter_isClassFunction thetaRep
  exact proposition_1_5_d_rep_orbit H theta (H.relIndex (inertiaSubgroup H theta))
    thetaRep conjRep (conjugateOrbit_fiber_count_of_relIndex H theta hclass)
    htheta hconjs htheta_irreducible hconj_irreducible
    (relIndex_inertia_ne_zero H theta)

theorem proposition_1_5_e_rep_dual_orbit_relIndex
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H)
    (thetaRep : Representation ℂ H V)
    (conjRep : conjugateOrbitIndex H theta → Representation ℂ H V)
    (hodd : Odd (Nat.card G))
    (htheta : theta = thetaRep.character)
    (hconjs :
      ∀ i : conjugateOrbitIndex H theta,
        conjugateOrbitConj H theta i = (conjRep i).character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hconj_irreducible :
      ∀ i : conjugateOrbitIndex H theta, Representation.IsIrreducible (conjRep i))
    (hne_principal : thetaRep.character ≠ principalCharacter H) :
    orthogonal G (inducedCF H theta) (conjugateCharacter (inducedCF H theta)) :=
by
  have hclass : IsClassFunction theta := by
    rw [htheta]
    exact representationCharacter_isClassFunction thetaRep
  exact proposition_1_5_e_rep_dual_orbit H theta (H.relIndex (inertiaSubgroup H theta))
    thetaRep conjRep (conjugateOrbit_fiber_count_of_relIndex H theta hclass)
    (relIndex_inertia_ne_zero H theta) hodd htheta hconjs htheta_irreducible
    hconj_irreducible hne_principal

public theorem proposition_1_5_a_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V) :
    subgroupRestriction H (inducedCF H thetaRep.character) =
      fun h =>
        (H.relIndex (inertiaSubgroup H thetaRep.character) : ℂ) *
          ∑ i : conjugateOrbitIndex H thetaRep.character,
            conjugateOrbitConj H thetaRep.character i h :=
  proposition_1_5_a_orbit_relIndex H thetaRep.character
    (representationCharacter_isClassFunction thetaRep)

public theorem proposition_1_5_b_rep_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep) :
    scalarProduct G
        (inducedCF H thetaRep.character)
        (inducedCF H thetaRep.character) =
      H.relIndex (inertiaSubgroup H thetaRep.character) :=
  proposition_1_5_b_rep_orbit_relIndex H thetaRep.character
    thetaRep (conjugateOrbitRepresentation H thetaRep) rfl
    (conjugateOrbitConj_representationCharacter H thetaRep)
    htheta_irreducible
    (conjugateOrbitRepresentation_irreducible H thetaRep htheta_irreducible)

public theorem proposition_1_5_b_norm_one_rep_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hr :
      H.relIndex (inertiaSubgroup H thetaRep.character) = 1) :
    scalarProduct G
        (inducedCF H thetaRep.character)
        (inducedCF H thetaRep.character) = 1 := by
  simpa [hr] using
    proposition_1_5_b_rep_orbit_relIndex_canonical H thetaRep htheta_irreducible

public theorem proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hr :
      H.relIndex (inertiaSubgroup H thetaRep.character) = 1) :
    IsIrreducibleCharacterOnGroup (inducedCF H thetaRep.character) := by
  have hnorm :
      scalarProduct G (inducedCF H thetaRep.character)
        (inducedCF H thetaRep.character) = 1 := by
    simpa [hr] using
      proposition_1_5_b_rep_orbit_relIndex_canonical H thetaRep htheta_irreducible
  haveI : FiniteDimensional ℂ (Representation.IndV H.subtype thetaRep) :=
    Theory.Representation.finiteDimensional_ind H thetaRep
  have hIndIrr : Representation.IsIrreducible (Representation.ind H.subtype thetaRep) := by
    exact (Theory.Character.irreducible_iff_character_norm_one
      (ρ := Representation.ind H.subtype thetaRep)).2
      (by
        change scalarProduct G (Representation.ind H.subtype thetaRep).character
          (Representation.ind H.subtype thetaRep).character = 1
        rw [← inducedCF_eq_representation_character_pf15 H thetaRep]
        exact hnorm)
  simpa [inducedCF_eq_representation_character_pf15 H thetaRep] using
    isIrreducibleCharacterOnGroup_of_representation
      (Representation.ind H.subtype thetaRep) hIndIrr

public theorem proposition_1_5_c_conjugate_orbit_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (phi : ClassFunction H)
    (i : conjugateOrbitIndex H thetaRep.character)
    (hphi :
      phi = conjugateOrbitConj H thetaRep.character i) :
    inducedCF H phi = inducedCF H thetaRep.character :=
  proposition_1_5_c_conjugate_orbit H thetaRep.character phi i hphi

public theorem proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (phi : ClassFunction H)
    (phiRep : Representation ℂ H V) (thetaRep : Representation ℂ H W)
    (hphi : phi = phiRep.character)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hnotConj :
      ∀ i : conjugateOrbitIndex H thetaRep.character,
        phi ≠ conjugateOrbitConj H thetaRep.character i) :
    scalarProduct G (inducedCF H phi)
        (inducedCF H thetaRep.character) = 0 :=
  proposition_1_5_c_nonconjugate_rep_orbit_relIndex H phi
    thetaRep.character phiRep (conjugateOrbitRepresentation H thetaRep)
    hphi (conjugateOrbitConj_representationCharacter H thetaRep)
    hphi_irreducible
    (conjugateOrbitRepresentation_irreducible H thetaRep htheta_irreducible)
    hnotConj

public theorem proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H : Subgroup G) [Finite H] [H.Normal]
    (phiRep : Representation ℂ H V) (thetaRep : Representation ℂ H W)
    (hphi_irreducible : Representation.IsIrreducible phiRep)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hInd : inducedCF H phiRep.character = inducedCF H thetaRep.character) :
    ∃ i : conjugateOrbitIndex H thetaRep.character,
      phiRep.character = conjugateOrbitConj H thetaRep.character i := by
  by_contra hnone
  have hnotConj :
      ∀ i : conjugateOrbitIndex H thetaRep.character,
        phiRep.character ≠ conjugateOrbitConj H thetaRep.character i := by
    intro i hi
    exact hnone ⟨i, hi⟩
  have horth := proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
    H phiRep.character phiRep thetaRep rfl hphi_irreducible htheta_irreducible hnotConj
  have hzero : scalarProduct G (inducedCF H thetaRep.character)
      (inducedCF H thetaRep.character) = 0 := by
    simpa [hInd] using horth
  have hself :=
    proposition_1_5_b_rep_orbit_relIndex_canonical H thetaRep htheta_irreducible
  have hrel_ne : H.relIndex (inertiaSubgroup H thetaRep.character) ≠ 0 := by
    haveI : (H.subgroupOf (inertiaSubgroup H thetaRep.character)).FiniteIndex :=
      inferInstance
    simpa [Subgroup.relIndex] using
      (Subgroup.FiniteIndex.index_ne_zero
        (H := H.subgroupOf (inertiaSubgroup H thetaRep.character)))
  have hself_ne : scalarProduct G (inducedCF H thetaRep.character)
      (inducedCF H thetaRep.character) ≠ 0 := by
    rw [hself]
    exact_mod_cast hrel_ne
  exact hself_ne hzero

public theorem proposition_1_5_d_rep_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (htheta_irreducible : Representation.IsIrreducible thetaRep) :
    (((degree (inducedCF H thetaRep.character)) /
        scalarProduct G
          (inducedCF H thetaRep.character)
          (inducedCF H thetaRep.character)) •
        subgroupRestriction H (inducedCF H thetaRep.character)) =
      (Subgroup.index H : ℂ) • fun h =>
        ∑ i : conjugateOrbitIndex H thetaRep.character,
          degree (conjugateOrbitConj H thetaRep.character i) *
            conjugateOrbitConj H thetaRep.character i h :=
  proposition_1_5_d_rep_orbit_relIndex H thetaRep.character
    thetaRep (conjugateOrbitRepresentation H thetaRep) rfl
    (conjugateOrbitConj_representationCharacter H thetaRep)
    htheta_irreducible
    (conjugateOrbitRepresentation_irreducible H thetaRep htheta_irreducible)

public theorem proposition_1_5_e_rep_dual_orbit_relIndex_canonical
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (thetaRep : Representation ℂ H V)
    (hodd : Odd (Nat.card G))
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hne_principal : thetaRep.character ≠ principalCharacter H) :
    orthogonal G
      (inducedCF H thetaRep.character)
      (conjugateCharacter (inducedCF H thetaRep.character)) :=
  proposition_1_5_e_rep_dual_orbit_relIndex H thetaRep.character
    thetaRep (conjugateOrbitRepresentation H thetaRep) hodd rfl
    (conjugateOrbitConj_representationCharacter H thetaRep)
    htheta_irreducible
    (conjugateOrbitRepresentation_irreducible H thetaRep htheta_irreducible)
    hne_principal

end CFSG.Section1
