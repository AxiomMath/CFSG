module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import Mathlib.GroupTheory.DoubleCoset

namespace CFSG
end CFSG
open CFSG

/-!
# Mackey infrastructure for Peterfalvi, Section 1, Proposition (1.7)

This file starts the direct local formalization of the Mackey machinery needed
for `PFsection1_7`, without wrapping an external Mackey/Clifford theorem.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1

universe v
universe u

set_option maxHeartbeats 800000

@[expose] public def mackeyIntersection
    {G : Type*} [Group G] (S K : Subgroup G) (a : G) : Subgroup K where
  carrier := {k : K | a * (k : G) * a⁻¹ ∈ S}
  one_mem' := by
    simp
  mul_mem' := by
    intro x y hx hy
    change a * ((x : G) * (y : G)) * a⁻¹ ∈ S
    have hx' : a * (x : G) * a⁻¹ ∈ S := hx
    have hy' : a * (y : G) * a⁻¹ ∈ S := hy
    have hmul :
        (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹) ∈ S :=
      S.mul_mem hx' hy'
    simpa [mul_assoc] using hmul
  inv_mem' := by
    intro x hx
    change a * ((x : G)⁻¹) * a⁻¹ ∈ S
    have hx' : a * (x : G) * a⁻¹ ∈ S := hx
    have hinv := S.inv_mem hx'
    simpa [mul_assoc] using hinv

@[expose] public def mackeyConjugateRestriction
    {G : Type*} [Group G] (S K : Subgroup G) (a : G)
    (phi : ClassFunction S) : ClassFunction (mackeyIntersection S K a) :=
  fun k => phi ⟨a * ((k : mackeyIntersection S K a) : K) * a⁻¹, k.2⟩


public theorem mackeyIntersection_mem_iff
    {G : Type*} [Group G] (S K : Subgroup G) (a : G) (k : K) :
    k ∈ mackeyIntersection S K a ↔ a * (k : G) * a⁻¹ ∈ S :=
  Iff.rfl


@[expose] public noncomputable def mackeySummand
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) : ClassFunction K :=
  inducedCF (mackeyIntersection S K a) (mackeyConjugateRestriction S K a phi)


@[expose] public noncomputable def mackeySummandFormula
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) : ClassFunction K :=
  by
    classical
    intro k
    exact (Nat.card (mackeyIntersection S K a) : ℂ)⁻¹ * ∑ x : K,
      if hx : x * k * x⁻¹ ∈ mackeyIntersection S K a then
        phi ⟨a * (((⟨x * k * x⁻¹, hx⟩ :
            mackeyIntersection S K a) : K) : G) * a⁻¹,
          (⟨x * k * x⁻¹, hx⟩ : mackeyIntersection S K a).2⟩
      else 0

public theorem mackeySummand_apply
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) (k : K) :
    mackeySummand S K a phi k = mackeySummandFormula S K a phi k := by
  unfold mackeySummand mackeySummandFormula inducedCF inducedClassFunction
    mackeyConjugateRestriction
  rfl

@[expose] public noncomputable def mackeySummandAmbientFormula
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) : ClassFunction K :=
  by
    classical
    intro k
    exact (Nat.card (mackeyIntersection S K a) : ℂ)⁻¹ * ∑ x : K,
      if hx : a * (((x * k * x⁻¹ : K) : G)) * a⁻¹ ∈ S then
        phi ⟨a * (((x * k * x⁻¹ : K) : G)) * a⁻¹, hx⟩
      else 0

@[expose] public noncomputable def mackeySummandAmbientInner
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) (k : K) : ℂ :=
  by
    classical
    exact ∑ x : K,
      if hx : a * (((x * k * x⁻¹ : K) : G)) * a⁻¹ ∈ S then
        phi ⟨a * (((x * k * x⁻¹ : K) : G)) * a⁻¹, hx⟩
      else 0

public theorem mackeySummandAmbientFormula_apply
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) (k : K) :
    mackeySummandAmbientFormula S K a phi k =
      (Nat.card (mackeyIntersection S K a) : ℂ)⁻¹ *
        mackeySummandAmbientInner S K a phi k := by
  unfold mackeySummandAmbientFormula mackeySummandAmbientInner
  rfl

public theorem mackeySummandFormula_eq_ambient
    {G : Type*} [Group G] (S K : Subgroup G) [Finite K]
    (a : G) (phi : ClassFunction S) :
    mackeySummandFormula S K a phi = mackeySummandAmbientFormula S K a phi := by
  unfold mackeySummandFormula mackeySummandAmbientFormula
  rfl

public theorem mackeyIntersection_self_eq_top_of_mem
    {G : Type*} [Group G] (S : Subgroup G) {a : G} (ha : a ∈ S) :
    mackeyIntersection S S a = ⊤ := by
  ext k
  constructor
  · intro _hk
    simp
  · intro _hk
    change a * (k : G) * a⁻¹ ∈ S
    exact S.mul_mem (S.mul_mem ha k.2) (S.inv_mem ha)

public theorem mackeySummandAmbientInner_self_eq_card_mul_of_mem
    {G : Type*} [Group G] (S : Subgroup G) [Finite S]
    {a : G} (ha : a ∈ S) (phi : ClassFunction S) (hphi : IsClassFunction phi)
    (k : S) :
    mackeySummandAmbientInner S S a phi k = (Nat.card S : ℂ) * phi k := by
  classical
  unfold mackeySummandAmbientInner
  calc
    (∑ x : S,
      if hx : a * (((x * k * x⁻¹ : S) : G)) * a⁻¹ ∈ S then
        phi ⟨a * (((x * k * x⁻¹ : S) : G)) * a⁻¹, hx⟩
      else 0) =
        ∑ _x : S, phi k := by
          refine Finset.sum_congr rfl ?_
          intro x _hx
          have hmem : a * (((x * k * x⁻¹ : S) : G)) * a⁻¹ ∈ S :=
            S.mul_mem
              (S.mul_mem ha
                (S.mul_mem (S.mul_mem x.2 k.2) (S.inv_mem x.2)))
              (S.inv_mem ha)
          rw [dif_pos hmem]
          let ax : S := ⟨a * (x : G), S.mul_mem ha x.2⟩
          have hclass := hphi ax k
          have harg :
              (ax * k * ax⁻¹ : S) =
                ⟨a * (((x * k * x⁻¹ : S) : G)) * a⁻¹, hmem⟩ := by
            ext
            simp [ax, mul_assoc]
          simpa [harg]
            using hclass
    _ = (Nat.card S : ℂ) * phi k := by
          simp [Finset.card_univ]

public theorem mackeySummandAmbientFormula_self_eq_of_mem
    {G : Type*} [Group G] (S : Subgroup G) [Finite S]
    {a : G} (ha : a ∈ S) (phi : ClassFunction S) (hphi : IsClassFunction phi)
    (k : S) :
    mackeySummandAmbientFormula S S a phi k = phi k := by
  classical
  rw [mackeySummandAmbientFormula_apply]
  rw [mackeySummandAmbientInner_self_eq_card_mul_of_mem S ha phi hphi k]
  rw [mackeyIntersection_self_eq_top_of_mem S ha]
  rw [Subgroup.card_top]
  have hcard : (Nat.card S : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := S)).ne'
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

public theorem mackeySummand_self_eq_of_mem
    {G : Type*} [Group G] (S : Subgroup G) [Finite S]
    {a : G} (ha : a ∈ S) (phi : ClassFunction S) (hphi : IsClassFunction phi)
    (k : S) :
    mackeySummand S S a phi k = phi k := by
  rw [mackeySummand_apply]
  rw [mackeySummandFormula_eq_ambient]
  exact mackeySummandAmbientFormula_self_eq_of_mem S ha phi hphi k

public theorem DoubleCoset.out_mem_of_eq_mk_one
    {G : Type*} [Group G] (S : Subgroup G)
    {q : DoubleCoset.Quotient (S : Set G) S}
    (hq : q = DoubleCoset.mk S S 1) :
    q.out ∈ S := by
  classical
  have hmk : DoubleCoset.mk S S q.out = DoubleCoset.mk S S 1 := by
    rw [DoubleCoset.out_eq' (H := S) (K := S) q, hq]
  rcases (DoubleCoset.eq (H := S) (K := S) (a := 1) (b := q.out)).mp hmk.symm with
    ⟨s, hs, t, ht, hqout⟩
  rw [hqout]
  simpa using S.mul_mem hs ht

public theorem DoubleCoset.eq_mk_one_of_out_mem
    {G : Type*} [Group G] (S : Subgroup G)
    {q : DoubleCoset.Quotient (S : Set G) S}
    (hq : q.out ∈ S) :
    q = DoubleCoset.mk S S 1 := by
  rw [← DoubleCoset.out_eq' (H := S) (K := S) q]
  apply (DoubleCoset.eq (H := S) (K := S) (a := q.out) (b := 1)).mpr
  refine ⟨q.out⁻¹, S.inv_mem hq, 1, S.one_mem, ?_⟩
  simp

public theorem DoubleCoset.out_not_mem_of_ne_mk_one
    {G : Type*} [Group G] (S : Subgroup G)
    {q : DoubleCoset.Quotient (S : Set G) S}
    (hq : q ≠ DoubleCoset.mk S S 1) :
    q.out ∉ S := by
  intro hmem
  exact hq (DoubleCoset.eq_mk_one_of_out_mem S hmem)

public theorem mackeySummand_principal_eq
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S]
    (phi : ClassFunction S) (hphi : IsClassFunction phi)
    {q : DoubleCoset.Quotient (S : Set G) S}
    (hq : q = DoubleCoset.mk S S 1) (k : S) :
    mackeySummand S S q.out phi k = phi k := by
  exact mackeySummand_self_eq_of_mem S
    (DoubleCoset.out_mem_of_eq_mk_one S hq) phi hphi k

public theorem subgroupOf_le_mackeyIntersection_self_of_normal
    {G : Type*} [Group G] (H T : Subgroup G) [H.Normal]
    (hHT : H ≤ T) (a : G) :
    H.subgroupOf T ≤ mackeyIntersection T T a := by
  intro h hh
  change a * (h : G) * a⁻¹ ∈ T
  exact hHT ((inferInstance : H.Normal).conj_mem (h : G) hh a)

public theorem mackeyConjugateRestriction_restrict_subgroupOf_normal
    {G : Type*} [Group G] (H T : Subgroup G) [H.Normal]
    (hHT : H ≤ T) (a : G)
    (psi : ClassFunction T) (theta : ClassFunction H) (c : ℂ)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta) :
    subgroupRestriction
        ((H.subgroupOf T).subgroupOf
          (mackeyIntersection T T a))
        (mackeyConjugateRestriction T T a psi) =
      c • subgroupOfClassFunction
        (T := mackeyIntersection T T a)
        (subgroupOfClassFunction (T := T) (conjugateOnNormal H theta a)) := by
  ext h
  let I : Subgroup T := mackeyIntersection T T a
  let Hsub : Subgroup T := H.subgroupOf T
  let hm : I := h
  let ht : T := hm
  have hh : (ht : G) ∈ H := by
    exact h.2
  have hconjH : a * (ht : G) * a⁻¹ ∈ H :=
    (inferInstance : H.Normal).conj_mem (ht : G) hh a
  have hres_apply := congrFun hres
    (⟨⟨a * (ht : G) * a⁻¹, hHT hconjH⟩, hconjH⟩ : Hsub)
  simpa [subgroupRestriction, mackeyConjugateRestriction,
    subgroupOfClassFunction, conjugateOnNormal, I, Hsub, hm, ht, hh, hconjH]
    using hres_apply

@[expose] public def mackeyIntersectionConjugateHom
    {G : Type*} [Group G] (T : Subgroup G) (a : G) :
    mackeyIntersection T T a →* T where
  toFun k := ⟨a * ((k : mackeyIntersection T T a) : T) * a⁻¹, k.2⟩
  map_one' := by
    ext
    simp
  map_mul' x y := by
    ext
    simp [mul_assoc]

public theorem mackeyConjugateRestriction_eq_representation_character_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) [Finite T] (a : G)
    (phi : ClassFunction T) (hphi : IsCharacter phi) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
      ∃ _ : FiniteDimensional ℂ V,
        ∃ rho : Representation ℂ (mackeyIntersection T T a) V,
          mackeyConjugateRestriction T T a phi = rho.character := by
  rcases hphi with ⟨V, _hadd, _hmod, _hfd, rho, hphi_eq⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance,
    rho.comp (mackeyIntersectionConjugateHom T a), ?_⟩
  rw [hphi_eq]
  rfl

public theorem subgroupRestriction_restrict_subgroupOf_mackeyIntersection
    {G : Type*} [Group G] (H T : Subgroup G) [H.Normal]
    (a : G)
    (psi : ClassFunction T) (theta : ClassFunction H) (c : ℂ)
    (hres :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta) :
    subgroupRestriction
        ((H.subgroupOf T).subgroupOf (mackeyIntersection T T a))
        (subgroupRestriction (mackeyIntersection T T a) psi) =
      c • subgroupOfClassFunction
        (T := mackeyIntersection T T a)
        (subgroupOfClassFunction (T := T) theta) := by
  ext h
  have hres_apply := congrFun hres
    (⟨(h : mackeyIntersection T T a), h.2⟩ : H.subgroupOf T)
  simpa [subgroupRestriction, subgroupOfClassFunction] using hres_apply

public theorem scalarProduct_subgroupOfClassFunction_smul
    {G : Type*} [Group G] {H T : Subgroup G} [Finite H] [Finite T]
    (hHT : H ≤ T) (theta phi : ClassFunction H) (c d : ℂ) :
    scalarProduct (H.subgroupOf T)
        (c • subgroupOfClassFunction (T := T) theta)
        (d • subgroupOfClassFunction (T := T) phi) =
      c * star d * scalarProduct H theta phi := by
  rw [scalarProduct_smul_left]
  rw [scalarProduct_smul_right]
  rw [scalarProduct_subgroupOfClassFunction hHT theta phi]
  ring

public theorem scalarProduct_conjugateOnNormal_eq_zero_of_ne
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (rho : Representation ℂ H V)
    (htheta : theta = rho.character)
    (hirr : Representation.IsIrreducible rho)
    (a : G) (hne : conjugateOnNormal H theta a ≠ theta) :
    scalarProduct H theta (conjugateOnNormal H theta a) = 0 := by
  have hconjRepTheta :
      conjugateOnNormal H theta a = (conjugateRepresentation H rho a).character := by
    rw [htheta]
    exact (representationCharacter_conjugateRepresentation H rho a).symm
  have hne' : rho.character ≠ (conjugateRepresentation H rho a).character := by
    intro hchars
    apply hne
    calc
      conjugateOnNormal H theta a = (conjugateRepresentation H rho a).character :=
        hconjRepTheta
      _ = rho.character := hchars.symm
      _ = theta := htheta.symm
  rw [hconjRepTheta]
  rw [htheta]
  letI : Representation.IsIrreducible rho := hirr
  letI : Representation.IsIrreducible (conjugateRepresentation H rho a) :=
    irreducible_conjugateRepresentation H rho a
  exact scalarProduct_representation_char_eq_zero_of_ne rho
    (conjugateRepresentation H rho a) hne'

public theorem scalarProduct_mackeySummand_right
    {G : Type*} [Group G] [Finite G] (T : Subgroup G) [Finite T]
    (a : G) (psi phi : ClassFunction T) (hpsi : IsClassFunction psi) :
    scalarProduct T psi (mackeySummand T T a phi) =
      scalarProduct (mackeyIntersection T T a)
        (subgroupRestriction (mackeyIntersection T T a) psi)
        (mackeyConjugateRestriction T T a phi) := by
  unfold mackeySummand
  exact inducedClassFunction_frobenius_right
    (mackeyIntersection T T a) (mackeyConjugateRestriction T T a phi) psi hpsi

public theorem scalarProduct_representation_char_eq_zero_of_subgroupRestriction_eq_zero
    {K V W : Type*} [Group K] [Finite K]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (L : Subgroup K) [Finite L]
    (rho : Representation ℂ K V) (sigma : Representation ℂ K W)
    (hzero : scalarProduct L
        (subgroupRestriction L sigma.character)
        (subgroupRestriction L rho.character) = 0) :
    scalarProduct K sigma.character rho.character = 0 := by
  classical
  let rhoL : Representation ℂ L V := rho.comp L.subtype
  let sigmaL : Representation ℂ L W := sigma.comp L.subtype
  have hresCharSigma :
      subgroupRestriction L sigma.character = sigmaL.character := by
    rfl
  have hresCharRho :
      subgroupRestriction L rho.character = rhoL.character := by
    rfl
  have hfinH_C :
      (Module.finrank ℂ
        (Representation.IntertwiningMap rhoL sigmaL) : ℂ) = 0 := by
    simpa [hresCharSigma, hresCharRho, rhoL, sigmaL] using
      (scalarProduct_representation_char_eq_finrank rhoL sigmaL).symm.trans hzero
  have hfinH_nat :
      Module.finrank ℂ (Representation.IntertwiningMap rhoL sigmaL) = 0 := by
    exact_mod_cast hfinH_C
  have hsubH : Subsingleton (Representation.IntertwiningMap rhoL sigmaL) :=
    Module.finrank_zero_iff.mp hfinH_nat
  have hsubK : Subsingleton (Representation.IntertwiningMap rho sigma) := by
    refine ⟨?_⟩
    intro f g
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    let fL : Representation.IntertwiningMap rhoL sigmaL :=
      { toLinearMap := f.toLinearMap
        isIntertwining' := by
          intro l
          exact f.isIntertwining' l }
    let gL : Representation.IntertwiningMap rhoL sigmaL :=
      { toLinearMap := g.toLinearMap
        isIntertwining' := by
          intro l
          exact g.isIntertwining' l }
    have hfg : fL = gL := Subsingleton.elim fL gL
    exact congrArg
      (fun u : Representation.IntertwiningMap rhoL sigmaL => u.toLinearMap v) hfg
  have hfinK_nat : Module.finrank ℂ (Representation.IntertwiningMap rho sigma) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hfinK_C :
      (Module.finrank ℂ (Representation.IntertwiningMap rho sigma) : ℂ) = 0 := by
    exact_mod_cast hfinK_nat
  rw [scalarProduct_representation_char_eq_finrank rho sigma]
  exact hfinK_C

public theorem scalarProduct_mackeyIntersection_representation_char_eq_zero_of_subgroupOf_restriction_zero
    {G V W : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H T : Subgroup G) [Finite H] [Finite T] [H.Normal]
    (a : G)
    (rho : Representation ℂ (mackeyIntersection T T a) V)
    (sigma : Representation ℂ (mackeyIntersection T T a) W)
    (hzero :
      scalarProduct ((H.subgroupOf T).subgroupOf (mackeyIntersection T T a))
        (subgroupRestriction ((H.subgroupOf T).subgroupOf
          (mackeyIntersection T T a)) sigma.character)
        (subgroupRestriction ((H.subgroupOf T).subgroupOf
          (mackeyIntersection T T a)) rho.character) = 0) :
    scalarProduct (mackeyIntersection T T a) sigma.character rho.character = 0 := by
  exact scalarProduct_representation_char_eq_zero_of_subgroupRestriction_eq_zero
    ((H.subgroupOf T).subgroupOf (mackeyIntersection T T a)) rho sigma hzero

public theorem subgroupRestriction_eq_representation_character_of_isCharacter
    {G : Type u} [Group G] [Finite G]
    (S : Subgroup G) [Finite S]
    (psi : ClassFunction G) (hpsi : IsCharacter psi) :
    ∃ V : Type u, ∃ _ : AddCommGroup V, ∃ _ : Module ℂ V,
      ∃ _ : FiniteDimensional ℂ V, ∃ rho : Representation ℂ S V,
        subgroupRestriction S psi = rho.character := by
  rcases hpsi with ⟨V, _hadd, _hmod, _hfd, rho, hpsi_eq⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, rho.comp S.subtype, ?_⟩
  rw [hpsi_eq]
  rfl

public theorem scalarProduct_mackeySummand_eq_zero_of_restrictions_and_conjugate_ne
    {G Vθ V W : Type*} [Group G] [Finite G]
    [AddCommGroup Vθ] [Module ℂ Vθ] [FiniteDimensional ℂ Vθ]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (H T : Subgroup G) [Finite H] [Finite T] [H.Normal]
    (hHT : H ≤ T) (a : G)
    (psi phi : ClassFunction T) (theta : ClassFunction H)
    (thetaRep : Representation ℂ H Vθ)
    (rho : Representation ℂ (mackeyIntersection T T a) V)
    (sigma : Representation ℂ (mackeyIntersection T T a) W)
    (c d : ℂ)
    (hpsi_class : IsClassFunction psi)
    (htheta : theta = thetaRep.character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hresPsi :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta)
    (hresPhi :
      subgroupRestriction (H.subgroupOf T) phi =
        d • subgroupOfClassFunction theta)
    (hpsiI : subgroupRestriction (mackeyIntersection T T a) psi = sigma.character)
    (hphiI : mackeyConjugateRestriction T T a phi = rho.character)
    (hne : conjugateOnNormal H theta a ≠ theta) :
    scalarProduct T psi (mackeySummand T T a phi) = 0 := by
  rw [scalarProduct_mackeySummand_right T a psi phi hpsi_class]
  rw [hpsiI, hphiI]
  apply scalarProduct_mackeyIntersection_representation_char_eq_zero_of_subgroupOf_restriction_zero
    H T a rho sigma
  rw [← hpsiI, ← hphiI]
  rw [subgroupRestriction_restrict_subgroupOf_mackeyIntersection H T a
    psi theta c hresPsi]
  rw [mackeyConjugateRestriction_restrict_subgroupOf_normal H T hHT a
    phi theta d hresPhi]
  rw [scalarProduct_subgroupOfClassFunction_smul
    (G := T) (H := H.subgroupOf T) (T := mackeyIntersection T T a)
    (subgroupOf_le_mackeyIntersection_self_of_normal H T hHT a)
    (subgroupOfClassFunction (T := T) theta)
    (subgroupOfClassFunction (T := T) (conjugateOnNormal H theta a)) c d]
  rw [scalarProduct_subgroupOfClassFunction hHT theta (conjugateOnNormal H theta a)]
  rw [scalarProduct_conjugateOnNormal_eq_zero_of_ne H theta thetaRep htheta
    htheta_irreducible a hne]
  ring

public theorem scalarProduct_mackeySummand_eq_zero_of_characters_restrictions_and_conjugate_ne
    {G Vθ : Type u} [Group G] [Finite G]
    [AddCommGroup Vθ] [Module ℂ Vθ] [FiniteDimensional ℂ Vθ]
    (H T : Subgroup G) [Finite H] [Finite T] [H.Normal]
    (hHT : H ≤ T) (a : G)
    (psi phi : ClassFunction T) (theta : ClassFunction H)
    (thetaRep : Representation ℂ H Vθ)
    (c d : ℂ)
    (hpsi_char : IsCharacter psi)
    (hphi_char : IsCharacter phi)
    (hpsi_class : IsClassFunction psi)
    (htheta : theta = thetaRep.character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hresPsi :
      subgroupRestriction (H.subgroupOf T) psi =
        c • subgroupOfClassFunction theta)
    (hresPhi :
      subgroupRestriction (H.subgroupOf T) phi =
        d • subgroupOfClassFunction theta)
    (hne : conjugateOnNormal H theta a ≠ theta) :
    scalarProduct T psi (mackeySummand T T a phi) = 0 := by
  rcases subgroupRestriction_eq_representation_character_of_isCharacter
      (mackeyIntersection T T a) psi hpsi_char with
    ⟨Vs, _hadds, _hmods, _hfds, sigma, hpsiI⟩
  rcases mackeyConjugateRestriction_eq_representation_character_of_isCharacter
      T a phi hphi_char with
    ⟨Vr, _haddr, _hmodr, _hfdr, rho, hphiI⟩
  exact scalarProduct_mackeySummand_eq_zero_of_restrictions_and_conjugate_ne
    H T hHT a psi phi theta thetaRep rho sigma c d hpsi_class htheta
    htheta_irreducible hresPsi hresPhi hpsiI hphiI hne

public theorem mackey_inertia_off_diagonal_zero_of_clifford_restrictions
    {G Vθ : Type u} {ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup Vθ] [Module ℂ Vθ] [FiniteDimensional ℂ Vθ]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (thetaRep : Representation ℂ H Vθ)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (hpsi_char : ∀ i : ι, IsCharacter (psi i))
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (htheta : theta = thetaRep.character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hres : ∀ i : ι,
      subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta) :
    ∀ i j : ι, ∀ q : DoubleCoset.Quotient ((inertiaSubgroup H theta) : Set G)
        (inertiaSubgroup H theta),
      q ≠ DoubleCoset.mk (inertiaSubgroup H theta) (inertiaSubgroup H theta) 1 →
        scalarProduct (inertiaSubgroup H theta) (psi i)
          (mackeySummand (inertiaSubgroup H theta) (inertiaSubgroup H theta)
            q.out (psi j)) = 0 := by
  intro i j q hq
  let T : Subgroup G := inertiaSubgroup H theta
  have hHT : H ≤ T := by
    intro h hh
    change conjugateOnNormal H theta h = theta
    rw [htheta]
    funext x
    change thetaRep.character ⟨h * (x : G) * h⁻¹, _⟩ = thetaRep.character x
    exact Representation.char_conj (ρ := thetaRep) x ⟨h, hh⟩
  have hne : conjugateOnNormal H theta q.out ≠ theta := by
    exact DoubleCoset.out_not_mem_of_ne_mk_one T hq
  exact scalarProduct_mackeySummand_eq_zero_of_characters_restrictions_and_conjugate_ne
    H T hHT q.out (psi i) (psi j) theta thetaRep (e i : ℂ) (e j : ℂ)
    (hpsi_char i) (hpsi_char j) (hpsi_class i) htheta htheta_irreducible
    (hres i) (hres j) hne

public instance finite_doubleCoset_quotient_of_finite
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) :
    Finite (DoubleCoset.Quotient (S : Set G) K) := by
  classical
  exact Quotient.finite _

@[expose] public noncomputable def mackeyRestrictionSum
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite K]
    (phi : ClassFunction S) : ClassFunction K :=
  familySum (fun q : DoubleCoset.Quotient (S : Set G) K =>
    mackeySummand S K q.out phi)


public theorem mackeyRestrictionSum_apply_formula
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite K]
    (phi : ClassFunction S) (k : K) :
    mackeyRestrictionSum S K phi k =
      ∑ q : DoubleCoset.Quotient (S : Set G) K,
        mackeySummandFormula S K q.out phi k := by
  simp [mackeyRestrictionSum, familySum, mackeySummand_apply]

public theorem mackeyRestrictionSum_apply_ambientFormula
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite K]
    (phi : ClassFunction S) (k : K) :
    mackeyRestrictionSum S K phi k =
      ∑ q : DoubleCoset.Quotient (S : Set G) K,
        mackeySummandAmbientFormula S K q.out phi k := by
  rw [mackeyRestrictionSum_apply_formula]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [mackeySummandFormula_eq_ambient]

@[expose] public noncomputable def inducedCFDoubleCosetFiberSum
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S]
    (phi : ClassFunction S) (k : K)
    (q : DoubleCoset.Quotient (S : Set G) K) : ℂ :=
  by
    classical
    exact ∑ x : {x : G // DoubleCoset.mk S K x = q},
      if hx : (x : G) * (k : G) * (x : G)⁻¹ ∈ S then
        phi ⟨(x : G) * (k : G) * (x : G)⁻¹, hx⟩
      else 0

@[expose] public noncomputable def inducedCFDoubleCosetFiberAt
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S]
    (phi : ClassFunction S) (k : K) (a : G) : ℂ :=
  by
    classical
    exact ∑ x : {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a},
      if hx : (x : G) * (k : G) * (x : G)⁻¹ ∈ S then
        phi ⟨(x : G) * (k : G) * (x : G)⁻¹, hx⟩
      else 0

public theorem inducedCFDoubleCosetFiberSum_eq_at_out
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S]
    (phi : ClassFunction S) (k : K)
    (q : DoubleCoset.Quotient (S : Set G) K) :
    inducedCFDoubleCosetFiberSum S K phi k q =
      inducedCFDoubleCosetFiberAt S K phi k q.out := by
  classical
  unfold inducedCFDoubleCosetFiberSum inducedCFDoubleCosetFiberAt
  let e :
      {x : G // DoubleCoset.mk S K x = q} ≃
        {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K q.out} :=
    Equiv.subtypeEquivRight fun x => by
      constructor
      · intro hx
        simpa [DoubleCoset.out_eq' (H := S) (K := K) q] using hx
      · intro hx
        simpa [DoubleCoset.out_eq' (H := S) (K := K) q] using hx
  exact Fintype.sum_equiv e _ _ (fun x => rfl)

public theorem subgroupRestriction_inducedCF_eq_doubleCoset_fiber_sum
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S]
    (phi : ClassFunction S) (k : K) :
    subgroupRestriction K (inducedCF S phi) k =
      (Nat.card S : ℂ)⁻¹ *
        ∑ q : DoubleCoset.Quotient (S : Set G) K,
          inducedCFDoubleCosetFiberSum S K phi k q := by
  classical
  unfold subgroupRestriction inducedCF inducedClassFunction inducedCFDoubleCosetFiberSum
  rw [← Fintype.sum_fiberwise (fun x : G => DoubleCoset.mk S K x)
    (fun x : G =>
      if hx : x * (k : G) * x⁻¹ ∈ S then
        phi ⟨x * (k : G) * x⁻¹, hx⟩
      else 0)]

@[expose] public noncomputable def mackeyDoubleParamSum
    {G : Type*} [Group G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (phi : ClassFunction S) (k : K) : ℂ :=
  by
    classical
    exact ∑ p : S × K,
      if hp : ((p.1 : G) * a * (p.2 : G)) * (k : G) *
          (((p.1 : G) * a * (p.2 : G))⁻¹) ∈ S then
        phi ⟨((p.1 : G) * a * (p.2 : G)) * (k : G) *
          (((p.1 : G) * a * (p.2 : G))⁻¹), hp⟩
      else 0

public theorem mackeyDoubleParamSum_eq_card_mul_inner
    {G : Type*} [Group G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (phi : ClassFunction S) (hphi : IsClassFunction phi) (k : K) :
    mackeyDoubleParamSum S K a phi k =
      (Nat.card S : ℂ) * mackeySummandAmbientInner S K a phi k := by
  classical
  unfold mackeyDoubleParamSum mackeySummandAmbientInner
  conv_lhs =>
    rw [← Finset.univ_product_univ]
    rw [Finset.sum_product]
  calc
    (∑ x : S, ∑ y : K,
      if hp : ((x : G) * a * (y : G)) * (k : G) *
          (((x : G) * a * (y : G))⁻¹) ∈ S then
        phi ⟨((x : G) * a * (y : G)) * (k : G) *
          (((x : G) * a * (y : G))⁻¹), hp⟩
      else 0) =
      ∑ x : S, ∑ y : K,
        if hy : a * (((y * k * y⁻¹ : K) : G)) * a⁻¹ ∈ S then
          phi ⟨a * (((y * k * y⁻¹ : K) : G)) * a⁻¹, hy⟩
        else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x _hx
        refine Finset.sum_congr rfl ?_
        intro y _hy
        let b : G := a * (((y * k * y⁻¹ : K) : G)) * a⁻¹
        have hconj_eq :
            ((x : G) * a * (y : G)) * (k : G) *
              (((x : G) * a * (y : G))⁻¹) =
                (x : G) * b * (x : G)⁻¹ := by
          dsimp [b]
          group
        have hmem_iff :
            ((x : G) * a * (y : G)) * (k : G) *
              (((x : G) * a * (y : G))⁻¹) ∈ S ↔ b ∈ S := by
          rw [hconj_eq]
          constructor
          · intro h
            have hback :
                (x : G)⁻¹ * ((x : G) * b * (x : G)⁻¹) * (x : G) ∈ S :=
              S.mul_mem (S.mul_mem (S.inv_mem x.2) h) x.2
            simpa [mul_assoc, b] using hback
          · intro hb
            exact S.mul_mem (S.mul_mem x.2 hb) (S.inv_mem x.2)
        by_cases hb : b ∈ S
        · have hp :
              ((x : G) * a * (y : G)) * (k : G) *
                (((x : G) * a * (y : G))⁻¹) ∈ S :=
            hmem_iff.mpr hb
          rw [dif_pos hp, dif_pos hb]
          let xb : S := ⟨x, x.2⟩
          let bs : S := ⟨b, hb⟩
          have hclass := hphi xb bs
          have hsub :
              (xb * bs * xb⁻¹ : S) =
                ⟨((x : G) * a * (y : G)) * (k : G) *
                  (((x : G) * a * (y : G))⁻¹), hp⟩ := by
            ext
            simpa [xb, bs, mul_assoc] using hconj_eq.symm
          rw [← hsub]
          exact hclass
        · have hp :
              ¬ ((x : G) * a * (y : G)) * (k : G) *
                (((x : G) * a * (y : G))⁻¹) ∈ S := by
            intro h
            exact hb (hmem_iff.mp h)
          rw [dif_neg hp, dif_neg hb]
    _ = (Nat.card S : ℂ) * mackeySummandAmbientInner S K a phi k := by
        unfold mackeySummandAmbientInner
        simp [Finset.card_univ]

@[expose] public noncomputable def mackeyPairFiberEquiv
    {G : Type*} [Group G] (S K : Subgroup G) (a x : G)
    (hx : DoubleCoset.mk S K x = DoubleCoset.mk S K a) :
    {p : S × K // (p.1 : G) * a * (p.2 : G) = x} ≃
      mackeyIntersection S K a := by
  classical
  let hrep : ∃ s ∈ S, ∃ y ∈ K, x = s * a * y :=
    (DoubleCoset.eq (H := S) (K := K) (a := a) (b := x)).mp hx.symm
  let s0 : G := Classical.choose hrep
  let hs0 : s0 ∈ S := (Classical.choose_spec hrep).1
  let y0 : G := Classical.choose (Classical.choose_spec hrep).2
  let hy0 : y0 ∈ K := (Classical.choose_spec (Classical.choose_spec hrep).2).1
  let hxrep : x = s0 * a * y0 :=
    (Classical.choose_spec (Classical.choose_spec hrep).2).2
  let s0S : S := ⟨s0, hs0⟩
  let y0K : K := ⟨y0, hy0⟩
  refine
    { toFun := fun p =>
        ⟨y0K * p.1.2⁻¹, ?_⟩
      invFun := fun t =>
        ⟨(s0S * ⟨a * ((t : K) : G) * a⁻¹, t.2⟩,
            (t : K)⁻¹ * y0K), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · change a * (y0 * (p.1.2 : G)⁻¹) * a⁻¹ ∈ S
    have hmain : (p.1.1 : G) * a * (p.1.2 : G) = s0 * a * y0 := by
      exact p.2.trans hxrep
    have hcalc :
        a * (y0 * (p.1.2 : G)⁻¹) * a⁻¹ = s0⁻¹ * (p.1.1 : G) := by
      have h := congrArg
        (fun z => s0⁻¹ * z * (p.1.2 : G)⁻¹ * a⁻¹) hmain
      simpa [mul_assoc] using h.symm
    have hS : s0⁻¹ * (p.1.1 : G) ∈ S :=
      S.mul_mem (S.inv_mem hs0) p.1.1.2
    simpa [hcalc] using hS
  · change ((s0 : G) * (a * ((t : K) : G) * a⁻¹)) * a *
      (((t : K) : G)⁻¹ * y0) = x
    rw [hxrep]
    group
  · intro p
    apply Subtype.ext
    apply Prod.ext
    · have hmain : (p.1.1 : G) * a * (p.1.2 : G) = s0 * a * y0 := by
        exact p.2.trans hxrep
      have hcalc :
          a * (y0 * (p.1.2 : G)⁻¹) * a⁻¹ = s0⁻¹ * (p.1.1 : G) := by
        have h := congrArg
          (fun z => s0⁻¹ * z * (p.1.2 : G)⁻¹ * a⁻¹) hmain
        simpa [mul_assoc] using h.symm
      ext
      change s0 * (a * (y0 * (p.1.2 : G)⁻¹) * a⁻¹) = (p.1.1 : G)
      rw [hcalc]
      group
    · ext
      change (y0 * (p.1.2 : G)⁻¹)⁻¹ * y0 = (p.1.2 : G)
      group
  · intro t
    apply Subtype.ext
    ext
    change y0 * (((t : K) : G)⁻¹ * y0)⁻¹ = ((t : K) : G)
    group

public theorem mackey_pair_fiber_card
    {G : Type*} [Group G] (S K : Subgroup G) [Finite S] [Finite K]
    (a x : G) (hx : DoubleCoset.mk S K x = DoubleCoset.mk S K a) :
    Nat.card {p : S × K // (p.1 : G) * a * (p.2 : G) = x} =
      Nat.card (mackeyIntersection S K a) := by
  classical
  exact Nat.card_congr (mackeyPairFiberEquiv S K a x hx)

@[expose] public def mackeyDoubleCosetParam
    {G : Type*} [Group G] (S K : Subgroup G) (a : G) :
    S × K → {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a} :=
  fun p => ⟨(p.1 : G) * a * (p.2 : G), by
    exact ((DoubleCoset.eq (H := S) (K := K) (a := a) (b := (p.1 : G) * a * (p.2 : G))).mpr
      ⟨(p.1 : G), p.1.2, (p.2 : G), p.2.2, rfl⟩).symm⟩

public theorem mackeyDoubleCosetParam_fiber_card
    {G : Type*} [Group G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (x : {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}) :
    Nat.card {p : S × K // mackeyDoubleCosetParam S K a p = x} =
      Nat.card (mackeyIntersection S K a) := by
  classical
  let e1 : {p : S × K // mackeyDoubleCosetParam S K a p = x} ≃
      {p : S × K // (p.1 : G) * a * (p.2 : G) = (x : G)} :=
    { toFun := fun p => ⟨p.1, congrArg Subtype.val p.2⟩
      invFun := fun p => ⟨p.1, by
        apply Subtype.ext
        exact p.2⟩
      left_inv := by intro p; apply Subtype.ext; rfl
      right_inv := by intro p; apply Subtype.ext; rfl }
  calc
    Nat.card {p : S × K // mackeyDoubleCosetParam S K a p = x} =
        Nat.card {p : S × K // (p.1 : G) * a * (p.2 : G) = (x : G)} := by
          exact Nat.card_congr e1
    _ = Nat.card (mackeyIntersection S K a) := by
          exact mackey_pair_fiber_card S K a (x : G) x.2

public theorem finite_sum_fiberwise_univ
    {ι κ M : Type*} [Finite ι] [Finite κ] [DecidableEq κ] [AddCommMonoid M]
    (g : ι → κ) (f : ι → M) :
    (∑ i ∈ (@Finset.univ ι (Fintype.ofFinite ι)), f i) =
      ∑ j ∈ (@Finset.univ κ (Fintype.ofFinite κ)),
        ∑ i ∈ (@Finset.univ ι (Fintype.ofFinite ι)) with g i = j, f i := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  letI : Fintype κ := Fintype.ofFinite κ
  simpa using
    (Finset.sum_fiberwise (s := (Finset.univ : Finset ι)) (g := g) (f := f)).symm


public theorem mackeyDoubleCosetParam_finite_sum_eq_card_mul_fiber_sum
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (f : {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a} → ℂ) :
    (∑ p ∈ (@Finset.univ (S × K) (Fintype.ofFinite (S × K))),
        f (mackeyDoubleCosetParam S K a p)) =
      (Nat.card (mackeyIntersection S K a) : ℂ) *
        ∑ x ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})), f x := by
  classical
  calc
    (∑ p ∈ (@Finset.univ (S × K) (Fintype.ofFinite (S × K))),
        f (mackeyDoubleCosetParam S K a p)) =
      ∑ j ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})),
        ∑ i ∈ (@Finset.univ (S × K) (Fintype.ofFinite (S × K))) with
            mackeyDoubleCosetParam S K a i = j,
          f (mackeyDoubleCosetParam S K a i) := by
        exact finite_sum_fiberwise_univ
          (g := fun i : S × K => mackeyDoubleCosetParam S K a i)
          (f := fun i : S × K => f (mackeyDoubleCosetParam S K a i))
    _ = ∑ j ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})),
        ∑ i ∈ (@Finset.univ (S × K) (Fintype.ofFinite (S × K))) with
            mackeyDoubleCosetParam S K a i = j,
          f j := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hij : mackeyDoubleCosetParam S K a i = j := by
          simpa using (Finset.mem_filter.mp hi).2
        rw [hij]
    _ = ∑ j ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})),
        (Nat.card (mackeyIntersection S K a) : ℂ) * f j := by
        refine Finset.sum_congr rfl ?_
        intro j _hj
        have hcard : (((@Finset.univ (S × K) (Fintype.ofFinite (S × K))).filter
              (fun i : S × K => mackeyDoubleCosetParam S K a i = j)).card : ℂ) =
            (Nat.card (mackeyIntersection S K a) : ℂ) := by
          have hnat : ((@Finset.univ (S × K) (Fintype.ofFinite (S × K))).filter
                (fun i : S × K => mackeyDoubleCosetParam S K a i = j)).card =
              Nat.card (mackeyIntersection S K a) := by
            rw [← mackeyDoubleCosetParam_fiber_card S K a j]
            have hft :
                Fintype.card {i : S × K // mackeyDoubleCosetParam S K a i = j} =
                  ((@Finset.univ (S × K) (Fintype.ofFinite (S × K))).filter
                    (fun i : S × K => mackeyDoubleCosetParam S K a i = j)).card := by
              exact Fintype.card_of_finset'
                (s := (@Finset.univ (S × K) (Fintype.ofFinite (S × K))).filter
                  (fun i : S × K => mackeyDoubleCosetParam S K a i = j))
                (p := {i : S × K | mackeyDoubleCosetParam S K a i = j})
                (by intro i; simp)
            rw [← hft]
            exact (Nat.card_eq_fintype_card :
              Nat.card {i : S × K // mackeyDoubleCosetParam S K a i = j} =
                Fintype.card {i : S × K // mackeyDoubleCosetParam S K a i = j}).symm
          exact_mod_cast hnat
        rw [Finset.sum_const]
        simp [hcard]
    _ = (Nat.card (mackeyIntersection S K a) : ℂ) *
        ∑ x ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})), f x := by
        rw [Finset.mul_sum]

public theorem mackeyDoubleParamSum_eq_card_intersection_mul_fiberAt
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (phi : ClassFunction S) (k : K) :
    mackeyDoubleParamSum S K a phi k =
      (Nat.card (mackeyIntersection S K a) : ℂ) *
        inducedCFDoubleCosetFiberAt S K phi k a := by
  classical
  let f : {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a} → ℂ :=
    fun x =>
      if hx : (x : G) * (k : G) * (x : G)⁻¹ ∈ S then
        phi ⟨(x : G) * (k : G) * (x : G)⁻¹, hx⟩
      else 0
  calc
    mackeyDoubleParamSum S K a phi k =
        ∑ p ∈ (@Finset.univ (S × K) (Fintype.ofFinite (S × K))),
        f (mackeyDoubleCosetParam S K a p) := by
          unfold mackeyDoubleParamSum mackeyDoubleCosetParam
          dsimp [f]
          have hprod :
              (@instFintypeProd S K (Fintype.ofFinite S) (Fintype.ofFinite K)) =
                Fintype.ofFinite (S × K) := Subsingleton.elim _ _
          rw [hprod]
    _ = (Nat.card (mackeyIntersection S K a) : ℂ) *
        ∑ x ∈ (@Finset.univ {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a}
          (Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a})), f x := by
          exact mackeyDoubleCosetParam_finite_sum_eq_card_mul_fiber_sum S K a f
    _ = (Nat.card (mackeyIntersection S K a) : ℂ) *
        inducedCFDoubleCosetFiberAt S K phi k a := by
          unfold inducedCFDoubleCosetFiberAt
          dsimp [f]
          have hinst :
              (Subtype.fintype fun x : G => DoubleCoset.mk S K x = DoubleCoset.mk S K a) =
                Fintype.ofFinite {x : G // DoubleCoset.mk S K x = DoubleCoset.mk S K a} :=
            Subsingleton.elim _ _
          rw [hinst]

public theorem inducedCFDoubleCosetFiberAt_normalized_eq_mackeySummandAmbientFormula
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S] [Finite K]
    (a : G) (phi : ClassFunction S) (hphi : IsClassFunction phi) (k : K) :
    (Nat.card S : ℂ)⁻¹ * inducedCFDoubleCosetFiberAt S K phi k a =
      mackeySummandAmbientFormula S K a phi k := by
  classical
  let cS : ℂ := Nat.card S
  let cI : ℂ := Nat.card (mackeyIntersection S K a)
  let fiber : ℂ := inducedCFDoubleCosetFiberAt S K phi k a
  let inner : ℂ := mackeySummandAmbientInner S K a phi k
  have hparam :
      cI * fiber = mackeyDoubleParamSum S K a phi k := by
    dsimp [cI, fiber]
    rw [mackeyDoubleParamSum_eq_card_intersection_mul_fiberAt S K a phi k]
  have hcollapse :
      mackeyDoubleParamSum S K a phi k = cS * inner := by
    dsimp [cS, inner]
    exact mackeyDoubleParamSum_eq_card_mul_inner S K a phi hphi k
  have hEq : cI * fiber = cS * inner := hparam.trans hcollapse
  have hcS : cS ≠ 0 := by
    dsimp [cS]
    exact_mod_cast (Nat.card_pos (α := S)).ne'
  have hcI : cI ≠ 0 := by
    dsimp [cI]
    exact_mod_cast (Nat.card_pos (α := mackeyIntersection S K a)).ne'
  have hfiber : fiber = cI⁻¹ * (cS * inner) := by
    calc
      fiber = cI⁻¹ * (cI * fiber) := by
        rw [← mul_assoc, inv_mul_cancel₀ hcI, one_mul]
      _ = cI⁻¹ * (cS * inner) := by
        rw [hEq]
  rw [mackeySummandAmbientFormula_apply]
  change cS⁻¹ * fiber = cI⁻¹ * inner
  rw [hfiber]
  calc
    cS⁻¹ * (cI⁻¹ * (cS * inner)) =
        cI⁻¹ * ((cS⁻¹ * cS) * inner) := by
          ring
    _ = cI⁻¹ * inner := by
          rw [inv_mul_cancel₀ hcS, one_mul]

public theorem mackey_restriction_inducedCF_apply
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S] [Finite K]
    (phi : ClassFunction S) (hphi : IsClassFunction phi) (k : K) :
    subgroupRestriction K (inducedCF S phi) k = mackeyRestrictionSum S K phi k := by
  classical
  rw [subgroupRestriction_inducedCF_eq_doubleCoset_fiber_sum S K phi k]
  rw [mackeyRestrictionSum_apply_ambientFormula]
  calc
    (Nat.card S : ℂ)⁻¹ *
        ∑ q : DoubleCoset.Quotient (S : Set G) K,
          inducedCFDoubleCosetFiberSum S K phi k q =
      ∑ q : DoubleCoset.Quotient (S : Set G) K,
          (Nat.card S : ℂ)⁻¹ * inducedCFDoubleCosetFiberSum S K phi k q := by
        rw [Finset.mul_sum]
    _ = ∑ q : DoubleCoset.Quotient (S : Set G) K,
          mackeySummandAmbientFormula S K q.out phi k := by
        refine Finset.sum_congr rfl ?_
        intro q _hq
        rw [inducedCFDoubleCosetFiberSum_eq_at_out]
        exact inducedCFDoubleCosetFiberAt_normalized_eq_mackeySummandAmbientFormula
          S K q.out phi hphi k

public theorem mackey_restriction_inducedCF
    {G : Type*} [Group G] [Finite G] (S K : Subgroup G) [Finite S] [Finite K]
    (phi : ClassFunction S) (hphi : IsClassFunction phi) :
    subgroupRestriction K (inducedCF S phi) = mackeyRestrictionSum S K phi := by
  ext k
  exact mackey_restriction_inducedCF_apply S K phi hphi k

public theorem scalarProduct_mackeyRestrictionSum_self_of_offDiagonal_zero
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S]
    (phi psi : ClassFunction S) (hphi : IsClassFunction phi)
    (hoff :
      ∀ q : DoubleCoset.Quotient (S : Set G) S,
        q ≠ DoubleCoset.mk S S 1 →
          scalarProduct S psi (mackeySummand S S q.out phi) = 0) :
    scalarProduct S psi (mackeyRestrictionSum S S phi) =
      scalarProduct S psi phi := by
  classical
  unfold mackeyRestrictionSum familySum
  change scalarProduct S psi
      (fun k : S =>
        ∑ q : DoubleCoset.Quotient (S : Set G) S,
          mackeySummand S S q.out phi k) =
    scalarProduct S psi phi
  rw [scalarProduct_fintype_sum_right]
  let q0 : DoubleCoset.Quotient (S : Set G) S := DoubleCoset.mk S S 1
  rw [Finset.sum_eq_single q0]
  · exact congrArg (fun eta : ClassFunction S => scalarProduct S psi eta)
      (funext fun k => (mackeySummand_principal_eq S phi hphi rfl k))
  · intro q _hq hqne
    exact hoff q hqne
  · intro hq0
    simp at hq0

public theorem scalarProduct_inducedCF_self_of_mackey_offDiagonal_zero
    {G : Type*} [Group G] [Finite G] (S : Subgroup G) [Finite S]
    (phi psi : ClassFunction S) (hphi : IsClassFunction phi)
    (hoff :
      ∀ q : DoubleCoset.Quotient (S : Set G) S,
        q ≠ DoubleCoset.mk S S 1 →
          scalarProduct S psi (mackeySummand S S q.out phi) = 0) :
    scalarProduct G (inducedCF S psi) (inducedCF S phi) =
      scalarProduct S psi phi := by
  classical
  rw [scalarProduct_inducedCF_inducedCF_left S psi phi]
  rw [mackey_restriction_inducedCF S S phi hphi]
  exact scalarProduct_mackeyRestrictionSum_self_of_offDiagonal_zero S phi psi hphi hoff

public theorem isaacs_theorem_6_11_from_mackey_offDiagonal_subgroup
    {G ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    (H T : Subgroup G) [Finite H] [Finite T] (hHT : H ≤ T)
    (theta : ClassFunction H)
    (e : ι → ℕ) (psi : ι → ClassFunction T)
    (chi : ι → ClassFunction G)
    (hpsi_character : ∀ i : ι, IsCharacter (psi i))
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT :
      ∀ i j : ι,
        scalarProduct T (psi i) (psi j) = if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf T) (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF T (psi i))
    (hoff :
      ∀ i j : ι, ∀ q : DoubleCoset.Quotient (T : Set G) T,
        q ≠ DoubleCoset.mk T T 1 →
          scalarProduct T (psi i) (mackeySummand T T q.out (psi j)) = 0) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  classical
  have horthG :
      ∀ i j : ι,
        scalarProduct G (chi i) (chi j) = if i = j then 1 else 0 := by
    intro i j
    rw [hchi i, hchi j]
    calc
      scalarProduct G (inducedCF T (psi i)) (inducedCF T (psi j)) =
          scalarProduct T (psi i) (psi j) := by
            exact scalarProduct_inducedCF_self_of_mackey_offDiagonal_zero
              T (psi j) (psi i) (hpsi_class j) (hoff i j)
      _ = if i = j then 1 else 0 := horthT i j
  have hchi_character : ∀ i : ι, IsCharacter (chi i) := by
    intro i
    rw [hchi i]
    exact isCharacter_inducedCF_of_isCharacter T (psi i) (hpsi_character i)
  have hdecompInd :
      inducedCF H theta =
        weightedFamilySum (fun i => (e i : ℂ)) (fun i : ι => inducedCF T (psi i)) :=
    proposition_1_7_a_decomposition_from_subgroup H T hHT e psi theta hdecompT
  have hdecompChi :
      inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
    calc
      inducedCF H theta =
          weightedFamilySum (fun i => (e i : ℂ)) (fun i : ι => inducedCF T (psi i)) :=
            hdecompInd
      _ = weightedFamilySum (fun i => (e i : ℂ)) chi := by
            exact weightedFamilySum_congr (fun i => (e i : ℂ))
              (fun i : ι => inducedCF T (psi i)) chi
              (fun i => (hchi i).symm)
  exact proposition_1_7_a_from_induced_orthonormal_characters
    e chi (inducedCF H theta) hchi_character horthG hdecompChi

public theorem isaacs_theorem_6_11_from_mackey_and_clifford_restrictions
    {G Vθ : Type u} {ι : Type*} [Group G] [Finite G] [Finite ι] [DecidableEq ι]
    [AddCommGroup Vθ] [Module ℂ Vθ] [FiniteDimensional ℂ Vθ]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : ClassFunction H) (thetaRep : Representation ℂ H Vθ)
    (e : ι → ℕ) (psi : ι → ClassFunction (inertiaSubgroup H theta))
    (chi : ι → ClassFunction G)
    (hpsi_character : ∀ i : ι, IsCharacter (psi i))
    (hpsi_class : ∀ i : ι, IsClassFunction (psi i))
    (horthT : ∀ i j : ι,
      scalarProduct (inertiaSubgroup H theta) (psi i) (psi j) =
        if i = j then 1 else 0)
    (hdecompT :
      inducedCF (H.subgroupOf (inertiaSubgroup H theta))
          (subgroupOfClassFunction theta) =
        weightedFamilySum (fun i => (e i : ℂ)) psi)
    (hchi : ∀ i : ι, chi i = inducedCF (inertiaSubgroup H theta) (psi i))
    (htheta : theta = thetaRep.character)
    (htheta_irreducible : Representation.IsIrreducible thetaRep)
    (hres : ∀ i : ι,
      subgroupRestriction (H.subgroupOf (inertiaSubgroup H theta)) (psi i) =
        (e i : ℂ) • subgroupOfClassFunction theta) :
    (Pairwise fun i j => chi i ≠ chi j) ∧
      (∀ i : ι, IsBookIrreducibleCharacter (chi i)) ∧
      inducedCF H theta = weightedFamilySum (fun i => (e i : ℂ)) chi := by
  let T : Subgroup G := inertiaSubgroup H theta
  have hHT : H ≤ T := by
    intro h hh
    change conjugateOnNormal H theta h = theta
    rw [htheta]
    funext x
    change thetaRep.character ⟨h * (x : G) * h⁻¹, _⟩ = thetaRep.character x
    exact Representation.char_conj (ρ := thetaRep) x ⟨h, hh⟩
  have hoff := mackey_inertia_off_diagonal_zero_of_clifford_restrictions
    H theta thetaRep e psi hpsi_character hpsi_class htheta htheta_irreducible hres
  exact isaacs_theorem_6_11_from_mackey_offDiagonal_subgroup H T hHT theta e psi chi
    hpsi_character hpsi_class horthT hdecompT hchi hoff

end CFSG.Section1
