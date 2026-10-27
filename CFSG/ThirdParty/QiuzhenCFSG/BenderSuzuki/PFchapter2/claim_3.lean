module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_3_appendixI
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Clifford
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.XV.theorem_15_16
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.theorem_8_15
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Core
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection6.PFsection6_5_a
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt.FixedPointProduct

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open External PFAppendixI PFAppendixII Representation
open PFchapter1section2 PFchapter1section3
open scoped Pointwise BigOperators DirectSum IsMulCommutative

/-!
# Peterfalvi, Part II, Chapter II, Claim (3)
-/

universe uNF vNF wNF uF uL uV uFix

/-- The action induced by an embedding in the unit group of a right near-field.
The opposite unit group corrects the order of composition of right translations. -/
private noncomputable def rightNearFieldEmbeddedMulAction_aux
    {F : Type uNF} [RightNearField F]
    {E : Type vNF} [Group E] [IsMulCommutative E]
    (f : E →* Fˣ) (e : E) : MulAut (Multiplicative F) :=
  { toFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x * (f e : F))
    invFun := fun x => Multiplicative.ofAdd (Multiplicative.toAdd x * ((f e)⁻¹ : F))
    left_inv := by
      intro x
      simp
    right_inv := by
      intro x
      simp
    map_mul' := by
      intro x y
      simp [RightNearField.right_distrib] }

private lemma rightNearFieldEmbeddedMulAction_aux_map_mul
    {F : Type uNF} [RightNearField F]
    {E : Type vNF} [Group E] [IsMulCommutative E]
    (f : E →* Fˣ) (a b : E) :
    rightNearFieldEmbeddedMulAction_aux f (a * b) =
      rightNearFieldEmbeddedMulAction_aux f a *
        rightNearFieldEmbeddedMulAction_aux f b := by
  ext x
  have hcomm : (f a : F) * (f b : F) = (f b : F) * (f a : F) := by
    calc
      (f a : F) * (f b : F) = ((f a * f b : Fˣ) : F) := rfl
      _ = ((f (a * b) : Fˣ) : F) := by simp
      _ = ((f (b * a) : Fˣ) : F) := by rw [mul_comm a b]
      _ = ((f b * f a : Fˣ) : F) := by simp
      _ = (f b : F) * (f a : F) := rfl
  calc
    rightNearFieldEmbeddedMulAction_aux f (a * b) x
        = Multiplicative.ofAdd (Multiplicative.toAdd x * (f (a * b) : F)) := rfl
    _ = Multiplicative.ofAdd (Multiplicative.toAdd x * ((f a : F) * (f b : F))) := by simp
    _ = Multiplicative.ofAdd (Multiplicative.toAdd x * ((f b : F) * (f a : F))) := by rw [hcomm]
    _ = Multiplicative.ofAdd ((Multiplicative.toAdd x * (f b : F)) * (f a : F)) := by
      simp [mul_assoc]
    _ = (rightNearFieldEmbeddedMulAction_aux f a * rightNearFieldEmbeddedMulAction_aux f b) x := by
      rw [MulAut.mul_apply]
      rfl

private noncomputable def rightNearFieldEmbeddedRightMulAction
    {F : Type uNF} [RightNearField F]
    {E : Type vNF} [Group E] [IsMulCommutative E]
    (f : E →* Fˣ) : E →* MulAut (Multiplicative F) :=
  { toFun := rightNearFieldEmbeddedMulAction_aux f
    map_one' := by
      ext x
      unfold rightNearFieldEmbeddedMulAction_aux
      simp [map_one, mul_one]
    map_mul' := rightNearFieldEmbeddedMulAction_aux_map_mul f }

private theorem rightNearFieldEmbeddedRightMulAction_apply
    {F : Type uNF} [RightNearField F]
    {E : Type vNF} [Group E] [IsMulCommutative E]
    (f : E →* Fˣ) (e : E) (x : F) :
    rightNearFieldEmbeddedRightMulAction f e (Multiplicative.ofAdd x) =
      Multiplicative.ofAdd (x * (f e : F)) := by
  unfold rightNearFieldEmbeddedRightMulAction
  unfold rightNearFieldEmbeddedMulAction_aux
  rfl

private theorem rightNearFieldEmbeddedRightMulAction_injective
    {F : Type uNF} [RightNearField F]
    {E : Type vNF} [Group E] [IsMulCommutative E]
    (f : E →* Fˣ) (hf : Function.Injective f) :
    Function.Injective (rightNearFieldEmbeddedRightMulAction f) := by
  intro e₁ e₂ he
  apply hf
  apply Units.ext
  have h := congrArg
    (fun a : MulAut (Multiplicative F) =>
      Multiplicative.toAdd (a (Multiplicative.ofAdd (1 : F)))) he
  simpa [rightNearFieldEmbeddedRightMulAction_apply] using h

/-- An odd elementary abelian subgroup of the unit group of a finite right
near-field has prime order.  This is the Huppert V.8.15 bridge used in Claim (3). -/
private theorem elementaryAbelian_card_eq_prime_of_injective_to_rightNearField_units
    {F : Type uNF} [RightNearField F] [Finite F]
    {E : Type vNF} [Group E] [Finite E] [Nontrivial E]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r E]
    (hr_two : r ≠ 2) (f : E →* Fˣ) (hf : Function.Injective f) :
    Nat.card E = r := by
  classical
  let rho : E →* MulAut (Multiplicative F) :=
    rightNearFieldEmbeddedRightMulAction f
  have hrho : Function.Injective rho :=
    rightNearFieldEmbeddedRightMulAction_injective f hf
  let A : Subgroup (MulAut (Multiplicative F)) := rho.range
  have hfixed :
      ∀ phi : A, phi ≠ 1 → ∀ x : Multiplicative F,
        (phi : MulAut (Multiplicative F)) x = x → x = 1 := by
    intro phi hphi x hx
    rcases phi.2 with ⟨e, he⟩
    change Multiplicative.toAdd x = 0
    by_contra hx_zero
    have hx_mul : Multiplicative.toAdd x * (f e : F) = Multiplicative.toAdd x := by
      rw [← he] at hx
      have hx_fixed : rightNearFieldEmbeddedRightMulAction f e x = x := by
        simpa [rho] using hx
      have happly := congrArg Multiplicative.toAdd
        (rightNearFieldEmbeddedRightMulAction_apply f e (Multiplicative.toAdd x))
      calc
        Multiplicative.toAdd x * (f e : F) =
            Multiplicative.toAdd (rightNearFieldEmbeddedRightMulAction f e x) := by
          simpa using happly.symm
        _ = Multiplicative.toAdd x := congrArg Multiplicative.toAdd hx_fixed
    have hfe : f e = 1 :=
      rightNearField_mul_right_fixed_of_ne_zero hx_zero (f e) hx_mul
    have he_one : e = 1 := by
      apply hf
      simpa using hfe
    apply hphi
    apply Subtype.ext
    rw [← he, he_one, map_one]
    rfl
  have hclassification :=
    huppert_V_8_15_fixedPointFree_automorphism_subgroup_classification A hfixed
  let eA : E ≃* A := MonoidHom.ofInjective hrho
  have hA_r : IsPGroup r A :=
    (IsElementaryAbelian.isPGroup r E).of_equiv eA
  have htop_r : IsPGroup r (⊤ : Subgroup A) := hA_r.to_subgroup ⊤
  have htop_index : ¬ r ∣ (⊤ : Subgroup A).index := by
    simp [Nat.Prime.not_dvd_one (Fact.out : r.Prime)]
  let R : Sylow r A := htop_r.toSylow htop_index
  have hR_cyclic : IsCyclic R := hclassification.1 r hr_two R
  have hRtop : (R : Subgroup A) = (⊤ : Subgroup A) := by
    ext x
    simp [R]
  have htop_cyclic : IsCyclic (⊤ : Subgroup A) := by
    -- hRtop gives equality of the underlying subgroups, so we can transport IsCyclic
    exact (hRtop ▸ hR_cyclic)
  have hA_cyclic : IsCyclic A :=
    (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).isCyclic.mp htop_cyclic
  have hE_cyclic : IsCyclic E := eA.isCyclic.mpr hA_cyclic
  calc
    Nat.card E = Monoid.exponent E := hE_cyclic.exponent_eq_card.symm
    _ = r := IsElementaryAbelian.exponent_eq_prime (p := r) (G := E)

/-- The unit coordinate in `PropositionOneConclusion` identifies its `Q`
factor with the unit group of the resulting right near-field. -/
private theorem propositionOneConclusion_exists_injective_to_rightNearField_units
    {B : Type uNF} [Group B] (H D Q : Subgroup B)
    {F : Type vNF} [RightNearField F] [Finite F]
    (hPO : PropositionOneConclusion H D Q F)
    {E : Type wNF} [Group E] (j : E →* Q) (hj : Function.Injective j) :
    ∃ f : E →* Fˣ, Function.Injective f := by
  obtain ⟨unitEquiv⟩ :=
    PFAppendixII.propositionOneConclusion_unitsEquiv H D Q hPO
  let f : E →* Fˣ := unitEquiv.symm.toMonoidHom.comp j
  refine ⟨f, ?_⟩
  exact unitEquiv.symm.injective.comp hj


/-- Restrict a quotient map to a subgroup, retaining injectivity when the
source meets the quotient kernel trivially. -/
private theorem exists_injective_to_quotient_subgroup_map
    {C : Type uNF} [Group C] (core QP : Subgroup C) [core.Normal]
    {E : Type wNF} [Group E] (j : E →* C)
    (hj_QP : ∀ e : E, j e ∈ QP)
    (hj_core : ∀ e : E, j e ∈ core → e = 1) :
    ∃ f : E →* QP.map (QuotientGroup.mk' core), Function.Injective f := by
  let pi : C →* C ⧸ core := QuotientGroup.mk' core
  let jbar : E →* C ⧸ core := pi.comp j
  have hjbar_mem (e : E) : jbar e ∈ QP.map pi := by
    exact ⟨j e, hj_QP e, rfl⟩
  let f : E →* QP.map pi := jbar.codRestrict (QP.map pi) hjbar_mem
  refine ⟨f, ?_⟩
  intro x y hxy
  have hbar : pi (j x) = pi (j y) := by
    simpa [f, jbar] using congrArg Subtype.val hxy
  have hdiv_quot : pi (j (x * y⁻¹)) = 1 := by
    simp only [map_mul, map_inv, hbar, mul_inv_cancel]
  have hdiv_core : j (x * y⁻¹) ∈ core :=
    (QuotientGroup.eq_one_iff (N := core) (j (x * y⁻¹))).1 hdiv_quot
  exact mul_inv_eq_one.mp (hj_core (x * y⁻¹) hdiv_core)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The `P`-fixed subgroup of the minimal elementary abelian layer embeds in
the image of `Q ∩ C_G(P)` modulo a core contained in `D ∩ C_G(P)`. -/
private theorem claim3_fixedPointSubgroup_exists_injective_to_quotient_QP
    {G : Type uNF} [Group G]
    (D Q Q1 P L : Subgroup G)
    (hP_le_L : P ≤ L) (hQ1_le_Q : Q1 ≤ Q) (hQD : Disjoint Q D)
    [MulDistribMulAction L Q1]
    (haction : ∀ l : L, ∀ q : Q1,
      ((l • q : Q1) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    {r : ℕ} (R : Sylow r Q1)
    (hRinv : IsInvariant L Q1 (R : Subgroup Q1))
    (M : Subgroup R) (hMinv : IsInvariant L R M)
    (N : Subgroup M) (hNinv : IsInvariant L M N)
    (core : Subgroup (Subgroup.centralizer (P : Set G))) [core.Normal]
    (hcore_le_DP : core ≤
      D.comap (Subgroup.centralizer (P : Set G)).subtype) :
    letI : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
    letI : IsInvariant L R M := hMinv
    letI : IsInvariant L M N := hNinv
    let PL : Subgroup L := P.subgroupOf L
    letI : MulDistribMulAction PL N :=
      MulDistribMulAction.compHom N PL.subtype
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let QP : Subgroup C := Q.comap C.subtype
    ∃ f : fixedPointSubgroup PL N →* QP.map (QuotientGroup.mk' core),
      Function.Injective f := by
  let : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
  let : IsInvariant L R M := hMinv
  let : IsInvariant L M N := hNinv
  let PL : Subgroup L := P.subgroupOf L
  let : MulDistribMulAction PL N :=
    MulDistribMulAction.compHom N PL.subtype
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let QP : Subgroup C := Q.comap C.subtype
  let E : Subgroup N := fixedPointSubgroup PL N
  let nToG : N →* G :=
    Q1.subtype.comp
      ((R : Subgroup Q1).subtype.comp (M.subtype.comp N.subtype))
  let jRaw : E →* G := nToG.comp E.subtype
  have hjRaw_mem_C (e : E) : jRaw e ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxP
    let xL : L := ⟨x, hP_le_L hxP⟩
    let xPL : PL := ⟨xL, hxP⟩
    have he_fixed : ∀ a : PL, a • (e : N) = e := by
      have he : (e : N) ∈ fixedPointSubgroup PL N := e.property
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at he
      exact he
    have hfixN : xPL • (e : N) = e := he_fixed xPL
    have hfixL : xL • (e : N) = e := hfixN
    have hfixQ1 :
        (xL • ((((e : E) : N) : M) : R) : Q1) =
          ((((e : E) : N) : M) : R) :=
      congrArg (fun y : N => ((((y : N) : M) : R) : Q1)) hfixL
    have hconj :
        x * (((((e : E) : N) : M) : R) : Q1) * x⁻¹ =
          (((((e : E) : N) : M) : R) : Q1) :=
      (haction xL ((((e : E) : N) : M) : R)).symm.trans
        (congrArg Subtype.val hfixQ1)
    exact mul_inv_eq_iff_eq_mul.mp hconj
  let j : E →* C := jRaw.codRestrict C hjRaw_mem_C
  have hnToG_injective : Function.Injective nToG :=
    Q1.subtype_injective.comp
      ((R : Subgroup Q1).subtype_injective.comp
        (M.subtype_injective.comp N.subtype_injective))
  have hj_injective : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply hnToG_injective
    simpa [j, jRaw] using congrArg Subtype.val hxy
  have hj_QP (e : E) : j e ∈ QP := by
    change (j e : G) ∈ Q
    exact hQ1_le_Q (((((e : E) : N) : M) : R) : Q1).property
  have hj_core (e : E) (hecore : j e ∈ core) : e = 1 := by
    have heD : (j e : G) ∈ D := hcore_le_DP hecore
    have heQ : (j e : G) ∈ Q := hj_QP e
    have he_bot : (j e : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hQD) heQ heD
    apply hj_injective
    apply Subtype.ext
    simpa using he_bot
  exact exists_injective_to_quotient_subgroup_map core QP j hj_QP hj_core

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The Claim (2b) quotient near-field model forces the nontrivial `P`-fixed
subgroup of the elementary abelian `r`-layer to have order `r`. -/
private theorem claim3_fixedPointSubgroup_card_eq_prime_of_propositionOneConclusion
    {G : Type uNF} [Group G] [Finite G]
    (D Q Q1 P L : Subgroup G)
    (hP_le_L : P ≤ L) (hQ1_le_Q : Q1 ≤ Q) (hQD : Disjoint Q D)
    [MulDistribMulAction L Q1]
    (haction : ∀ l : L, ∀ q : Q1,
      ((l • q : Q1) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    {r : ℕ} [Fact r.Prime]
    (R : Sylow r Q1) (hRinv : IsInvariant L Q1 (R : Subgroup Q1))
    (M : Subgroup R) (hMinv : IsInvariant L R M)
    (N : Subgroup M) (hNinv : IsInvariant L M N)
    (hNelem : IsElementaryAbelian r N)
    (core : Subgroup (Subgroup.centralizer (P : Set G))) [core.Normal]
    (hcore_le_DP : core ≤
      D.comap (Subgroup.centralizer (P : Set G)).subtype)
    (Hbar Dbar : Subgroup (Subgroup.centralizer (P : Set G) ⧸ core))
    {F : Type vNF} [RightNearField F] [Finite F]
    (hPO : PropositionOneConclusion Hbar Dbar
      ((Q.comap (Subgroup.centralizer (P : Set G)).subtype).map
        (QuotientGroup.mk' core)) F)
    (hr_two : r ≠ 2)
    (hfixed_nontrivial :
      letI : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
      letI : IsInvariant L R M := hMinv
      letI : IsInvariant L M N := hNinv
      let PL : Subgroup L := P.subgroupOf L
      letI : MulDistribMulAction PL N :=
        MulDistribMulAction.compHom N PL.subtype
      Nontrivial (fixedPointSubgroup PL N)) :
    letI : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
    letI : IsInvariant L R M := hMinv
    letI : IsInvariant L M N := hNinv
    let PL : Subgroup L := P.subgroupOf L
    letI : MulDistribMulAction PL N :=
      MulDistribMulAction.compHom N PL.subtype
    Nat.card (fixedPointSubgroup PL N) = r := by
  let : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
  let : IsInvariant L R M := hMinv
  let : IsInvariant L M N := hNinv
  let PL : Subgroup L := P.subgroupOf L
  let : MulDistribMulAction PL N :=
    MulDistribMulAction.compHom N PL.subtype
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let QP : Subgroup C := Q.comap C.subtype
  let E : Subgroup N := fixedPointSubgroup PL N
  let : IsElementaryAbelian r N := hNelem
  have hEelem : IsElementaryAbelian r E := by
    refine
      { toIsMulCommutative := by infer_instance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro e
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p r N) (e : N)
  let : IsElementaryAbelian r E := hEelem
  let : Nontrivial E := hfixed_nontrivial
  obtain ⟨j, hj⟩ :=
    claim3_fixedPointSubgroup_exists_injective_to_quotient_QP
      D Q Q1 P L hP_le_L hQ1_le_Q hQD haction R hRinv M hMinv N hNinv
        core hcore_le_DP
  obtain ⟨f, hf⟩ :=
    propositionOneConclusion_exists_injective_to_rightNearField_units
      Hbar Dbar (QP.map (QuotientGroup.mk' core)) hPO j hj
  exact elementaryAbelian_card_eq_prime_of_injective_to_rightNearField_units
    hr_two f hf


/-- Prime-dimensional Clifford dichotomy.  An irreducible representation
restricts to a normal subgroup either irreducibly or with a one-dimensional
irreducible constituent. -/
private theorem clifford_prime_finrank_restriction
    {F : Type uF} {L : Type uL} {V : Type uV}
    [Field F] [Group L] [Finite L]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (rho : Representation F L V) (K : Subgroup L) [K.Normal]
    (hrho : Representation.IsIrreducible rho)
    {p : Nat} (hp : Nat.Prime p) (hdim : Module.finrank F V = p) :
    (∃ W : Subrepresentation (rho.comp K.subtype),
        Representation.IsIrreducible W.toRepresentation ∧
          Module.finrank F W.toSubmodule = 1) ∨
      Representation.IsIrreducible (rho.comp K.subtype) := by
  let rhoK : Representation F K V := rho.comp K.subtype
  let : Representation.IsIrreducible rho := hrho
  let : Nontrivial V :=
    Subrepresentation.irreducible_module_nontrivial rho
  obtain ⟨W, hWirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional rhoK
  obtain ⟨n, g, hInternal, hUirr, hConj, _hMultiplicity⟩ :=
    Theory.Representation.isaacs_theorem_6_5.{uF, uL, uV, uV}
      rho K hrho W hWirr
  let U : Fin n → Subrepresentation rhoK := fun i =>
    Theory.Representation.conjugateSubrepresentation rho K W (g i)
  change DirectSum.IsInternal (fun i => (U i).toSubmodule) at hInternal
  have hUdim (i : Fin n) :
      Module.finrank F (U i).toSubmodule =
        Module.finrank F W.toSubmodule := by
    simpa [U] using
      (LinearEquiv.finrank_eq (hConj i).some.toLinearEquiv)
  have hdimSum :
      Module.finrank F V =
        ∑ i : Fin n, Module.finrank F (U i).toSubmodule := by
    let e : (DirectSum (Fin n) fun i => (U i).toSubmodule) ≃ₗ[F] V :=
      LinearEquiv.ofBijective
        (DirectSum.coeLinearMap fun i => (U i).toSubmodule) hInternal
    calc
      Module.finrank F V =
          Module.finrank F (DirectSum (Fin n) fun i => (U i).toSubmodule) :=
        (LinearEquiv.finrank_eq e).symm
      _ = ∑ i : Fin n, Module.finrank F (U i).toSubmodule :=
        Module.finrank_directSum F _
  have hfactor : p = n * Module.finrank F W.toSubmodule := by
    calc
      p = Module.finrank F V := hdim.symm
      _ = ∑ i : Fin n, Module.finrank F (U i).toSubmodule := hdimSum
      _ = ∑ _i : Fin n, Module.finrank F W.toSubmodule := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact hUdim i
      _ = n * Module.finrank F W.toSubmodule := by simp
  rcases hp.eq_one_or_self_of_dvd n
      ⟨Module.finrank F W.toSubmodule, hfactor⟩ with hn | hn
  · right
    subst n
    have hUtop : U 0 = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      change (U 0).toSubmodule = (⊤ : Submodule F V)
      simpa using hInternal.submodule_iSup_eq_top
    have htopIrr := hUirr 0
    change Representation.IsIrreducible (U 0).toRepresentation at htopIrr
    rw [hUtop] at htopIrr
    show IsSimpleOrder (Subrepresentation rhoK)
    rw [isSimpleOrder_iff_isAtom_top]
    exact
      (Subrepresentation.irreducible_iff_isAtom
        (⊤ : Subrepresentation rhoK)).mp htopIrr
  · left
    have hpd : p = p * Module.finrank F W.toSubmodule := by
      simpa [hn] using hfactor
    have hd : Module.finrank F W.toSubmodule = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      calc
        p * Module.finrank F W.toSubmodule = p := hpd.symm
        _ = p * 1 := by simp
    exact ⟨W, hWirr, hd⟩

/-- The prime-dimensional Clifford dichotomy for the representation attached
to an action on an elementary abelian group. -/
private theorem elementaryAbelian_clifford_prime_finrank_restriction
    {L : Type uL} {N : Type uV} [Group L] [Finite L] [Group N] [Finite N]
    {r p : Nat} [Fact r.Prime] [IsElementaryAbelian r N]
    [MulDistribMulAction L N]
    (K : Subgroup L) [K.Normal]
    (hrho : Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)))
    (hp : Nat.Prime p)
    (hdim : Module.finrank (ZMod r) (Additive N) = p) :
    (∃ W : Subrepresentation
        ((Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)).comp K.subtype),
        Representation.IsIrreducible W.toRepresentation ∧
          Module.finrank (ZMod r) W.toSubmodule = 1) ∨
      Representation.IsIrreducible
        ((Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)).comp K.subtype) := by
  exact clifford_prime_finrank_restriction
    (Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r))
    K hrho hp hdim


set_option backward.isDefEq.respectTransparency false in
/-- Chapter-I Proposition 3 supplies a binary field model whose scalar and
field-automorphism coordinates respect direct conjugation on any transported
copy of `K`. -/
private theorem claim3_chapterI_semilinear_adapter
    {G : Type uNF} [Group G]
    (D K V W Q0 : Subgroup G)
    {F : Type uF} [Field F]
    (A : Subgroup (F ≃+* F))
    (hKleD : K ≤ D) (hVleD : V ≤ D)
    [hWV : (W.subgroupOf V).Normal]
    [hWD : (W.subgroupOf D).Normal]
    (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
    (rhoMul : Fˣ →* MulAut (Multiplicative F))
    (rhoAut : A →* MulAut
      (SemidirectProduct (Multiplicative F) Fˣ rhoMul))
    (k_units : K ≃* Fˣ)
    (vmodW_aut : V ⧸ W.subgroupOf V ≃* A)
    (modelIso :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut)
    (hrhoAut_inr : ∀ sigma : A, ∀ u : Fˣ,
      rhoAut sigma (SemidirectProduct.inr u) =
        SemidirectProduct.inr
          (Units.map (sigma : F ≃+* F).toMonoidWithZeroHom u))
    (hmodel_k : ∀ k : K,
      modelIso
          (SemidirectProduct.inr
            (QuotientGroup.mk
              (⟨(k : G), hKleD k.property⟩ : D))) =
        SemidirectProduct.inl
          (SemidirectProduct.inr (k_units k)))
    (hmodel_v : ∀ v : V,
      modelIso
          (SemidirectProduct.inr
            (QuotientGroup.mk
              (⟨(v : G), hVleD v.property⟩ : D))) =
        SemidirectProduct.inr
          (vmodW_aut (QuotientGroup.mk v)))
    {K0 : Type uL} [Group K0]
    (kToK : K0 →* K) (hkToK : Function.Injective kToK)
    {P0 : Type uV} [Group P0]
    (pToV : P0 →* V)
    (act : P0 →* MulAut K0)
    (hact : ∀ a : P0, ∀ k : K0,
      (((kToK (act a k) : K) : G)) =
        ((pToV a : V) : G) * ((kToK k : K) : G) *
          ((pToV a : V) : G)⁻¹) :
    let scalar2 : K0 →* Fˣ := k_units.toMonoidHom.comp kToK
    let sigma2 : P0 →* (F ≃+* F) :=
      A.subtype.comp
        (vmodW_aut.toMonoidHom.comp
          ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV))
    Function.Injective scalar2 ∧
      ∀ a : P0, ∀ k : K0,
        scalar2 (act a k) =
          Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k) := by
  dsimp
  refine ⟨k_units.injective.comp hkToK, ?_⟩
  intro a k
  let v : V := pToV a
  let dV : D := ⟨(v : G), hVleD v.property⟩
  let dK : D := ⟨((kToK k : K) : G), hKleD (kToK k).property⟩
  let dAct : D :=
    ⟨((kToK (act a k) : K) : G), hKleD (kToK (act a k)).property⟩
  let piD : D →* D ⧸ W.subgroupOf D :=
    QuotientGroup.mk' (W.subgroupOf D)
  have hdAct : dAct = dV * dK * dV⁻¹ := by
    apply Subtype.ext
    exact hact a k
  have hqAct : piD dAct = piD dV * piD dK * (piD dV)⁻¹ := by
    calc
      piD dAct = piD (dV * dK * dV⁻¹) := congrArg piD hdAct
      _ = piD dV * piD dK * (piD dV)⁻¹ := by simp
  have hsemi :
      SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dAct) =
        SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dV) *
          SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dK) *
            (SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dV))⁻¹ := by
    calc
      SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dAct) =
          SemidirectProduct.inr (N := Q0) (φ := rhoD)
            (piD dV * piD dK * (piD dV)⁻¹) :=
        congrArg SemidirectProduct.inr hqAct
      _ = SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dV) *
          SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dK) *
            (SemidirectProduct.inr (N := Q0) (φ := rhoD) (piD dV))⁻¹ := by simp
  have hmodel := congrArg modelIso hsemi
  rw [map_mul, map_mul, map_inv] at hmodel
  rw [show piD dAct = QuotientGroup.mk dAct from rfl,
    show piD dV = QuotientGroup.mk dV from rfl,
    show piD dK = QuotientGroup.mk dK from rfl] at hmodel
  rw [show dAct =
      ⟨((kToK (act a k) : K) : G), hKleD (kToK (act a k)).property⟩ from rfl,
    show dV = ⟨(v : G), hVleD v.property⟩ from rfl,
    show dK = ⟨((kToK k : K) : G), hKleD (kToK k).property⟩ from rfl,
    hmodel_k, hmodel_v, hmodel_k] at hmodel
  have hconj := SemidirectProduct.inl_aut (φ := rhoAut)
    (vmodW_aut (QuotientGroup.mk v))
    (SemidirectProduct.inr (N := Multiplicative F) (φ := rhoMul)
      (k_units (kToK k)))
  have hconj' :
      SemidirectProduct.inr (φ := rhoAut) (vmodW_aut (QuotientGroup.mk v)) *
          SemidirectProduct.inl (φ := rhoAut)
            (SemidirectProduct.inr (N := Multiplicative F) (φ := rhoMul)
              (k_units (kToK k))) *
            (SemidirectProduct.inr (φ := rhoAut)
              (vmodW_aut (QuotientGroup.mk v)))⁻¹ =
        SemidirectProduct.inl (φ := rhoAut)
          (rhoAut (vmodW_aut (QuotientGroup.mk v))
            (SemidirectProduct.inr (N := Multiplicative F) (φ := rhoMul)
              (k_units (kToK k)))) := by
    simpa only [map_inv] using hconj.symm
  rw [hconj', hrhoAut_inr] at hmodel
  exact SemidirectProduct.inr_injective
    (SemidirectProduct.inl_injective hmodel)

/-- The Chapter-I binary field degree equals the Chapter-II prime once the
two cardinality descriptions of `Q0` are identified. -/
private theorem claim3_binary_galoisField_finrank_eq_of_q0_card
    {Q0Type : Type*} (n p : Nat) (hn : n ≠ 0)
    (hmodelCard : Nat.card Q0Type = Nat.card (GaloisField 2 n))
    (hQ0card : Nat.card Q0Type = 2 ^ p) :
    Module.finrank (ZMod 2) (GaloisField 2 n) = p := by
  have hpow : 2 ^ n = 2 ^ p := by
    calc
      2 ^ n = Nat.card (GaloisField 2 n) :=
        (GaloisField.card 2 n hn).symm
      _ = Nat.card Q0Type := hmodelCard.symm
      _ = 2 ^ p := hQ0card
  have hnp : n = p :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow
  simpa [hnp] using GaloisField.finrank 2 hn


/-- A one-dimensional constituent of a fixed-point-free representation gives the first congruence branch. -/
private theorem claim3_actor_card_dvd_prime_sub_one_of_oneDim_subrepresentation
    {K V : Type*} [Group K] [Finite K]
    {r : ℕ} [Fact r.Prime]
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (rho : Representation (ZMod r) K V)
    (W : Subrepresentation rho)
    (hWdim : Module.finrank (ZMod r) W.toSubmodule = 1)
    (hfree : ∀ k : K, k ≠ 1 → ∀ v : V, rho k v = v → v = 0) :
    Nat.card K ∣ r - 1 := by
  let rhoW := W.toRepresentation
  let : MulDistribMulAction K (Multiplicative W.toSubmodule) := {
    smul k x := Multiplicative.ofAdd (rhoW k (Multiplicative.toAdd x))
    one_smul x := by
      change Multiplicative.ofAdd
        (rhoW 1 (Multiplicative.toAdd x)) = x
      rw [rhoW.map_one]
      rfl
    mul_smul k l x := by
      change Multiplicative.ofAdd
          (rhoW (k * l) (Multiplicative.toAdd x)) =
        Multiplicative.ofAdd
          (rhoW k (rhoW l (Multiplicative.toAdd x)))
      rw [rhoW.map_mul]
      rfl
    smul_mul k x y := by
      apply Multiplicative.toAdd.injective
      exact (rhoW k).map_add (Multiplicative.toAdd x) (Multiplicative.toAdd y)
    smul_one k := by
      apply Multiplicative.toAdd.injective
      exact (rhoW k).map_zero
  }
  have hfreeW : ∀ k : K, k ≠ 1 →
      ∀ x : Multiplicative W.toSubmodule, k • x = x → x = 1 := by
    intro k hk x hx
    have hxW := congrArg Multiplicative.toAdd hx
    have hxV : rho k ((Multiplicative.toAdd x : W.toSubmodule) : V) =
        ((Multiplicative.toAdd x : W.toSubmodule) : V) :=
      congrArg Subtype.val hxW
    have hzero := hfree k hk _ hxV
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simpa using hzero
  have hWcard : Nat.card W.toSubmodule = r := by
    have hnat := Module.natCard_eq_pow_finrank
      (K := ZMod r) (V := W.toSubmodule)
    simpa [ZMod.card, hWdim] using hnat
  have hmultCard : Nat.card (Multiplicative W.toSubmodule) = r := by
    exact (Nat.card_congr Multiplicative.toAdd).trans hWcard
  have hdvd := Section6.natCard_actor_dvd_group_card_sub_one hfreeW
  simpa [hmultCard] using hdvd

/-- Equality of two power descriptions of an automorphism of a finite cyclic
group gives equality of the exponents modulo the group order. -/
private theorem modEq_of_equal_power_actions
    {K : Type*} [Group K] [Finite K] [IsCyclic K]
    {m r e : ℕ} (hcard : Nat.card K = m)
    (hpow : ∀ k : K, k ^ r = k ^ e) :
    r ≡ e [MOD m] := by
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := K)
  have hkorder : orderOf k = Nat.card K :=
    orderOf_eq_card_of_forall_mem_zpowers hk
  simpa [hkorder, hcard] using
    (pow_eq_pow_iff_modEq.mp (hpow k))

/-- Every automorphism of a finite field of degree `p` over `ZMod r` is a
power of Frobenius, written as a pointwise power formula. -/
private theorem finiteField_ringAut_eq_frobenius_pow
    {F : Type*} [Field F] [Finite F]
    {r p : ℕ} [Fact r.Prime] [CharP F r] [Algebra (ZMod r) F]
    (hfinrank : Module.finrank (ZMod r) F = p)
    (σ : F ≃+* F) :
    ∃ i : ℕ, i < p ∧ ∀ x : F, σ x = x ^ (r ^ i) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let σAlg : F ≃ₐ[ZMod r] F :=
    AlgEquiv.ofRingEquiv (f := σ) (by
      intro x
      have h :
          (σ.toRingHom.comp (algebraMap (ZMod r) F) : ZMod r →+* F) =
            algebraMap (ZMod r) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  obtain ⟨⟨i, hi⟩, hσ⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
      (ZMod r) F).2 σAlg
  refine ⟨i, by simpa [hfinrank] using hi, ?_⟩
  intro x
  have hσx := DFunLike.congr_fun hσ x
  calc
    σ x = σAlg x := rfl
    _ = (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod r) F ^ i) x :=
      hσx.symm
    _ = ((⇑(FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod r) F))^[i]) x := by
      rw [AlgEquiv.coe_pow]
    _ = x ^ (Fintype.card (ZMod r) ^ i) :=
      congrFun
        (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate
          (ZMod r) F i) x
    _ = x ^ (r ^ i) := by rw [ZMod.card]

/-- The cardinality form used to turn a faithful order-`p` operator group
into the full automorphism group of a field with `r ^ p` elements. -/
private theorem finiteField_ringAut_card_eq_of_finrank
    {F : Type*} [Field F] [Finite F]
    {r p : ℕ} [Fact r.Prime] [CharP F r] [Algebra (ZMod r) F]
    (hfinrank : Module.finrank (ZMod r) F = p) :
    Nat.card (F ≃+* F) = p := by
  classical
  let e : (F ≃+* F) ≃ (F ≃ₐ[ZMod r] F) :=
    { toFun := fun σ =>
        AlgEquiv.ofRingEquiv (f := σ) (by
          intro x
          have h :
              (σ.toRingHom.comp (algebraMap (ZMod r) F) : ZMod r →+* F) =
                algebraMap (ZMod r) F :=
            RingHom.ext_zmod _ _
          exact DFunLike.congr_fun h x)
      invFun := fun σ => σ.toRingEquiv
      left_inv := by
        intro σ
        ext x
        rfl
      right_inv := by
        intro σ
        ext x
        rfl }
  calc
    Nat.card (F ≃+* F) = Nat.card (F ≃ₐ[ZMod r] F) :=
      Nat.card_congr e
    _ = Module.finrank (ZMod r) F :=
      IsGalois.card_aut_eq_finrank (ZMod r) F
    _ = p := hfinrank

/-- The extension degree is determined by the cardinality of the finite
field. -/
private theorem finiteField_finrank_eq_of_natCard_eq_prime_pow
    {F : Type*} [Field F] [Finite F]
    {r p : ℕ} [Fact r.Prime] [CharP F r] [Algebra (ZMod r) F]
    (hcard : Nat.card F = r ^ p) :
    Module.finrank (ZMod r) F = p := by
  classical
  let : Fintype F := Fintype.ofFinite F
  apply Nat.pow_right_injective (Fact.out : r.Prime).two_le
  calc
    r ^ Module.finrank (ZMod r) F = Nat.card F :=
      FiniteField.pow_finrank_eq_natCard r F
    _ = r ^ p := hcard

/-- A faithful order-`p` group of automorphisms of a field of cardinality
`r ^ p` contains the Frobenius automorphism `x ↦ x ^ r`. -/
private theorem exists_actor_with_prime_frobenius
    {P F : Type*} [Group P] [Finite P] [Field F] [Finite F]
    {r p : ℕ} [Fact r.Prime] [CharP F r] [Algebra (ZMod r) F]
    (σ : P →* (F ≃+* F)) (hσ : Function.Injective σ)
    (hcardP : Nat.card P = p) (hcardF : Nat.card F = r ^ p) :
    ∃ a : P, ∀ x : F, σ a x = x ^ r := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let : Fintype F := Fintype.ofFinite F
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
      intro e f h
      ext x
      exact congrFun h x)
  let : Fintype (F ≃+* F) := Fintype.ofFinite (F ≃+* F)
  have hfinrank : Module.finrank (ZMod r) F = p :=
    finiteField_finrank_eq_of_natCard_eq_prime_pow hcardF
  have hcardAut : Nat.card (F ≃+* F) = p :=
    finiteField_ringAut_card_eq_of_finrank hfinrank
  have hσbij : Function.Bijective σ :=
    (Fintype.bijective_iff_injective_and_card σ).2
      ⟨hσ, by simpa [Nat.card_eq_fintype_card] using hcardP.trans hcardAut.symm⟩
  let frob : F ≃+* F :=
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod r) F).toRingEquiv
  obtain ⟨a, ha⟩ := hσbij.2 frob
  refine ⟨a, ?_⟩
  intro x
  rw [ha]
  change x ^ Fintype.card (ZMod r) = x ^ r
  rw [ZMod.card]

/-- Semilinear compatibility transfers faithfulness of the action on the
scalar subgroup to faithfulness of the field-automorphism part. -/
private theorem semilinear_aut_injective_of_faithful_scalar_action
    {K P F : Type*} [Group K] [Group P] [Field F]
    (act : P →* MulAut K) (hact : Function.Injective act)
    (scalar : K →* Fˣ) (hscalar : Function.Injective scalar)
    (sigma : P →* (F ≃+* F))
    (hcompat : ∀ a : P, ∀ k : K,
      scalar (act a k) =
        Units.map (sigma a).toMonoidWithZeroHom (scalar k)) :
    Function.Injective sigma := by
  intro a b hab
  apply hact
  apply MulEquiv.ext
  intro k
  apply hscalar
  rw [hcompat, hcompat, hab]

/-- The transferable core of Claim (3)'s irreducible branch. The two
compatibility hypotheses say that the same operator on `K` is semilinear in
the Appendix-I `r`-field model and in the Chapter-I binary field model. -/
private theorem modEq_of_semilinear_field_models
    {K P Fr F2 : Type*}
    [Group K] [Finite K] [IsCyclic K] [Group P] [Finite P]
    [Field Fr] [Finite Fr] [Field F2] [Finite F2]
    {r p : ℕ} [Fact r.Prime]
    [CharP F2 2] [Algebra (ZMod 2) F2]
    (hcardK : Nat.card K = 2 ^ p - 1)
    (hfinrank2 : Module.finrank (ZMod 2) F2 = p)
    (act : P →* MulAut K)
    (scalarR : K →* Frˣ) (hscalarR : Function.Injective scalarR)
    (sigmaR : P →* (Fr ≃+* Fr))
    (scalar2 : K →* F2ˣ) (hscalar2 : Function.Injective scalar2)
    (sigma2 : P →* (F2 ≃+* F2))
    (hcompatR : ∀ a : P, ∀ k : K,
      scalarR (act a k) =
        Units.map (sigmaR a).toMonoidWithZeroHom (scalarR k))
    (hcompat2 : ∀ a : P, ∀ k : K,
      scalar2 (act a k) =
        Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k))
    (a : P) (haR : ∀ x : Fr, sigmaR a x = x ^ r) :
    ∃ i : ℕ, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1] := by
  have hactR : ∀ k : K, act a k = k ^ r := by
    intro k
    apply hscalarR
    rw [hcompatR, map_pow]
    apply Units.ext
    change sigmaR a (scalarR k : Fr) = (scalarR k : Fr) ^ r
    exact haR (scalarR k : Fr)
  rcases finiteField_ringAut_eq_frobenius_pow hfinrank2 (sigma2 a) with
    ⟨i, hi, hi_action⟩
  have hact2 : ∀ k : K, act a k = k ^ (2 ^ i) := by
    intro k
    apply hscalar2
    rw [hcompat2, map_pow]
    apply Units.ext
    change sigma2 a (scalar2 k : F2) = (scalar2 k : F2) ^ (2 ^ i)
    exact hi_action (scalar2 k : F2)
  refine ⟨i, by omega, ?_⟩
  apply modEq_of_equal_power_actions hcardK
  intro k
  exact (hactR k).symm.trans (hact2 k)

/-- End-to-end abstract core of the irreducible branch once Appendix I and
Chapter I have supplied their scalar embeddings and conjugation formulas. -/
private theorem exists_modEq_of_faithful_semilinear_field_models
    {K P Fr F2 : Type*}
    [Group K] [Finite K] [IsCyclic K] [Group P] [Finite P]
    [Field Fr] [Finite Fr] [Field F2] [Finite F2]
    {r p : ℕ} [Fact r.Prime]
    [CharP Fr r] [Algebra (ZMod r) Fr]
    [CharP F2 2] [Algebra (ZMod 2) F2]
    (hcardK : Nat.card K = 2 ^ p - 1)
    (hcardP : Nat.card P = p) (hcardFr : Nat.card Fr = r ^ p)
    (hfinrank2 : Module.finrank (ZMod 2) F2 = p)
    (act : P →* MulAut K) (hact : Function.Injective act)
    (scalarR : K →* Frˣ) (hscalarR : Function.Injective scalarR)
    (sigmaR : P →* (Fr ≃+* Fr))
    (scalar2 : K →* F2ˣ) (hscalar2 : Function.Injective scalar2)
    (sigma2 : P →* (F2 ≃+* F2))
    (hcompatR : ∀ a : P, ∀ k : K,
      scalarR (act a k) =
        Units.map (sigmaR a).toMonoidWithZeroHom (scalarR k))
    (hcompat2 : ∀ a : P, ∀ k : K,
      scalar2 (act a k) =
        Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k)) :
    ∃ i : ℕ, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1] := by
  have hsigmaR : Function.Injective sigmaR :=
    semilinear_aut_injective_of_faithful_scalar_action
      act hact scalarR hscalarR sigmaR hcompatR
  obtain ⟨a, ha⟩ :=
    exists_actor_with_prime_frobenius sigmaR hsigmaR hcardP hcardFr
  exact modEq_of_semilinear_field_models
    hcardK hfinrank2 act scalarR hscalarR sigmaR
      scalar2 hscalar2 sigma2 hcompatR hcompat2 a ha


private theorem claim3_q1_subgroupOf_characteristic
    {G : Type*} [Group G] [Finite G]
    (Q S Q1 : Subgroup G)
    (hS_le : S ≤ Q) (hQ1_le : Q1 ≤ Q)
    (hsyl : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hodd : Odd (Nat.card Q1))
    (hdisj : Disjoint S Q1)
    (hcomm : ∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s)
    (hsup : S ⊔ Q1 = Q) :
    (Q1.subgroupOf Q).Characteristic := by
  let SQ : Subgroup Q := S.subgroupOf Q
  let Q1Q : Subgroup Q := Q1.subgroupOf Q
  have hS_norm : S ≤ Subgroup.normalizer (Q1 : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hc := hcomm s hs q hq
      simpa [hc]
    · intro hq
      let w : G := s * q * s⁻¹
      have hw : w ∈ Q1 := hq
      have hc : s * w = w * s := hcomm s hs w hw
      have hinv : s⁻¹ * w * s = w := by
        calc
          s⁻¹ * w * s = s⁻¹ * (w * s) := by simp [mul_assoc]
          _ = s⁻¹ * (s * w) := by rw [hc]
          _ = w := by simp
      have hqeq : q = w := by
        calc
          q = s⁻¹ * w * s := by dsimp [w]; group
          _ = w := hinv
      exact hqeq.symm ▸ hw
  have hnormal : Q1Q.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [← hsup]
    exact sup_le hS_norm Subgroup.le_normalizer
  let : Q1Q.Normal := hnormal
  have hdisjQ : Disjoint SQ Q1Q := by
    rw [Subgroup.disjoint_def]
    intro x hxS hxQ1
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisj) hxS hxQ1
  have hsupQ : SQ ⊔ Q1Q = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hS_le hQ1_le, hsup]
    exact Subgroup.subgroupOf_self Q
  have hmul : (SQ : Set Q) * (Q1Q : Set Q) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_mul]
    have hx : x ∈ SQ ⊔ Q1Q := by rw [hsupQ]; exact Subgroup.mem_top x
    exact Subgroup.mem_sup_of_normal_right.mp hx
  have hcomp : SQ.IsComplement' Q1Q :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjQ hmul
  obtain ⟨P2, hSeq⟩ := hsyl
  have hSQeq : SQ = (P2 : Subgroup Q) := by
    ext x
    change (x : G) ∈ S ↔ x ∈ (P2 : Subgroup Q)
    rw [hSeq]
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx : y = x := Q.subtype_injective heq
      rw [← hyx]
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hSQcard : Nat.card SQ = 2 ^ (Nat.card Q).factorization 2 := by
    rw [hSQeq]
    exact Sylow.card_eq_multiplicity P2
  have hQ1Qcard : Nat.card Q1Q = Nat.card Q1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card Q1Q) Q1Q.index := by
    rw [hcomp.index_eq_card, hSQcard, hQ1Qcard]
    exact hodd.coprime_two_right.pow_right _
  let pi : Set Nat.Primes := {q | q.val ∣ Nat.card Q1Q}
  have hHall : IsHallSubgroup pi Q1Q := by
    refine isHallSubgroup_of pi Q1Q ?_ ?_
    · intro q hq
      exact hq
    · intro q hqpi hqindex
      have hqone : q.val = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop hqpi hqindex
      exact q.property.ne_one hqone
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact hHall.eq_of_normal (hHall.map_mulAut e)

private theorem claim3_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H) [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (((K : Subgroup H).map H.subtype : Subgroup G) : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem ((K : Subgroup H).map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, by simp⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

private theorem claim3_frobenius_sup_of_prime_complement
    {G : Type*} [Group G] [Finite G]
    (K P : Subgroup G) (p : Nat)
    (hp : Nat.Prime p) (hPcard : Nat.card P = p)
    (hKnormal : (K.subgroupOf (K ⊔ P)).Normal)
    (hKcentral : K ⊓ Subgroup.centralizer (P : Set G) = ⊥)
    (hKne : K ≠ ⊥) :
    IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (K ⊔ P)) (P.subgroupOf (K ⊔ P)) := by
  classical
  let L : Subgroup G := K ⊔ P
  let KL : Subgroup L := K.subgroupOf L
  let PL : Subgroup L := P.subgroupOf L
  have : Fact p.Prime := ⟨hp⟩
  have : IsCyclic P := isCyclic_of_prime_card hPcard
  have hPcent : P ≤ Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : P) ⟨x, hx⟩)
  have hPne : P ≠ ⊥ := by
    intro hP
    apply hp.ne_one
    rw [← hPcard, hP]
    simp
  have hdisj : Disjoint K P := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    have hxbot : x ∈ K ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨hxK, hPcent hxP⟩
    rw [hKcentral] at hxbot
    simpa using hxbot
  have hdisjL : Disjoint KL PL := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxP
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisj) hxK hxP
  have hsupL : KL ⊔ PL = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self L
  let : KL.Normal := by
    simpa [KL, L] using hKnormal
  have hmul : (KL : Set L) * (PL : Set L) = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_mul]
    have hx : x ∈ KL ⊔ PL := by rw [hsupL]; exact Subgroup.mem_top x
    exact Subgroup.mem_sup_of_normal_left.mp hx
  have hcomp : KL.IsComplement' PL :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisjL hmul
  have hmapK : KL.map L.subtype = K := by
    simpa [KL] using
      (Subgroup.map_subgroupOf_eq_of_le (show K ≤ L from le_sup_left))
  have hmapP : PL.map L.subtype = P := by
    simpa [PL] using
      (Subgroup.map_subgroupOf_eq_of_le (show P ≤ L from le_sup_right))
  have hKLne : KL ≠ ⊥ := by
    intro hbot
    apply hKne
    rw [← hmapK, hbot, Subgroup.map_bot]
  have hPLne : PL ≠ ⊥ := by
    intro hbot
    apply hPne
    rw [← hmapP, hbot, Subgroup.map_bot]
  apply (lemma_3_1 KL PL hKLne hPLne (inferInstance : KL.Normal) hcomp).2
  intro x hxne
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hyK : (((y : L) : G)) ∈ K := hy.1
  have hxP : ((((x : PL) : L) : G)) ∈ P := x.property
  let xP : P := ⟨(((x : PL) : L) : G), hxP⟩
  have hxPne : xP ≠ 1 := by
    intro hxPone
    have hxG : ((((x : PL) : L) : G)) = 1 := by
      simpa [xP] using congrArg Subtype.val hxPone
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hxG
  have hycomm :
      Commute (((y : L) : G)) ((((x : PL) : L) : G)) := by
    have hcommL : Commute (y : L) ((x : PL) : L) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    show (((y : L) : G)) * ((((x : PL) : L) : G)) =
      ((((x : PL) : L) : G)) * (((y : L) : G))
    simpa using congrArg (fun z : L => ((z : L) : G)) hcommL.eq
  have hyCP : (((y : L) : G)) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hzP
    let zP : P := ⟨z, hzP⟩
    have hzpow : zP ∈ Subgroup.zpowers xP :=
      mem_zpowers_of_prime_card hPcard hxPne
    rcases Subgroup.mem_zpowers_iff.mp hzpow with ⟨n, hn⟩
    have hnG : ((((x : PL) : L) : G)) ^ n = z := by
      exact congrArg Subtype.val hn
    rw [← hnG]
    exact (hycomm.zpow_right n).eq.symm
  have hybot : (((y : L) : G)) ∈ (⊥ : Subgroup G) := by
    rw [← hKcentral]
    exact ⟨hyK, hyCP⟩
  apply Subtype.ext
  simpa using hybot

private theorem claim3_setup
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : Nat)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    (Q1.subgroupOf Q).Characteristic ∧
      K ⊔ P ≤ Subgroup.normalizer (Q1 : Set G) ∧
        IsFrobeniusGroupWithKernelComplement
          (K.subgroupOf (K ⊔ P)) (P.subgroupOf (K ⊔ P)) := by
  have hQ1char : (Q1.subgroupOf Q).Characteristic :=
    claim3_q1_subgroupOf_characteristic Q S Q1
      hch.section3.section2.S_le_Q hch.section3.section2.Q1_le_Q
      hch.section3.section2.S_sylow_in_Q hch.section3.section2.Q1_odd_order
      hch.section3.section2.S_disjoint_Q1 hch.section3.section2.S_commutes_Q1
      hch.section3.section2.Q_decomp
  let : (Q1.subgroupOf Q).Characteristic := hQ1char
  have hVleD : V ≤ D :=
    proposition_3_V_le_D H D Q K V W Q0 S Q1 t hch.section3.section2
  have hKPleD : K ⊔ P ≤ D :=
    sup_le hch.section3.section2.K_le_D (hch.B1.P_le_V.trans hVleD)
  have hDnormK : D ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      hch.section3.section2.K_le_D).1
        (proposition_2 H D Q K V W Q0 S Q1 t hch.section3.section2).2
  have hKnormal : (K.subgroupOf (K ⊔ P)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hKPleD.trans hDnormK)
  have hKne : K ≠ ⊥ := by
    intro hK
    rcases proposition_1_b_K_nontrivial H D Q K V W Q0 S Q1 t
      hch.section3.section2 with ⟨x, hxK, hxne⟩
    exact hxne (by simpa [hK] using hxK)
  have hfrob :
      IsFrobeniusGroupWithKernelComplement
        (K.subgroupOf (K ⊔ P)) (P.subgroupOf (K ⊔ P)) :=
    claim3_frobenius_sup_of_prime_complement K P p
      hch.B1.p_prime hch.B1.P_card hKnormal
      (claim_1_K_inf_centralizer_P_eq_bot
        H D Q K V W Q0 S Q1 P t s p hch) hKne
  have hHnormQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      hch.section3.section2.hA.A1.Q_le_H).1
        hch.section3.section2.hA.A1.Q_normal_in_H
  have hKPnormQ : K ⊔ P ≤ Subgroup.normalizer (Q : Set G) :=
    hKPleD.trans hch.section3.section2.hA.A1.D_le_H |>.trans hHnormQ
  have hNQleNQ1 :
      Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Q1 : Set G) := by
    simpa [Subgroup.map_subgroupOf_eq_of_le hch.section3.section2.Q1_le_Q] using
      (claim3_normalizer_le_normalizer_map_subtype_of_characteristic
        Q (Q1.subgroupOf Q))
  exact ⟨hQ1char, hKPnormQ.trans hNQleNQ1, hfrob⟩

private theorem claim3_isElementaryAbelian_subgroup
    {M : Type uL} [Group M] {r : ℕ} [Fact r.Prime]
    [IsElementaryAbelian r M] (N : Subgroup M) :
    IsElementaryAbelian r N := by
  refine
    { toIsMulCommutative := by infer_instance
      exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
  intro x
  apply Subtype.ext
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p r M) (x : N)

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem claim3_minimal_invariant_subgroup_representation_irreducible
    {L : Type uL} {M : Type uV}
    [Group L] [Finite L] [Group M] [Finite M]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r M]
    [MulDistribMulAction L M]
    (N : Subgroup M) (hNinv : IsInvariant L M N) (hNne : N ≠ ⊥)
    (hmin : ∀ T : Subgroup M, T.Normal → IsInvariant L M T →
      T ≠ ⊥ → T ≤ N → T = N) :
    letI : IsInvariant L M N := hNinv
    letI : IsElementaryAbelian r N := claim3_isElementaryAbelian_subgroup N
    Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)) := by
  let : IsInvariant L M N := hNinv
  let : IsElementaryAbelian r N := claim3_isElementaryAbelian_subgroup N
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
  let rho := Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)
  change IsSimpleOrder (Subrepresentation rho)
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro S
  let T0 : Subgroup N := S.toSubmodule.toAddSubgroup.toSubgroup'
  have hT0inv : IsInvariant L N T0 := by
    have hmap_mem (a : L) {x : N} (hx : x ∈ T0) : a • x ∈ T0 := by
      change Additive.ofMul (a • x) ∈ S.toSubmodule
      have hx' : Additive.ofMul x ∈ S.toSubmodule := by
        simpa [T0, Submodule.mem_toAddSubgroup] using hx
      have hx'' := S.apply_mem_toSubmodule a hx'
      simpa [rho, Theory.Representation.ofElementaryAbelianAction_apply_ofMul] using hx''
    refine { invariant := ?_ }
    intro a x
    constructor
    · intro hx
      exact hmap_mem a hx
    · intro hx
      have hx' : (a : L)⁻¹ • ((a : L) • x) ∈ T0 := hmap_mem (a : L)⁻¹ hx
      simpa [smul_smul] using hx'
  by_cases hT0bot : T0 = ⊥
  · left
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = (⊥ : Submodule (ZMod r) (Additive N))
    ext x
    have hxT0 : Additive.toMul x ∈ T0 ↔ x ∈ S.toSubmodule := by
      simp [T0]
    rw [← hxT0, hT0bot]
    constructor
    · intro hx
      simpa [hx]
    · intro hx
      change x = 0 at hx
      subst x
      simp
  · right
    let : IsInvariant L N T0 := hT0inv
    let T : Subgroup M := T0.map N.subtype
    have hTnormal : T.Normal := Subgroup.normal_of_isMulCommutative T
    have hTinv : IsInvariant L M T := by
      exact isInvariant_map_subtype (A := L) (G := M) N T0
    have hTne : T ≠ ⊥ := by
      intro hTbot
      apply hT0bot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := T0) (f := N.subtype) N.subtype_injective).1 hTbot
    have hTleN : T ≤ N := Subgroup.map_subtype_le T0
    have hTeq : T = N := hmin T hTnormal hTinv hTne hTleN
    have hT0top : T0 = ⊤ := by
      apply top_unique
      intro n _hn
      have hnT : (n : M) ∈ T := by
        rw [hTeq]
        exact n.property
      rcases hnT with ⟨t, htT0, htn⟩
      have ht_eq : t = n := N.subtype_injective htn
      simpa [ht_eq] using htT0
    apply Subrepresentation.toSubmodule_injective
    ext x
    have hxT0 : Additive.toMul x ∈ T0 ↔ x ∈ S.toSubmodule := by
      simp [T0]
    rw [← hxT0, hT0top]
    constructor
    · intro _hx
      exact Submodule.mem_top
    · intro _hx
      simp


private theorem claim3_exists_minimal_invariant_elementaryAbelian
    {G : Type*} [Group G] [Finite G]
    (L Q1 : Subgroup G) (hLnorm : L ≤ Subgroup.normalizer (Q1 : Set G))
    {r : ℕ} (hr : Nat.Prime r) (hrdiv : r ∣ Nat.card Q1)
    (hnil : Group.IsNilpotent Q1) :
    letI : MulDistribMulAction L Q1 :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer L Q1 hLnorm
    ∃ R : Sylow r Q1, ∃ hRinv : IsInvariant L Q1 (R : Subgroup Q1),
      letI : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
      ∃ M : Subgroup R, ∃ hMinv : IsInvariant L R M,
        letI : IsInvariant L R M := hMinv
        ∃ N : Subgroup M, ∃ _hNinv : IsInvariant L M N,
          IsElementaryAbelian r M ∧ IsElementaryAbelian r N ∧ N ≠ ⊥ ∧
            ∀ T : Subgroup M, T.Normal → IsInvariant L M T →
              T ≠ ⊥ → T ≤ N → T = N := by
  let : MulDistribMulAction L Q1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer L Q1 hLnorm
  let : Fact r.Prime := ⟨hr⟩
  let R : Sylow r Q1 := default
  have hRne : (R : Subgroup Q1) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card (G := Q1) (p := r) R hrdiv
  have hRnormal : (R : Subgroup Q1).Normal := by
    exact Group.IsNilpotent.sylow_normal hnil r R
  have hRchar : (R : Subgroup Q1).Characteristic :=
    Sylow.characteristic_of_normal R hRnormal
  let : (R : Subgroup Q1).Characteristic := hRchar
  have hRinv : IsInvariant L Q1 (R : Subgroup Q1) :=
    isInvariant_of_characteristic (R : Subgroup Q1)
  let : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot (R : Subgroup Q1)).2 hRne
  obtain ⟨M, hMnormal, hMinv, hMne, hMmin⟩ :=
    exists_minimal_normal_isInvariant (G := R) (A := L)
  let : M.Normal := hMnormal
  let : IsInvariant L R M := hMinv
  have hRsolv : Group.IsSolvable R := by
    let : Group.IsNilpotent R := R.isPGroup'.isNilpotent
    infer_instance
  have hMsolv : Group.IsSolvable M := by
    let : Group.IsSolvable R := hRsolv
    infer_instance
  let : Group.IsSolvable M := hMsolv
  obtain ⟨q, hq, hMelemQ⟩ :=
    minimalInvariantNormal_solvable_exists_isElementaryAbelian
      (G := R) (A := L) M hMne hMmin
  have hqr : q = r := by
    have : Fact q.Prime := ⟨hq⟩
    let : IsElementaryAbelian q M := hMelemQ
    have hMr : IsPGroup r M := R.isPGroup'.to_subgroup M
    have hMq : IsPGroup q M := IsElementaryAbelian.isPGroup q M
    obtain ⟨a, ha⟩ := hMr.exists_card_eq
    obtain ⟨b, hb⟩ := hMq.exists_card_eq
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hMne
      apply (Subgroup.eq_bot_iff_card (H := M)).2
      simp [ha, ha0]
    have hrM : r ∣ Nat.card M := by
      rw [ha]
      exact dvd_pow_self r ha0
    have hrq : r ∣ q := by
      apply hr.dvd_of_dvd_pow
      simpa [hb] using hrM
    exact ((Nat.dvd_prime hq).mp hrq).resolve_left hr.ne_one |>.symm
  subst q
  let : IsElementaryAbelian r M := hMelemQ
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot M).2 hMne
  obtain ⟨N, hNnormal, hNinv, hNne, hNmin⟩ :=
    exists_minimal_normal_isInvariant (G := M) (A := L)
  have hNelem : IsElementaryAbelian r N := by
    refine
      { toIsMulCommutative := by infer_instance
        exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p r M) (x : M)
  exact ⟨R, hRinv, M, hMinv, N, hNinv, hMelemQ, hNelem, hNne, hNmin⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
private theorem claim3_K_acts_fixedPointFree
    {G : Type*} [Group G] [Finite G]
    {L K Q Q1 : Subgroup G} [MulDistribMulAction L Q1]
    (_hKleL : K ≤ L) (hQ1leQ : Q1 ≤ Q)
    (haction : ∀ l : L, ∀ q : Q1,
      ((l • q : Q1) : G) = (l : G) * (q : G) * (l : G)⁻¹)
    (hfreeK : ∀ k : G, k ∈ K → k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) ⊓ Q = ⊥)
    {r : ℕ} (R : Sylow r Q1)
    (hRinv : IsInvariant L Q1 (R : Subgroup Q1))
    (M : Subgroup R) (hMinv : IsInvariant L R M)
    (N : Subgroup M) (hNinv : IsInvariant L M N) :
    letI : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
    letI : IsInvariant L R M := hMinv
    letI : IsInvariant L M N := hNinv
    letI : MulDistribMulAction (K.subgroupOf L) N :=
      MulDistribMulAction.compHom N (K.subgroupOf L).subtype
    ∀ a : K.subgroupOf L, a ≠ 1 → ∀ x : N, a • x = x → x = 1 := by
  let : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
  let : IsInvariant L R M := hMinv
  let : IsInvariant L M N := hNinv
  let : MulDistribMulAction (K.subgroupOf L) N :=
    MulDistribMulAction.compHom N (K.subgroupOf L).subtype
  intro a hane x hfix
  let aL : L := a
  have haK : ((aL : L) : G) ∈ K := a.property
  have haGne : ((aL : L) : G) ≠ 1 := by
    intro haone
    apply hane
    apply Subtype.ext
    apply Subtype.ext
    exact haone
  have hfixL : (aL • x : N) = x := hfix
  have hfixQ1 :
      (aL • ((((x : N) : M) : R) : Q1) : Q1) =
        ((((x : N) : M) : R) : Q1) :=
    congrArg (fun y : N => ((((y : N) : M) : R) : Q1)) hfixL
  have hfixG : ((aL : L) : G) * (((((x : N) : M) : R) : Q1) : G) *
      ((aL : L) : G)⁻¹ = (((((x : N) : M) : R) : Q1) : G) :=
    (haction aL ((((x : N) : M) : R) : Q1)).symm.trans
      (congrArg Subtype.val hfixQ1)
  have hxcent : (((((x : N) : M) : R) : Q1) : G) ∈
      Subgroup.centralizer ({((aL : L) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp hfixG).symm
  have hxQ1 : (((((x : N) : M) : R) : Q1) : G) ∈ Q1 :=
    ((((x : N) : M) : R) : Q1).property
  have hxbot : (((((x : N) : M) : R) : Q1) : G) ∈ (⊥ : Subgroup G) := by
    rw [← hfreeK ((aL : L) : G) haK haGne]
    exact ⟨hxcent, hQ1leQ hxQ1⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  simpa using hxbot

private theorem claim3_ringChar_not_dvd_actor_card_of_fixedPointFree
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    {r : ℕ} (hr : Nat.Prime r) [IsElementaryAbelian r N]
    [MulDistribMulAction A N]
    (hNne : Nontrivial N)
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x = 1) :
    ¬ ringChar (ZMod r) ∣ Nat.card A := by
  let : Fact r.Prime := ⟨hr⟩
  let : Nontrivial N := hNne
  have hAdvd : Nat.card A ∣ Nat.card N - 1 :=
    Section6.natCard_actor_dvd_group_card_sub_one hfree
  have hNp : IsPGroup r N := IsElementaryAbelian.isPGroup r N
  obtain ⟨n, hNcard⟩ := hNp.exists_card_eq
  have hn : n ≠ 0 := by
    intro hn
    have hcardOne : Nat.card N = 1 := by simp [hNcard, hn]
    exact not_subsingleton_iff_nontrivial.mpr hNne
      (Nat.card_eq_one_iff_unique.mp hcardOne).1
  have hrN : r ∣ Nat.card N := by
    rw [hNcard]
    exact dvd_pow_self r hn
  rw [ringChar.eq (ZMod r) r]
  intro hrA
  have hrNm1 : r ∣ Nat.card N - 1 := hrA.trans hAdvd
  have hcardPos : 0 < Nat.card N := Nat.card_pos
  have hcop : Nat.Coprime (Nat.card N) (Nat.card N - 1) :=
    (Nat.coprime_self_sub_right (by omega : 1 ≤ Nat.card N)).2
      (Nat.coprime_one_right (Nat.card N))
  exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrN hrNm1)

private theorem claim3_fixedPointSubgroup_eq_bot_of_fixedPointFree
    {A N : Type*} [Group A] [Nontrivial A] [Group N]
    [MulDistribMulAction A N]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x = 1) :
    fixedPointSubgroup A N = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hx
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  exact hfree a ha x (hx a)

/-- The Isaacs dimension formula forces the complement fixed subgroup to be nontrivial. -/
private theorem claim3_fixedPointSubgroup_nontrivial_of_dimension_formula
    {L N : Type*} [Group L] [Finite L] [Group N] [Finite N]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r N]
    [MulDistribMulAction L N]
    (P : Subgroup L) (hNne : Nontrivial N)
    (hformula :
      let rho := Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)
      Module.finrank (ZMod r) (Additive N) =
        Nat.card P * Module.finrank (ZMod r) (rho.fixedSubspace P)) :
    letI : MulDistribMulAction P N :=
      MulDistribMulAction.compHom N P.subtype
    Nontrivial (fixedPointSubgroup P N) := by
  let : MulDistribMulAction P N :=
    MulDistribMulAction.compHom N P.subtype
  let : Nontrivial N := hNne
  let rho := Theory.Representation.ofElementaryAbelianAction
    (A := L) (G := N) (p := r)
  by_contra hnon
  have : Subsingleton (fixedPointSubgroup P N) :=
    not_nontrivial_iff_subsingleton.mp hnon
  have hfix : fixedPointSubgroup P N = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x _hx
    exact congrArg Subtype.val
      (Subsingleton.elim (⟨x, _hx⟩ : fixedPointSubgroup P N) 1)
  have hfixedSpace : rho.fixedSubspace P = ⊥ :=
    theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot P hfix
  have hdim0 : Module.finrank (ZMod r) (rho.fixedSubspace P) = 0 := by
    rw [hfixedSpace]
    simp
  have hNpos : 0 < Module.finrank (ZMod r) (Additive N) :=
    Module.finrank_pos
  rw [hformula, hdim0] at hNpos
  simp at hNpos

/-- Prime cardinality of the fixed subgroup is equivalent to a one-dimensional fixed space. -/
private theorem claim3_fixedSubspace_finrank_eq_one_of_fixedPointSubgroup_card_eq_prime
    {L N : Type uFix} [Group L] [Group N] [Finite N]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r N]
    [MulDistribMulAction L N]
    (P : Subgroup L)
    (hcard :
      letI : MulDistribMulAction P N :=
        MulDistribMulAction.compHom N P.subtype
      Nat.card (fixedPointSubgroup P N) = r) :
    let rho := Theory.Representation.ofElementaryAbelianAction
      (A := L) (G := N) (p := r)
    Module.finrank (ZMod r) (rho.fixedSubspace P) = 1 := by
  classical
  let : MulDistribMulAction P N :=
    MulDistribMulAction.compHom N P.subtype
  let rho := Theory.Representation.ofElementaryAbelianAction
    (A := L) (G := N) (p := r)
  let e := Wielandt.fixedPointSubgroup_fixedSubspaceEquiv
    (A := L) (M := N) (p := r) P
  have hsubcard : Nat.card (rho.fixedSubspace P) =
      Nat.card (fixedPointSubgroup P N) := by
    calc
      Nat.card (rho.fixedSubspace P) =
          Nat.card (Additive (fixedPointSubgroup P N)) := Nat.card_congr e
      _ = Nat.card (fixedPointSubgroup P N) :=
        Nat.card_congr Additive.toMul
  have hnat := Module.natCard_eq_pow_finrank
    (K := ZMod r) (V := rho.fixedSubspace P)
  have hpow : r ^ Module.finrank (ZMod r) (rho.fixedSubspace P) = r ^ 1 := by
    calc
      r ^ Module.finrank (ZMod r) (rho.fixedSubspace P) =
          Nat.card (rho.fixedSubspace P) := by
        simpa [ZMod.card] using hnat.symm
      _ = Nat.card (fixedPointSubgroup P N) := hsubcard
      _ = r := hcard
      _ = r ^ 1 := by simp
  exact Nat.pow_right_injective (Fact.out : Nat.Prime r).one_lt hpow

set_option backward.isDefEq.respectTransparency false in
private theorem claim3_isaacs_dimension_formula
    {L N : Type*} [Group L] [Finite L] [Group N] [Finite N]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r N]
    [MulDistribMulAction L N]
    (K P : Subgroup L)
    (hfrob : IsFrobeniusGroupWithKernelComplement K P)
    (hchar : ¬ ringChar (ZMod r) ∣ Nat.card K)
    (hKfix :
      letI : MulDistribMulAction K N := MulDistribMulAction.compHom N K.subtype
      fixedPointSubgroup K N = ⊥) :
    let rho := Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)
    Module.finrank (ZMod r) (Additive N) =
      Nat.card P * Module.finrank (ZMod r) (rho.fixedSubspace P) := by
  let rho := Theory.Representation.ofElementaryAbelianAction (A := L) (G := N) (p := r)
  let : FiniteDimensional (ZMod r) (Additive N) := Module.Finite.of_finite
  have hfixedK : rho.fixedSubspace K = ⊥ :=
    theorem_3_7_fixedSubspace_eq_bot_of_fixedPointSubgroup_eq_bot K hKfix
  have hdim :=
    (BenderSuzuki.External.Isaacs.XV.isaacs_theorem_15_16
      K P rho hfrob hchar hfixedK).2 (⊥ : Subgroup P)
  let rhoP : Representation (ZMod r) P (Additive N) := rho.comp P.subtype
  have hbot : rhoP.fixedSubspace (⊥ : Subgroup P) = ⊤ := by
    apply top_unique
    intro x _hx
    change ∀ h : (⊥ : Subgroup P), rhoP h x = x
    intro h
    have hh : (h : P) = 1 := Subgroup.mem_bot.mp h.property
    simp [hh]
  change Module.finrank (ZMod r) ↥(rhoP.fixedSubspace (⊥ : Subgroup P)) = _ at hdim
  rw [hbot] at hdim
  simpa [rho] using hdim

private theorem chapter2_claim3_not_dvd_mersenne_of_modEq
    {p r i : ℕ} (hp : Nat.Prime p) (_hi : i ≤ p - 1)
    (hr : Nat.Prime r) (hmod : r ≡ 2 ^ i [MOD 2 ^ p - 1]) :
    ¬ r ∣ 2 ^ p - 1 := by
  intro hrdiv
  have hrpow : r ∣ 2 ^ i :=
    (hmod.dvd_iff hrdiv).mp (dvd_refl r)
  have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow hrpow
  have hre : r = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hr2 |>.resolve_left hr.ne_one
  have hp0 : 0 < p := hp.pos
  have hpow_eq : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
    omega
  subst r
  rw [hpow_eq] at hrdiv
  exact Nat.two_not_dvd_two_mul_sub_one (pow_pos (by omega) _) hrdiv

private theorem chapter2_claim3_ne_characteristic_of_modEq
    {p r i : ℕ} (hp : Nat.Prime p) (hr : Nat.Prime r) (hrodd : Odd r)
    (hi : i ≤ p - 1) (hmod : r ≡ 2 ^ i [MOD 2 ^ p - 1]) :
    r ≠ p := by
  intro hrp
  subst r
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    subst p
    rcases hrodd with ⟨k, hk⟩
    omega
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : 3 ≤ p := by omega
  have aux : ∀ n : ℕ, 3 ≤ n → n ≤ 2 ^ (n - 1) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        rw [show n + 1 - 1 = n by omega]
        have hpos : 0 < 2 ^ (n - 1) := pow_pos (by omega) _
        have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
          conv_lhs => rw [show n = (n - 1) + 1 by omega]
          rw [pow_succ]
          omega
        rw [hpow]
        omega
  have hp_le_half : p ≤ 2 ^ (p - 1) := aux p hp3
  have hhalf_pos : 0 < 2 ^ (p - 1) := pow_pos (by omega) _
  have hpow_eq : 2 ^ p = 2 * 2 ^ (p - 1) := by
    conv_lhs => rw [show p = (p - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have hp_lt : p < 2 ^ p - 1 := by omega
  have hi_pow : 2 ^ i ≤ 2 ^ (p - 1) :=
    pow_le_pow_right₀ (by omega) hi
  have hi_lt : 2 ^ i < 2 ^ p - 1 := by omega
  have hp_le_i : p ≤ 2 ^ i :=
    hmod.le_of_lt_add (hp_lt.trans_le (Nat.le_add_left _ _))
  have hi_le_p : 2 ^ i ≤ p :=
    hmod.symm.le_of_lt_add (hi_lt.trans_le (Nat.le_add_left _ _))
  have heq : 2 ^ i = p := Nat.le_antisymm hi_le_p hp_le_i
  have hbase := (hp.pow_eq_iff).mp heq
  exact hp_ne_two hbase.1.symm

private theorem claim3_card_eq_mul_of_characteristic_decomposition
    {G : Type*} [Group G] [Finite G]
    (Q S Q1 : Subgroup G) (hSle : S ≤ Q) (hQ1le : Q1 ≤ Q)
    [(Q1.subgroupOf Q).Characteristic]
    (hdisj : Disjoint S Q1) (hsup : S ⊔ Q1 = Q) :
    Nat.card Q = Nat.card S * Nat.card Q1 := by
  let SQ : Subgroup Q := S.subgroupOf Q
  let Q1Q : Subgroup Q := Q1.subgroupOf Q
  let : Q1Q.Normal := by infer_instance
  have hdisjQ : Disjoint Q1Q SQ := by
    rw [Subgroup.disjoint_def]
    intro x hxQ1 hxS
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisj) hxS hxQ1
  have hsupQ : Q1Q ⊔ SQ = ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup hSle hQ1le, hsup]
    exact Subgroup.subgroupOf_self Q
  have hcomp : Q1Q.IsComplement' SQ :=
    isComplement'_of_disjoint_sup_eq_top_of_normal Q1Q SQ hdisjQ hsupQ
  have hcard := hcomp.card_mul_card
  simpa [Q1Q, SQ, natCard_subgroupOf_eq Q1 Q hQ1le,
    natCard_subgroupOf_eq S Q hSle, Nat.mul_comm] using hcard.symm

private theorem claim3_card_KP_eq_of_frobenius
    {G : Type*} [Group G] [Finite G]
    (K P : Subgroup G)
    (hfrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (K ⊔ P : Subgroup G))
      (P.subgroupOf (K ⊔ P : Subgroup G))) :
    Nat.card (K ⊔ P : Subgroup G) = Nat.card K * Nat.card P := by
  have hcard := hfrob.isComplement'.card_mul_card
  simpa [natCard_subgroupOf_eq K (K ⊔ P) le_sup_left,
    natCard_subgroupOf_eq P (K ⊔ P) le_sup_right] using hcard.symm

private theorem claim3_S_card_power_two
    {G : Type*} [Group G] [Finite G]
    (Q S : Subgroup G)
    (hsyl : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype) :
    ∃ n : ℕ, Nat.card S = 2 ^ n := by
  obtain ⟨P2, rfl⟩ := hsyl
  refine ⟨(Nat.card Q).factorization 2, ?_⟩
  calc
    Nat.card ((P2 : Subgroup Q).map Q.subtype) = Nat.card (P2 : Subgroup Q) :=
      Subgroup.card_map_of_injective (K := (P2 : Subgroup Q))
        (f := Q.subtype) Q.subtype_injective
    _ = 2 ^ (Nat.card Q).factorization 2 := Sylow.card_eq_multiplicity P2

private theorem claim3_coprime_of_card_data
    {q l s q1 p : ℕ}
    (hp : Nat.Prime p) (hpodd : Odd p)
    (hq : q = s * q1) (hl : l = (2 ^ p - 1) * p)
    (hs : ∃ n : ℕ, s = 2 ^ n)
    (hcong : ∀ r : ℕ, Nat.Prime r → r ∣ q1 →
      (∃ i : ℕ, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1]) ∧ r ≠ p) :
    Nat.Coprime q l := by
  apply Nat.coprime_of_dvd
  intro r hr hrq hrl
  rw [hq] at hrq
  rw [hl] at hrl
  rcases hr.dvd_mul.mp hrq with hrs | hrq1
  · rcases hs with ⟨n, rfl⟩
    have hr2 : r ∣ 2 := hr.dvd_of_dvd_pow hrs
    have hre : r = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hr2 |>.resolve_left hr.ne_one
    subst r
    rcases Nat.prime_two.dvd_mul.mp hrl with hM | hpdiv
    · have hp0 : 0 < p := hp.pos
      have hpow_eq : 2 ^ p = 2 * 2 ^ (p - 1) := by
        conv_lhs => rw [show p = (p - 1) + 1 by omega]
        rw [pow_succ]
        omega
      rw [hpow_eq] at hM
      exact Nat.two_not_dvd_two_mul_sub_one (pow_pos (by omega) _) hM
    · rcases hpodd with ⟨k, hk⟩
      rcases hpdiv with ⟨m, hm⟩
      omega
  · rcases hcong r hr hrq1 with ⟨⟨i, hi, hmod⟩, hrnep⟩
    rcases hr.dvd_mul.mp hrl with hM | hpdiv
    · exact chapter2_claim3_not_dvd_mersenne_of_modEq hp hi hr hmod hM
    · have hre : r = p :=
        (Nat.dvd_prime hp).mp hpdiv |>.resolve_left hr.ne_one
      exact hrnep hre

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Complete the irreducible branch once the binary field model and the
faithful direct-conjugation action have been supplied. -/
private theorem claim3_irreducible_semilinear_core
    {r p : Nat} [Fact r.Prime] (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrodd : Odd r)
    {L N F2 : Type*}
    [Group L] [Finite L] [Group N] [Finite N] [Nontrivial N]
    [IsElementaryAbelian r N] [MulDistribMulAction L N]
    [Field F2] [Finite F2] [CharP F2 2] [Algebra (ZMod 2) F2]
    (K P : Subgroup L) [K.Normal] [IsCyclic K] [FaithfulSMul K N]
    (hIrrK : Representation.IsIrreducible
      ((Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)).comp K.subtype))
    (act : P →* MulAut K) (hact : Function.Injective act)
    (hact_coe : ∀ (a : P) (k : K),
      (((act a) k : K) : L) = (a : L) * (k : L) * (a : L)⁻¹)
    (hNdim : Module.finrank (ZMod r) (Additive N) = p)
    (hKcard : Nat.card K = 2 ^ p - 1) (hPcard : Nat.card P = p)
    (hfinrank2 : Module.finrank (ZMod 2) F2 = p)
    (scalar2 : K →* F2ˣ) (hscalar2 : Function.Injective scalar2)
    (sigma2 : P →* (F2 ≃+* F2))
    (hcompat2 : ∀ a : P, ∀ k : K,
      scalar2 (act a k) =
        Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k)) :
    (∃ i : Nat, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1]) ∧ r ≠ p := by
  let T : Subgroup K := ⊤
  let : Representation.IsIrreducible
      (AppendixIRepresentationOfT (p := r) (E := N) T) := by
    let rhoK : Representation (ZMod r) K (Additive N) :=
      Theory.Representation.ofElementaryAbelianAction (A := K) (G := N) (p := r)
    have hrhoK : rhoK =
        (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)).comp K.subtype := by
      ext k x
      simp only [rhoK, MonoidHom.comp_apply,
        Theory.Representation.ofElementaryAbelianAction_apply]
      rfl
    have hIrrK' : Representation.IsIrreducible rhoK := by
      rw [hrhoK]
      exact hIrrK
    have htop_surjective : Function.Surjective T.subtype := by
      intro k
      exact ⟨⟨k, Subgroup.mem_top k⟩, rfl⟩
    have htopIrr := Section6.representation_isIrreducible_comp_surjective
      rhoK T.subtype htop_surjective hIrrK'
    have htopRep : AppendixIRepresentationOfT (p := r) (E := N) T =
        rhoK.comp T.subtype := by
      ext k x
      simp only [AppendixIRepresentationOfT, rhoK, MonoidHom.comp_apply,
        Theory.Representation.ofElementaryAbelianAction_apply]
      rfl
    rw [htopRep]
    exact htopIrr
  let rhoT := AppendixIRepresentationOfT (p := r) (E := N) T
  let : FiniteDimensional (ZMod r) (Additive N) := Module.Finite.of_finite
  let : Field (AppendixIEndT (p := r) (E := N) T) := endField_field rhoT
  let : Finite (AppendixIEndT (p := r) (E := N) T) := endField_finite rhoT
  let : Module (AppendixIEndT (p := r) (E := N) T) (Additive N) :=
    endFieldModule rhoT
  let Fr := AppendixIFpT (p := r) (E := N) T
  let : Field Fr := (Finite.isField_of_domain Fr).toField
  let : Module Fr (Additive N) :=
    Module.compHom (Additive N) Fr.val.toRingHom
  let : CharP Fr r := charP_of_injective_algebraMap' (ZMod r) r
  have hscalarPackage := claim3_appendixI_scalar_adapter_KP
    K P act hact_coe hNdim
  obtain ⟨scalarR, hFrCard, hscalarR,
    hscalarSet_closure, hscalar_conj⟩ := hscalarPackage
  have hscalar_conj' : ∀ (a : P) (k : K) (x : Additive N),
      (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (a : L) ((scalarR k : Fr) • x) =
        (scalarR ((act a) k) : Fr) •
          (Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) x := by
    intro a k x
    change
      (Theory.Representation.ofElementaryAbelianAction
          (A := L) (G := N) (p := r)) (a : L) ((scalarR k : Fr).1 x) =
        (scalarR ((act a) k) : Fr).1
          ((Theory.Representation.ofElementaryAbelianAction
            (A := L) (G := N) (p := r)) (a : L) x)
    exact hscalar_conj a k x
  have hNcard : Nat.card (Additive N) = r ^ p := by
    let : FiniteDimensional (ZMod r) (Additive N) := Module.Finite.of_finite
    have hcard := Module.natCard_eq_pow_finrank
      (K := ZMod r) (V := Additive N)
    simpa [hNdim] using hcard
  obtain ⟨sigmaR, hcompatR⟩ := claim3_appendixI_sigma_adapter_KP
    K P act hact hact_coe scalarR (hFrCard.trans hNcard.symm)
      hscalarSet_closure hscalar_conj'
  obtain ⟨i, hi, hmod⟩ := exists_modEq_of_faithful_semilinear_field_models
    hKcard hPcard hFrCard hfinrank2 act hact scalarR hscalarR sigmaR
      scalar2 hscalar2 sigma2 hcompatR hcompat2
  exact ⟨⟨i, hi, hmod⟩,
    chapter2_claim3_ne_characteristic_of_modEq hp hr hrodd hi hmod⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- Package the Chapter-I binary field model for a transported copy of `K`
and an arbitrary actor mapping into `P ≤ V`. -/
private theorem claim3_chapterI_field_model
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t : G) (p : Nat)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨
                (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P2 : Sylow 2 Q,
                      S = (P2 : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                            s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q))
    (_hP_le_V : P ≤ V) (hQ0card : Nat.card Q0 = 2 ^ p)
    {K0 P0 : Type*} [Group K0] [Group P0]
    (kToK : K0 →* K) (hkToK : Function.Injective kToK)
    (pToV : P0 →* V) (act : P0 →* MulAut K0)
    (hact : ∀ a : P0, ∀ k : K0,
      (((kToK (act a k) : K) : G)) =
        ((pToV a : V) : G) * ((kToK k : K) : G) *
          ((pToV a : V) : G)⁻¹) :
    ∃ (n : Nat) (_hn : n ≠ 0),
      let F2 : Type := GaloisField 2 n
      ∃ (scalar2 : K0 →* F2ˣ) (sigma2 : P0 →* (F2 ≃+* F2)),
        Module.finrank (ZMod 2) F2 = p ∧
          Function.Injective scalar2 ∧
            ∀ a : P0, ∀ k : K0,
              scalar2 (act a k) =
                Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k) := by
  have hVleD : V ≤ D :=
    proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec
  rcases proposition_3_field_model_with_q0_card
      H D Q K V W Q0 S Q1 t hsec with
    ⟨n, hn, _hQ0powN, A, hWV, hWD, rhoD, rhoMul, rhoAut,
      _q0_add, k_units, vmodW_aut, modelIso, hmodelCard,
      _hrhoMul, _hrhoAut_inl, hrhoAut_inr, _hrhoD, _hmodel_q,
      hmodel_k, hmodel_v, _hk_right, _hv_right⟩
  let : (W.subgroupOf V).Normal := hWV
  let : (W.subgroupOf D).Normal := hWD
  let F2 : Type := GaloisField 2 n
  let scalar2 : K0 →* F2ˣ :=
    k_units.toMonoidHom.comp kToK
  let sigma2 : P0 →* (F2 ≃+* F2) :=
    A.subtype.comp
      (vmodW_aut.toMonoidHom.comp
        ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV))
  have hbinary := claim3_chapterI_semilinear_adapter
    D K V W Q0 A hsec.K_le_D hVleD rhoD rhoMul rhoAut
      k_units vmodW_aut modelIso hrhoAut_inr hmodel_k hmodel_v
      kToK hkToK pToV act hact
  change Function.Injective scalar2 ∧
    ∀ a : P0, ∀ k : K0,
      scalar2 (act a k) =
        Units.map (sigma2 a).toMonoidWithZeroHom (scalar2 k) at hbinary
  refine ⟨n, hn, scalar2, sigma2, ?_, hbinary⟩
  exact claim3_binary_galoisField_finrank_eq_of_q0_card
    n p hn hmodelCard hQ0card

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/-- The irreducible Clifford branch of Claim (3), isolated with only the
forward Chapter-I data and the Frobenius action on the minimal layer. -/
private theorem chapter2_claim3_irreducible_branch
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega] [Finite Omega]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t : G) (p : Nat)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Omega H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧
      _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨
                (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P2 : Sylow 2 Q,
                      S = (P2 : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 →
                            s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q))
    (hP_le_V : P ≤ V) (hP_card : Nat.card P = p) (hp : Nat.Prime p)
    (hQ0card : Nat.card Q0 = 2 ^ p) (hKcard : Nat.card K = 2 ^ p - 1)
    {r : Nat} [Fact r.Prime] (hr : Nat.Prime r) (hrodd : Odd r)
    {N : Type*} [Group N] [Finite N] [Nontrivial N]
    [IsElementaryAbelian r N]
    [MulDistribMulAction ↥(K ⊔ P : Subgroup G) N]
    (hKfree :
      let Ksub : Subgroup ↥(K ⊔ P : Subgroup G) :=
        K.subgroupOf (K ⊔ P : Subgroup G)
      letI : MulDistribMulAction Ksub N :=
        MulDistribMulAction.compHom N Ksub.subtype
      ∀ a : Ksub, a ≠ 1 → ∀ x : N, a • x = x → x = 1)
    (hfrob : IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf (K ⊔ P : Subgroup G))
      (P.subgroupOf (K ⊔ P : Subgroup G)))
    (hNdim : Module.finrank (ZMod r) (Additive N) = p)
    (hIrrK : Representation.IsIrreducible
      ((Theory.Representation.ofElementaryAbelianAction
        (A := ↥(K ⊔ P : Subgroup G)) (G := N) (p := r)).comp
          (K.subgroupOf (K ⊔ P : Subgroup G)).subtype)) :
    (∃ i : Nat, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1]) ∧ r ≠ p := by
  classical
  let L : Subgroup G := K ⊔ P
  let Ksub : Subgroup L := K.subgroupOf L
  let Psub : Subgroup L := P.subgroupOf L
  have hfrob' : IsFrobeniusGroupWithKernelComplement Ksub Psub := by
    simpa [Ksub, Psub, L] using hfrob
  let : Ksub.Normal := hfrob'.normal
  let : Nontrivial Ksub :=
    (Subgroup.nontrivial_iff_ne_bot Ksub).2 hfrob'.kernel_ne_bot
  let eK : Ksub ≃* K :=
    Subgroup.subgroupOfEquivOfLe (show K ≤ L from le_sup_left)
  let eP : Psub ≃* P :=
    Subgroup.subgroupOfEquivOfLe (show P ≤ L from le_sup_right)
  let : IsCyclic Ksub :=
    eK.isCyclic.mpr
      (proposition_2 H D Q K V W Q0 S Q1 t hsec).1
  let : MulDistribMulAction Ksub N :=
    MulDistribMulAction.compHom N Ksub.subtype
  have hKfree' : ∀ a : Ksub, a ≠ 1 → ∀ x : N, a • x = x → x = 1 := by
    simpa [Ksub, L] using hKfree
  let : FaithfulSMul Ksub N :=
    { eq_of_smul_eq_smul := by
        intro a b hab
        apply mul_inv_eq_one.mp
        by_contra hc
        obtain ⟨x, hx⟩ := exists_ne (1 : N)
        apply hx
        apply hKfree' (a * b⁻¹) hc x
        calc
          (a * b⁻¹) • x = a • (b⁻¹ • x) := mul_smul a b⁻¹ x
          _ = b • (b⁻¹ • x) := hab (b⁻¹ • x)
          _ = x := smul_inv_smul b x }
  have hPnormK : Psub ≤ Subgroup.normalizer (Ksub : Set L) :=
    Subgroup.le_normalizer_of_normal (H := Ksub)
  let : MulDistribMulAction Psub Ksub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer Psub Ksub hPnormK
  let act : Psub →* MulAut Ksub :=
    MulDistribMulAction.toMulAut Psub Ksub
  have hact_coe : ∀ (a : Psub) (k : Ksub),
      (((act a) k : Ksub) : L) = (a : L) * (k : L) * (a : L)⁻¹ := by
    intro a k
    change ((a • k : Ksub) : L) = (a : L) * (k : L) * (a : L)⁻¹
    exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
      Psub Ksub hPnormK a k
  have hregular : ActsRegularly Psub Ksub :=
    IsFrobeniusGroupWithKernelComplement.regular_conj_action
      (K := Ksub) (R := Psub) hfrob'
  have hact_injective : Function.Injective act := by
    apply (MonoidHom.ker_eq_bot_iff act).1
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have hacta : act a = 1 := ha
    by_contra hane
    obtain ⟨k, hk⟩ := exists_ne (1 : Ksub)
    have hfix : a • k = k := by
      change act a k = k
      rw [hacta]
      rfl
    have hkfixed : k ∈ fixedPointSubgroup (Subgroup.zpowers a) Ksub := by
      rw [fixedPointSubgroup, FixedPoints.mem_subgroup]
      intro z
      exact smul_eq_self_of_mem_zpowers z.2 hfix
    rw [hregular a hane] at hkfixed
    exact hk (by simpa using hkfixed)
  let pToV : Psub →* V :=
    (Subgroup.inclusion hP_le_V).comp eP.toMonoidHom
  have hactG : ∀ a : Psub, ∀ k : Ksub,
      (((eK (act a k) : K) : G)) =
        ((pToV a : V) : G) * ((eK k : K) : G) *
          ((pToV a : V) : G)⁻¹ := by
    intro a k
    have hconj :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
        Psub Ksub hPnormK a k
    have hconjG := congrArg L.subtype hconj
    change (((a • k : Ksub) : L) : G) =
      ((a : L) : G) * ((k : L) : G) * ((a : L) : G)⁻¹
    exact hconjG
  rcases claim3_chapterI_field_model
      H D Q K V W Q0 S Q1 P t p hsec hP_le_V hQ0card
      eK.toMonoidHom eK.injective pToV act hactG with
    ⟨n, _hn, scalar2, sigma2, hfinrank2, hscalar2, hcompat2⟩
  let F2 : Type := GaloisField 2 n
  have hKsub_card : Nat.card Ksub = 2 ^ p - 1 := by
    rw [natCard_subgroupOf_eq K L (show K ≤ L from le_sup_left)]
    exact hKcard
  have hPsub_card : Nat.card Psub = p := by
    rw [natCard_subgroupOf_eq P L (show P ≤ L from le_sup_right)]
    exact hP_card
  have hIrrK' : Representation.IsIrreducible
      ((Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)).comp Ksub.subtype) := by
    simpa [Ksub, L] using hIrrK
  exact claim3_irreducible_semilinear_core hr hp hrodd Ksub Psub hIrrK'
    act hact_injective hact_coe hNdim hKsub_card hPsub_card
      hfinrank2 scalar2 hscalar2 sigma2 hcompat2

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option backward.isDefEq.respectTransparency false in
/- Claim (3): prime-divisor congruence for `Q1`. -/
private theorem chapter2_claim3_prime_divisors_Q1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    ∀ r : ℕ, Nat.Prime r → r ∣ Nat.card Q1 →
      (∃ i : ℕ, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1]) ∧ r ≠ p := by
  intro r hr hrdiv
  let : Fact r.Prime := ⟨hr⟩
  let L : Subgroup G := K ⊔ P
  have hsetup := claim3_setup H D Q K V W Q0 S Q1 P t s p hch
  let : MulDistribMulAction L Q1 :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer L Q1 hsetup.2.1
  have hnilQ : Group.IsNilpotent Q :=
    PFchapter1section2.proposition_1_b
      H D Q K V W Q0 S Q1 t hch.section3.section2
  let : Group.IsNilpotent Q := hnilQ
  have hnilQ1 : Group.IsNilpotent Q1 := by
    let Q1Q : Subgroup Q := Q1.subgroupOf Q
    let : Group.IsNilpotent Q1Q := Subgroup.isNilpotent Q1Q
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hch.section3.section2.Q1_le_Q)
  obtain ⟨R, hRinv, M, hMinv, N, hNinv, hMelem, hNelem, hNne, hNmin⟩ :=
    claim3_exists_minimal_invariant_elementaryAbelian
      L Q1 hsetup.2.1 hr hrdiv hnilQ1
  let : IsInvariant L Q1 (R : Subgroup Q1) := hRinv
  let : IsInvariant L R M := hMinv
  let : IsInvariant L M N := hNinv
  let : IsElementaryAbelian r M := hMelem
  let : IsElementaryAbelian r N := hNelem
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).2 hNne
  let Ksub : Subgroup L := K.subgroupOf L
  let Psub : Subgroup L := P.subgroupOf L
  let : Ksub.Normal := hsetup.2.2.normal
  let : Nontrivial Ksub :=
    (Subgroup.nontrivial_iff_ne_bot Ksub).2 hsetup.2.2.kernel_ne_bot
  let : MulDistribMulAction Ksub N :=
    MulDistribMulAction.compHom N Ksub.subtype
  let : MulDistribMulAction Psub N :=
    MulDistribMulAction.compHom N Psub.subtype
  have haction (l : L) (q : Q1) :
      ((l • q : Q1) : G) = (l : G) * (q : G) * (l : G)⁻¹ :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
      L Q1 hsetup.2.1 l q
  have hKfree : ∀ a : Ksub, a ≠ 1 →
      ∀ x : N, a • x = x → x = 1 :=
    claim3_K_acts_fixedPointFree
      (L := L) (K := K) (Q := Q) (Q1 := Q1) le_sup_left
      hch.section3.section2.Q1_le_Q haction
      (PFchapter1section2.proposition_1_a
        H D Q K V W Q0 S Q1 t hch.section3.section2)
      R hRinv M hMinv N hNinv
  have hchar : ¬ ringChar (ZMod r) ∣ Nat.card Ksub :=
    claim3_ringChar_not_dvd_actor_card_of_fixedPointFree
      hr (show Nontrivial N from inferInstance) hKfree
  have hKfix : fixedPointSubgroup Ksub N = ⊥ :=
    claim3_fixedPointSubgroup_eq_bot_of_fixedPointFree hKfree
  have hformula :
      let rho := Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)
      Module.finrank (ZMod r) (Additive N) =
        Nat.card Psub * Module.finrank (ZMod r) (rho.fixedSubspace Psub) :=
    claim3_isaacs_dimension_formula Ksub Psub hsetup.2.2 hchar hKfix
  have hfixed_nontrivial :
      letI : MulDistribMulAction Psub N :=
        MulDistribMulAction.compHom N Psub.subtype
      Nontrivial (fixedPointSubgroup Psub N) :=
    claim3_fixedPointSubgroup_nontrivial_of_dimension_formula
      Psub (show Nontrivial N from inferInstance) hformula
  have hrodd : Odd r :=
    hch.section3.section2.Q1_odd_order.of_dvd_nat hrdiv
  have hr_two : r ≠ 2 := by
    intro hre
    subst r
    rcases hrodd with ⟨k, hk⟩
    omega
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type _ := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
  let : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨hNcore, hnormal, quotientAction, hsmul, hAbar,
      F, hF, hFfinite, hFnontrivial, _unitEquiv, hPO, _hcharacteristic⟩
  let : RightNearField F := hF
  let : Finite F := hFfinite
  let : Nontrivial F := hFnontrivial
  let : core.Normal := hnormal
  have hcore_le_DP : core ≤ DP := by
    change pointStabilizerCore C OmegaP ≤ DP
    rw [← hNcore]
    intro x hx
    exact hx.1.1
  have hfixedCard :
      letI : MulDistribMulAction Psub N :=
        MulDistribMulAction.compHom N Psub.subtype
      Nat.card (fixedPointSubgroup Psub N) = r :=
    claim3_fixedPointSubgroup_card_eq_prime_of_propositionOneConclusion
      D Q Q1 P L le_sup_right hch.section3.section2.Q1_le_Q
      hch.section3.section2.hA.A1.Q_disjoint_D haction
      R hRinv M hMinv N hNinv hNelem core hcore_le_DP
      (HP.map (QuotientGroup.mk' core))
      (DP.map (QuotientGroup.mk' core)) hPO hr_two hfixed_nontrivial
  have hfixedDim :
      let rho := Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)
      Module.finrank (ZMod r) (rho.fixedSubspace Psub) = 1 :=
    claim3_fixedSubspace_finrank_eq_one_of_fixedPointSubgroup_card_eq_prime
      Psub hfixedCard
  have hNdim : Module.finrank (ZMod r) (Additive N) = p := by
    calc
      Module.finrank (ZMod r) (Additive N) =
          Nat.card Psub *
            Module.finrank (ZMod r)
              ((Theory.Representation.ofElementaryAbelianAction
                (A := L) (G := N) (p := r)).fixedSubspace Psub) := hformula
      _ = p * 1 := by
        rw [natCard_subgroupOf_eq P L le_sup_right, hch.B1.P_card, hfixedDim]
      _ = p := by simp
  have hirrL : Representation.IsIrreducible
      (Theory.Representation.ofElementaryAbelianAction
        (A := L) (G := N) (p := r)) :=
    claim3_minimal_invariant_subgroup_representation_irreducible
      N hNinv hNne hNmin
  have hsplit := elementaryAbelian_clifford_prime_finrank_restriction
    Ksub hirrL hch.B1.p_prime hNdim
  obtain hOne | hIrrK := hsplit
  · rcases hOne with ⟨X, hXirr, hXdim⟩
    let rhoL := Theory.Representation.ofElementaryAbelianAction
      (A := L) (G := N) (p := r)
    let rhoK := rhoL.comp Ksub.subtype
    have hfreeVec : ∀ k : Ksub, k ≠ 1 →
        ∀ x : Additive N, rhoK k x = x → x = 0 := by
      intro k hk x hx
      have hxmul : (k : L) • Additive.toMul x = Additive.toMul x := by
        apply Additive.ofMul.injective
        simpa [rhoK, rhoL] using hx
      have hone := hKfree k hk (Additive.toMul x) hxmul
      apply Additive.toMul.injective
      simpa using hone
    have hdvd : Nat.card Ksub ∣ r - 1 :=
      claim3_actor_card_dvd_prime_sub_one_of_oneDim_subrepresentation
        rhoK X hXdim hfreeVec
    have hKcard : Nat.card Ksub = 2 ^ p - 1 := by
      rw [natCard_subgroupOf_eq K L le_sup_left]
      exact claim_1_K_card_eq_mersenne
        H D Q K V W Q0 S Q1 P t s p hch
    have hdvdM : 2 ^ p - 1 ∣ r - 1 := by
      simpa [hKcard] using hdvd
    have hmod : r ≡ 1 [MOD 2 ^ p - 1] :=
      ((Nat.modEq_iff_dvd' hr.one_le).2 hdvdM).symm
    refine ⟨⟨0, Nat.zero_le _, by simpa using hmod⟩, ?_⟩
    exact chapter2_claim3_ne_characteristic_of_modEq
      hch.B1.p_prime hr hrodd (Nat.zero_le _) (by simpa using hmod)
  · exact chapter2_claim3_irreducible_branch
      H D Q K V W Q0 S Q1 P t p hch.section3.section2
      hch.B1.P_le_V hch.B1.P_card hch.B1.p_prime
      (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
      (claim_1_K_card_eq_mersenne H D Q K V W Q0 S Q1 P t s p hch)
      hr hrodd
      hKfree hsetup.2.2 hNdim hIrrK

/- Claim (3): coprimality transfer from the prime-divisor congruence. -/
private theorem chapter2_claim3_coprime_Q_K_sup_P
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    Nat.Coprime (Nat.card Q) (Nat.card ((K ⊔ P : Subgroup G))) := by
  have hsetup := claim3_setup H D Q K V W Q0 S Q1 P t s p hch
  let : (Q1.subgroupOf Q).Characteristic := hsetup.1
  have hQcard : Nat.card Q = Nat.card S * Nat.card Q1 :=
    claim3_card_eq_mul_of_characteristic_decomposition Q S Q1
      hch.section3.section2.S_le_Q hch.section3.section2.Q1_le_Q
      hch.section3.section2.S_disjoint_Q1 hch.section3.section2.Q_decomp
  have hKPcard : Nat.card (K ⊔ P : Subgroup G) = Nat.card K * Nat.card P :=
    claim3_card_KP_eq_of_frobenius K P hsetup.2.2
  have hKcard : Nat.card K = 2 ^ p - 1 :=
    claim_1_K_card_eq_mersenne H D Q K V W Q0 S Q1 P t s p hch
  have hKPcard' : Nat.card (K ⊔ P : Subgroup G) = (2 ^ p - 1) * p := by
    rw [hKPcard, hKcard, hch.B1.P_card]
  have hVleD : V ≤ D :=
    proposition_3_V_le_D H D Q K V W Q0 S Q1 t hch.section3.section2
  have hpodd : Odd p := by
    rw [← hch.B1.P_card]
    exact hch.section3.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le (hch.B1.P_le_V.trans hVleD))
  exact claim3_coprime_of_card_data hch.B1.p_prime hpodd hQcard hKPcard'
    (claim3_S_card_power_two Q S hch.section3.section2.S_sylow_in_Q)
    (chapter2_claim3_prime_divisors_Q1
      H D Q K V W Q0 S Q1 P t s p hch)

public theorem claim_3
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    (∀ r : ℕ, Nat.Prime r → r ∣ Nat.card Q1 →
      (∃ i : ℕ, i ≤ p - 1 ∧ r ≡ 2 ^ i [MOD 2 ^ p - 1]) ∧ r ≠ p) ∧
      Nat.Coprime (Nat.card Q) (Nat.card ((K ⊔ P : Subgroup G))) := by
  exact
    ⟨chapter2_claim3_prime_divisors_Q1
        H D Q K V W Q0 S Q1 P t s p hch,
      chapter2_claim3_coprime_Q_K_sup_P
        H D Q K V W Q0 S Q1 P t s p hch⟩

end PFchapter2
end CFSG.BenderSuzuki
