module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.RightNearField.Linear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Maschke

namespace CFSG
end CFSG
open CFSG

/-!
# Semilinear coordinates for finite right near-fields

This file isolates the Appendix-I field and semilinear coordinate construction used by both Peterfalvi Appendix II and Huppert--Blackburn XI.2.5.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixII

universe u
set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
private theorem appendixIFpT_exists_normalized_addEquiv
    {p : ℕ} [Fact (Nat.Prime p)]
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) [IsMulCommutative A]
    [MulDistribMulAction A (Multiplicative F)]
    [IsElementaryAbelian p (Multiplicative F)]
    (T : Subgroup A) [T.Normal] [IsCyclic T]
    [Module (PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T)
      (Additive (Multiplicative F))]
    (hIrr : Representation.IsIrreducible
      (PFAppendixI.AppendixIRepresentationOfT
        (p := p) (E := Multiplicative F) T))
    (hKcard : Nat.card
      (PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T) =
        Nat.card F)
    (hsmul : ∀
      (k : PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T)
      (x : Additive (Multiplicative F)), k • x = k.1 x) :
    ∃ eKV :
      (PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T) ≃+
        Additive (Multiplicative F),
      eKV 1 = Additive.ofMul (Multiplicative.ofAdd (1 : F)) ∧
        ∀ k l, eKV (k * l) = k • eKV l := by
  let K := PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T
  let rhoT := PFAppendixI.AppendixIRepresentationOfT
    (p := p) (E := Multiplicative F) T
  let v1 : Additive (Multiplicative F) :=
    Additive.ofMul (Multiplicative.ofAdd (1 : F))
  have hv1 : v1 ≠ 0 := by
    intro h
    change (1 : F) = 0 at h
    exact one_ne_zero h
  let eval : K →+ Additive (Multiplicative F) :=
    { toFun := fun k => k • v1
      map_zero' := Module.zero_smul v1
      map_add' := fun k l => Module.add_smul k l v1 }
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype (Additive (Multiplicative F)) :=
    Fintype.ofFinite (Additive (Multiplicative F))
  have hcards : Fintype.card K = Fintype.card (Additive (Multiplicative F)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hKcard
  have heval_injective : Function.Injective eval := by
    intro k l hkl
    change k • v1 = l • v1 at hkl
    rw [hsmul k v1, hsmul l v1] at hkl
    let d : Module.End (MonoidAlgebra (ZMod p) T) rhoT.asModule := k.1 - l.1
    have hdv1 : d v1 = 0 := by
      change k.1 v1 - l.1 v1 = 0
      exact sub_eq_zero.mpr hkl
    let W : Subrepresentation rhoT :=
      Subrepresentation.ofSubmodule' (LinearMap.ker d)
    have hW_ne_bot : W ≠ ⊥ := by
      intro hW
      have hv1bot : v1 ∈ (⊥ : Subrepresentation rhoT) := by
        rw [← hW]
        exact hdv1
      exact hv1 ((Submodule.mem_bot (ZMod p)).mp
        (show v1 ∈ (⊥ : Subrepresentation rhoT).toSubmodule from hv1bot))
    have hWtop : W = ⊤ :=
      (hIrr.eq_bot_or_eq_top W).resolve_left hW_ne_bot
    apply Subtype.ext
    apply sub_eq_zero.mp
    change d = 0
    ext x
    have hxW : x ∈ W := by rw [hWtop]; exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (show x ∈ LinearMap.ker d from hxW)
  have heval_surjective : Function.Surjective eval := by
    by_contra hsurj
    have hlt := Fintype.card_lt_of_injective_not_surjective eval
      heval_injective hsurj
    omega
  let eKV : K ≃+ Additive (Multiplicative F) :=
    AddEquiv.ofBijective eval ⟨heval_injective, heval_surjective⟩
  refine ⟨eKV, ?_, ?_⟩
  · change (1 : K) • v1 = v1
    exact one_smul K v1
  · intro k l
    change (k * l) • v1 = k • (l • v1)
    exact mul_smul k l v1

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
public theorem rightNearField_irreducible_cyclic_field_coordinates
    {F : Type u} [RightNearField F] [Finite F]
    (A : Subgroup Fˣ) (hA_cyclic : IsCyclic A)
    (hIrrA :
      let p := addOrderOf (1 : F)
      letI : Fact (Nat.Prime p) := ⟨rightNearField_addOrderOf_one_prime⟩
      letI : Module (ZMod p) F := rightNearFieldZModModule F
      letI : IsElementaryAbelian p (Multiplicative F) :=
        rightNearFieldMultiplicativeIsElementaryAbelian
      letI : IsMulCommutative A := hA_cyclic.isMulCommutative
      letI : MulDistribMulAction A (Multiplicative F) :=
        rightNearFieldUnitsMulDistribMulAction A
      let T : Subgroup A := ⊤
      Representation.IsIrreducible
        (PFAppendixI.AppendixIRepresentationOfT
          (p := p) (E := Multiplicative F) T)) :
    ∃ (p n : ℕ) (K : Type u) (_ : CommRing K) (_ : Finite K)
        (_ : Algebra (ZMod p) K) (e : F ≃+ K),
      IsField K ∧ Nat.Prime p ∧ Nat.card K = p ^ n ∧ e 1 = 1 ∧
        (∀ (x : F) (a : A),
          e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F)) ∧
        Subring.closure
          (Set.range (algebraMap (ZMod p) K) ∪
            Set.range (fun a : A => e (((a : A) : Fˣ) : F))) = ⊤ := by
  let p := addOrderOf (1 : F)
  letI : Fact (Nat.Prime p) := ⟨rightNearField_addOrderOf_one_prime⟩
  letI : Module (ZMod p) F := rightNearFieldZModModule F
  letI : IsMulCommutative A := hA_cyclic.isMulCommutative
  letI : MulDistribMulAction A (Multiplicative F) :=
    rightNearFieldUnitsMulDistribMulAction A
  letI : FaithfulSMul A (Multiplicative F) := {
    eq_of_smul_eq_smul h := by
      have h1 := h (Multiplicative.ofAdd (1 : F))
      change (1 : F) * ((_ : A) : Fˣ) = 1 * ((_ : A) : Fˣ) at h1
      apply Subtype.ext
      apply Units.ext
      simpa using h1 }
  letI : IsElementaryAbelian p (Multiplicative F) :=
    { toIsMulCommutative := { is_comm := ⟨mul_comm⟩ }
      exponent_dvd_p := by
        refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
        intro x
        change addOrderOf (1 : F) • Multiplicative.toAdd x = 0
        exact rightNearField_addOrderOf_one_nsmul_eq_zero
          (F := F) (Multiplicative.toAdd x) }
  let T : Subgroup A := ⊤
  letI : T.Normal := inferInstance
  letI : IsCyclic A := hA_cyclic
  letI : IsCyclic T := inferInstance
  let rhoT := PFAppendixI.AppendixIRepresentationOfT
    (p := p) (E := Multiplicative F) T
  have hIrr : Representation.IsIrreducible rhoT := hIrrA
  letI : Representation.IsIrreducible rhoT := hIrr
  obtain ⟨n, hcard⟩ := rightNearField_natCard_eq_addOrderOf_one_pow (F := F)
  let K := PFAppendixI.AppendixIFpT (p := p) (E := Multiplicative F) T
  have hKisField : IsField K := Finite.isField_of_domain K
  obtain ⟨fieldInst, hfield⟩ :=
    PFAppendixI.peterfalvi_appendixI_proposition_2_a
      (p := p) (n := n) (U := A) (E := Multiplicative F) T hcard
  have hfieldData :
      ∃ moduleInst : Module K (Additive (Multiplicative F)),
        letI : Module K (Additive (Multiplicative F)) := moduleInst
        Nat.card K = p ^ n ∧
          ∀ (k : K) (x : Additive (Multiplicative F)), k • x = k.1 x := by
    letI : Field K := fieldInst
    obtain ⟨moduleInst, hmodule⟩ := hfield
    exact ⟨moduleInst, hmodule.1, hmodule.2.2⟩
  obtain ⟨moduleInst, hKcard, hsmul⟩ := hfieldData
  letI : Module K (Additive (Multiplicative F)) := moduleInst
  obtain ⟨eKV, heKV1, heKV_mul⟩ :=
    appendixIFpT_exists_normalized_addEquiv A T hIrr
      (hKcard.trans hcard.symm) hsmul
  let e : F ≃+ K := eKV.symm
  have he1 : e 1 = 1 := by
    apply eKV.injective
    rw [show eKV (e 1) = Additive.ofMul (Multiplicative.ofAdd (1 : F)) from
      eKV.apply_symm_apply (Additive.ofMul (Multiplicative.ofAdd (1 : F)))]
    exact heKV1.symm
  have he_apply (x : F) :
      eKV (e x) = Additive.ofMul (Multiplicative.ofAdd x) :=
    eKV.apply_symm_apply (Additive.ofMul (Multiplicative.ofAdd x))
  let kt (t : T) : K :=
    ⟨PFAppendixI.AppendixITActionEnd (p := p) (E := Multiplicative F) T t,
      Algebra.subset_adjoin (Set.mem_range_self t)⟩
  have hkt_smul (t : T) (z : Additive (Multiplicative F)) :
      kt t • z = Additive.ofMul
        (Multiplicative.ofAdd
          (Multiplicative.toAdd (Additive.toMul z) * (((t : T) : A) : Fˣ))) := by
    rw [hsmul]
    change PFAppendixI.AppendixITActionEnd
      (p := p) (E := Multiplicative F) T t z = _
    rw [PFAppendixI.AppendixITActionEnd_apply]
    rfl
  have hcoordT (t : T) :
      e (((((t : T) : A) : Fˣ) : F)) = kt t := by
    apply eKV.injective
    rw [he_apply, ← mul_one (kt t), heKV_mul, heKV1, hkt_smul]
    simp
  have hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F) := by
    intro x a
    let t : T := ⟨a, by simp [T]⟩
    have hta : ((((t : T) : A) : Fˣ) : F) = (((a : A) : Fˣ) : F) := rfl
    apply eKV.injective
    rw [he_apply, ← hta, hcoordT t]
    calc
      Additive.ofMul (Multiplicative.ofAdd (x * ((a : A) : Fˣ))) =
          kt t • Additive.ofMul (Multiplicative.ofAdd x) := by
        rw [hkt_smul]
        rfl
      _ = kt t • eKV (e x) := by rw [he_apply]
      _ = eKV (kt t * e x) := (heKV_mul (kt t) (e x)).symm
      _ = eKV (e x * kt t) := congrArg eKV (mul_comm (kt t) (e x))
  let S : Set K :=
    Set.range (algebraMap (ZMod p) K) ∪
      Set.range (fun a : A => e (((a : A) : Fˣ) : F))
  have hclosure : Subring.closure S = ⊤ := by
    apply (Subring.eq_top_iff' _).2
    intro k
    refine Algebra.adjoin_induction
      (p := fun x hx => (⟨x, hx⟩ : K) ∈ Subring.closure S) ?_ ?_ ?_ ?_ k.2
    · intro x hx
      obtain ⟨t, rfl⟩ := hx
      change kt t ∈ Subring.closure S
      rw [← hcoordT t]
      exact Subring.subset_closure
        (Or.inr ⟨((t : T) : A), rfl⟩)
    · intro r
      exact Subring.subset_closure (Or.inl ⟨r, rfl⟩)
    · intro x y hx hy hx' hy'
      exact Subring.add_mem _ hx' hy'
    · intro x y hx hy hx' hy'
      exact Subring.mul_mem _ hx' hy'
  exact ⟨p, n, K, inferInstance, inferInstance, inferInstance, e, hKisField,
    rightNearField_addOrderOf_one_prime, hKcard, he1, hscalar, hclosure⟩

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 500000 in
set_option backward.isDefEq.respectTransparency false in
public theorem rightNearField_semilinear_coordinates
    {F K : Type u} [RightNearField F] [Finite F]
    {p : ℕ} [Fact (Nat.Prime p)] [Field K] [Finite K] [Algebra (ZMod p) K]
    (A : Subgroup Fˣ) (hAnormal : A.Normal) (e : F ≃+ K) (he1 : e 1 = 1)
    (hscalar : ∀ (x : F) (a : A),
      e (x * ((a : A) : Fˣ)) = e x * e (((a : A) : Fˣ) : F))
    (hclosure : Subring.closure
      (Set.range (algebraMap (ZMod p) K) ∪
        Set.range (fun a : A => e (((a : A) : Fˣ) : F))) = ⊤) :
    ∃ σHom : (Fˣ)ᵐᵒᵖ →* (K ≃+* K), ∀ (x : F) (y : Fˣ),
      e (x * (y : F)) = σHom (MulOpposite.op y) (e x) * e (y : F) := by
  letI : Module (ZMod p) F :=
    AddCommGroup.zmodModule (n := p) (by
      intro x
      apply e.injective
      rw [map_nsmul, map_zero]
      rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
      simp)
  let Q0 : Subgroup (Multiplicative F) := ⊤
  let q0Top : Q0 ≃* Multiplicative F := Subgroup.topEquiv
  let q0_add : Q0 ≃* Multiplicative K :=
    q0Top.trans e.toMultiplicative
  let u_add : (Fˣ)ᵐᵒᵖ →* (Q0 ≃* Q0) := {
    toFun u :=
      (q0Top.trans
        (rightNearFieldRightMulAddEquiv u.unop).toMultiplicative).trans q0Top.symm
    map_one' := by
      ext x
      change Multiplicative.toAdd (q0Top x) * (1 : F) =
        Multiplicative.toAdd (q0Top x)
      simp
    map_mul' := by
      intro u v
      ext x
      change Multiplicative.toAdd (q0Top x) *
          ((v.unop * u.unop : Fˣ) : F) =
        (Multiplicative.toAdd (q0Top x) * (v.unop : F)) * (u.unop : F)
      rw [Units.val_mul, mul_assoc] }
  have hu_add_injective : Function.Injective u_add := by
    intro u v huv
    let oneQ : Q0 := ⟨Multiplicative.ofAdd (1 : F), by simp [Q0]⟩
    have h := congrArg (fun g : Q0 ≃* Q0 => q0Top (g oneQ)) huv
    have hval : (u.unop : F) = (v.unop : F) := by
      simpa [u_add, oneQ, q0Top, rightNearFieldRightMulAddEquiv,
        rightNearFieldRightMulAddHom] using congrArg Multiplicative.toAdd h
    apply MulOpposite.unop_injective
    apply Units.ext
    exact hval
  let s : Q0 := ⟨Multiplicative.ofAdd (1 : F), by simp [Q0]⟩
  have hs : (s : Multiplicative F) ≠ 1 := by
    change (1 : F) ≠ 0
    exact one_ne_zero
  let S : Set K :=
    Set.range (algebraMap (ZMod p) K) ∪
      Set.range (fun a : A => e (((a : A) : Fˣ) : F))
  have hconjT : ∀ (u : (Fˣ)ᵐᵒᵖ) (lambda : K), lambda ∈ S →
      ∃ c : K, ∀ x : Q0,
        u_add u (q0_add.symm
            (Multiplicative.ofAdd (lambda * Multiplicative.toAdd (q0_add x)))) =
          q0_add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0_add (u_add u x)))) := by
    intro u lambda hlambda
    rcases hlambda with hlambda | hlambda
    · obtain ⟨r, rfl⟩ := hlambda
      refine ⟨algebraMap (ZMod p) K r, ?_⟩
      intro x
      apply q0Top.injective
      let z : F := Multiplicative.toAdd (q0Top x)
      change e.symm (algebraMap (ZMod p) K r * e z) * (u.unop : F) =
        e.symm
          (algebraMap (ZMod p) K r * e (z * (u.unop : F)))
      rw [← Algebra.smul_def, ← Algebra.smul_def]
      calc
        e.symm (r • e z) * (u.unop : F) =
            (r • z) * (u.unop : F) := by
          rw [ZMod.map_smul, e.symm_apply_apply]
        _ = r • (z * (u.unop : F)) :=
          ZMod.map_smul (rightNearFieldRightMulAddHom (u.unop : F)) r z
        _ = e.symm (r • e (z * (u.unop : F))) := by
          rw [ZMod.map_smul, e.symm_apply_apply]
    · obtain ⟨a, rfl⟩ := hlambda
      let a' : A :=
        ⟨u.unop⁻¹ * (a : Fˣ) * u.unop, hAnormal.conj_mem' a.1 a.2 u.unop⟩
      refine ⟨e (((a' : A) : Fˣ) : F), ?_⟩
      intro x
      apply q0Top.injective
      let z : F := Multiplicative.toAdd (q0Top x)
      change e.symm (e (((a : A) : Fˣ) : F) * e z) * (u.unop : F) =
        e.symm
          (e (((a' : A) : Fˣ) : F) * e (z * (u.unop : F)))
      have hleft :
          e.symm (e (((a : A) : Fˣ) : F) * e z) =
            z * ((a : A) : Fˣ) := by
        apply e.injective
        rw [e.apply_symm_apply, hscalar]
        exact mul_comm _ _
      have hright :
          e.symm
              (e (((a' : A) : Fˣ) : F) * e (z * (u.unop : F))) =
            (z * (u.unop : F)) * ((a' : A) : Fˣ) := by
        apply e.injective
        rw [e.apply_symm_apply, hscalar]
        exact mul_comm _ _
      rw [hleft, hright]
      simp [a', mul_assoc]
  obtain ⟨σHom, hsemi, _⟩ :=
    PFAppendixI.peterfalvi_appendixI_proposition_2_b
      Q0 q0_add u_add hu_add_injective s hs S hclosure hconjT
  refine ⟨σHom, ?_⟩
  intro x y
  have h := hsemi (MulOpposite.op y) (e x) s
  have h' :=
    congrArg (fun z : Q0 => Multiplicative.toAdd (q0_add z)) h
  have hq0s : Multiplicative.toAdd (q0_add s) = 1 := by
    change e 1 = 1
    exact he1
  have htopS : Multiplicative.toAdd (q0Top s) = 1 := rfl
  rw [hq0s, mul_one] at h'
  simpa [q0_add, q0Top, u_add, s, he1, htopS,
    rightNearFieldRightMulAddEquiv, rightNearFieldRightMulAddHom] using h'

end PFAppendixII
end CFSG.BenderSuzuki
