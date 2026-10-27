module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_b
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

open scoped IsMulCommutative

attribute [local instance] commutatorElement

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixI PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Proposition 2
-/

private def proposition_2_invariantSubgroupMulAut
    {X : Type*} [Group X] (tau : MulAut X) (A : Subgroup X)
    (hA : A.map tau.toMonoidHom = A) : MulAut A :=
  (MulEquiv.subgroupMap tau A).trans (MulEquiv.subgroupCongr hA)

private theorem proposition_2_invariantSubgroupMulAut_coe
    {X : Type*} [Group X] (tau : MulAut X) (A : Subgroup X)
    (hA : A.map tau.toMonoidHom = A) (x : A) :
    ((proposition_2_invariantSubgroupMulAut tau A hA x : A) : X) = tau x := rfl

/-- A fixed-point-free involutive automorphism is inversion.  This is the
automorphism form of the odd-order factorization used in Chapter I, Section 1. -/
private theorem proposition_2_involutiveMulAut_eq_inv_of_fixed_eq_one
    {X : Type*} [Group X] [Finite X]
    (tau : MulAut X) (htau : ∀ x : X, tau (tau x) = x)
    (hfix : ∀ x : X, tau x = x → x = 1) :
    ∀ x : X, tau x = x⁻¹ := by
  let f : X → X := fun y => (tau y)⁻¹ * y
  have hf_injective : Function.Injective f := by
    intro a b hab
    change (tau a)⁻¹ * a = (tau b)⁻¹ * b at hab
    have hfixed : tau (b * a⁻¹) = b * a⁻¹ := by
      rw [map_mul, map_inv]
      calc
        tau b * (tau a)⁻¹ =
            tau b * ((tau a)⁻¹ * a) * a⁻¹ := by group
        _ = tau b * ((tau b)⁻¹ * b) * a⁻¹ := by rw [hab]
        _ = b * a⁻¹ := by group
    have hba : b * a⁻¹ = 1 := hfix _ hfixed
    have hba' := congrArg (fun z : X => z * a) hba
    have : b = a := by simpa [mul_assoc] using hba'
    exact this.symm
  have hf_surjective : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf_injective
  intro x
  obtain ⟨y, rfl⟩ := hf_surjective x
  change tau ((tau y)⁻¹ * y) = ((tau y)⁻¹ * y)⁻¹
  rw [map_mul, map_inv, htau]
  simp

/-- The Fitting argument in the first paragraph of Proposition 2. -/
private theorem proposition_2_fitting_eq_antiFixed_of_involutiveMulAut
    {X : Type*} [Group X] [Finite X]
    (hXodd : Odd (Nat.card X))
    (tau : MulAut X) (htau : ∀ x : X, tau (tau x) = x)
    (hfixF : ∀ x : fittingSubgroup X, tau (x : X) = x → x = 1)
    (hquotient_comm : IsMulCommutative (X ⧸ fittingSubgroup X)) :
    ∀ x : X, tau x = x⁻¹ ↔ x ∈ fittingSubgroup X := by
  classical
  let F : Subgroup X := fittingSubgroup X
  have hFmap : F.map tau.toMonoidHom = F :=
    (Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (fittingSubgroup X).Characteristic)) tau
  let tauF : MulAut F := proposition_2_invariantSubgroupMulAut tau F hFmap
  have htauF : ∀ x : F, tauF (tauF x) = x := by
    intro x
    apply Subtype.ext
    simp only [proposition_2_invariantSubgroupMulAut_coe, tauF]
    exact htau x
  have hfixF' : ∀ x : F, tauF x = x → x = 1 := by
    intro x hx
    apply hfixF x
    exact congrArg Subtype.val hx
  have hantiF : ∀ x : F, tauF x = x⁻¹ :=
    proposition_2_involutiveMulAut_eq_inv_of_fixed_eq_one tauF htauF hfixF'
  let pi : X →* X ⧸ F := QuotientGroup.mk' F
  let tauQ : MulAut (X ⧸ F) :=
    QuotientGroup.congr (G' := F) (H' := F) tau hFmap
  have htaupi (x : X) : tauQ (pi x) = pi (tau x) := by
    exact QuotientGroup.congr_mk' F F tau hFmap x
  have htauQ : ∀ q : X ⧸ F, tauQ (tauQ q) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective F q
    rw [htaupi, htaupi, htau]
  letI : IsMulCommutative (X ⧸ F) := hquotient_comm
  let A : Subgroup (X ⧸ F) :=
    { carrier := {q | tauQ q = q⁻¹}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change tauQ (a * b) = (a * b)⁻¹
        rw [map_mul, ha, hb]
        simpa only [mul_inv_rev] using (mul_comm a⁻¹ b⁻¹)
      inv_mem' := by
        intro a ha
        change tauQ a⁻¹ = (a⁻¹)⁻¹
        rw [map_inv, ha] }
  let B : Subgroup X := A.comap pi
  have hBnormal : B.Normal := by
    letI : CommGroup (X ⧸ F) := IsMulCommutative.instCommGroup
    exact Subgroup.Normal.comap (inferInstance : A.Normal) pi
  have hBstable : ∀ x : X, x ∈ B → tau x ∈ B := by
    intro x hx
    change tauQ (pi (tau x)) = (pi (tau x))⁻¹
    change tauQ (pi x) = (pi x)⁻¹ at hx
    rw [← htaupi x, htauQ, hx]
    exact (inv_inv (pi x)).symm
  have hBmap : B.map tau.toMonoidHom = B := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hBstable y hy
    · intro x hx
      refine ⟨tau x, hBstable x hx, ?_⟩
      exact htau x
  let tauB : MulAut B := proposition_2_invariantSubgroupMulAut tau B hBmap
  have htauB : ∀ x : B, tauB (tauB x) = x := by
    intro x
    apply Subtype.ext
    simp only [proposition_2_invariantSubgroupMulAut_coe, tauB]
    exact htau x
  have hquotient_odd : Odd (Nat.card (X ⧸ F)) :=
    odd_of_card_dvd hXodd (Subgroup.card_quotient_dvd_card (s := F))
  have hfixB : ∀ x : B, tauB x = x → x = 1 := by
    intro x hx
    have hxtau : tau (x : X) = x := by
      simpa only [proposition_2_invariantSubgroupMulAut_coe, tauB] using
        congrArg Subtype.val hx
    have hqxfix : tauQ (pi (x : X)) = pi (x : X) := by
      rw [htaupi, hxtau]
    have hqxanti : tauQ (pi (x : X)) = (pi (x : X))⁻¹ := x.property
    have hselfinv : pi (x : X) = (pi (x : X))⁻¹ :=
      hqxfix.symm.trans hqxanti
    have hsq : (pi (x : X)) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hselfinv]
      simp
    have hord_dvd_two : orderOf (pi (x : X)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one hsq
    have hcop : Nat.Coprime 2 (Nat.card (X ⧸ F)) :=
      hquotient_odd.coprime_two_left
    have hord_dvd_one : orderOf (pi (x : X)) ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hord_dvd_two (orderOf_dvd_natCard (pi (x : X)))
    have hqone : pi (x : X) = 1 :=
      orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord_dvd_one)
    have hxF : (x : X) ∈ F :=
      (QuotientGroup.eq_one_iff (N := F) (x : X)).mp hqone
    have hxone : (⟨(x : X), hxF⟩ : fittingSubgroup X) = 1 := by
      apply hfixF
      exact hxtau
    have hxXone : (x : X) = 1 :=
      congrArg (fun y : fittingSubgroup X => (y : X)) hxone
    exact Subtype.ext hxXone
  have hantiB : ∀ x : B, tauB x = x⁻¹ :=
    proposition_2_involutiveMulAut_eq_inv_of_fixed_eq_one tauB htauB hfixB
  have hBcomm : IsMulCommutative B := by
    refine IsMulCommutative.mk <| Std.Commutative.mk ?_
    intro a b
    have hinv_comm : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
      calc
        a⁻¹ * b⁻¹ = tauB a * tauB b := by rw [hantiB a, hantiB b]
        _ = tauB (a * b) := (map_mul tauB a b).symm
        _ = (a * b)⁻¹ := hantiB (a * b)
        _ = b⁻¹ * a⁻¹ := by simp
    have hcomm := congrArg (fun z : B => z⁻¹) hinv_comm
    simpa using hcomm.symm
  have hBleF : B ≤ F := by
    letI : IsMulCommutative B := hBcomm
    have hBnil : Group.IsNilpotent B := by
      letI : IsMulCommutative B := hBcomm
      refine ⟨1, ?_⟩
      have hcenter : Subgroup.center B = ⊤ := by
        ext x
        simp [Subgroup.mem_center_iff, mul_comm]
      simpa [Subgroup.upperCentralSeries_one] using hcenter
    exact le_sSup
      (show B.Normal ∧ Group.IsNilpotent B from ⟨hBnormal, hBnil⟩)
  have hFleB : F ≤ B := by
    intro x hx
    change tauQ (pi x) = (pi x)⁻¹
    have hpix : pi x = 1 :=
      (QuotientGroup.eq_one_iff (N := F) x).mpr hx
    simp [hpix]
  have hBeqF : B = F := le_antisymm hBleF hFleB
  intro x
  constructor
  · intro hx
    have hxB : x ∈ B := by
      change tauQ (pi x) = (pi x)⁻¹
      rw [htaupi, hx]
      simp
    simpa [hBeqF] using hxB
  · intro hx
    let xF : F := ⟨x, hx⟩
    have hxanti := hantiF xF
    exact congrArg Subtype.val hxanti

private theorem proposition_2_rightConjugateElem_mem_D_of_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {d : G} (hd : d ∈ D) :
    rightConjugateElem d t ∈ D := by
  classical
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  rw [hA1.D_eq]
  refine ⟨?_, ?_⟩
  · rcases hd'.2 with ⟨h, hhH, hhd⟩
    have tht : t * h * t = d := by
      simpa [MulAut.conj, htinv, mul_assoc] using hhd
    have hconj_eq : rightConjugateElem d t = h := by
      calc
        rightConjugateElem d t = t * d * t := by simp [rightConjugateElem, htinv]
        _ = t * (t * h * t) * t := by rw [← tht]
        _ = (t * t) * h * (t * t) := by simp [mul_assoc]
        _ = h := by simp [htt]
    rw [hconj_eq]
    exact hhH
  · refine ⟨d, hd'.1, ?_⟩
    simp [rightConjugateElem]

private theorem proposition_2_eq_one_of_sq_eq_one_of_odd_card
    {X : Type*} [Group X] [Finite X] (hXodd : Odd (Nat.card X))
    (x : X) (hx : x ^ 2 = 1) : x = 1 := by
  have hord_dvd_two : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime 2 (Nat.card X) := hXodd.coprime_two_left
  have hord_dvd_one : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hord_dvd_two (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord_dvd_one)

/-- Conjugation by the distinguished involution, restricted to `D`. -/
private def proposition_2_D_conjugationMulAut
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    MulAut D where
  toFun d :=
    ⟨rightConjugateElem (d : G) t,
      proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1 d.property⟩
  invFun d :=
    ⟨rightConjugateElem (d : G) t,
      proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1 d.property⟩
  left_inv d := by
    apply Subtype.ext
    exact rightConjugateElem_involutive_of_isInvolution hA1.involution_t d
  right_inv d := by
    apply Subtype.ext
    exact rightConjugateElem_involutive_of_isInvolution hA1.involution_t d
  map_mul' a b := by
    apply Subtype.ext
    simp [rightConjugateElem, mul_assoc]


private theorem proposition_2_D_conjugationMulAut_eq_self_of_mem_V
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (d : D) (hdV : (d : G) ∈ peterfalviV D t) :
    proposition_2_D_conjugationMulAut H D Q t hA1 d = d := by
  apply Subtype.ext
  change rightConjugateElem (d : G) t = (d : G)
  have hcomm : (d : G) * t = t * (d : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp hdV.2
  calc
    rightConjugateElem (d : G) t = t * (d : G) * t := by
      rw [rightConjugateElem, hA1.involution_t.inv_eq_self]
    _ = (d : G) * (t * t) := by rw [← hcomm, mul_assoc]
    _ = (d : G) := by
      rw [show t * t = 1 by
        simpa [pow_two] using hA1.involution_t.sq_eq_one]
      simp

private theorem proposition_2_D_conjugationMulAut_eq_inv_of_mem_KSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t)
    (k : peterfalviKSet D t) :
    proposition_2_D_conjugationMulAut H D Q t hA1
      (⟨(k : G), k.property.1⟩ : D) =
        (⟨(k : G), k.property.1⟩ : D)⁻¹ := by
  apply Subtype.ext
  exact k.property.2

private theorem proposition_2_D_normalized_by_t_of_hA1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G) (hA1 : HypothesisA1 G Ω H D Q t) :
    t ∈ Subgroup.normalizer (D : Set G) := by
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  rw [Subgroup.mem_normalizer_iff'']
  intro d
  constructor
  · intro hd
    simpa [rightConjugateElem, htinv] using
      (proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1 (d := d) hd)
  · intro hd
    have hmem :=
      proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1
        (d := t⁻¹ * d * t) hd
    have htd : t * (t * d) = d := by
      calc
        t * (t * d) = (t * t) * d := by simp [mul_assoc]
        _ = 1 * d := by rw [htt]
        _ = d := by simp
    have hmem' : t * (t * d) ∈ D := by
      simpa [rightConjugateElem, htinv, htt, mul_assoc] using hmem
    simpa [htd] using hmem'

/-- In Hypothesis (A1), the distinguished involution normalizes `D`. -/
public theorem hypothesisA1_t_mem_normalizer_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    t ∈ Subgroup.normalizer (D : Set G) := by
  exact proposition_2_D_normalized_by_t_of_hA1 H D Q t hA1

set_option maxHeartbeats 800000 in
private theorem proposition_2_canonical_quotient_fitting
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q Q0 : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hQ0_comm : IsMulCommutative Q0)
    (hQ0_sq : ∀ x : Q0, x ^ 2 = 1) :
    let V := peterfalviV D t
    let W := peterfalviW V (peterfalviKSet D t)
    ∃ hWD : (W.subgroupOf D).Normal,
      letI : (W.subgroupOf D).Normal := hWD
      ∃ tau : MulAut (D ⧸ W.subgroupOf D),
        IsCyclic (fittingSubgroup (D ⧸ W.subgroupOf D)) ∧
          (∀ d : D,
            tau (QuotientGroup.mk d) =
              QuotientGroup.mk
                (proposition_2_D_conjugationMulAut H D Q t hA1 d)) ∧
          ∀ x : D ⧸ W.subgroupOf D,
            tau x = x⁻¹ ↔ x ∈ fittingSubgroup (D ⧸ W.subgroupOf D) := by
  classical
  dsimp only
  let V : Subgroup G := peterfalviV D t
  let W : Subgroup G := peterfalviW V (peterfalviKSet D t)
  have hW_eq_centralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    peterfalvi_chapter1_section2_canonical_W_eq_D_centralizer_involutions
      H D Q V W t hA1 rfl rfl
  have hWD : (W.subgroupOf D).Normal :=
    peterfalvi_chapter1_section2_canonical_W_normal_D
      H D Q V W t hA1 rfl rfl
  letI : (W.subgroupOf D).Normal := hWD
  obtain ⟨rhoD, hrhoD, hrhoD_formula⟩ :=
    peterfalvi_chapter1_section2_canonical_quotient_conjugation_action
      H D W Q0 hA1.D_le_H hQ0_def hW_eq_centralizer hWD
  letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
    MulDistribMulAction.compHom Q0 rhoD
  letI : FaithfulSMul (D ⧸ W.subgroupOf D) Q0 := by
    constructor
    intro a b hab
    apply hrhoD
    apply MulEquiv.ext
    intro q
    exact hab q
  letI : IsElementaryAbelian 2 Q0 :=
    isElementaryAbelian_two_of_forall_sq_one hQ0_comm hQ0_sq
  have htrans :
      ∀ x : Q0, x ≠ 1 → ∀ y : Q0, y ≠ 1 →
        ∃ d : D ⧸ W.subgroupOf D, d • x = y :=
    peterfalvi_chapter1_section2_canonical_quotient_transitive_on_Q0_nontrivial
      H D Q W Q0 t hA1 hQ0_def hWD rhoD
        (fun d q => congrArg Subtype.val (hrhoD_formula d q))
  have hDbar_odd : Odd (Nat.card (D ⧸ W.subgroupOf D)) :=
    odd_of_card_dvd hA1.D_odd
      (Subgroup.card_quotient_dvd_card (s := W.subgroupOf D))
  obtain ⟨hFcyclic, hFfree, hFquotient_comm⟩ :=
    peterfalvi_appendixI_proposition_1
      (q := 2) (D := D ⧸ W.subgroupOf D) (E := Q0) hDbar_odd
      (fun a b ha hb => htrans a ha b hb)
  obtain ⟨s, _hsH, hsI, _hsStructure, hsQ0, _hVstabilizer, hVfix⟩ :=
    peterfalvi_chapter1_section2_proposition_3_distinguished_involution
      H D Q V Q0 t hA1 rfl hQ0_def
  let sQ0 : Q0 := ⟨s, hsQ0⟩
  have hsQ0_ne : sQ0 ≠ 1 := by
    intro hs
    apply hsI.ne_one
    simpa [sQ0] using congrArg Subtype.val hs
  let tauD : MulAut D := proposition_2_D_conjugationMulAut H D Q t hA1
  have hWleV : W ≤ V := by
    exact inf_le_left
  have hWfixed : ∀ w : W.subgroupOf D, tauD w = w := by
    intro w
    apply Subtype.ext
    change rightConjugateElem (w : G) t = (w : G)
    have hwV : (w : G) ∈ V := hWleV w.property
    have hwC : (w : G) ∈ Subgroup.centralizer ({t} : Set G) := hwV.2
    have hcomm : (w : G) * t = t * (w : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hwC
    calc
      rightConjugateElem (w : G) t = t * (w : G) * t := by
        rw [rightConjugateElem, hA1.involution_t.inv_eq_self]
      _ = (w : G) * (t * t) := by rw [← hcomm, mul_assoc]
      _ = (w : G) := by
        rw [show t * t = 1 by
          simpa [pow_two] using hA1.involution_t.sq_eq_one]
        simp
  have hWmap :
      (W.subgroupOf D).map tauD.toMonoidHom = W.subgroupOf D := by
    apply le_antisymm
    · rintro x ⟨w, hw, rfl⟩
      have heq : tauD w = w := hWfixed ⟨w, hw⟩
      change tauD w ∈ W.subgroupOf D
      rw [heq]
      exact hw
    · intro w hw
      exact ⟨w, hw, hWfixed ⟨w, hw⟩⟩
  let tau : MulAut (D ⧸ W.subgroupOf D) :=
    QuotientGroup.congr
      (G' := W.subgroupOf D) (H' := W.subgroupOf D) tauD hWmap
  have htau_formula (d : D) :
      tau (QuotientGroup.mk d) = QuotientGroup.mk (tauD d) :=
    QuotientGroup.congr_mk' (W.subgroupOf D) (W.subgroupOf D)
      tauD hWmap d
  have htauD : ∀ d : D, tauD (tauD d) = d := by
    intro d
    apply Subtype.ext
    exact rightConjugateElem_involutive_of_isInvolution hA1.involution_t d
  have htau : ∀ x : D ⧸ W.subgroupOf D, tau (tau x) = x := by
    intro x
    obtain ⟨d, rfl⟩ :=
      QuotientGroup.mk'_surjective (W.subgroupOf D) x
    calc
      tau (tau (QuotientGroup.mk d)) =
          tau (QuotientGroup.mk (tauD d)) :=
        congrArg tau (htau_formula d)
      _ = QuotientGroup.mk (tauD (tauD d)) := htau_formula (tauD d)
      _ = QuotientGroup.mk d := congrArg QuotientGroup.mk (htauD d)
  have hfixed_lift :
      ∀ d : D, tau (QuotientGroup.mk d) = QuotientGroup.mk d →
        (d : G) ∈ V := by
    intro d hd
    let w : D := d⁻¹ * tauD d
    have hwW : w ∈ W.subgroupOf D := by
      apply (QuotientGroup.eq_one_iff (N := W.subgroupOf D) w).mp
      change (QuotientGroup.mk' (W.subgroupOf D))
        (d⁻¹ * tauD d) = 1
      rw [map_mul, map_inv]
      have hreplace :
          (QuotientGroup.mk' (W.subgroupOf D)) (tauD d) =
            (QuotientGroup.mk' (W.subgroupOf D)) d := by
        exact (htau_formula d).symm.trans hd
      rw [hreplace]
      simp
    have htauw : tauD w = w := hWfixed ⟨w, hwW⟩
    have htau_eq : tauD d = d * w := by
      simp [w]
    have hrelation : tauD d * w = d := by
      calc
        tauD d * w = tauD d * tauD w := by rw [htauw]
        _ = tauD (d * w) := (map_mul tauD d w).symm
        _ = tauD (tauD d) := by rw [← htau_eq]
        _ = d := htauD d
    have hwsq : w ^ 2 = 1 := by
      rw [htau_eq] at hrelation
      have h := congrArg (fun z : D => d⁻¹ * z) hrelation
      simpa [pow_two, mul_assoc] using h
    have hwone : w = 1 :=
      proposition_2_eq_one_of_sq_eq_one_of_odd_card hA1.D_odd w hwsq
    have htaud : tauD d = d := by simp [htau_eq, hwone]
    refine ⟨d.property, ?_⟩
    change (d : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hconj : t * (d : G) * t = (d : G) := by
      simpa [tauD, proposition_2_D_conjugationMulAut,
        rightConjugateElem, hA1.involution_t.inv_eq_self] using
          congrArg Subtype.val htaud
    have h := congrArg (fun z : G => z * t) hconj
    have htt : t * t = 1 := by
      simpa [pow_two] using hA1.involution_t.sq_eq_one
    simpa [mul_assoc, htt] using h.symm
  have hfixF :
      ∀ x : fittingSubgroup (D ⧸ W.subgroupOf D),
        tau (x : D ⧸ W.subgroupOf D) = x → x = 1 := by
    intro x hx
    obtain ⟨d, hd⟩ :=
      QuotientGroup.mk'_surjective (W.subgroupOf D) (x : D ⧸ W.subgroupOf D)
    have hdV : (d : G) ∈ V := hfixed_lift d (by
      calc
        tau (QuotientGroup.mk d) = tau (x : D ⧸ W.subgroupOf D) :=
          congrArg tau hd
        _ = (x : D ⧸ W.subgroupOf D) := hx
        _ = QuotientGroup.mk d := hd.symm)
    have hdInvV : (d : G)⁻¹ ∈ V := V.inv_mem hdV
    let dInvV : V := ⟨(d : G)⁻¹, hdInvV⟩
    have hfixs : (x : D ⧸ W.subgroupOf D) • sQ0 = sQ0 := by
      change rhoD (x : D ⧸ W.subgroupOf D) sQ0 = sQ0
      rw [← hd]
      have hformula := congrArg Subtype.val (hrhoD_formula d sQ0)
      have heqG :
          (((rhoD (QuotientGroup.mk d) sQ0 : Q0) : G)) = (sQ0 : G) := by
        simpa [sQ0, dInvV] using hformula.trans (hVfix dInvV)
      exact Subtype.val_injective heqG
    by_contra hxone
    exact hsQ0_ne (hFfree x hxone sQ0 hfixs)
  have hanti :=
    proposition_2_fitting_eq_antiFixed_of_involutiveMulAut
      hDbar_odd tau htau hfixF hFquotient_comm
  exact ⟨hWD, tau, hFcyclic, htau_formula, hanti⟩

set_option maxHeartbeats 800000 in
public theorem proposition_2_exists_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q Q0 : Subgroup G) (t : G)
    (hA : HypothesisA G Ω H D Q t)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hQ0_comm : IsMulCommutative Q0)
    (hQ0_sq : ∀ x : Q0, x ^ 2 = 1) :
    ∃ K V W : Subgroup G,
      K ≤ D ∧
        (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
        V = peterfalviV D t ∧
        W ≤ V ∧
        W = peterfalviW V (K : Set G) ∧
        IsCyclic K ∧
        (K.subgroupOf D).Normal := by
  classical
  let V : Subgroup G := peterfalviV D t
  let W : Subgroup G := peterfalviW V (peterfalviKSet D t)
  obtain ⟨hWD, tau, hFcyclic, htau_formula, hanti⟩ :=
    proposition_2_canonical_quotient_fitting
      H D Q Q0 t hA.A1 hQ0_def hQ0_comm hQ0_sq
  letI : (W.subgroupOf D).Normal := hWD
  let Dbar := D ⧸ W.subgroupOf D
  let pi : D →* Dbar := QuotientGroup.mk' (W.subgroupOf D)
  let F : Subgroup Dbar := fittingSubgroup Dbar
  let tauD : MulAut D := proposition_2_D_conjugationMulAut H D Q t hA.A1
  have hDbar_odd : Odd (Nat.card Dbar) :=
    odd_of_card_dvd hA.A1.D_odd
      (Subgroup.card_quotient_dvd_card (s := W.subgroupOf D))
  have hWleV : W ≤ V := inf_le_left
  have hquotient_anti (k : peterfalviKSet D t) :
      tau (pi (⟨(k : G), k.property.1⟩ : D)) =
        (pi (⟨(k : G), k.property.1⟩ : D))⁻¹ := by
    let kD : D := ⟨(k : G), k.property.1⟩
    calc
      tau (pi kD) = pi (tauD kD) := htau_formula kD
      _ = pi kD⁻¹ := congrArg pi
        (proposition_2_D_conjugationMulAut_eq_inv_of_mem_KSet
          H D Q t hA.A1 k)
      _ = (pi kD)⁻¹ := map_inv pi kD
  let kToF : peterfalviKSet D t → F := fun k =>
    ⟨pi (⟨(k : G), k.property.1⟩ : D),
      (hanti _).mp (hquotient_anti k)⟩
  have hDnorm : t ∈ Subgroup.normalizer (D : Set G) :=
    proposition_2_D_normalized_by_t_of_hA1 H D Q t hA.A1
  obtain ⟨hleft, _hright, _hcard⟩ :=
    PFchapter1section1.lemma_a t D hA.A1.involution_t hA.A1.D_odd hDnorm
  have hkToF_surjective : Function.Surjective kToF := by
    intro f
    obtain ⟨d, hd⟩ :=
      QuotientGroup.mk'_surjective (W.subgroupOf D) (f : Dbar)
    obtain ⟨p, _hp_univ, hp⟩ := hleft.surjOn d.property
    let k : peterfalviKSet D t := ⟨(p.2 : G), p.2.property⟩
    let kD : D := ⟨(k : G), k.property.1⟩
    let vD : D := ⟨(p.1 : G), p.1.property.1⟩
    have hpD : vD * kD = d := by
      apply Subtype.ext
      exact hp
    have hpi_mul : pi vD * pi kD = pi d := by
      simpa only [map_mul] using congrArg pi hpD
    have hv_eq : pi vD = pi d * (pi kD)⁻¹ := by
      rw [← hpi_mul]
      group
    have hdF : pi d ∈ F := by
      rw [hd]
      exact f.property
    have hkF : pi kD ∈ F := (kToF k).property
    have hvF : pi vD ∈ F := by
      rw [hv_eq]
      exact F.mul_mem hdF (F.inv_mem hkF)
    have hvV : (vD : G) ∈ V := p.1.property
    have hvfixD : tauD vD = vD :=
      proposition_2_D_conjugationMulAut_eq_self_of_mem_V
        H D Q t hA.A1 vD hvV
    have hvfix : tau (pi vD) = pi vD := by
      calc
        tau (pi vD) = pi (tauD vD) := htau_formula vD
        _ = pi vD := congrArg pi hvfixD
    have hvanti : tau (pi vD) = (pi vD)⁻¹ := (hanti _).mpr hvF
    have hvselfinv : pi vD = (pi vD)⁻¹ := hvfix.symm.trans hvanti
    have hvsq : (pi vD) ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hvselfinv]
      simp
    have hvone : pi vD = 1 :=
      proposition_2_eq_one_of_sq_eq_one_of_odd_card hDbar_odd (pi vD) hvsq
    refine ⟨k, ?_⟩
    apply Subtype.val_injective
    change pi kD = (f : Dbar)
    calc
      pi kD = 1 * pi kD := by simp
      _ = pi vD * pi kD := by rw [hvone]
      _ = pi d := hpi_mul
      _ = (f : Dbar) := hd
  have hkToF_injective : Function.Injective kToF := by
    intro a b hab
    let aD : D := ⟨(a : G), a.property.1⟩
    let bD : D := ⟨(b : G), b.property.1⟩
    have hab_pi : pi aD = pi bD := congrArg Subtype.val hab
    let w : D := aD * bD⁻¹
    have hwW : w ∈ W.subgroupOf D := by
      apply (QuotientGroup.eq_one_iff (N := W.subgroupOf D) w).mp
      change pi (aD * bD⁻¹) = 1
      rw [map_mul, map_inv, hab_pi]
      simp
    have hwG : (w : G) ∈ W := hwW
    have hwV : (w : G) ∈ V := hWleV hwG
    have hwfix : tauD w = w :=
      proposition_2_D_conjugationMulAut_eq_self_of_mem_V
        H D Q t hA.A1 w hwV
    have haanti : tauD aD = aD⁻¹ :=
      proposition_2_D_conjugationMulAut_eq_inv_of_mem_KSet
        H D Q t hA.A1 a
    have hbanti : tauD bD = bD⁻¹ :=
      proposition_2_D_conjugationMulAut_eq_inv_of_mem_KSet
        H D Q t hA.A1 b
    have hwinvW : (w : G)⁻¹ ∈ W := W.inv_mem hwG
    have hcommInvG : (w : G)⁻¹ * (b : G) = (b : G) * (w : G)⁻¹ := by
      exact ((Subgroup.mem_centralizer_iff.mp hwinvW.2) (b : G) b.property).symm
    have hcommInv : w⁻¹ * bD = bD * w⁻¹ := by
      apply Subtype.ext
      exact hcommInvG
    have hwa : aD = w * bD := by simp [w]
    have hwanti : tauD w = w⁻¹ := by
      calc
        tauD w = tauD aD * (tauD bD)⁻¹ := by
          simp [w]
        _ = aD⁻¹ * (bD⁻¹)⁻¹ := by rw [haanti, hbanti]
        _ = aD⁻¹ * bD := by simp
        _ = (w * bD)⁻¹ * bD := by rw [hwa]
        _ = bD⁻¹ * w⁻¹ * bD := by simp
        _ = bD⁻¹ * (bD * w⁻¹) := by rw [mul_assoc, hcommInv]
        _ = w⁻¹ := by simp
    have hwselfinv : w = w⁻¹ := hwfix.symm.trans hwanti
    have hwsq : w ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hwselfinv]
      simp
    have hwone : w = 1 :=
      proposition_2_eq_one_of_sq_eq_one_of_odd_card hA.A1.D_odd w hwsq
    apply Subtype.ext
    have h := congrArg (fun z : D => z * bD) hwone
    have habD : aD = bD := by simpa [w, mul_assoc] using h
    change (aD : G) = (bD : G)
    exact congrArg Subtype.val habD
  have hcard_KSet_F : Nat.card (peterfalviKSet D t) = Nat.card F :=
    Nat.card_congr
      (Equiv.ofBijective kToF ⟨hkToF_injective, hkToF_surjective⟩)
  letI : IsCyclic F := hFcyclic
  obtain ⟨f, hfgen⟩ :=
    (isCyclic_iff_exists_zpowers_eq_top (α := F)).mp hFcyclic
  obtain ⟨k, hkf⟩ := hkToF_surjective f
  let kG : G := k
  let kD : D := ⟨kG, k.property.1⟩
  have hcard_F_order : Nat.card F = orderOf f := by
    have hcard : Nat.card (Subgroup.zpowers f) = Nat.card F := by
      rw [hfgen]
      simp
    simpa [Nat.card_zpowers] using hcard.symm
  have hk_image : pi kD = (f : Dbar) := congrArg Subtype.val hkf
  have hcardF_dvd_order_k : Nat.card F ∣ orderOf kG := by
    rw [hcard_F_order]
    have himage_dvd : orderOf (pi kD) ∣ orderOf kD := orderOf_map_dvd pi kD
    rw [hk_image] at himage_dvd
    rw [← Subgroup.orderOf_coe kD] at himage_dvd
    simpa [kD, kG] using himage_dvd
  have hcardF_le_order_k : Nat.card F ≤ orderOf kG :=
    Nat.le_of_dvd (orderOf_pos kG) hcardF_dvd_order_k
  have hzp_subset : (Subgroup.zpowers kG : Set G) ⊆ peterfalviKSet D t := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
    refine ⟨D.zpow_mem k.property.1 n, ?_⟩
    change t⁻¹ * kG ^ n * t = (kG ^ n)⁻¹
    have hkanti : t⁻¹ * kG * t = kG⁻¹ := by
      simpa [kG, rightConjugateElem] using k.property.2
    calc
      t⁻¹ * kG ^ n * t = (t⁻¹ * kG * t) ^ n := by
        simpa using (conj_zpow (a := t⁻¹) (b := kG) (i := n)).symm
      _ = (kG⁻¹) ^ n := by rw [hkanti]
      _ = (kG ^ n)⁻¹ := by simp
  have hcard_KSet_le_zpowers :
      Nat.card (peterfalviKSet D t) ≤ Nat.card (Subgroup.zpowers kG) := by
    rw [hcard_KSet_F, Nat.card_zpowers]
    exact hcardF_le_order_k
  have hKSet_eq :
      peterfalviKSet D t = (Subgroup.zpowers kG : Set G) := by
    exact (Set.Finite.eq_of_subset_of_card_le (Set.toFinite _)
      hzp_subset hcard_KSet_le_zpowers).symm
  let K : Subgroup G := Subgroup.zpowers kG
  have hK_def :
      ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹ := by
    intro x
    change x ∈ (Subgroup.zpowers kG : Set G) ↔ x ∈ peterfalviKSet D t
    rw [hKSet_eq]
  have hKleD : K ≤ D := by
    intro x hx
    exact (hK_def x).mp hx |>.1
  have hclosure_eq :
      K.subgroupOf D =
        Subgroup.closure {x : D | rightConjugateElem (x : G) t = (x : G)⁻¹} := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.subset_closure
      exact ((hK_def (x : G)).mp hx).2
    · rw [Subgroup.closure_le]
      intro x hx
      exact (hK_def (x : G)).mpr ⟨x.property, hx⟩
  have hKnormal : (K.subgroupOf D).Normal := by
    have hclosure_normal :
        (Subgroup.closure
          {x : D | rightConjugateElem (x : G) t = (x : G)⁻¹}).Normal := by
      simpa using
        (PFchapter1section1.lemma_b t D hA.A1.involution_t hA.A1.D_odd hDnorm)
    rw [hclosure_eq]
    exact hclosure_normal
  refine ⟨K, V, W, hKleD, hK_def, rfl, hWleV, ?_,
    Subgroup.isCyclic_zpowers kG, hKnormal⟩
  rw [show (K : Set G) = peterfalviKSet D t by
    simpa [K] using hKSet_eq.symm]

private theorem proposition_2_K_isMulCommutative
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    IsMulCommutative K := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  apply Subtype.ext
  have haK := (hsec.K_def (a : G)).mp a.property
  have hbK := (hsec.K_def (b : G)).mp b.property
  have habK := (hsec.K_def ((a * b : K) : G)).mp (a * b : K).property
  have hconj_mul :
      rightConjugateElem ((a : G) * (b : G)) t =
        rightConjugateElem (a : G) t * rightConjugateElem (b : G) t := by
    simp [rightConjugateElem, mul_assoc]
  have hinv_comm : (a : G)⁻¹ * (b : G)⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ := by
    calc
      (a : G)⁻¹ * (b : G)⁻¹ =
          rightConjugateElem (a : G) t * rightConjugateElem (b : G) t := by
        rw [haK.2, hbK.2]
      _ = rightConjugateElem ((a : G) * (b : G)) t := hconj_mul.symm
      _ = ((a : G) * (b : G))⁻¹ := habK.2
      _ = (b : G)⁻¹ * (a : G)⁻¹ := by simp
  have hcomm := congrArg (fun x : G => x⁻¹) hinv_comm
  simpa using hcomm.symm

private theorem proposition_2_K_isZGroup
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    IsZGroup K := by
  classical
  let QH : Subgroup H := Q.subgroupOf H
  have hK_le_H : K ≤ H := hsec.K_le_D.trans hsec.hA.A1.D_le_H
  let KH : Subgroup H := K.subgroupOf H
  let L : Subgroup H := QH ⊔ KH
  haveI : QH.Normal := by
    simpa [QH] using hsec.hA.A1.Q_normal_in_H
  have hQH_norm : (QH.subgroupOf L).Normal := by
    simpa [L, QH, KH] using
      (Subgroup.Normal.subgroupOf (inferInstance : QH.Normal) L)
  have hdisj_QH_KH : Disjoint QH KH := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxK
    apply Subtype.ext
    have hxQG : (x : G) ∈ Q := by
      simpa [QH, Subgroup.mem_subgroupOf] using hxQ
    have hxDG : (x : G) ∈ D := hsec.K_le_D (by
      simpa [KH, Subgroup.mem_subgroupOf] using hxK)
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hsec.hA.A1.Q_disjoint_D) hxQG hxDG
    simpa using hxbot
  have hcomp : (QH.subgroupOf L).IsComplement' (KH.subgroupOf L) := by
    simpa [L] using isComplement'_subgroupOf_sup_of_disjoint QH KH hdisj_QH_KH
  have hQH_ne : QH.subgroupOf L ≠ ⊥ := by
    let eQH : Q ≃* QH :=
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := H) hsec.hA.A1.Q_le_H).symm
    let eQL : QH ≃* QH.subgroupOf L :=
      (Subgroup.subgroupOfEquivOfLe (H := QH) (K := L) le_sup_left).symm
    let eQ : Q ≃* QH.subgroupOf L := eQH.trans eQL
    have hQ_even_sub : Even (Nat.card (QH.subgroupOf L)) := by
      have hcard : Nat.card (QH.subgroupOf L) = Nat.card Q :=
        (Nat.card_congr eQ.toEquiv).symm
      simpa [hcard] using hsec.hA.A1.Q_even
    intro hbot
    have hcard_one : Nat.card (QH.subgroupOf L) = 1 :=
      (Subgroup.eq_bot_iff_card (H := QH.subgroupOf L)).1 hbot
    have hEven_one : Even 1 := by
      rw [← hcard_one]
      exact hQ_even_sub
    rcases hEven_one with ⟨n, hn⟩
    omega
  have hKH_ne : KH.subgroupOf L ≠ ⊥ := by
    obtain ⟨x, hxK, hxne⟩ :=
      proposition_1_b_K_nontrivial H D Q K V W Q0 S Q1 t hsec
    intro hbot
    let xH : H := ⟨x, hK_le_H hxK⟩
    have hxKH : xH ∈ KH := by
      simpa [KH, Subgroup.mem_subgroupOf] using hxK
    let xL : L := ⟨xH, (show KH ≤ L from le_sup_right) hxKH⟩
    have hxmem : xL ∈ KH.subgroupOf L := by
      exact hxKH
    have hxbot : xL ∈ (⊥ : Subgroup L) := by
      simpa [hbot] using hxmem
    have hxone : x = 1 := by
      simpa [xL, xH] using hxbot
    exact hxne hxone
  have hcent :
      ∀ x : KH.subgroupOf L, x ≠ 1 →
        elementCentralizerIn (QH.subgroupOf L) (x : L) = ⊥ := by
    intro x hxne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    rcases hy with ⟨hyQH, hycent⟩
    have hxKH : ((x : L) : H) ∈ KH := x.property
    have hxK : ((((x : L) : H) : G)) ∈ K := by
      simpa [KH, Subgroup.mem_subgroupOf] using hxKH
    have hxneG : ((((x : L) : H) : G)) ≠ 1 := by
      intro hxG
      apply hxne
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hxG
    have hyQH' : ((y : L) : H) ∈ QH := hyQH
    have hyQ : ((((y : L) : H) : G)) ∈ Q := by
      simpa [QH, Subgroup.mem_subgroupOf] using hyQH'
    have hcommL : Commute (y : L) (x : L) :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent
    have hcommG :
        ((((y : L) : H) : G)) * ((((x : L) : H) : G)) =
          ((((x : L) : H) : G)) * ((((y : L) : H) : G)) := by
      simpa using congrArg (fun z : L => ((z : H) : G)) hcommL.eq
    have hycentG : ((((y : L) : H) : G)) ∈
        Subgroup.centralizer ({((((x : L) : H) : G))} : Set G) := by
      exact Subgroup.mem_centralizer_singleton_iff.mpr hcommG
    have hbotG : ((((y : L) : H) : G)) ∈ (⊥ : Subgroup G) := by
      rw [← proposition_1_a H D Q K V W Q0 S Q1 t hsec
        ((((x : L) : H) : G)) hxK hxneG]
      exact ⟨hycentG, hyQ⟩
    apply Subtype.ext
    apply Subtype.ext
    exact (show (((y : L) : H) : G) = 1 from by simpa using hbotG)
  have hfrob :
      IsFrobeniusGroupWithKernelComplement (QH.subgroupOf L) (KH.subgroupOf L) := by
    exact
      (lemma_3_1 (K := QH.subgroupOf L) (R := KH.subgroupOf L)
        hQH_ne hKH_ne hQH_norm hcomp).2 hcent
  have hodd_KHsub : Odd (Nat.card (KH.subgroupOf L)) := by
    have hK_odd : Odd (Nat.card K) :=
      odd_of_card_dvd hsec.hA.A1.D_odd (Subgroup.card_dvd_of_le hsec.K_le_D)
    let eKH : K ≃* KH :=
      (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hK_le_H).symm
    let eL : KH ≃* KH.subgroupOf L :=
      (Subgroup.subgroupOfEquivOfLe (H := KH) (K := L) le_sup_right).symm
    let e : K ≃* KH.subgroupOf L := eKH.trans eL
    have hcard : Nat.card (KH.subgroupOf L) = Nat.card K :=
      (Nat.card_congr e.toEquiv).symm
    simpa [hcard] using hK_odd
  have hZ_KHsub : IsZGroup (KH.subgroupOf L) :=
    isZGroup_of_frobenius_complement_of_odd
      (K := QH.subgroupOf L) (R := KH.subgroupOf L) hfrob hodd_KHsub
  let eKH : K ≃* KH :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := H) hK_le_H).symm
  let eL : KH ≃* KH.subgroupOf L :=
    (Subgroup.subgroupOfEquivOfLe (H := KH) (K := L) le_sup_right).symm
  let e : K ≃* KH.subgroupOf L := eKH.trans eL
  letI : IsZGroup (KH.subgroupOf L) := hZ_KHsub
  exact IsZGroup.of_injective (f := e.toMonoidHom) e.injective

private theorem proposition_2_order_bound_of_isZGroup
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q))
    (hZ : IsZGroup K) :
    ∃ k : K, Nat.card K ≤ orderOf k := by
  classical
  letI : IsZGroup K := hZ
  letI : IsMulCommutative K :=
    proposition_2_K_isMulCommutative H D Q K V W Q0 S Q1 t hsec
  letI : CommGroup K := IsMulCommutative.instCommGroup
  letI : Group.IsNilpotent K := by infer_instance
  have hcyc : IsCyclic K := by infer_instance
  rcases (isCyclic_iff_exists_zpowers_eq_top (α := K)).1 hcyc with ⟨k, hk_top⟩
  refine ⟨k, ?_⟩
  have hcard : Nat.card (Subgroup.zpowers k) = Nat.card K := by
    rw [hk_top]
    simp
  exact le_of_eq (by simpa [Nat.card_zpowers] using hcard.symm)

private theorem proposition_2_D_normalized_by_t
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    t ∈ Subgroup.normalizer (D : Set G) := by
  have hA1 := hsec.hA.A1
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  rw [Subgroup.mem_normalizer_iff'']
  intro d
  constructor
  · intro hd
    simpa [rightConjugateElem, htinv] using
      (proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1 (d := d) hd)
  · intro hd
    have hmem :=
      proposition_2_rightConjugateElem_mem_D_of_mem_D H D Q t hA1
        (d := t⁻¹ * d * t) hd
    have htd : t * (t * d) = d := by
      calc
        t * (t * d) = (t * t) * d := by simp [mul_assoc]
        _ = 1 * d := by rw [htt]
        _ = d := by simp
    have hmem' : t * (t * d) ∈ D := by
      simpa [rightConjugateElem, htinv, htt, mul_assoc] using hmem
    simpa [htd] using hmem'

private theorem proposition_2_K_eq_inverted_closure_in_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    K.subgroupOf D =
      Subgroup.closure {x : D | rightConjugateElem (x : G) t = (x : G)⁻¹} := by
  apply le_antisymm
  · intro x hx
    apply Subgroup.subset_closure
    have hxK : (x : G) ∈ K := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact ((hsec.K_def (x : G)).mp hxK).2
  · rw [Subgroup.closure_le]
    intro x hx
    have hxK : (x : G) ∈ K :=
      (hsec.K_def (x : G)).mpr ⟨x.property, hx⟩
    simpa [Subgroup.mem_subgroupOf] using hxK

public theorem proposition_2
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t : G)
    (hsec : (_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
                            S ⊔ Q1 = Q)) :
    IsCyclic K ∧ (K.subgroupOf D).Normal := by
  constructor
  · rcases
      proposition_2_order_bound_of_isZGroup H D Q K V W Q0 S Q1 t hsec
        (proposition_2_K_isZGroup H D Q K V W Q0 S Q1 t hsec) with
      ⟨k, hk_order⟩
    refine isCyclic_iff_exists_zpowers_eq_top.2 ⟨k, ?_⟩
    apply (Subgroup.card_eq_iff_eq_top (H := Subgroup.zpowers k)).1
    rw [Nat.card_zpowers]
    exact le_antisymm
      (Nat.le_of_dvd (Nat.card_pos (α := K)) (orderOf_dvd_natCard k))
      hk_order
  · have hclosure_normal :
        (Subgroup.closure
          {x : D | rightConjugateElem (x : G) t = (x : G)⁻¹}).Normal := by
      simpa using
        (PFchapter1section1.lemma_b (M := G) t D hsec.hA.A1.involution_t
          hsec.hA.A1.D_odd
          (proposition_2_D_normalized_by_t H D Q K V W Q0 S Q1 t hsec))
    simpa [proposition_2_K_eq_inverted_closure_in_D H D Q K V W Q0 S Q1 t hsec]
      using hclosure_normal

end PFchapter1section2
end CFSG.BenderSuzuki
