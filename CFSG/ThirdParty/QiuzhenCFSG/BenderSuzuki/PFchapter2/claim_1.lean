module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_b
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section2
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (1)
-/

private theorem claim_1_exists_nontrivial_mem_of_subgroup_ne_bot
    {G : Type*} [Group G] (A : Subgroup G) (hA : A ≠ ⊥) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 := by
  by_contra hnone
  apply hA
  apply le_antisymm
  · intro x hxA
    have hx1 : x = 1 := by
      by_contra hxne
      exact hnone ⟨x, hxA, hxne⟩
    simp [hx1]
  · exact bot_le

private theorem claim_1_isMulCommutative_of_forall_sq_one
    {A : Type*} [Group A] (hA : ∀ x : A, x ^ 2 = 1) :
    IsMulCommutative A := by
  refine IsMulCommutative.mk <| Std.Commutative.mk ?_
  intro a b
  have hinv : ∀ x : A, x⁻¹ = x := by
    intro x
    have hx : x * x = 1 := by
      simpa [pow_two] using hA x
    calc
      x⁻¹ = x⁻¹ * 1 := by simp
      _ = x⁻¹ * (x * x) := by rw [hx]
      _ = x := by simp
  calc
    a * b = (a * b)⁻¹ := (hinv (a * b)).symm
    _ = b⁻¹ * a⁻¹ := by simp
    _ = b * a := by rw [hinv a, hinv b]

private theorem claim_1_exists_two_distinct_nontrivial_of_card_gt_two
    {A : Type*} [Group A] [Finite A] (hcard : 2 < Nat.card A) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : 2 < Fintype.card A := by
    simpa [Nat.card_eq_fintype_card] using hcard
  rcases Fintype.two_lt_card_iff.mp hcardF with ⟨a, b, c, hab, hac, hbc⟩
  by_cases ha : a = 1
  · by_cases hb : b = 1
    · exact False.elim (hab (ha.trans hb.symm))
    · by_cases hc : c = 1
      · exact False.elim (hac (ha.trans hc.symm))
      · exact ⟨b, c, hb, hc, hbc⟩
  · by_cases hb : b = 1
    · by_cases hc : c = 1
      · exact False.elim (hbc (hb.trans hc.symm))
      · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

private theorem claim_1_four_subgroup_card_of_exp_two
    {A : Type*} [Group A] [Finite A]
    (a b : A) (ha_ne : a ≠ 1) (hb_ne : b ≠ 1) (hab : a ≠ b)
    (hsq : ∀ x : A, x ^ 2 = 1) :
    ∃ E : Subgroup A, Nat.card E = 4 ∧ ∀ z : E, (z : E) ^ 2 = 1 := by
  classical
  have hcommInst : IsMulCommutative A :=
    claim_1_isMulCommutative_of_forall_sq_one hsq
  letI : IsMulCommutative A := hcommInst
  have hcomm : ∀ x y : A, x * y = y * x := fun x y =>
    (IsMulCommutative.is_comm (M := A)).comm x y
  have ha2 : a * a = 1 := by simpa [pow_two] using hsq a
  have hb2 : b * b = 1 := by simpa [pow_two] using hsq b
  have hba : b * a = a * b := hcomm b a
  have hab_ne_one : a * b ≠ 1 := by
    intro h
    have ha_eq_b : a = b := by
      calc
        a = a * 1 := by simp
        _ = a * (b * b) := by rw [hb2]
        _ = (a * b) * b := by group
        _ = b := by rw [h]; simp
    exact hab ha_eq_b
  have hab_ne_a : a * b ≠ a := by
    intro h
    apply hb_ne
    calc
      b = 1 * b := by simp
      _ = (a * a) * b := by rw [ha2]
      _ = a * (a * b) := by group
      _ = a * a := by rw [h]
      _ = 1 := ha2
  have hab_ne_b : a * b ≠ b := by
    intro h
    apply ha_ne
    calc
      a = a * 1 := by simp
      _ = a * (b * b) := by rw [hb2]
      _ = (a * b) * b := by group
      _ = b * b := by rw [h]
      _ = 1 := hb2
  let E : Subgroup A :=
    { carrier := {x : A | x = 1 ∨ x = a ∨ x = b ∨ x = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx1 | hxa | hxb | hxab <;>
          rcases hy with hy1 | hya | hyb | hyab
        · subst x
          subst y
          exact Or.inl (by simp)
        · subst x
          subst y
          exact Or.inr (Or.inl (by simp))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inl (by simp)))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inr (by simp)))
        · subst x
          subst y
          exact Or.inr (Or.inl (by simp))
        · subst x
          subst y
          exact Or.inl ha2
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inr rfl))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inl (by
            rw [← mul_assoc, ha2]
            simp)))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inl (by simp)))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inr hba))
        · subst x
          subst y
          exact Or.inl hb2
        · subst x
          subst y
          exact Or.inr (Or.inl (by
            calc
              b * (a * b) = (b * a) * b := by group
              _ = (a * b) * b := by rw [hba]
              _ = a * (b * b) := by group
              _ = a := by rw [hb2]; simp))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inr (by simp)))
        · subst x
          subst y
          exact Or.inr (Or.inr (Or.inl (by
            calc
              (a * b) * a = a * (b * a) := by group
              _ = a * (a * b) := by rw [hba]
              _ = (a * a) * b := by group
              _ = b := by rw [ha2]; simp)))
        · subst x
          subst y
          exact Or.inr (Or.inl (by
            calc
              (a * b) * b = a * (b * b) := by group
              _ = a := by rw [hb2]; simp))
        · subst x
          subst y
          exact Or.inl (by
            calc
              (a * b) * (a * b) = a * (b * a) * b := by group
              _ = a * (a * b) * b := by rw [hba]
              _ = (a * a) * (b * b) := by group
              _ = 1 := by rw [ha2, hb2]; simp)
      inv_mem' := by
        intro x hx
        have hx2 : x * x = 1 := by
          simpa [pow_two] using hsq x
        have hx_inv : x⁻¹ = x := by
          calc
            x⁻¹ = x⁻¹ * 1 := by simp
            _ = x⁻¹ * (x * x) := by rw [hx2]
            _ = x := by simp
        simpa [hx_inv] using hx }
  have hEcarrier :
      ∀ x : A, x ∈ ({1, a, b, a * b} : Finset A) ↔ x ∈ E := by
    intro x
    change x ∈ ({1, a, b, a * b} : Finset A) ↔
      (x = 1 ∨ x = a ∨ x = b ∨ x = a * b)
    simp
  have hfin_card : ({1, a, b, a * b} : Finset A).card = 4 := by
    simp [ha_ne.symm, hb_ne.symm, hab, hab_ne_one.symm, hab_ne_a.symm,
      hab_ne_b.symm]
  refine ⟨E, ?_, ?_⟩
  · let instE : Fintype E := Fintype.ofFinset ({1, a, b, a * b} : Finset A) hEcarrier
    have hcardF : @Fintype.card E instE = 4 := by
      simpa [hfin_card] using
        Fintype.card_ofFinset ({1, a, b, a * b} : Finset A) hEcarrier
    have hnat : Nat.card E = @Fintype.card E instE := by
      exact @Nat.card_eq_fintype_card E instE
    exact hnat.trans hcardF
  · intro z
    apply Subtype.ext
    exact hsq (z : A)

/-- A finite exponent-two subgroup of cardinality greater than two supplies a
rank-two subgroup in any ambient overgroup. -/
public theorem claim_1_rank_two_subgroup_of_large_exp_two_subgroup
    {G : Type*} [Group G] [Finite G] {Q0 C : Subgroup G}
    (hQ0_le_C : Q0 ≤ C) (hQ0_large : 2 < Nat.card Q0)
    (hQ0_sq : ∀ x : Q0, x ^ 2 = 1) :
    ∃ E : Subgroup C, Nat.card E = 4 ∧ ∀ z : E, (z : E) ^ 2 = 1 := by
  classical
  rcases claim_1_exists_two_distinct_nontrivial_of_card_gt_two hQ0_large with
    ⟨a, b, ha_ne, hb_ne, hab⟩
  rcases claim_1_four_subgroup_card_of_exp_two a b ha_ne hb_ne hab hQ0_sq with
    ⟨E0, hE0_card, hE0_sq⟩
  let ι : Q0 →* C := Subgroup.inclusion hQ0_le_C
  let E : Subgroup C := E0.map ι
  refine ⟨E, ?_, ?_⟩
  · have hι_inj : Function.Injective ι := Subgroup.inclusion_injective hQ0_le_C
    have hcard_map : Nat.card E = Nat.card E0 := by
      exact Subgroup.card_map_of_injective (K := E0) (f := ι) hι_inj
    simpa [E, hE0_card] using hcard_map
  · intro z
    apply Subtype.ext
    rcases Subgroup.mem_map.mp z.property with ⟨x, hxE0, hxz⟩
    have hx_sq_Q0 : x ^ 2 = 1 := by
      exact congrArg (fun y : E0 => (y : Q0)) (hE0_sq ⟨x, hxE0⟩)
    have hx_sq_C : (ι x) ^ 2 = 1 := by
      simpa using congrArg (fun y : Q0 => ι y) hx_sq_Q0
    simpa [E, hxz] using hx_sq_C

/-- The distinguished elementary abelian subgroup `Q0` has cardinality strictly
greater than two. -/
public theorem claim_1_Q0_card_gt_two
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
    2 < Nat.card Q0 := by
  classical
  rcases
      proposition_3_field_model_with_q0_card
        H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨field_n, _hn, _hQ0pow, _A, _hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, _q0_add, k_units, _vmodW_aut, _modelIso,
      hQ0card, _hrhoMul, _hrhoAut_inl, _hrhoAut_inr, _hrhoD,
      _hmodel_q, _hmodel_k, _hmodel_v, _hk_action, _hv_action⟩
  let F : Type := GaloisField 2 field_n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  rcases proposition_1_b_K_nontrivial H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨k, hkK, hk_ne⟩
  let kK : K := ⟨k, hkK⟩
  let u : Fˣ := k_units kK
  have hu_ne_one : u ≠ 1 := by
    intro hu
    have hu' : k_units kK = k_units 1 := by
      simpa [u] using hu
    have hkK_one : kK = 1 := k_units.injective hu'
    exact hk_ne (by simpa [kK] using congrArg Subtype.val hkK_one)
  have hF_card_gt_two : 2 < Nat.card F := by
    letI : Fintype F := Fintype.ofFinite F
    have hzero_one : (0 : F) ≠ 1 := zero_ne_one
    have hzero_u : (0 : F) ≠ (u : F) := by
      exact (Units.ne_zero u).symm
    have hone_u : (1 : F) ≠ (u : F) := by
      intro h
      exact hu_ne_one (Units.ext h.symm)
    have hcardF : 2 < Fintype.card F := by
      exact Fintype.two_lt_card_iff.mpr ⟨0, 1, (u : F), hzero_one, hzero_u, hone_u⟩
    simpa [Nat.card_eq_fintype_card] using hcardF
  have hQ0_nat_card : Nat.card Q0 = Nat.card Q0 := by
    exact Nat.card_coe_set_eq (Q0 : Set G)
  rw [hQ0_nat_card, hQ0card]
  exact hF_card_gt_two

/-- Every element of the distinguished elementary abelian subgroup `Q0` has
square one. -/
public theorem claim_1_Q0_sq
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
    ∀ x : Q0, x ^ 2 = 1 := by
  intro x
  apply Subtype.ext
  have hxQ0 : (x : G) ∈ Q0 := x.property
  rcases (hch.section3.section2.Q0_def (x : G)).mp hxQ0 with hx_one | hx_inv
  · simp [hx_one]
  · simpa using hx_inv.2.sq_eq_one

private theorem claim_1_Q0_inf_centralizer_P_card_eq_two
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
    Nat.card ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) = 2 := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let A : Subgroup G := Q0 ⊓ C
  rcases
      proposition_3_field_model_with_q0_card
        H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨field_n, _hn, _hQ0pow, _Afield, hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, q0_add, _k_units, vmodW_aut, _modelIso,
      _hQ0card, _hrhoMul, _hrhoAut_inl, _hrhoAut_inr, _hrhoD,
      _hmodel_q, _hmodel_k, _hmodel_v, _hk_action, hv_action⟩
  let F : Type := GaloisField 2 field_n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  letI : (W.subgroupOf V).Normal := hWnormalV
  let qOne : Q0 := q0_add.symm (Multiplicative.ofAdd (1 : F))
  have hqOne_ne_one : (qOne : G) ≠ 1 := by
    intro hq
    have hq_sub : qOne = 1 := by
      exact Subtype.ext hq
    have hmap := congrArg q0_add hq_sub
    have hone_zero : (1 : F) = 0 := by
      simp [qOne] at hmap
    exact one_ne_zero hone_zero
  have hqOne_C : (qOne : G) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxP
    let xV : V := ⟨x, hch.B1.P_le_V hxP⟩
    rcases hv_action xV qOne with ⟨hq_conj, hq_image⟩
    have hq_image' :
        q0_add ⟨rightConjugateElem (qOne : G) x, hq_conj⟩ = q0_add qOne := by
      simpa [qOne, xV] using hq_image
    have hfix :
        rightConjugateElem (qOne : G) x = (qOne : G) :=
      congrArg Subtype.val (q0_add.injective hq_image')
    calc
      x * (qOne : G) = x * rightConjugateElem (qOne : G) x := by rw [hfix]
      _ = (qOne : G) * x := by simp [rightConjugateElem, mul_assoc]
  let qOneA : A := ⟨(qOne : G), qOne.property, hqOne_C⟩
  have hqOneA_ne_one : qOneA ≠ 1 := by
    intro hq
    exact hqOne_ne_one (by simpa [qOneA] using congrArg Subtype.val hq)
  have htwo_le : 2 ≤ Nat.card A := by
    letI : Fintype A := Fintype.ofFinite A
    let f : Fin 2 → A := fun i => if i = 0 then 1 else qOneA
    have hf : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢
      · exact False.elim (hqOneA_ne_one hij.symm)
      · exact False.elim (hqOneA_ne_one hij)
    have hcard : Fintype.card (Fin 2) ≤ Fintype.card A :=
      Fintype.card_le_of_injective f hf
    simpa [Nat.card_eq_fintype_card] using hcard
  have hnot_two_lt : ¬ 2 < Nat.card A := by
    intro hgt
    have hsq : ∀ x : A, x ^ 2 = 1 := by
      intro x
      apply Subtype.ext
      have hx_sq_Q0 :
          (⟨(x : G), x.property.1⟩ : Q0) ^ 2 = 1 :=
        claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch ⟨(x : G), x.property.1⟩
      simpa using congrArg Subtype.val hx_sq_Q0
    rcases
      claim_1_rank_two_subgroup_of_large_exp_two_subgroup
        (G := G) (Q0 := A) (C := C) (show A ≤ C from inf_le_right) hgt hsq with
      ⟨E, hEcard, hEsq⟩
    exact hch.B1.centralizer_has_two_rank_one ⟨E, hEcard, hEsq⟩
  have hcardA : Nat.card A = 2 :=
    le_antisymm (Nat.le_of_not_gt hnot_two_lt) htwo_le
  simpa [A, C, Nat.card, Nat.card_coe_set_eq] using hcardA

private theorem claim_1_P_nontrivial_not_mem_centralizer_K
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
    ∀ x : G, x ∈ P → x ≠ 1 → x ∉ Subgroup.centralizer (K : Set G) := by
  intro x hxP hxne hxC
  have hxInf : x ∈ P ⊓ Subgroup.centralizer (K : Set G) := ⟨hxP, hxC⟩
  have hP_inf_bot : P ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    by_contra hne
    have htwo : TwoRankAtLeastTwo (Subgroup.centralizer (P : Set G)) := by
      rcases claim_1_exists_nontrivial_mem_of_subgroup_ne_bot
          (P ⊓ Subgroup.centralizer (K : Set G)) hne with
        ⟨u, hu, hune⟩
      have huP : u ∈ P := hu.1
      have huK : u ∈ Subgroup.centralizer (K : Set G) := hu.2
      have hrank :
          ∃ E : Subgroup (Subgroup.centralizer (P : Set G)),
            Nat.card E = 4 ∧ ∀ z : E, (z : E) ^ 2 = 1 := by
        have hP_le_W : P ≤ W := by
          have hP_le_CK : P ≤ Subgroup.centralizer (K : Set G) := by
            let C : Subgroup G := Subgroup.centralizer (K : Set G)
            let uP : P := ⟨u, huP⟩
            have huP_ne : uP ≠ 1 := by
              intro h
              exact hune (by simpa [uP] using congrArg Subtype.val h)
            have hPcard : Nat.card P = p := by
              simpa [Nat.card, Nat.card_coe_set_eq] using hch.B1.P_card
            haveI : Fact p.Prime := ⟨hch.B1.p_prime⟩
            have huC : uP ∈ C.comap P.subtype := by
              change (u : G) ∈ C
              exact huK
            have hzp_le : Subgroup.zpowers uP ≤ C.comap P.subtype :=
              (Subgroup.zpowers_le).2 huC
            intro y hyP
            let yP : P := ⟨y, hyP⟩
            have hy_z : yP ∈ Subgroup.zpowers uP :=
              mem_zpowers_of_prime_card hPcard huP_ne
            have hyC : yP ∈ C.comap P.subtype := hzp_le hy_z
            change (yP : G) ∈ C at hyC
            simpa [yP, C] using hyC
          intro y hyP
          have hyW' : y ∈ peterfalviW V (K : Set G) :=
            ⟨hch.B1.P_le_V hyP, hP_le_CK hyP⟩
          simpa [hch.section3.section2.W_eq] using hyW'
        exact
          claim_1_rank_two_subgroup_of_large_exp_two_subgroup
            (G := G) (Q0 := Q0) (C := Subgroup.centralizer (P : Set G))
            (by
              intro q hqQ0
              rw [Subgroup.mem_centralizer_iff]
              intro y hyP
              have hfix :
                  rightConjugateElem q y = q := by
                rcases
                    proposition_3_field_model_with_q0_card
                      H D Q K V W Q0 S Q1 t hch.section3.section2 with
                  ⟨field_n, _hn, _hQ0pow, _A, hWnormalV, _hWnormalD,
                    _rhoD, _rhoMul, _rhoAut, q0_add, _k_units, vmodW_aut,
                    _modelIso, _hQ0card, _hrhoMul, _hrhoAut_inl,
                    _hrhoAut_inr, _hrhoD, _hmodel_q, _hmodel_k,
                    _hmodel_v, _hk_action, hv_action⟩
                let F : Type := GaloisField 2 field_n
                letI : Field F := inferInstance
                letI : Finite F := inferInstance
                letI : (W.subgroupOf V).Normal := hWnormalV
                let yV : V := ⟨y, hch.section3.section2.W_le_V (hP_le_W hyP)⟩
                let qQ0 : Q0 := ⟨q, hqQ0⟩
                rcases hv_action yV qQ0 with ⟨hq_conj, hq_image⟩
                have hy_quot :
                    QuotientGroup.mk yV = (1 : V ⧸ W.subgroupOf V) := by
                  exact (QuotientGroup.eq_one_iff (N := W.subgroupOf V) yV).2 (by
                    change (yV : G) ∈ W
                    exact hP_le_W hyP)
                have hq_image' :
                    q0_add ⟨rightConjugateElem q y, hq_conj⟩ = q0_add qQ0 := by
                  rw [hq_image, hy_quot]
                  have hvone :
                      (vmodW_aut (1 : V ⧸ W.subgroupOf V) : F ≃+* F) = 1 :=
                    congrArg Subtype.val (map_one vmodW_aut)
                  rw [hvone]
                  change Multiplicative.ofAdd
                      (Multiplicative.toAdd (q0_add qQ0)) = q0_add qQ0
                  simp
                exact congrArg Subtype.val (q0_add.injective hq_image')
              calc
                y * q = y * (rightConjugateElem q y) := by rw [hfix]
                _ = q * y := by simp [rightConjugateElem, mul_assoc])
            (claim_1_Q0_card_gt_two H D Q K V W Q0 S Q1 P t s p hch)
            (claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch)
      simpa [TwoRankAtLeastTwo] using hrank
    exact hch.B1.centralizer_has_two_rank_one htwo
  have hxBot : x ∈ (⊥ : Subgroup G) := by
    simpa [hP_inf_bot] using hxInf
  exact hxne (by simpa using hxBot)

private theorem claim_1_W_inf_P_eq_bot
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
    W ⊓ P = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hxW : x ∈ W := hx.1
    have hxP : x ∈ P := hx.2
    have hxW' : x ∈ peterfalviW V (K : Set G) := by
      simpa [hch.section3.section2.W_eq] using hxW
    have hxC : x ∈ Subgroup.centralizer (K : Set G) := by
      simpa [peterfalviW] using hxW'.2
    have hx1 : x = 1 := by
      by_contra hxne
      exact (claim_1_P_nontrivial_not_mem_centralizer_K H D Q K V W Q0 S Q1 P t s p hch
        x hxP hxne) hxC
    rw [hx1]
    exact Subgroup.one_mem ⊥
  · exact bot_le

private theorem claim_1_P_ne_bot
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
    P ≠ ⊥ := by
  intro hP
  have hcard : Nat.card P = 1 := by
    simp [hP, Nat.card]
  exact hch.B1.p_prime.ne_one (hch.B1.P_card ▸ hcard)

private theorem claim_1_W_normalized_by_V
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
    ∀ h n : G, h ∈ V → n ∈ W → h * n * h⁻¹ ∈ W := by
  intro h n hhV hnW
  have hnW' : n ∈ peterfalviW V (K : Set G) := by
    simpa [hch.section3.section2.W_eq] using hnW
  have hnV : n ∈ V := hnW'.1
  have hnC : n ∈ Subgroup.centralizer (K : Set G) := hnW'.2
  have hmemV : h * n * h⁻¹ ∈ V :=
    V.mul_mem (V.mul_mem hhV hnV) (V.inv_mem hhV)
  have hD_le_normK : D ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hch.section3.section2.K_le_D).1
      (proposition_2 H D Q K V W Q0 S Q1 t hch.section3.section2).2
  have hh_norm : h ∈ Subgroup.normalizer (K : Set G) :=
    hD_le_normK (proposition_3_V_le_D H D Q K V W Q0 S Q1 t hch.section3.section2 hhV)
  have hh_inv_norm : h⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normalizer (K : Set G)).inv_mem hh_norm
  have hmemC : h * n * h⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hkK
    have hk' : h⁻¹ * k * h ∈ K := by
      simpa using ((Subgroup.mem_normalizer_iff.mp hh_inv_norm k).1 hkK)
    have hkn : (h⁻¹ * k * h) * n = n * (h⁻¹ * k * h) :=
      (Subgroup.mem_centralizer_iff.mp hnC) (h⁻¹ * k * h) hk'
    calc
      k * (h * n * h⁻¹) = h * ((h⁻¹ * k * h) * n) * h⁻¹ := by
        simp [mul_assoc]
      _ = h * (n * (h⁻¹ * k * h)) * h⁻¹ := by rw [hkn]
      _ = (h * n * h⁻¹) * k := by
        simp [mul_assoc]
  have hmemW' : h * n * h⁻¹ ∈ peterfalviW V (K : Set G) := ⟨hmemV, hmemC⟩
  simpa [hch.section3.section2.W_eq] using hmemW'

private theorem claim_1_P_image_eq_top_of_VmodW_card_eq_p
    {G : Type*} [Group G] [Finite G]
    (V W P : Subgroup G) (p : ℕ)
    (hP_le_V : P ≤ V)
    (hW_normal : (W.subgroupOf V).Normal)
    (hW_inf_P : W ⊓ P = ⊥)
    (hP_card : Nat.card P = p)
    (hquot_card : Nat.card (V ⧸ W.subgroupOf V) = p) :
    (P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)) = ⊤ := by
  classical
  haveI : (W.subgroupOf V).Normal := hW_normal
  let π : V →* V ⧸ W.subgroupOf V := QuotientGroup.mk' (W.subgroupOf V)
  let ι : P →* V := Subgroup.inclusion hP_le_V
  let φ : P →* V ⧸ W.subgroupOf V := π.comp ι
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hdivW : ι x / ι y ∈ W.subgroupOf V :=
      QuotientGroup.eq_iff_div_mem.mp hxy
    have hdivW_G : (x : G) * (y : G)⁻¹ ∈ W := by
      simpa [ι, Subgroup.inclusion, Subgroup.coe_mk, div_eq_mul_inv] using
        (Subgroup.mem_subgroupOf.mp hdivW)
    have hdivP_G : (x : G) * (y : G)⁻¹ ∈ P :=
      P.mul_mem x.property (P.inv_mem y.property)
    have hbot : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      simpa [hW_inf_P] using (show (x : G) * (y : G)⁻¹ ∈ W ⊓ P from
        ⟨hdivW_G, hdivP_G⟩)
    have hxyG : (x : G) * (y : G)⁻¹ = 1 := by
      simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp hxyG)
  have hcard_range : Nat.card φ.range = p := by
    have hP_nat : Nat.card P = p := by
      simpa [Nat.card, Nat.card_coe_set_eq] using hP_card
    have hcard : Nat.card P = Nat.card φ.range :=
      Nat.card_congr (Equiv.ofInjective φ hφ_inj)
    exact hcard.symm.trans hP_nat
  have hrange_top : φ.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard_range, hquot_card]
  have himage_eq_range : (P.subgroupOf V).map π = φ.range := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨xV, hxP, hxz⟩
      let xP : P := ⟨(xV : G), by
        simpa [Subgroup.mem_subgroupOf] using hxP⟩
      refine ⟨xP, ?_⟩
      simpa [φ, ι, π, xP, Subgroup.inclusion, Subgroup.coe_mk] using hxz
    · intro hz
      rcases hz with ⟨xP, rfl⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨ι xP, ?_, rfl⟩
      simp [ι, Subgroup.mem_subgroupOf]
  rw [himage_eq_range, hrange_top]

private theorem claim_1_ringAut_card_le_finrank_zmod_two
    (F : Type*) [Field F] [Finite F] [CharP F 2] [Module (ZMod 2) F] :
    Nat.card (F ≃+* F) ≤ Module.finrank (ZMod 2) F := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  letI : Algebra (ZMod 2) F := ZMod.algebraOfModule 2 F
  let toAlg : (F ≃+* F) → (F ≃ₐ[ZMod 2] F) := fun e =>
    AlgEquiv.ofRingEquiv (R := ZMod 2) (A₁ := F) (A₂ := F) (f := e) (by
      intro x
      have h :
          (e.toRingHom.comp (algebraMap (ZMod 2) F) :
              ZMod 2 →+* F) = algebraMap (ZMod 2) F :=
        RingHom.ext_zmod _ _
      exact DFunLike.congr_fun h x)
  have hinj : Function.Injective toAlg := by
    intro e₁ e₂ h
    ext x
    exact DFunLike.congr_fun h x
  calc
    Nat.card (F ≃+* F) ≤ Nat.card (F ≃ₐ[ZMod 2] F) :=
      Nat.card_le_card_of_injective toAlg hinj
    _ ≤ Module.finrank (ZMod 2) F := by
      simpa [Nat.card_eq_fintype_card] using (AlgEquiv.card_le (F := ZMod 2) (K := F))

private theorem claim_1_finrank_zmod_two_of_card_eq_two_pow
    (F : Type*) [Field F] [Finite F] [CharP F 2] [Module (ZMod 2) F] {p : ℕ}
    [Fact p.Prime] (hcard : Nat.card F = 2 ^ p) :
    Module.finrank (ZMod 2) F = p := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have hpow : 2 ^ Module.finrank (ZMod 2) F = 2 ^ p := by
    calc
      2 ^ Module.finrank (ZMod 2) F = Nat.card F :=
        FiniteField.pow_finrank_eq_natCard 2 F
      _ = 2 ^ p := hcard
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpow

private theorem claim_1_VmodW_card_eq_p_from_faithful_fieldAut
    {G : Type*} [Group G] [Finite G]
    (Q0 V W P : Subgroup G) (p : ℕ)
    (hP_le_V : P ≤ V)
    (hW_normal : (W.subgroupOf V).Normal)
    (hW_inf_P : W ⊓ P = ⊥)
    (hP_card : Nat.card P = p)
    (hp : Nat.Prime p)
    (F : Type) [Field F] [Finite F] (A : Subgroup (F ≃+* F))
    (vmodW_aut : V ⧸ W.subgroupOf V ≃* A)
    (hStarCommAut_inj : Function.Injective (fun σ : A => (σ : F ≃+* F)))
    (hQ0card : Nat.card Q0 = Nat.card F)
    (hQ0_card_pow : Nat.card Q0 = 2 ^ p) :
    Nat.card (V ⧸ W.subgroupOf V) = p := by
  classical
  haveI : (W.subgroupOf V).Normal := hW_normal
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite A := Finite.of_equiv (V ⧸ W.subgroupOf V) vmodW_aut.toEquiv
  let π : V →* V ⧸ W.subgroupOf V := QuotientGroup.mk' (W.subgroupOf V)
  let ι : P →* V := Subgroup.inclusion hP_le_V
  let φ : P →* A := vmodW_aut.toMonoidHom.comp (π.comp ι)
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have hq : π (ι x) = π (ι y) := vmodW_aut.injective hxy
    have hdivW : ι x / ι y ∈ W.subgroupOf V :=
      QuotientGroup.eq_iff_div_mem.mp hq
    have hdivW_G : (x : G) * (y : G)⁻¹ ∈ W := by
      simpa [ι, Subgroup.inclusion, Subgroup.coe_mk, div_eq_mul_inv] using
        (Subgroup.mem_subgroupOf.mp hdivW)
    have hdivP_G : (x : G) * (y : G)⁻¹ ∈ P :=
      P.mul_mem x.property (P.inv_mem y.property)
    have hbot : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
      simpa [hW_inf_P] using (show (x : G) * (y : G)⁻¹ ∈ W ⊓ P from
        ⟨hdivW_G, hdivP_G⟩)
    have hxyG : (x : G) * (y : G)⁻¹ = 1 := by
      simpa using hbot
    exact Subtype.ext (mul_inv_eq_one.mp hxyG)
  have hP_nat : Nat.card P = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hP_card
  have hp_le_A : p ≤ Nat.card A := by
    calc
      p = Nat.card P := hP_nat.symm
      _ ≤ Nat.card A := Nat.card_le_card_of_injective φ hφ_inj
  have hcardF : Nat.card F = 2 ^ p := hQ0card ▸ hQ0_card_pow
  have hchar : CharP F 2 := by
    letI : Fintype F := Fintype.ofFinite F
    apply charP_of_card_eq_prime_pow (R := F) (p := 2) (f := p)
    simpa [Nat.card_eq_fintype_card] using hcardF
  letI : CharP F 2 := hchar
  letI : Module (ZMod 2) F := { (ZMod.castHom dvd_rfl F : ZMod 2 →+* _).toModule with }
  letI : Algebra (ZMod 2) F := ZMod.algebraOfModule 2 F
  have hfinrank : Module.finrank (ZMod 2) F = p :=
    claim_1_finrank_zmod_two_of_card_eq_two_pow F hcardF
  have hA_le_p : Nat.card A ≤ p := by
    letI : Fintype F := Fintype.ofFinite F
    haveI : Finite (F ≃+* F) :=
      Finite.of_injective (fun e : F ≃+* F => (e : F → F)) (by
        intro e₁ e₂ h
        ext x
        exact congr_fun h x)
    calc
      Nat.card A ≤ Nat.card (F ≃+* F) :=
        Nat.card_le_card_of_injective (fun σ : A => (σ : F ≃+* F)) hStarCommAut_inj
      _ ≤ Module.finrank (ZMod 2) F :=
        claim_1_ringAut_card_le_finrank_zmod_two F
      _ = p := hfinrank
  have hA_card : Nat.card A = p := le_antisymm hA_le_p hp_le_A
  calc
    Nat.card (V ⧸ W.subgroupOf V) = Nat.card A :=
      Nat.card_congr vmodW_aut.toEquiv
    _ = p := hA_card

private theorem claim_1_VmodW_card_eq_p_obligation
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
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hW_normal : (W.subgroupOf V).Normal)
    (hQ0_card_pow : Nat.card Q0 = 2 ^ p) :
    Nat.card (V ⧸ W.subgroupOf V) = p := by
  classical
  rcases (proposition_3 H D Q K V W Q0 S Q1 t hch.section3.section2).1 with
    ⟨n, _hn, _hQ0pow, A, _hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, _q0_add, _k_units, vmodW_aut, _modelIso,
      hQ0card, _hdata⟩
  let F : Type := GaloisField 2 n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  have hStarCommAut_inj : Function.Injective (fun σ : A => (σ : F ≃+* F)) :=
    fun _ _ hστ => Subtype.ext hστ
  exact
    claim_1_VmodW_card_eq_p_from_faithful_fieldAut Q0 V W P p hch.B1.P_le_V
      hW_normal (claim_1_W_inf_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch)
      hch.B1.P_card hch.B1.p_prime F A vmodW_aut hStarCommAut_inj hQ0card
      hQ0_card_pow

private theorem claim_1_P_image_eq_top_in_VmodW
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
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hW_normal : (W.subgroupOf V).Normal)
    (hQ0_card_pow : Nat.card Q0 = 2 ^ p) :
    (P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)) = ⊤ := by
  have hquot_card :
      Nat.card (V ⧸ W.subgroupOf V) = p :=
    claim_1_VmodW_card_eq_p_obligation H D Q K V W Q0 S Q1 P t s p hch hW_normal
      hQ0_card_pow
  exact
    claim_1_P_image_eq_top_of_VmodW_card_eq_p V W P p hch.B1.P_le_V hW_normal
      (claim_1_W_inf_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch) hch.B1.P_card
      hquot_card

private theorem claim_1_W_sup_P_eq_V
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
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hQ0_card_pow : Nat.card Q0 = 2 ^ p) :
    W ⊔ P = V := by
  classical
  rcases (proposition_3 H D Q K V W Q0 S Q1 t hch.section3.section2).2 with
    ⟨hW_normal, _hcyc⟩
  haveI : (W.subgroupOf V).Normal := hW_normal
  have hP_image_top :
      (P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)) = ⊤ :=
    claim_1_P_image_eq_top_in_VmodW
      H D Q K V W Q0 S Q1 P t s p hch hW_normal hQ0_card_pow
  apply le_antisymm
  · exact sup_le hch.section3.section2.W_le_V hch.B1.P_le_V
  · intro x hxV
    let xV : V := ⟨x, hxV⟩
    have hxq :
        QuotientGroup.mk xV ∈
          (P.subgroupOf V).map (QuotientGroup.mk' (W.subgroupOf V)) := by
      rw [hP_image_top]
      simp
    rcases Subgroup.mem_map.mp hxq with ⟨pV, hpP, hpq⟩
    have hpP_G : (pV : G) ∈ P := by
      simpa using (Subgroup.mem_subgroupOf.mp hpP)
    have hx_div_p : xV / pV ∈ W.subgroupOf V := by
      exact QuotientGroup.eq_iff_div_mem.mp hpq.symm
    have hx_div_p_G : x * (pV : G)⁻¹ ∈ W := by
      simpa [xV, div_eq_mul_inv] using (Subgroup.mem_subgroupOf.mp hx_div_p)
    have hwp : x * (pV : G)⁻¹ ∈ W ⊔ P :=
      Subgroup.mem_sup_left hx_div_p_G
    have hp : (pV : G) ∈ W ⊔ P :=
      Subgroup.mem_sup_right hpP_G
    have hprod : (x * (pV : G)⁻¹) * (pV : G) ∈ W ⊔ P :=
      (W ⊔ P).mul_mem hwp hp
    simpa [mul_assoc] using hprod

private theorem claim_1_q0_card_obligation
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
    Nat.card Q0 = 2 ^ p := by
  classical
  have hfixed :
      Nat.card ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) = 2 :=
    claim_1_Q0_inf_centralizer_P_card_eq_two H D Q K V W Q0 S Q1 P t s p hch
  have hQ0_large : 2 < Nat.card Q0 :=
    claim_1_Q0_card_gt_two H D Q K V W Q0 S Q1 P t s p hch
  let Ctr : Subgroup G := Subgroup.centralizer (P : Set G)
  rcases
      proposition_3_field_model_with_q0_card
        H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨field_n, _hn, _hQ0pow, A, hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, q0_add, _k_units, vmodW_aut, _modelIso,
      hQ0card, _hrhoMul, _hrhoAut_inl, _hrhoAut_inr, _hrhoD,
      _hmodel_q, _hmodel_k, _hmodel_v, _hk_action, hv_action⟩
  let F : Type := GaloisField 2 field_n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  letI : (W.subgroupOf V).Normal := hWnormalV
  let pToV : P →* V := Subgroup.inclusion hch.B1.P_le_V
  let rho : P →* (F ≃+* F) :=
    A.subtype.comp
      (vmodW_aut.toMonoidHom.comp ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV))
  letI : MulSemiringAction P F := MulSemiringAction.compHom F rho
  let fixedEquiv : FixedPoints.subfield P F ≃ ↥(Q0 ⊓ Ctr) :=
    { toFun := fun x => by
        let q : Q0 := q0_add.symm (Multiplicative.ofAdd (x : F))
        refine ⟨(q : G), q.property, ?_⟩
        change (q : G) ∈ Ctr
        rw [Subgroup.mem_centralizer_iff]
        intro y hyP
        let yP : P := ⟨y, hyP⟩
        let yV : V := pToV yP
        rcases hv_action yV q with ⟨hq_conj, hq_image⟩
        have hfixF : rho yP (x : F) = (x : F) := by
          simpa [rho, MulAction.compHom_smul_def] using (x.property yP)
        have hStarComm :
            (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F)
                (Multiplicative.toAdd (q0_add q)) =
              Multiplicative.toAdd (q0_add q) := by
          simpa [rho, pToV, yP, yV, q] using hfixF
        have hStarCommInv :
            (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).symm
                (Multiplicative.toAdd (q0_add q)) =
              Multiplicative.toAdd (q0_add q) := by
          apply (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).injective
          simpa [yV, yP, pToV, Subgroup.inclusion] using hStarComm.symm
        have hq_image' :
            q0_add ⟨rightConjugateElem (q : G) y, hq_conj⟩ = q0_add q := by
          calc
            q0_add ⟨rightConjugateElem (q : G) y, hq_conj⟩ =
                Multiplicative.ofAdd ((vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).symm
                  (Multiplicative.toAdd (q0_add q))) := hq_image
            _ = Multiplicative.ofAdd (Multiplicative.toAdd (q0_add q)) := by rw [hStarCommInv]
            _ = q0_add q := by simp
        have hright : rightConjugateElem (q : G) y = (q : G) :=
          congrArg Subtype.val (q0_add.injective hq_image')
        calc
          y * (q : G) = y * rightConjugateElem (q : G) y := by rw [hright]
          _ = (q : G) * y := by simp [rightConjugateElem, mul_assoc]
      invFun := fun y => by
        let q : Q0 := ⟨(y : G), y.property.1⟩
        let a : F := Multiplicative.toAdd (q0_add q)
        refine ⟨a, ?_⟩
        change a ∈ MulAction.fixedPoints P F
        rw [MulAction.mem_fixedPoints]
        intro xP
        let xV : V := pToV xP
        rcases hv_action xV q with ⟨hq_conj, hq_image⟩
        have hright : rightConjugateElem (q : G) (xP : G) = (q : G) := by
          have hcomm : (xP : G) * (q : G) = (q : G) * (xP : G) :=
            (Subgroup.mem_centralizer_iff.mp y.property.2) (xP : G) xP.property
          calc
            rightConjugateElem (q : G) (xP : G) =
                (xP : G)⁻¹ * ((q : G) * (xP : G)) := by
              simp [rightConjugateElem, mul_assoc]
            _ = (xP : G)⁻¹ * ((xP : G) * (q : G)) := by rw [← hcomm]
            _ = (q : G) := by simp
        have hsymm :
            (vmodW_aut (QuotientGroup.mk xV) : F ≃+* F).symm a = a := by
          apply Multiplicative.ofAdd.injective
          calc
            Multiplicative.ofAdd
                ((vmodW_aut (QuotientGroup.mk xV) : F ≃+* F).symm a) =
                q0_add ⟨rightConjugateElem (q : G) (xP : G), hq_conj⟩ := by
              simpa [q, a, xV, pToV, Subgroup.inclusion] using hq_image.symm
            _ = q0_add q := by simp [hright]
            _ = Multiplicative.ofAdd a := by simp [a]
        change rho xP a = a
        change (vmodW_aut (QuotientGroup.mk xV) : F ≃+* F) a = a
        calc
          (vmodW_aut (QuotientGroup.mk xV) : F ≃+* F) a =
              (vmodW_aut (QuotientGroup.mk xV) : F ≃+* F)
                ((vmodW_aut (QuotientGroup.mk xV) : F ≃+* F).symm a) := by
            rw [hsymm]
          _ = a := (vmodW_aut (QuotientGroup.mk xV) : F ≃+* F).apply_symm_apply a
      left_inv := by
        intro x
        apply Subtype.ext
        show Multiplicative.toAdd
            (q0_add (q0_add.symm (Multiplicative.ofAdd (x : F)))) = (x : F)
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        show (q0_add.symm
            (Multiplicative.ofAdd
              (Multiplicative.toAdd (q0_add ⟨(y : G), y.property.1⟩))) : G) = (y : G)
        exact congrArg Subtype.val (by simp :
          q0_add.symm
              (Multiplicative.ofAdd
                (Multiplicative.toAdd (q0_add ⟨(y : G), y.property.1⟩))) =
            ⟨(y : G), y.property.1⟩) }
  have hfixed_card : Nat.card (FixedPoints.subfield P F) = 2 := by
    calc
      Nat.card (FixedPoints.subfield P F) = Nat.card ↥(Q0 ⊓ Ctr) :=
        Nat.card_congr fixedEquiv
      _ = Nat.card ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) := by
        simp [Ctr]
      _ = 2 := hfixed
  have hPcard : Nat.card P = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hch.B1.P_card
  haveI : Fact p.Prime := ⟨hch.B1.p_prime⟩
  have hrho_ker : ∀ x : P, rho x = 1 → x = 1 := by
    intro x hxrho
    by_contra hxne
    have hQ0_le_Ctr : Q0 ≤ Ctr := by
      intro q hqQ0
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      let qQ0 : Q0 := ⟨q, hqQ0⟩
      let yP : P := ⟨y, hyP⟩
      have hy_z : yP ∈ Subgroup.zpowers x :=
        mem_zpowers_of_prime_card hPcard hxne
      have hxker : x ∈ rho.ker := by
        simpa [MonoidHom.mem_ker] using hxrho
      have hker_le : Subgroup.zpowers x ≤ rho.ker := (Subgroup.zpowers_le).2 hxker
      have hyrho : rho yP = 1 := by
        have hyker : yP ∈ rho.ker := hker_le hy_z
        simpa [MonoidHom.mem_ker] using hyker
      let yV : V := pToV yP
      rcases hv_action yV qQ0 with ⟨hq_conj, hq_image⟩
      have hStarComm :
          (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F)
              (Multiplicative.toAdd (q0_add qQ0)) =
            Multiplicative.toAdd (q0_add qQ0) := by
        change rho yP (Multiplicative.toAdd (q0_add qQ0)) =
          Multiplicative.toAdd (q0_add qQ0)
        rw [hyrho]
        simp
      have hStarCommInv :
          (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).symm
              (Multiplicative.toAdd (q0_add qQ0)) =
            Multiplicative.toAdd (q0_add qQ0) := by
        apply (vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).injective
        simpa [yV, yP, pToV, Subgroup.inclusion] using hStarComm.symm
      have hq_image' :
          q0_add ⟨rightConjugateElem (qQ0 : G) y, hq_conj⟩ = q0_add qQ0 := by
        calc
          q0_add ⟨rightConjugateElem (qQ0 : G) y, hq_conj⟩ =
              Multiplicative.ofAdd ((vmodW_aut (QuotientGroup.mk yV) : F ≃+* F).symm
                (Multiplicative.toAdd (q0_add qQ0))) := hq_image
          _ = Multiplicative.ofAdd (Multiplicative.toAdd (q0_add qQ0)) := by rw [hStarCommInv]
          _ = q0_add qQ0 := by simp
      have hright : rightConjugateElem (qQ0 : G) y = (qQ0 : G) :=
        congrArg Subtype.val (q0_add.injective hq_image')
      calc
        y * q = y * rightConjugateElem (qQ0 : G) y := by rw [hright]
        _ = q * y := by simp [qQ0, rightConjugateElem, mul_assoc]
    have hQ0_inf_eq : Q0 ⊓ Ctr = Q0 := by
      apply le_antisymm
      · exact inf_le_left
      · intro q hq
        exact ⟨hq, hQ0_le_Ctr hq⟩
    have hQ0_card_eq_two : Nat.card Q0 = 2 := by
      have hsub : Nat.card Q0 = 2 := by
        simpa [Ctr, hQ0_inf_eq] using hfixed
      have hnat : Nat.card Q0 = Nat.card Q0 :=
        Nat.card_coe_set_eq (Q0 : Set G)
      exact hnat.trans hsub
    omega
  have hrho_inj : Function.Injective rho := by
    intro x y hxy
    have hker : rho (x * y⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy]
      simp
    have hxy1 : x * y⁻¹ = 1 := hrho_ker (x * y⁻¹) hker
    exact mul_inv_eq_one.mp hxy1
  have hfaithful : FaithfulSMul P F := by
    refine ⟨?_⟩
    intro x y hxy
    apply hrho_inj
    exact FaithfulSMul.eq_of_smul_eq_smul (fun a : F => by
      simpa [MulAction.compHom_smul_def] using hxy a)
  letI : Fintype P := Fintype.ofFinite P
  have hfinrank : Module.finrank (FixedPoints.subfield P F) F = p := by
    letI : FaithfulSMul P F := hfaithful
    have h := FixedPoints.finrank_eq_card P F
    have hcardP : Fintype.card P = p := by
      simpa [Nat.card_eq_fintype_card] using hPcard
    exact h.trans hcardP
  have hF_card : Nat.card F = 2 ^ p := by
    letI : FaithfulSMul P F := hfaithful
    calc
      Nat.card F = Nat.card (FixedPoints.subfield P F) ^
          Module.finrank (FixedPoints.subfield P F) F := by
        exact Module.natCard_eq_pow_finrank (K := FixedPoints.subfield P F) (V := F)
      _ = 2 ^ p := by rw [hfixed_card, hfinrank]
  exact hQ0card.trans hF_card

private theorem claim_1_semidirect_product
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
    W ≤ V ∧ P ≤ V ∧
      (∀ v w : G, v ∈ V → w ∈ W → v * w * v⁻¹ ∈ W) ∧
        Disjoint W P ∧ W ⊔ P = V := by
  have hW_inf_P := claim_1_W_inf_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch
  have hQ0_card_pow :
      Nat.card Q0 = 2 ^ p :=
    claim_1_q0_card_obligation H D Q K V W Q0 S Q1 P t s p hch
  exact
    ⟨hch.section3.section2.W_le_V, hch.B1.P_le_V,
      claim_1_W_normalized_by_V H D Q K V W Q0 S Q1 P t s p hch,
      by
        rw [disjoint_iff_inf_le]
        rw [hW_inf_P],
      claim_1_W_sup_P_eq_V H D Q K V W Q0 S Q1 P t s p hch hQ0_card_pow⟩

/-- Claim (1)'s fixed-point-free consequence for the action of `P` on `K`. -/
public theorem claim_1_K_inf_centralizer_P_eq_bot
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
    K ⊓ Subgroup.centralizer (P : Set G) = ⊥ := by
  classical
  let Ctr : Subgroup G := Subgroup.centralizer (P : Set G)
  let Ainf : Subgroup G := Q0 ⊓ Ctr
  have hfixed :
      Nat.card ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) = 2 :=
    claim_1_Q0_inf_centralizer_P_card_eq_two H D Q K V W Q0 S Q1 P t s p hch
  rcases
      proposition_3_field_model_with_q0_card
        H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨field_n, _hn, _hQ0pow, _A, hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, q0_add, k_units, _vmodW_aut, _modelIso,
      _hQ0card, _hrhoMul, _hrhoAut_inl, _hrhoAut_inr, _hrhoD,
      _hmodel_q, _hmodel_k, _hmodel_v, hk_action, hv_action⟩
  let F : Type := GaloisField 2 field_n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  letI : (W.subgroupOf V).Normal := hWnormalV
  let qOne : Q0 := q0_add.symm (Multiplicative.ofAdd (1 : F))
  have hqOne_ne_one : (qOne : G) ≠ 1 := by
    intro hq
    have hq_sub : qOne = 1 := Subtype.ext hq
    have hmap := congrArg q0_add hq_sub
    have hone_zero : (1 : F) = 0 := by
      simp [qOne] at hmap
    exact one_ne_zero hone_zero
  have hqOne_C : (qOne : G) ∈ Ctr := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hxP
    let xV : V := ⟨x, hch.B1.P_le_V hxP⟩
    rcases hv_action xV qOne with ⟨hq_conj, hq_image⟩
    have hq_image' :
        q0_add ⟨rightConjugateElem (qOne : G) x, hq_conj⟩ = q0_add qOne := by
      simpa [qOne, xV] using hq_image
    have hfix : rightConjugateElem (qOne : G) x = (qOne : G) :=
      congrArg Subtype.val (q0_add.injective hq_image')
    calc
      x * (qOne : G) = x * rightConjugateElem (qOne : G) x := by rw [hfix]
      _ = (qOne : G) * x := by simp [rightConjugateElem, mul_assoc]
  apply le_antisymm
  · intro k hk
    have hkK : k ∈ K := hk.1
    have hkC : k ∈ Ctr := by simpa [Ctr] using hk.2
    let kK : K := ⟨k, hkK⟩
    let u : Fˣ := k_units kK
    rcases hk_action kK qOne with ⟨hqU_Q0, hqU_image⟩
    let qU : Q0 := ⟨rightConjugateElem (qOne : G) k, hqU_Q0⟩
    have hqU_image_u_inv :
        q0_add qU = Multiplicative.ofAdd (↑(u⁻¹) : F) := by
      simpa [qU, qOne, u] using hqU_image
    have hqU_C : (qU : G) ∈ Ctr := by
      have hmem : k⁻¹ * (qOne : G) * k ∈ Ctr :=
        Ctr.mul_mem (Ctr.mul_mem (Ctr.inv_mem hkC) hqOne_C) hkC
      simpa [qU, rightConjugateElem, mul_assoc] using hmem
    let qOneA : Ainf := ⟨(qOne : G), qOne.property, hqOne_C⟩
    let qUA : Ainf := ⟨(qU : G), qU.property, hqU_C⟩
    have hqOneA_ne_one : qOneA ≠ 1 := by
      intro hq
      exact hqOne_ne_one (by simpa [qOneA] using congrArg Subtype.val hq)
    have hqUA_ne_one : qUA ≠ 1 := by
      intro hq
      have hqU_one_G : (qU : G) = 1 := by
        simpa [qUA] using congrArg Subtype.val hq
      have hqU_one : qU = 1 := Subtype.ext hqU_one_G
      have hqU_zero : q0_add qU = Multiplicative.ofAdd (0 : F) := by
        rw [hqU_one]
        simp
      have hu_zero_mult :
          Multiplicative.ofAdd (↑(u⁻¹) : F) = Multiplicative.ofAdd (0 : F) :=
        hqU_image_u_inv.symm.trans hqU_zero
      have hu_zero : (↑(u⁻¹) : F) = 0 :=
        Multiplicative.ofAdd.injective hu_zero_mult
      exact Units.ne_zero (u⁻¹) hu_zero
    have hcardA : Nat.card Ainf = 2 := by
      calc
        Nat.card Ainf = Nat.card ↥(Q0 ⊓ Subgroup.centralizer (P : Set G)) := by
          simp [Ainf, Ctr]
        _ = 2 := hfixed
    rcases (Nat.card_eq_two_iff' (1 : Ainf)).mp hcardA with ⟨z, _hz, hzuniq⟩
    have hqOne_z : qOneA = z := hzuniq qOneA hqOneA_ne_one
    have hqU_z : qUA = z := hzuniq qUA hqUA_ne_one
    have hqU_eq_qOne : qU = qOne := by
      apply Subtype.ext
      exact by simpa [qUA, qOneA] using congrArg Subtype.val (hqU_z.trans hqOne_z.symm)
    have hunit_inv_one_mult :
        Multiplicative.ofAdd (↑(u⁻¹) : F) = Multiplicative.ofAdd (1 : F) := by
      calc
        Multiplicative.ofAdd (↑(u⁻¹) : F) = q0_add qU := hqU_image_u_inv.symm
        _ = q0_add qOne := by rw [hqU_eq_qOne]
        _ = Multiplicative.ofAdd (1 : F) := by simp [qOne]
    have hu_inv_one : u⁻¹ = 1 :=
      Units.ext (Multiplicative.ofAdd.injective hunit_inv_one_mult)
    have hu_one : u = 1 := inv_eq_one.mp hu_inv_one
    have hkK_one : kK = 1 := k_units.injective (by simpa [u] using hu_one)
    have hk_one : k = 1 := by simpa [kK] using congrArg Subtype.val hkK_one
    simp [hk_one]
  · exact bot_le

private theorem claim_1_normalizer_eq_centralizer
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
    Subgroup.normalizer (P : Set G) = Subgroup.centralizer (P : Set G) := by
  have hP_ne : P ≠ ⊥ :=
    claim_1_P_ne_bot H D Q K V W Q0 S Q1 P t s p hch
  have hnormalizer :
      Subgroup.normalizer (P : Set G) =
        Subgroup.centralizer (P : Set G) ⊔
          (V ⊓ Subgroup.normalizer (P : Set G)) :=
    PFchapter1section3.proposition_1_b H D Q K V W Q0 S Q1 P t s hch.section3
      hP_ne hch.B1.P_le_V
  apply le_antisymm
  · intro x hx
    have hx_sup :
        x ∈ Subgroup.centralizer (P : Set G) ⊔
          (V ⊓ Subgroup.normalizer (P : Set G)) := by
      rw [← hnormalizer]
      exact hx
    have hV_norm_le :
        V ⊓ Subgroup.normalizer (P : Set G) ≤
          Subgroup.centralizer (P : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      let c : G := v * y * v⁻¹ * y⁻¹
      have hcW : c ∈ W := by
        rcases (proposition_3 H D Q K V W Q0 S Q1 t hch.section3.section2).2 with
          ⟨hW_normal, hcyc⟩
        let vV : V := ⟨v, hv.1⟩
        let yV : V := ⟨y, hch.B1.P_le_V hyP⟩
        haveI : (W.subgroupOf V).Normal := hW_normal
        haveI : IsCyclic (V ⧸ W.subgroupOf V) := hcyc
        have hquot_comm :
            Std.Commutative (α := V ⧸ W.subgroupOf V) (· * ·) :=
          inferInstance
        have hquot :
            (QuotientGroup.mk' (W.subgroupOf V) (vV * yV) :
                V ⧸ W.subgroupOf V) =
              QuotientGroup.mk' (W.subgroupOf V) (yV * vV) := by
          simpa using
            (hquot_comm.comm
              (QuotientGroup.mk' (W.subgroupOf V) vV)
              (QuotientGroup.mk' (W.subgroupOf V) yV))
        have hdiv :
            vV * yV / (yV * vV) ∈ W.subgroupOf V := by
          exact QuotientGroup.eq_iff_div_mem.mp hquot
        change ((vV * yV / (yV * vV) : V) : G) ∈ W at hdiv
        simpa [c, vV, yV, div_eq_mul_inv, mul_assoc] using hdiv
      have hvyvP : v * y * v⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp hv.2 y).1 hyP
      have hcP : c ∈ P := by
        exact P.mul_mem hvyvP (P.inv_mem hyP)
      have hcBot : c ∈ (⊥ : Subgroup G) := by
        simpa [claim_1_W_inf_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch]
          using (show c ∈ W ⊓ P from ⟨hcW, hcP⟩)
      have hc_one : c = 1 := by
        simpa using hcBot
      have hconj : v * y * v⁻¹ = y := by
        calc
          v * y * v⁻¹ = (v * y * v⁻¹ * y⁻¹) * y := by simp [mul_assoc]
          _ = y := by
            change c * y = y
            rw [hc_one]
            simp
      have hcomm : v * y = y * v := by
        calc
          v * y = (v * y * v⁻¹) * v := by simp [mul_assoc]
          _ = y * v := by rw [hconj]
      exact hcomm.symm
    exact (sup_le le_rfl hV_norm_le) hx_sup
  · exact centralizer_le_normalizer P

private theorem claim_1_P_le_centralizer_P
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
    P ≤ Subgroup.centralizer (P : Set G) := by
  intro x hxP
  rw [Subgroup.mem_centralizer_iff]
  intro y hyP
  have hPcard : Nat.card P = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hch.B1.P_card
  haveI : Fact p.Prime := ⟨hch.B1.p_prime⟩
  haveI : IsCyclic P := isCyclic_of_prime_card hPcard
  have hcomm : (⟨x, hxP⟩ : P) * ⟨y, hyP⟩ = ⟨y, hyP⟩ * ⟨x, hxP⟩ := by
    letI : CommGroup P :=
      { mul_comm := fun a b => (inferInstance : IsMulCommutative P).is_comm.comm a b }
    exact mul_comm _ _
  exact (congrArg Subtype.val hcomm).symm

private theorem claim_1_D_inf_centralizer_le_V_obligation
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
    D ⊓ Subgroup.centralizer (P : Set G) ≤ V := by
  let Ctr : Subgroup G := Subgroup.centralizer (P : Set G)
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hK_C_bot :
      K ⊓ Ctr = ⊥ := by
    simpa [Ctr] using
      claim_1_K_inf_centralizer_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch
  have hfactor :
      D ⊓ N ≤ (K ⊓ N) ⊔ (V ⊓ N) :=
    section1_normalizer_factorization_for_X_le_V
      H D Q K V W Q0 S Q1 P t s hch.section3 hch.B1.P_le_V
  have hKnorm_le_C :
      K ⊓ N ≤ Ctr :=
    k_inf_normalizer_le_centralizer_of_le_V
      H D Q K V W Q0 S Q1 P t s hch.section3 hch.B1.P_le_V
  have hKnorm_le_V : K ⊓ N ≤ V := by
    intro x hx
    have hxKC : x ∈ K ⊓ Ctr := ⟨hx.1, hKnorm_le_C hx⟩
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hK_C_bot] using hxKC
    have hx1 : x = 1 := by
      simpa using hxbot
    simp [hx1]
  have hsup_le_V : (K ⊓ N) ⊔ (V ⊓ N) ≤ V :=
    sup_le hKnorm_le_V inf_le_left
  intro x hx
  have hxN : x ∈ D ⊓ N := ⟨hx.1, centralizer_le_normalizer P hx.2⟩
  exact hsup_le_V (hfactor hxN)

private theorem claim_1_D_inf_centralizer_normalizes_W
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
    ∀ h a : G,
      h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
        a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
          h * a * h⁻¹ ∈ W := by
  intro h a hh ha
  exact
    claim_1_W_normalized_by_V H D Q K V W Q0 S Q1 P t s p hch h a
      (claim_1_D_inf_centralizer_le_V_obligation H D Q K V W Q0 S Q1 P t s p hch hh)
      ha.1

private theorem claim_1_D_inf_centralizer_normalizes_W_inf_centralizer
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
    ∀ h a : G,
      h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
        a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
          h * a * h⁻¹ ∈ W ⊓ Subgroup.centralizer (P : Set G) := by
  intro h a hh ha
  refine
    ⟨claim_1_D_inf_centralizer_normalizes_W H D Q K V W Q0 S Q1 P t s p hch h a hh ha,
      ?_⟩
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  change h * a * h⁻¹ ∈ C
  exact C.mul_mem (C.mul_mem hh.2 ha.2) (C.inv_mem hh.2)

private theorem claim_1_D_inf_centralizer_normalizes_P
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (_hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∀ h b : G,
      h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
        b ∈ P → h * b * h⁻¹ ∈ P := by
  intro h b hh hb
  have hconj : h * b * h⁻¹ = b := by
    have hcomm : b * h = h * b := (Subgroup.mem_centralizer_iff.mp hh.2) b hb
    calc
      h * b * h⁻¹ = b * h * h⁻¹ := by rw [← hcomm]
      _ = b := by simp
  simpa [hconj] using hb

private theorem claim_1_W_inf_centralizer_sup_P_eq_D_inf_centralizer
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
    (W ⊓ Subgroup.centralizer (P : Set G)) ⊔ P =
      D ⊓ Subgroup.centralizer (P : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hVleD : V ≤ D :=
    proposition_3_V_le_D H D Q K V W Q0 S Q1 t hch.section3.section2
  have hWleD : W ≤ D :=
    proposition_3_W_le_D H D Q K V W Q0 S Q1 t hch.section3.section2
  have hP_le_C := claim_1_P_le_centralizer_P H D Q K V W Q0 S Q1 P t s p hch
  apply le_antisymm
  · apply sup_le
    · intro x hx
      exact ⟨hWleD hx.1, hx.2⟩
    · intro x hx
      exact ⟨hVleD (hch.B1.P_le_V hx), hP_le_C hx⟩
  · intro x hx
    have hxV : x ∈ V :=
      claim_1_D_inf_centralizer_le_V_obligation H D Q K V W Q0 S Q1 P t s p hch hx
    let xV : V := ⟨x, hxV⟩
    rcases (proposition_3 H D Q K V W Q0 S Q1 t hch.section3.section2).2 with
      ⟨hW_normal, _hcyc⟩
    haveI : (W.subgroupOf V).Normal := hW_normal
    have hsup_top : W.subgroupOf V ⊔ P.subgroupOf V = ⊤ := by
      have hsub :
          (W ⊔ P).subgroupOf V = W.subgroupOf V ⊔ P.subgroupOf V :=
        Subgroup.subgroupOf_sup hch.section3.section2.W_le_V hch.B1.P_le_V
      rw [← hsub]
      rw [claim_1_W_sup_P_eq_V H D Q K V W Q0 S Q1 P t s p hch
        (claim_1_q0_card_obligation H D Q K V W Q0 S Q1 P t s p hch)]
      simp
    have hx_sup : xV ∈ W.subgroupOf V ⊔ P.subgroupOf V := by
      rw [hsup_top]
      exact (show xV ∈ (⊤ : Subgroup V) from by simp)
    rcases (Subgroup.mem_sup_of_normal_left.mp hx_sup) with
      ⟨wV, hwW, pV, hpP, hwp⟩
    have hwW_G : (wV : G) ∈ W := hwW
    have hpP_G : (pV : G) ∈ P := hpP
    have hwp_G : (wV : G) * (pV : G) = x := by
      simpa [xV] using congrArg Subtype.val hwp
    have hpC : (pV : G) ∈ C := by
      simpa [C] using hP_le_C hpP_G
    have hwC : (wV : G) ∈ C := by
      have hw_eq : (wV : G) = x * (pV : G)⁻¹ := by
        calc
          (wV : G) = ((wV : G) * (pV : G)) * (pV : G)⁻¹ := by
            simp [mul_assoc]
          _ = x * (pV : G)⁻¹ := by rw [hwp_G]
      have hxC : x ∈ C := by simpa [C] using hx.2
      simpa [hw_eq] using C.mul_mem hxC (C.inv_mem hpC)
    have hw_sup : (wV : G) ∈ (W ⊓ C) ⊔ P :=
      Subgroup.mem_sup_left ⟨hwW_G, hwC⟩
    have hp_sup : (pV : G) ∈ (W ⊓ C) ⊔ P :=
      Subgroup.mem_sup_right hpP_G
    have hprod : (wV : G) * (pV : G) ∈ (W ⊓ C) ⊔ P :=
      ((W ⊓ C) ⊔ P).mul_mem hw_sup hp_sup
    simpa [C, hwp_G] using hprod

private theorem claim_1_centralizer_direct_product
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
    (W ⊓ Subgroup.centralizer (P : Set G)) ≤
        (D ⊓ Subgroup.centralizer (P : Set G)) ∧
      P ≤ (D ⊓ Subgroup.centralizer (P : Set G)) ∧
        (∀ h a : G,
          h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
            a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
              h * a * h⁻¹ ∈ W ⊓ Subgroup.centralizer (P : Set G)) ∧
          (∀ h b : G,
            h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
              b ∈ P → h * b * h⁻¹ ∈ P) ∧
            Disjoint (W ⊓ Subgroup.centralizer (P : Set G)) P ∧
              (W ⊓ Subgroup.centralizer (P : Set G)) ⊔ P =
                D ⊓ Subgroup.centralizer (P : Set G) ∧
                ∀ a b : G,
                  a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
                    b ∈ P → a * b = b * a := by
  have hW_inf_P := claim_1_W_inf_P_eq_bot H D Q K V W Q0 S Q1 P t s p hch
  have hP_le_C := claim_1_P_le_centralizer_P H D Q K V W Q0 S Q1 P t s p hch
  exact
    ⟨by
        intro x hx
        exact ⟨proposition_3_W_le_D H D Q K V W Q0 S Q1 t hch.section3.section2 hx.1, hx.2⟩,
      by
        intro x hx
        exact ⟨proposition_3_V_le_D H D Q K V W Q0 S Q1 t hch.section3.section2 (hch.B1.P_le_V hx), hP_le_C hx⟩,
      claim_1_D_inf_centralizer_normalizes_W_inf_centralizer
        H D Q K V W Q0 S Q1 P t s p hch,
      claim_1_D_inf_centralizer_normalizes_P H D Q K V W Q0 S Q1 P t s p hch,
      by
        rw [disjoint_iff_inf_le]
        intro x hx
        have hxWP : x ∈ W ⊓ P := ⟨hx.1.1, hx.2⟩
        simpa [hW_inf_P] using hxWP,
      claim_1_W_inf_centralizer_sup_P_eq_D_inf_centralizer H D Q K V W Q0 S Q1 P t s p hch,
      by
        intro a b ha hb
        exact ((Subgroup.mem_centralizer_iff.mp ha.2) b hb).symm⟩

public theorem claim_1
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
    (W ≤ V ∧ P ≤ V ∧
      (∀ v w : G, v ∈ V → w ∈ W → v * w * v⁻¹ ∈ W) ∧
        Disjoint W P ∧ W ⊔ P = V) ∧ Nat.card Q0 = 2 ^ p ∧
      Subgroup.normalizer (P : Set G) = Subgroup.centralizer (P : Set G) ∧
        ((W ⊓ Subgroup.centralizer (P : Set G)) ≤
            (D ⊓ Subgroup.centralizer (P : Set G)) ∧
          P ≤ (D ⊓ Subgroup.centralizer (P : Set G)) ∧
            (∀ h a : G,
              h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
                a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
                  h * a * h⁻¹ ∈ W ⊓ Subgroup.centralizer (P : Set G)) ∧
              (∀ h b : G,
                h ∈ D ⊓ Subgroup.centralizer (P : Set G) →
                  b ∈ P → h * b * h⁻¹ ∈ P) ∧
                Disjoint (W ⊓ Subgroup.centralizer (P : Set G)) P ∧
                  (W ⊓ Subgroup.centralizer (P : Set G)) ⊔ P =
                    D ⊓ Subgroup.centralizer (P : Set G) ∧
                    ∀ a b : G,
                      a ∈ W ⊓ Subgroup.centralizer (P : Set G) →
                        b ∈ P → a * b = b * a) := by
  exact
    ⟨claim_1_semidirect_product H D Q K V W Q0 S Q1 P t s p hch,
      claim_1_q0_card_obligation H D Q K V W Q0 S Q1 P t s p hch,
      claim_1_normalizer_eq_centralizer H D Q K V W Q0 S Q1 P t s p hch,
      claim_1_centralizer_direct_product H D Q K V W Q0 S Q1 P t s p hch⟩

/-- The order of the Frobenius kernel `K` in the Claim (1) finite-field model. -/
public theorem claim_1_K_card_eq_mersenne
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
    Nat.card K = 2 ^ p - 1 := by
  rcases proposition_3_field_model_with_q0_card
      H D Q K V W Q0 S Q1 t hch.section3.section2 with
    ⟨n, hn, hQ0pow, _A, _hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, _q0_add, k_units, _vmodW_aut, _modelIso,
      _hQ0card, _hrhoMul, _hrhoAut_inl, _hrhoAut_inr, _hrhoD,
      _hmodel_q, _hmodel_k, _hmodel_v, _hk_action, _hv_action⟩
  let F : Type := GaloisField 2 n
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  have hn_eq_p : n = p :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      (hQ0pow.symm.trans
        (claim_1_q0_card_obligation H D Q K V W Q0 S Q1 P t s p hch))
  calc
    Nat.card K = Nat.card Fˣ := Nat.card_congr k_units.toEquiv
    _ = Nat.card F - 1 := by
      simpa only using (Nat.card_units (α := F))
    _ = 2 ^ n - 1 := by rw [GaloisField.card 2 n hn]
    _ = 2 ^ p - 1 := by rw [hn_eq_p]

end PFchapter2
end CFSG.BenderSuzuki
