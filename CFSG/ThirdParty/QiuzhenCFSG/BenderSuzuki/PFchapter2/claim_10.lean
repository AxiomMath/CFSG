module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_7
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Algebra.Field.MinimalAxioms

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

universe u v

/-!
# Peterfalvi, Part II, Chapter II, Claim (10)
-/

private theorem chapter2_claim10_fixed_field_order_or_nine
    {E : Type*} [Field E] [Finite E]
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP E ell] [Algebra (ZMod ell) E]
    (hunits : ∃ b : ℕ, Nat.card Eˣ = 2 ^ b) :
    Nat.card E = ell ∨ Nat.card E = 9 := by
  have hellPrime : Nat.Prime ell := Fact.out
  have hcard : ell ^ Module.finrank (ZMod ell) E = Nat.card E :=
    FiniteField.pow_finrank_eq_natCard ell E
  have ha : 0 < Module.finrank (ZMod ell) E := Module.finrank_pos
  obtain ⟨b, hb⟩ := hunits
  have hsucc : ell ^ Module.finrank (ZMod ell) E = 2 ^ b + 1 := by
    rw [hcard, Nat.card_eq_card_units_add_one, hb]
  by_cases hb0 : b = 0
  · have hpowTwo : ell ^ Module.finrank (ZMod ell) E = 2 := by
      simpa [hb0] using hsucc
    have hellDvdTwo : ell ∣ 2 := by
      rw [← hpowTwo]
      exact dvd_pow_self ell ha.ne'
    have hellTwo : ell = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hellDvdTwo with hellOne | hellTwo
      · exact False.elim (hellPrime.ne_one hellOne)
      · exact hellTwo
    have haOne : Module.finrank (ZMod ell) E = 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
      simpa [hellTwo] using hpowTwo
    left
    simpa [haOne] using hcard.symm
  · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
    rcases
        prime_power_successor_trichotomy
          hellPrime Nat.prime_two ha hbpos hsucc with
      hMersenne | hFermat | hNine
    · rcases hMersenne with ⟨hellTwo, _hbOne, _haPrime, htwo⟩
      have hpowThree : 2 ^ Module.finrank (ZMod ell) E = 3 := by omega
      have hpowEven : Even (2 ^ Module.finrank (ZMod ell) E) :=
        Nat.even_pow.mpr ⟨even_two, ha.ne'⟩
      rw [hpowThree] at hpowEven
      rcases hpowEven with ⟨k, hk⟩
      omega
    · left
      rcases hFermat with ⟨_htwo, haOne, _⟩
      simpa [haOne] using hcard.symm
    · right
      exact hcard.symm.trans hNine.1

private noncomputable def chapter2_claim10_ringAutToAlgAut
    {F : Type*} [Field F] (ell : ℕ) [Fact (Nat.Prime ell)]
    [CharP F ell] [Algebra (ZMod ell) F] :
    (F ≃+* F) →* (F ≃ₐ[ZMod ell] F) where
  toFun e := AlgEquiv.ofRingEquiv (R := ZMod ell) (A₁ := F) (A₂ := F) (f := e) (by
    intro x
    have h :
        (e.toRingHom.comp (algebraMap (ZMod ell) F) : ZMod ell →+* F) =
          algebraMap (ZMod ell) F :=
      RingHom.ext_zmod _ _
    exact DFunLike.congr_fun h x)
  map_one' := by
    ext x
    rfl
  map_mul' := by
    intro e₁ e₂
    ext x
    rfl

private theorem chapter2_claim10_ringAutToAlgAut_injective
    {F : Type*} [Field F] (ell : ℕ) [Fact (Nat.Prime ell)]
    [CharP F ell] [Algebra (ZMod ell) F] :
    Function.Injective (chapter2_claim10_ringAutToAlgAut (F := F) ell) := by
  intro e₁ e₂ h
  ext x
  exact DFunLike.congr_fun h x

private noncomputable def chapter2_claim10_sigmaAlgHom
    {A F : Type*} [Group A] [Field F]
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F]
    (rho : A →* (F ≃+* F)) :
    A →* (F ≃ₐ[ZMod ell] F) :=
  (chapter2_claim10_ringAutToAlgAut (F := F) ell).comp rho

private theorem chapter2_claim10_sigmaAlgHom_injective
    {A F : Type*} [Group A] [Field F]
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F]
    (rho : A →* (F ≃+* F)) (hrho : Function.Injective rho) :
    Function.Injective (chapter2_claim10_sigmaAlgHom ell rho) :=
  (chapter2_claim10_ringAutToAlgAut_injective (F := F) ell).comp hrho

private theorem chapter2_claim10_fixed_field_classification_of_local_control
    {A F : Type*} [Group A] [Finite A] [Field F] [Finite F]
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F]
    (rho : A →* (F ≃+* F)) (hrho : Function.Injective rho)
    (hAodd : Odd (Nat.card A)) (hA_ne_one : Nat.card A ≠ 1)
    (hell : ell = 3 ∨ ell = 5)
    (hlocal : ∀ a : A, a ≠ 1 →
      ∃ b : ℕ,
        Nat.card ((↥(IntermediateField.fixedField
          (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))))ˣ) = 2 ^ b) :
    Nat.Prime (Nat.card A) ∧
      (Nat.card F = 3 ^ Nat.card A ∨
        Nat.card F = 5 ^ Nat.card A ∨ Nat.card F = 9 ^ Nat.card A) := by
  classical
  let rhoAlg : A →* (F ≃ₐ[ZMod ell] F) :=
    chapter2_claim10_sigmaAlgHom ell rho
  have hrhoAlg : Function.Injective rhoAlg :=
    chapter2_claim10_sigmaAlgHom_injective ell rho hrho
  let : IsCyclic A := isCyclic_of_injective rhoAlg hrhoAlg
  have hAutCard :
      Nat.card (F ≃ₐ[ZMod ell] F) = Module.finrank (ZMod ell) F :=
    IsGalois.card_aut_eq_finrank (ZMod ell) F
  have hA_dvd_finrank : Nat.card A ∣ Module.finrank (ZMod ell) F := by
    rw [← hAutCard]
    exact Subgroup.card_dvd_of_injective rhoAlg hrhoAlg
  have hFpow : ell ^ Module.finrank (ZMod ell) F = Nat.card F :=
    FiniteField.pow_finrank_eq_natCard ell F
  have hdata (a : A) (ha : a ≠ 1) :
      orderOf a = Nat.card A ∧
        (Nat.card F = ell ^ Nat.card A ∨
          ell = 3 ∧ Nat.card F = 9 ^ Nat.card A) := by
    let Ha : Subgroup (F ≃ₐ[ZMod ell] F) := Subgroup.zpowers (rhoAlg a)
    let E : IntermediateField (ZMod ell) F := IntermediateField.fixedField Ha
    have hEunits : ∃ b : ℕ, Nat.card Eˣ = 2 ^ b := by
      simpa [rhoAlg, Ha, E] using hlocal a ha
    have hEorder : Nat.card E = ell ∨ Nat.card E = 9 :=
      chapter2_claim10_fixed_field_order_or_nine (E := E) ell hEunits
    have hrel : Module.finrank E F = orderOf a := by
      calc
        Module.finrank E F = Nat.card Ha := by
          simpa [E] using
            (IntermediateField.finrank_fixedField_eq_card (H := Ha))
        _ = orderOf (rhoAlg a) := by
          simpa [Ha] using (Nat.card_zpowers (rhoAlg a))
        _ = orderOf a := orderOf_injective rhoAlg hrhoAlg a
    have hEpow : ell ^ Module.finrank (ZMod ell) E = Nat.card E :=
      FiniteField.pow_finrank_eq_natCard ell E
    rcases hEorder with hEprime | hEnine
    · have hEfinrank : Module.finrank (ZMod ell) E = 1 := by
        apply Nat.pow_right_injective (Fact.out : Nat.Prime ell).two_le
        calc
          ell ^ Module.finrank (ZMod ell) E = Nat.card E := hEpow
          _ = ell := hEprime
          _ = ell ^ 1 := (pow_one ell).symm
      have hfinrankF : Module.finrank (ZMod ell) F = orderOf a := by
        calc
          Module.finrank (ZMod ell) F =
              Module.finrank (ZMod ell) E * Module.finrank E F :=
            (Module.finrank_mul_finrank (ZMod ell) E F).symm
          _ = 1 * orderOf a := by rw [hEfinrank, hrel]
          _ = orderOf a := one_mul _
      have hcard_dvd_order : Nat.card A ∣ orderOf a := by
        rw [← hfinrankF]
        exact hA_dvd_finrank
      have horder : orderOf a = Nat.card A :=
        Nat.dvd_antisymm (orderOf_dvd_natCard a) hcard_dvd_order
      refine ⟨horder, Or.inl ?_⟩
      calc
        Nat.card F = ell ^ Module.finrank (ZMod ell) F := hFpow.symm
        _ = ell ^ orderOf a := by rw [hfinrankF]
        _ = ell ^ Nat.card A := by rw [horder]
    · have hellDvdNine : ell ∣ 9 := by
        rw [← hEnine, ← hEpow]
        exact dvd_pow_self ell (Module.finrank_pos.ne')
      have hellThree : ell = 3 :=
        Nat.prime_eq_prime_of_dvd_pow
          (m := 2) (Fact.out : Nat.Prime ell) Nat.prime_three
            (by simpa using hellDvdNine)
      have hEfinrank : Module.finrank (ZMod ell) E = 2 := by
        apply Nat.pow_right_injective (Fact.out : Nat.Prime ell).two_le
        calc
          ell ^ Module.finrank (ZMod ell) E = Nat.card E := hEpow
          _ = 9 := hEnine
          _ = ell ^ 2 := by norm_num [hellThree]
      have hfinrankF : Module.finrank (ZMod ell) F = 2 * orderOf a := by
        calc
          Module.finrank (ZMod ell) F =
              Module.finrank (ZMod ell) E * Module.finrank E F :=
            (Module.finrank_mul_finrank (ZMod ell) E F).symm
          _ = 2 * orderOf a := by rw [hEfinrank, hrel]
      have hcard_dvd_two_order : Nat.card A ∣ 2 * orderOf a := by
        rw [← hfinrankF]
        exact hA_dvd_finrank
      have hcard_dvd_order : Nat.card A ∣ orderOf a := by
        apply (hAodd.coprime_two_right.dvd_mul_right).mp
        simpa [mul_comm] using hcard_dvd_two_order
      have horder : orderOf a = Nat.card A :=
        Nat.dvd_antisymm (orderOf_dvd_natCard a) hcard_dvd_order
      refine ⟨horder, Or.inr ⟨hellThree, ?_⟩⟩
      calc
        Nat.card F = ell ^ Module.finrank (ZMod ell) F := hFpow.symm
        _ = ell ^ (2 * orderOf a) := by rw [hfinrankF]
        _ = 3 ^ (2 * orderOf a) := by rw [hellThree]
        _ = 3 ^ (2 * Nat.card A) := by rw [horder]
        _ = (3 ^ 2) ^ Nat.card A := by rw [pow_mul]
        _ = 9 ^ Nat.card A := by norm_num
  have hA_one_lt : 1 < Nat.card A := by
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp hA_one_lt
  have hsimple : IsSimpleGroup A := by
    refine { eq_bot_or_eq_top_of_normal := ?_ }
    intro H _hHnormal
    by_cases hHbot : H = ⊥
    · exact Or.inl hHbot
    · right
      let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hHbot
      obtain ⟨a, ha⟩ := exists_ne (1 : H)
      have haA : (a : A) ≠ 1 := by
        intro hone
        apply ha
        apply Subtype.ext
        simpa using hone
      have horder : orderOf (a : A) = Nat.card A := (hdata (a : A) haA).1
      have hzp : Subgroup.zpowers (a : A) = ⊤ := by
        rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, horder]
      apply top_unique
      intro x hx
      have hxzp : x ∈ Subgroup.zpowers (a : A) := by
        rw [hzp]
        exact Subgroup.mem_top x
      exact (Subgroup.zpowers_le.mpr a.property) hxzp
  let : IsMulCommutative A :=
    IsCyclic.isMulCommutative
  have hAprime : Nat.Prime (Nat.card A) :=
    (Group.is_simple_iff_prime_card (α := A)).mp hsimple
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  rcases (hdata a ha).2 with hFieldEll | ⟨hellThree, hFieldNine⟩
  · rcases hell with hellThree | hellFive
    · exact ⟨hAprime, Or.inl (by simpa [hellThree] using hFieldEll)⟩
    · exact ⟨hAprime, Or.inr (Or.inl (by simpa [hellFive] using hFieldEll))⟩
  · exact ⟨hAprime, Or.inr (Or.inr hFieldNine)⟩


private theorem chapter2_claim10_nearField_commutative_of_unitEquiv
    {G F : Type*} [Group G] [PFAppendixII.RightNearField F]
    (Q P : Subgroup G) (unitEquiv : nearFieldStar Q P ≃* Fˣ)
    (hstar : IsMulCommutative (nearFieldStar Q P)) :
    IsMulCommutative F := by
  have hUnits : IsMulCommutative Fˣ := by
    let : IsMulCommutative (nearFieldStar Q P) := hstar
    refine ⟨⟨fun x y => ?_⟩⟩
    apply unitEquiv.symm.injective
    rw [map_mul, map_mul]
    exact (IsMulCommutative.is_comm (M := nearFieldStar Q P)).comm _ _
  let : IsMulCommutative Fˣ := hUnits
  refine ⟨⟨fun x y => ?_⟩⟩
  by_cases hx : x = 0
  · simp [hx]
  by_cases hy : y = 0
  · simp [hy]
  let ux : Fˣ := Units.mk0 x hx
  let uy : Fˣ := Units.mk0 y hy
  exact congrArg Units.val
    ((IsMulCommutative.is_comm (M := Fˣ)).comm ux uy)


/-- Checked characteristic restriction in the fixed-field argument.  This is
exactly the part supplied by the chapter induction hypothesis through Chapter I,
Proposition 1(c); it does not use the fixed-field coordinate transport. -/
private theorem chapter2_claim10_characteristic_three_or_five
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p ell : ℕ)
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hSigma_ne_one : Nat.card Sigma ≠ 1)
    (hEllOrder : ell = orderOf (s * t)) :
    ell = 3 ∨ ell = 5 := by
  classical
  have hWC_ne_one :
      Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) ≠ 1 := by
    rw [← hSigma]
    exact hSigma_ne_one
  have hWC_one_lt :
      1 < Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) := by
    have hpos :
        0 < Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) := Nat.card_pos
    omega
  let : Nontrivial ↥(W ⊓ Subgroup.centralizer (P : Set G)) :=
    Finite.one_lt_card_iff_nontrivial.mp hWC_one_lt
  obtain ⟨w, hw⟩ :=
    exists_ne (1 : ↥(W ⊓ Subgroup.centralizer (P : Set G)))
  let Xw : Subgroup G := Subgroup.zpowers (w : G)
  let CX : Subgroup G := Subgroup.centralizer (Xw : Set G)
  have hwG : (w : G) ≠ 1 := by
    intro hwOne
    apply hw
    apply Subtype.ext
    simpa using hwOne
  have hXw_ne : Xw ≠ ⊥ := by
    simpa [Xw] using (Subgroup.zpowers_ne_bot.mpr hwG)
  have hXw_le_W : Xw ≤ W := by
    exact Subgroup.zpowers_le.mpr w.property.1
  have hXw_le_V : Xw ≤ V :=
    hXw_le_W.trans hch.section3.section2.W_le_V
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
          hch.section3.section2.K_def hch.section3.section2.V_eq
          hch.section3.section2.W_eq
  have hQ0_le_CX : Q0 ≤ CX := by
    intro q hqQ0
    rw [Subgroup.mem_centralizer_iff]
    intro x hxXw
    have hxW : x ∈ W := hXw_le_W hxXw
    have hxCentralizer :
        x ∈ Subgroup.centralizer ({y : G | y ∈ H ∧ IsInvolution y}) := by
      rw [hWcentralizer] at hxW
      exact hxW.2
    rcases (hch.section3.section2.Q0_def q).mp hqQ0 with hq_one | hq_inv
    · subst q
      simp
    · exact ((Subgroup.mem_centralizer_iff.mp hxCentralizer) q hq_inv).symm
  have h2rank : TwoRankAtLeastTwo CX :=
    claim_1_rank_two_subgroup_of_large_exp_two_subgroup
      hQ0_le_CX
      (claim_1_Q0_card_gt_two H D Q K V W Q0 S Q1 P t s p hch)
      (claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch)
  have hprop :=
    PFchapter1section3.proposition_1_c
      H D Q K V W Q0 S Q1 Xw t s hch.section3 hind
        hXw_ne hXw_le_V h2rank
  dsimp only at hprop
  rcases hprop with
    ⟨_hCXQ1, _hNLF, _ell0, _hellpow, _hellgt, _hellcard, hcases⟩
  rcases hcases with hlinear | hquadratic | hcubic
  · rcases hlinear with ⟨_, _, _, _, horder, _, _⟩
    exact Or.inl (hEllOrder.trans horder)
  · rcases hquadratic with ⟨_, _, _, _, horder, _, _⟩
    exact Or.inr (hEllOrder.trans horder)
  · rcases hcubic with ⟨_, _, _, _, _, _, _, _, horder, _, _⟩
    exact Or.inl (hEllOrder.trans horder)

/-- Checked environment-group side of the local fixed-field argument: every
nontrivial quotient actor corresponds to an element of `W ∩ C_G(P)` whose
centralizer in `Q` is a 2-group. -/
private theorem chapter2_claim10_actor_centralizers_two_group
    {G : Type u} {Ω : Type v} {X : Type u}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [Group X] [Finite X]
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (A : Subgroup X)
    (e : A ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G))) :
    ∀ a : A, a ≠ 1 →
      IsPGroup 2 ↥(Subgroup.centralizer
        ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G) ⊓ Q) := by
  classical
  intro a ha
  let w : ↥(W ⊓ Subgroup.centralizer (P : Set G)) := e a
  let Xw : Subgroup G := Subgroup.zpowers (w : G)
  let CX : Subgroup G := Subgroup.centralizer (Xw : Set G)
  let R : Subgroup G := CX ⊓ Q
  have hw : w ≠ 1 := by
    intro hwOne
    apply ha
    apply e.injective
    simpa [w] using hwOne
  have hwG : (w : G) ≠ 1 := by
    intro hwOne
    apply hw
    apply Subtype.ext
    simpa using hwOne
  have hXw_ne : Xw ≠ ⊥ := by
    simpa [Xw] using (Subgroup.zpowers_ne_bot.mpr hwG)
  have hXw_le_W : Xw ≤ W :=
    Subgroup.zpowers_le.mpr w.property.1
  have hXw_le_V : Xw ≤ V :=
    hXw_le_W.trans hch.section3.section2.W_le_V
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    _root_.CFSG.BenderSuzuki.PFchapter1section2.peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
        H D Q K V W t hch.section3.section2.hA.A1
          hch.section3.section2.K_def hch.section3.section2.V_eq
          hch.section3.section2.W_eq
  have hQ0_le_CX : Q0 ≤ CX := by
    intro q hqQ0
    rw [Subgroup.mem_centralizer_iff]
    intro x hxXw
    have hxW : x ∈ W := hXw_le_W hxXw
    have hxCentralizer :
        x ∈ Subgroup.centralizer ({y : G | y ∈ H ∧ IsInvolution y}) := by
      rw [hWcentralizer] at hxW
      exact hxW.2
    rcases (hch.section3.section2.Q0_def q).mp hqQ0 with hq_one | hq_inv
    · subst q
      simp
    · exact ((Subgroup.mem_centralizer_iff.mp hxCentralizer) q hq_inv).symm
  have h2rank : TwoRankAtLeastTwo CX :=
    claim_1_rank_two_subgroup_of_large_exp_two_subgroup
      hQ0_le_CX
      (claim_1_Q0_card_gt_two H D Q K V W Q0 S Q1 P t s p hch)
      (claim_1_Q0_sq H D Q K V W Q0 S Q1 P t s p hch)
  have hprop :=
    PFchapter1section3.proposition_1_c
      H D Q K V W Q0 S Q1 Xw t s hch.section3 hind
        hXw_ne hXw_le_V h2rank
  dsimp only at hprop
  rcases hprop with
    ⟨_hCXQ1, _hNLF, _ell0, hellpow, _hellgt, _hellcard, hcases⟩
  rcases hellpow with ⟨n, hn⟩
  have hR_pgroup : IsPGroup 2 R := by
    rcases hcases with hlinear | hquadratic | hcubic
    · rcases hlinear with ⟨_, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n)
      simpa [R, CX, hn] using hcard
    · rcases hquadratic with ⟨_, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n * 2)
      simpa [R, CX, hn, pow_mul] using hcard
    · rcases hcubic with ⟨_, _, _, _, _, _, _, _, _, _, hcard⟩
      apply IsPGroup.of_card (n := n * 3)
      simpa [R, CX, hn, pow_mul] using hcard.1
  simpa [w, Xw, CX, R] using hR_pgroup


/-- In a Proposition-One model, the unit coordinate is normalized by the actor
coordinate, and its new field value is the semilinear actor image. -/
private theorem chapter2_claim10_proposition_one_unit_conjugation
    {X : Type u} {Ω F : Type v}
    [Group X] [Finite X] [MulAction X Ω] [Finite Ω]
    [PFAppendixII.RightNearField F]
    (H D Q : Subgroup X) (t : X)
    (hA1 : HypothesisA1 X Ω H D Q t)
    (addLift : F → X) (unitLift : Fˣ → X) (sigmaAct : D → F → F)
    (hcoordinates : Function.Bijective
      (fun z : F × Fˣ × D =>
        addLift z.1 * unitLift z.2.1 * (z.2.2 : X)))
    (hunitOne : unitLift 1 = 1)
    (hunitRange : ∀ q : X, q ∈ Q ↔ ∃ x : Fˣ, unitLift x = q)
    (hrightQ : ∀ a : F, ∀ x : Fˣ,
      PFAppendixIII.rightConjugateElem (addLift a) (unitLift x) =
        addLift (a * (x : F)))
    (hsigmaMaps : ∀ d : D, ∀ a b : F,
      sigmaAct d (a + b) = sigmaAct d a + sigmaAct d b ∧
        sigmaAct d (a * b) = sigmaAct d a * sigmaAct d b ∧
          sigmaAct d 1 = 1)
    (hrightD : ∀ d : D, ∀ a : F,
      PFAppendixIII.rightConjugateElem (addLift a) (d : X) =
        addLift (sigmaAct d a)) :
    ∀ (d : D) (x : Fˣ),
      ∃ y : Fˣ,
        (y : F) = sigmaAct d (x : F) ∧
          PFAppendixIII.rightConjugateElem (unitLift x) (d : X) = unitLift y := by
  classical
  intro d x
  have haddInjective : Function.Injective addLift := by
    intro a b hab
    have htriple : (a, (1 : Fˣ), (1 : D)) = (b, 1, 1) :=
      hcoordinates.1 (by simpa [hunitOne] using hab)
    exact congrArg (fun z : F × Fˣ × D => z.1) htriple
  have hxQ : unitLift x ∈ Q :=
    (hunitRange (unitLift x)).2 ⟨x, rfl⟩
  let dH : H := ⟨(d : X), hA1.D_le_H d.property⟩
  let qH : H := ⟨unitLift x, hA1.Q_le_H hxQ⟩
  have hqH : qH ∈ Q.subgroupOf H := by
    simpa [qH, Subgroup.mem_subgroupOf] using hxQ
  have hconjH := hA1.Q_normal_in_H.conj_mem qH hqH dH⁻¹
  have hconjQ :
      PFAppendixIII.rightConjugateElem (unitLift x) (d : X) ∈ Q := by
    simpa [PFAppendixIII.rightConjugateElem, dH, qH,
      Subgroup.mem_subgroupOf, mul_assoc] using hconjH
  obtain ⟨y, hy⟩ := (hunitRange
    (PFAppendixIII.rightConjugateElem (unitLift x) (d : X))).1 hconjQ
  have hconjAction :
      PFAppendixIII.rightConjugateElem (addLift 1)
          (PFAppendixIII.rightConjugateElem (unitLift x) (d : X)) =
        addLift (sigmaAct d (x : F)) := by
    calc
      PFAppendixIII.rightConjugateElem (addLift 1)
          (PFAppendixIII.rightConjugateElem (unitLift x) (d : X)) =
          PFAppendixIII.rightConjugateElem
            (PFAppendixIII.rightConjugateElem
              (PFAppendixIII.rightConjugateElem (addLift 1) ((d : X)⁻¹))
                (unitLift x)) (d : X) := by
            simp [PFAppendixIII.rightConjugateElem, mul_assoc]
      _ = PFAppendixIII.rightConjugateElem
          (PFAppendixIII.rightConjugateElem (addLift 1) (unitLift x))
            (d : X) := by
          have hone :
              PFAppendixIII.rightConjugateElem (addLift 1) ((d : X)⁻¹) =
                addLift 1 := by
            calc
              PFAppendixIII.rightConjugateElem (addLift 1) ((d : X)⁻¹) =
                  PFAppendixIII.rightConjugateElem (addLift 1) (d⁻¹ : X) := rfl
              _ = addLift (sigmaAct d⁻¹ 1) := hrightD d⁻¹ 1
              _ = addLift 1 := by rw [(hsigmaMaps d⁻¹ 1 1).2.2]
          rw [hone]
      _ = PFAppendixIII.rightConjugateElem
          (addLift (1 * (x : F))) (d : X) := by rw [hrightQ]
      _ = addLift (sigmaAct d (1 * (x : F))) := hrightD d _
      _ = addLift (sigmaAct d (x : F)) := by rw [one_mul]
  have hvalue : (y : F) = sigmaAct d (x : F) := by
    apply haddInjective
    calc
      addLift (y : F) =
          PFAppendixIII.rightConjugateElem (addLift 1) (unitLift y) := by
            simpa using (hrightQ (1 : F) y).symm
      _ = PFAppendixIII.rightConjugateElem (addLift 1)
          (PFAppendixIII.rightConjugateElem (unitLift x) (d : X)) := by rw [hy]
      _ = addLift (sigmaAct d (x : F)) := hconjAction
  exact ⟨y, hvalue, hy.symm⟩
/-- Checked quotient-map equivalence on a subgroup disjoint from the quotient
kernel, retaining its pointwise quotient computation. -/
private theorem chapter2_claim10_quotientMap_subgroup_equiv_of_disjoint
    {G : Type*} [Group G] (N Q : Subgroup G) [N.Normal]
    (hdis : Disjoint Q N) :
    ∃ e : Q ≃* Q.map (QuotientGroup.mk' N),
      ∀ q : Q, (e q : G ⧸ N) = QuotientGroup.mk' N q := by
  let pi : G →* G ⧸ N := QuotientGroup.mk' N
  let f : Q →* Q.map pi :=
    (pi.domRestrict Q).codRestrict (Q.map pi) (fun q => ⟨q, q.2, rfl⟩)
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hpi : pi (x : G) = pi (y : G) := by
      have hxy' := congrArg Subtype.val hxy
      change pi (x : G) = pi (y : G) at hxy'
      exact hxy'
    have hdivN : (x : G) / (y : G) ∈ N :=
      QuotientGroup.eq_iff_div_mem.mp hpi
    have hdivQ : (x : G) / (y : G) ∈ Q := Q.div_mem x.2 y.2
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdis) hdivQ hdivN
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hf_surjective : Function.Surjective f := by
    intro z
    rcases z.2 with ⟨g, hgQ, hg⟩
    refine ⟨⟨g, hgQ⟩, ?_⟩
    apply Subtype.ext
    change pi g = (z : G ⧸ N)
    exact hg
  let e : Q ≃* Q.map pi := MulEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  refine ⟨e, ?_⟩
  intro q
  change pi (q : G) = (QuotientGroup.mk' N) (q : G)
  rfl

/-- Checked Proposition-One unit-coordinate equivalence, retaining the exact
underlying `unitLift` formula. -/
private theorem chapter2_claim10_proposition_one_units_equiv
    {G : Type u} {F : Type v} [Group G] [PFAppendixII.RightNearField F]
    (D Q : Subgroup G)
    (addLift : F → G) (unitLift : Fˣ → G)
    (hcoordinates : Function.Bijective
      (fun z : F × Fˣ × D => addLift z.1 * unitLift z.2.1 * (z.2.2 : G)))
    (haddZero : addLift 0 = 1)
    (hunitOne : unitLift 1 = 1)
    (hunitMul : ∀ x y : Fˣ, unitLift (x * y) = unitLift x * unitLift y)
    (hunitRange : ∀ q : G, q ∈ Q ↔ ∃ x : Fˣ, unitLift x = q) :
    ∃ e : Fˣ ≃* Q, ∀ x : Fˣ, (e x : G) = unitLift x := by
  let unitHom : Fˣ →* G :=
    { toFun := unitLift
      map_one' := hunitOne
      map_mul' := hunitMul }
  have hunit_mem (x : Fˣ) : unitHom x ∈ Q :=
    (hunitRange (unitHom x)).2 ⟨x, rfl⟩
  let unitHomQ : Fˣ →* Q := unitHom.codRestrict Q hunit_mem
  have hunit_injective : Function.Injective unitHomQ := by
    intro x y hxy
    have hxyG : unitLift x = unitLift y := by
      simpa [unitHomQ, unitHom] using congrArg Subtype.val hxy
    let tx : F × Fˣ × D := (0, x, 1)
    let ty : F × Fˣ × D := (0, y, 1)
    have htriple : tx = ty := hcoordinates.1 (by
      simpa [tx, ty, haddZero] using hxyG)
    exact congrArg (fun z : F × Fˣ × D => z.2.1) htriple
  have hunit_surjective : Function.Surjective unitHomQ := by
    intro q
    rcases (hunitRange (q : G)).1 q.property with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    simpa [unitHomQ, unitHom] using hx
  let e : Fˣ ≃* Q :=
    MulEquiv.ofBijective unitHomQ ⟨hunit_injective, hunit_surjective⟩
  refine ⟨e, ?_⟩
  intro x
  rfl
private theorem chapter2_claim10_fixed_unit_image_mem_actor_centralizer
    {G : Type u} {X : Type u} {F : Type v}
    [Group G] [Finite G] [Group X] [Finite X]
    [Field F] [Finite F]
    (Q W P : Subgroup G) (A : Subgroup X)
    (rho : A →* (F ≃+* F))
    (toStar : Fˣ →* nearFieldStar Q P)
    (e : A ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinateConj : ∀ (a : A) (y : Fˣ),
      PFAppendixIII.rightConjugateElem
          ((toStar y : nearFieldStar Q P) : G) (e a : G) =
        ((toStar (Units.map (rho a⁻¹).toRingHom y) : nearFieldStar Q P) : G))
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F] :
    ∀ (a : A) (_ha : a ≠ 1)
      (x : (↥(IntermediateField.fixedField
        (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))))ˣ),
      ((toStar (Units.map
        (IntermediateField.fixedField
          (Subgroup.zpowers
            (chapter2_claim10_sigmaAlgHom ell rho a))).val.toRingHom x) :
          nearFieldStar Q P) : G) ∈
        Subgroup.centralizer
          ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G) := by
  classical
  intro a _ha x
  let rhoAlg : A →* (F ≃ₐ[ZMod ell] F) :=
    chapter2_claim10_sigmaAlgHom ell rho
  let E : IntermediateField (ZMod ell) F :=
    IntermediateField.fixedField (Subgroup.zpowers (rhoAlg a))
  let inclUnits : Eˣ →* Fˣ := Units.map E.val.toRingHom
  let y : Fˣ := inclUnits x
  let q : G := ((toStar y : nearFieldStar Q P) : G)
  have hxmem : ((x : E) : F) ∈ E := (x : E).property
  have hinvMem : rhoAlg a⁻¹ ∈ Subgroup.zpowers (rhoAlg a) := by
    have h :=
      (Subgroup.zpowers (rhoAlg a)).inv_mem (Subgroup.mem_zpowers (rhoAlg a))
    rw [map_inv]
    exact h
  have hfixedAlg : rhoAlg a⁻¹ ((x : E) : F) = ((x : E) : F) := by
    rw [IntermediateField.mem_fixedField_iff] at hxmem
    exact hxmem _ hinvMem
  have hfixed : rho a⁻¹ ((x : E) : F) = ((x : E) : F) := by
    simpa [rhoAlg, chapter2_claim10_sigmaAlgHom,
      chapter2_claim10_ringAutToAlgAut] using hfixedAlg
  have hyfixed : Units.map (rho a⁻¹).toRingHom y = y := by
    apply Units.ext
    simpa [y, inclUnits] using hfixed
  have hconj := hcoordinateConj a y
  rw [hyfixed] at hconj
  change q ∈ Subgroup.centralizer
    ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G)
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    Subgroup.mem_centralizer_singleton_iff]
  have hconjQ : PFAppendixIII.rightConjugateElem q (e a : G) = q := by
    simpa [q] using hconj
  calc
    q * (e a : G) = (e a : G) * PFAppendixIII.rightConjugateElem q (e a : G) := by
      simp [PFAppendixIII.rightConjugateElem, mul_assoc]
    _ = (e a : G) * q := by rw [hconjQ]

/-- Checked construction of the fixed-unit embedding from pointwise coordinate
control. -/
private theorem chapter2_claim10_fixed_units_embedding_actor_centralizer
    {G : Type u} {X : Type u} {F : Type v}
    [Group G] [Finite G] [Group X] [Finite X]
    [Field F] [Finite F]
    (Q W P : Subgroup G) (A : Subgroup X)
    (rho : A →* (F ≃+* F))
    (toStar : Fˣ →* nearFieldStar Q P) (htoStar : Function.Injective toStar)
    (e : A ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinateConj : ∀ (a : A) (y : Fˣ),
      PFAppendixIII.rightConjugateElem
          ((toStar y : nearFieldStar Q P) : G) (e a : G) =
        ((toStar (Units.map (rho a⁻¹).toRingHom y) : nearFieldStar Q P) : G))
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F] :
    ∀ a : A, a ≠ 1 →
      ∃ f :
        ((↥(IntermediateField.fixedField
          (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))))ˣ) →*
            ↥(Subgroup.centralizer
              ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G) ⊓ Q),
        Function.Injective f := by
  intro a ha
  let E : IntermediateField (ZMod ell) F :=
    IntermediateField.fixedField
      (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))
  let inclUnits : Eˣ →* Fˣ := Units.map E.val.toRingHom
  let toStarE : Eˣ →* nearFieldStar Q P := toStar.comp inclUnits
  let C : Subgroup G :=
    Subgroup.centralizer
      ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G) ⊓ Q
  have hmem (x : Eˣ) : ((toStarE x : nearFieldStar Q P) : G) ∈ C := by
    refine ⟨?_, (toStarE x).property.1⟩
    simpa [E, inclUnits, toStarE] using
      chapter2_claim10_fixed_unit_image_mem_actor_centralizer
        Q W P A rho toStar e hcoordinateConj ell a ha x
  let f : Eˣ →* C :=
    ((nearFieldStar Q P).subtype.comp toStarE).codRestrict C hmem
  refine ⟨f, ?_⟩
  have hinclUnits : Function.Injective inclUnits :=
    Units.map_injective E.val.injective
  have htoStarE : Function.Injective toStarE := htoStar.comp hinclUnits
  intro x y hxy
  apply htoStarE
  apply Subtype.ext
  have hxy' := congrArg Subtype.val hxy
  change ((nearFieldStar Q P).subtype (toStarE x) : G) =
      ((nearFieldStar Q P).subtype (toStarE y) : G) at hxy'
  exact hxy'

/-- Checked cardinal consequence of the fixed-unit coordinate embedding. -/
private theorem chapter2_claim10_fixed_units_card_dvd_actor_centralizer
    {G : Type u} {X : Type u} {F : Type v}
    [Group G] [Finite G] [Group X] [Finite X]
    [Field F] [Finite F]
    (Q W P : Subgroup G) (A : Subgroup X)
    (rho : A →* (F ≃+* F))
    (toStar : Fˣ →* nearFieldStar Q P) (htoStar : Function.Injective toStar)
    (e : A ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinateConj : ∀ (a : A) (y : Fˣ),
      PFAppendixIII.rightConjugateElem
          ((toStar y : nearFieldStar Q P) : G) (e a : G) =
        ((toStar (Units.map (rho a⁻¹).toRingHom y) : nearFieldStar Q P) : G))
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F] :
    ∀ a : A, a ≠ 1 →
      Nat.card ((↥(IntermediateField.fixedField
        (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))))ˣ) ∣
        Nat.card ↥(Subgroup.centralizer
          ((Subgroup.zpowers (e a : G) : Subgroup G) : Set G) ⊓ Q) := by
  intro a ha
  obtain ⟨f, hf⟩ :=
    chapter2_claim10_fixed_units_embedding_actor_centralizer
      Q W P A rho toStar htoStar e hcoordinateConj ell a ha
  exact Subgroup.card_dvd_of_injective f hf
/-- Checked local fixed-field control assembled from the environment 2-group
calculation and the checked coordinate-compatibility construction. -/
private theorem chapter2_claim10_fixed_field_units_local_control
    {G : Type u} {Ω : Type v} {X : Type u} {F : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [Group X] [Finite X]
    [Field F] [Finite F]
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (A : Subgroup X)
    (rho : A →* (F ≃+* F))
    (toStar : Fˣ →* nearFieldStar Q P) (htoStar : Function.Injective toStar)
    (e : A ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G)))
    (hcoordinateConj : ∀ (a : A) (y : Fˣ),
      PFAppendixIII.rightConjugateElem
          ((toStar y : nearFieldStar Q P) : G) (e a : G) =
        ((toStar (Units.map (rho a⁻¹).toRingHom y) : nearFieldStar Q P) : G))
    (ell : ℕ) [Fact (Nat.Prime ell)] [CharP F ell] [Algebra (ZMod ell) F] :
    ∀ a : A, a ≠ 1 →
      ∃ b : ℕ,
          Nat.card ((↥(IntermediateField.fixedField
            (Subgroup.zpowers (chapter2_claim10_sigmaAlgHom ell rho a))))ˣ) = 2 ^ b := by
  have hcentralizer :=
    chapter2_claim10_actor_centralizers_two_group
      H D Q K V W Q0 S Q1 P t s p hch hind A e
  intro a ha
  have hdvd :=
    chapter2_claim10_fixed_units_card_dvd_actor_centralizer
      Q W P A rho toStar htoStar e hcoordinateConj ell a ha
  obtain ⟨n, hn⟩ := (hcentralizer a ha).exists_card_eq
  rw [hn] at hdvd
  obtain ⟨b, _hb_le, hcard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨b, hcard⟩

/-- The fixed-field classification used in Chapter II Claims (8) and (10),
with the chapter induction hypothesis made explicit. -/
public theorem chapter2_fixed_field_orders_of_Q1_ne_bot
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p : ℕ)
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm : IsMulCommutative (nearFieldStar Q P))
    (hSigma_ne_one : Nat.card Sigma ≠ 1) :
    Nat.Prime (Nat.card Sigma) ∧
      (Nat.card (nearFieldStar Q P) + 1 = 3 ^ Nat.card Sigma ∨
        Nat.card (nearFieldStar Q P) + 1 = 5 ^ Nat.card Sigma ∨
        Nat.card (nearFieldStar Q P) + 1 = 9 ^ Nat.card Sigma) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let OmegaP : Type v := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
  let : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let core : Subgroup C := pointStabilizerCore C OmegaP
  let N : Subgroup G :=
    D ⊓ Subgroup.centralizer
      ((Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) ⊓
        Subgroup.centralizer (P : Set G)
  have h7 :=
    claim_7 H D Q K V W Q0 S Q1 P N t s p hch hind rfl
  dsimp only at h7
  rcases h7 with ⟨hnormal7, hNP, eSigma⟩
  let : core.Normal := hnormal7
  obtain ⟨eSigma, heSigma⟩ := eSigma
  have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
  dsimp only at h2b
  rcases h2b with
    ⟨hNcore, _hnormal2b, _quotientAction, _hsmul, hAbar,
      F, hF, hFfinite, hFnontrivial, _unitEquiv, hPO, hcharacteristic⟩
  let : core.Normal := hnormal7
  let : PFAppendixII.RightNearField F := hF
  let : Finite F := hFfinite
  let : Nontrivial F := hFnontrivial
  let SigmaBar : Subgroup (C ⧸ core) :=
    DP.map (QuotientGroup.mk' core)
  let eSigmaBar : SigmaBar ≃* ↥(W ⊓ Subgroup.centralizer (P : Set G)) := by
    simpa [SigmaBar, DP, core, OmegaP, C] using eSigma
  have heSigmaBar (a : SigmaBar) :
      QuotientGroup.mk' core
          ⟨(eSigmaBar a : G), (eSigmaBar a).property.2⟩ =
        (a : C ⧸ core) := by
    simpa [SigmaBar, DP, core, OmegaP, C, eSigmaBar] using heSigma a
  have hSigmaBarCard : Nat.card SigmaBar = Nat.card Sigma := by
    calc
      Nat.card SigmaBar =
          Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) :=
        Nat.card_congr eSigmaBar.toEquiv
      _ = Nat.card Sigma := by rw [hSigma]
  have hSigmaBar_ne_one : Nat.card SigmaBar ≠ 1 := by
    intro hcard
    apply hSigma_ne_one
    rw [← hSigmaBarCard]
    exact hcard
  have hPOcopy := hPO
  rcases hPOcopy with
    ⟨addLift, unitLift, sigmaAct, hcoordinates, haddZero, _hadd,
      hunitOne, hunitMul, hunitRange, hrightQ, hsigmaMaps,
      hsigmaOne, hsigmaMul, hsigmaInjective, hrightSigma,
      _hinvolutionUnique, _hinvolutionOrder⟩
  have hV_le_D : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hP_le_D : P ≤ D := hch.B1.P_le_V.trans hV_le_D
  have hNcoreLocal : N.subgroupOf C = core := by
    simpa [N, C, core, OmegaP] using hNcore
  have hQP_core_disjoint : Disjoint QP core := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxcore
    have hxPsub := hxcore
    rw [← hNcoreLocal, hNP] at hxPsub
    have hxP : (x : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hxPsub
    have hxQG : (x : G) ∈ Q := by
      change (x : G) ∈ Q at hxQ
      exact hxQ
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      hch.section3.section2.hA.A1.Q_disjoint_D.le_bot
        ⟨hxQG, hP_le_D hxP⟩
    simpa using hxBot
  obtain ⟨qpToQbar, hqpToQbar⟩ :=
    chapter2_claim10_quotientMap_subgroup_equiv_of_disjoint
      core QP hQP_core_disjoint
  obtain ⟨unitToQbar, hunitToQbar⟩ :=
    chapter2_claim10_proposition_one_units_equiv
      SigmaBar (QP.map (QuotientGroup.mk' core)) addLift unitLift
        hcoordinates haddZero hunitOne hunitMul hunitRange
  let starToQP : nearFieldStar Q P ≃* QP :=
    { toFun := fun x => ⟨⟨x, x.2.2⟩, x.2.1⟩
      invFun := fun x => ⟨x, x.2, x.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let unitEquivCoord : nearFieldStar Q P ≃* Fˣ :=
    (starToQP.trans qpToQbar).trans unitToQbar.symm
  have hunitCoordinateNear (y : Fˣ) :
      QuotientGroup.mk' core
          ⟨((unitEquivCoord.symm y : nearFieldStar Q P) : G),
            (unitEquivCoord.symm y).property.2⟩ =
        unitLift y := by
    let qP : QP := starToQP (unitEquivCoord.symm y)
    calc
      QuotientGroup.mk' core
          ⟨((unitEquivCoord.symm y : nearFieldStar Q P) : G),
            (unitEquivCoord.symm y).property.2⟩ =
          (qpToQbar qP : C ⧸ core) := by
            symm
            simpa [qP, starToQP] using hqpToQbar qP
      _ = (unitToQbar y : C ⧸ core) := by
        have hq : qpToQbar qP = unitToQbar y := by
          simp [qP, unitEquivCoord]
        exact congrArg Subtype.val hq
      _ = unitLift y := hunitToQbar y
  have hFcomm : IsMulCommutative F :=
    chapter2_claim10_nearField_commutative_of_unitEquiv
      Q P unitEquivCoord hStarComm
  have hcardBridge :
      Nat.card (nearFieldStar Q P) + 1 = Nat.card F := by
    calc
      Nat.card (nearFieldStar Q P) + 1 = Nat.card Fˣ + 1 := by
        rw [Nat.card_congr unitEquivCoord.toEquiv]
      _ = Nat.card F := (Nat.card_eq_card_units_add_one F).symm
  let : IsMulCommutative F := hFcomm
  let fieldF : Field F :=
    Field.ofMinimalAxioms F add_assoc zero_add neg_add_cancel mul_assoc
      (IsMulCommutative.is_comm (M := F)).comm one_mul
      (fun a ha => mul_inv_cancel₀ ha) inv_zero
      (fun a b c => by
        calc
          a * (b + c) = (b + c) * a :=
            (IsMulCommutative.is_comm (M := F)).comm _ _
          _ = b * a + c * a :=
            PFAppendixII.RightNearField.right_distrib b c a
          _ = a * b + a * c := by
            rw [(IsMulCommutative.is_comm (M := F)).comm b a,
              (IsMulCommutative.is_comm (M := F)).comm c a])
      ⟨0, 1, zero_ne_one⟩
  let : Field F := fieldF
  let : AddCommGroup F := fieldF.toAddCommGroup
  let : AddCommMonoid F := fieldF.toAddCommGroup.toAddCommMonoid
  let fieldMonoid : Monoid F :=
    fieldF.toSemifield.toDivisionSemiring.toMonoidWithZero.toMonoid
  let nearMonoid : Monoid F :=
    hF.toGroupWithZero.toMonoidWithZero.toMonoid
  let fieldToNear :
      @MonoidHom F F
        fieldMonoid.toMulOneClass.toMulOne
        nearMonoid.toMulOneClass.toMulOne :=
    { toFun := id
      map_one' := rfl
      map_mul' := by
        intro x y
        rfl }
  let fieldUnitsToNearUnits :
      @Units F fieldMonoid →* @Units F nearMonoid :=
    @Units.map F F fieldMonoid nearMonoid fieldToNear
  let fieldUnitsToStar : @Units F fieldMonoid →* nearFieldStar Q P :=
    unitEquivCoord.symm.toMonoidHom.comp fieldUnitsToNearUnits
  have hfieldToNear_injective : Function.Injective fieldToNear := by
    intro x y hxy
    exact hxy
  have hfieldUnitsToStar_injective : Function.Injective fieldUnitsToStar :=
    unitEquivCoord.symm.injective.comp
      (@Units.map_injective F F fieldMonoid nearMonoid
        fieldToNear hfieldToNear_injective)
  let ell : ℕ := orderOf (s * t)
  have hcharEll : addOrderOf (1 : F) = ell := by
    change @addOrderOf F hF.toAddCommGroup.toAddMonoid (1 : F) = orderOf (s * t)
    exact hcharacteristic
  have hellPrime : Nat.Prime ell := by
    rw [← hcharEll]
    exact PFAppendixII.rightNearField_addOrderOf_one_prime
  let : Fact (Nat.Prime ell) := ⟨hellPrime⟩
  let zmodField : Field (ZMod ell) := inferInstance
  let : Semiring (ZMod ell) :=
    zmodField.toSemifield.toDivisionSemiring.toSemiring
  let : CharP F ell := by
    rw [← hcharEll]
    exact CharP.addOrderOf_one F
  let : Module (ZMod ell) F :=
    { (ZMod.castHom dvd_rfl F : ZMod ell →+* _).toModule with }
  let : Algebra (ZMod ell) F := ZMod.algebraOfModule ell F
  let : Module (ZMod ell) F := Algebra.toModule
  let sigmaRingEquiv (d : SigmaBar) : F ≃+* F :=
    { toFun := sigmaAct d⁻¹
      invFun := sigmaAct d
      left_inv := by
        intro x
        calc
          sigmaAct d (sigmaAct d⁻¹ x) = sigmaAct (d⁻¹ * d) x :=
            (hsigmaMul d⁻¹ d x).symm
          _ = x := by simpa using hsigmaOne x
      right_inv := by
        intro x
        calc
          sigmaAct d⁻¹ (sigmaAct d x) = sigmaAct (d * d⁻¹) x :=
            (hsigmaMul d d⁻¹ x).symm
          _ = x := by simpa using hsigmaOne x
      map_mul' := by
        intro x y
        exact (hsigmaMaps d⁻¹ x y).2.1
      map_add' := by
        intro x y
        exact (hsigmaMaps d⁻¹ x y).1 }
  let sigmaRingHom : SigmaBar →* (F ≃+* F) :=
    { toFun := sigmaRingEquiv
      map_one' := by
        ext x
        change sigmaAct (1 : SigmaBar)⁻¹ x = x
        rw [inv_one]
        exact hsigmaOne x
      map_mul' := by
        intro d e
        ext x
        change sigmaAct (d * e)⁻¹ x = sigmaAct d⁻¹ (sigmaAct e⁻¹ x)
        rw [mul_inv_rev]
        exact hsigmaMul e⁻¹ d⁻¹ x }
  have hsigmaRingInjective : Function.Injective sigmaRingHom := by
    intro d e hde
    have hfun : sigmaAct d⁻¹ = sigmaAct e⁻¹ := by
      funext x
      exact congrArg (fun f : F ≃+* F => f x) hde
    have hinv : d⁻¹ = e⁻¹ := hsigmaInjective hfun
    exact inv_injective hinv
  have hpiInjective : Function.Injective
      (fun z : nearFieldStar Q P =>
        QuotientGroup.mk' core ⟨(z : G), z.property.2⟩) := by
    intro x y hxy
    apply Subtype.ext
    have hdivCore :
        (⟨(x : G), x.property.2⟩ : C) /
            ⟨(y : G), y.property.2⟩ ∈ core :=
      QuotientGroup.eq_iff_div_mem.mp hxy
    rw [← hNcoreLocal, hNP] at hdivCore
    have hdivP : (x : G) / (y : G) ∈ P := by
      simpa [Subgroup.mem_subgroupOf] using hdivCore
    have hdivQ : (x : G) / (y : G) ∈ Q :=
      Q.div_mem x.property.1 y.property.1
    have hdivBot : (x : G) / (y : G) ∈ (⊥ : Subgroup G) :=
      hch.section3.section2.hA.A1.Q_disjoint_D.le_bot
        ⟨hdivQ, hP_le_D hdivP⟩
    exact div_eq_one.mp (Subgroup.mem_bot.mp hdivBot)
  have hcoordinateConj (a : SigmaBar) (y : @Units F fieldMonoid) :
      PFAppendixIII.rightConjugateElem
          ((fieldUnitsToStar y : nearFieldStar Q P) : G)
            (eSigmaBar a : G) =
        ((fieldUnitsToStar
          (@Units.map F F fieldMonoid fieldMonoid (sigmaRingHom a⁻¹).toRingHom.toMonoidHom y) :
            nearFieldStar Q P) : G) := by
    let yNear : @Units F nearMonoid := fieldUnitsToNearUnits y
    let yPrime : @Units F fieldMonoid :=
      @Units.map F F fieldMonoid fieldMonoid
        (sigmaRingHom a⁻¹).toRingHom.toMonoidHom y
    let yNearPrime : @Units F nearMonoid := fieldUnitsToNearUnits yPrime
    let q : nearFieldStar Q P := fieldUnitsToStar y
    let qPrime : nearFieldStar Q P := fieldUnitsToStar yPrime
    let actorC : C := ⟨(eSigmaBar a : G), (eSigmaBar a).property.2⟩
    let qC : C := ⟨(q : G), q.property.2⟩
    have hactorD : (eSigmaBar a : G) ∈ D :=
      PFchapter1section2.proposition_3_W_le_D
        H D Q K V W Q0 S Q1 t hch.section3.section2
          (eSigmaBar a).property.1
    have hqQ : (q : G) ∈ Q := q.property.1
    let actorH : H :=
      ⟨(eSigmaBar a : G), hch.section3.section2.hA.A1.D_le_H hactorD⟩
    let qH : H :=
      ⟨(q : G), hch.section3.section2.hA.A1.Q_le_H hqQ⟩
    have hqHmem : qH ∈ Q.subgroupOf H := by
      simpa [qH, Subgroup.mem_subgroupOf] using hqQ
    have hconjH :=
      hch.section3.section2.hA.A1.Q_normal_in_H.conj_mem qH hqHmem actorH⁻¹
    have hconjQ :
        PFAppendixIII.rightConjugateElem (q : G) (eSigmaBar a : G) ∈ Q := by
      simpa [PFAppendixIII.rightConjugateElem, actorH, qH,
        Subgroup.mem_subgroupOf, mul_assoc] using hconjH
    have hconjC :
        PFAppendixIII.rightConjugateElem (q : G) (eSigmaBar a : G) ∈ C := by
      exact C.mul_mem
        (C.mul_mem (C.inv_mem (eSigmaBar a).property.2) q.property.2)
        (eSigmaBar a).property.2
    let qConj : nearFieldStar Q P :=
      ⟨PFAppendixIII.rightConjugateElem (q : G) (eSigmaBar a : G),
        hconjQ, hconjC⟩
    obtain ⟨z, hzValue, hzConj⟩ :=
      chapter2_claim10_proposition_one_unit_conjugation
        (HP.map (QuotientGroup.mk' core)) SigmaBar
          (QP.map (QuotientGroup.mk' core)) _ hAbar
            addLift unitLift sigmaAct hcoordinates hunitOne hunitRange
              hrightQ hsigmaMaps hrightSigma a yNear
    have hz : z = yNearPrime := by
      apply Units.ext
      calc
        (z : F) = sigmaAct a (yNear : F) := hzValue
        _ = sigmaAct a (y : F) := by rfl
        _ = sigmaRingHom a⁻¹ (y : F) := by
          change sigmaAct a (y : F) = sigmaAct (a⁻¹)⁻¹ (y : F)
          rw [inv_inv]
        _ = (yNearPrime : F) := by
          simp [yNearPrime, yPrime, fieldUnitsToNearUnits, fieldToNear]
    have hqCoordinate :
        QuotientGroup.mk' core ⟨(q : G), q.property.2⟩ = unitLift yNear := by
      simpa [q, fieldUnitsToStar, yNear] using hunitCoordinateNear yNear
    have hqPrimeCoordinate :
        QuotientGroup.mk' core ⟨(qPrime : G), qPrime.property.2⟩ =
          unitLift yNearPrime := by
      simpa [qPrime, fieldUnitsToStar, yNearPrime] using
        hunitCoordinateNear yNearPrime
    have hquot :
        QuotientGroup.mk' core ⟨(qConj : G), qConj.property.2⟩ =
          QuotientGroup.mk' core ⟨(qPrime : G), qPrime.property.2⟩ := by
      calc
        QuotientGroup.mk' core ⟨(qConj : G), qConj.property.2⟩ =
            PFAppendixIII.rightConjugateElem
              (QuotientGroup.mk' core qC) (QuotientGroup.mk' core actorC) := by
          change QuotientGroup.mk' core (actorC⁻¹ * qC * actorC) =
            PFAppendixIII.rightConjugateElem
              (QuotientGroup.mk' core qC) (QuotientGroup.mk' core actorC)
          simp [PFAppendixIII.rightConjugateElem]
        _ = PFAppendixIII.rightConjugateElem (unitLift yNear)
              (a : C ⧸ core) := by
          rw [hqCoordinate, heSigmaBar]
        _ = unitLift z := hzConj
        _ = unitLift yNearPrime := by rw [hz]
        _ = QuotientGroup.mk' core
            ⟨(qPrime : G), qPrime.property.2⟩ := hqPrimeCoordinate.symm
    have hsub : qConj = qPrime := hpiInjective hquot
    change (qConj : G) = (qPrime : G)
    exact congrArg Subtype.val hsub
  have hEllCases : ell = 3 ∨ ell = 5 :=
    chapter2_claim10_characteristic_three_or_five
      H D Q K V W Q0 S Q1 P Sigma t s p ell hch hind hSigma
        hSigma_ne_one rfl
  have hlocal :=
    chapter2_claim10_fixed_field_units_local_control
      H D Q K V W Q0 S Q1 P t s p hch hind
        SigmaBar sigmaRingHom
        fieldUnitsToStar hfieldUnitsToStar_injective eSigmaBar hcoordinateConj ell
  have hclassified :=
    chapter2_claim10_fixed_field_classification_of_local_control
      ell sigmaRingHom hsigmaRingInjective hAbar.D_odd hSigmaBar_ne_one
        hEllCases hlocal
  refine ⟨?_, ?_⟩
  · simpa [← hSigmaBarCard] using hclassified.1
  · rcases hclassified.2 with hThree | hFive | hNine
    · left
      calc
        Nat.card (nearFieldStar Q P) + 1 = Nat.card F := hcardBridge
        _ = 3 ^ Nat.card SigmaBar := hThree
        _ = 3 ^ Nat.card Sigma := by rw [hSigmaBarCard]
    · right
      left
      calc
        Nat.card (nearFieldStar Q P) + 1 = Nat.card F := hcardBridge
        _ = 5 ^ Nat.card SigmaBar := hFive
        _ = 5 ^ Nat.card Sigma := by rw [hSigmaBarCard]
    · right
      right
      calc
        Nat.card (nearFieldStar Q P) + 1 = Nat.card F := hcardBridge
        _ = 9 ^ Nat.card SigmaBar := hNine
        _ = 9 ^ Nat.card Sigma := by rw [hSigmaBarCard]

private theorem chapter2_claim10_Q_card_eq_S_mul_Q1
    {G : Type*} [Group G] [Finite G]
    (Q S Q1 : Subgroup G) (hS_le : S ≤ Q) (hQ1_le : Q1 ≤ Q)
    (hdisj : Disjoint S Q1)
    (hcomm : ∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s)
    (hsup : S ⊔ Q1 = Q) :
    Nat.card Q = Nat.card S * Nat.card Q1 := by
  let SQ : Subgroup Q := S.subgroupOf Q
  let Q1Q : Subgroup Q := Q1.subgroupOf Q
  have hS_norm : S ≤ Subgroup.normalizer (Q1 : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hc := hcomm x hx q hq
      simpa [hc]
    · intro hq
      let w : G := x * q * x⁻¹
      have hw : w ∈ Q1 := hq
      have hc : x * w = w * x := hcomm x hx w hw
      have hinv : x⁻¹ * w * x = w := by
        calc
          x⁻¹ * w * x = x⁻¹ * (w * x) := by simp [mul_assoc]
          _ = x⁻¹ * (x * w) := by rw [hc]
          _ = w := by simp
      have hqeq : q = w := by
        calc
          q = x⁻¹ * w * x := by dsimp [w]; group
          _ = w := hinv
      exact hqeq.symm ▸ hw
  have hQ1normal : Q1Q.Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [← hsup]
    exact sup_le hS_norm Subgroup.le_normalizer
  let : Q1Q.Normal := hQ1normal
  have hdisjQ : Disjoint Q1Q SQ := by
    rw [Subgroup.disjoint_def]
    intro x hxQ1 hxS
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisj) hxS hxQ1
  have hsupQ : Q1Q ⊔ SQ = ⊤ := by
    rw [sup_comm, ← Subgroup.subgroupOf_sup hS_le hQ1_le, hsup]
    exact Subgroup.subgroupOf_self Q
  have hcomp : Q1Q.IsComplement' SQ :=
    isComplement'_of_disjoint_sup_eq_top_of_normal Q1Q SQ hdisjQ hsupQ
  have hcard := hcomp.card_mul_card
  simpa [Q1Q, SQ, natCard_subgroupOf_eq Q1 Q hQ1_le,
    natCard_subgroupOf_eq S Q hS_le, Nat.mul_comm] using hcard.symm

private theorem chapter2_claim10_S_card_power_two
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

private theorem chapter2_claim10_prime_dvd_Q1_of_dvd_nearFieldStar
    {G : Type*} [Group G] [Finite G]
    (Q S Q1 P : Subgroup G)
    (hS_le : S ≤ Q) (hQ1_le : Q1 ≤ Q)
    (hsyl : ∃ P2 : Sylow 2 Q, S = (P2 : Subgroup Q).map Q.subtype)
    (hdisj : Disjoint S Q1)
    (hcomm : ∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s)
    (hsup : S ⊔ Q1 = Q)
    (r : ℕ) (hr : Nat.Prime r) (hr_ne_two : r ≠ 2)
    (hrStar : r ∣ Nat.card (nearFieldStar Q P)) :
    r ∣ Nat.card Q1 := by
  have hQcard : Nat.card Q = Nat.card S * Nat.card Q1 :=
    chapter2_claim10_Q_card_eq_S_mul_Q1 Q S Q1
      hS_le hQ1_le hdisj hcomm hsup
  have hrQ : r ∣ Nat.card Q :=
    hrStar.trans (Subgroup.card_dvd_of_le
      (show nearFieldStar Q P ≤ Q from inf_le_left))
  rw [hQcard] at hrQ
  rcases hr.dvd_mul.mp hrQ with hrS | hrQ1
  · rcases chapter2_claim10_S_card_power_two Q S hsyl with ⟨n, hS⟩
    rw [hS] at hrS
    have hrTwo : r ∣ 2 := hr.dvd_of_dvd_pow hrS
    have hre : r = 2 :=
      ((Nat.dvd_prime Nat.prime_two).mp hrTwo).resolve_left hr.ne_one
    exact (hr_ne_two hre).elim
  · exact hrQ1

private theorem chapter2_claim10_Q1_eq_bot_of_p_dvd_sigma
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p m : ℕ)
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m)
    (hpSigma : p ∣ Nat.card Sigma) :
    Q1 = ⊥ := by
  classical
  by_contra hQ1
  have hStarComm : IsMulCommutative (nearFieldStar Q P) := by
    by_contra hnotcomm
    change ¬ IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (P : Set G)) at hnotcomm
    exact hQ1 (claim_5 H D Q K V W Q0 S Q1 P t s p hch hnotcomm).2.1
  have hSigma_ne_one : Nat.card Sigma ≠ 1 := by
    intro hSigmaOne
    have hpOne : p = 1 := Nat.dvd_one.mp (by simpa [hSigmaOne] using hpSigma)
    exact hch.B1.p_prime.ne_one hpOne
  rcases
      chapter2_fixed_field_orders_of_Q1_ne_bot
        H D Q K V W Q0 S Q1 P Sigma t s p hch hind hSigma hStarComm
          hSigma_ne_one with
    ⟨hSigmaPrime, hfieldOrders⟩
  have hp_eq_sigma : p = Nat.card Sigma := by
    rcases (Nat.dvd_prime hSigmaPrime).mp hpSigma with hpOne | hpSigmaEq
    · exact False.elim (hch.B1.p_prime.ne_one hpOne)
    · exact hpSigmaEq
  have hm_ne : m ≠ 0 := by
    intro hm
    rw [hm, pow_zero] at hStarComm_order
    have hzero : Nat.card (nearFieldStar Q P) = 0 := by omega
    exact Nat.card_pos.ne' hzero
  have hpPow : p ∣ p ^ m := dvd_pow_self p hm_ne
  have hprimeDivisors :=
    (claim_3 H D Q K V W Q0 S Q1 P t s p hch).1
  rcases hfieldOrders with hThree | hFive | hNine
  · have hpow : p ^ m = 3 ^ Nat.card Sigma :=
      hStarComm_order.symm.trans hThree
    have hpDvdThreePow : p ∣ 3 ^ Nat.card Sigma := by
      rw [← hpow]
      exact hpPow
    have hpThree : p = 3 :=
      Nat.prime_eq_prime_of_dvd_pow hch.B1.p_prime Nat.prime_three
        hpDvdThreePow
    have hSigmaThree : Nat.card Sigma = 3 := by
      rw [← hp_eq_sigma, hpThree]
    have hStarCard : Nat.card (nearFieldStar Q P) = 26 := by
      norm_num [hSigmaThree] at hThree
      omega
    have hThirteenStar : 13 ∣ Nat.card (nearFieldStar Q P) := by
      rw [hStarCard]
      norm_num
    have hThirteenQ1 : 13 ∣ Nat.card Q1 :=
      chapter2_claim10_prime_dvd_Q1_of_dvd_nearFieldStar Q S Q1 P
        hch.section3.section2.S_le_Q hch.section3.section2.Q1_le_Q
        hch.section3.section2.S_sylow_in_Q
        hch.section3.section2.S_disjoint_Q1
        hch.section3.section2.S_commutes_Q1
        hch.section3.section2.Q_decomp 13 (by decide) (by norm_num)
        hThirteenStar
    rcases hprimeDivisors 13 (by decide) hThirteenQ1 with
      ⟨⟨i, hi, hmod⟩, _⟩
    norm_num [hpThree] at hi hmod
    interval_cases i <;> norm_num [Nat.ModEq] at hmod
  · have hpow : p ^ m = 5 ^ Nat.card Sigma :=
      hStarComm_order.symm.trans hFive
    have hpDvdFivePow : p ∣ 5 ^ Nat.card Sigma := by
      rw [← hpow]
      exact hpPow
    have hpFive : p = 5 :=
      Nat.prime_eq_prime_of_dvd_pow hch.B1.p_prime Nat.prime_five
        hpDvdFivePow
    have hSigmaFive : Nat.card Sigma = 5 := by
      rw [← hp_eq_sigma, hpFive]
    have hStarCard : Nat.card (nearFieldStar Q P) = 3124 := by
      norm_num [hSigmaFive] at hFive
      omega
    have hElevenStar : 11 ∣ Nat.card (nearFieldStar Q P) := by
      rw [hStarCard]
      norm_num
    have hElevenQ1 : 11 ∣ Nat.card Q1 :=
      chapter2_claim10_prime_dvd_Q1_of_dvd_nearFieldStar Q S Q1 P
        hch.section3.section2.S_le_Q hch.section3.section2.Q1_le_Q
        hch.section3.section2.S_sylow_in_Q
        hch.section3.section2.S_disjoint_Q1
        hch.section3.section2.S_commutes_Q1
        hch.section3.section2.Q_decomp 11 Nat.prime_eleven (by norm_num)
        hElevenStar
    rcases hprimeDivisors 11 Nat.prime_eleven hElevenQ1 with
      ⟨⟨i, hi, hmod⟩, _⟩
    norm_num [hpFive] at hi hmod
    interval_cases i <;> norm_num [Nat.ModEq] at hmod
  · have hpow : p ^ m = 9 ^ Nat.card Sigma :=
      hStarComm_order.symm.trans hNine
    have hNinePow : 9 ^ Nat.card Sigma = 3 ^ (2 * Nat.card Sigma) := by
      rw [show 9 = 3 ^ 2 by norm_num, pow_mul]
    have hpDvdThreePow : p ∣ 3 ^ (2 * Nat.card Sigma) := by
      rw [← hNinePow, ← hpow]
      exact hpPow
    have hpThree : p = 3 :=
      Nat.prime_eq_prime_of_dvd_pow hch.B1.p_prime Nat.prime_three
        hpDvdThreePow
    have hSigmaThree : Nat.card Sigma = 3 := by
      rw [← hp_eq_sigma, hpThree]
    have hStarCard : Nat.card (nearFieldStar Q P) = 728 := by
      norm_num [hSigmaThree] at hNine
      omega
    have hThirteenStar : 13 ∣ Nat.card (nearFieldStar Q P) := by
      rw [hStarCard]
      norm_num
    have hThirteenQ1 : 13 ∣ Nat.card Q1 :=
      chapter2_claim10_prime_dvd_Q1_of_dvd_nearFieldStar Q S Q1 P
        hch.section3.section2.S_le_Q hch.section3.section2.Q1_le_Q
        hch.section3.section2.S_sylow_in_Q
        hch.section3.section2.S_disjoint_Q1
        hch.section3.section2.S_commutes_Q1
        hch.section3.section2.Q_decomp 13 (by decide) (by norm_num)
        hThirteenStar
    rcases hprimeDivisors 13 (by decide) hThirteenQ1 with
      ⟨⟨i, hi, hmod⟩, _⟩
    norm_num [hpThree] at hi hmod
    interval_cases i <;> norm_num [Nat.ModEq] at hmod

/-- Checked global cardinality formula used in the `p`-part calculation. -/
private theorem chapter2_claim10_G_card
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    Nat.card G =
      (Nat.card Q + 1) * Nat.card Q * Nat.card K * Nat.card W * p := by
  classical
  have hA1 := hch.section3.section2.hA.A1
  have hOmega : Nat.card Ω = Nat.card Q + 1 :=
    hypothesisA1_card_space_eq_card_Q_add_one_of_hypothesis H D Q t hA1
  have : MulAction.IsMultiplyPretransitive G Ω 2 := hA1.two_transitive
  have : MulAction.IsPretransitive G Ω :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨alpha, hH⟩ := hA1.point_stabilizer
  have hHindex : H.index = Nat.card Ω := by
    rw [hH]
    exact MulAction.index_stabilizer_of_transitive (G := G) (x := alpha)
  let QH : Subgroup H := Q.subgroupOf H
  let DH : Subgroup H := D.subgroupOf H
  have : QH.Normal := by
    simpa [QH] using hA1.Q_normal_in_H
  have hdisjH : Disjoint QH DH := by
    rw [Subgroup.disjoint_def]
    intro x hxQ hxD
    apply Subtype.ext
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hA1.Q_disjoint_D)
        (by simpa [QH, Subgroup.mem_subgroupOf] using hxQ)
        (by simpa [DH, Subgroup.mem_subgroupOf] using hxD)
    simpa using hxbot
  have hsupH : QH ⊔ DH = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA1.Q_le_H hA1.D_le_H]
    rw [hA1.Q_sup_D, Subgroup.subgroupOf_self]
  have hcompH : QH.IsComplement' DH :=
    isComplement'_of_disjoint_sup_eq_top_of_normal QH DH hdisjH hsupH
  have hHcard : Nat.card H = Nat.card Q * Nat.card D := by
    have hcard := hcompH.card_mul_card
    rw [natCard_subgroupOf_eq Q H hA1.Q_le_H,
      natCard_subgroupOf_eq D H hA1.D_le_H] at hcard
    exact hcard.symm
  have hGQD :
      Nat.card G = (Nat.card Q + 1) * Nat.card Q * Nat.card D := by
    calc
      Nat.card G = Nat.card H * H.index := H.card_mul_index.symm
      _ = (Nat.card Q * Nat.card D) * (Nat.card Q + 1) := by
        rw [hHcard, hHindex, hOmega]
      _ = (Nat.card Q + 1) * Nat.card Q * Nat.card D := by ring
  let Y : Subgroup G := D ⊓ Subgroup.centralizer ({t} : Set G)
  let Z : Set G :=
    {x : G | x ∈ D ∧ PFAppendixIII.rightConjugateElem x t = x⁻¹}
  have htNormD : t ∈ Subgroup.normalizer (D : Set G) :=
    PFchapter1section2.hypothesisA1_t_mem_normalizer_D H D Q t hA1
  have hDYZ : Nat.card D = Nat.card Y * Nat.card Z := by
    simpa [Y, Z] using
      (PFchapter1section1.lemma_a (M := G) t D hA1.involution_t
        hA1.D_odd htNormD).2.2
  have hYeq : Y = V := by
    rw [hch.section3.section2.V_eq]
    rfl
  let eKZ : K ≃ Z :=
    { toFun := fun k =>
        ⟨(k : G), (hch.section3.section2.K_def (k : G)).mp k.property⟩
      invFun := fun z =>
        ⟨(z : G), (hch.section3.section2.K_def (z : G)).mpr z.property⟩
      left_inv := by intro k; rfl
      right_inv := by intro z; rfl }
  have hZcard : Nat.card Z = Nat.card K :=
    (Nat.card_congr eKZ).symm
  have hDcard : Nat.card D = Nat.card V * Nat.card K := by
    rw [hYeq, hZcard] at hDYZ
    exact hDYZ
  rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
    ⟨hWleV, hPleV, hWnorm, hdisjWP, hsupWP⟩
  let WV : Subgroup V := W.subgroupOf V
  let PV : Subgroup V := P.subgroupOf V
  have : WV.Normal := ⟨by
    intro w hw v
    have hwG : (w : G) ∈ W := by
      simpa [WV, Subgroup.mem_subgroupOf] using hw
    have hvG : (v : G) ∈ V := v.property
    have hconj := hWnorm (v : G) (w : G) hvG hwG
    simpa [WV, Subgroup.mem_subgroupOf] using hconj⟩
  have hdisjV : Disjoint WV PV := by
    rw [Subgroup.disjoint_def]
    intro x hxW hxP
    apply Subtype.ext
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
      (Subgroup.disjoint_def.mp hdisjWP)
        (by simpa [WV, Subgroup.mem_subgroupOf] using hxW)
        (by simpa [PV, Subgroup.mem_subgroupOf] using hxP)
    simpa using hxbot
  have hsupV : WV ⊔ PV = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hWleV hPleV]
    rw [hsupWP, Subgroup.subgroupOf_self]
  have hcompV : WV.IsComplement' PV :=
    isComplement'_of_disjoint_sup_eq_top_of_normal WV PV hdisjV hsupV
  have hVcard : Nat.card V = Nat.card W * p := by
    have hcard := hcompV.card_mul_card
    rw [natCard_subgroupOf_eq W V hWleV,
      natCard_subgroupOf_eq P V hPleV, hch.B1.P_card] at hcard
    exact hcard.symm
  rw [hGQD, hDcard, hVcard]
  ring

/-- Checked structural cardinality and fixed-point facts used by the `p`-part calculation. -/
private theorem chapter2_claim10_card_structure
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p : ℕ)
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
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G)) :
    Nat.card G =
        (Nat.card Q + 1) * Nat.card Q * Nat.card K * Nat.card W * p ∧
      ¬ p ∣ Nat.card Q ∧ ¬ p ∣ Nat.card K ∧
        (¬ p ∣ Nat.card Sigma → ¬ p ∣ Nat.card W) := by
  classical
  have hGcard :
      Nat.card G =
        (Nat.card Q + 1) * Nat.card Q * Nat.card K * Nat.card W * p := by
    exact chapter2_claim10_G_card
      H D Q K V W Q0 S Q1 P t s p hch
  have hpQ : ¬ p ∣ Nat.card Q := by
    have hcop :=
      (claim_3 H D Q K V W Q0 S Q1 P t s p hch).2
    have hp_dvd_KP : p ∣ Nat.card (K ⊔ P : Subgroup G) := by
      have hcard := Subgroup.card_dvd_of_le (show P ≤ K ⊔ P from le_sup_right)
      simpa [hch.B1.P_card] using hcard
    exact hch.B1.p_prime.coprime_iff_not_dvd.mp
      (hcop.coprime_dvd_right hp_dvd_KP).symm
  have hpK : ¬ p ∣ Nat.card K := by
    rw [claim_1_K_card_eq_mersenne H D Q K V W Q0 S Q1 P t s p hch]
    intro hdvd
    have hone : 1 ≤ 2 ^ p := Nat.one_le_pow p 2 (by omega)
    have hdvdZ : (p : ℤ) ∣ (2 : ℤ) ^ p - 1 := by
      exact_mod_cast hdvd
    have hfermat : (p : ℤ) ∣ (2 : ℤ) ^ p - 2 :=
      Int.prime_dvd_pow_self_sub hch.B1.p_prime 2
    have hp1 : (p : ℤ) ∣ 1 := by
      have hdiff := dvd_sub hdvdZ hfermat
      have hdiff_eq :
          (2 : ℤ) ^ p - 1 - ((2 : ℤ) ^ p - 2) = 1 := by
        ring
      rw [hdiff_eq] at hdiff
      exact hdiff
    have hp1Nat : p ∣ 1 := by
      exact_mod_cast hp1
    exact hch.B1.p_prime.ne_one (Nat.dvd_one.mp hp1Nat)
  have hpW : ¬ p ∣ Nat.card Sigma → ¬ p ∣ Nat.card W := by
    intro hpSigma
    rcases (claim_1 H D Q K V W Q0 S Q1 P t s p hch).1 with
      ⟨_hWleV, hPleV, hWnorm, _hdisj, _hsup⟩
    have hPnormW : P ≤ Subgroup.normalizer (W : Set G) := by
      intro x hxP
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact hWnorm x w (hPleV hxP)
      · intro hxwx
        have hxinvP : x⁻¹ ∈ P := P.inv_mem hxP
        have hxinv := hWnorm x⁻¹ (x * w * x⁻¹) (hPleV hxinvP) hxwx
        simpa [mul_assoc] using hxinv
    let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
    let : Subgroup.Normalizes P W := ⟨hPnormW⟩
    have hPgroup : IsPGroup p P := by
      apply IsPGroup.of_card (n := 1)
      rw [pow_one]
      exact hch.B1.P_card
    have hfix :
        fixedPointSubgroup (↥P) (↥W) =
          (subgroupCentralizerIn W P).subgroupOf W := by
      simpa using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn W P hPnormW
    have hcentLe : subgroupCentralizerIn W P ≤ W := by
      intro x hx
      exact hx.1
    have hfixcard :
        Nat.card (MulAction.fixedPoints (↥P) (↥W)) = Nat.card Sigma := by
      calc
        Nat.card (MulAction.fixedPoints (↥P) (↥W)) =
            Nat.card (fixedPointSubgroup (↥P) (↥W)) := rfl
        _ = Nat.card ((subgroupCentralizerIn W P).subgroupOf W) := by rw [hfix]
        _ = Nat.card (subgroupCentralizerIn W P) :=
          natCard_subgroupOf_eq (subgroupCentralizerIn W P) W hcentLe
        _ = Nat.card Sigma := by rw [hSigma]; rfl
    have hmod : Nat.card W ≡ Nat.card Sigma [MOD p] := by
      rw [← hfixcard]
      exact hPgroup.card_modEq_card_fixedPoints (↥W)
    intro hpWcard
    apply hpSigma
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.symm.trans hpWcard.modEq_zero_nat)
  exact ⟨hGcard, hpQ, hpK, hpW⟩

/-- Checked exact `p`-part cardinality calculations in Claim (10). -/
private theorem chapter2_claim10_p_part
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p m : ℕ)
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
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m) :
    ((¬ p ∣ Nat.card Sigma) →
      ∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧
        Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u) ∧
    (p = 3 → Nat.card (nearFieldStar Q P) = 8 →
      (Nat.card W = 3 ∨ Nat.card W = 9) →
      ∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
        Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) := by
  classical
  let : Fact (Nat.Prime p) := ⟨hch.B1.p_prime⟩
  rcases
      chapter2_claim10_card_structure
        H D Q K V W Q0 S Q1 P Sigma t s p hch hSigma with
    ⟨hGcard, hpQ, hpK, hpW⟩
  have hm_ne : m ≠ 0 := by
    intro hm
    rw [hm, pow_zero] at hStarComm_order
    have hzero : Nat.card (nearFieldStar Q P) = 0 := by omega
    exact Nat.card_pos.ne' hzero
  have hpow_one : 1 ≤ p ^ m := Nat.one_le_pow m p hch.B1.p_prime.pos
  have hStarCard : Nat.card (nearFieldStar Q P) = p ^ m - 1 := by
    omega
  have hQplus : Nat.card Q + 1 = (p ^ m - 1) ^ p + 1 := by
    have h4 := claim_4 H D Q K V W Q0 S Q1 P t s p hch
    calc
      Nat.card Q + 1 = Nat.card (nearFieldStar Q P) ^ p + 1 := by
        simpa [nearFieldStar] using congrArg (fun n : ℕ => n + 1) h4
      _ = (p ^ m - 1) ^ p + 1 := by rw [hStarCard]
  have hpOdd : Odd p := by
    have hVleD :=
      _root_.CFSG.BenderSuzuki.PFchapter1section2.proposition_3_V_le_D
        H D Q K V W Q0 S Q1 t hch.section3.section2
    rw [← hch.B1.P_card]
    exact hch.section3.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le (hch.B1.P_le_V.trans hVleD))
  have hpDvdPow : p ∣ p ^ m := dvd_pow_self p hm_ne
  have hCoprime : Nat.Coprime (p ^ m - 1) (p ^ m) := by
    rw [Nat.coprime_self_sub_left hpow_one]
    simp
  have hpNotDvdBase : ¬ p ∣ p ^ m - 1 := by
    exact hch.B1.p_prime.coprime_iff_not_dvd.mp
      (hCoprime.coprime_dvd_right hpDvdPow).symm
  have hpDvdBaseSucc : p ∣ (p ^ m - 1) + 1 := by
    rw [Nat.sub_add_cancel hpow_one]
    exact hpDvdPow
  have hVal : padicValNat p (Nat.card Q + 1) = m + 1 := by
    rw [hQplus]
    calc
      padicValNat p ((p ^ m - 1) ^ p + 1) =
          padicValNat p ((p ^ m - 1) + 1) + padicValNat p p :=
        by simpa using
          (padicValNat.pow_add_pow hpOdd hpDvdBaseSucc hpNotDvdBase hpOdd)
      _ = m + 1 := by
        have hpval : padicValNat p p = 1 := by
          simpa only [pow_one] using (padicValNat.prime_pow (p := p) 1)
        rw [Nat.sub_add_cancel hpow_one, padicValNat.prime_pow, hpval]
  let uQ : ℕ := (Nat.card Q + 1).divMaxPow p
  have hQplusDecomp : Nat.card Q + 1 = p ^ (m + 1) * uQ := by
    rw [← hVal]
    exact (Nat.pow_padicValNat_mul_divMaxPow p (Nat.card Q + 1)).symm
  have hpUQ : ¬ p ∣ uQ :=
    Nat.not_dvd_divMaxPow hch.B1.p_prime.one_lt (by omega)
  constructor
  · intro hpSigma
    refine ⟨m + 2, uQ * Nat.card Q * Nat.card K * Nat.card W, rfl, ?_, ?_⟩
    · rw [hGcard, hQplusDecomp]
      rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
      ring
    · exact hch.B1.p_prime.not_dvd_mul
        (hch.B1.p_prime.not_dvd_mul
          (hch.B1.p_prime.not_dvd_mul hpUQ hpQ) hpK)
        (hpW hpSigma)
  · intro hp3 hStarCard8 hWcards
    have hm2 : m = 2 := by
      rw [hStarCard8, hp3] at hStarComm_order
      have hpow : 3 ^ 2 = 3 ^ m := by
        norm_num at hStarComm_order ⊢
        exact hStarComm_order
      exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow).symm
    let u : ℕ := uQ * Nat.card Q * Nat.card K
    have hu : ¬ 3 ∣ u := by
      rw [← hp3]
      exact hch.B1.p_prime.not_dvd_mul
        (hch.B1.p_prime.not_dvd_mul hpUQ hpQ) hpK
    rcases hWcards with hW3 | hW9
    · refine ⟨5, u, ?_, ?_, hu⟩
      · rw [hW3]
        norm_num
      · rw [hGcard, hQplusDecomp, hp3, hm2, hW3]
        dsimp [u]
        ring
    · refine ⟨6, u, ?_, ?_, hu⟩
      · rw [hW9]
        norm_num
      · rw [hGcard, hQplusDecomp, hp3, hm2, hW9]
        dsimp [u]
        ring

private theorem claim_10_addOrderOf_one_eq_three_of_dickson_model
    {F : Type*} [PFAppendixII.RightNearField F] [Finite F]
    (hmodel : PFAppendixII.IsDicksonIndexTwoModel F 3 1) :
    addOrderOf (1 : F) = 3 := by
  rw [PFAppendixII.IsDicksonIndexTwoModel] at hmodel
  rcases hmodel with
    ⟨_hprime, _hne_two, _hn_pos, hfact, e, he1, _hmul, _hfrob, _hcenter⟩
  let : Fact (Nat.Prime 3) := hfact
  apply addOrderOf_eq_prime
  · apply e.injective
    have hchar : (3 : GaloisField 3 (2 * 1)) = 0 :=
      CharP.cast_eq_zero (GaloisField 3 (2 * 1)) 3
    simp [map_nsmul, he1, nsmul_eq_mul, hchar]
  · exact one_ne_zero

public theorem claim_10
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p m : ℕ)
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hStarComm_order : Nat.card (nearFieldStar Q P) + 1 = p ^ m) :
    (¬ p ∣ Nat.card Sigma ∧
      (∃ k u : ℕ, p ^ (m + 2) = p ^ k ∧
        Nat.card G = p ^ (m + 2) * u ∧ ¬ p ∣ u)) ∨
      p = 3 ∧ Nat.card Sigma = 3 ∧
        Nat.card (nearFieldStar Q P) = 8 ∧ IsCyclic W ∧
          (Nat.card W = 3 ∨ Nat.card W = 9) ∧
            (∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
              Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) ∧
              ∃ (F : Type v) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
                  (_ : Nontrivial F),
                PFAppendixII.IsDicksonIndexTwoModel F 3 1 ∧
                  Nonempty (nearFieldStar Q P ≃* Fˣ) := by
  classical
  rcases
      chapter2_claim10_p_part
        H D Q K V W Q0 S Q1 P Sigma t s p m hch hSigma hStarComm_order with
    ⟨hpartOne, hpartTwo⟩
  by_cases hpSigma : p ∣ Nat.card Sigma
  · right
    have hQ1bot : Q1 = ⊥ :=
      chapter2_claim10_Q1_eq_bot_of_p_dvd_sigma
        H D Q K V W Q0 S Q1 P Sigma t s p m hch hind hSigma
          hStarComm_order hpSigma
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let OmegaP : Type v := {w : Ω // w ∈ fixedPointsOfSubgroup G Ω P}
    let : MulAction C OmegaP := fixedPointCentralizerAction G Ω P
    let DP : Subgroup C := D.comap C.subtype
    let core : Subgroup C := pointStabilizerCore C OmegaP
    let N : Subgroup G :=
      D ⊓ Subgroup.centralizer
        ((Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) ⊓
          Subgroup.centralizer (P : Set G)
    have h7 :=
      claim_7 H D Q K V W Q0 S Q1 P N t s p hch hind rfl
    dsimp only at h7
    rcases h7 with ⟨hnormal7, _hNP, eSigma⟩
    let : core.Normal := hnormal7
    rcases eSigma with ⟨eSigma, _heSigma⟩
    have hSigmaBarCard :
        Nat.card (DP.map (QuotientGroup.mk' core)) = Nat.card Sigma := by
      calc
        Nat.card (DP.map (QuotientGroup.mk' core)) =
            Nat.card ↥(W ⊓ Subgroup.centralizer (P : Set G)) :=
          Nat.card_congr eSigma.toEquiv
        _ = Nat.card Sigma := by rw [hSigma]
    have h6 :=
      claim_6 H D Q K V W Q0 S Q1 P t s p (orderOf (s * t))
        hch hQ1bot rfl
    dsimp only at h6
    rcases h6 with ⟨_hnormal6, hnoncomm6, hcomm6⟩
    have hStarNoncomm : ¬ IsMulCommutative (nearFieldStar Q P) := by
      intro hStarComm
      have hSigmaBarBot := (hcomm6 hStarComm).2
      have hSigmaCardOne : Nat.card Sigma = 1 := by
        rw [← hSigmaBarCard, hSigmaBarBot, Subgroup.card_bot]
      have hpOne : p = 1 := Nat.dvd_one.mp (by simpa [hSigmaCardOne] using hpSigma)
      exact hch.B1.p_prime.ne_one hpOne
    have hSigmaCases : Nat.card Sigma = 1 ∨ Nat.card Sigma = 3 := by
      rcases hnoncomm6 hStarNoncomm with hOne | hThree
      · exact Or.inl (hSigmaBarCard.symm.trans hOne)
      · exact Or.inr (hSigmaBarCard.symm.trans hThree)
    have hSigmaCard : Nat.card Sigma = 3 := by
      rcases hSigmaCases with hOne | hThree
      · have hpOne : p = 1 := Nat.dvd_one.mp (by simpa [hOne] using hpSigma)
        exact False.elim (hch.B1.p_prime.ne_one hpOne)
      · exact hThree
    have hp3 : p = 3 := by
      have hpDvd3 : p ∣ 3 := by simpa [hSigmaCard] using hpSigma
      rcases (Nat.dvd_prime Nat.prime_three).mp hpDvd3 with hpOne | hpThree
      · exact False.elim (hch.B1.p_prime.ne_one hpOne)
      · exact hpThree
    have h2b := claim_2_b H D Q K V W Q0 S Q1 P t s p hch
    dsimp only at h2b
    rcases h2b with
      ⟨_hNcore, _hnormal2b, _quotientAction, _hsmul, _hAbar,
        F, hF, hFfinite, hFnontrivial, unitEquiv, _hPO, hcharacteristic⟩
    let : PFAppendixII.RightNearField F := hF
    let : Finite F := hFfinite
    let : Nontrivial F := hFnontrivial
    have hQnil : Group.IsNilpotent Q :=
      _root_.CFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
        H D Q K V W Q0 S Q1 t hch.section3.section2
    have hSclass : IsMulCommutative S ∨ PFAppendixIII.IsSuzukiTwoGroup S :=
      _root_.CFSG.BenderSuzuki.PFchapter1section2.corollary
        H D Q K V W Q0 S Q1 t hch.section3.section2
    obtain ⟨_hFnoncomm, hUnitsCard, hmodel⟩ :=
      claim_5_classify_nearFieldWitness Q S P hQnil
        hch.section3.section2.S_sylow_in_Q hSclass unitEquiv hStarNoncomm
    have hStarCardUnits :
        Nat.card (nearFieldStar Q P) = Nat.card Fˣ :=
      Nat.card_congr unitEquiv.toEquiv
    have hStarCard : Nat.card (nearFieldStar Q P) = 8 :=
      hStarCardUnits.trans hUnitsCard
    have horder3 : orderOf (s * t) = 3 :=
      hcharacteristic.symm.trans
        (claim_10_addOrderOf_one_eq_three_of_dickson_model hmodel)
    have hS_eq_Q : S = Q := by
      calc
        S = S ⊔ Q1 := by simp [hQ1bot]
        _ = Q := hch.section3.section2.Q_decomp
    have hQSuzuki : IsSuzukiTwoGroup Q := by
      rcases hSclass with hScomm | hSsuzuki
      · exfalso
        apply hStarNoncomm
        let : IsMulCommutative S := hScomm
        refine ⟨⟨fun a b => ?_⟩⟩
        apply Subtype.ext
        let aS : S := ⟨(a : G), by rw [hS_eq_Q]; exact a.property.1⟩
        let bS : S := ⟨(b : G), by rw [hS_eq_Q]; exact b.property.1⟩
        simpa [aS, bS] using congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm aS bS)
      · rw [hS_eq_Q] at hSsuzuki
        exact hSsuzuki
    have hQcard : Nat.card Q = Nat.card Q0 ^ 3 := by
      have h4 := claim_4 H D Q K V W Q0 S Q1 P t s p hch
      have hQ0card := (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
      calc
        Nat.card Q = Nat.card (nearFieldStar Q P) ^ p := by
          simpa [nearFieldStar] using h4
        _ = 8 ^ p := by rw [hStarCard]
        _ = 8 ^ 3 := by rw [hp3]
        _ = (2 ^ p) ^ 3 := by rw [hp3]; norm_num
        _ = Nat.card Q0 ^ 3 := by rw [hQ0card]
    have hWdata : IsCyclic W ∧ Nat.card W ∣ Nat.card Q0 + 1 := by
      have hWlemma := PFchapter1section3.lemma_5
        H D Q K V W Q0 S Q1 t s hch.1 hind horder3 hQSuzuki hQcard
      exact ⟨hWlemma.1, hWlemma.2.1⟩
    have hQ0card8 : Nat.card Q0 = 8 := by
      have hQ0card := (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
      rw [hQ0card, hp3]
      norm_num
    have hWdiv9 : Nat.card W ∣ 9 := by
      simpa [hQ0card8] using hWdata.2
    have hSigma_le_W : Sigma ≤ W := by
      rw [hSigma]
      exact inf_le_left
    have hThreeDvdW : 3 ∣ Nat.card W := by
      rw [← hSigmaCard]
      exact Subgroup.card_dvd_of_le hSigma_le_W
    have hWcards : Nat.card W = 3 ∨ Nat.card W = 9 := by
      have hWdivPow : Nat.card W ∣ 3 ^ 2 := by
        norm_num
        exact hWdiv9
      obtain ⟨k, hk, hWcard⟩ :=
        (Nat.dvd_prime_pow Nat.prime_three).mp hWdivPow
      have hk_ne_zero : k ≠ 0 := by
        intro hk0
        rw [hk0, pow_zero] at hWcard
        rw [hWcard] at hThreeDvdW
        norm_num at hThreeDvdW
      have hk_cases : k = 1 ∨ k = 2 := by omega
      rcases hk_cases with rfl | rfl
      · exact Or.inl (by simpa using hWcard)
      · exact Or.inr (by norm_num at hWcard ⊢; exact hWcard)
    exact
      ⟨hp3, hSigmaCard, hStarCard, hWdata.1, hWcards,
        hpartTwo hp3 hStarCard hWcards, F, hF, hFfinite, hFnontrivial,
          hmodel, ⟨unitEquiv⟩⟩
  · left
    exact ⟨hpSigma, hpartOne hpSigma⟩

end PFchapter2
end CFSG.BenderSuzuki
