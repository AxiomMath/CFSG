module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixI.proposition_2
public import Mathlib.GroupTheory.SemidirectProduct
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section2

open PFchapter1section1 PFAppendixI PFAppendixIII
open Representation
open Theory.Representation
open scoped IsMulCommutative

/-!
# Peterfalvi, Part II, Chapter I, Section 2, Proposition 3
-/

public theorem proposition_3_V_le_D
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
    V ≤ D := by
  simp [hsec.V_eq, peterfalviV]

public theorem proposition_3_W_le_D
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
    W ≤ D :=
  hsec.W_le_V.trans (proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec)

/-- The left-conjugation action of D preserves Q0. The inverse in the
right-conjugation notation turns d⁻¹ * q * d into d * q * d⁻¹. -/
public theorem proposition_3_Q0_rightConjugate_mem_of_D
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
    ∀ d : D, ∀ q : Q0,
      rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0 := by
  intro d q
  apply (hsec.Q0_def _).mpr
  rcases (hsec.Q0_def (q : G)).mp q.property with hq_one | hq
  · left
    simp [hq_one, rightConjugateElem]
  · right
    have hdH : (d : G) ∈ H := hsec.hA.A1.D_le_H d.property
    refine ⟨?_, isInvolution_rightConjugateElem hq.2⟩
    simpa [rightConjugateElem] using
      H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH)

private theorem proposition_3_appendixIRepresentation_irreducible_of_transitive
    {p : ℕ} [Fact p.Prime]
    {E U : Type*} [Group E] [Finite E] [Nontrivial E]
    [Group U] [IsElementaryAbelian p E] [MulDistribMulAction U E]
    (T : Subgroup U)
    (htrans :
      ∀ x : E, x ≠ 1 →
        ∀ y : E, y ≠ 1 →
          ∃ τ : T, (τ : U) • x = y) :
    IsSimpleOrder (Subrepresentation (AppendixIRepresentationOfT (p := p) (E := E) T)) := by
  let ρ := AppendixIRepresentationOfT (p := p) (E := E) T
  refine
    { toNontrivial := ?_
      eq_bot_or_eq_top := ?_ }
  · exact ⟨⟨⊥, ⊤, bot_ne_top⟩⟩
  · intro L
    by_cases hLbot : L = ⊥
    · exact Or.inl hLbot
    · right
      have hLsub : L.toSubmodule ≠ ⊥ := by
        intro h
        apply hLbot
        apply Subrepresentation.toSubmodule_injective
        exact h
      obtain ⟨x, hxL, hx0⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot hLsub
      apply top_unique
      intro y _hy
      by_cases hy0 : y = 0
      · subst y
        exact L.toSubmodule.zero_mem
      · have hx1 : Additive.toMul x ≠ 1 := by simpa using hx0
        have hy1 : Additive.toMul y ≠ 1 := by simpa using hy0
        obtain ⟨τ, hτ⟩ :=
          htrans (Additive.toMul x) hx1 (Additive.toMul y) hy1
        have hρxy : ρ τ x = y := by
          calc
            ρ τ x = Additive.ofMul ((τ : U) • Additive.toMul x) := by
              dsimp [ρ, AppendixIRepresentationOfT]
              have h_rep : (Theory.Representation.ofElementaryAbelianAction (A := T) (G := E) (p := p)) τ x = Additive.ofMul (τ • Additive.toMul x) := by
                calc
                  (Theory.Representation.ofElementaryAbelianAction (A := T) (G := E) (p := p)) τ x
                      = (Theory.Representation.ofElementaryAbelianAction (A := T) (G := E) (p := p)) τ (Additive.ofMul (Additive.toMul x)) := by
                        cases x; rfl
                  _ = Additive.ofMul (τ • Additive.toMul x) :=
                    Theory.Representation.ofElementaryAbelianAction_apply_ofMul (A := T) (G := E) (p := p) τ (Additive.toMul x)
              have h_smul : τ • Additive.toMul x = (τ : U) • Additive.toMul x := rfl
              rw [h_rep, h_smul]
            _ = Additive.ofMul (Additive.toMul y) := congrArg Additive.ofMul hτ
            _ = y := by simp
        have hmem := L.apply_mem_toSubmodule τ hxL
        rw [← hρxy]
        exact hmem

private theorem proposition_3_quotient_conjugation_action
    {G : Type*} [Group G]
    (H D W Q0 : Subgroup G)
    (hDleH : D ≤ H)
    (hQ0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x))
    (hW_eq :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}))
    (hWD : (W.subgroupOf D).Normal)
    (hfaith :
      ∀ d : D, (∀ x : G, x ∈ Q0 → rightConjugateElem x (d : G) = x) →
        (d : G) ∈ W) :
    letI : (W.subgroupOf D).Normal := hWD
    ∃ rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0,
      Function.Injective rhoD ∧
        ∀ d : D, ∀ q : Q0,
          rhoD (QuotientGroup.mk d) q =
            ⟨rightConjugateElem (q : G) (d : G)⁻¹, by
              rw [hQ0_def]
              rcases (hQ0_def (q : G)).mp q.property with hq_one | hq
              · left
                simp [hq_one, rightConjugateElem]
              · right
                have hdH : (d : G) ∈ H := hDleH d.property
                refine ⟨?_, by
                  simpa [rightConjugateElem] using
                    (isInvolution_rightConjugateElem (g := (d : G)⁻¹) hq.2)⟩
                simpa [rightConjugateElem] using
                  H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH)⟩ := by
  classical
  letI : (W.subgroupOf D).Normal := hWD
  have hclosed :
      ∀ d : G, d ∈ D → ∀ q : G, q ∈ Q0 → d * q * d⁻¹ ∈ Q0 := by
    intro d hdD q hqQ0
    apply (hQ0_def _).mpr
    rcases (hQ0_def q).mp hqQ0 with hq_one | hq
    · left
      simp [hq_one]
    · right
      have hdH : d ∈ H := hDleH hdD
      refine ⟨H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH), ?_⟩
      simpa [rightConjugateElem] using
        (isInvolution_rightConjugateElem (g := d⁻¹) hq.2)
  have hDnorm : D ≤ Subgroup.normalizer (Q0 : Set G) := by
    intro d hdD
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · exact hclosed d hdD q
    · intro hq
      have hback := hclosed d⁻¹ (D.inv_mem hdD) (d * q * d⁻¹) hq
      simpa [mul_assoc] using hback
  letI : Subgroup.Normalizes D Q0 := ⟨hDnorm⟩
  let conjHom : D →* MulAut Q0 := MulDistribMulAction.toMulAut D Q0
  have hWker : W.subgroupOf D ≤ conjHom.ker := by
    intro w hwW
    change conjHom w = 1
    apply MulEquiv.ext
    intro q
    apply Subtype.ext
    change (w : G) * (q : G) * (w : G)⁻¹ = (q : G)
    have hwW' : (w : G) ∈ W := hwW
    rw [hW_eq] at hwW'
    rcases (hQ0_def (q : G)).mp q.property with hq_one | hq
    · simp [hq_one]
    · have hcomm : (w : G) * (q : G) = (q : G) * (w : G) :=
        ((Subgroup.mem_centralizer_iff.mp hwW'.2) (q : G) hq).symm
      rw [hcomm]
      simp
  have hker_le : conjHom.ker ≤ W.subgroupOf D := by
    intro d hd
    have hdInv : d⁻¹ ∈ conjHom.ker := conjHom.ker.inv_mem hd
    apply hfaith d
    intro x hxQ0
    let q : Q0 := ⟨x, hxQ0⟩
    have heq : conjHom d⁻¹ q = q := by
      have h := MonoidHom.mem_ker.mp hdInv
      exact congrArg (fun f : MulAut Q0 => f q) h
    have hcoe := congrArg Subtype.val heq
    simpa [conjHom, q, rightConjugateElem] using hcoe
  have hker : conjHom.ker = W.subgroupOf D :=
    le_antisymm hker_le hWker
  let rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0 :=
    QuotientGroup.lift (W.subgroupOf D) conjHom hWker
  have hrho_ker : rhoD.ker = ⊥ := by
    change
      (QuotientGroup.lift (W.subgroupOf D) conjHom hWker).ker = ⊥
    rw [QuotientGroup.ker_lift, hker, QuotientGroup.map_mk'_self]
  refine ⟨rhoD, (MonoidHom.ker_eq_bot_iff rhoD).mp hrho_ker, ?_⟩
  intro d q
  change
    (QuotientGroup.lift (W.subgroupOf D) conjHom hWker)
      (QuotientGroup.mk d) q = _
  rw [QuotientGroup.lift_mk]
  apply Subtype.ext
  simp [conjHom, rightConjugateElem]

private theorem proposition_3_quotient_transitive_on_Q0_nontrivial
    {G : Type*} [Group G]
    (D K W Q0 : Subgroup G)
    (hKWleD : K ⊔ W ≤ D)
    (hWD : (W.subgroupOf D).Normal)
    (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
    (hrhoD_coe : ∀ d : D, ∀ q : Q0,
      ((rhoD (QuotientGroup.mk d) q : Q0) : G) =
        rightConjugateElem (q : G) (d : G)⁻¹)
    (htrans :
      ∀ x : G, x ∈ Q0 → x ≠ 1 →
        ∀ y : G, y ∈ Q0 → y ≠ 1 →
          ∃ a : (K ⊔ W : Subgroup G), rightConjugateElem x (a : G) = y) :
    letI : (W.subgroupOf D).Normal := hWD
    letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
      MulDistribMulAction.compHom Q0 rhoD
    ∀ x : Q0, x ≠ 1 → ∀ y : Q0, y ≠ 1 →
      ∃ τ : ((K ⊔ W).subgroupOf D).map
          (QuotientGroup.mk' (W.subgroupOf D)),
        (τ : D ⧸ W.subgroupOf D) • x = y := by
  classical
  letI : (W.subgroupOf D).Normal := hWD
  letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
    MulDistribMulAction.compHom Q0 rhoD
  intro x hx y hy
  have hxG : (x : G) ≠ 1 := by
    intro h
    apply hx
    exact Subtype.ext h
  have hyG : (y : G) ≠ 1 := by
    intro h
    apply hy
    exact Subtype.ext h
  obtain ⟨a, ha⟩ :=
    htrans (x : G) x.property hxG (y : G) y.property hyG
  let d : D := ⟨(a : G)⁻¹, D.inv_mem (hKWleD a.property)⟩
  let u : D ⧸ W.subgroupOf D := QuotientGroup.mk d
  have huT : u ∈ ((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D)) := by
    refine ⟨d, ?_, rfl⟩
    change (d : G) ∈ K ⊔ W
    exact (K ⊔ W).inv_mem a.property
  let τ : ((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D)) := ⟨u, huT⟩
  refine ⟨τ, ?_⟩
  change rhoD u x = y
  apply Subtype.ext
  rw [show u = QuotientGroup.mk d from rfl, hrhoD_coe d x]
  simpa [d] using ha
/-
Source-gap audit: Peterfalvi invokes Appendix I, Proposition 2 after showing
that `KW/W` is cyclic normal in `D/W` and acts transitively on `Q0#`. The
current Section 2 setup plus `hVleD` and `hq0` gives only the local inclusions,
definitions, and two-power order input; it does not expose that quotient-action
package or the finite-field/semilinear coordinate construction. The field model
and cyclicity calls therefore stay inline in the public theorem proofs, not as
extra private proof-process declarations or an `External` interface.
-/

/-- The actual structural inputs used by the finite-field construction in
Section 2, Proposition 3.  The global action hypotheses `(A2)` and `(A3)` are
used upstream to produce these facts, but do not occur in the construction
itself. -/
public structure Proposition3FieldModelA1Data
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 : Subgroup G) (t : G) : Prop where
  hA1 : HypothesisA1 G Ω H D Q t
  K_le_D : K ≤ D
  K_def : ∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹
  V_eq : V = peterfalviV D t
  V_le_D : V ≤ D
  W_le_V : W ≤ V
  W_eq : W = peterfalviW V (K : Set G)
  Q0_def : ∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)
  K_cyclic : IsCyclic K
  K_normal_D : (K.subgroupOf D).Normal
  Q0_commutative : IsMulCommutative Q0
  Q0_sq : ∀ x : Q0, x ^ 2 = 1

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
public theorem proposition_3_field_model_with_q0_card_of_hypothesisA1
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 : Subgroup G) (t : G)
    (hsec : Proposition3FieldModelA1Data H D Q K V W Q0 t) :
    ∃ (n : ℕ) (_ : n ≠ 0),
      Nat.card Q0 = 2 ^ n ∧
      let F : Type := GaloisField 2 n
      letI : Field F := inferInstance
      letI : Finite F := inferInstance
      ∃ (A : Subgroup (F ≃+* F))
          (hWV : (W.subgroupOf V).Normal)
          (hWD : (W.subgroupOf D).Normal),
        letI : (W.subgroupOf V).Normal := hWV
        letI : (W.subgroupOf D).Normal := hWD
        ∃ (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
            (rhoMul : Fˣ →* MulAut (Multiplicative F))
            (rhoAut : A →* MulAut
              (SemidirectProduct (Multiplicative F) Fˣ rhoMul))
            (q0_add : Q0 ≃* Multiplicative F)
            (k_units : K ≃* Fˣ)
            (vmodW_aut : V ⧸ W.subgroupOf V ≃* A)
            (modelIso :
              SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
                SemidirectProduct
                  (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut),
          Nat.card Q0 = Nat.card F ∧
            (∀ u : Fˣ, ∀ a : Multiplicative F,
              rhoMul u a =
                Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F))) ∧
            (∀ σ : A, ∀ a : Multiplicative F,
              rhoAut σ (SemidirectProduct.inl a) =
                SemidirectProduct.inl
                  (Multiplicative.ofAdd
                    ((σ : F ≃+* F) (Multiplicative.toAdd a)))) ∧
            (∀ σ : A, ∀ u : Fˣ,
              rhoAut σ (SemidirectProduct.inr u) =
                SemidirectProduct.inr
                  (Units.map (σ : F ≃+* F).toMonoidWithZeroHom u)) ∧
            (∀ d : D, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0,
                rhoD (QuotientGroup.mk d) q =
                  ⟨rightConjugateElem (q : G) (d : G)⁻¹, hq⟩) ∧
            (∀ q : Q0,
              modelIso (SemidirectProduct.inl q) =
                SemidirectProduct.inl
                  (SemidirectProduct.inl (q0_add q))) ∧
            (∀ k : K,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      (⟨(k : G),
                        (Proposition3FieldModelA1Data.K_le_D (Ω := Ω) hsec)
                          k.property⟩ : D))) =
                SemidirectProduct.inl
                  (SemidirectProduct.inr (k_units k))) ∧
            (∀ v : V,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      (⟨(v : G),
                        (Proposition3FieldModelA1Data.V_le_D (Ω := Ω) hsec)
                          v.property⟩ : D))) =
                SemidirectProduct.inr
                  (vmodW_aut (QuotientGroup.mk v))) ∧
            (∀ k : K, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (k : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (k : G), hq⟩ =
                  Multiplicative.ofAdd
                    (Multiplicative.toAdd (q0_add q) *
                      (↑((k_units k)⁻¹) : F))) ∧
            (∀ v : V, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (v : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (v : G), hq⟩ =
                  Multiplicative.ofAdd
                    ((vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm
                      (Multiplicative.toAdd (q0_add q)))) := by
  classical
  have hVleD : V ≤ D := hsec.V_le_D
  have hQ0_conjugate : ∀ d : D, ∀ q : Q0,
      rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0 := by
    intro d q
    apply (hsec.Q0_def _).mpr
    rcases (hsec.Q0_def (q : G)).mp q.property with hq_one | hq
    · left
      simp [hq_one, rightConjugateElem]
    · right
      have hdH : (d : G) ∈ H := hsec.hA1.D_le_H d.property
      refine ⟨?_, isInvolution_rightConjugateElem hq.2⟩
      simpa [rightConjugateElem] using
        H.mul_mem (H.mul_mem hdH hq.1) (H.inv_mem hdH)
  rcases
      peterfalvi_chapter1_section2_proposition_3_appendixI_input
        H D Q K V W Q0 t hsec.hA1 hsec.K_le_D hsec.K_def hsec.V_eq
        hsec.W_le_V hsec.W_eq hsec.Q0_def hVleD hsec.K_cyclic
        hsec.K_normal_D with
    ⟨hWD, hKWleD, hKWmodW_cyclic, hKWmodW_normal, hfaith, htrans⟩
  obtain ⟨s, hsH, hsI, _hsStructure, hsQ0, _hVstabilizer, _hVfix⟩ :=
    peterfalvi_chapter1_section2_proposition_3_distinguished_involution
      H D Q V Q0 t hsec.hA1 hsec.V_eq hsec.Q0_def
  let sQ0 : Q0 := ⟨s, hsQ0⟩
  have hsQ0_ne : sQ0 ≠ 1 := by
    intro h
    apply hsI.ne_one
    simpa [sQ0] using congrArg Subtype.val h
  letI : Nontrivial Q0 := ⟨⟨sQ0, 1, hsQ0_ne⟩⟩
  letI : IsElementaryAbelian 2 Q0 :=
    isElementaryAbelian_two_of_forall_sq_one
      hsec.Q0_commutative hsec.Q0_sq
  have hpgroup : IsPGroup 2 Q0 := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hdiv : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (hsec.Q0_sq x)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with horder | horder
    · exact ⟨0, by simp [horder]⟩
    · exact ⟨1, by simp [horder]⟩
  obtain ⟨n, hQ0card⟩ := IsPGroup.exists_card_eq hpgroup
  have hn : n ≠ 0 := by
    intro hn0
    have hcardOne : Nat.card Q0 = 1 := by
      simpa [hn0] using hQ0card
    letI : Subsingleton Q0 := (Nat.card_eq_one_iff_unique.mp hcardOne).1
    exact hsQ0_ne (Subsingleton.elim sQ0 1)
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
      H D Q K V W t hsec.hA1 hsec.K_def hsec.V_eq hsec.W_eq
  rcases
      proposition_3_quotient_conjugation_action
        H D W Q0 hsec.hA1.D_le_H hsec.Q0_def hWcentralizer hWD hfaith with
    ⟨rhoD, hrhoD_injective, hrhoD⟩
  letI : (W.subgroupOf D).Normal := hWD
  letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
    MulDistribMulAction.compHom Q0 rhoD
  letI : FaithfulSMul (D ⧸ W.subgroupOf D) Q0 :=
    { eq_of_smul_eq_smul := fun h =>
        hrhoD_injective (MulEquiv.ext fun x => h x) }
  let T : Subgroup (D ⧸ W.subgroupOf D) :=
    ((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D))
  letI : T.Normal := by
    simpa [T] using hKWmodW_normal
  letI : IsCyclic T := by
    simpa [T] using hKWmodW_cyclic
  have hrhoD_coe : ∀ d : D, ∀ q : Q0,
      ((rhoD (QuotientGroup.mk d) q : Q0) : G) =
        rightConjugateElem (q : G) (d : G)⁻¹ := by
    intro d q
    exact congrArg Subtype.val (hrhoD d q)
  have htransT :
      ∀ x : Q0, x ≠ 1 → ∀ y : Q0, y ≠ 1 →
        ∃ τ : T, (τ : D ⧸ W.subgroupOf D) • x = y := by
    simpa [T] using
      proposition_3_quotient_transitive_on_Q0_nontrivial
        D K W Q0 hKWleD hWD rhoD hrhoD_coe htrans
  letI :
      Representation.IsIrreducible
        (AppendixIRepresentationOfT (p := 2) (E := Q0) T) :=
    proposition_3_appendixIRepresentation_irreducible_of_transitive T htransT
  obtain ⟨fieldInst, hfield⟩ :=
    peterfalvi_appendixI_proposition_2_a
      (p := 2) (n := n) (U := D ⧸ W.subgroupOf D) (E := Q0) T hQ0card
  let F0 := AppendixIFpT (p := 2) (E := Q0) T
  letI : Field F0 := fieldInst
  obtain ⟨_moduleInst, hfieldCard, _hfinrank, _hscalar⟩ := hfield
  have hF0isField : IsField F0 := by
    simpa [F0] using
      (Finite.isField_of_domain (AppendixIFpT (p := 2) (E := Q0) T))
  let canonicalField : Field F0 := hF0isField.toField
  letI : Field F0 := canonicalField
  let sAdd : Additive Q0 := Additive.ofMul sQ0
  have hsAdd_ne : sAdd ≠ 0 := by
    simpa [sAdd] using hsQ0_ne
  let toQ0 : F0 →+ Additive Q0 :=
    { toFun := fun a => a.1 sAdd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have htoQ0_injective : Function.Injective toQ0 := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra hne
    have hzeroEval : (a - b).1 sAdd = 0 := by
      change a.1 sAdd - b.1 sAdd = 0
      change toQ0 a - toQ0 b = 0
      rw [hab, sub_self]
    obtain ⟨cInv, hinv⟩ := hF0isField.mul_inv_cancel hne
    have hinv' : cInv * (a - b) = (1 : F0) := by
      rw [hF0isField.mul_comm]
      exact hinv
    have hsZero : sAdd = 0 := by
      calc
        sAdd = (1 : F0).1 sAdd := rfl
        _ = ((cInv * (a - b)) : F0).1 sAdd := by rw [hinv']
        _ = cInv.1 ((a - b).1 sAdd) := rfl
        _ = 0 := by
          rw [hzeroEval]
          exact cInv.1.map_zero
    exact hsAdd_ne hsZero
  letI : Fintype F0 := Fintype.ofFinite F0
  letI : Fintype (Additive Q0) := Fintype.ofFinite (Additive Q0)
  have hcardEq : Fintype.card F0 = Fintype.card (Additive Q0) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card (AppendixIFpT (p := 2) (E := Q0) T) = Nat.card Q0
    exact hfieldCard.trans hQ0card.symm
  have htoQ0_bijective : Function.Bijective toQ0 :=
    (Fintype.bijective_iff_injective_and_card toQ0).2
      ⟨htoQ0_injective, hcardEq⟩
  let coord : F0 ≃+ Additive Q0 :=
    AddEquiv.ofBijective toQ0 htoQ0_bijective
  let q0_add0 : Q0 ≃* Multiplicative F0 :=
    { toFun := fun q =>
        Multiplicative.ofAdd (coord.symm (Additive.ofMul q))
      invFun := fun a =>
        Additive.toMul (coord (Multiplicative.toAdd a))
      left_inv := fun q => by simp
      right_inv := fun a => by simp
      map_mul' := fun q r => by
        change coord.symm (Additive.ofMul (q * r)) =
          coord.symm (Additive.ofMul q) + coord.symm (Additive.ofMul r)
        exact coord.symm.map_add _ _ }
  have hq0_add0_s : q0_add0 sQ0 = Multiplicative.ofAdd 1 := by
    change coord.symm sAdd = 1
    apply coord.injective
    simp [coord, toQ0, sAdd]
  let tauF0 : T →* F0 :=
    { toFun := fun tau =>
        ⟨AppendixITActionEnd (p := 2) (E := Q0) T tau,
          Algebra.subset_adjoin (Set.mem_range_self tau)⟩
      map_one' := by
        ext x
        simp [AppendixITActionEnd_apply]
      map_mul' := by
        intro a b
        ext x
        simp [AppendixITActionEnd_apply, mul_smul] }
  have htauF0_q0 (tau : T) (x : Q0) :
      q0_add0 ((tau : D ⧸ W.subgroupOf D) • x) =
        Multiplicative.ofAdd
          (tauF0 tau * Multiplicative.toAdd (q0_add0 x)) := by
    apply Multiplicative.toAdd.injective
    change coord.symm
          (Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x)) =
        tauF0 tau * coord.symm (Additive.ofMul x)
    apply htoQ0_injective
    calc
      toQ0 (coord.symm
          (Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x))) =
          Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x) := by
            simpa [coord] using
              coord.apply_symm_apply
                (Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x))
      _ = (tauF0 tau).1 (Additive.ofMul x) := by
            simp [tauF0, AppendixITActionEnd_apply]
      _ = (tauF0 tau).1 (toQ0 (coord.symm (Additive.ofMul x))) := by
            rw [show toQ0 (coord.symm (Additive.ofMul x)) =
              Additive.ofMul x by
                simpa [coord] using coord.apply_symm_apply (Additive.ofMul x)]
      _ = toQ0 (tauF0 tau * coord.symm (Additive.ofMul x)) := rfl
  let F : Type := GaloisField 2 n
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F0 = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hfieldCard.trans (GaloisField.card 2 n hn).symm
  let g : F0 ≃+* F := FiniteField.ringEquivOfCardEq hcardF
  let gMul : Multiplicative F0 ≃* Multiplicative F :=
    { toFun := fun a =>
        Multiplicative.ofAdd (g (Multiplicative.toAdd a))
      invFun := fun a =>
        Multiplicative.ofAdd (g.symm (Multiplicative.toAdd a))
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_mul' := fun a b => by
        change g (Multiplicative.toAdd a + Multiplicative.toAdd b) =
          g (Multiplicative.toAdd a) + g (Multiplicative.toAdd b)
        exact g.map_add _ _ }
  let q0_add : Q0 ≃* Multiplicative F := q0_add0.trans gMul
  have hq0_add_s : q0_add sQ0 = Multiplicative.ofAdd 1 := by
    simpa [q0_add, gMul, hq0_add0_s] using (map_one g)
  let tauF : T →* F := g.toMonoidHom.comp tauF0
  have htauF_q0 (tau : T) (x : Q0) :
      q0_add ((tau : D ⧸ W.subgroupOf D) • x) =
        Multiplicative.ofAdd
          (tauF tau * Multiplicative.toAdd (q0_add x)) := by
    apply Multiplicative.toAdd.injective
    change g (Multiplicative.toAdd
          (q0_add0 ((tau : D ⧸ W.subgroupOf D) • x))) =
      g (tauF0 tau) * g (Multiplicative.toAdd (q0_add0 x))
    rw [congrArg Multiplicative.toAdd (htauF0_q0 tau x)]
    exact g.map_mul _ _
  let tauUnits : T →* Fˣ :=
    MonoidHom.toHomUnits (G := T) (M := F) tauF
  have htauUnits_bijective : Function.Bijective tauUnits := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply FaithfulSMul.eq_of_smul_eq_smul (α := Q0)
      intro x
      apply q0_add.injective
      rw [htauF_q0, htauF_q0]
      have hval := congrArg Units.val hab
      change tauF a = tauF b at hval
      rw [hval]
    · intro u
      let y : Q0 := q0_add.symm
        (Multiplicative.ofAdd ((u : F) * Multiplicative.toAdd (q0_add sQ0)))
      have hy : y ≠ 1 := by
        intro hyone
        have hcoord := congrArg
          (fun z : Q0 => Multiplicative.toAdd (q0_add z)) hyone
        have hu_zero : (u : F) = 0 := by
          simpa [y, hq0_add_s] using hcoord
        exact Units.ne_zero u hu_zero
      obtain ⟨tau, htau⟩ := htransT sQ0 hsQ0_ne y hy
      refine ⟨tau, ?_⟩
      apply Units.ext
      have hcoord := congrArg
        (fun z : Q0 => Multiplicative.toAdd (q0_add z)) htau
      simpa [tauUnits, htauF_q0, y, hq0_add_s] using hcoord
  let scalarSet : Set F := Set.range tauF
  have hscalarSet_closure : Subring.closure scalarSet = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hx : x = 0
    · subst x
      exact (Subring.closure scalarSet).zero_mem
    · let u : Fˣ := Units.mk0 x hx
      obtain ⟨tau, htau⟩ := htauUnits_bijective.2 u
      apply Subring.subset_closure
      refine ⟨tau, ?_⟩
      have hval := congrArg Units.val htau
      simpa [tauUnits, u] using hval
  have hscalar_eq_action (tau : T) (x : Q0) :
      q0_add.symm
          (Multiplicative.ofAdd
            (tauF tau * Multiplicative.toAdd (q0_add x))) =
        (tau : D ⧸ W.subgroupOf D) • x := by
    apply q0_add.injective
    simpa using (htauF_q0 tau x).symm
  have hconjT : ∀ (u : D ⧸ W.subgroupOf D) (lambda : F),
      lambda ∈ scalarSet → ∃ c : F, ∀ x : Q0,
        rhoD u (q0_add.symm
            (Multiplicative.ofAdd
              (lambda * Multiplicative.toAdd (q0_add x)))) =
          q0_add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0_add (rhoD u x)))) := by
    intro u lambda hlambda
    rcases hlambda with ⟨tau, rfl⟩
    let tau' : T :=
      ⟨u * (tau : D ⧸ W.subgroupOf D) * u⁻¹,
        (inferInstance : T.Normal).conj_mem (tau : D ⧸ W.subgroupOf D) tau.property u⟩
    refine ⟨tauF tau', ?_⟩
    intro x
    rw [hscalar_eq_action, hscalar_eq_action]
    change rhoD u (rhoD (tau : D ⧸ W.subgroupOf D) x) =
      rhoD (tau' : D ⧸ W.subgroupOf D) (rhoD u x)
    calc
      rhoD u (rhoD (tau : D ⧸ W.subgroupOf D) x) =
          rhoD (u * (tau : D ⧸ W.subgroupOf D)) x := by
            rw [map_mul]
            rfl
      _ = rhoD ((tau' : D ⧸ W.subgroupOf D) * u) x := by
            congr 2
            simp [tau', mul_assoc]
      _ = rhoD (tau' : D ⧸ W.subgroupOf D) (rhoD u x) := by
            rw [map_mul]
            rfl
  have hsQ0_val_ne : (sQ0 : G) ≠ 1 := by
    simpa [sQ0] using hsI.ne_one
  rcases peterfalvi_appendixI_proposition_2_b
      Q0 q0_add rhoD hrhoD_injective sQ0 hsQ0_val_ne
        scalarSet hscalarSet_closure hconjT with
    ⟨sigmaHom, hsemilinear, hstabilizer⟩
  let C : Subgroup (D ⧸ W.subgroupOf D) :=
    { carrier := {u | rhoD u sQ0 = sQ0}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        change rhoD (u * v) sQ0 = sQ0
        rw [map_mul]
        change rhoD u (rhoD v sQ0) = sQ0
        rw [hv, hu]
      inv_mem' := by
        intro u hu
        change rhoD u⁻¹ sQ0 = sQ0
        rw [map_inv]
        change (rhoD u)⁻¹ sQ0 = sQ0
        apply (rhoD u).injective
        simpa using hu.symm }
  change ∃ (A : Subgroup (F ≃+* F)) (e : C ≃* A),
    ∀ u : C, (e u : F ≃+* F) = sigmaHom u at hstabilizer
  obtain ⟨A, c_aut, hc_aut⟩ := hstabilizer
  have hWleD : W ≤ D := hsec.W_le_V.trans hVleD
  have hWV : (W.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff hsec.W_le_V).2 (by
      intro w v hw hv
      have hconj := hWD.conj_mem
        (⟨w, hWleD hw⟩ : D) hw (⟨v, hVleD hv⟩ : D)
      exact hconj)
  letI : (W.subgroupOf V).Normal := hWV
  let vToD : V →* D := Subgroup.inclusion hVleD
  let vToU : V →* (D ⧸ W.subgroupOf D) :=
    (QuotientGroup.mk' (W.subgroupOf D)).comp vToD
  have hvToU_ker : vToU.ker = W.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker]
    change ((vToD v : D) : D ⧸ W.subgroupOf D) = 1 ↔
      (v : G) ∈ W
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hvToU_range : vToU.range = C := by
    apply le_antisymm
    · intro u hu
      rcases hu with ⟨v, rfl⟩
      change rhoD (vToU v) sQ0 = sQ0
      rw [show vToU v = QuotientGroup.mk (vToD v) by rfl, hrhoD]
      apply Subtype.ext
      simpa [vToD, sQ0] using _hVfix (v⁻¹)
    · intro u hu
      obtain ⟨d, rfl⟩ :=
        QuotientGroup.mk'_surjective (W.subgroupOf D) u
      have hfix : rhoD (QuotientGroup.mk d) sQ0 = sQ0 := hu
      have hright : rightConjugateElem s (d : G)⁻¹ = s := by
        exact congrArg Subtype.val ((hrhoD d sQ0).symm.trans hfix)
      have hcomm : s * (d : G) = (d : G) * s := by
        have hcomm' : (d : G) * s = s * (d : G) := by
          calc
            (d : G) * s =
                ((d : G) * s * (d : G)⁻¹) * (d : G) := by group
            _ = s * (d : G) := by
              simpa [rightConjugateElem] using
                congrArg (fun z : G => z * (d : G)) hright
        exact hcomm'.symm
      have hdCentralizer : (d : G) ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : x = s := by simpa using hx
        subst x
        exact hcomm
      have hdV : (d : G) ∈ V := by
        rw [_hVstabilizer]
        exact ⟨d.property, hdCentralizer⟩
      refine ⟨⟨(d : G), hdV⟩, ?_⟩
      rfl
  let vmodW_C : V ⧸ W.subgroupOf V ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hvToU_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange vToU).trans
        (MulEquiv.subgroupCongr hvToU_range))
  let vmodW_aut : V ⧸ W.subgroupOf V ≃* A := vmodW_C.trans c_aut
  let piD : D →* D ⧸ W.subgroupOf D :=
    QuotientGroup.mk' (W.subgroupOf D)
  have hpiK_injective :
      Function.Injective (piD.subgroupMap (K.subgroupOf D)) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hpixy : piD (x : D) = piD (y : D) :=
      congrArg Subtype.val hxy
    have hdivW_D : (x : D) / (y : D) ∈ W.subgroupOf D :=
      QuotientGroup.eq_iff_div_mem.mp hpixy
    let z : G := (x : G) / (y : G)
    have hzW : z ∈ W := hdivW_D
    have hzK : z ∈ K := by
      simpa [z, div_eq_mul_inv] using
        K.mul_mem x.property (K.inv_mem y.property)
    have hzV : z ∈ V := hsec.W_le_V hzW
    have hzCent : z ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hsec.V_eq] at hzV
      exact hzV.2
    have hzFix : rightConjugateElem z t = z := by
      have hcomm : t * z = z * t :=
        (Subgroup.mem_centralizer_iff.mp hzCent) t (by simp)
      calc
        rightConjugateElem z t = t⁻¹ * (z * t) := by
          rw [rightConjugateElem, mul_assoc]
        _ = t⁻¹ * (t * z) := by rw [← hcomm]
        _ = z := by simp
    have hzInv : rightConjugateElem z t = z⁻¹ :=
      ((hsec.K_def z).mp hzK).2
    have hzEqInv : z = z⁻¹ := hzFix.symm.trans hzInv
    have hz2 : z ^ 2 = 1 := by
      calc
        z ^ 2 = z * z := pow_two z
        _ = z * z⁻¹ := congrArg (z * ·) hzEqInv
        _ = 1 := mul_inv_cancel z
    have hzD : z ∈ D := ((hsec.K_def z).mp hzK).1
    have hzOne : z = 1 := by
      by_contra hzNe
      exact
        (not_isInvolution_of_mem_odd_subgroup
          D hsec.hA1.D_odd hzD) ⟨hzNe, hz2⟩
    change (x : G) = (y : G)
    exact div_eq_one.mp hzOne
  let kD : K ≃* K.subgroupOf D :=
    (Subgroup.subgroupOfEquivOfLe hsec.K_le_D).symm
  let kImage : K.subgroupOf D ≃* (K.subgroupOf D).map piD :=
    MulEquiv.ofBijective (piD.subgroupMap (K.subgroupOf D))
      ⟨hpiK_injective, piD.subgroupMap_surjective (K.subgroupOf D)⟩
  have hTK : T = (K.subgroupOf D).map piD := by
    simpa [T, piD] using
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_eq_KmodW
        D K V W hsec.K_le_D hsec.W_le_V hVleD hWD
  let kT : K ≃* T :=
    kD.trans (kImage.trans (MulEquiv.subgroupCongr hTK.symm))
  let tUnits : T ≃* Fˣ :=
    MulEquiv.ofBijective tauUnits htauUnits_bijective
  let k_units : K ≃* Fˣ := kT.trans tUnits
  have hC_stabilizer :
      C = MulAction.stabilizer (D ⧸ W.subgroupOf D) sQ0 := by
    ext u
    rfl
  have hT_free :
      ∀ tau : T, (tau : D ⧸ W.subgroupOf D) • sQ0 = sQ0 → tau = 1 := by
    intro tau htau
    apply htauUnits_bijective.1
    apply Units.ext
    have hcoord := congrArg
      (fun z : Q0 => Multiplicative.toAdd (q0_add z)) htau
    simpa [tauUnits, htauF_q0, hq0_add_s] using hcoord
  have hT_move_back :
      ∀ u : D ⧸ W.subgroupOf D,
        ∃ tau : T, (tau : D ⧸ W.subgroupOf D) • u • sQ0 = sQ0 := by
    intro u
    have hu_ne : u • sQ0 ≠ 1 := by
      intro hu
      apply hsQ0_ne
      change rhoD u sQ0 = 1 at hu
      have hback := congrArg (rhoD u)⁻¹ hu
      simpa using hback
    exact htransT (u • sQ0) hu_ne sQ0 hsQ0_ne
  have hTC : T.IsComplement' C := by
    rw [hC_stabilizer]
    exact Subgroup.isComplement'_stabilizer sQ0 hT_free hT_move_back
  let rhoTC : C →* MulAut T :=
    (T.normalizerMonoidHom).comp
      (Subgroup.inclusion (T.normalizer_eq_top ▸ le_top))
  let tc_U :
      SemidirectProduct T C rhoTC ≃* (D ⧸ W.subgroupOf D) := by
    simpa [rhoTC] using SemidirectProduct.mulEquivSubgroup hTC
  let rhoMul : Fˣ →* MulAut (Multiplicative F) :=
    (MulAutMultiplicative F).symm.toMonoidHom.comp
      (DistribMulAction.toAddAut Fˣ F)
  let sigmaAdd (sigma : F ≃+* F) : MulAut (Multiplicative F) :=
    AddEquiv.toMultiplicative sigma.toAddEquiv
  let sigmaUnits (sigma : F ≃+* F) : MulAut Fˣ :=
    Units.mapEquiv sigma.toMulEquiv
  have hsigma_compat (sigma : F ≃+* F) : ∀ u : Fˣ,
      (rhoMul u).trans (sigmaAdd sigma) =
        (sigmaAdd sigma).trans (rhoMul (sigmaUnits sigma u)) := by
    intro u
    apply MulEquiv.ext
    intro a
    change Multiplicative.ofAdd
        (sigma ((u : F) * Multiplicative.toAdd a)) =
      Multiplicative.ofAdd
        (sigma (u : F) * sigma (Multiplicative.toAdd a))
    rw [map_mul]
  let affineAut (sigma : F ≃+* F) :
      MulAut (SemidirectProduct (Multiplicative F) Fˣ rhoMul) :=
    SemidirectProduct.congr
      (sigmaAdd sigma) (sigmaUnits sigma) (hsigma_compat sigma)
  let rhoAut :
      A →* MulAut (SemidirectProduct (Multiplicative F) Fˣ rhoMul) :=
    { toFun := fun sigma => affineAut (sigma : F ≃+* F)
      map_one' := by
        apply MulEquiv.ext
        rintro ⟨a, u⟩
        rfl
      map_mul' := by
        intro sigma tau
        apply MulEquiv.ext
        rintro ⟨a, u⟩
        rfl }
  have hrhoMul :
      ∀ u : Fˣ, ∀ a : Multiplicative F,
        rhoMul u a =
          Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F)) := by
    intro u a
    change Multiplicative.ofAdd ((u : F) * Multiplicative.toAdd a) =
      Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F))
    rw [mul_comm]
  have hrhoAut_inl :
      ∀ sigma : A, ∀ a : Multiplicative F,
        rhoAut sigma (SemidirectProduct.inl a) =
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((sigma : F ≃+* F) (Multiplicative.toAdd a))) := by
    intro sigma a
    apply SemidirectProduct.ext <;>
      simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
  have hrhoAut_inr :
      ∀ sigma : A, ∀ u : Fˣ,
        rhoAut sigma (SemidirectProduct.inr u) =
          SemidirectProduct.inr
            (Units.map (sigma : F ≃+* F).toMonoidWithZeroHom u) := by
    intro sigma u
    apply SemidirectProduct.ext
    · simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
    · simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
      apply Units.ext
      rfl
  have hrhoAut_right (sigma : A)
      (x : SemidirectProduct (Multiplicative F) Fˣ rhoMul) :
      (rhoAut sigma x).right =
        sigmaUnits (sigma : F ≃+* F) x.right := by
    rfl
  have hT_action (tau : T) (q : Q0) :
      q0_add (rhoD (tau : D ⧸ W.subgroupOf D) q) =
        rhoMul (tUnits tau) (q0_add q) := by
    rw [hrhoMul]
    change q0_add ((tau : D ⧸ W.subgroupOf D) • q) =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (q0_add q) * tauF tau)
    rw [htauF_q0]
    congr 1
    exact mul_comm _ _
  have hC_action (c : C) (q : Q0) :
      q0_add (rhoD (c : D ⧸ W.subgroupOf D) q) =
        sigmaAdd (c_aut c) (q0_add q) := by
    let lambda : F := Multiplicative.toAdd (q0_add q)
    have hsemi := hsemilinear
      (c : D ⧸ W.subgroupOf D) lambda sQ0
    have hcfix : rhoD (c : D ⧸ W.subgroupOf D) sQ0 = sQ0 :=
      c.property
    have hcoord := congrArg
      (fun z : Q0 => Multiplicative.toAdd (q0_add z)) hsemi
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd
        (q0_add (rhoD (c : D ⧸ W.subgroupOf D) q)) =
      (c_aut c : F ≃+* F) lambda
    simpa [lambda, hq0_add_s, hcfix, hc_aut c] using hcoord
  have htauF_from_s (tau : T) :
      tauF tau =
        Multiplicative.toAdd
          (q0_add ((tau : D ⧸ W.subgroupOf D) • sQ0)) := by
    have hcoord := congrArg Multiplicative.toAdd
      (htauF_q0 tau sQ0)
    simpa [hq0_add_s] using hcoord.symm
  have hrhoTC_coe (c : C) (tau : T) :
      ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) =
        (c : D ⧸ W.subgroupOf D) *
          (tau : D ⧸ W.subgroupOf D) *
            (c : D ⧸ W.subgroupOf D)⁻¹ := by
    rfl
  have hC_on_T (c : C) (tau : T) :
      tUnits (rhoTC c tau) = sigmaUnits (c_aut c) (tUnits tau) := by
    apply Units.ext
    change tauF (rhoTC c tau) =
      (c_aut c : F ≃+* F) (tauF tau)
    rw [htauF_from_s, htauF_from_s]
    have hcfix : rhoD (c : D ⧸ W.subgroupOf D) sQ0 = sQ0 :=
      c.property
    have hcinvfix :
        rhoD (c : D ⧸ W.subgroupOf D)⁻¹ sQ0 = sQ0 := by
      rw [map_inv]
      change (rhoD (c : D ⧸ W.subgroupOf D))⁻¹ sQ0 = sQ0
      apply (rhoD (c : D ⧸ W.subgroupOf D)).injective
      simpa using hcfix.symm
    have hact :
        ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) • sQ0 =
          (c : D ⧸ W.subgroupOf D) •
            ((tau : D ⧸ W.subgroupOf D) • sQ0) := by
      change rhoD ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) sQ0 =
        rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D) sQ0)
      rw [hrhoTC_coe, map_mul, map_mul]
      change rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D)
            (rhoD (c : D ⧸ W.subgroupOf D)⁻¹ sQ0)) =
        rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D) sQ0)
      rw [hcinvfix]
    rw [hact]
    exact congrArg Multiplicative.toAdd
      (hC_action c ((tau : D ⧸ W.subgroupOf D) • sQ0)
        |>.trans rfl)
  have htc_U_apply (z : SemidirectProduct T C rhoTC) :
      tc_U z =
        (z.1 : D ⧸ W.subgroupOf D) *
          (z.2 : D ⧸ W.subgroupOf D) := by
    rfl
  let modelHom :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD →*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    { toFun := fun x =>
        let z := tc_U.symm x.2
        ⟨⟨q0_add x.1, tUnits z.1⟩, c_aut z.2⟩
      map_one' := by
        simp
      map_mul' := by
        rintro ⟨q, u⟩ ⟨q', u'⟩
        obtain ⟨z, rfl⟩ := tc_U.surjective u
        obtain ⟨z', rfl⟩ := tc_U.surjective u'
        rcases z with ⟨tau, c⟩
        rcases z' with ⟨tau', c'⟩
        dsimp
        rw [← map_mul tc_U, tc_U.symm_apply_apply]
        apply SemidirectProduct.ext
        · apply SemidirectProduct.ext
          · simp only [SemidirectProduct.mul_left, tc_U.symm_apply_apply, map_mul]
            rw [htc_U_apply, map_mul]
            change q0_add q *
                q0_add (rhoD (tau : D ⧸ W.subgroupOf D)
                  (rhoD (c : D ⧸ W.subgroupOf D) q')) =
              q0_add q *
                rhoMul (tUnits tau)
                  (sigmaAdd (c_aut c) (q0_add q'))
            rw [hT_action, hC_action]
          · rw [tc_U.symm_apply_apply, tc_U.symm_apply_apply]
            simp only [SemidirectProduct.mul_left,
              SemidirectProduct.mul_right]
            calc
              tUnits (tau * rhoTC c tau') =
                  tUnits tau * tUnits (rhoTC c tau') :=
                tUnits.map_mul tau (rhoTC c tau')
              _ = tUnits tau *
                    sigmaUnits (c_aut c) (tUnits tau') :=
                congrArg (tUnits tau * ·) (hC_on_T c tau')
              _ = tUnits tau *
                    (rhoAut (c_aut c)
                      ⟨q0_add q', tUnits tau'⟩).right :=
                congrArg (tUnits tau * ·)
                  (hrhoAut_right (c_aut c)
                    ⟨q0_add q', tUnits tau'⟩).symm
        · simpa only [SemidirectProduct.mul_right,
            tc_U.symm_apply_apply] using c_aut.map_mul c c' }
  let modelEquiv :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    { toFun := fun x =>
        let z := tc_U.symm x.2
        ⟨⟨q0_add x.1, tUnits z.1⟩, c_aut z.2⟩
      invFun := fun y =>
        ⟨q0_add.symm y.1.1,
          tc_U ⟨tUnits.symm y.1.2, c_aut.symm y.2⟩⟩
      left_inv := by
        rintro ⟨q, u⟩
        obtain ⟨z, rfl⟩ := tc_U.surjective u
        rcases z with ⟨tau, c⟩
        apply SemidirectProduct.ext
        · simp
        · simp
      right_inv := by
        rintro ⟨⟨a, u⟩, sigma⟩
        apply SemidirectProduct.ext
        · apply SemidirectProduct.ext
          · simp
          · simp
        · simp }
  let modelIso :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    MulEquiv.ofBijective modelHom modelEquiv.bijective
  have hkT_coe (k : K) :
      (kT k : D ⧸ W.subgroupOf D) =
        QuotientGroup.mk
          (⟨(k : G), hsec.K_le_D k.property⟩ : D) := by
    rfl
  have hvmodW_C_coe (v : V) :
      ((vmodW_C (QuotientGroup.mk v) : C) :
          D ⧸ W.subgroupOf D) =
        QuotientGroup.mk
          (⟨(v : G), hVleD v.property⟩ : D) := by
    rfl
  have htc_K_decomp (k : K) :
      tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D)) =
        SemidirectProduct.inl (kT k) := by
    apply tc_U.injective
    rw [tc_U.apply_symm_apply, htc_U_apply]
    simpa using (hkT_coe k).symm
  have htc_V_decomp (v : V) :
      tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D)) =
        SemidirectProduct.inr
          (vmodW_C (QuotientGroup.mk v)) := by
    apply tc_U.injective
    rw [tc_U.apply_symm_apply, htc_U_apply]
    simpa using (hvmodW_C_coe v).symm
  have hmodel_q :
      ∀ q : Q0,
        modelIso (SemidirectProduct.inl q) =
          SemidirectProduct.inl
            (SemidirectProduct.inl (q0_add q)) := by
    intro q
    change (⟨⟨q0_add q, tUnits (tc_U.symm 1).1⟩,
        c_aut (tc_U.symm 1).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inl
          (SemidirectProduct.inl (q0_add q))
    simp
  have hmodel_k :
      ∀ k : K,
        modelIso
            (SemidirectProduct.inr
              (QuotientGroup.mk
                (⟨(k : G), hsec.K_le_D k.property⟩ : D))) =
          SemidirectProduct.inl
            (SemidirectProduct.inr (k_units k)) := by
    intro k
    change (⟨⟨q0_add 1,
        tUnits (tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D))).1⟩,
        c_aut (tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D))).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inl
          (SemidirectProduct.inr (k_units k))
    rw [htc_K_decomp]
    simp [k_units]
  have hmodel_v :
      ∀ v : V,
        modelIso
            (SemidirectProduct.inr
              (QuotientGroup.mk
                (⟨(v : G), hVleD v.property⟩ : D))) =
          SemidirectProduct.inr
            (vmodW_aut (QuotientGroup.mk v)) := by
    intro v
    change (⟨⟨q0_add 1,
        tUnits (tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D))).1⟩,
        c_aut (tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D))).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inr
          (vmodW_aut (QuotientGroup.mk v))
    rw [htc_V_decomp]
    simp [vmodW_aut]
  have hmodel_card : Nat.card Q0 = Nat.card F :=
    hQ0card.trans (GaloisField.card 2 n hn).symm
  have hrhoD_exists :
      ∀ d : D, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0,
          rhoD (QuotientGroup.mk d) q =
            ⟨rightConjugateElem (q : G) (d : G)⁻¹, hq⟩ := by
    intro d q
    let hq := hQ0_conjugate d q
    exact ⟨hq, hrhoD d q⟩
  have hk_action :
      ∀ k : K, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (k : G) ∈ Q0,
          q0_add ⟨rightConjugateElem (q : G) (k : G), hq⟩ =
            Multiplicative.ofAdd
              (Multiplicative.toAdd (q0_add q) *
                (↑((k_units k)⁻¹) : F)) := by
    intro k q
    let kInv : K := k⁻¹
    let d : D := ⟨(kInv : G), hsec.K_le_D kInv.property⟩
    let hq := hQ0_conjugate d q
    have hq' : rightConjugateElem (q : G) (k : G) ∈ Q0 := by
      simpa [d, kInv] using hq
    refine ⟨hq', ?_⟩
    have hcoe : (kT kInv : D ⧸ W.subgroupOf D) = QuotientGroup.mk d := by
      simpa [d] using hkT_coe kInv
    have haction := hT_action (kT kInv) q
    have hrho_eq :
        rhoD (kT kInv : D ⧸ W.subgroupOf D) q =
          ⟨rightConjugateElem (q : G) (k : G), hq'⟩ := by
      apply Subtype.ext
      rw [hcoe]
      simpa [d, kInv] using congrArg Subtype.val (hrhoD d q)
    rw [← hrho_eq, haction, hrhoMul]
    simp [kInv, k_units]
  have hv_action :
      ∀ v : V, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (v : G) ∈ Q0,
          q0_add ⟨rightConjugateElem (q : G) (v : G), hq⟩ =
            Multiplicative.ofAdd
              ((vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm
                (Multiplicative.toAdd (q0_add q))) := by
    intro v q
    let vInv : V := v⁻¹
    let d : D := ⟨(vInv : G), hVleD vInv.property⟩
    let c : C := vmodW_C (QuotientGroup.mk vInv)
    let hq := hQ0_conjugate d q
    have hq' : rightConjugateElem (q : G) (v : G) ∈ Q0 := by
      simpa [d, vInv] using hq
    refine ⟨hq', ?_⟩
    have hcoe : (c : D ⧸ W.subgroupOf D) = QuotientGroup.mk d := by
      simpa [c, d] using hvmodW_C_coe vInv
    have haction := hC_action c q
    have hrho_eq :
        rhoD (c : D ⧸ W.subgroupOf D) q =
          ⟨rightConjugateElem (q : G) (v : G), hq'⟩ := by
      apply Subtype.ext
      rw [hcoe]
      simpa [d, vInv] using congrArg Subtype.val (hrhoD d q)
    have hmkInv :
        (QuotientGroup.mk vInv : V ⧸ W.subgroupOf V) =
          (QuotientGroup.mk v : V ⧸ W.subgroupOf V)⁻¹ := by
      simp [vInv]
    have hcAut :
        (c_aut c : F ≃+* F) =
          (vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm := by
      calc
        (c_aut c : F ≃+* F) =
            (vmodW_aut (QuotientGroup.mk vInv) : F ≃+* F) := rfl
        _ = (vmodW_aut ((QuotientGroup.mk v)⁻¹) : F ≃+* F) := by rw [hmkInv]
        _ = (vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm := by
          exact congrArg Subtype.val (map_inv vmodW_aut (QuotientGroup.mk v))
    rw [← hrho_eq, haction]
    change Multiplicative.ofAdd
        ((c_aut c : F ≃+* F) (Multiplicative.toAdd (q0_add q))) = _
    rw [hcAut]
  refine ⟨n, hn, hQ0card, A, hWV, hWD,
    rhoD, rhoMul, rhoAut, q0_add, k_units, vmodW_aut, modelIso, ?_⟩
  exact ⟨hmodel_card, hrhoMul, hrhoAut_inl, hrhoAut_inr,
    hrhoD_exists, hmodel_q, hmodel_k, hmodel_v, hk_action, hv_action⟩

set_option maxHeartbeats 1600000 in
set_option backward.isDefEq.respectTransparency false in
public theorem proposition_3_field_model_with_q0_card
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
    ∃ (n : ℕ) (_ : n ≠ 0),
      Nat.card Q0 = 2 ^ n ∧
      let F : Type := GaloisField 2 n
      letI : Field F := inferInstance
      letI : Finite F := inferInstance
      ∃ (A : Subgroup (F ≃+* F))
          (hWV : (W.subgroupOf V).Normal)
          (hWD : (W.subgroupOf D).Normal),
        letI : (W.subgroupOf V).Normal := hWV
        letI : (W.subgroupOf D).Normal := hWD
        ∃ (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
            (rhoMul : Fˣ →* MulAut (Multiplicative F))
            (rhoAut : A →* MulAut
              (SemidirectProduct (Multiplicative F) Fˣ rhoMul))
            (q0_add : Q0 ≃* Multiplicative F)
            (k_units : K ≃* Fˣ)
            (vmodW_aut : V ⧸ W.subgroupOf V ≃* A)
            (modelIso :
              SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
                SemidirectProduct
                  (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut),
          Nat.card Q0 = Nat.card F ∧
            (∀ u : Fˣ, ∀ a : Multiplicative F,
              rhoMul u a =
                Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F))) ∧
            (∀ σ : A, ∀ a : Multiplicative F,
              rhoAut σ (SemidirectProduct.inl a) =
                SemidirectProduct.inl
                  (Multiplicative.ofAdd
                    ((σ : F ≃+* F) (Multiplicative.toAdd a)))) ∧
            (∀ σ : A, ∀ u : Fˣ,
              rhoAut σ (SemidirectProduct.inr u) =
                SemidirectProduct.inr
                  (Units.map (σ : F ≃+* F).toMonoidWithZeroHom u)) ∧
            (∀ d : D, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0,
                rhoD (QuotientGroup.mk d) q =
                  ⟨rightConjugateElem (q : G) (d : G)⁻¹, hq⟩) ∧
            (∀ q : Q0,
              modelIso (SemidirectProduct.inl q) =
                SemidirectProduct.inl
                  (SemidirectProduct.inl (q0_add q))) ∧
            (∀ k : K,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      ⟨(k : G), hsec.K_le_D k.property⟩)) =
                SemidirectProduct.inl
                  (SemidirectProduct.inr (k_units k))) ∧
            (∀ v : V,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      ⟨(v : G),
                        (proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec)
                          v.property⟩)) =
                SemidirectProduct.inr
                  (vmodW_aut (QuotientGroup.mk v))) ∧
            (∀ k : K, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (k : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (k : G), hq⟩ =
                  Multiplicative.ofAdd
                    (Multiplicative.toAdd (q0_add q) *
                      (↑((k_units k)⁻¹) : F))) ∧
            (∀ v : V, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (v : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (v : G), hq⟩ =
                  Multiplicative.ofAdd
                    ((vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm
                      (Multiplicative.toAdd (q0_add q)))) := by
  classical
  have hVleD : V ≤ D :=
    proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec
  have hprop1c := proposition_1_c H D Q K V W Q0 S Q1 t hsec
  have hprop2 := proposition_2 H D Q K V W Q0 S Q1 t hsec
  rcases
      peterfalvi_chapter1_section2_proposition_3_appendixI_input
        H D Q K V W Q0 t hsec.hA.A1 hsec.K_le_D hsec.K_def hsec.V_eq
        hsec.W_le_V hsec.W_eq hsec.Q0_def hVleD hprop2.1 hprop2.2 with
    ⟨hWD, hKWleD, hKWmodW_cyclic, hKWmodW_normal, hfaith, htrans⟩
  obtain ⟨s, hsH, hsI, _hsStructure, hsQ0, _hVstabilizer, _hVfix⟩ :=
    peterfalvi_chapter1_section2_proposition_3_distinguished_involution
      H D Q V Q0 t hsec.hA.A1 hsec.V_eq hsec.Q0_def
  let sQ0 : Q0 := ⟨s, hsQ0⟩
  have hsQ0_ne : sQ0 ≠ 1 := by
    intro h
    apply hsI.ne_one
    simpa [sQ0] using congrArg Subtype.val h
  letI : Nontrivial Q0 := ⟨⟨sQ0, 1, hsQ0_ne⟩⟩
  letI : IsElementaryAbelian 2 Q0 :=
    isElementaryAbelian_two_of_forall_sq_one hprop1c.2.1 hprop1c.2.2
  have hpgroup : IsPGroup 2 Q0 := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hdiv : orderOf x ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (hprop1c.2.2 x)
    rcases (Nat.dvd_prime Nat.prime_two).1 hdiv with horder | horder
    · exact ⟨0, by simp [horder]⟩
    · exact ⟨1, by simp [horder]⟩
  obtain ⟨n, hQ0card⟩ := IsPGroup.exists_card_eq hpgroup
  have hn : n ≠ 0 := by
    intro hn0
    have hcardOne : Nat.card Q0 = 1 := by
      simpa [hn0] using hQ0card
    letI : Subsingleton Q0 := (Nat.card_eq_one_iff_unique.mp hcardOne).1
    exact hsQ0_ne (Subsingleton.elim sQ0 1)
  have hWcentralizer :
      W = D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
      H D Q K V W t hsec.hA.A1 hsec.K_def hsec.V_eq hsec.W_eq
  rcases
      proposition_3_quotient_conjugation_action
        H D W Q0 hsec.hA.A1.D_le_H hsec.Q0_def hWcentralizer hWD hfaith with
    ⟨rhoD, hrhoD_injective, hrhoD⟩
  letI : (W.subgroupOf D).Normal := hWD
  letI : MulDistribMulAction (D ⧸ W.subgroupOf D) Q0 :=
    MulDistribMulAction.compHom Q0 rhoD
  letI : FaithfulSMul (D ⧸ W.subgroupOf D) Q0 :=
    { eq_of_smul_eq_smul := fun h =>
        hrhoD_injective (MulEquiv.ext fun x => h x) }
  let T : Subgroup (D ⧸ W.subgroupOf D) :=
    ((K ⊔ W).subgroupOf D).map
      (QuotientGroup.mk' (W.subgroupOf D))
  letI : T.Normal := by
    simpa [T] using hKWmodW_normal
  letI : IsCyclic T := by
    simpa [T] using hKWmodW_cyclic
  have hrhoD_coe : ∀ d : D, ∀ q : Q0,
      ((rhoD (QuotientGroup.mk d) q : Q0) : G) =
        rightConjugateElem (q : G) (d : G)⁻¹ := by
    intro d q
    exact congrArg Subtype.val (hrhoD d q)
  have htransT :
      ∀ x : Q0, x ≠ 1 → ∀ y : Q0, y ≠ 1 →
        ∃ τ : T, (τ : D ⧸ W.subgroupOf D) • x = y := by
    simpa [T] using
      proposition_3_quotient_transitive_on_Q0_nontrivial
        D K W Q0 hKWleD hWD rhoD hrhoD_coe htrans
  haveI : IsSimpleOrder (Subrepresentation (AppendixIRepresentationOfT (p := 2) (E := Q0) T)) :=
    proposition_3_appendixIRepresentation_irreducible_of_transitive T htransT
  obtain ⟨fieldInst, hfield⟩ :=
    peterfalvi_appendixI_proposition_2_a
      (p := 2) (n := n) (U := D ⧸ W.subgroupOf D) (E := Q0) T hQ0card
  let F0 := AppendixIFpT (p := 2) (E := Q0) T
  letI : Field F0 := fieldInst
  obtain ⟨_moduleInst, hfieldCard, _hfinrank, _hscalar⟩ := hfield
  have hF0isField : IsField F0 := by
    simpa [F0] using
      (Finite.isField_of_domain (AppendixIFpT (p := 2) (E := Q0) T))
  let canonicalField : Field F0 := hF0isField.toField
  letI : Field F0 := canonicalField
  let sAdd : Additive Q0 := Additive.ofMul sQ0
  have hsAdd_ne : sAdd ≠ 0 := by
    simpa [sAdd] using hsQ0_ne
  let toQ0 : F0 →+ Additive Q0 :=
    { toFun := fun a => a.1 sAdd
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have htoQ0_injective : Function.Injective toQ0 := by
    intro a b hab
    apply sub_eq_zero.mp
    by_contra hne
    have hzeroEval : (a - b).1 sAdd = 0 := by
      change a.1 sAdd - b.1 sAdd = 0
      change toQ0 a - toQ0 b = 0
      rw [hab, sub_self]
    obtain ⟨cInv, hinv⟩ := hF0isField.mul_inv_cancel hne
    have hinv' : cInv * (a - b) = (1 : F0) := by
      rw [hF0isField.mul_comm]
      exact hinv
    have hsZero : sAdd = 0 := by
      calc
        sAdd = (1 : F0).1 sAdd := rfl
        _ = ((cInv * (a - b)) : F0).1 sAdd := by rw [hinv']
        _ = cInv.1 ((a - b).1 sAdd) := rfl
        _ = 0 := by
          rw [hzeroEval]
          exact cInv.1.map_zero
    exact hsAdd_ne hsZero
  letI : Fintype F0 := Fintype.ofFinite F0
  letI : Fintype (Additive Q0) := Fintype.ofFinite (Additive Q0)
  have hcardEq : Fintype.card F0 = Fintype.card (Additive Q0) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    change Nat.card (AppendixIFpT (p := 2) (E := Q0) T) = Nat.card Q0
    exact hfieldCard.trans hQ0card.symm
  have htoQ0_bijective : Function.Bijective toQ0 :=
    (Fintype.bijective_iff_injective_and_card toQ0).2
      ⟨htoQ0_injective, hcardEq⟩
  let coord : F0 ≃+ Additive Q0 :=
    AddEquiv.ofBijective toQ0 htoQ0_bijective
  let q0_add0 : Q0 ≃* Multiplicative F0 :=
    { toFun := fun q =>
        Multiplicative.ofAdd (coord.symm (Additive.ofMul q))
      invFun := fun a =>
        Additive.toMul (coord (Multiplicative.toAdd a))
      left_inv := fun q => by simp
      right_inv := fun a => by simp
      map_mul' := fun q r => by
        change coord.symm (Additive.ofMul (q * r)) =
          coord.symm (Additive.ofMul q) + coord.symm (Additive.ofMul r)
        exact coord.symm.map_add _ _ }
  have hq0_add0_s : q0_add0 sQ0 = Multiplicative.ofAdd 1 := by
    change coord.symm sAdd = 1
    apply coord.injective
    simp [coord, toQ0, sAdd]
  let tauF0 : T →* F0 :=
    { toFun := fun tau =>
        ⟨AppendixITActionEnd (p := 2) (E := Q0) T tau,
          Algebra.subset_adjoin (Set.mem_range_self tau)⟩
      map_one' := by
        ext x
        simp [AppendixITActionEnd_apply]
      map_mul' := by
        intro a b
        ext x
        simp [AppendixITActionEnd_apply, mul_smul] }
  have htauF0_q0 (tau : T) (x : Q0) :
      q0_add0 ((tau : D ⧸ W.subgroupOf D) • x) =
        Multiplicative.ofAdd
          (tauF0 tau * Multiplicative.toAdd (q0_add0 x)) := by
    apply Multiplicative.toAdd.injective
    change coord.symm
          (Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x)) =
        tauF0 tau * coord.symm (Additive.ofMul x)
    apply htoQ0_injective
    calc
      toQ0 (coord.symm
          (Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x))) =
          Additive.ofMul ((tau : D ⧸ W.subgroupOf D) • x) := by
            simp [coord]
      _ = (tauF0 tau).1 (Additive.ofMul x) := by
            simp [tauF0, AppendixITActionEnd_apply]
      _ = (tauF0 tau).1 (toQ0 (coord.symm (Additive.ofMul x))) := by
            rw [show toQ0 (coord.symm (Additive.ofMul x)) =
              Additive.ofMul x by
                simp [coord]]
      _ = toQ0 (tauF0 tau * coord.symm (Additive.ofMul x)) := rfl
  let F : Type := GaloisField 2 n
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F0 = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hfieldCard.trans (GaloisField.card 2 n hn).symm
  let g : F0 ≃+* F := FiniteField.ringEquivOfCardEq hcardF
  let gMul : Multiplicative F0 ≃* Multiplicative F :=
    { toFun := fun a =>
        Multiplicative.ofAdd (g (Multiplicative.toAdd a))
      invFun := fun a =>
        Multiplicative.ofAdd (g.symm (Multiplicative.toAdd a))
      left_inv := fun a => by simp
      right_inv := fun a => by simp
      map_mul' := fun a b => by
        change g (Multiplicative.toAdd a + Multiplicative.toAdd b) =
          g (Multiplicative.toAdd a) + g (Multiplicative.toAdd b)
        exact g.map_add _ _ }
  let q0_add : Q0 ≃* Multiplicative F := q0_add0.trans gMul
  have hq0_add_s : q0_add sQ0 = Multiplicative.ofAdd 1 := by
    simp [q0_add, gMul, hq0_add0_s, map_one g]
  let tauF : T →* F := g.toMonoidHom.comp tauF0
  have htauF_q0 (tau : T) (x : Q0) :
      q0_add ((tau : D ⧸ W.subgroupOf D) • x) =
        Multiplicative.ofAdd
          (tauF tau * Multiplicative.toAdd (q0_add x)) := by
    apply Multiplicative.toAdd.injective
    change g (Multiplicative.toAdd
          (q0_add0 ((tau : D ⧸ W.subgroupOf D) • x))) =
      g (tauF0 tau) * g (Multiplicative.toAdd (q0_add0 x))
    rw [congrArg Multiplicative.toAdd (htauF0_q0 tau x)]
    exact g.map_mul _ _
  let tauUnits : T →* Fˣ :=
    MonoidHom.toHomUnits (G := T) (M := F) tauF
  have htauUnits_bijective : Function.Bijective tauUnits := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply FaithfulSMul.eq_of_smul_eq_smul (α := Q0)
      intro x
      apply q0_add.injective
      rw [htauF_q0, htauF_q0]
      have hval := congrArg Units.val hab
      change tauF a = tauF b at hval
      rw [hval]
    · intro u
      let y : Q0 := q0_add.symm
        (Multiplicative.ofAdd ((u : F) * Multiplicative.toAdd (q0_add sQ0)))
      have hy : y ≠ 1 := by
        intro hyone
        have hcoord := congrArg
          (fun z : Q0 => Multiplicative.toAdd (q0_add z)) hyone
        have hu_zero : (u : F) = 0 := by
          simpa [y, hq0_add_s] using hcoord
        exact Units.ne_zero u hu_zero
      obtain ⟨tau, htau⟩ := htransT sQ0 hsQ0_ne y hy
      refine ⟨tau, ?_⟩
      apply Units.ext
      have hcoord := congrArg
        (fun z : Q0 => Multiplicative.toAdd (q0_add z)) htau
      simpa [tauUnits, htauF_q0, y, hq0_add_s] using hcoord
  let scalarSet : Set F := Set.range tauF
  have hscalarSet_closure : Subring.closure scalarSet = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hx : x = 0
    · subst x
      exact (Subring.closure scalarSet).zero_mem
    · let u : Fˣ := Units.mk0 x hx
      obtain ⟨tau, htau⟩ := htauUnits_bijective.2 u
      apply Subring.subset_closure
      refine ⟨tau, ?_⟩
      have hval := congrArg Units.val htau
      simpa [tauUnits, u] using hval
  have hscalar_eq_action (tau : T) (x : Q0) :
      q0_add.symm
          (Multiplicative.ofAdd
            (tauF tau * Multiplicative.toAdd (q0_add x))) =
        (tau : D ⧸ W.subgroupOf D) • x := by
    apply q0_add.injective
    simpa using (htauF_q0 tau x).symm
  have hconjT : ∀ (u : D ⧸ W.subgroupOf D) (lambda : F),
      lambda ∈ scalarSet → ∃ c : F, ∀ x : Q0,
        rhoD u (q0_add.symm
            (Multiplicative.ofAdd
              (lambda * Multiplicative.toAdd (q0_add x)))) =
          q0_add.symm
            (Multiplicative.ofAdd
              (c * Multiplicative.toAdd (q0_add (rhoD u x)))) := by
    intro u lambda hlambda
    rcases hlambda with ⟨tau, rfl⟩
    let tau' : T :=
      ⟨u * (tau : D ⧸ W.subgroupOf D) * u⁻¹,
        (inferInstance : T.Normal).conj_mem (tau : D ⧸ W.subgroupOf D) tau.property u⟩
    refine ⟨tauF tau', ?_⟩
    intro x
    rw [hscalar_eq_action, hscalar_eq_action]
    change rhoD u (rhoD (tau : D ⧸ W.subgroupOf D) x) =
      rhoD (tau' : D ⧸ W.subgroupOf D) (rhoD u x)
    calc
      rhoD u (rhoD (tau : D ⧸ W.subgroupOf D) x) =
          rhoD (u * (tau : D ⧸ W.subgroupOf D)) x := by
            rw [map_mul]
            rfl
      _ = rhoD ((tau' : D ⧸ W.subgroupOf D) * u) x := by
            congr 2
            simp [tau', mul_assoc]
      _ = rhoD (tau' : D ⧸ W.subgroupOf D) (rhoD u x) := by
            rw [map_mul]
            rfl
  have hsQ0_val_ne : (sQ0 : G) ≠ 1 := by
    simpa [sQ0] using hsI.ne_one
  rcases peterfalvi_appendixI_proposition_2_b
      Q0 q0_add rhoD hrhoD_injective sQ0 hsQ0_val_ne
        scalarSet hscalarSet_closure hconjT with
    ⟨sigmaHom, hsemilinear, hstabilizer⟩
  let C : Subgroup (D ⧸ W.subgroupOf D) :=
    { carrier := {u | rhoD u sQ0 = sQ0}
      one_mem' := by simp
      mul_mem' := by
        intro u v hu hv
        change rhoD (u * v) sQ0 = sQ0
        rw [map_mul]
        change rhoD u (rhoD v sQ0) = sQ0
        rw [hv, hu]
      inv_mem' := by
        intro u hu
        change rhoD u⁻¹ sQ0 = sQ0
        rw [map_inv]
        change (rhoD u)⁻¹ sQ0 = sQ0
        apply (rhoD u).injective
        simpa using hu.symm }
  change ∃ (A : Subgroup (F ≃+* F)) (e : C ≃* A),
    ∀ u : C, (e u : F ≃+* F) = sigmaHom u at hstabilizer
  obtain ⟨A, c_aut, hc_aut⟩ := hstabilizer
  have hWleD : W ≤ D := hsec.W_le_V.trans hVleD
  have hWV : (W.subgroupOf V).Normal :=
    (Subgroup.normal_subgroupOf_iff hsec.W_le_V).2 (by
      intro w v hw hv
      have hconj := hWD.conj_mem
        (⟨w, hWleD hw⟩ : D) hw (⟨v, hVleD hv⟩ : D)
      exact hconj)
  letI : (W.subgroupOf V).Normal := hWV
  let vToD : V →* D := Subgroup.inclusion hVleD
  let vToU : V →* (D ⧸ W.subgroupOf D) :=
    (QuotientGroup.mk' (W.subgroupOf D)).comp vToD
  have hvToU_ker : vToU.ker = W.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker]
    change ((vToD v : D) : D ⧸ W.subgroupOf D) = 1 ↔
      (v : G) ∈ W
    rw [QuotientGroup.eq_one_iff]
    rfl
  have hvToU_range : vToU.range = C := by
    apply le_antisymm
    · intro u hu
      rcases hu with ⟨v, rfl⟩
      change rhoD (vToU v) sQ0 = sQ0
      rw [show vToU v = QuotientGroup.mk (vToD v) by rfl, hrhoD]
      apply Subtype.ext
      simpa [vToD, sQ0] using _hVfix (v⁻¹)
    · intro u hu
      obtain ⟨d, rfl⟩ :=
        QuotientGroup.mk'_surjective (W.subgroupOf D) u
      have hfix : rhoD (QuotientGroup.mk d) sQ0 = sQ0 := hu
      have hright : rightConjugateElem s (d : G)⁻¹ = s := by
        exact congrArg Subtype.val ((hrhoD d sQ0).symm.trans hfix)
      have hcomm : s * (d : G) = (d : G) * s := by
        have hcomm' : (d : G) * s = s * (d : G) := by
          calc
            (d : G) * s =
                ((d : G) * s * (d : G)⁻¹) * (d : G) := by group
            _ = s * (d : G) := by
              simpa [rightConjugateElem] using
                congrArg (fun z : G => z * (d : G)) hright
        exact hcomm'.symm
      have hdCentralizer : (d : G) ∈ Subgroup.centralizer ({s} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hx' : x = s := by simpa using hx
        subst x
        exact hcomm
      have hdV : (d : G) ∈ V := by
        rw [_hVstabilizer]
        exact ⟨d.property, hdCentralizer⟩
      refine ⟨⟨(d : G), hdV⟩, ?_⟩
      rfl
  let vmodW_C : V ⧸ W.subgroupOf V ≃* C :=
    (QuotientGroup.quotientMulEquivOfEq hvToU_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange vToU).trans
        (MulEquiv.subgroupCongr hvToU_range))
  let vmodW_aut : V ⧸ W.subgroupOf V ≃* A := vmodW_C.trans c_aut
  let piD : D →* D ⧸ W.subgroupOf D :=
    QuotientGroup.mk' (W.subgroupOf D)
  have hpiK_injective :
      Function.Injective (piD.subgroupMap (K.subgroupOf D)) := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hpixy : piD (x : D) = piD (y : D) :=
      congrArg Subtype.val hxy
    have hdivW_D : (x : D) / (y : D) ∈ W.subgroupOf D :=
      QuotientGroup.eq_iff_div_mem.mp hpixy
    let z : G := (x : G) / (y : G)
    have hzW : z ∈ W := hdivW_D
    have hzK : z ∈ K := by
      simpa [z, div_eq_mul_inv] using
        K.mul_mem x.property (K.inv_mem y.property)
    have hzV : z ∈ V := hsec.W_le_V hzW
    have hzCent : z ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hsec.V_eq] at hzV
      exact hzV.2
    have hzFix : rightConjugateElem z t = z := by
      have hcomm : t * z = z * t :=
        (Subgroup.mem_centralizer_iff.mp hzCent) t (by simp)
      calc
        rightConjugateElem z t = t⁻¹ * (z * t) := by
          rw [rightConjugateElem, mul_assoc]
        _ = t⁻¹ * (t * z) := by rw [← hcomm]
        _ = z := by simp
    have hzInv : rightConjugateElem z t = z⁻¹ :=
      ((hsec.K_def z).mp hzK).2
    have hzEqInv : z = z⁻¹ := hzFix.symm.trans hzInv
    have hz2 : z ^ 2 = 1 := by
      calc
        z ^ 2 = z * z := pow_two z
        _ = z * z⁻¹ := congrArg (z * ·) hzEqInv
        _ = 1 := mul_inv_cancel z
    have hzD : z ∈ D := ((hsec.K_def z).mp hzK).1
    have hzOne : z = 1 := by
      by_contra hzNe
      exact
        (not_isInvolution_of_mem_odd_subgroup
          D hsec.hA.A1.D_odd hzD) ⟨hzNe, hz2⟩
    change (x : G) = (y : G)
    exact div_eq_one.mp hzOne
  let kD : K ≃* K.subgroupOf D :=
    (Subgroup.subgroupOfEquivOfLe hsec.K_le_D).symm
  let kImage : K.subgroupOf D ≃* (K.subgroupOf D).map piD :=
    MulEquiv.ofBijective (piD.subgroupMap (K.subgroupOf D))
      ⟨hpiK_injective, piD.subgroupMap_surjective (K.subgroupOf D)⟩
  have hTK : T = (K.subgroupOf D).map piD := by
    simpa [T, piD] using
      peterfalvi_chapter1_section2_proposition_3_appendixI_input_KWmodW_eq_KmodW
        D K V W hsec.K_le_D hsec.W_le_V hVleD hWD
  let kT : K ≃* T :=
    kD.trans (kImage.trans (MulEquiv.subgroupCongr hTK.symm))
  let tUnits : T ≃* Fˣ :=
    MulEquiv.ofBijective tauUnits htauUnits_bijective
  let k_units : K ≃* Fˣ := kT.trans tUnits
  have hC_stabilizer :
      C = MulAction.stabilizer (D ⧸ W.subgroupOf D) sQ0 := by
    ext u
    rfl
  have hT_free :
      ∀ tau : T, (tau : D ⧸ W.subgroupOf D) • sQ0 = sQ0 → tau = 1 := by
    intro tau htau
    apply htauUnits_bijective.1
    apply Units.ext
    have hcoord := congrArg
      (fun z : Q0 => Multiplicative.toAdd (q0_add z)) htau
    simpa [tauUnits, htauF_q0, hq0_add_s] using hcoord
  have hT_move_back :
      ∀ u : D ⧸ W.subgroupOf D,
        ∃ tau : T, (tau : D ⧸ W.subgroupOf D) • u • sQ0 = sQ0 := by
    intro u
    have hu_ne : u • sQ0 ≠ 1 := by
      intro hu
      apply hsQ0_ne
      change rhoD u sQ0 = 1 at hu
      have hback := congrArg (rhoD u)⁻¹ hu
      simpa using hback
    exact htransT (u • sQ0) hu_ne sQ0 hsQ0_ne
  have hTC : T.IsComplement' C := by
    rw [hC_stabilizer]
    exact Subgroup.isComplement'_stabilizer sQ0 hT_free hT_move_back
  let rhoTC : C →* MulAut T :=
    (T.normalizerMonoidHom).comp
      (Subgroup.inclusion (T.normalizer_eq_top ▸ le_top))
  let tc_U :
      SemidirectProduct T C rhoTC ≃* (D ⧸ W.subgroupOf D) := by
    simpa [rhoTC] using SemidirectProduct.mulEquivSubgroup hTC
  let rhoMul : Fˣ →* MulAut (Multiplicative F) :=
    (MulAutMultiplicative F).symm.toMonoidHom.comp
      (DistribMulAction.toAddAut Fˣ F)
  let sigmaAdd (sigma : F ≃+* F) : MulAut (Multiplicative F) :=
    AddEquiv.toMultiplicative sigma.toAddEquiv
  let sigmaUnits (sigma : F ≃+* F) : MulAut Fˣ :=
    Units.mapEquiv sigma.toMulEquiv
  have hsigma_compat (sigma : F ≃+* F) : ∀ u : Fˣ,
      (rhoMul u).trans (sigmaAdd sigma) =
        (sigmaAdd sigma).trans (rhoMul (sigmaUnits sigma u)) := by
    intro u
    apply MulEquiv.ext
    intro a
    change Multiplicative.ofAdd
        (sigma ((u : F) * Multiplicative.toAdd a)) =
      Multiplicative.ofAdd
        (sigma (u : F) * sigma (Multiplicative.toAdd a))
    rw [map_mul]
  let affineAut (sigma : F ≃+* F) :
      MulAut (SemidirectProduct (Multiplicative F) Fˣ rhoMul) :=
    SemidirectProduct.congr
      (sigmaAdd sigma) (sigmaUnits sigma) (hsigma_compat sigma)
  let rhoAut :
      A →* MulAut (SemidirectProduct (Multiplicative F) Fˣ rhoMul) :=
    { toFun := fun sigma => affineAut (sigma : F ≃+* F)
      map_one' := by
        apply MulEquiv.ext
        rintro ⟨a, u⟩
        rfl
      map_mul' := by
        intro sigma tau
        apply MulEquiv.ext
        rintro ⟨a, u⟩
        rfl }
  have hrhoMul :
      ∀ u : Fˣ, ∀ a : Multiplicative F,
        rhoMul u a =
          Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F)) := by
    intro u a
    change Multiplicative.ofAdd ((u : F) * Multiplicative.toAdd a) =
      Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F))
    rw [mul_comm]
  have hrhoAut_inl :
      ∀ sigma : A, ∀ a : Multiplicative F,
        rhoAut sigma (SemidirectProduct.inl a) =
          SemidirectProduct.inl
            (Multiplicative.ofAdd
              ((sigma : F ≃+* F) (Multiplicative.toAdd a))) := by
    intro sigma a
    apply SemidirectProduct.ext <;>
      simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
  have hrhoAut_inr :
      ∀ sigma : A, ∀ u : Fˣ,
        rhoAut sigma (SemidirectProduct.inr u) =
          SemidirectProduct.inr
            (Units.map (sigma : F ≃+* F).toMonoidWithZeroHom u) := by
    intro sigma u
    apply SemidirectProduct.ext
    · simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
    · simp [rhoAut, affineAut, sigmaAdd, sigmaUnits,
        SemidirectProduct.congr]
      apply Units.ext
      rfl
  have hrhoAut_right (sigma : A)
      (x : SemidirectProduct (Multiplicative F) Fˣ rhoMul) :
      (rhoAut sigma x).right =
        sigmaUnits (sigma : F ≃+* F) x.right := by
    rfl
  have hT_action (tau : T) (q : Q0) :
      q0_add (rhoD (tau : D ⧸ W.subgroupOf D) q) =
        rhoMul (tUnits tau) (q0_add q) := by
    rw [hrhoMul]
    change q0_add ((tau : D ⧸ W.subgroupOf D) • q) =
      Multiplicative.ofAdd
        (Multiplicative.toAdd (q0_add q) * tauF tau)
    rw [htauF_q0]
    congr 1
    exact mul_comm _ _
  have hC_action (c : C) (q : Q0) :
      q0_add (rhoD (c : D ⧸ W.subgroupOf D) q) =
        sigmaAdd (c_aut c) (q0_add q) := by
    let lambda : F := Multiplicative.toAdd (q0_add q)
    have hsemi := hsemilinear
      (c : D ⧸ W.subgroupOf D) lambda sQ0
    have hcfix : rhoD (c : D ⧸ W.subgroupOf D) sQ0 = sQ0 :=
      c.property
    have hcoord := congrArg
      (fun z : Q0 => Multiplicative.toAdd (q0_add z)) hsemi
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd
        (q0_add (rhoD (c : D ⧸ W.subgroupOf D) q)) =
      (c_aut c : F ≃+* F) lambda
    simpa [lambda, hq0_add_s, hcfix, hc_aut c] using hcoord
  have htauF_from_s (tau : T) :
      tauF tau =
        Multiplicative.toAdd
          (q0_add ((tau : D ⧸ W.subgroupOf D) • sQ0)) := by
    have hcoord := congrArg Multiplicative.toAdd
      (htauF_q0 tau sQ0)
    simpa [hq0_add_s] using hcoord.symm
  have hrhoTC_coe (c : C) (tau : T) :
      ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) =
        (c : D ⧸ W.subgroupOf D) *
          (tau : D ⧸ W.subgroupOf D) *
            (c : D ⧸ W.subgroupOf D)⁻¹ := by
    rfl
  have hC_on_T (c : C) (tau : T) :
      tUnits (rhoTC c tau) = sigmaUnits (c_aut c) (tUnits tau) := by
    apply Units.ext
    change tauF (rhoTC c tau) =
      (c_aut c : F ≃+* F) (tauF tau)
    rw [htauF_from_s, htauF_from_s]
    have hcfix : rhoD (c : D ⧸ W.subgroupOf D) sQ0 = sQ0 :=
      c.property
    have hcinvfix :
        rhoD (c : D ⧸ W.subgroupOf D)⁻¹ sQ0 = sQ0 := by
      rw [map_inv]
      change (rhoD (c : D ⧸ W.subgroupOf D))⁻¹ sQ0 = sQ0
      apply (rhoD (c : D ⧸ W.subgroupOf D)).injective
      simpa using hcfix.symm
    have hact :
        ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) • sQ0 =
          (c : D ⧸ W.subgroupOf D) •
            ((tau : D ⧸ W.subgroupOf D) • sQ0) := by
      change rhoD ((rhoTC c tau : T) : D ⧸ W.subgroupOf D) sQ0 =
        rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D) sQ0)
      rw [hrhoTC_coe, map_mul, map_mul]
      change rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D)
            (rhoD (c : D ⧸ W.subgroupOf D)⁻¹ sQ0)) =
        rhoD (c : D ⧸ W.subgroupOf D)
          (rhoD (tau : D ⧸ W.subgroupOf D) sQ0)
      rw [hcinvfix]
    rw [hact]
    exact congrArg Multiplicative.toAdd
      (hC_action c ((tau : D ⧸ W.subgroupOf D) • sQ0)
        |>.trans rfl)
  have htc_U_apply (z : SemidirectProduct T C rhoTC) :
      tc_U z =
        (z.1 : D ⧸ W.subgroupOf D) *
          (z.2 : D ⧸ W.subgroupOf D) := by
    rfl
  let modelHom :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD →*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    { toFun := fun x =>
        let z := tc_U.symm x.2
        ⟨⟨q0_add x.1, tUnits z.1⟩, c_aut z.2⟩
      map_one' := by
        simp
      map_mul' := by
        rintro ⟨q, u⟩ ⟨q', u'⟩
        obtain ⟨z, rfl⟩ := tc_U.surjective u
        obtain ⟨z', rfl⟩ := tc_U.surjective u'
        rcases z with ⟨tau, c⟩
        rcases z' with ⟨tau', c'⟩
        dsimp
        rw [← map_mul tc_U, tc_U.symm_apply_apply]
        apply SemidirectProduct.ext
        · apply SemidirectProduct.ext
          · simp only [SemidirectProduct.mul_left, tc_U.symm_apply_apply, map_mul]
            rw [htc_U_apply, map_mul]
            change q0_add q *
                q0_add (rhoD (tau : D ⧸ W.subgroupOf D)
                  (rhoD (c : D ⧸ W.subgroupOf D) q')) =
              q0_add q *
                rhoMul (tUnits tau)
                  (sigmaAdd (c_aut c) (q0_add q'))
            rw [hT_action, hC_action]
          · rw [tc_U.symm_apply_apply, tc_U.symm_apply_apply]
            simp only [SemidirectProduct.mul_left,
              SemidirectProduct.mul_right]
            calc
              tUnits (tau * rhoTC c tau') =
                  tUnits tau * tUnits (rhoTC c tau') :=
                tUnits.map_mul tau (rhoTC c tau')
              _ = tUnits tau *
                    sigmaUnits (c_aut c) (tUnits tau') :=
                congrArg (tUnits tau * ·) (hC_on_T c tau')
              _ = tUnits tau *
                    (rhoAut (c_aut c)
                      ⟨q0_add q', tUnits tau'⟩).right :=
                congrArg (tUnits tau * ·)
                  (hrhoAut_right (c_aut c)
                    ⟨q0_add q', tUnits tau'⟩).symm
        · simpa only [SemidirectProduct.mul_right,
            tc_U.symm_apply_apply] using c_aut.map_mul c c' }
  let modelEquiv :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    { toFun := fun x =>
        let z := tc_U.symm x.2
        ⟨⟨q0_add x.1, tUnits z.1⟩, c_aut z.2⟩
      invFun := fun y =>
        ⟨q0_add.symm y.1.1,
          tc_U ⟨tUnits.symm y.1.2, c_aut.symm y.2⟩⟩
      left_inv := by
        rintro ⟨q, u⟩
        obtain ⟨z, rfl⟩ := tc_U.surjective u
        rcases z with ⟨tau, c⟩
        apply SemidirectProduct.ext
        · simp
        · simp
      right_inv := by
        rintro ⟨⟨a, u⟩, sigma⟩
        apply SemidirectProduct.ext
        · apply SemidirectProduct.ext
          · simp
          · simp
        · simp }
  let modelIso :
      SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
        SemidirectProduct
          (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut :=
    MulEquiv.ofBijective modelHom modelEquiv.bijective
  have hkT_coe (k : K) :
      (kT k : D ⧸ W.subgroupOf D) =
        QuotientGroup.mk
          (⟨(k : G), hsec.K_le_D k.property⟩ : D) := by
    rfl
  have hvmodW_C_coe (v : V) :
      ((vmodW_C (QuotientGroup.mk v) : C) :
          D ⧸ W.subgroupOf D) =
        QuotientGroup.mk
          (⟨(v : G), hVleD v.property⟩ : D) := by
    rfl
  have htc_K_decomp (k : K) :
      tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D)) =
        SemidirectProduct.inl (kT k) := by
    apply tc_U.injective
    rw [tc_U.apply_symm_apply, htc_U_apply]
    simpa using (hkT_coe k).symm
  have htc_V_decomp (v : V) :
      tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D)) =
        SemidirectProduct.inr
          (vmodW_C (QuotientGroup.mk v)) := by
    apply tc_U.injective
    rw [tc_U.apply_symm_apply, htc_U_apply]
    simpa using (hvmodW_C_coe v).symm
  have hmodel_q :
      ∀ q : Q0,
        modelIso (SemidirectProduct.inl q) =
          SemidirectProduct.inl
            (SemidirectProduct.inl (q0_add q)) := by
    intro q
    change (⟨⟨q0_add q, tUnits (tc_U.symm 1).1⟩,
        c_aut (tc_U.symm 1).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inl
          (SemidirectProduct.inl (q0_add q))
    simp
  have hmodel_k :
      ∀ k : K,
        modelIso
            (SemidirectProduct.inr
              (QuotientGroup.mk
                (⟨(k : G), hsec.K_le_D k.property⟩ : D))) =
          SemidirectProduct.inl
            (SemidirectProduct.inr (k_units k)) := by
    intro k
    change (⟨⟨q0_add 1,
        tUnits (tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D))).1⟩,
        c_aut (tc_U.symm
          (QuotientGroup.mk
            (⟨(k : G), hsec.K_le_D k.property⟩ : D))).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inl
          (SemidirectProduct.inr (k_units k))
    rw [htc_K_decomp]
    simp [k_units]
  have hmodel_v :
      ∀ v : V,
        modelIso
            (SemidirectProduct.inr
              (QuotientGroup.mk
                (⟨(v : G), hVleD v.property⟩ : D))) =
          SemidirectProduct.inr
            (vmodW_aut (QuotientGroup.mk v)) := by
    intro v
    change (⟨⟨q0_add 1,
        tUnits (tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D))).1⟩,
        c_aut (tc_U.symm
          (QuotientGroup.mk
            (⟨(v : G), hVleD v.property⟩ : D))).2⟩ :
      SemidirectProduct
        (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut) =
        SemidirectProduct.inr
          (vmodW_aut (QuotientGroup.mk v))
    rw [htc_V_decomp]
    simp [vmodW_aut]
  have hmodel_card : Nat.card Q0 = Nat.card F :=
    hQ0card.trans (GaloisField.card 2 n hn).symm
  have hrhoD_exists :
      ∀ d : D, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0,
          rhoD (QuotientGroup.mk d) q =
            ⟨rightConjugateElem (q : G) (d : G)⁻¹, hq⟩ := by
    intro d q
    let hq :=
      proposition_3_Q0_rightConjugate_mem_of_D
        H D Q K V W Q0 S Q1 t hsec d q
    exact ⟨hq, hrhoD d q⟩
  have hk_action :
      ∀ k : K, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (k : G) ∈ Q0,
          q0_add ⟨rightConjugateElem (q : G) (k : G), hq⟩ =
            Multiplicative.ofAdd
              (Multiplicative.toAdd (q0_add q) *
                (↑((k_units k)⁻¹) : F)) := by
    intro k q
    let kInv : K := k⁻¹
    let d : D := ⟨(kInv : G), hsec.K_le_D kInv.property⟩
    let hq :=
      proposition_3_Q0_rightConjugate_mem_of_D
        H D Q K V W Q0 S Q1 t hsec d q
    have hq' : rightConjugateElem (q : G) (k : G) ∈ Q0 := by
      simpa [d, kInv] using hq
    refine ⟨hq', ?_⟩
    have hcoe : (kT kInv : D ⧸ W.subgroupOf D) = QuotientGroup.mk d := by
      simpa [d] using hkT_coe kInv
    have haction := hT_action (kT kInv) q
    have hrho_eq :
        rhoD (kT kInv : D ⧸ W.subgroupOf D) q =
          ⟨rightConjugateElem (q : G) (k : G), hq'⟩ := by
      apply Subtype.ext
      rw [hcoe]
      simpa [d, kInv] using congrArg Subtype.val (hrhoD d q)
    rw [← hrho_eq, haction, hrhoMul]
    simp [kInv, k_units]
  have hv_action :
      ∀ v : V, ∀ q : Q0,
        ∃ hq : rightConjugateElem (q : G) (v : G) ∈ Q0,
          q0_add ⟨rightConjugateElem (q : G) (v : G), hq⟩ =
            Multiplicative.ofAdd
              ((vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm
                (Multiplicative.toAdd (q0_add q))) := by
    intro v q
    let vInv : V := v⁻¹
    let d : D := ⟨(vInv : G), hVleD vInv.property⟩
    let c : C := vmodW_C (QuotientGroup.mk vInv)
    let hq :=
      proposition_3_Q0_rightConjugate_mem_of_D
        H D Q K V W Q0 S Q1 t hsec d q
    have hq' : rightConjugateElem (q : G) (v : G) ∈ Q0 := by
      simpa [d, vInv] using hq
    refine ⟨hq', ?_⟩
    have hcoe : (c : D ⧸ W.subgroupOf D) = QuotientGroup.mk d := by
      simpa [c, d] using hvmodW_C_coe vInv
    have haction := hC_action c q
    have hrho_eq :
        rhoD (c : D ⧸ W.subgroupOf D) q =
          ⟨rightConjugateElem (q : G) (v : G), hq'⟩ := by
      apply Subtype.ext
      rw [hcoe]
      simpa [d, vInv] using congrArg Subtype.val (hrhoD d q)
    have hmkInv :
        (QuotientGroup.mk vInv : V ⧸ W.subgroupOf V) =
          (QuotientGroup.mk v : V ⧸ W.subgroupOf V)⁻¹ := by
      simp [vInv]
    have hcAut :
        (c_aut c : F ≃+* F) =
          (vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm := by
      calc
        (c_aut c : F ≃+* F) =
            (vmodW_aut (QuotientGroup.mk vInv) : F ≃+* F) := rfl
        _ = (vmodW_aut ((QuotientGroup.mk v)⁻¹) : F ≃+* F) := by rw [hmkInv]
        _ = (vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm := by
          exact congrArg Subtype.val (map_inv vmodW_aut (QuotientGroup.mk v))
    rw [← hrho_eq, haction]
    change Multiplicative.ofAdd
        ((c_aut c : F ≃+* F) (Multiplicative.toAdd (q0_add q))) = _
    rw [hcAut]
  refine ⟨n, hn, hQ0card, A, hWV, hWD,
    rhoD, rhoMul, rhoAut, q0_add, k_units, vmodW_aut, modelIso, ?_⟩
  exact ⟨hmodel_card, hrhoMul, hrhoAut_inl, hrhoAut_inr,
    hrhoD_exists, hmodel_q, hmodel_k, hmodel_v, hk_action, hv_action⟩

/-- The Galois-theoretic consequence of Proposition 3 used in Chapter IV,
Section 4: an element of `V` that centralizes the `P`-fixed part of `Q0`
lies in `P W`. -/
public theorem proposition_3_V_inf_centralizer_fixed_Q0_le_sup
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
    (P : Subgroup G) (hPV : P ≤ V) :
    V ⊓ Subgroup.centralizer
        ((Q0 ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) ≤
      P ⊔ W := by
  classical
  intro v hv
  rcases proposition_3_field_model_with_q0_card
      H D Q K V W Q0 S Q1 t hsec with
    ⟨fieldN, _hfieldN, _hQ0pow, A, hWnormalV, _hWnormalD,
      _rhoD, _rhoMul, _rhoAut, q0Add, _kUnits, vmodWAut, _modelIso,
      _hQ0card, _hrhoMul, _hrhoAutInl, _hrhoAutInr, _hrhoD,
      _hmodelQ, _hmodelK, _hmodelV, _hkAction, hvAction⟩
  let F : Type := GaloisField 2 fieldN
  letI : Field F := inferInstance
  letI : Finite F := inferInstance
  letI : (W.subgroupOf V).Normal := hWnormalV
  let pToV : P →* V := Subgroup.inclusion hPV
  let rhoP : P →* (F ≃+* F) :=
    A.subtype.comp
      (vmodWAut.toMonoidHom.comp
        ((QuotientGroup.mk' (W.subgroupOf V)).comp pToV))
  letI : MulSemiringAction P F := MulSemiringAction.compHom F rhoP
  let vV : V := ⟨v, hv.1⟩
  have hvFixes :
      ∀ x : FixedPoints.subfield P F,
        (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) (x : F) = x := by
    intro x
    let q : Q0 := q0Add.symm (Multiplicative.ofAdd (x : F))
    have hqCentralizerP : (q : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hpP
      let pP : P := ⟨p, hpP⟩
      let pV : V := pToV pP
      rcases hvAction pV q with ⟨hqConj, hqImage⟩
      have hxFixed : rhoP pP (x : F) = x := x.property pP
      have hforward :
          (vmodWAut (QuotientGroup.mk pV) : F ≃+* F) (x : F) = x := by
        simpa [rhoP, pToV, pP, pV] using hxFixed
      have hbackward :
          (vmodWAut (QuotientGroup.mk pV) : F ≃+* F).symm (x : F) = x := by
        apply (vmodWAut (QuotientGroup.mk pV) : F ≃+* F).injective
        simpa using hforward.symm
      have hqImage' :
          q0Add ⟨rightConjugateElem (q : G) p, hqConj⟩ = q0Add q := by
        simpa [q, hbackward, pV, pToV, pP] using hqImage
      have hright : rightConjugateElem (q : G) p = (q : G) :=
        congrArg Subtype.val (q0Add.injective hqImage')
      calc
        p * (q : G) = p * rightConjugateElem (q : G) p := by rw [hright]
        _ = (q : G) * p := by simp [rightConjugateElem, mul_assoc]
    have hqInf :
        (q : G) ∈ Q0 ⊓ Subgroup.centralizer (P : Set G) :=
      ⟨q.property, hqCentralizerP⟩
    have hvComm : v * (q : G) = (q : G) * v :=
      (Subgroup.mem_centralizer_iff.mp hv.2 (q : G) hqInf).symm
    rcases hvAction vV q with ⟨hqConj, hqImage⟩
    have hright : rightConjugateElem (q : G) v = (q : G) := by
      calc
        rightConjugateElem (q : G) v = v⁻¹ * ((q : G) * v) := by
          simp [rightConjugateElem, mul_assoc]
        _ = v⁻¹ * (v * (q : G)) := by rw [hvComm]
        _ = (q : G) := by simp
    have hbackward :
        (vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm (x : F) = x := by
      apply Multiplicative.ofAdd.injective
      calc
        Multiplicative.ofAdd
            ((vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm (x : F)) =
            q0Add ⟨rightConjugateElem (q : G) v, hqConj⟩ := by
          simpa [q] using hqImage.symm
        _ = q0Add q := by simp [hright]
        _ = Multiplicative.ofAdd (x : F) := by simp [q]
    apply (vmodWAut (QuotientGroup.mk vV) : F ≃+* F).symm.injective
    simpa using hbackward.symm
  have h_algebraMap_eq_val' :
      (algebraMap (FixedPoints.subfield P F) F : FixedPoints.subfield P F → F) = Subtype.val := by
    ext x; rfl
  let sigma : F ≃ₐ[FixedPoints.subfield P F] F :=
    AlgEquiv.ofRingEquiv
      (f := (vmodWAut (QuotientGroup.mk vV) : F ≃+* F))
      (by
        intro r
        have htemp : algebraMap (FixedPoints.subfield P F) F r = (r : F) := rfl
        simpa [htemp] using hvFixes r)
  obtain ⟨p, hpSigma⟩ := FixedPoints.toAlgAut_surjective P F sigma
  have hAutEq :
      (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) = rhoP p := by
    have htemp : (sigma : F ≃+* F) = (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) := by
      dsimp [sigma]
      rfl
    have htemp' : (sigma : F ≃+* F) = (rhoP p : F ≃+* F) := by
      calc
        (sigma : F ≃+* F) = ((MulSemiringAction.toAlgAut (↥P) (↥(FixedPoints.subfield (↥P) F)) F) p : F ≃+* F) := by
          simpa using congrArg (fun e : F ≃ₐ[FixedPoints.subfield P F] F => (e : F ≃+* F)) hpSigma.symm
        _ = (rhoP p : F ≃+* F) := by
          ext x
          calc
            ((MulSemiringAction.toAlgAut (↥P) (↥(FixedPoints.subfield (↥P) F)) F) p : F → F) x =
              p • x := rfl
            _ = rhoP p x := rfl
    calc
      (vmodWAut (QuotientGroup.mk vV) : F ≃+* F) = (sigma : F ≃+* F) := htemp.symm
      _ = (rhoP p : F ≃+* F) := htemp'
  have hQuotientEq :
      QuotientGroup.mk' (W.subgroupOf V) vV =
        QuotientGroup.mk' (W.subgroupOf V) (pToV p) := by
    apply vmodWAut.injective
    apply Subtype.ext
    exact hAutEq
  have hdivW : vV / pToV p ∈ W.subgroupOf V :=
    (QuotientGroup.eq_iff_div_mem (N := W.subgroupOf V)).mp hQuotientEq
  have hdivW_G : ((vV / pToV p : V) : G) ∈ W := hdivW
  have hv_factor : v = ((vV / pToV p : V) : G) * (p : G) := by
    simp [vV, pToV, div_eq_mul_inv, mul_assoc]
  rw [hv_factor]
  exact (P ⊔ W).mul_mem
    ((show W ≤ P ⊔ W from le_sup_right) hdivW_G)
    ((show P ≤ P ⊔ W from le_sup_left) p.property)

public theorem proposition_3
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
    (∃ (n : ℕ) (_ : n ≠ 0),
      Nat.card Q0 = 2 ^ n ∧
      let F : Type := GaloisField 2 n
      letI : Field F := inferInstance
      letI : Finite F := inferInstance
      ∃ (A : Subgroup (F ≃+* F))
          (hWV : (W.subgroupOf V).Normal)
          (hWD : (W.subgroupOf D).Normal),
        letI : (W.subgroupOf V).Normal := hWV
        letI : (W.subgroupOf D).Normal := hWD
        ∃ (rhoD : (D ⧸ W.subgroupOf D) →* MulAut Q0)
            (rhoMul : Fˣ →* MulAut (Multiplicative F))
            (rhoAut : A →* MulAut
              (SemidirectProduct (Multiplicative F) Fˣ rhoMul))
            (q0_add : Q0 ≃* Multiplicative F)
            (k_units : K ≃* Fˣ)
            (vmodW_aut : V ⧸ W.subgroupOf V ≃* A)
            (modelIso :
              SemidirectProduct Q0 (D ⧸ W.subgroupOf D) rhoD ≃*
                SemidirectProduct
                  (SemidirectProduct (Multiplicative F) Fˣ rhoMul) A rhoAut),
          Nat.card Q0 = Nat.card F ∧
            (∀ u : Fˣ, ∀ a : Multiplicative F,
              rhoMul u a =
                Multiplicative.ofAdd (Multiplicative.toAdd a * (u : F))) ∧
            (∀ σ : A, ∀ a : Multiplicative F,
              rhoAut σ (SemidirectProduct.inl a) =
                SemidirectProduct.inl
                  (Multiplicative.ofAdd
                    ((σ : F ≃+* F) (Multiplicative.toAdd a)))) ∧
            (∀ σ : A, ∀ u : Fˣ,
              rhoAut σ (SemidirectProduct.inr u) =
                SemidirectProduct.inr
                  (Units.map (σ : F ≃+* F).toMonoidWithZeroHom u)) ∧
            (∀ d : D, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (d : G)⁻¹ ∈ Q0,
                rhoD (QuotientGroup.mk d) q =
                  ⟨rightConjugateElem (q : G) (d : G)⁻¹, hq⟩) ∧
            (∀ q : Q0,
              modelIso (SemidirectProduct.inl q) =
                SemidirectProduct.inl
                  (SemidirectProduct.inl (q0_add q))) ∧
            (∀ k : K,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      ⟨(k : G), hsec.K_le_D k.property⟩)) =
                SemidirectProduct.inl
                  (SemidirectProduct.inr (k_units k))) ∧
            (∀ v : V,
              modelIso
                  (SemidirectProduct.inr
                    (QuotientGroup.mk
                      ⟨(v : G),
                        (proposition_3_V_le_D H D Q K V W Q0 S Q1 t hsec)
                          v.property⟩)) =
                SemidirectProduct.inr
                  (vmodW_aut (QuotientGroup.mk v))) ∧
            (∀ k : K, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (k : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (k : G), hq⟩ =
                  Multiplicative.ofAdd
                    (Multiplicative.toAdd (q0_add q) *
                      (↑((k_units k)⁻¹) : F))) ∧
            (∀ v : V, ∀ q : Q0,
              ∃ hq : rightConjugateElem (q : G) (v : G) ∈ Q0,
                q0_add ⟨rightConjugateElem (q : G) (v : G), hq⟩ =
                  Multiplicative.ofAdd
                    ((vmodW_aut (QuotientGroup.mk v) : F ≃+* F).symm
                      (Multiplicative.toAdd (q0_add q))))) ∧
      ∃ hWV : (W.subgroupOf V).Normal,
        letI : (W.subgroupOf V).Normal := hWV
        IsCyclic (V ⧸ W.subgroupOf V) := by
  classical
  have hmodel :=
    proposition_3_field_model_with_q0_card
      H D Q K V W Q0 S Q1 t hsec
  refine ⟨hmodel, ?_⟩
  rcases hmodel with
    ⟨n, hn, hQ0card, A, hWV, hWD, rhoD, rhoMul, rhoAut,
      q0_add, k_units, vmodW_aut, modelIso, hdata⟩
  refine ⟨hWV, ?_⟩
  letI : (W.subgroupOf V).Normal := hWV
  let F : Type := GaloisField 2 n
  letI : Algebra (ZMod 2) F := ZMod.algebra F 2
  let toAlg : (F ≃+* F) →* (F ≃ₐ[ZMod 2] F) :=
    { toFun := fun e =>
        AlgEquiv.ofRingEquiv (f := e) (by
          intro x
          have h :
              (e.toRingHom.comp (algebraMap (ZMod 2) F) :
                ZMod 2 →+* F) = algebraMap (ZMod 2) F :=
            RingHom.ext_zmod _ _
          exact DFunLike.congr_fun h x)
      map_one' := by
        ext x
        rfl
      map_mul' := by
        intro e f
        ext x
        rfl }
  letI : IsCyclic (F ≃+* F) :=
    isCyclic_of_injective toAlg (by
      intro e f h
      ext x
      exact DFunLike.congr_fun h x)
  letI : IsCyclic A := inferInstance
  exact (vmodW_aut.isCyclic).2 inferInstance
end PFchapter1section2
end CFSG.BenderSuzuki
