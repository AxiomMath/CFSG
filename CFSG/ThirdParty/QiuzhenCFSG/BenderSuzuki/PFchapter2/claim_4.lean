module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_2
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (4)
-/

private theorem claim_4_P_le_H
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
    P ≤ H := by
  intro x hxP
  have hxV : x ∈ V := hch.B1.P_le_V hxP
  have hxVD : x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
    simpa [hch.section3.section2.V_eq, peterfalviV] using hxV
  exact hch.section3.section2.hA.A1.D_le_H hxVD.1

private theorem claim_4_P_le_normalizer_Q
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
    P ≤ Subgroup.normalizer (Q : Set G) := by
  have hP_le_H : P ≤ H := claim_4_P_le_H H D Q K V W Q0 S Q1 P t s p hch
  have hforward :
      ∀ x : G, x ∈ P → ∀ q : G, q ∈ Q → x * q * x⁻¹ ∈ Q := by
    intro x hxP q hqQ
    let xH : H := ⟨x, hP_le_H hxP⟩
    let qH : H := ⟨q, hch.section3.section2.hA.A1.Q_le_H hqQ⟩
    have hqSub : qH ∈ Q.subgroupOf H := by
      simpa [Subgroup.mem_subgroupOf] using hqQ
    have hconj :=
      hch.section3.section2.hA.A1.Q_normal_in_H.conj_mem qH hqSub xH
    simpa [xH, qH, Subgroup.mem_subgroupOf] using hconj
  intro x hxP
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hqQ
    exact hforward x hxP q hqQ
  · intro hqQ
    have hback := hforward x⁻¹ (P.inv_mem hxP) (x * q * x⁻¹) hqQ
    simpa [mul_assoc] using hback

private theorem claim_4_K_le_H
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
    K ≤ H :=
  hch.section3.section2.K_le_D.trans hch.section3.section2.hA.A1.D_le_H

private theorem claim_4_K_le_normalizer_Q
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
    K ≤ Subgroup.normalizer (Q : Set G) := by
  have hK_le_H : K ≤ H := claim_4_K_le_H H D Q K V W Q0 S Q1 P t s p hch
  have hforward :
      ∀ x : G, x ∈ K → ∀ q : G, q ∈ Q → x * q * x⁻¹ ∈ Q := by
    intro x hxK q hqQ
    let xH : H := ⟨x, hK_le_H hxK⟩
    let qH : H := ⟨q, hch.section3.section2.hA.A1.Q_le_H hqQ⟩
    have hqSub : qH ∈ Q.subgroupOf H := by
      simpa [Subgroup.mem_subgroupOf] using hqQ
    have hconj :=
      hch.section3.section2.hA.A1.Q_normal_in_H.conj_mem qH hqSub xH
    simpa [xH, qH, Subgroup.mem_subgroupOf] using hconj
  intro x hxK
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hqQ
    exact hforward x hxK q hqQ
  · intro hqQ
    have hback := hforward x⁻¹ (K.inv_mem hxK) (x * q * x⁻¹) hqQ
    simpa [mul_assoc] using hback

private theorem claim_4_K_sup_P_le_normalizer_Q
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
    K ⊔ P ≤ Subgroup.normalizer (Q : Set G) :=
  sup_le
    (claim_4_K_le_normalizer_Q H D Q K V W Q0 S Q1 P t s p hch)
    (claim_4_P_le_normalizer_Q H D Q K V W Q0 S Q1 P t s p hch)

private theorem claim_4_KP_action_conj
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
    let toNormalizer : ↥(K ⊔ P) →* Subgroup.normalizer (Q : Set G) :=
      { toFun := fun x =>
          ⟨(x : G), claim_4_K_sup_P_le_normalizer_Q
            H D Q K V W Q0 S Q1 P t s p hch x.2⟩
        map_one' := by
          ext
          rfl
        map_mul' := by
          intro x y
          ext
          rfl }
    letI : MulAction ↥(K ⊔ P) Q := MulAction.compHom Q toNormalizer
    ∀ a : ↥(K ⊔ P), ∀ q : Q,
      ((a • q : Q) : G) = (a : G) * (q : G) * (a : G)⁻¹ := by
  let toNormalizer : ↥(K ⊔ P) →* Subgroup.normalizer (Q : Set G) :=
    { toFun := fun x =>
        ⟨(x : G), claim_4_K_sup_P_le_normalizer_Q
          H D Q K V W Q0 S Q1 P t s p hch x.2⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  let : MulAction ↥(K ⊔ P) Q := MulAction.compHom Q toNormalizer
  change ∀ a : ↥(K ⊔ P), ∀ q : Q,
    ((a • q : Q) : G) = (a : G) * (q : G) * (a : G)⁻¹
  intro a q
  rfl

private theorem claim_4_KP_action_by_automorphisms
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
    let toNormalizer : ↥(K ⊔ P) →* Subgroup.normalizer (Q : Set G) :=
      { toFun := fun x =>
          ⟨(x : G), claim_4_K_sup_P_le_normalizer_Q
            H D Q K V W Q0 S Q1 P t s p hch x.2⟩
        map_one' := by
          ext
          rfl
        map_mul' := by
          intro x y
          ext
          rfl }
    letI : MulAction ↥(K ⊔ P) Q := MulAction.compHom Q toNormalizer
    (∀ a : ↥(K ⊔ P), ∀ x y : Q,
        a • (x * y) = (a • x) * (a • y)) ∧
      ∀ a : ↥(K ⊔ P), a • (1 : Q) = 1 := by
  let toNormalizer : ↥(K ⊔ P) →* Subgroup.normalizer (Q : Set G) :=
    { toFun := fun x =>
        ⟨(x : G), claim_4_K_sup_P_le_normalizer_Q
          H D Q K V W Q0 S Q1 P t s p hch x.2⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  let : MulAction ↥(K ⊔ P) Q := MulAction.compHom Q toNormalizer
  constructor
  · intro a x y
    apply Subtype.ext
    simp [claim_4_KP_action_conj H D Q K V W Q0 S Q1 P t s p hch, mul_assoc]
  · intro a
    apply Subtype.ext
    simp [claim_4_KP_action_conj H D Q K V W Q0 S Q1 P t s p hch]

/- Claim (4): the reduced Frobenius/Wielandt source core for the concrete
fixed-point calculation. The fixed-point subgroup is expressed with the library
`fixedPointSubgroup`, not with a local data wrapper. -/
-- Huppert-Blackburn XI.12.4.
private theorem chapter2_claim4_wielandt_fixed_point_formula_source
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
    [MulDistribMulAction ↥(K ⊔ P) Q]
    (haction_conj : ∀ a : ↥(K ⊔ P), ∀ q : Q,
      ((a • q : Q) : G) = (a : G) * (q : G) * (a : G)⁻¹) :
    let Psrc : Subgroup ↥(K ⊔ P) := P.subgroupOf (K ⊔ P)
    letI : MulDistribMulAction (↥Psrc) Q := MulDistribMulAction.compHom Q Psrc.subtype
    Nat.card Q = Nat.card (fixedPointSubgroup (↥Psrc) Q) ^ p := by
  classical
  let Ksrc : Subgroup ↥(K ⊔ P) := K.subgroupOf (K ⊔ P)
  let Psrc : Subgroup ↥(K ⊔ P) := P.subgroupOf (K ⊔ P)
  have : Fact p.Prime := ⟨hch.B1.p_prime⟩
  have hV_le_D : V ≤ D :=
    PFchapter1section2.proposition_3_V_le_D
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hKP_le_D : K ⊔ P ≤ D :=
    sup_le hch.section3.section2.K_le_D (hch.B1.P_le_V.trans hV_le_D)
  have hKnormalD : (K.subgroupOf D).Normal :=
    (PFchapter1section2.proposition_2
      H D Q K V W Q0 S Q1 t hch.section3.section2).2
  have hKnormalizer : K ⊔ P ≤ Subgroup.normalizer (K : Set G) :=
    hKP_le_D.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hch.section3.section2.K_le_D).mp
        hKnormalD)
  have hKsrc_normal : Ksrc.Normal := by
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (show K ≤ K ⊔ P from le_sup_left)).2 hKnormalizer
  have hP_le_centralizer : P ≤ Subgroup.centralizer (P : Set G) := by
    have hPcyclic : IsCyclic P := isCyclic_of_prime_card hch.B1.P_card
    let : CommGroup P := hPcyclic.commGroup
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    have hcomm : (⟨x, hxP⟩ : P) * ⟨y, hyP⟩ = ⟨y, hyP⟩ * ⟨x, hxP⟩ :=
      mul_comm _ _
    exact (congrArg Subtype.val hcomm).symm
  have hKP_bot : K ⊓ P = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxKC : x ∈ K ⊓ Subgroup.centralizer (P : Set G) :=
        ⟨hx.1, hP_le_centralizer hx.2⟩
      simpa [claim_1_K_inf_centralizer_P_eq_bot
        H D Q K V W Q0 S Q1 P t s p hch] using hxKC
    · exact bot_le
  have hdisj : Disjoint Ksrc Psrc := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hxKP : (x : G) ∈ K ⊓ P := ⟨hx.1, hx.2⟩
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by simpa [hKP_bot] using hxKP
    simpa using hxbot
  have hsup : Ksrc ⊔ Psrc = ⊤ := by
    rw [← Subgroup.subgroupOf_sup
      (A := K) (A' := P) (B := K ⊔ P) le_sup_left le_sup_right]
    simp
  have hcomp : Ksrc.IsComplement' Psrc := by
    let : Ksrc.Normal := hKsrc_normal
    exact isComplement'_of_disjoint_sup_eq_top_of_normal Ksrc Psrc hdisj hsup
  have hKsrc_ne : Ksrc ≠ ⊥ := by
    obtain ⟨k, hkK, hk_ne⟩ :=
      PFchapter1section2.proposition_1_b_K_nontrivial
        H D Q K V W Q0 S Q1 t hch.section3.section2
    intro hbot
    let kKP : ↥(K ⊔ P) := ⟨k, (show K ≤ K ⊔ P from le_sup_left) hkK⟩
    have hkKsrc : kKP ∈ Ksrc := hkK
    have hkbot : kKP ∈ (⊥ : Subgroup ↥(K ⊔ P)) := by simpa [hbot] using hkKsrc
    exact hk_ne (by simpa [kKP] using hkbot)
  have hP_ne : P ≠ ⊥ := by
    intro hP
    have hcard : Nat.card P = 1 := by simp [hP, Nat.card]
    exact hch.B1.p_prime.ne_one (hch.B1.P_card ▸ hcard)
  have hPsrc_ne : Psrc ≠ ⊥ := by
    intro hbot
    apply hP_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxP
    let xKP : ↥(K ⊔ P) := ⟨x, (show P ≤ K ⊔ P from le_sup_right) hxP⟩
    have hxPsrc : xKP ∈ Psrc := hxP
    have hxbot : xKP ∈ (⊥ : Subgroup ↥(K ⊔ P)) := by simpa [hbot] using hxPsrc
    simpa [xKP] using hxbot
  have hcent :
      ∀ x : Psrc, x ≠ 1 →
        elementCentralizerIn Ksrc (x : ↥(K ⊔ P)) = ⊥ := by
    intro x hx_ne
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    let xP : P := ⟨((x : ↥(K ⊔ P)) : G), x.property⟩
    have hxP_ne : xP ≠ 1 := by
      intro hxP_one
      apply hx_ne
      apply Subtype.ext
      apply Subtype.ext
      simpa [xP] using congrArg Subtype.val hxP_one
    have hcommKP : Commute (y : ↥(K ⊔ P)) (x : ↥(K ⊔ P)) :=
      Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have hcommG : Commute (((y : ↥(K ⊔ P)) : G)) (((x : ↥(K ⊔ P)) : G)) := by
      exact congrArg Subtype.val hcommKP.eq
    have hycent : ((y : ↥(K ⊔ P)) : G) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hzP
      let zP : P := ⟨z, hzP⟩
      have hzmem : zP ∈ Subgroup.zpowers xP :=
        mem_zpowers_of_prime_card hch.B1.P_card hxP_ne
      rcases Subgroup.mem_zpowers_iff.mp hzmem with ⟨n, hn⟩
      have hcommz := hcommG.zpow_right n
      have hxpow : (((x : ↥(K ⊔ P)) : G)) ^ n = z := by
        simpa [xP, zP] using congrArg Subtype.val hn
      rw [hxpow] at hcommz
      exact hcommz.eq.symm
    have hybot : ((y : ↥(K ⊔ P)) : G) ∈ (⊥ : Subgroup G) := by
      rw [← claim_1_K_inf_centralizer_P_eq_bot
        H D Q K V W Q0 S Q1 P t s p hch]
      exact ⟨hy.1, hycent⟩
    apply Subtype.ext
    simpa using hybot
  have hfrob : IsFrobeniusGroupWithKernelComplement Ksrc Psrc :=
    (lemma_3_1 Ksrc Psrc hKsrc_ne hPsrc_ne hKsrc_normal hcomp).2 hcent
  have hKbot :
      letI : MulDistribMulAction (↥Ksrc) Q :=
        MulDistribMulAction.compHom Q Ksrc.subtype
      fixedPointSubgroup (↥Ksrc) Q = ⊥ := by
    let : MulDistribMulAction (↥Ksrc) Q :=
      MulDistribMulAction.compHom Q Ksrc.subtype
    rw [Subgroup.eq_bot_iff_forall]
    intro q hqfix
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hqfix
    obtain ⟨k, hkK, hk_ne⟩ :=
      PFchapter1section2.proposition_1_b_K_nontrivial
        H D Q K V W Q0 S Q1 t hch.section3.section2
    let kKP : ↥(K ⊔ P) := ⟨k, (show K ≤ K ⊔ P from le_sup_left) hkK⟩
    let kKsrc : Ksrc := ⟨kKP, hkK⟩
    have hfix : kKsrc • q = q := hqfix kKsrc
    have hfixQ : kKP • q = q := by
      change kKsrc • q = q
      exact hfix
    have hfixG : ((kKP • q : Q) : G) = (q : G) := by
      exact congrArg (fun z : Q => (z : G)) hfixQ
    have hconj : k * (q : G) * k⁻¹ = (q : G) := by
      have hact := haction_conj kKP q
      exact hact.symm.trans hfixG
    have hqcent : (q : G) ∈ Subgroup.centralizer ({k} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    have hqbot : (q : G) ∈ (⊥ : Subgroup G) := by
      rw [← PFchapter1section2.proposition_1_a
        H D Q K V W Q0 S Q1 t hch.section3.section2 k hkK hk_ne]
      exact ⟨hqcent, q.property⟩
    apply Subtype.ext
    simpa using hqbot
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ
    have hcard : Nat.card Q = 1 := by simp [hQ, Nat.card]
    have heven := hch.section3.section2.hA.A1.Q_even
    rw [hcard] at heven
    exact Nat.not_even_one heven
  let : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).2 hQ_ne
  let : Group.IsNilpotent Q :=
    PFchapter1section2.proposition_1_b
      H D Q K V W Q0 S Q1 t hch.section3.section2
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card ↥(K ⊔ P)) :=
    (claim_3 H D Q K V W Q0 S Q1 P t s p hch).2
  let : Fintype Ksrc := Fintype.ofFinite Ksrc
  have hprod :=
    Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq
      (G := ↥(K ⊔ P)) (V := Q)
      hcop (show Group.IsSolvable Q from inferInstance)
      (Wielandt.frobeniusProductSubgroup Ksrc Psrc)
      (Wielandt.frobeniusProductLeftCoeff Ksrc)
      (Wielandt.frobeniusProductRightCoeff Ksrc)
      (Wielandt.frobeniusProduct_coeff_sum_eq Ksrc Psrc hfrob)
  have hcore :=
    Wielandt.fixedPointSubgroup_card_identity_kernel_fixed_bot_of_frobenius_of_product_card_eq
      (A := ↥(K ⊔ P)) (M := Q) Ksrc Psrc hKbot hprod
  have hPsrc_card : Nat.card Psrc = p := by
    calc
      Nat.card Psrc = Nat.card P :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (show P ≤ K ⊔ P from le_sup_right)).toEquiv
      _ = p := hch.B1.P_card
  simpa [Psrc, hPsrc_card] using hcore

private theorem claim_4_fixed_point_formula_obligation
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
    Nat.card Q = Nat.card (↥(Q ⊓ Subgroup.centralizer (P : Set G))) ^ p := by
  let toNormalizer : ↥(K ⊔ P) →* Subgroup.normalizer (Q : Set G) :=
    { toFun := fun x =>
        ⟨(x : G), claim_4_K_sup_P_le_normalizer_Q
          H D Q K V W Q0 S Q1 P t s p hch x.2⟩
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  let : MulAction ↥(K ⊔ P) Q := MulAction.compHom Q toNormalizer
  have hauto :
      (∀ a : ↥(K ⊔ P), ∀ x y : Q,
          a • (x * y) = (a • x) * (a • y)) ∧
        ∀ a : ↥(K ⊔ P), a • (1 : Q) = 1 :=
    claim_4_KP_action_by_automorphisms H D Q K V W Q0 S Q1 P t s p hch
  let : MulDistribMulAction ↥(K ⊔ P) Q :=
    { (inferInstance : MulAction ↥(K ⊔ P) Q) with
      smul_mul := hauto.1
      smul_one := hauto.2 }
  have haction_conj :
      ∀ a : ↥(K ⊔ P), ∀ q : Q,
        ((a • q : Q) : G) = (a : G) * (q : G) * (a : G)⁻¹ :=
    claim_4_KP_action_conj H D Q K V W Q0 S Q1 P t s p hch
  let Psrc : Subgroup ↥(K ⊔ P) := P.subgroupOf (K ⊔ P)
  let : MulDistribMulAction (↥Psrc) Q := MulDistribMulAction.compHom Q Psrc.subtype
  have hfixed_external :
      Nat.card Q = Nat.card (fixedPointSubgroup (↥Psrc) Q) ^ p := by
    simpa [Psrc] using
      (chapter2_claim4_wielandt_fixed_point_formula_source
        H D Q K V W Q0 S Q1 P t s p hch haction_conj)
  have hfixed_equiv_centralizer :
      fixedPointSubgroup (↥Psrc) Q ≃
        ↥(Q ⊓ Subgroup.centralizer (P : Set G)) := by
    refine
      { toFun := ?toFun
        invFun := ?invFun
        left_inv := ?left_inv
        right_inv := ?right_inv }
    · intro x
      refine ⟨(x.1 : G), ?_⟩
      refine ⟨x.1.2, ?_⟩
      change (x.1 : G) ∈ Subgroup.centralizer (P : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hyP
      let aSup : ↥(K ⊔ P) := ⟨y, (show P ≤ K ⊔ P from le_sup_right) hyP⟩
      have haPsrc : aSup ∈ Psrc := by
        have haPsub : aSup ∈ P.subgroupOf (K ⊔ P) := by
          simpa [Subgroup.mem_subgroupOf, aSup] using hyP
        simpa [Psrc] using haPsub
      let aPsrc : Psrc := ⟨aSup, haPsrc⟩
      have hxmem : (x.1 : Q) ∈ FixedPoints.subgroup (↥Psrc) Q := by
        simp [fixedPointSubgroup]
      have hfix : aPsrc • x.1 = x.1 :=
        (FixedPoints.mem_subgroup (M := ↥Psrc) (α := Q) (a := x.1)).1 hxmem aPsrc
      have hparent_fix : aSup • x.1 = x.1 := by
        simpa [aPsrc, MulAction.compHom_smul_def] using hfix
      have hfixG : ((aSup • x.1 : Q) : G) = (x.1 : G) :=
        congrArg (fun z : Q => (z : G)) hparent_fix
      have hconj : y * (x.1 : G) * y⁻¹ = (x.1 : G) := by
        have hact := haction_conj aSup x.1
        simpa [aSup] using hact.symm.trans hfixG
      exact mul_inv_eq_iff_eq_mul.mp hconj
    · intro z
      refine ⟨⟨(z : G), z.2.1⟩, ?_⟩
      show (⟨(z : G), z.2.1⟩ : Q) ∈ FixedPoints.subgroup (↥Psrc) Q
      rw [FixedPoints.mem_subgroup]
      intro aPsrc
      apply Subtype.ext
      have haP : ((aPsrc : ↥(K ⊔ P)) : G) ∈ P := by
        have haPsub : (aPsrc : ↥(K ⊔ P)) ∈ P.subgroupOf (K ⊔ P) := by
          simp [Psrc]
        exact Subgroup.mem_subgroupOf.mp haPsub
      have hcomm : ((aPsrc : ↥(K ⊔ P)) : G) * (z : G) =
          (z : G) * ((aPsrc : ↥(K ⊔ P)) : G) :=
        (Subgroup.mem_centralizer_iff.mp z.2.2) ((aPsrc : ↥(K ⊔ P)) : G) haP
      have hconj : ((aPsrc : ↥(K ⊔ P)) : G) * (z : G) *
          ((aPsrc : ↥(K ⊔ P)) : G)⁻¹ = (z : G) :=
        mul_inv_eq_iff_eq_mul.mpr hcomm
      calc
        (((aPsrc : ↥Psrc) • (⟨(z : G), z.2.1⟩ : Q) : Q) : G) =
            (((aPsrc : ↥(K ⊔ P)) • (⟨(z : G), z.2.1⟩ : Q) : Q) : G) := by
          rfl
        _ = ((aPsrc : ↥(K ⊔ P)) : G) * (z : G) * ((aPsrc : ↥(K ⊔ P)) : G)⁻¹ :=
          haction_conj (aPsrc : ↥(K ⊔ P)) ⟨(z : G), z.2.1⟩
        _ = (z : G) := hconj
    · intro x
      apply Subtype.ext
      rfl
    · intro z
      apply Subtype.ext
      rfl
  exact hfixed_external.trans (by
    exact congrArg (fun n : ℕ => n ^ p) (Nat.card_congr hfixed_equiv_centralizer))
public theorem claim_4
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
    Nat.card Q = Nat.card (↥(Q ⊓ Subgroup.centralizer (P : Set G))) ^ p := by
  exact claim_4_fixed_point_formula_obligation H D Q K V W Q0 S Q1 P t s p hch

end PFchapter2
end CFSG.BenderSuzuki
