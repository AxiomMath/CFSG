module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixII.proposition_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL28Facts
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_6_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_9
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
import Mathlib.Data.Nat.Factorization.PrimePow

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (13)
-/

/- Checked Bruhat-cover portion of Chapter I, Section 3, Lemma 4. -/

private theorem lemma_4_braid_of_order_three_involutions
    {G : Type*} [Group G] {s t : G}
    (hs : IsInvolution s) (ht : IsInvolution t)
    (hst : orderOf (s * t) = 3) :
    t * s * t = s * t * s := by
  have ht2 : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hs_inv : s⁻¹ = s := hs.inv_eq_self
  have ht_inv : t⁻¹ = t := ht.inv_eq_self
  have hpow : (s * t) ^ 3 = 1 := by
    simpa [hst] using pow_orderOf_eq_one (s * t)
  have hinv : (s * t)⁻¹ = (s * t) ^ 2 := by
    calc
      (s * t)⁻¹ = (s * t)⁻¹ * 1 := by simp
      _ = (s * t)⁻¹ * ((s * t) ^ 3) := by rw [hpow]
      _ = (s * t) ^ 2 := by simp [pow_succ, mul_assoc]
  calc
    t * s * t = (s * t)⁻¹ * t := by
      simp [mul_inv_rev, hs_inv, ht_inv, mul_assoc]
    _ = (s * t) ^ 2 * t := by rw [hinv]
    _ = s * t * s := by simp [pow_two, ht2, mul_assoc]

private theorem lemma_4_rightConjugate_Q0_mem_of_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q k : G, q ∈ Q0 → k ∈ K → rightConjugateElem q k ∈ Q0 := by
  intro q k hq hk
  classical
  let d : D := ⟨k⁻¹, D.inv_mem (hsec.section2.K_le_D hk)⟩
  let qQ0 : Q0 := ⟨q, hq⟩
  have hmem :=
    PFchapter1section2.proposition_3_Q0_rightConjugate_mem_of_D
      H D Q K V W Q0 S Q1 t hsec.section2 d qQ0
  simpa [d, qQ0] using hmem

private theorem lemma_4_leftConjugate_Q0_mem_of_K
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q k : G, q ∈ Q0 → k ∈ K → k * q * k⁻¹ ∈ Q0 := by
  intro q k hq hk
  have hmem :=
    lemma_4_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
      q k⁻¹ hq (K.inv_mem hk)
  simpa [rightConjugateElem] using hmem

private theorem lemma_4_t_conjugate_K_mem
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ k : G, k ∈ K → t * k * t ∈ K := by
  intro k hk
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have htk : t * k * t = k⁻¹ := by
    have hkanti := ((hsec.section2.K_def k).mp hk).2
    simpa [rightConjugateElem, ht_inv] using hkanti
  simpa [htk] using K.inv_mem hk

private theorem lemma_4_q0K_mul_q0K_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q₁ k₁ q₂ k₂ : G,
      q₁ ∈ Q0 → k₁ ∈ K → q₂ ∈ Q0 → k₂ ∈ K →
        (q₁ * k₁) * (q₂ * k₂) ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro q₁ k₁ q₂ k₂ hq₁ hk₁ hq₂ hk₂
  left
  have hq₂' : k₁ * q₂ * k₁⁻¹ ∈ Q0 :=
    lemma_4_leftConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
      q₂ k₁ hq₂ hk₁
  refine ⟨q₁ * (k₁ * q₂ * k₁⁻¹), k₁ * k₂,
    Q0.mul_mem hq₁ hq₂', K.mul_mem hk₁ hk₂, ?_⟩
  group

private theorem lemma_4_q0K_mul_q0KtQ0_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q₁ k₁ q₂ k₂ r₂ : G,
      q₁ ∈ Q0 → k₁ ∈ K → q₂ ∈ Q0 → k₂ ∈ K → r₂ ∈ Q0 →
        (q₁ * k₁) * (q₂ * k₂ * t * r₂) ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro q₁ k₁ q₂ k₂ r₂ hq₁ hk₁ hq₂ hk₂ hr₂
  right
  have hq₂' : k₁ * q₂ * k₁⁻¹ ∈ Q0 :=
    lemma_4_leftConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
      q₂ k₁ hq₂ hk₁
  refine ⟨q₁ * (k₁ * q₂ * k₁⁻¹), k₁ * k₂, r₂,
    Q0.mul_mem hq₁ hq₂', K.mul_mem hk₁ hk₂, hr₂, ?_⟩
  group

private theorem lemma_4_union_mul_Q0_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ x q : G,
      x ∈ q0KUnionQ0KtQ0 Q0 K t → q ∈ Q0 →
        x * q ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro x q hx hq
  rcases hx with ⟨q₁, k₁, hq₁, hk₁, rfl⟩ |
    ⟨q₁, k₁, r₁, hq₁, hk₁, hr₁, rfl⟩
  · simpa using
      lemma_4_q0K_mul_q0K_mem_union H D Q K V W Q0 S Q1 t s hsec
        q₁ k₁ q 1 hq₁ hk₁ hq K.one_mem
  · right
    refine ⟨q₁, k₁, r₁ * q, hq₁, hk₁, Q0.mul_mem hr₁ hq, ?_⟩
    group

private theorem lemma_4_q0K_mul_union_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q k x : G,
      q ∈ Q0 → k ∈ K → x ∈ q0KUnionQ0KtQ0 Q0 K t →
        (q * k) * x ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro q k x hq hk hx
  rcases hx with ⟨q₂, k₂, hq₂, hk₂, rfl⟩ |
    ⟨q₂, k₂, r₂, hq₂, hk₂, hr₂, rfl⟩
  · exact
      lemma_4_q0K_mul_q0K_mem_union H D Q K V W Q0 S Q1 t s hsec
        q k q₂ k₂ hq hk hq₂ hk₂
  · exact
      lemma_4_q0K_mul_q0KtQ0_mem_union H D Q K V W Q0 S Q1 t s hsec
        q k q₂ k₂ r₂ hq hk hq₂ hk₂ hr₂

private theorem lemma_4_q0KUnionQ0KtQ0_subset_generated
    {G : Type*} [Group G] (Q0 K : Subgroup G) (t : G) :
    q0KUnionQ0KtQ0 Q0 K t ⊆ (psl2GeneratedSubgroup Q0 K t : Set G) := by
  intro x hx
  let L : Subgroup G := psl2GeneratedSubgroup Q0 K t
  have hQ0_le : Q0 ≤ L := by
    intro q hq
    exact Subgroup.subset_closure (Or.inl (Or.inl hq))
  have hK_le : K ≤ L := by
    intro k hk
    exact Subgroup.subset_closure (Or.inl (Or.inr hk))
  have ht_mem : t ∈ L := Subgroup.subset_closure (Or.inr rfl)
  rcases hx with ⟨q, k, hq, hk, rfl⟩ | ⟨q, k, q', hq, hk, hq', rfl⟩
  · exact L.mul_mem (hQ0_le hq) (hK_le hk)
  · simpa [mul_assoc] using
      L.mul_mem (L.mul_mem (L.mul_mem (hQ0_le hq) (hK_le hk)) ht_mem) (hQ0_le hq')

private theorem lemma_4_t_conjugate_Q0_subset_union_of_braid
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hbraid : t * s * t = s * t * s) :
    ∀ q : G, q ∈ Q0 → t * q * t ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro q hq
  classical
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  rcases (hsec.section2.Q0_def q).mp hq with hq_one | hq_inv
  · left
    refine ⟨1, 1, Q0.one_mem, K.one_mem, ?_⟩
    simp [hq_one, ht_sq]
  · rcases hq_inv with ⟨hqH, hqI⟩
    have hprop3 :=
      (PFchapter1section1.proposition_3 H D Q t hsec.section2.hA.A1).2
        s hsec.s_mem_H
          hsec.s_involution
    rcases (hprop3 q).1 ⟨hqH, hqI⟩ with ⟨k, hkKset, hkq⟩
    have hkK : k ∈ K := (hsec.section2.K_def k).mpr hkKset
    have hkInvK : k⁻¹ ∈ K := K.inv_mem hkK
    have hkInvKset : k⁻¹ ∈ peterfalviKSet D t :=
      (hsec.section2.K_def k⁻¹).mp hkInvK
    have hq1Q0 : rightConjugateElem s k⁻¹ ∈ Q0 := by
      apply (hsec.section2.Q0_def (rightConjugateElem s k⁻¹)).mpr
      right
      exact (hprop3 (rightConjugateElem s k⁻¹)).2 ⟨k⁻¹, hkInvKset, rfl⟩
    have htk : t * k * t = k⁻¹ := by
      have hkanti := ((hsec.section2.K_def k).mp hkK).2
      simpa [rightConjugateElem, ht_inv] using hkanti
    have htk_inv : t * k⁻¹ * t = k := by
      have hkinvanti := ((hsec.section2.K_def k⁻¹).mp hkInvK).2
      simpa [rightConjugateElem, ht_inv] using hkinvanti
    have htk_comm : t * k = k⁻¹ * t := by
      calc
        t * k = t * k * 1 := by simp
        _ = t * k * (t * t) := by rw [ht_sq]
        _ = (t * k * t) * t := by group
        _ = k⁻¹ * t := by rw [htk]
    have hktk : k * t * k = t := by
      calc
        k * t * k = k * (t * k) := by rw [mul_assoc]
        _ = k * (k⁻¹ * t) := by rw [htk_comm]
        _ = t := by group
    right
    refine ⟨rightConjugateElem s k⁻¹, k * k, rightConjugateElem s k⁻¹,
      hq1Q0, K.mul_mem hkK hkK, hq1Q0, ?_⟩
    exact calc
      t * q * t = t * rightConjugateElem s k * t := by
        rw [← hkq]
      _ = (t * k⁻¹ * t) * (t * s * t) * (t * k * t) := by
        rw [rightConjugateElem]
        symm
        calc
          (t * k⁻¹ * t) * (t * s * t) * (t * k * t)
              = t * k⁻¹ * (t * t) * s * (t * t) * k * t := by group
          _ = t * (k⁻¹ * s * k) * t := by
            rw [ht_sq]
            group
      _ = k * (s * t * s) * k⁻¹ := by
        rw [htk_inv, hbraid, htk]
      _ = rightConjugateElem s k⁻¹ * (k * k) * t * rightConjugateElem s k⁻¹ := by
        symm
        calc
          rightConjugateElem s k⁻¹ * (k * k) * t * rightConjugateElem s k⁻¹ =
              (k * s * k⁻¹) * (k * k) * t * (k * s * k⁻¹) := by
            simp [rightConjugateElem]
          _ = k * s * k * t * k * s * k⁻¹ := by group
          _ = k * s * (k * t * k) * s * k⁻¹ := by group
          _ = k * s * t * s * k⁻¹ := by rw [hktk]
          _ = k * (s * t * s) * k⁻¹ := by group

private theorem lemma_4_q0KtQ0_mul_q0KtQ0_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hbraid : t * s * t = s * t * s) :
    ∀ q₁ k₁ r₁ q₂ k₂ r₂ : G,
      q₁ ∈ Q0 → k₁ ∈ K → r₁ ∈ Q0 →
      q₂ ∈ Q0 → k₂ ∈ K → r₂ ∈ Q0 →
        (q₁ * k₁ * t * r₁) * (q₂ * k₂ * t * r₂) ∈
          q0KUnionQ0KtQ0 Q0 K t := by
  intro q₁ k₁ r₁ q₂ k₂ r₂ hq₁ hk₁ hr₁ hq₂ hk₂ hr₂
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  have htt_cancel : ∀ a : G, t * (t * a) = a := by
    intro a
    calc
      t * (t * a) = (t * t) * a := by rw [mul_assoc]
      _ = 1 * a := by rw [ht_sq]
      _ = a := by simp
  let qmid : G := r₁ * q₂
  let qtwist : G := rightConjugateElem qmid k₂
  have hqmid : qmid ∈ Q0 := Q0.mul_mem hr₁ hq₂
  have hqtwist : qtwist ∈ Q0 :=
    lemma_4_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
      qmid k₂ hqmid hk₂
  have hkt : t * k₂ * t ∈ K :=
    lemma_4_t_conjugate_K_mem H D Q K V W Q0 S Q1 t s hsec k₂ hk₂
  have hmiddle : t * qtwist * t ∈ q0KUnionQ0KtQ0 Q0 K t :=
    lemma_4_t_conjugate_Q0_subset_union_of_braid
      H D Q K V W Q0 S Q1 t s hsec hbraid qtwist hqtwist
  have hleft :
      (q₁ * (k₁ * (t * k₂ * t))) * (t * qtwist * t) ∈
        q0KUnionQ0KtQ0 Q0 K t :=
    lemma_4_q0K_mul_union_mem_union H D Q K V W Q0 S Q1 t s hsec
      q₁ (k₁ * (t * k₂ * t)) (t * qtwist * t) hq₁
      (K.mul_mem hk₁ hkt) hmiddle
  have hright :
      ((q₁ * (k₁ * (t * k₂ * t))) * (t * qtwist * t)) * r₂ ∈
        q0KUnionQ0KtQ0 Q0 K t :=
    lemma_4_union_mul_Q0_mem_union H D Q K V W Q0 S Q1 t s hsec
      ((q₁ * (k₁ * (t * k₂ * t))) * (t * qtwist * t)) r₂ hleft hr₂
  have heq :
      (q₁ * k₁ * t * r₁) * (q₂ * k₂ * t * r₂) =
        ((q₁ * (k₁ * (t * k₂ * t))) * (t * qtwist * t)) * r₂ := by
    simp only [qtwist, qmid, rightConjugateElem, mul_assoc]
    rw [htt_cancel]
    group
  simpa [heq] using hright

private theorem lemma_4_q0KtQ0_mul_q0K_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ q₁ k₁ r₁ q₂ k₂ : G,
      q₁ ∈ Q0 → k₁ ∈ K → r₁ ∈ Q0 → q₂ ∈ Q0 → k₂ ∈ K →
        (q₁ * k₁ * t * r₁) * (q₂ * k₂) ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro q₁ k₁ r₁ q₂ k₂ hq₁ hk₁ hr₁ hq₂ hk₂
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  have htt_cancel : ∀ a : G, t * (t * a) = a := by
    intro a
    calc
      t * (t * a) = (t * t) * a := by rw [mul_assoc]
      _ = 1 * a := by rw [ht_sq]
      _ = a := by simp
  let qmid : G := r₁ * q₂
  let qtwist : G := rightConjugateElem qmid k₂
  have hqmid : qmid ∈ Q0 := Q0.mul_mem hr₁ hq₂
  have hqtwist : qtwist ∈ Q0 :=
    lemma_4_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
      qmid k₂ hqmid hk₂
  have hkt : t * k₂ * t ∈ K :=
    lemma_4_t_conjugate_K_mem H D Q K V W Q0 S Q1 t s hsec k₂ hk₂
  right
  refine ⟨q₁, k₁ * (t * k₂ * t), qtwist,
    hq₁, K.mul_mem hk₁ hkt, hqtwist, ?_⟩
  simp only [qtwist, qmid, rightConjugateElem, mul_assoc]
  rw [htt_cancel]
  group

private theorem lemma_4_union_mul_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hbraid : t * s * t = s * t * s) :
    ∀ x y : G,
      x ∈ q0KUnionQ0KtQ0 Q0 K t →
      y ∈ q0KUnionQ0KtQ0 Q0 K t →
        x * y ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro x y hx hy
  rcases hx with ⟨q₁, k₁, hq₁, hk₁, rfl⟩ |
    ⟨q₁, k₁, r₁, hq₁, hk₁, hr₁, rfl⟩
  · rcases hy with ⟨q₂, k₂, hq₂, hk₂, rfl⟩ |
      ⟨q₂, k₂, r₂, hq₂, hk₂, hr₂, rfl⟩
    · exact
        lemma_4_q0K_mul_q0K_mem_union H D Q K V W Q0 S Q1 t s hsec
          q₁ k₁ q₂ k₂ hq₁ hk₁ hq₂ hk₂
    · exact
        lemma_4_q0K_mul_q0KtQ0_mem_union H D Q K V W Q0 S Q1 t s hsec
          q₁ k₁ q₂ k₂ r₂ hq₁ hk₁ hq₂ hk₂ hr₂
  · rcases hy with ⟨q₂, k₂, hq₂, hk₂, rfl⟩ |
      ⟨q₂, k₂, r₂, hq₂, hk₂, hr₂, rfl⟩
    · exact
        lemma_4_q0KtQ0_mul_q0K_mem_union H D Q K V W Q0 S Q1 t s hsec
          q₁ k₁ r₁ q₂ k₂ hq₁ hk₁ hr₁ hq₂ hk₂
    · exact
        lemma_4_q0KtQ0_mul_q0KtQ0_mem_union H D Q K V W Q0 S Q1 t s hsec
          hbraid q₁ k₁ r₁ q₂ k₂ r₂ hq₁ hk₁ hr₁ hq₂ hk₂ hr₂

private theorem lemma_4_union_inv_mem_union
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)) :
    ∀ x : G,
      x ∈ q0KUnionQ0KtQ0 Q0 K t →
        x⁻¹ ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro x hx
  have ht_inv : t⁻¹ = t :=
    hsec.section2.hA.A1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.section2.hA.A1.involution_t.sq_eq_one
  rcases hx with ⟨q, k, hq, hk, rfl⟩ |
    ⟨q, k, r, hq, hk, hr, rfl⟩
  · left
    have hq' : rightConjugateElem q⁻¹ k ∈ Q0 :=
      lemma_4_rightConjugate_Q0_mem_of_K H D Q K V W Q0 S Q1 t s hsec
        q⁻¹ k (Q0.inv_mem hq) hk
    refine ⟨rightConjugateElem q⁻¹ k, k⁻¹, hq', K.inv_mem hk, ?_⟩
    simp [rightConjugateElem]
  · right
    have hk' : t * k⁻¹ * t ∈ K :=
      lemma_4_t_conjugate_K_mem H D Q K V W Q0 S Q1 t s hsec
        k⁻¹ (K.inv_mem hk)
    refine ⟨r⁻¹, t * k⁻¹ * t, q⁻¹,
      Q0.inv_mem hr, hk', Q0.inv_mem hq, ?_⟩
    calc
      (q * k * t * r)⁻¹ = r⁻¹ * t * k⁻¹ * q⁻¹ := by
        simp [mul_inv_rev, ht_inv, mul_assoc]
      _ = r⁻¹ * (t * k⁻¹ * t) * t * q⁻¹ := by
        symm
        calc
          r⁻¹ * (t * k⁻¹ * t) * t * q⁻¹ =
              r⁻¹ * t * k⁻¹ * (t * t) * q⁻¹ := by group
          _ = r⁻¹ * t * k⁻¹ * q⁻¹ := by
            rw [ht_sq]
            group

private theorem lemma_4_generator_mem_union
    {G : Type*} [Group G] (Q0 K : Subgroup G) (t : G) :
    ∀ x : G,
      x ∈ ((Q0 : Set G) ∪ (K : Set G) ∪ ({t} : Set G)) →
        x ∈ q0KUnionQ0KtQ0 Q0 K t := by
  intro x hx
  rcases hx with (hxQ0 | hxK) | hxT
  · left
    exact ⟨x, 1, hxQ0, K.one_mem, by simp⟩
  · left
    exact ⟨1, x, Q0.one_mem, hxK, by simp⟩
  · right
    refine ⟨1, 1, 1, Q0.one_mem, K.one_mem, Q0.one_mem, ?_⟩
    simpa using hxT

private theorem lemma_4_generated_subgroup_le_union_of_braid_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hbraid : t * s * t = s * t * s) :
    (psl2GeneratedSubgroup Q0 K t : Set G) ⊆ q0KUnionQ0KtQ0 Q0 K t := by
  intro x hx
  dsimp [psl2GeneratedSubgroup] at hx
  exact
    Subgroup.closure_induction
      (p := fun g _ => g ∈ q0KUnionQ0KtQ0 Q0 K t)
      (fun y hy => lemma_4_generator_mem_union Q0 K t y hy)
      (by
        left
        exact ⟨1, 1, Q0.one_mem, K.one_mem, by simp⟩)
      (fun a b _ _ ha hb =>
        lemma_4_union_mul_mem_union H D Q K V W Q0 S Q1 t s hsec hbraid
          a b ha hb)
      (fun a _ ha =>
        lemma_4_union_inv_mem_union H D Q K V W Q0 S Q1 t s hsec a ha)
      hx

private theorem lemma_4_generated_subgroup_eq_of_braid
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hbraid : t * s * t = s * t * s) :
    (psl2GeneratedSubgroup Q0 K t : Set G) = q0KUnionQ0KtQ0 Q0 K t := by
  exact Set.Subset.antisymm
    (lemma_4_generated_subgroup_le_union_of_braid_obligation
      H D Q K V W Q0 S Q1 t s hsec hbraid)
    (lemma_4_q0KUnionQ0KtQ0_subset_generated Q0 K t)

private theorem lemma_4_generated_subgroup_eq_obligation
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
    (hsec : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hst : orderOf (s * t) = 3) :
    (psl2GeneratedSubgroup Q0 K t : Set G) = q0KUnionQ0KtQ0 Q0 K t :=
  lemma_4_generated_subgroup_eq_of_braid
    H D Q K V W Q0 S Q1 t s hsec
    (lemma_4_braid_of_order_three_involutions
      hsec.s_involution
      hsec.section2.hA.A1.involution_t hst)


private theorem claim_13_generated_subgroup_card
    {G : Type*} [Group G] [Finite G]
    (H D Q K Q0 : Subgroup G) (t : G)
    (hQ0Q : Q0 ≤ Q) (hKD : K ≤ D)
    (hQH : Q ≤ H) (hDH : D ≤ H) (hQD : Disjoint Q D)
    (htH : t ∉ H) (hD_eq : D = H ⊓ rightConjugate H t)
    (hcover : (psl2GeneratedSubgroup Q0 K t : Set G) =
      q0KUnionQ0KtQ0 Q0 K t)
    (hQ0card : Nat.card Q0 = 8) (hKcard : Nat.card K = 7) :
    Nat.card (psl2GeneratedSubgroup Q0 K t) = 504 := by
  classical
  let L : Subgroup G := psl2GeneratedSubgroup Q0 K t
  have hQ0L : Q0 ≤ L := fun _ hq =>
    Subgroup.subset_closure (Or.inl (Or.inl hq))
  have hKL : K ≤ L := fun _ hk =>
    Subgroup.subset_closure (Or.inl (Or.inr hk))
  have htL : t ∈ L := Subgroup.subset_closure (Or.inr rfl)
  have hQ0H : Q0 ≤ H := hQ0Q.trans hQH
  have hKH : K ≤ H := hKD.trans hDH
  have hqk_unique :
      ∀ q1 q2 : G, q1 ∈ Q0 → q2 ∈ Q0 →
        ∀ k1 k2 : G, k1 ∈ K → k2 ∈ K →
          q1 * k1 = q2 * k2 → q1 = q2 ∧ k1 = k2 := by
    intro q1 q2 hq1 hq2 k1 k2 hk1 hk2 heq
    have hcross : q2⁻¹ * q1 = k2 * k1⁻¹ := by
      calc
        q2⁻¹ * q1 = q2⁻¹ * (q1 * k1) * k1⁻¹ := by group
        _ = q2⁻¹ * (q2 * k2) * k1⁻¹ := by rw [heq]
        _ = k2 * k1⁻¹ := by group
    have hmem : q2⁻¹ * q1 ∈ Q ⊓ D := by
      refine ⟨Q.mul_mem (Q.inv_mem (hQ0Q hq2)) (hQ0Q hq1), ?_⟩
      rw [hcross]
      exact D.mul_mem (hKD hk2) (D.inv_mem (hKD hk1))
    have hone : q2⁻¹ * q1 = 1 := by
      rw [hQD.eq_bot] at hmem
      simpa using hmem
    have hq : q1 = q2 := (inv_mul_eq_one.mp hone).symm
    subst q2
    exact ⟨rfl, mul_left_cancel heq⟩
  have hqtq_unique :
      ∀ q1 q2 : G, q1 ∈ Q0 → q2 ∈ Q0 →
        ∀ k1 k2 : G, k1 ∈ K → k2 ∈ K →
          ∀ r1 r2 : G, r1 ∈ Q0 → r2 ∈ Q0 →
            q1 * k1 * t * r1 = q2 * k2 * t * r2 →
              q1 = q2 ∧ k1 = k2 ∧ r1 = r2 := by
    intro q1 q2 hq1 hq2 k1 k2 hk1 hk2 r1 r2 hr1 hr2 heq
    let a : G := r1 * r2⁻¹
    have haQ : a ∈ Q := Q.mul_mem (hQ0Q hr1) (Q.inv_mem (hQ0Q hr2))
    have haH : a ∈ H := hQH haQ
    have hconj_eq : t * a * t⁻¹ = (q1 * k1)⁻¹ * (q2 * k2) := by
      dsimp [a]
      calc
        t * (r1 * r2⁻¹) * t⁻¹ =
            (q1 * k1)⁻¹ * (q1 * k1 * t * r1) * r2⁻¹ * t⁻¹ := by group
        _ = (q1 * k1)⁻¹ * (q2 * k2 * t * r2) * r2⁻¹ * t⁻¹ := by rw [heq]
        _ = (q1 * k1)⁻¹ * (q2 * k2) := by group
    have hconjH : t * a * t⁻¹ ∈ H := by
      rw [hconj_eq]
      exact H.mul_mem (H.inv_mem (H.mul_mem (hQ0H hq1) (hKH hk1)))
        (H.mul_mem (hQ0H hq2) (hKH hk2))
    have haHt : a ∈ rightConjugate H t := by
      rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
      refine ⟨t * a * t⁻¹, hconjH, ?_⟩
      simp [mul_assoc]
    have haD : a ∈ D := by
      rw [hD_eq]
      exact ⟨haH, haHt⟩
    have ha_one : a = 1 := by
      have ha_inf : a ∈ Q ⊓ D := ⟨haQ, haD⟩
      rw [hQD.eq_bot] at ha_inf
      simpa using ha_inf
    have hr_eq : r1 = r2 := by
      exact mul_inv_eq_one.mp (by simpa [a] using ha_one)
    subst r2
    have hqk_eq : q1 * k1 = q2 * k2 := by
      have h := congrArg (fun z : G => z * (t * r1)⁻¹) heq
      simpa [mul_assoc] using h
    rcases hqk_unique q1 q2 hq1 hq2 k1 k2 hk1 hk2 hqk_eq with
      ⟨hq, hk⟩
    exact ⟨hq, hk, rfl⟩
  have hcells_disjoint :
      ∀ q1 q2 : G, q1 ∈ Q0 → q2 ∈ Q0 →
        ∀ k1 k2 : G, k1 ∈ K → k2 ∈ K →
          ∀ r : G, r ∈ Q0 → q1 * k1 ≠ q2 * k2 * t * r := by
    intro q1 q2 hq1 hq2 k1 k2 hk1 hk2 r hr heq
    apply htH
    have ht_eq : t = (q2 * k2)⁻¹ * (q1 * k1) * r⁻¹ := by
      calc
        t = (q2 * k2)⁻¹ * (q2 * k2 * t * r) * r⁻¹ := by group
        _ = (q2 * k2)⁻¹ * (q1 * k1) * r⁻¹ := by rw [← heq]
    rw [ht_eq]
    exact H.mul_mem
      (H.mul_mem (H.inv_mem (H.mul_mem (hQ0H hq2) (hKH hk2)))
        (H.mul_mem (hQ0H hq1) (hKH hk1)))
      (H.inv_mem (hQ0H hr))
  let f : (Q0 × K) ⊕ ((Q0 × K) × Q0) → L
    | Sum.inl qk =>
        ⟨(qk.1 : G) * (qk.2 : G), L.mul_mem (hQ0L qk.1.2) (hKL qk.2.2)⟩
    | Sum.inr qkr =>
        ⟨(qkr.1.1 : G) * (qkr.1.2 : G) * t * (qkr.2 : G),
          L.mul_mem (L.mul_mem (L.mul_mem (hQ0L qkr.1.1.2) (hKL qkr.1.2.2)) htL)
            (hQ0L qkr.2.2)⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        rcases x with ⟨q1, k1⟩
        rcases y with ⟨q2, k2⟩
        have hval : (q1 : G) * (k1 : G) = q2 * k2 := congrArg Subtype.val hxy
        rcases hqk_unique q1 q2 q1.2 q2.2 k1 k2 k1.2 k2.2 hval with ⟨hq, hk⟩
        have hq' : q1 = q2 := Subtype.ext hq
        have hk' : k1 = k2 := Subtype.ext hk
        subst q2
        subst k2
        rfl
      | inr y =>
        rcases x with ⟨q1, k1⟩
        rcases y with ⟨⟨q2, k2⟩, r⟩
        exact (hcells_disjoint q1 q2 q1.2 q2.2 k1 k2 k1.2 k2.2 r r.2
          (congrArg Subtype.val hxy)).elim
    | inr x =>
      cases y with
      | inl y =>
        rcases x with ⟨⟨q1, k1⟩, r⟩
        rcases y with ⟨q2, k2⟩
        exact (hcells_disjoint q2 q1 q2.2 q1.2 k2 k1 k2.2 k1.2 r r.2
          (congrArg Subtype.val hxy).symm).elim
      | inr y =>
        rcases x with ⟨⟨q1, k1⟩, r1⟩
        rcases y with ⟨⟨q2, k2⟩, r2⟩
        have hval : (q1 : G) * (k1 : G) * t * (r1 : G) =
            q2 * k2 * t * r2 := congrArg Subtype.val hxy
        rcases hqtq_unique q1 q2 q1.2 q2.2 k1 k2 k1.2 k2.2
            r1 r2 r1.2 r2.2 hval with ⟨hq, hk, hr⟩
        have hq' : q1 = q2 := Subtype.ext hq
        have hk' : k1 = k2 := Subtype.ext hk
        have hr' : r1 = r2 := Subtype.ext hr
        subst q2
        subst k2
        subst r2
        rfl
  have hf_surj : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈ q0KUnionQ0KtQ0 Q0 K t := by
      rw [← hcover]
      exact x.2
    rcases hx with ⟨q, k, hq, hk, hx⟩ | ⟨q, k, r, hq, hk, hr, hx⟩
    · refine ⟨Sum.inl (⟨q, hq⟩, ⟨k, hk⟩), ?_⟩
      apply Subtype.ext
      exact hx.symm
    · refine ⟨Sum.inr ((⟨q, hq⟩, ⟨k, hk⟩), ⟨r, hr⟩), ?_⟩
      apply Subtype.ext
      exact hx.symm
  have hcard := Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [Nat.card_sum, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    hQ0card, hKcard] at hcard
  norm_num at hcard ⊢
  exact hcard.symm

private theorem claim_13_prime_dvd_504_ne_two {r : ℕ}
    (hr : Nat.Prime r) (hr_dvd : r ∣ 504) (hr_ne_two : r ≠ 2) :
    r = 3 ∨ r = 7 := by
  have hfac : 504 = 8 * 9 * 7 := by norm_num
  rw [hfac] at hr_dvd
  rcases (Nat.Prime.dvd_mul hr).mp hr_dvd with h89 | h7
  · rcases (Nat.Prime.dvd_mul hr).mp h89 with h8 | h9
    · have h2 : r = 2 := by
        have h8' : r ∣ 2 ^ 3 := by simpa using h8
        exact Nat.prime_eq_prime_of_dvd_pow hr Nat.prime_two h8'
      exact (hr_ne_two h2).elim
    · have h3 : r = 3 := by
        have h9' : r ∣ 3 ^ 2 := by simpa using h9
        exact Nat.prime_eq_prime_of_dvd_pow hr Nat.prime_three h9'
      exact Or.inl h3
  · have h7eq : r = 7 := by
      have h7' : r ∣ 7 ^ 1 := by simpa using h7
      exact Nat.prime_eq_prime_of_dvd_pow hr (by decide) h7'
    exact Or.inr h7eq

private theorem claim_13_fixed_cover_of_card_le_two
    {G Ω : Type*} [Group G] [MulAction G Ω] [Finite Ω]
    {X : Subgroup G} {a b z : Ω}
    (ha : a ∈ fixedPointsOfSubgroup G Ω X)
    (hb : b ∈ fixedPointsOfSubgroup G Ω X)
    (hz : z ∈ fixedPointsOfSubgroup G Ω X)
    (hab : a ≠ b)
    (hcard : Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} ≤ 2) :
    z = a ∨ z = b := by
  classical
  by_contra hcover
  have hza : z ≠ a := fun h => hcover (Or.inl h)
  have hzb : z ≠ b := fun h => hcover (Or.inr h)
  let Fixed : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X}
  let pa : Fixed := ⟨a, ha⟩
  let pb : Fixed := ⟨b, hb⟩
  let pz : Fixed := ⟨z, hz⟩
  have hpa_ne_pb : pa ≠ pb := fun h => hab (congrArg Subtype.val h)
  have hpa_ne_pz : pa ≠ pz := fun h => hza (congrArg Subtype.val h).symm
  have hpb_ne_pz : pb ≠ pz := fun h => hzb (congrArg Subtype.val h).symm
  have hthree_le : 3 ≤ Nat.card Fixed := by
    let f : Fin 3 → Fixed := fun i => if i = 0 then pa else if i = 1 then pb else pz
    have hf_inj : Function.Injective f := by
      intro i j hij
      fin_cases i <;> fin_cases j <;>
        simp [f, hpa_ne_pb, hpa_ne_pb.symm, hpa_ne_pz, hpa_ne_pz.symm,
          hpb_ne_pz, hpb_ne_pz.symm] at hij ⊢
    haveI : Fintype Fixed := Fintype.ofFinite Fixed
    simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hf_inj
  have hcard' : Nat.card Fixed ≤ 2 := by simpa [Fixed] using hcard
  omega

private theorem claim_13_stronglyReal_rightConjugateElem
    {G : Type*} [Group G] {x : G} (g : G) (hx : IsStronglyReal x) :
    IsStronglyReal (rightConjugateElem x g) := by
  rcases hx with ⟨u, v, hu, hv, huv⟩
  refine ⟨rightConjugateElem u g, rightConjugateElem v g,
    isInvolution_rightConjugateElem hu, isInvolution_rightConjugateElem hv, ?_⟩
  calc
    rightConjugateElem x g = rightConjugateElem (u * v) g := by rw [huv]
    _ = rightConjugateElem u g * rightConjugateElem v g := by
      simp [rightConjugateElem, mul_assoc]

private theorem claim_13_centralizer_order_seven_le_D
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
    (k : G) (hkK : k ∈ K) (hkorder : orderOf k = 7) :
    Subgroup.centralizer ({k} : Set G) ≤ D := by
  classical
  let X : Subgroup G := Subgroup.zpowers k
  have hk_ne : k ≠ 1 := by
    intro hk
    simp [hk] at hkorder
  have hX_le_D : X ≤ D :=
    Subgroup.zpowers_le_of_mem (hsec.K_le_D hkK)
  have hfixed_le :
      Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} ≤ 2 := by
    by_contra hnot
    have hthree : 3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} := by
      omega
    have heven := PFchapter1section1.proposition_6_b H D Q X t hsec.hA.A1 hX_le_D hthree
    have hCX_eq : Subgroup.centralizer (X : Set G) =
        Subgroup.centralizer ({k} : Set G) := by
      dsimp [X]
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hbot := PFchapter1section2.proposition_1_a
      H D Q K V W Q0 S Q1 t hsec k hkK hk_ne
    rw [hCX_eq, hbot] at heven
    norm_num at heven
  obtain ⟨base, hHbase⟩ := hsec.hA.A1.point_stabilizer
  let beta : Ω := t⁻¹ • base
  have hbase_ne_beta : base ≠ beta := by
    intro heq
    apply hsec.hA.A1.t_not_mem_H
    have htinv_stab : t⁻¹ ∈ MulAction.stabilizer G base := heq.symm
    have htinv_H : t⁻¹ ∈ H := by simpa [hHbase] using htinv_stab
    simpa using H.inv_mem htinv_H
  have hbase_fixed : base ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    have hxH : x ∈ H := hsec.hA.A1.D_le_H (hX_le_D hx)
    have hxstab : x ∈ MulAction.stabilizer G base := by simpa [hHbase] using hxH
    simpa using hxstab
  have hbeta_fixed : beta ∈ fixedPointsOfSubgroup G Ω X := by
    intro x hx
    have hxD : x ∈ D := hX_le_D hx
    have hxright : x ∈ rightConjugate H t := by
      have hxinf : x ∈ H ⊓ rightConjugate H t := by
        simpa [← hsec.hA.A1.D_eq] using hxD
      exact hxinf.2
    have hright : rightConjugate H t = MulAction.stabilizer G beta := by
      dsimp [beta]
      rw [hHbase]
      exact rightConjugate_stabilizer base t
    have hxstab : x ∈ MulAction.stabilizer G beta := by simpa [hright] using hxright
    simpa using hxstab
  intro c hc
  have hkc : k * c = c * k :=
    (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
  have hkbase : k • base = base :=
    hbase_fixed k (Subgroup.mem_zpowers k)
  have hkbeta : k • beta = beta :=
    hbeta_fixed k (Subgroup.mem_zpowers k)
  have hcbase_fixed : c • base ∈ fixedPointsOfSubgroup G Ω X := by
    have hkfix : k • (c • base) = c • base := by
      calc
        k • (c • base) = (k * c) • base := by rw [mul_smul]
        _ = (c * k) • base := by rw [hkc]
        _ = c • (k • base) := by rw [mul_smul]
        _ = c • base := by rw [hkbase]
    have hle : X ≤ MulAction.stabilizer G (c • base) := by
      dsimp [X]
      rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le]
      intro x hx
      have hxk : x = k := by simpa using hx
      subst x
      exact hkfix
    exact fun x hx => hle hx
  have hcbeta_fixed : c • beta ∈ fixedPointsOfSubgroup G Ω X := by
    have hkfix : k • (c • beta) = c • beta := by
      calc
        k • (c • beta) = (k * c) • beta := by rw [mul_smul]
        _ = (c * k) • beta := by rw [hkc]
        _ = c • (k • beta) := by rw [mul_smul]
        _ = c • beta := by rw [hkbeta]
    have hle : X ≤ MulAction.stabilizer G (c • beta) := by
      dsimp [X]
      rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le]
      intro x hx
      have hxk : x = k := by simpa using hx
      subst x
      exact hkfix
    exact fun x hx => hle hx
  have hcbase_cases := claim_13_fixed_cover_of_card_le_two
    hbase_fixed hbeta_fixed hcbase_fixed hbase_ne_beta hfixed_le
  have hcbeta_cases := claim_13_fixed_cover_of_card_le_two
    hbase_fixed hbeta_fixed hcbeta_fixed hbase_ne_beta hfixed_le
  have hmem_D_of_fixes (g : G) (hgb : g • base = base) (hgβ : g • beta = beta) :
      g ∈ D := by
    rw [hsec.hA.A1.D_eq]
    constructor
    · rw [hHbase]
      exact hgb
    · have hright : rightConjugate H t = MulAction.stabilizer G beta := by
        dsimp [beta]
        rw [hHbase]
        exact rightConjugate_stabilizer base t
      rw [hright]
      exact hgβ
  rcases hcbase_cases with hcbase | hcbase
  · have hcbeta : c • beta = beta := by
      rcases hcbeta_cases with hcbeta | hcbeta
      · exact (hbase_ne_beta ((MulAction.injective c) (hcbase.trans hcbeta.symm))).elim
      · exact hcbeta
    exact hmem_D_of_fixes c hcbase hcbeta
  · have hcbeta : c • beta = base := by
      rcases hcbeta_cases with hcbeta | hcbeta
      · exact hcbeta
      · exact (hbase_ne_beta ((MulAction.injective c) (hcbase.trans hcbeta.symm))).elim
    let d : G := c * t
    have ht_inv : t⁻¹ = t := hsec.hA.A1.involution_t.inv_eq_self
    have htt : t * t = 1 := by
      simpa [pow_two] using hsec.hA.A1.involution_t.sq_eq_one
    have htbase : t • base = beta := by simp [beta, ht_inv]
    have htbeta : t • beta = base := by simp [beta, smul_smul]
    have hdbase : d • base = base := by
      simp only [d, mul_smul, htbase, hcbeta]
    have hdbeta : d • beta = beta := by
      simp only [d, mul_smul, htbeta, hcbase]
    have hdD : d ∈ D := hmem_D_of_fixes d hdbase hdbeta
    have htkt : t * k * t⁻¹ = k⁻¹ := by
      simpa [rightConjugateElem, ht_inv] using (hsec.K_def k).mp hkK |>.2
    have hck : c * k = k * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    have hd_inverts : d * k * d⁻¹ = k⁻¹ := by
      dsimp [d]
      calc
        c * t * k * (c * t)⁻¹ = c * (t * k * t⁻¹) * c⁻¹ := by group
        _ = c * k⁻¹ * c⁻¹ := by rw [htkt]
        _ = (c * k * c⁻¹)⁻¹ := by group
        _ = k⁻¹ := by rw [show c * k * c⁻¹ = k by
          calc c * k * c⁻¹ = k * c * c⁻¹ := by rw [hck]
               _ = k := by simp]
    have hd_inverts_inv : d * k⁻¹ * d⁻¹ = k := by
      calc
        d * k⁻¹ * d⁻¹ = (d * k * d⁻¹)⁻¹ := by group
        _ = k := by rw [hd_inverts]; simp
    have hd2_fixes : d ^ 2 * k * (d ^ 2)⁻¹ = k := by
      calc
        d ^ 2 * k * (d ^ 2)⁻¹ = d * (d * k * d⁻¹) * d⁻¹ := by
          simp only [pow_two]
          group
        _ = d * k⁻¹ * d⁻¹ := by rw [hd_inverts]
        _ = k := hd_inverts_inv
    have hd2_comm : Commute (d ^ 2) k := by
      apply (commute_iff_eq _ _).2
      have h := congrArg (fun z : G => z * d ^ 2) hd2_fixes
      simpa [mul_assoc] using h
    have hd_order_odd : Odd (orderOf d) := by
      have hdDorder : orderOf (⟨d, hdD⟩ : D) ∣ Nat.card D := orderOf_dvd_natCard _
      have : orderOf d ∣ Nat.card D := by simpa using hdDorder
      exact Odd.of_dvd_nat hsec.hA.A1.D_odd this
    rcases hd_order_odd with ⟨n, hn⟩
    have hdpow : d ^ (2 * n + 1) = 1 := by
      rw [← hn]
      exact pow_orderOf_eq_one d
    have heven_comm : Commute (d ^ (2 * n)) k := by
      simpa [← pow_mul] using hd2_comm.pow_left n
    have hd_eq : d = (d ^ (2 * n))⁻¹ := by
      apply mul_left_cancel (a := d ^ (2 * n))
      simpa [pow_succ, mul_assoc] using hdpow
    have hd_comm : Commute d k := by
      rw [hd_eq]
      exact heven_comm.inv_left
    have hk_inv : k = k⁻¹ := by
      calc
        k = d * k * d⁻¹ := by
          rw [hd_comm.eq]
          simp
        _ = k⁻¹ := hd_inverts
    have hk2 : k ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [hk_inv]
      exact mul_inv_cancel k
    have hk_dvd_two : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
    rw [hkorder] at hk_dvd_two
    norm_num at hk_dvd_two

private def claim_13_invariantSubgroupAut
    {M : Type*} [Group M] (phi : MulAut M) (X : Subgroup M)
    (hX : forall x : M, x ∈ X ↔ phi x ∈ X) : MulAut X where
  toFun x := ⟨phi x, (hX x).mp x.2⟩
  invFun x := ⟨phi.symm x, (hX (phi.symm x)).mpr (by simp)⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_mul' x y := by ext; simp

private theorem claim_13_exists_prime_order_invertingSet
    {M : Type*} [Group M] [Finite M] (t : M) (X : Subgroup M)
    (ht : IsInvolution t) (hXodd : Odd (Nat.card X))
    (hXnorm : t ∈ Subgroup.normalizer (X : Set M))
    {r : Nat} (hr : Nat.Prime r)
    (hrdvd :
      r ∣ Nat.card {x : M //
        x ∈ ({y : M | y ∈ X ∧ rightConjugateElem y t = y⁻¹} : Set M)}) :
    ∃ x : M, x ∈ X ∧ rightConjugateElem x t = x⁻¹ ∧ orderOf x = r := by
  classical
  let phiM : MulAut M := MulAut.conj t
  have hphiM_X : ∀ x : M, x ∈ X ↔ phiM x ∈ X := by
    intro x
    simpa [phiM, MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hXnorm x)
  let phi : MulAut X := claim_13_invariantSubgroupAut phiM X hphiM_X
  have htt : t * t = 1 := by
    simpa [pow_two] using ht.sq_eq_one
  have hphi_sq : phi ^ 2 = 1 := by
    ext x
    simp [phi, claim_13_invariantSubgroupAut, phiM, pow_two,
      MulAut.conj_apply, ht.inv_eq_self, mul_assoc]
    rw [← mul_assoc, htt, one_mul, mul_one]
  have hphi_order : orderOf phi ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hphi_sq
  let A : Subgroup (MulAut X) := Subgroup.zpowers phi
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA_pgroup : IsPGroup 2 A := by
    have hcard_dvd : Nat.card A ∣ 2 := by
      simpa [A, Nat.card_zpowers] using hphi_order
    rcases Nat.prime_two.eq_one_or_self_of_dvd (Nat.card A) hcard_dvd with
      hcard_one | hcard_two
    · exact IsPGroup.of_card (p := 2) (G := A) (n := 0) (by simp [hcard_one])
    · exact IsPGroup.of_card (p := 2) (G := A) (n := 1) (by simp [hcard_two])
  letI : Fact (IsPGroup 2 A) := ⟨hA_pgroup⟩
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  have hcoprime : Nat.Coprime 2 (Nat.card X) :=
    hXodd.coprime_two_left
  obtain ⟨P, hPinv⟩ :=
    exists_invariant_sylow (G := X) (A := A) (p := 2) (q := r) hcoprime
  let Y : Subgroup M := X ⊓ Subgroup.centralizer ({t} : Set M)
  let J : Set M :=
    {y : M | y ∈ X ∧ rightConjugateElem y t = y⁻¹}
  have hfactor :
      Nat.card X = Nat.card Y * Nat.card J := by
    simpa [Y, J] using (PFchapter1section1.lemma_a t X ht hXodd hXnorm).2.2
  have hJ_dvd_X : Nat.card J ∣ Nat.card X := by
    refine ⟨Nat.card Y, ?_⟩
    simpa [Nat.mul_comm] using hfactor
  have hr_dvd_J : r ∣ Nat.card J := by
    change r ∣ Nat.card {x : M //
      x ∈ ({y : M | y ∈ X ∧ rightConjugateElem y t = y⁻¹} : Set M)}
    exact hrdvd
  have hr_dvd_X : r ∣ Nat.card X := by
    exact hr_dvd_J.trans hJ_dvd_X
  have hr_ne_two : r ≠ 2 := by
    intro hr2
    exact hXodd.not_two_dvd_nat (by simpa [hr2] using hr_dvd_X)
  let YX : Subgroup X := Y.subgroupOf X
  have hY_le_X : Y ≤ X := inf_le_left
  have hYXcard : Nat.card YX = Nat.card Y := by
    simpa [YX] using natCard_subgroupOf_eq Y X hY_le_X
  have hYXindex : YX.index = Nat.card J := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Y))
    calc
      YX.index * Nat.card Y = YX.index * Nat.card YX := by rw [hYXcard]
      _ = Nat.card X := Subgroup.index_mul_card (H := YX)
      _ = Nat.card Y * Nat.card J := hfactor
      _ = Nat.card J * Nat.card Y := by rw [Nat.mul_comm]
  have hP_not_le_YX : ¬ (P : Subgroup X) ≤ YX := by
    intro hP_le
    have hr_dvd_YXindex : r ∣ YX.index := by
      rw [hYXindex]
      exact hr_dvd_J
    have hindex_dvd : YX.index ∣ (P : Subgroup X).index :=
      Subgroup.index_dvd_of_le hP_le
    exact P.not_dvd_index (hr_dvd_YXindex.trans hindex_dvd)
  let PG : Subgroup M := (P : Subgroup X).map X.subtype
  have hPG_le_X : PG ≤ X := by
    simpa [PG] using
      (Subgroup.map_subtype_le (H := X) (K := (P : Subgroup X)))
  have hPG_not_le_Ct : ¬ PG ≤ Subgroup.centralizer ({t} : Set M) := by
    intro hPG_le
    apply hP_not_le_YX
    intro x hxP
    change (x : M) ∈ Y
    refine ⟨x.2, hPG_le ?_⟩
    exact ⟨x, hxP, rfl⟩
  have ht_norm_PG : t ∈ Subgroup.normalizer (PG : Set M) := by
    rw [Subgroup.mem_normalizer_iff]
    have hforward :
        ∀ x : M, x ∈ PG → t * x * t⁻¹ ∈ PG := by
      intro x hx
      rcases hx with ⟨xX, hxP, rfl⟩
      let a : A := ⟨phi, Subgroup.mem_zpowers phi⟩
      have hmem : phi xX ∈ (P : Subgroup X) := by
        have hmem' := (hPinv.invariant a xX).mp hxP
        change phi xX ∈ (P : Subgroup X) at hmem'
        exact hmem'
      refine ⟨phi xX, hmem, ?_⟩
      rfl
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (t * x * t⁻¹) hx
      have hconj_twice : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rwa [hconj_twice] at hback
  obtain ⟨z, hzPG, hznotC⟩ := SetLike.not_le_iff_exists.mp hPG_not_le_Ct
  have hPGp : IsPGroup r PG :=
    IsPGroup.map (p := r) (H := (P : Subgroup X)) P.isPGroup' X.subtype
  have hPGodd : Odd (Nat.card PG) := by
    rcases (IsPGroup.iff_card.mp hPGp) with ⟨n, hn⟩
    rw [hn]
    exact (hr.odd_of_ne_two hr_ne_two).pow
  let YP : Subgroup M := PG ⊓ Subgroup.centralizer ({t} : Set M)
  let ZP : Set M :=
    {x : M | x ∈ PG ∧ rightConjugateElem x t = x⁻¹}
  have hbij :
      Set.BijOn
        (fun p : YP × ZP => (p.1 : M) * (p.2 : M))
        Set.univ (PG : Set M) := by
    simpa [YP, ZP] using
      (PFchapter1section1.lemma_a t PG ht hPGodd ht_norm_PG).1
  rcases hbij.2.2 hzPG with ⟨yz, _hyz, hyz_eq⟩
  let z0 : M := yz.2
  have hz0PG : z0 ∈ PG := yz.2.property.1
  have hz0inv : rightConjugateElem z0 t = z0⁻¹ := yz.2.property.2
  have hz0_ne : z0 ≠ 1 := by
    intro hz0
    apply hznotC
    have hz_eq : z = (yz.1 : M) := by
      simpa [z0, hz0] using hyz_eq.symm
    rw [hz_eq]
    exact yz.1.property.2
  let zPG : PG := ⟨z0, hz0PG⟩
  rcases (IsPGroup.iff_orderOf.mp hPGp) zPG with ⟨k, hk⟩
  have hz0_order : orderOf z0 = r ^ k := by
    simpa [zPG] using hk
  have hk_ne : k ≠ 0 := by
    intro hk0
    apply hz0_ne
    apply orderOf_eq_one_iff.mp
    simp [hz0_order, hk0]
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk_ne
  have hr_dvd_order : r ∣ orderOf z0 := by
    rw [hz0_order, pow_succ]
    exact dvd_mul_left r (r ^ l)
  let x : M := z0 ^ (orderOf z0 / r)
  refine ⟨x, hPG_le_X (PG.pow_mem hz0PG _), ?_, ?_⟩
  · have hx_conj : (MulAut.conj t⁻¹) x = x⁻¹ := by
      rw [show (MulAut.conj t⁻¹) x =
          (MulAut.conj t⁻¹ z0) ^ (orderOf z0 / r) by
        exact map_pow (MulAut.conj t⁻¹) z0 _]
      have hz0inv' : (MulAut.conj t⁻¹) z0 = z0⁻¹ := by
        simpa [MulAut.conj_apply, rightConjugateElem] using hz0inv
      rw [hz0inv']
      simp [x]
    simpa [MulAut.conj_apply, rightConjugateElem] using hx_conj
  · exact orderOf_pow_orderOf_div (orderOf_pos z0).ne' hr_dvd_order

private theorem claim_13_strongly_real_of_inverted_by_involution
    {G : Type*} [Group G] {x s : G}
    (hs : IsInvolution s) (hxinv : rightConjugateElem x s = x⁻¹)
    (hx2 : x ^ 2 ≠ 1) :
    IsStronglyReal x := by
  have hs_inv : s⁻¹ = s := by
    have hs_mul : s * s = 1 := by
      simpa [pow_two] using hs.sq_eq_one
    calc
      s⁻¹ = s⁻¹ * 1 := by simp
      _ = s⁻¹ * (s * s) := by rw [hs_mul]
      _ = s := by simp
  have hs_mul : s * s = 1 := by
    simpa [pow_two] using hs.sq_eq_one
  have hconj : s * x * s = x⁻¹ := by
    simpa [rightConjugateElem, hs_inv, mul_assoc] using hxinv
  have hxs_sq : (x * s) ^ 2 = 1 := by
    calc
      (x * s) ^ 2 = x * (s * x * s) := by
        simp [pow_two, mul_assoc]
      _ = 1 := by
        rw [hconj]
        simp
  have hxs_ne : x * s ≠ 1 := by
    intro hxs
    have hx_eq_s : x = s := by
      calc
        x = x * 1 := by simp
        _ = x * (s * s) := by rw [hs_mul]
        _ = (x * s) * s := by simp [mul_assoc]
        _ = s := by rw [hxs]; simp
    exact hx2 (by simpa [hx_eq_s] using hs.sq_eq_one)
  refine ⟨x * s, s, ⟨hxs_ne, hxs_sq⟩, hs, ?_⟩
  simp [hs_mul, mul_assoc]

private theorem claim_13_invertingSet_mem_strongly_real
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Z1 : Subgroup G) (t s x : G) (p : ℕ)
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
    (hxJ : x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)) (hx2 : x ^ 2 ≠ 1) :
    IsStronglyReal x := by
  exact
    claim_13_strongly_real_of_inverted_by_involution
      hch.section3.s_involution hxJ.2 hx2


private theorem claim_13_card_three_power_of_prime_divisors
    {G : Type*} [Group G] [Finite G] (Z1 : Subgroup G) (s : G)
    (hprime :
      ∀ r : ℕ, Nat.Prime r →
        r ∣ Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} → r = 3) :
    ∃ n : ℕ, Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} = 3 ^ n := by
  have hJ_nonempty : Nonempty {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} := by
    refine ⟨⟨1, ?_⟩⟩
    exact ⟨by simp, by simp [rightConjugateElem]⟩
  haveI : Nonempty {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} := hJ_nonempty
  have hJ_pos : Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} ≠ 0 :=
    (Nat.card_pos (α := {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)})).ne'
  refine
    ⟨(Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)}).primeFactorsList.length, ?_⟩
  exact
    Nat.eq_prime_pow_of_unique_prime_dvd hJ_pos
      (by
        intro r hr hrdvd
        exact hprime r hr hrdvd)

/- Claim (13): a prime divisor of the inverting set yields a strongly-real
prime-order element in the generated `PSL(2,8)` copy, so the possible odd
prime divisors are `3` and `7`. -/
private theorem chapter2_claim13_strong_real_psl28_prime_divisor_three_or_seven
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Z1 : Subgroup G) (t s : G) (p : ℕ)
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
    (hp3 : p = 3) (hst : orderOf (s * t) = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t)) :
    ∀ r : ℕ, Nat.Prime r →
      r ∣ Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} → r = 3 ∨ r = 7 := by
  classical
  intro r hr hrdvd
  let X : Subgroup G := Subgroup.centralizer (Z1 : Set G)
  have hCZ1_eq : X = Subgroup.centralizer ({s * t} : Set G) := by
    dsimp [X]
    rw [hZ1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hst_sq_ne : (s * t) ^ 2 ≠ 1 := by
    intro hsq
    have hdvd : orderOf (s * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hst] at hdvd
    norm_num at hdvd
  have hst_strong : IsStronglyReal (s * t) :=
    ⟨s, t, hch.section3.s_involution,
      hch.section3.section2.hA.A1.involution_t, rfl⟩
  have hXodd : Odd (Nat.card X) := by
    rw [hCZ1_eq]
    exact
      (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
        (s * t) hst_strong hst_sq_ne).2
  have hsI := hch.section3.s_involution
  have hs_inv : s⁻¹ = s := hsI.inv_eq_self
  have hss : s * s = 1 := by
    simpa [pow_two] using hsI.sq_eq_one
  have hgen_conj : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [hs_inv]
    calc
      s * (s * t) * s = t * s := by rw [← mul_assoc, hss]; simp
      _ = (s * t)⁻¹ := by
        simp [hs_inv, hch.section3.section2.hA.A1.involution_t.inv_eq_self]
  have hs_norm_X : s ∈ Subgroup.normalizer (X : Set G) := by
    rw [hCZ1_eq, Subgroup.mem_normalizer_iff]
    have hforward :
        ∀ x : G, x ∈ Subgroup.centralizer ({s * t} : Set G) →
          s * x * s⁻¹ ∈ Subgroup.centralizer ({s * t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hy_eq : y = s * t := by simpa using hy
      subst y
      have hcomm : Commute (s * t) x := hx (s * t) (by simp)
      have hcomm_inv : Commute ((s * t)⁻¹) (s * x * s⁻¹) := by
        rw [← hgen_conj]
        exact hcomm.conj s
      exact (Commute.inv_left_iff.mp hcomm_inv).eq
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (s * x * s⁻¹) hx
      have hconj_twice : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hs_inv]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by
            simp only [mul_assoc]
          _ = x := by rw [hss]; simp
      rwa [hconj_twice] at hback
  obtain ⟨x, hxX, hxinv, hxorder⟩ :=
    claim_13_exists_prime_order_invertingSet s X hsI hXodd hs_norm_X hr
      (by simpa [X] using hrdvd)
  have hr_dvd_X : r ∣ Nat.card X := by
    rw [← hxorder]
    simpa using orderOf_dvd_natCard (⟨x, hxX⟩ : X)
  have hr_ne_two : r ≠ 2 := by
    intro hr2
    exact hXodd.not_two_dvd_nat (by simpa [hr2] using hr_dvd_X)
  have hx2 : x ^ 2 ≠ 1 := by
    intro hx2
    have hdvd : r ∣ 2 := by
      rw [← hxorder]
      exact orderOf_dvd_of_pow_eq_one hx2
    exact hr_ne_two (Nat.dvd_prime Nat.prime_two |>.mp hdvd |>.resolve_left hr.ne_one)
  have hxstrong : IsStronglyReal x :=
    claim_13_invertingSet_mem_strongly_real
      H D Q K V W Q0 S Q1 P Z1 t s x p hch ⟨hxX, hxinv⟩ hx2
  rcases
      (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
        x hxstrong hx2).1 with ⟨u, g, huQ0, _hu_ne, hxug⟩
  let L : Subgroup G := psl2GeneratedSubgroup Q0 K t
  let y : G := u * t
  have hyL : y ∈ L := by
    exact L.mul_mem
      (Subgroup.subset_closure (Or.inl (Or.inl huQ0)))
      (Subgroup.subset_closure (Or.inr rfl))
  have horder_conj : orderOf (rightConjugateElem x g) = orderOf x := by
    simpa [rightConjugateElem, MulAut.conj_symm_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj g).symm x)
  have hyorder : orderOf y = r := by
    change orderOf (u * t) = r
    rw [← hxug, horder_conj, hxorder]
  have hQ0card : Nat.card Q0 = 8 := by
    have hq := (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
    norm_num [hp3] at hq ⊢
    exact hq
  have hKcard : Nat.card K = 7 := by
    have hk := claim_1_K_card_eq_mersenne
      H D Q K V W Q0 S Q1 P t s p hch
    norm_num [hp3] at hk ⊢
    exact hk
  have hcover := lemma_4_generated_subgroup_eq_obligation
    H D Q K V W Q0 S Q1 t s hch.section3 hst
  have hLcard : Nat.card L = 504 :=
    claim_13_generated_subgroup_card H D Q K Q0 t
      hch.section3.section2.Q0_le_Q hch.section3.section2.K_le_D
      hch.section3.section2.hA.A1.Q_le_H hch.section3.section2.hA.A1.D_le_H
      hch.section3.section2.hA.A1.Q_disjoint_D
      hch.section3.section2.hA.A1.t_not_mem_H hch.section3.section2.hA.A1.D_eq
      hcover hQ0card hKcard
  have hr_dvd_L : r ∣ Nat.card L := by
    rw [← hyorder]
    simpa using orderOf_dvd_natCard (⟨y, hyL⟩ : L)
  exact claim_13_prime_dvd_504_ne_two hr (by simpa [hLcard] using hr_dvd_L) hr_ne_two

/- Claim (13): the order-seven branch in the inverting set is impossible after
transporting the `PSL(2,8)` centralizer information back to the ambient
centralizer/fixed-point data. -/
private theorem chapter2_claim13_psl28_excludes_seven_in_invertingSet
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Z1 : Subgroup G) (t s : G) (p : ℕ)
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
    (hp3 : p = 3) (hst : orderOf (s * t) = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t)) :
    ¬ 7 ∣ Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} := by
  classical
  intro hseven
  let X : Subgroup G := Subgroup.centralizer (Z1 : Set G)
  have hCZ1_eq : X = Subgroup.centralizer ({s * t} : Set G) := by
    dsimp [X]
    rw [hZ1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hst_sq_ne : (s * t) ^ 2 ≠ 1 := by
    intro hsq
    have hdvd : orderOf (s * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rw [hst] at hdvd
    norm_num at hdvd
  have hst_strong : IsStronglyReal (s * t) :=
    ⟨s, t, hch.section3.s_involution,
      hch.section3.section2.hA.A1.involution_t, rfl⟩
  have hXodd : Odd (Nat.card X) := by
    rw [hCZ1_eq]
    exact
      (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
        (s * t) hst_strong hst_sq_ne).2
  have hsI := hch.section3.s_involution
  have hs_inv : s⁻¹ = s := hsI.inv_eq_self
  have hss : s * s = 1 := by simpa [pow_two] using hsI.sq_eq_one
  have hgen_conj : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
    rw [hs_inv]
    calc
      s * (s * t) * s = t * s := by rw [← mul_assoc, hss]; simp
      _ = (s * t)⁻¹ := by
        simp [hs_inv, hch.section3.section2.hA.A1.involution_t.inv_eq_self]
  have hs_norm_X : s ∈ Subgroup.normalizer (X : Set G) := by
    rw [hCZ1_eq, Subgroup.mem_normalizer_iff]
    have hforward :
        ∀ x : G, x ∈ Subgroup.centralizer ({s * t} : Set G) →
          s * x * s⁻¹ ∈ Subgroup.centralizer ({s * t} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      have hy_eq : y = s * t := by simpa using hy
      subst y
      have hcomm : Commute (s * t) x := hx (s * t) (by simp)
      have hcomm_inv : Commute ((s * t)⁻¹) (s * x * s⁻¹) := by
        rw [← hgen_conj]
        exact hcomm.conj s
      exact (Commute.inv_left_iff.mp hcomm_inv).eq
    intro x
    constructor
    · exact hforward x
    · intro hx
      have hback := hforward (s * x * s⁻¹) hx
      have hconj_twice : s * (s * x * s⁻¹) * s⁻¹ = x := by
        rw [hs_inv]
        calc
          s * (s * x * s) * s = (s * s) * x * (s * s) := by simp only [mul_assoc]
          _ = x := by rw [hss]; simp
      rwa [hconj_twice] at hback
  obtain ⟨x, hxX, hxinv, hxorder⟩ :=
    claim_13_exists_prime_order_invertingSet s X hsI hXodd hs_norm_X
      Nat.prime_seven (by simpa [X] using hseven)
  have hx2 : x ^ 2 ≠ 1 := by
    intro hx2
    have hdvd : 7 ∣ 2 := by
      rw [← hxorder]
      exact orderOf_dvd_of_pow_eq_one hx2
    norm_num at hdvd
  have hxstrong : IsStronglyReal x :=
    claim_13_invertingSet_mem_strongly_real
      H D Q K V W Q0 S Q1 P Z1 t s x p hch ⟨hxX, hxinv⟩ hx2
  rcases
      (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
        x hxstrong hx2).1 with ⟨u, g, huQ0, _hu_ne, hxug⟩
  let L : Subgroup G := psl2GeneratedSubgroup Q0 K t
  let y : G := u * t
  have hyL : y ∈ L :=
    L.mul_mem (Subgroup.subset_closure (Or.inl (Or.inl huQ0)))
      (Subgroup.subset_closure (Or.inr rfl))
  have horder_conj_x : orderOf (rightConjugateElem x g) = orderOf x := by
    simpa [rightConjugateElem, MulAut.conj_symm_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj g).symm x)
  have hyorder : orderOf y = 7 := by
    change orderOf (u * t) = 7
    rw [← hxug, horder_conj_x, hxorder]
  have hQ0card : Nat.card Q0 = 8 := by
    have hq := (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.1
    norm_num [hp3] at hq ⊢
    exact hq
  have hKcard : Nat.card K = 7 := by
    have hk := claim_1_K_card_eq_mersenne H D Q K V W Q0 S Q1 P t s p hch
    norm_num [hp3] at hk ⊢
    exact hk
  have hcover := lemma_4_generated_subgroup_eq_obligation
    H D Q K V W Q0 S Q1 t s hch.section3 hst
  have hLcard : Nat.card L = 504 :=
    claim_13_generated_subgroup_card H D Q K Q0 t
      hch.section3.section2.Q0_le_Q hch.section3.section2.K_le_D
      hch.section3.section2.hA.A1.Q_le_H hch.section3.section2.hA.A1.D_le_H
      hch.section3.section2.hA.A1.Q_disjoint_D
      hch.section3.section2.hA.A1.t_not_mem_H hch.section3.section2.hA.A1.D_eq
      hcover hQ0card hKcard
  let KL : Subgroup L := K.subgroupOf L
  have hKLcard : Nat.card KL = 7 := by
    simpa [KL, natCard_subgroupOf_eq K L
      (show K ≤ L from fun _ hk => Subgroup.subset_closure (Or.inl (Or.inr hk)))]
      using hKcard
  letI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  let K7 : Sylow 7 L := Sylow.ofCard KL (by
    have hfac : (Nat.card L).factorization 7 = 1 := by
      rw [hLcard]
      have hpos : 0 < (Nat.factorization 504) 7 :=
        Nat.prime_seven.factorization_pos_of_dvd (by norm_num) (by norm_num)
      have hlt : (Nat.factorization 504) 7 < 2 := by
        by_contra hnot
        have htwo : 2 ≤ (Nat.factorization 504) 7 := by omega
        have h49 : 7 ^ 2 ∣ 504 :=
          (Nat.prime_seven.pow_dvd_iff_le_factorization (by norm_num)).2 htwo
        norm_num at h49
      omega
    rw [hKLcard, hfac, pow_one])
  let yL : L := ⟨y, hyL⟩
  let Y : Subgroup L := Subgroup.zpowers yL
  have hYp : IsPGroup 7 Y := by
    rw [IsPGroup.iff_card, Nat.card_zpowers]
    refine ⟨1, ?_⟩
    simpa [yL] using hyorder
  obtain ⟨Y7, hYle⟩ := IsPGroup.exists_le_sylow hYp
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq L Y7 K7
  let kL : L := (MulAut.conj a) yL
  have hkKL : kL ∈ KL := by
    have hyY7 : yL ∈ (Y7 : Subgroup L) := hYle (Subgroup.mem_zpowers yL)
    have hkK7 : kL ∈ (K7 : Subgroup L) := by
      rw [← ha, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul yL (MulAut.conj a) (Y7 : Subgroup L) hyY7
    simpa [K7] using hkK7
  let k : G := kL
  have hkK : k ∈ K := hkKL
  let b : G := g * (a : G)⁻¹
  have hk_eq : rightConjugateElem x b = k := by
    calc
      rightConjugateElem x b =
          rightConjugateElem (rightConjugateElem x g) (a : G)⁻¹ := by
            rw [rightConjugateElem_comp]
      _ = rightConjugateElem y (a : G)⁻¹ := by rw [hxug]
      _ = k := by simp [rightConjugateElem, k, kL, yL]
  have hkorder : orderOf k = 7 := by
    rw [← hk_eq]
    simpa [rightConjugateElem, MulAut.conj_symm_apply] using
      (MulEquiv.orderOf_eq (MulAut.conj b).symm x).trans hxorder
  let z : G := rightConjugateElem (s * t) b
  have hzorder : orderOf z = 3 := by
    dsimp [z]
    calc
      orderOf (rightConjugateElem (s * t) b) = orderOf (s * t) := by
        simpa [rightConjugateElem, MulAut.conj_symm_apply] using
          (MulEquiv.orderOf_eq (MulAut.conj b).symm (s * t))
      _ = 3 := hst
  have hzstrong : IsStronglyReal z :=
    claim_13_stronglyReal_rightConjugateElem b hst_strong
  have hx_cent_st : Commute x (s * t) := by
    have hstZ1 : s * t ∈ Z1 := by rw [hZ1]; exact Subgroup.mem_zpowers _
    exact ((Subgroup.mem_centralizer_iff.mp hxX) (s * t) hstZ1).symm
  have hkz : Commute k z := by
    have hmap := hx_cent_st.map (MulAut.conj b⁻¹).toMonoidHom
    rw [← hk_eq]
    simpa [z, rightConjugateElem, MulAut.conj_apply] using hmap
  have hzD : z ∈ D :=
    claim_13_centralizer_order_seven_le_D H D Q K V W Q0 S Q1 t
      hch.section3.section2 k hkK hkorder
      (Subgroup.mem_centralizer_singleton_iff.mpr hkz.eq.symm)
  have htI := hch.section3.section2.hA.A1.involution_t
  have ht_inv : t⁻¹ = t := htI.inv_eq_self
  have htt : t * t = 1 := by simpa [pow_two] using htI.sq_eq_one
  have ht_norm_D : t ∈ Subgroup.normalizer (D : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    have hforward : ∀ d : G, d ∈ D → t * d * t⁻¹ ∈ D := by
      intro d hd
      have hdinf : d ∈ H ⊓ rightConjugate H t := by
        simpa [← hch.section3.section2.hA.A1.D_eq] using hd
      rw [hch.section3.section2.hA.A1.D_eq]
      constructor
      · have hdright := hdinf.2
        change d ∈ rightConjugate H t at hdright
        rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map] at hdright
        rcases hdright with ⟨h, hhH, hhd⟩
        change t * d * t⁻¹ ∈ H
        have hd_eq : t * h * t = d := by
          simpa [MulAut.conj_apply, ht_inv, mul_assoc] using hhd
        have hback : t * d * t = h := by
          rw [← hd_eq]
          calc
            t * (t * h * t) * t = (t * t) * h * (t * t) := by group
            _ = h := by rw [htt]; simp
        simpa [ht_inv, hback] using hhH
      · change t * d * t⁻¹ ∈ rightConjugate H t
        rw [rightConjugate, Subgroup.conjBy, Subgroup.mem_map]
        refine ⟨d, hdinf.1, ?_⟩
        simp [MulAut.conj_apply, ht_inv]
    intro d
    constructor
    · exact hforward d
    · intro hd
      have hback := hforward (t * d * t⁻¹) hd
      have htwice : t * (t * d * t⁻¹) * t⁻¹ = d := by
        rw [ht_inv]
        calc
          t * (t * d * t) * t = (t * t) * d * (t * t) := by group
          _ = d := by rw [htt]; simp
      exact htwice ▸ hback
  have hbij :=
    (PFchapter1section1.lemma_a t D htI
      hch.section3.section2.hA.A1.D_odd ht_norm_D).1
  rcases hbij.2.2 hzD with ⟨vk, _hvk_univ, hvk_eq⟩
  let v : G := vk.1
  let k1 : G := vk.2
  have hvV : v ∈ V := by
    rw [hch.section3.section2.V_eq]
    exact vk.1.property
  have hk1K : k1 ∈ K :=
    (hch.section3.section2.K_def k1).mpr vk.2.property
  have hz_eq : z = v * k1 := by simpa [v, k1] using hvk_eq.symm
  haveI : IsCyclic K := isCyclic_of_prime_card hKcard
  have hkgen : Subgroup.zpowers k = K := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem hkK)
    rw [Nat.card_zpowers, hkorder, hKcard]
  have hzCK : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [← hkgen, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hkz.eq.symm
  have hk1CK : k1 ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    let k1K : K := ⟨k1, hk1K⟩
    let qK : K := ⟨q, hq⟩
    exact congrArg Subtype.val (mul_comm' qK k1K)
  have hvCK : v ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hzq : q * z = z * q := (Subgroup.mem_centralizer_iff.mp hzCK) q hq
    have hkq : q * k1 = k1 * q := (Subgroup.mem_centralizer_iff.mp hk1CK) q hq
    rw [hz_eq] at hzq
    apply mul_right_cancel (b := k1)
    calc
      (q * v) * k1 = q * (v * k1) := by group
      _ = (v * k1) * q := hzq
      _ = v * (q * k1) := by rw [hkq]; group
      _ = (v * q) * k1 := by group
  have hvW : v ∈ W := by
    rw [hch.section3.section2.W_eq]
    exact ⟨hvV, hvCK⟩
  have hKW : Disjoint K W := by
    rw [disjoint_iff]
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    have haV : a ∈ V := hch.section3.section2.W_le_V ha.2
    have haCt : a ∈ Subgroup.centralizer ({t} : Set G) := by
      have : a ∈ peterfalviV D t := by simpa [← hch.section3.section2.V_eq] using haV
      exact this.2
    have hat_fixed : rightConjugateElem a t = a := by
      have hcomm : t * a = a * t :=
        (Subgroup.mem_centralizer_singleton_iff.mp haCt).symm
      calc
        rightConjugateElem a t = t * a * t := by rw [rightConjugateElem, ht_inv]
        _ = a * (t * t) := by rw [hcomm]; group
        _ = a := by rw [htt]; simp
    have hat_inv : rightConjugateElem a t = a⁻¹ :=
      (hch.section3.section2.K_def a).mp ha.1 |>.2
    have ha_inv : a = a⁻¹ := hat_fixed.symm.trans hat_inv
    have ha2 : a ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 2 [ha_inv]
      exact mul_inv_cancel a
    by_cases ha1 : a = 1
    · simp [ha1]
    · have haorder : orderOf a = 2 := orderOf_eq_prime ha2 ha1
      have htwoD : 2 ∣ Nat.card D := by
        rw [← haorder]
        simpa using orderOf_dvd_natCard
          (⟨a, hch.section3.section2.K_le_D ha.1⟩ : D)
      exact (hch.section3.section2.hA.A1.D_odd.not_two_dvd_nat htwoD).elim
  have hvk_comm : Commute v k1 := by
    have := (Subgroup.mem_centralizer_iff.mp hvCK) k1 hk1K
    exact this.symm
  have hzpow : z ^ 3 = 1 := by simpa [hzorder] using pow_orderOf_eq_one z
  have hvkpow : v ^ 3 * k1 ^ 3 = 1 := by
    rw [← hvk_comm.mul_pow]
    simpa [← hz_eq] using hzpow
  have hv3_eq : v ^ 3 = (k1 ^ 3)⁻¹ := by
    apply mul_right_cancel (b := k1 ^ 3)
    rw [hvkpow]
    simp
  have hv3_bot : v ^ 3 ∈ (⊥ : Subgroup G) := by
    have hv3K : v ^ 3 ∈ K := by
      rw [hv3_eq]
      exact K.inv_mem (K.pow_mem hk1K 3)
    have hv3W : v ^ 3 ∈ W := W.pow_mem hvW 3
    have hv3inf : v ^ 3 ∈ K ⊓ W := ⟨hv3K, hv3W⟩
    rw [← hKW.eq_bot]
    exact hv3inf
  have hv3_one : v ^ 3 = 1 := by simpa using hv3_bot
  have hk13 : k1 ^ 3 = 1 := by
    rw [← hvkpow, hv3_one]
    simp
  have hk1_order_dvd3 : orderOf (⟨k1, hk1K⟩ : K) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    exact hk13
  have hk1_order_dvd7 : orderOf (⟨k1, hk1K⟩ : K) ∣ 7 := by
    simpa [hKcard] using orderOf_dvd_natCard (⟨k1, hk1K⟩ : K)
  have hk1_order_one : orderOf (⟨k1, hk1K⟩ : K) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hk1_order_dvd3 with h1 | h3
    · exact h1
    · rcases (Nat.dvd_prime Nat.prime_seven).mp hk1_order_dvd7 with h1 | h7
      · exact h1
      · omega
  have hk1_one : k1 = 1 := by
    simpa using congrArg Subtype.val (orderOf_eq_one_iff.mp hk1_order_one)
  have hzW : z ∈ W := by simpa [hz_eq, hk1_one] using hvW
  have hzCt : z ∈ Subgroup.centralizer ({t} : Set G) := by
    have hzV := hch.section3.section2.W_le_V hzW
    have : z ∈ peterfalviV D t := by simpa [← hch.section3.section2.V_eq] using hzV
    exact this.2
  have htCz : t ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_singleton_iff.mp hzCt).symm
  have hz2 : z ^ 2 ≠ 1 := by
    intro hz2
    have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    rw [hzorder] at hdvd
    norm_num at hdvd
  have hCzodd :=
    (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
      z hzstrong hz2).2
  have htwoCz : 2 ∣ Nat.card (Subgroup.centralizer ({z} : Set G)) := by
    have htorder : orderOf t = 2 := orderOf_eq_prime htI.sq_eq_one htI.ne_one
    rw [← htorder]
    simpa using orderOf_dvd_natCard
      (⟨t, htCz⟩ : Subgroup.centralizer ({z} : Set G))
  exact hCzodd.not_two_dvd_nat htwoCz


private theorem claim_13_invertingSet_three_power_from_psl28_exclusion
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Z1 : Subgroup G) (t s : G) (p : ℕ)
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
    (hp3 : p = 3) (hst : orderOf (s * t) = 3)
    (hZ1 : Z1 = Subgroup.zpowers (s * t)) :
    ∃ n : ℕ, Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} = 3 ^ n := by
  exact
    claim_13_card_three_power_of_prime_divisors Z1 s
      (by
        intro r hrprime hrdvd
        rcases
          chapter2_claim13_strong_real_psl28_prime_divisor_three_or_seven
            H D Q K V W Q0 S Q1 P Z1 t s p hch hp3 hst hZ1 r hrprime hrdvd with hr3 | hr7
        · exact hr3
        ·
            exfalso
            exact
              chapter2_claim13_psl28_excludes_seven_in_invertingSet
                H D Q K V W Q0 S Q1 P Z1 t s p hch hp3 hst hZ1
                (by simpa [hr7] using hrdvd))

private theorem claim_13_hasPrimePowerOrder_of_factorization
    {G : Type*} [Group G] [Finite G] (Z1 : Subgroup G) (s : G)
    (hJ : ∃ n : ℕ, Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} = 3 ^ n)
    (hfactor :
      Nat.card (Subgroup.centralizer (Z1 : Set G)) =
        Nat.card ((((Subgroup.centralizer (Z1 : Set G) : Subgroup G) ⊓ (Subgroup.centralizer ({s} : Set G) : Subgroup G)) : Subgroup G)) *
          Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)})
    (hinter :
      ∃ n : ℕ, Nat.card ((((Subgroup.centralizer (Z1 : Set G) : Subgroup G) ⊓ (Subgroup.centralizer ({s} : Set G) : Subgroup G)) : Subgroup G)) = 3 ^ n) :
    ∃ n : ℕ, Nat.card (Subgroup.centralizer (Z1 : Set G)) = 3 ^ n := by
  rcases hJ with ⟨j, hJcard⟩
  rcases hinter with ⟨i, hi⟩
  refine ⟨i + j, ?_⟩
  rw [hfactor, hi, hJcard, ← pow_add]

public theorem claim_13
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Z1 : Subgroup G) (t s : G) (p : ℕ)
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
    (hcase10_2 : p = 3 ∧ Nat.card ((W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G)) = 3 ∧
      Nat.card (nearFieldStar Q P) = 8 ∧ IsCyclic W ∧
        (Nat.card W = 3 ∨ Nat.card W = 9) ∧
          (∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
            Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) ∧
            ∃ (F : Type*) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
                (_ : Nontrivial F),
              PFAppendixII.IsDicksonIndexTwoModel F 3 1 ∧
                Nonempty (nearFieldStar Q P ≃* Fˣ))
    (hZ1 : Z1 = Subgroup.zpowers (s * t)) :
    ∃ n : ℕ, Nat.card (Subgroup.centralizer (Z1 : Set G)) = 3 ^ n := by
  have hp_order : p = orderOf (s * t) :=
    claim_9 H D Q K V W Q0 S Q1 P t s p (orderOf (s * t)) hch rfl
  have hst : orderOf (s * t) = 3 := hp_order.symm.trans hcase10_2.1
  have hJ :
      ∃ n : ℕ, Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} = 3 ^ n :=
    claim_13_invertingSet_three_power_from_psl28_exclusion
      H D Q K V W Q0 S Q1 P Z1 t s p hch hcase10_2.1 hst hZ1
  have hfactor_and_intersection :
      Nat.card ((Subgroup.centralizer (Z1 : Set G) : Subgroup G)) =
          Nat.card
            (((Subgroup.centralizer (Z1 : Set G) : Subgroup G) ⊓
              (Subgroup.centralizer ({s} : Set G) : Subgroup G)) : Subgroup G) *
            Nat.card {x : G // x ∈ ({y : G | y ∈ Subgroup.centralizer (Z1 : Set G) ∧ rightConjugateElem y s = y⁻¹} : Set G)} ∧
        (∃ n : ℕ,
          Nat.card (((Subgroup.centralizer (Z1 : Set G) : Subgroup G) ⊓
            (Subgroup.centralizer ({s} : Set G) : Subgroup G)) : Subgroup G) = 3 ^ n) := by
    classical
    have hA1 := hch.section3.section2.hA.A1
    have hsI := hch.section3.s_involution
    have htI := hA1.involution_t
    have hsH := hch.section3.s_mem_H
    have hCZ1_eq :
        Subgroup.centralizer (Z1 : Set G) =
          Subgroup.centralizer ({s * t} : Set G) := by
      rw [hZ1, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hst_ne : s * t ≠ 1 := by
      intro hst
      apply hA1.t_not_mem_H
      have ht_eq : t = s⁻¹ := by
        calc
          t = 1 * t := by simp
          _ = (s⁻¹ * s) * t := by simp
          _ = s⁻¹ * (s * t) := by simp
          _ = s⁻¹ := by rw [hst]; simp
      rw [ht_eq]
      exact H.inv_mem hsH
    have hst_order_odd : Odd (orderOf (s * t)) :=
      proposition_2_a H D Q t hA1 s t hsH hsI htI hA1.t_not_mem_H
    have hst_sq_ne : (s * t) ^ 2 ≠ 1 := by
      intro hsq
      have hdvd : orderOf (s * t) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with hone | htwo
      · exact hst_ne (orderOf_eq_one_iff.mp hone)
      · exact hst_order_odd.not_two_dvd_nat (by rw [htwo])
    have hst_strong : IsStronglyReal (s * t) :=
      ⟨s, t, hsI, htI, rfl⟩
    have hCZ1_odd : Odd (Nat.card (Subgroup.centralizer (Z1 : Set G))) := by
      rw [hCZ1_eq]
      exact
        (PFchapter1section3.lemma_3 H D Q K V W Q0 S Q1 t s hch.section3
          (s * t) hst_strong hst_sq_ne).2
    have hs_inv : s⁻¹ = s := hsI.inv_eq_self
    have hss : s * s = 1 := by
      simpa [pow_two] using hsI.sq_eq_one
    have hgen_conj : s * (s * t) * s⁻¹ = (s * t)⁻¹ := by
      rw [hs_inv]
      calc
        s * (s * t) * s = t * s := by rw [← mul_assoc, hss]; simp
        _ = (s * t)⁻¹ := by simp [hs_inv, htI.inv_eq_self]
    have hs_normalizes_CZ1 :
        s ∈ Subgroup.normalizer (Subgroup.centralizer (Z1 : Set G) : Set G) := by
      rw [hCZ1_eq, Subgroup.mem_normalizer_iff]
      have hforward :
          ∀ x : G, x ∈ Subgroup.centralizer ({s * t} : Set G) →
            s * x * s⁻¹ ∈ Subgroup.centralizer ({s * t} : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff] at hx ⊢
        intro y hy
        have hy_eq : y = s * t := by simpa using hy
        subst y
        have hcomm : Commute (s * t) x := hx (s * t) (by simp)
        have hcomm_inv : Commute ((s * t)⁻¹) (s * x * s⁻¹) := by
          rw [← hgen_conj]
          exact hcomm.conj s
        exact (Commute.inv_left_iff.mp hcomm_inv).eq
      intro x
      constructor
      · exact hforward x
      · intro hx
        have hback := hforward (s * x * s⁻¹) hx
        have hconj_twice : s * (s * x * s⁻¹) * s⁻¹ = x := by
          rw [hs_inv]
          calc
            s * (s * x * s) * s = (s * s) * x * (s * s) := by
              simp only [mul_assoc]
            _ = x := by rw [hss]; simp
        rw [hconj_twice] at hback
        exact hback
    have hfactor :
        Nat.card (Subgroup.centralizer (Z1 : Set G)) =
          Nat.card
              ((Subgroup.centralizer (Z1 : Set G) ⊓
                Subgroup.centralizer ({s} : Set G)) : Subgroup G) *
            Nat.card {x : G // x ∈ ({y : G |
              y ∈ Subgroup.centralizer (Z1 : Set G) ∧
                rightConjugateElem y s = y⁻¹} : Set G)} := by
      have hfactor' :=
        (lemma_a (M := G) s (Subgroup.centralizer (Z1 : Set G)) hsI
          hCZ1_odd hs_normalizes_CZ1).2.2
      change
        Nat.card (Subgroup.centralizer (Z1 : Set G)) =
          Nat.card
              ((Subgroup.centralizer (Z1 : Set G) ⊓
                Subgroup.centralizer ({s} : Set G)) : Subgroup G) *
            Nat.card {x : G // x ∈ ({y : G |
              y ∈ Subgroup.centralizer (Z1 : Set G) ∧
                rightConjugateElem y s = y⁻¹} : Set G)} at hfactor'
      exact hfactor'
    have hsQ : s ∈ Q :=
      involution_mem_Q_of_mem_H H D Q t hA1 s hsH hsI
    have hCs_le_H : Subgroup.centralizer ({s} : Set G) ≤ H := by
      intro x hx
      apply
        proposition_1_b H D Q t hA1 (Subgroup.zpowers s)
          (Subgroup.zpowers_ne_bot.mpr hsI.ne_one)
          (Subgroup.zpowers_le.mpr hsQ)
      apply centralizer_le_normalizer (Subgroup.zpowers s)
      simpa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] using hx
    have hV_eq_Cs :
        V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
      calc
        V = peterfalviV D t := hch.section3.section2.V_eq
        _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
          (proposition_5 H D Q t s hA1 hsH hsI hch.section3.s_conjugate).1
    have hinter_eq :
        Subgroup.centralizer (Z1 : Set G) ⊓
            Subgroup.centralizer ({s} : Set G) = V := by
      apply le_antisymm
      · intro x hx
        have hxCst : x ∈ Subgroup.centralizer ({s * t} : Set G) := by
          rw [← hCZ1_eq]
          exact hx.1
        have hstx : Commute (s * t) x :=
          (Subgroup.mem_centralizer_iff.mp hxCst) (s * t) (by simp)
        have hsx : Commute s x :=
          (Subgroup.mem_centralizer_iff.mp hx.2) s (by simp)
        have htx : Commute t x := by
          have h := hsx.inv_left.mul_left hstx
          simpa [mul_assoc] using h
        have hxCt : x ∈ Subgroup.centralizer ({t} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy_eq : y = t := by simpa using hy
          subst y
          exact htx.eq
        have hxH : x ∈ H := hCs_le_H hx.2
        have hx_right : x ∈ rightConjugate H t := by
          rw [rightConjugate]
          refine ⟨x, hxH, ?_⟩
          change t⁻¹ * x * (t⁻¹)⁻¹ = x
          simpa [htI.inv_eq_self] using htx.mul_inv_cancel
        have hxD : x ∈ D := by
          rw [hA1.D_eq]
          exact ⟨hxH, hx_right⟩
        rw [hch.section3.section2.V_eq]
        exact ⟨hxD, hxCt⟩
      · intro x hxV
        have hxDt :
            x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
          have hxVpet : x ∈ peterfalviV D t := by
            rw [← hch.section3.section2.V_eq]
            exact hxV
          exact hxVpet
        have hxDs :
            x ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
          rw [← hV_eq_Cs]
          exact hxV
        have hsx : Commute s x :=
          (Subgroup.mem_centralizer_iff.mp hxDs.2) s (by simp)
        have htx : Commute t x :=
          (Subgroup.mem_centralizer_iff.mp hxDt.2) t (by simp)
        have hstx : Commute (s * t) x := hsx.mul_left htx
        have hxCst : x ∈ Subgroup.centralizer ({s * t} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy_eq : y = s * t := by simpa using hy
          subst y
          exact hstx.eq
        constructor
        · rw [hCZ1_eq]
          exact hxCst
        · exact hxDs.2
    have hWP :=
      (PFchapter2.claim_1 H D Q K V W Q0 S Q1 P t s p hch).1
    letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hWcard_or : Nat.card W = 3 ∨ Nat.card W = 9 :=
      hcase10_2.2.2.2.2.1
    have hW3 : IsPGroup 3 W := by
      rw [IsPGroup.iff_card]
      rcases hWcard_or with hWcard | hWcard
      · exact ⟨1, by simpa using hWcard⟩
      · exact ⟨2, by norm_num [hWcard]⟩
    have hP3 : IsPGroup 3 P := by
      rw [IsPGroup.iff_card]
      refine ⟨1, ?_⟩
      rw [pow_one, hch.B1.P_card, hcase10_2.1]
    have hP_normalizes_W : P ≤ Subgroup.normalizer (W : Set G) := by
      intro v hvP
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact hWP.2.2.1 v w (hWP.2.1 hvP)
      · intro hvwv
        have hback :=
          hWP.2.2.1 v⁻¹ (v * w * v⁻¹)
            (V.inv_mem (hWP.2.1 hvP)) hvwv
        simpa [mul_assoc] using hback
    have hV3 : IsPGroup 3 V := by
      have hsup := IsPGroup.to_sup_of_normal_left' hW3 hP3 hP_normalizes_W
      rw [hWP.2.2.2.2] at hsup
      exact hsup
    refine ⟨hfactor, ?_⟩
    rw [hinter_eq]
    exact IsPGroup.iff_card.mp hV3
  rcases hfactor_and_intersection with ⟨hfactor, hinter⟩
  exact claim_13_hasPrimePowerOrder_of_factorization Z1 s hJ hfactor hinter

end PFchapter2
end CFSG.BenderSuzuki
