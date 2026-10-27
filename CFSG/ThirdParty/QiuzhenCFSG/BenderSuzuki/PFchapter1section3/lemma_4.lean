module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_1_c
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.proposition_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.AppendixIInput
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.lemma_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.lemma_3_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_6
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section3

open PFchapter1section1 PFAppendixIII MatrixGroups
open PFchapter1section2
open scoped LinearAlgebra.Projectivization

universe u v

private theorem lemma_4_isMulCommutative_of_forall_sq_one
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
    _ = b⁻¹ * a⁻¹ := by rw [mul_inv_rev]
    _ = b * a := by rw [hinv b, hinv a]

/-!
# Peterfalvi, Part II, Chapter I, Section 3, Lemma 4
-/

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

private theorem lemma_4_Q0_le_generated
    {G : Type*} [Group G] (Q0 K : Subgroup G) (t : G) :
    Q0 ≤ psl2GeneratedSubgroup Q0 K t := by
  intro q hq
  exact Subgroup.subset_closure (Or.inl (Or.inl hq))

private theorem lemma_4_K_le_generated
    {G : Type*} [Group G] (Q0 K : Subgroup G) (t : G) :
    K ≤ psl2GeneratedSubgroup Q0 K t := by
  intro k hk
  exact Subgroup.subset_closure (Or.inl (Or.inr hk))

public theorem lemma_4_t_mem_generated
    {G : Type*} [Group G] (Q0 K : Subgroup G) (t : G) :
    t ∈ psl2GeneratedSubgroup Q0 K t :=
  Subgroup.subset_closure (Or.inr rfl)

private theorem lemma_4_Q0_card_ge_four
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
    4 ≤ Nat.card Q0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E0, hE0card, hE0sq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hsec.hA.A3
  have hE0p : IsPGroup 2 E0 := by
    refine IsPGroup.of_card (p := 2) (G := E0) (n := 2) ?_
    norm_num [hE0card]
  obtain ⟨T0, hE0T⟩ := IsPGroup.exists_le_sylow (G := G) (p := 2) hE0p
  obtain ⟨S0, hS0Q⟩ := PFchapter1section1.proposition_1_c H D Q t hsec.hA.A1
  obtain ⟨g, hgTS⟩ := MulAction.exists_smul_eq G T0 S0
  let A0 : Subgroup G := E0.map (MulAut.conj g).toMonoidHom
  have hA0_le_S0 : A0 ≤ (S0 : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyE, rfl⟩
    have hyT : y ∈ (T0 : Subgroup G) := hE0T hyE
    rw [← hgTS, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul y (MulAut.conj g)
      (T0 : Subgroup G) hyT
  have hA0card : Nat.card A0 = 4 := by
    calc
      Nat.card A0 = Nat.card E0 :=
        Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 4 := hE0card
  have hA0sq : ∀ x : A0, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    change (x : G) ^ 2 = 1
    rcases Subgroup.mem_map.mp x.property with ⟨y, hyE, hyx⟩
    have hy2 : y ^ 2 = (1 : G) :=
      congrArg Subtype.val (hE0sq ⟨y, hyE⟩)
    rw [← hyx]
    simpa [pow_two] using congrArg (fun z : G => (MulAut.conj g) z) hy2
  have hA0Q0 : A0 ≤ Q0 := by
    intro x hx
    apply (hsec.Q0_def x).mpr
    by_cases hx1 : x = 1
    · exact Or.inl hx1
    · exact Or.inr ⟨hsec.hA.A1.Q_le_H (hS0Q (hA0_le_S0 hx)),
        ⟨hx1, congrArg Subtype.val (hA0sq ⟨x, hx⟩)⟩⟩
  rw [← hA0card]
  exact Subgroup.card_le_of_le hA0Q0


private theorem lemma_4_D_inf_generated_eq_K
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
    D ⊓ psl2GeneratedSubgroup Q0 K t = K := by
  apply le_antisymm
  · intro x hx
    have hxUnion : x ∈ q0KUnionQ0KtQ0 Q0 K t := by
      rw [← lemma_4_generated_subgroup_eq_obligation
        H D Q K V W Q0 S Q1 t s hsec hst]
      exact hx.2
    rcases hxUnion with ⟨q, k, hq, hk, hxEq⟩ |
      ⟨q, k, qprime, hq, hk, hqprime, hxEq⟩
    · have hqD : q ∈ D := by
        have hxD : x ∈ D := hx.1
        have hkD : k ∈ D := hsec.section2.K_le_D hk
        rw [hxEq] at hxD
        have := D.mul_mem hxD (D.inv_mem hkD)
        simpa [mul_assoc] using this
      have hqOne : q = 1 := by
        have hqBot : q ∈ Q ⊓ D := ⟨hsec.section2.Q0_le_Q hq, hqD⟩
        simpa using hsec.section2.hA.A1.Q_disjoint_D.le_bot hqBot
      rw [hxEq, hqOne, one_mul]
      exact hk
    · exfalso
      apply hsec.section2.hA.A1.t_not_mem_H
      have hxH : x ∈ H := hsec.section2.hA.A1.D_le_H hx.1
      have hqH : q ∈ H :=
        hsec.section2.hA.A1.Q_le_H (hsec.section2.Q0_le_Q hq)
      have hkH : k ∈ H :=
        hsec.section2.hA.A1.D_le_H (hsec.section2.K_le_D hk)
      have hqprimeH : qprime ∈ H :=
        hsec.section2.hA.A1.Q_le_H (hsec.section2.Q0_le_Q hqprime)
      have hmem := H.mul_mem
        (H.mul_mem (H.inv_mem (H.mul_mem hqH hkH)) hxH)
        (H.inv_mem hqprimeH)
      have htEq : (q * k)⁻¹ * x * qprime⁻¹ = t := by
        rw [hxEq]
        group
      rwa [htEq] at hmem
  · intro k hk
    exact ⟨hsec.section2.K_le_D hk, lemma_4_K_le_generated Q0 K t hk⟩

private theorem lemma_4_K_inf_V_eq_bot
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
    K ⊓ V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxK : x ∈ K := hx.1
  have hxV : x ∈ V := hx.2
  have ht_inv : t⁻¹ = t := hsec.hA.A1.involution_t.inv_eq_self
  have ht_sq : t * t = 1 := by
    simpa [pow_two] using hsec.hA.A1.involution_t.sq_eq_one
  have hxInv : t * x * t = x⁻¹ := by
    have := ((hsec.K_def x).mp hxK).2
    simpa [rightConjugateElem, ht_inv] using this
  have hxComm : x * t = t * x := by
    rw [hsec.V_eq] at hxV
    exact Subgroup.mem_centralizer_singleton_iff.mp hxV.2
  have hxFix : t * x * t = x := by
    rw [← hxComm, mul_assoc, ht_sq, mul_one]
  have hxSelfInv : x = x⁻¹ := hxFix.symm.trans hxInv
  have hxSq : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := by rw [pow_two]
      _ = x * x⁻¹ := congrArg (fun z : G => x * z) hxSelfInv
      _ = 1 := mul_inv_cancel x
  by_contra hxOne
  let xD : D := ⟨x, hsec.K_le_D hxK⟩
  have hxDsq : xD ^ 2 = 1 := by
    apply Subtype.ext
    exact hxSq
  have hxDne : xD ≠ 1 := by
    intro h
    apply hxOne
    exact congrArg Subtype.val h
  have horder : orderOf xD = 2 :=
    orderOf_eq_prime_iff.mpr ⟨hxDsq, hxDne⟩
  have htwoDvd : 2 ∣ Nat.card D := by
    rw [← horder]
    exact orderOf_dvd_natCard xD
  exact (Nat.not_even_iff_odd.mpr hsec.hA.A1.D_odd)
    (even_iff_two_dvd.mpr htwoDvd)

private theorem lemma_4_K_inf_centralizer_Q0_eq_bot
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
    K ⊓ Subgroup.centralizer (Q0 : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hWcentralizer :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_W_eq_D_centralizer_involutions
      H D Q K V W t hsec.hA.A1 hsec.K_def hsec.V_eq hsec.W_eq
  let xD : D := ⟨x, hsec.K_le_D hx.1⟩
  have hxW : x ∈ W :=
    peterfalvi_chapter1_section2_proposition_3_appendixI_input_DmodW_faithful_on_Q0
      H D W Q0 hsec.Q0_def hWcentralizer xD (by
        intro q hq
        have hcomm : q * x = x * q :=
          Subgroup.mem_centralizer_iff.mp hx.2 q hq
        rw [rightConjugateElem]
        simpa [xD, mul_assoc] using (show x⁻¹ * (q * x) = q from by
          calc
            x⁻¹ * (q * x) = x⁻¹ * (x * q) := by rw [hcomm]
            _ = q := by simp))
  have hxBot : x ∈ (⊥ : Subgroup G) := by
    rw [← lemma_4_K_inf_V_eq_bot H D Q K V W Q0 S Q1 t hsec]
    exact ⟨hx.1, hsec.W_le_V hxW⟩
  exact hxBot

private theorem lemma_4_generated_lt_top
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
    (hst : orderOf (s * t) = 3) (hV_ne : V ≠ ⊥) :
    psl2GeneratedSubgroup Q0 K t < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hVleD : V ≤ D := by
    intro x hx
    rw [hsec.section2.V_eq] at hx
    exact hx.1
  have hVleL : V ≤ psl2GeneratedSubgroup Q0 K t := by
    rw [htop]
    exact le_top
  have hVleK : V ≤ K := by
    rw [← lemma_4_D_inf_generated_eq_K
      H D Q K V W Q0 S Q1 t s hsec hst]
    exact fun x hx => ⟨hVleD hx, hVleL hx⟩
  have hVbot : V ≤ (⊥ : Subgroup G) := by
    rw [← lemma_4_K_inf_V_eq_bot H D Q K V W Q0 S Q1 t hsec.section2]
    exact fun x hx => ⟨hVleK hx, hx⟩
  exact hV_ne (le_antisymm hVbot bot_le)


/-- Peterfalvi source obligation for the PSL(2,q) recognition step in Lemma 4. -/
private theorem lemma_4_psl2_matrix_group_obligation
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion.{u, v} L ΩL)
    (hst : orderOf (s * t) = 3) (hV_ne : V ≠ ⊥) :
    ∃ m : ℕ, m ≠ 0 ∧ Nat.card Q0 = 2 ^ m ∧
      Nonempty (psl2GeneratedSubgroup Q0 K t ≃* PSL2BinaryMatrixGroup m) := by
  classical
  rcases proposition_3_field_model_with_q0_card
      H D Q K V W Q0 S Q1 t hsec.section2 with
    ⟨m, hm, hQ0card, A, hWV, hWD, rhoD, rhoMul, rhoAut,
      q0_add, k_units, vmodW_aut, modelIso, hfieldData⟩
  refine ⟨m, hm, hQ0card, ?_⟩
  let L : Subgroup G := psl2GeneratedSubgroup Q0 K t
  let U : Subgroup L := Q0.subgroupOf L
  let T : Subgroup L := K.subgroupOf L
  let w : L := ⟨t, lemma_4_t_mem_generated Q0 K t⟩
  obtain ⟨α, hHα⟩ := hsec.section2.hA.A1.point_stabilizer
  let orbitClass : MulAction.orbitRel.Quotient L Ω := Quotient.mk'' α
  let ΩL : Type v := orbitClass.orbit
  let αL : ΩL := ⟨α, by
    simp [orbitClass, MulAction.mem_orbit_self]⟩
  let β : Ω := t⁻¹ • α
  let βL : ΩL := w⁻¹ • αL
  have htinv : t⁻¹ = t := hsec.section2.hA.A1.involution_t.inv_eq_self
  have hβL_val : (βL : Ω) = β := by
    change t⁻¹ • α = t⁻¹ • α
    rfl
  have hβ_ne : β ≠ α := by
    intro hβ
    apply hsec.section2.hA.A1.t_not_mem_H
    rw [hHα, MulAction.mem_stabilizer_iff]
    simpa [β, htinv] using hβ
  have hβL_ne : βL ≠ αL := by
    intro h
    apply hβ_ne
    simpa [hβL_val, αL] using congrArg Subtype.val h
  have hD_stab :
      D = MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := by
    simpa [β, hHα, rightConjugate_stabilizer] using
      hsec.section2.hA.A1.D_eq
  have hA1stab : HypothesisA1 G Ω (MulAction.stabilizer G α) D Q t := by
    simpa only [hHα] using hsec.section2.hA.A1
  have hQregular :=
    hypothesisA1_Q_regular_on_complement hA1stab hβ_ne hD_stab
  have hK_fixes_alpha : ∀ k : G, k ∈ K → k • α = α := by
    intro k hk
    rw [← MulAction.mem_stabilizer_iff, ← hHα]
    exact hsec.section2.hA.A1.D_le_H (hsec.section2.K_le_D hk)
  have hK_fixes_beta : ∀ k : G, k ∈ K → k • β = β := by
    intro k hk
    have hkD := hsec.section2.K_le_D hk
    rw [hD_stab] at hkD
    exact hkD.2
  have hQ0_fixes_alpha : ∀ q : G, q ∈ Q0 → q • α = α := by
    intro q hq
    rw [← MulAction.mem_stabilizer_iff, ← hHα]
    exact hsec.section2.hA.A1.Q_le_H (hsec.section2.Q0_le_Q hq)
  have hpoint_cases : ∀ x : ΩL,
      x = αL ∨ ∃ q : U, q • βL = x := by
    intro x
    have hxOrbit : (x : Ω) ∈ MulAction.orbit L α := by
      dsimp [ΩL, orbitClass] at *
      exact x.property
    rcases hxOrbit with ⟨l, hl⟩
    have hlUnion : (l : G) ∈ q0KUnionQ0KtQ0 Q0 K t := by
      rw [← lemma_4_generated_subgroup_eq_obligation
        H D Q K V W Q0 S Q1 t s hsec hst]
      exact l.property
    rcases hlUnion with ⟨q, k, hq, hk, hlEq⟩ |
      ⟨q, k, q', hq, hk, hq', hlEq⟩
    · left
      apply Subtype.ext
      calc
        (x : Ω) = (l : G) • α := hl.symm
        _ = (q * k) • α := by rw [hlEq]
        _ = α := by rw [mul_smul, hK_fixes_alpha k hk,
          hQ0_fixes_alpha q hq]
        _ = (αL : Ω) := rfl
    · right
      let qU : U :=
        ⟨⟨q, lemma_4_Q0_le_generated Q0 K t hq⟩, hq⟩
      refine ⟨qU, ?_⟩
      apply Subtype.ext
      calc
        ((qU • βL : ΩL) : Ω) = q • β := by
          change q • (βL : Ω) = q • β
          rw [hβL_val]
        _ = (q * k * t * q') • α := by
          symm
          calc
            (q * k * t * q') • α = q • (k • (t • (q' • α))) := by
              simp only [mul_smul]
            _ = q • (k • (t • α)) := by rw [hQ0_fixes_alpha q' hq']
            _ = q • (k • β) := by rw [show t • α = β by simp [β, htinv]]
            _ = q • β := by rw [hK_fixes_beta k hk]
        _ = (l : G) • α := by rw [hlEq]
        _ = (x : Ω) := hl
  have hUregular : Set.BijOn (fun q : U => q • βL) Set.univ
      ({x : ΩL | x ≠ αL} : Set ΩL) := by
    refine ⟨?_, ?_, ?_⟩
    · intro q _hq hqα
      apply hβL_ne
      apply smul_left_cancel q
      calc
        q • βL = αL := hqα
        _ = q • αL := by
          symm
          apply Subtype.ext
          exact hQ0_fixes_alpha (q : G) q.property
    · intro q₁ _ q₂ _ hq
      have hqG := congrArg (fun z : ΩL => (z : Ω)) hq
      let q₁Q : Q := ⟨(q₁ : G), hsec.section2.Q0_le_Q q₁.property⟩
      let q₂Q : Q := ⟨(q₂ : G), hsec.section2.Q0_le_Q q₂.property⟩
      have hqEq : q₁Q = q₂Q := hQregular.2.1 trivial trivial (by
        calc
          (q₁Q : Q) • β = (q₁ : G) • β := by simp [q₁Q]
          _ = (q₁ : G) • (βL : Ω) := by rw [hβL_val]
          _ = (q₁ • βL : ΩL).val := rfl
          _ = (q₂ • βL : ΩL).val := hqG
          _ = (q₂ : G) • (βL : Ω) := rfl
          _ = (q₂ : G) • β := by rw [hβL_val]
          _ = (q₂Q : Q) • β := by simp [q₂Q]
      )
      have hqEqG : (q₁Q : G) = (q₂Q : G) :=
        congrArg (fun z : Q => (z : G)) hqEq
      exact Subtype.ext (Subtype.ext hqEqG)
    · intro x hx
      rcases hpoint_cases x with rfl | ⟨q, hq⟩
      · exact False.elim (hx rfl)
      · exact ⟨q, trivial, hq⟩
  have hU_fixes_alpha : ∀ q : U, (q : L) • αL = αL := by
    intro q
    apply Subtype.ext
    exact hQ0_fixes_alpha (q : G) q.property
  have hLtwo : MulAction.IsMultiplyPretransitive L ΩL 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro a b c d hab hcd
    letI : MulAction.IsPretransitive L ΩL := inferInstance
    rcases MulAction.exists_smul_eq L a αL with ⟨la, hla⟩
    rcases MulAction.exists_smul_eq L c αL with ⟨lc, hlc⟩
    have hla_b : la • b ≠ αL := by
      intro h
      exact hab (smul_left_cancel la (hla.trans h.symm))
    have hlc_d : lc • d ≠ αL := by
      intro h
      exact hcd (smul_left_cancel lc (hlc.trans h.symm))
    rcases hUregular.2.2 hla_b with ⟨q₁, _hq₁, hq₁⟩
    rcases hUregular.2.2 hlc_d with ⟨q₂, _hq₂, hq₂⟩
    have hq₁alpha : (q₁ : L) • αL = αL := by
      apply Subtype.ext
      exact hQ0_fixes_alpha (q₁ : G) q₁.property
    have hq₂alpha : (q₂ : L) • αL = αL := by
      apply Subtype.ext
      exact hQ0_fixes_alpha (q₂ : G) q₂.property
    have hq₁invAlpha : (q₁ : L)⁻¹ • αL = αL := by
      rw [inv_smul_eq_iff]
      exact hq₁alpha.symm
    refine ⟨lc⁻¹ * (q₂ : L) * (q₁ : L)⁻¹ * la, ?_, ?_⟩
    · calc
        (lc⁻¹ * (q₂ : L) * (q₁ : L)⁻¹ * la) • a =
            lc⁻¹ • ((q₂ : L) • ((q₁ : L)⁻¹ • (la • a))) := by
              simp only [mul_smul]
        _ = lc⁻¹ • ((q₂ : L) • ((q₁ : L)⁻¹ • αL)) := by rw [hla]
        _ = lc⁻¹ • ((q₂ : L) • αL) := by
          rw [show (q₁ : L)⁻¹ • αL = αL by
            simpa using hU_fixes_alpha q₁⁻¹]
        _ = lc⁻¹ • αL := by rw [hU_fixes_alpha q₂]
        _ = c := by rw [← hlc]; simp
    · calc
        (lc⁻¹ * (q₂ : L) * (q₁ : L)⁻¹ * la) • b =
            lc⁻¹ • ((q₂ : L) • ((q₁ : L)⁻¹ • (la • b))) := by
              simp only [mul_smul]
        _ = lc⁻¹ • ((q₂ : L) • βL) := by
          have hq₁' : (q₁ : L) • βL = la • b := hq₁
          rw [← hq₁', inv_smul_smul]
        _ = lc⁻¹ • (lc • d) := by
          have hq₂' : (q₂ : L) • βL = lc • d := hq₂
          rw [hq₂']
        _ = d := by simp
  let HL : Subgroup L := MulAction.stabilizer L αL
  have hHL_factor : ∀ x : HL, ∃ q : U, ∃ k : T, (x : L) = q * k := by
    intro x
    have hxUnion : (x : G) ∈ q0KUnionQ0KtQ0 Q0 K t := by
      rw [← lemma_4_generated_subgroup_eq_obligation
        H D Q K V W Q0 S Q1 t s hsec hst]
      exact (x : L).property
    rcases hxUnion with ⟨q, k, hq, hk, hxEq⟩ |
      ⟨q, k, q', hq, hk, hq', hxEq⟩
    · let qU : U :=
        ⟨⟨q, lemma_4_Q0_le_generated Q0 K t hq⟩, hq⟩
      let kT : T :=
        ⟨⟨k, lemma_4_K_le_generated Q0 K t hk⟩, hk⟩
      exact ⟨qU, kT, by apply Subtype.ext; exact hxEq⟩
    · exfalso
      have hxfix : (x : L) • αL = αL := x.property
      have hval := congrArg (fun z : ΩL => (z : Ω)) hxfix
      have hqβ_ne : q • β ≠ α := by
        let qQ : Q := ⟨q, hsec.section2.Q0_le_Q hq⟩
        change (qQ : G) • β ≠ α
        exact hQregular.mapsTo (x := qQ) trivial
      apply hqβ_ne
      calc
        q • β = (q * k * t * q') • α := by
          symm
          calc
            (q * k * t * q') • α = q • (k • (t • (q' • α))) := by
              simp only [mul_smul]
            _ = q • (k • (t • α)) := by
              rw [hQ0_fixes_alpha q' hq']
            _ = q • (k • β) := by
              rw [show t • α = β by simp [β, htinv]]
            _ = q • β := by rw [hK_fixes_beta k hk]
        _ = (x : G) • α := by rw [hxEq]
        _ = α := by
          have hval' : ((x : L) : G) • α = α := by
            calc
              ((x : L) : G) • α = (((x : L) • αL : ΩL) : Ω) := rfl
              _ = α := by
                calc
                  (((x : L) • αL : ΩL) : Ω) = (αL : Ω) := congrArg (fun z : ΩL => (z : Ω)) hxfix
                  _ = α := rfl
          exact hval'
  have hU_le_HL : U ≤ HL := by
    intro q hq
    change (q : L) • αL = αL
    apply Subtype.ext
    exact hQ0_fixes_alpha (q : G) hq
  have hT_le_HL : T ≤ HL := by
    intro k hk
    change (k : L) • αL = αL
    apply Subtype.ext
    exact hK_fixes_alpha (k : G) hk
  have hU_sup_T : U ⊔ T = HL := by
    apply le_antisymm (sup_le hU_le_HL hT_le_HL)
    intro x hx
    rcases hHL_factor ⟨x, hx⟩ with ⟨q, k, hxEq⟩
    have hxEqL : x = (q : L) * (k : L) := by simpa using hxEq
    rw [hxEqL]
    exact Subgroup.mul_mem_sup q.property k.property
  have hU_disjoint_T : Disjoint U T := by
    rw [disjoint_iff]
    apply le_antisymm
    · intro x hx
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) :=
        hsec.section2.hA.A1.Q_disjoint_D.le_bot
          ⟨hsec.section2.Q0_le_Q hx.1,
            hsec.section2.K_le_D hx.2⟩
      simpa using hxbot
    · exact bot_le
  have hT_eq_stabilizer_pair :
      T = HL ⊓ rightConjugate HL w := by
    rw [rightConjugate_stabilizer]
    ext x
    change (x : G) ∈ K ↔
      (x : L) • αL = αL ∧ (x : L) • (w⁻¹ • αL) = w⁻¹ • αL
    have hpair : (x : G) ∈ D ↔
        (x : G) • α = α ∧ (x : G) • β = β := by
      rw [hD_stab]
      rfl
    constructor
    · intro hxK
      refine ⟨Subtype.ext (hK_fixes_alpha _ hxK), ?_⟩
      apply Subtype.ext
      calc
        (x : G) • (βL : Ω) = (x : G) • β := by rw [hβL_val]
        _ = β := hK_fixes_beta _ hxK
        _ = (βL : Ω) := by rw [hβL_val]
    · rintro ⟨hxα, hxβ⟩
      have hxαG : ((x : L) : G) • α = α := by
        calc
          ((x : L) : G) • α = ((x : L) : G) • (αL : Ω) := rfl
          _ = Subtype.val ((x : L) • αL) := rfl
          _ = Subtype.val αL := by rw [hxα]
          _ = (αL : Ω) := rfl
          _ = α := rfl
      have hxβG : ((x : L) : G) • β = β := by
        calc
          ((x : L) : G) • β = ((x : L) : G) • (βL : Ω) := by rw [hβL_val]
          _ = Subtype.val ((x : L) • βL) := rfl
          _ = Subtype.val βL := by rw [hxβ]
          _ = (βL : Ω) := rfl
          _ = β := by rw [hβL_val]
      have hxD : (x : G) ∈ D := hpair.mpr ⟨hxαG, hxβG⟩
      have hxInf : (x : G) ∈ D ⊓ L := ⟨hxD, x.property⟩
      rw [lemma_4_D_inf_generated_eq_K
        H D Q K V W Q0 S Q1 t s hsec hst] at hxInf
      exact hxInf
  have hU_normal_HL : (U.subgroupOf HL).Normal := by
    constructor
    intro x hx y
    rcases hHL_factor y with ⟨q, k, hyEq⟩
    have hkConj : rightConjugateElem (x : G) (k : G)⁻¹ ∈ Q0 := by
      simpa [rightConjugateElem] using
        lemma_4_leftConjugate_Q0_mem_of_K
          H D Q K V W Q0 S Q1 t s hsec (x : G) (k : G) hx k.property
    change ((y : L) * (x : L) * (y : L)⁻¹) ∈ U
    rw [hyEq]
    show ((q : G) * (k : G) * (x : G) * ((q : G) * (k : G))⁻¹) ∈ Q0
    have hinner : (k : G) * (x : G) * (k : G)⁻¹ ∈ Q0 := by
      simpa [rightConjugateElem] using hkConj
    have hmem := Q0.mul_mem
      (Q0.mul_mem q.property hinner) (Q0.inv_mem q.property)
    simpa only [Subgroup.coe_subtype, Subgroup.coe_mk, mul_inv_rev, mul_assoc] using hmem
  have hUeven : Even (Nat.card U) := by
    have hcardU : Nat.card U = Nat.card Q0 :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (lemma_4_Q0_le_generated Q0 K t)).toEquiv
    rw [hcardU, hQ0card]
    exact Nat.even_pow.mpr ⟨even_two, hm⟩
  have hTodd : Odd (Nat.card T) := by
    have hcardT : Nat.card T = Nat.card K :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (lemma_4_K_le_generated Q0 K t)).toEquiv
    rw [hcardT]
    exact hsec.section2.hA.A1.D_odd.of_dvd_nat
      (Subgroup.card_dvd_of_le hsec.section2.K_le_D)
  have hA2L : FaithfulSMul L ΩL := by
    rw [faithfulSMul_iff]
    intro x hxfix
    have hxα : (x : L) • αL = αL := hxfix αL
    have hxβ : (x : L) • βL = βL := hxfix βL
    have hxK : (x : G) ∈ K := by
      have hxRight : x ∈ rightConjugate HL w := by
        rw [rightConjugate_stabilizer]
        change x • (w⁻¹ • αL) = w⁻¹ • αL
        exact hxβ
      have hxPair : x ∈ HL ⊓ rightConjugate HL w := ⟨hxα, hxRight⟩
      rw [← hT_eq_stabilizer_pair] at hxPair
      exact hxPair
    have hxCentral : (x : G) ∈ Subgroup.centralizer (Q0 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have hqConj : (x : G) * q * (x : G)⁻¹ ∈ Q0 :=
        lemma_4_leftConjugate_Q0_mem_of_K
          H D Q K V W Q0 S Q1 t s hsec q (x : G) hq hxK
      let q₁Q : Q :=
        ⟨(x : G) * q * (x : G)⁻¹, hsec.section2.Q0_le_Q hqConj⟩
      let q₂Q : Q := ⟨q, hsec.section2.Q0_le_Q hq⟩
      have hactEq : (q₁Q : G) • β = (q₂Q : G) • β := by
        let qL : L := ⟨q, lemma_4_Q0_le_generated Q0 K t hq⟩
        let qU : U := ⟨qL, hq⟩
        have hxβinv : (x : L)⁻¹ • βL = βL := by
          calc
            (x : L)⁻¹ • βL = (x : L)⁻¹ • ((x : L) • βL) := by rw [hxβ]
            _ = βL := by simp
        have hactEqL :
            ((x : L) * qL * (x : L)⁻¹) • βL = qL • βL := by
          calc
            ((x : L) * qL * (x : L)⁻¹) • βL =
                (x : L) • (qL • ((x : L)⁻¹ • βL)) := by
                  simp only [mul_smul]
            _ = (x : L) • (qL • βL) := by rw [hxβinv]
            _ = qL • βL := hxfix (qU • βL)
        calc
          (q₁Q : G) • β = ((x : G) * q * (x : G)⁻¹) • β := rfl
          _ = ((x : L) * qL * (x : L)⁻¹ : G) • β := by simp [qL]
          _ = ((x : L) * qL * (x : L)⁻¹ : G) • (βL : Ω) := by rw [hβL_val]
          _ = Subtype.val (((x : L) * qL * (x : L)⁻¹) • βL) := rfl
          _ = Subtype.val (qL • βL) := by rw [hactEqL]
          _ = (qL : G) • (βL : Ω) := rfl
          _ = q • β := by simp [qL, hβL_val]
          _ = (q₂Q : G) • β := rfl
      have hqEq : q₁Q = q₂Q := hQregular.2.1 trivial trivial hactEq
      have hconjEq : (x : G) * q * (x : G)⁻¹ = q :=
        congrArg Subtype.val hqEq
      have hmul := congrArg (fun z : G => z * (x : G)) hconjEq
      simpa [mul_assoc] using hmul.symm
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← lemma_4_K_inf_centralizer_Q0_eq_bot
        H D Q K V W Q0 S Q1 t hsec.section2]
      exact ⟨hxK, hxCentral⟩
    apply Subtype.ext
    simpa using hxbot
  have hA3L : TwoRankAtLeastTwo L := by
    have hQ0ge : 4 ≤ Nat.card Q0 :=
      lemma_4_Q0_card_ge_four H D Q K V W Q0 S Q1 t hsec.section2
    have hm2 : 2 ≤ m := by
      by_contra hnot
      have hmle : m ≤ 1 := by omega
      have hmone : m = 1 := by omega
      rw [hmone] at hQ0card
      omega
    have hU_pgroup : IsPGroup 2 U := by
      exact IsPGroup.of_card (by
        calc
          Nat.card U = Nat.card Q0 := Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe
              (lemma_4_Q0_le_generated Q0 K t)).toEquiv
          _ = 2 ^ m := hQ0card)
    obtain ⟨E, hEcard⟩ :=
      Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hU_pgroup
        (n := 2) (by
          have hcardU : Nat.card U = 2 ^ m := by
            calc
              Nat.card U = Nat.card Q0 := Nat.card_congr
                (Subgroup.subgroupOfEquivOfLe
                  (lemma_4_Q0_le_generated Q0 K t)).toEquiv
              _ = 2 ^ m := hQ0card
          rw [hcardU]
          exact Nat.pow_le_pow_right (by omega) hm2)
    let EL : Subgroup L := E.map U.subtype
    refine ⟨EL, ?_, ?_⟩
    · calc
        Nat.card EL = Nat.card E :=
          Subgroup.card_map_of_injective U.subtype_injective
        _ = 4 := by norm_num [hEcard]
    · intro x
      rcases x.property with ⟨e, he, hex⟩
      have hxEq : (x : L) = U.subtype e := hex.symm
      apply Subtype.ext
      change (x : L) ^ 2 = 1
      rw [hxEq]
      let eQ0 : Q0 := ⟨(e : G), e.property⟩
      have hUsq : eQ0 ^ 2 = 1 :=
        (PFchapter1section2.proposition_1_c
          H D Q K V W Q0 S Q1 t hsec.section2).2.2 eQ0
      exact Subtype.ext (congrArg (fun z : Q0 => (z : G)) hUsq)
  have hAL : HypothesisA L ΩL HL T U w :=
    { A1 :=
        { two_transitive := hLtwo
          point_stabilizer := ⟨αL, rfl⟩
          involution_t := by
            exact ⟨fun h => hsec.section2.hA.A1.involution_t.ne_one
                (congrArg Subtype.val h),
              Subtype.ext hsec.section2.hA.A1.involution_t.sq_eq_one⟩
          t_not_mem_H := by
            intro hwH
            exact hβL_ne (by
              have hwfix := MulAction.mem_stabilizer_iff.mp hwH
              have hwinv : w⁻¹ = w := by
                apply Subtype.ext
                exact hsec.section2.hA.A1.involution_t.inv_eq_self
              simpa [βL, hwinv] using hwfix)
          D_eq := hT_eq_stabilizer_pair
          Q_le_H := hU_le_HL
          D_le_H := hT_le_HL
          Q_normal_in_H := hU_normal_HL
          Q_disjoint_D := hU_disjoint_T
          Q_sup_D := hU_sup_T
          Q_even := hUeven
          D_odd := hTodd }
      A2 := hA2L
      A3 := hA3L }
  have hlt : Nat.card L < Nat.card G := by
    simpa [L] using natCard_lt_of_subgroup_lt
      (lemma_4_generated_lt_top H D Q K V W Q0 S Q1 t s hsec hst hV_ne)
  have hindResult := hind L ΩL HL T U w hlt hAL
  rcases hindResult with ⟨N, hNnormal, q, hodd, hq, hq_gt, hmodel⟩
  have hmodelCore :=
    hypothesisA_model_subgroup_eq_twoPrimeResidual
      HL T U w hAL N hNnormal q hodd hq hq_gt hmodel
  rcases hmodelCore with ⟨hUp, hres_eq⟩
  have hinvolution_mem_N : ∀ x : L, IsInvolution x → x ∈ N := by
    intro x hx
    have hzp : IsPGroup 2 (Subgroup.zpowers x) := by
      apply IsPGroup.of_card (p := 2) (G := Subgroup.zpowers x) (n := 1)
      rw [Nat.card_zpowers,
        (orderOf_eq_prime_iff (x := x) (p := 2)).2 ⟨hx.sq_eq_one, hx.ne_one⟩,
        pow_one]
    obtain ⟨P, hzpP⟩ := hzp.exists_le_sylow
    rw [← hres_eq, twoPrimeResidual]
    exact (le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) P)
      (hzpP (Subgroup.mem_zpowers x))
  have hU_le_N : U ≤ N := by
    obtain ⟨P, hUP⟩ := hUp.exists_le_sylow
    intro x hx
    rw [← hres_eq, twoPrimeResidual]
    exact (le_iSup (fun S : Sylow 2 L => (S : Subgroup L)) P) (hUP hx)
  have hwN : w ∈ N := hinvolution_mem_N w hAL.A1.involution_t
  have hT_le_N : T ≤ N := by
    intro k hk
    have hkSet : (k : G) ∈ peterfalviKSet D t :=
      (hsec.section2.K_def (k : G)).mp hk
    have hktI : IsInvolution ((k : G) * t) := by
      have htinv : t⁻¹ = t := hsec.section2.hA.A1.involution_t.inv_eq_self
      have htk : t * (k : G) * t = (k : G)⁻¹ := by
        simpa [peterfalviKSet, rightConjugateElem, htinv, mul_assoc]
          using hkSet.2
      constructor
      · intro hkt
        have hkH : (k : G) ∈ H :=
          hsec.section2.hA.A1.D_le_H hkSet.1
        have hk_eq_tinv : (k : G) = t⁻¹ := by
          calc
            (k : G) = (k : G) * 1 := by simp
            _ = (k : G) * (t * t⁻¹) := by simp
            _ = ((k : G) * t) * t⁻¹ := by rw [mul_assoc]
            _ = t⁻¹ := by rw [hkt]; simp
        exact hsec.section2.hA.A1.t_not_mem_H
          ((by simpa [htinv] using hk_eq_tinv) ▸ hkH)
      · calc
          ((k : G) * t) ^ 2 = (k : G) * (t * (k : G) * t) := by
            simp [pow_two, mul_assoc]
          _ = (k : G) * (k : G)⁻¹ := by rw [htk]
          _ = 1 := by simp
    have hkwI : IsInvolution ((k : L) * w) := by
      constructor
      · intro h
        exact hktI.ne_one (congrArg Subtype.val h)
      · apply Subtype.ext
        exact hktI.sq_eq_one
    have hkwN : (k : L) * w ∈ N := hinvolution_mem_N _ hkwI
    have hww : w * w = 1 := by
      simpa [pow_two] using hAL.A1.involution_t.sq_eq_one
    rw [show (k : L) = ((k : L) * w) * w by simp [mul_assoc, hww]]
    exact N.mul_mem hkwN hwN
  have hNtop : N = ⊤ := by
    have hQ0_le_map : Q0 ≤ N.map L.subtype := by
      intro x hx
      let xU : U := ⟨⟨x, lemma_4_Q0_le_generated Q0 K t hx⟩, hx⟩
      exact ⟨(xU : L), hU_le_N xU.property, rfl⟩
    have hK_le_map : K ≤ N.map L.subtype := by
      intro x hx
      let xT : T := ⟨⟨x, lemma_4_K_le_generated Q0 K t hx⟩, hx⟩
      exact ⟨(xT : L), hT_le_N xT.property, rfl⟩
    have ht_map : t ∈ N.map L.subtype := ⟨w, hwN, rfl⟩
    have hgen_le : L ≤ N.map L.subtype := by
      change Subgroup.closure ((Q0 : Set G) ∪ (K : Set G) ∪ {t}) ≤ _
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with (hxQ0 | hxK) | hxt
      · exact hQ0_le_map hxQ0
      · exact hK_le_map hxK
      · rw [Set.mem_singleton_iff] at hxt
        subst x
        exact ht_map
    apply top_unique
    intro x _hx
    rcases hgen_le x.property with ⟨y, hyN, hyx⟩
    have hyxL : y = x := Subtype.ext hyx
    simpa [hyxL] using hyN
  have hUcard : Nat.card U = 2 ^ m := by
    calc
      Nat.card U = Nat.card Q0 := Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (lemma_4_Q0_le_generated Q0 K t)).toEquiv
      _ = 2 ^ m := hQ0card
  have hUsq : ∀ x : U, x ^ 2 = 1 := by
    intro x
    apply Subtype.ext
    let xQ0 : Q0 := ⟨(x : G), x.property⟩
    have hxsq : xQ0 ^ 2 = 1 :=
      (PFchapter1section2.proposition_1_c
        H D Q K V W Q0 S Q1 t hsec.section2).2.2 xQ0
    exact Subtype.ext (congrArg (fun z : Q0 => (z : G)) hxsq)
  obtain ⟨P, hP_le_U⟩ := PFchapter1section1.proposition_1_c HL T U w hAL.A1
  have hU_eq_P : U = (P : Subgroup L) :=
    P.is_maximal' hUp hP_le_U
  have htwo_subgroup_sq_one :
      ∀ (R : Subgroup L), IsPGroup 2 R → ∀ x : R, x ^ 2 = 1 := by
    intro R hRp x
    obtain ⟨PR, hRPR⟩ := hRp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L PR P
    have hxP : (MulAut.conj g) (x : L) ∈ (P : Subgroup L) := by
      rw [← hg, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul (x : L) (MulAut.conj g)
        (PR : Subgroup L) (hRPR x.property)
    have hxU : (MulAut.conj g) (x : L) ∈ U := by
      rw [hU_eq_P]
      exact hxP
    let xU : U := ⟨(MulAut.conj g) (x : L), hxU⟩
    apply Subtype.ext
    change (x : L) ^ 2 = 1
    apply (MulAut.conj g).injective
    rw [map_pow, map_one]
    exact congrArg Subtype.val (hUsq xU)
  rw [hNtop] at hmodel
  rcases hmodel with
      ⟨k, hk, hqk, eL, rho, eΩ, hnatural, hequiv⟩ |
      ⟨k, hk, hqk, eL, rho, eΩ, hnatural, hequiv⟩ |
      ⟨E, hEfield, hEfinite, J, hJstandard, hEcard, hfixedCard,
        eL, rho, eΩ, hnatural, hequiv⟩
  · have hfield : Nat.card (BinaryGaloisField k) = 2 ^ k := by
      simpa [BinaryGaloisField] using GaloisField.card 2 k hk
    have hpoints :
        Nat.card (ℙ (BinaryGaloisField k)
          (Fin 2 → BinaryGaloisField k)) = 2 ^ k + 1 := by
      calc
        Nat.card (ℙ (BinaryGaloisField k)
            (Fin 2 → BinaryGaloisField k)) =
            Nat.card (BinaryGaloisField k) + 1 :=
          Projectivization.card_of_finrank_two
            (BinaryGaloisField k) (Fin 2 → BinaryGaloisField k) (by simp)
        _ = 2 ^ k + 1 := by rw [hfield]
    have hUorbit : Nat.card U = Nat.card ΩL - 1 :=
      hypothesisA1_q_card_eq_complement_card HL T U w hAL.A1
    have hpows : 2 ^ m = 2 ^ k := by
      calc
        2 ^ m = Nat.card U := hUcard.symm
        _ = Nat.card ΩL - 1 := hUorbit
        _ = 2 ^ k := by rw [Nat.card_congr eΩ, hpoints]; omega
    have hmk : m = k :=
      Nat.pow_right_injective (by norm_num : 2 ≤ 2) hpows
    subst k
    exact ⟨(Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm.trans eL⟩
  · let eModel : L ≃* SuzukiMatrixGroup k :=
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm.trans eL
    have hsQ0 : s ∈ Q0 :=
      (hsec.section2.Q0_def s).2
        (Or.inr ⟨hsec.s_mem_H, hsec.s_involution⟩)
    let sL : L := ⟨s, lemma_4_Q0_le_generated Q0 K t hsQ0⟩
    have hstL : orderOf (sL * w) = 3 := by
      calc
        orderOf (sL * w) = orderOf ((sL * w : L) : G) :=
          (Subgroup.orderOf_coe (sL * w)).symm
        _ = orderOf (s * t) := by rfl
        _ = 3 := hst
    have hthreeL : 3 ∣ Nat.card L := by
      rw [← hstL]
      exact orderOf_dvd_natCard (sL * w)
    have hthreeSuzuki : 3 ∣ Nat.card (SuzukiMatrixGroup k) := by
      rw [← Nat.card_congr eModel.toEquiv]
      exact hthreeL
    exact ((External.huppert_blackburn_XI_3_6 k
      (Nat.pos_of_ne_zero hk)).2 hthreeSuzuki).elim
  · letI : Field E := hEfield
    letI : Finite E := hEfinite
    let eModel : L ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
      (Subgroup.topEquiv : (⊤ : Subgroup L) ≃* L).symm.trans eL
    rcases External.huppert_II_10_12
        J q hEcard hfixedCard hJstandard with
      ⟨_, rho0, pinf, _, _, _, hRH, _, _, _⟩
    rcases hRH with
      ⟨R, H0, _, _, _, _, _, _, hRcard, _, hcommcard, _, _, _, _, _⟩
    rcases hq with ⟨n, hn⟩
    have hRp : IsPGroup 2 R := by
      apply IsPGroup.of_card (p := 2) (G := R) (n := n * 3)
      rw [hRcard, hn]
      simp [pow_mul]
    let RL : Subgroup L := R.map eModel.symm.toMonoidHom
    have hRLp : IsPGroup 2 RL := hRp.map eModel.symm.toMonoidHom
    have hRsq : ∀ x : R, x ^ 2 = 1 := by
      intro x
      let xL : L := eModel.symm (x : ProjectiveSpecialUnitaryMatrixGroup J)
      have hxRL : xL ∈ RL := ⟨(x : ProjectiveSpecialUnitaryMatrixGroup J),
        x.property, rfl⟩
      have hxsqSub := htwo_subgroup_sq_one RL hRLp (⟨xL, hxRL⟩ : RL)
      have hxsqL : xL ^ 2 = 1 := congrArg Subtype.val hxsqSub
      apply Subtype.ext
      have hmap := congrArg eModel hxsqL
      simpa [xL] using hmap
    letI : IsMulCommutative R :=
      lemma_4_isMulCommutative_of_forall_sq_one hRsq
    letI : CommGroup R := IsMulCommutative.instCommGroup
    have hcommbot : commutator R = ⊥ :=
      (commutator_eq_bot_iff_center_eq_top (G := R)).2
        CommGroup.center_eq_top
    have hcommcardOne : Nat.card (commutator R) = 1 := by
      rw [hcommbot]
      simp
    have hqone : q = 1 := hcommcard.symm.trans hcommcardOne
    omega

public theorem lemma_4
    {G : Type u} {Ω : Type v}
    [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
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
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion.{u, v} L ΩL)
    (hst : orderOf (s * t) = 3) (hV_ne : V ≠ ⊥) :
    (psl2GeneratedSubgroup Q0 K t : Set G) = q0KUnionQ0KtQ0 Q0 K t ∧
      ∃ m : ℕ, m ≠ 0 ∧ Nat.card Q0 = 2 ^ m ∧
        Nonempty (psl2GeneratedSubgroup Q0 K t ≃* PSL2BinaryMatrixGroup m) := by
  exact
    ⟨lemma_4_generated_subgroup_eq_obligation
        H D Q K V W Q0 S Q1 t s hsec hst,
      lemma_4_psl2_matrix_group_obligation
        H D Q K V W Q0 S Q1 t s hsec hind hst hV_ne⟩

end PFchapter1section3
end CFSG.BenderSuzuki
