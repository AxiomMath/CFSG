module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.proposition_1_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

/-!
# Peterfalvi, Part II, Chapter II, Claim (2)(a)
-/

private theorem claim_2_a_P_ne_bot
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

private theorem claim_2_a_centralizer_A1
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
    (hP_ne : P ≠ ⊥) :
    let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let ΩP : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
    letI : MulAction C ΩP := fixedPointCentralizerAction G Ω P
    let HP : Subgroup C := H.comap C.subtype
    let DP : Subgroup C := D.comap C.subtype
    let QP : Subgroup C := Q.comap C.subtype
    let tP : C :=
      ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hch.B1.P_le_V
        hch.section3.section2.V_eq⟩
    @HypothesisA1 C ΩP inferInstance inferInstance inferInstance inferInstance HP DP QP tP := by
  exact (PFchapter1section3.proposition_1_a H D Q K V W Q0 S Q1 P t s
    hch.section3 hP_ne hch.B1.P_le_V).1

public theorem claim_2_a
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
    (let C : Subgroup G := Subgroup.centralizer (P : Set G)
     let ΩP : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
     letI : MulAction C ΩP := fixedPointCentralizerAction G Ω P
     let HP : Subgroup C := H.comap C.subtype
     let DP : Subgroup C := D.comap C.subtype
     let QP : Subgroup C := Q.comap C.subtype
     let tP : C :=
      ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hch.B1.P_le_V
        hch.section3.section2.V_eq⟩
     @HypothesisA1 C ΩP inferInstance inferInstance inferInstance inferInstance HP DP QP tP) ∧
            ∃ N : Subgroup G,
        N = D ⊓ Subgroup.centralizer ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
            Subgroup.centralizer (P : Set G) ∧
          (let C : Subgroup G := Subgroup.centralizer (P : Set G)
           let ΩP : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
           letI : MulAction C ΩP := fixedPointCentralizerAction G Ω P
           N.subgroupOf C = (MulAction.toPermHom C ΩP).ker) := by
  classical
  refine ⟨?_, ?_⟩
  · exact claim_2_a_centralizer_A1 H D Q K V W Q0 S Q1 P t s p hch
      (claim_2_a_P_ne_bot H D Q K V W Q0 S Q1 P t s p hch)
  · let C : Subgroup G := Subgroup.centralizer (P : Set G)
    let N : Subgroup G :=
      D ⊓ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) ⊓ C
    refine ⟨N, rfl, ?_⟩
    let ΩP : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
    letI : MulAction C ΩP := fixedPointCentralizerAction G Ω P
    have hP_ne : P ≠ ⊥ :=
      claim_2_a_P_ne_bot H D Q K V W Q0 S Q1 P t s p hch
    have hkernel :=
      (PFchapter1section3.proposition_1_a H D Q K V W Q0 S Q1 P t s
        hch.section3 hP_ne hch.B1.P_le_V).2
    have hcore :
        ∀ n : C, n ∈ pointStabilizerCore C ΩP ↔
          (n : G) ∈ (C ⊓ D) ⊓ Subgroup.centralizer ((C ⊓ Q : Subgroup G) : Set G) := by
      simpa [C, ΩP] using hkernel.1
    have hcent_QC_to_CQ :
        ∀ {x : G},
          x ∈ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) →
            x ∈ Subgroup.centralizer ((C ⊓ Q : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      exact hx y ⟨hy.2, hy.1⟩
    have hcent_CQ_to_QC :
        ∀ {x : G},
          x ∈ Subgroup.centralizer ((C ⊓ Q : Subgroup G) : Set G) →
            x ∈ Subgroup.centralizer ((Q ⊓ C : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro y hy
      exact hx y ⟨hy.2, hy.1⟩
    have hNcore : N.subgroupOf C = pointStabilizerCore C ΩP := by
      apply le_antisymm
      · intro n hn
        have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
        rw [hcore]
        exact ⟨⟨n.2, hnN.1.1⟩, hcent_QC_to_CQ hnN.1.2⟩
      · intro n hn
        have hnNL : (n : G) ∈
            (C ⊓ D) ⊓ Subgroup.centralizer ((C ⊓ Q : Subgroup G) : Set G) :=
          (hcore n).1 hn
        rw [Subgroup.mem_subgroupOf]
        exact ⟨⟨hnNL.1.2, hcent_CQ_to_QC hnNL.2⟩, hnNL.1.1⟩
    calc
      N.subgroupOf C = pointStabilizerCore C ΩP := hNcore
      _ = (MulAction.toPermHom C ΩP).ker := by
        ext g
        simp [pointStabilizerCore, MulAction.mem_stabilizer_iff, MonoidHom.mem_ker,
          Equiv.Perm.ext_iff]

end PFchapter2
end CFSG.BenderSuzuki



