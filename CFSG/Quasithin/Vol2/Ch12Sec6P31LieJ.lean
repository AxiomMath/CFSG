module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

open CFSG.QuasithinUnique

section Helpers

variable {Q : Type} [Group Q] (X : Subgroup Q)

private theorem liej_isSylowTwoOf_subgroupOf_top {S : Subgroup Q} (hS : IsSylowTwoOf S X) :
    IsSylowTwoOf (S.subgroupOf X) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  show ¬ 2 ∣ (S.subgroupOf X).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact hS.2.2

private theorem liej_normalizer_subgroupOf {S : Subgroup Q} (hS : S ≤ X) :
    Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) =
      (X ⊓ Subgroup.normalizer (S : Set Q)).subgroupOf X := by
  rw [Subgroup.inf_subgroupOf_left]
  exact (Subgroup.subgroupOf_normalizer_eq hS).symm

end Helpers

section Transport

variable {Q : Type} [Group Q] [Finite Q] (X : Subgroup Q)

theorem three_rank_transport
    (h : ∃ A B : Subgroup ↥X, Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set ↥X) ∧ A ⊓ B = ⊥) :
    ∃ A B : Subgroup Q, A ≤ X ∧ B ≤ X ∧ Nat.card A = 3 ∧ Nat.card B = 3 ∧
      A ≤ Subgroup.centralizer (B : Set Q) ∧ A ⊓ B = ⊥ := by
  obtain ⟨A, B, hA, hB, hcomm, hinf⟩ := h
  refine ⟨A.map X.subtype, B.map X.subtype, Subgroup.map_subtype_le A,
    Subgroup.map_subtype_le B, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hA
  · rw [Subgroup.card_map_of_injective X.subtype_injective]
    exact hB
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hab := congrArg X.subtype (Subgroup.mem_centralizer_iff.mp (hcomm ha) b hb)
    rw [map_mul, map_mul] at hab
    exact hab
  · rw [← Subgroup.map_inf_eq A B X.subtype X.subtype_injective, hinf, Subgroup.map_bot]

theorem card_borel_transport (m : ℕ)
    (h : ∀ T : Subgroup ↥X, IsSylowTwoOf T ⊤ →
      Nat.card ↥(Subgroup.normalizer (T : Set ↥X)) = m) :
    ∀ S : Subgroup Q, IsSylowTwoOf S X →
      Nat.card ↥(X ⊓ Subgroup.normalizer (S : Set Q)) = m := by
  intro S hS
  have hT := h (S.subgroupOf X) (liej_isSylowTwoOf_subgroupOf_top X hS)
  rw [liej_normalizer_subgroupOf X hS.1] at hT
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
    X ⊓ Subgroup.normalizer (S : Set Q) ≤ X)).symm.toEquiv).trans hT

theorem overgroup_transport (d : ℕ)
    (h : ∀ T N W : Subgroup ↥X, IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set ↥X) ≤ N →
      N ≠ Subgroup.normalizer (T : Set ↥X) → N ≠ ⊤ → W ≤ N → (W.subgroupOf N).Normal →
      (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) → ¬ d ∣ Nat.card W) :
    ∀ S N W : Subgroup Q, IsSylowTwoOf S X → X ⊓ Subgroup.normalizer (S : Set Q) ≤ N →
      N ≤ X → N ≠ X ⊓ Subgroup.normalizer (S : Set Q) → N ≠ X → W ≤ N →
      (W.subgroupOf N).Normal → (∀ p : ℕ, p.Prime → p ∣ Nat.card W → p = 2 ∨ p = 3) →
      ¬ d ∣ Nat.card W := by
  intro S N W hS hNorm hNX hNne hNX' hWN hWnorm hprimes
  have hWX : W ≤ X := hWN.trans hNX
  have hT := liej_isSylowTwoOf_subgroupOf_top X hS
  have hNorm' : Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) ≤
      N.subgroupOf X := by
    rw [liej_normalizer_subgroupOf X hS.1]
    exact Subgroup.subgroupOf_mono X hNorm
  have hne : N.subgroupOf X ≠ Subgroup.normalizer ((S.subgroupOf X : Subgroup ↥X) : Set ↥X) := by
    rw [liej_normalizer_subgroupOf X hS.1]
    intro heq
    apply hNne
    have h2 := Subgroup.subgroupOf_inj.mp heq
    rwa [inf_eq_left.mpr hNX,
      inf_eq_left.mpr (inf_le_left : X ⊓ Subgroup.normalizer (S : Set Q) ≤ X)] at h2
  have htop : N.subgroupOf X ≠ ⊤ := by
    intro heq
    rw [Subgroup.subgroupOf_eq_top] at heq
    exact hNX' (le_antisymm hNX heq)
  have hWN' : W.subgroupOf X ≤ N.subgroupOf X := Subgroup.subgroupOf_mono X hWN
  have hWnorm' : ((W.subgroupOf X).subgroupOf (N.subgroupOf X)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hWN').mpr ?_
    intro a b ha hb
    have key := (Subgroup.normal_subgroupOf_iff hWN).mp hWnorm
    rw [Subgroup.mem_subgroupOf] at ha hb ⊢
    simpa using key (a : Q) (b : Q) ha hb
  have hcard : Nat.card ↥(W.subgroupOf X) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWX).toEquiv
  have hprimes' : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥(W.subgroupOf X) → p = 2 ∨ p = 3 := by
    intro p hp hdvd
    rw [hcard] at hdvd
    exact hprimes p hp hdvd
  have key := h (S.subgroupOf X) (N.subgroupOf X) (W.subgroupOf X) hT hNorm' hne htop hWN'
    hWnorm' hprimes'
  rw [hcard] at key
  exact key

end Transport

end CFSG.Quasithin.H13.S126P31
