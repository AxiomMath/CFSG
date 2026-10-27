module

public import CFSG.RankThree.PartTwo.Sec4.T444.DiagGriess
public import CFSG.HardMathSupport.Solomon.Coordinator.T112MCover
public import CFSG.CGT.PushingUpLit.T2KSW.Prop28

public section

open CFSG Subgroup

namespace CFSG.RankThree.PartTwo.Sec11

theorem fa_sylow_of_card {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J) {Q : Type}
    [Group Q] (hZ : Nat.card (Subgroup.center J) = 3) (e : J ⧸ Subgroup.center J ≃* Q) {m : ℕ}
    (hQ : Nat.card Q = 3 ^ 2 * m) (hm : ¬ 3 ∣ m) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  obtain ⟨-, ⟨r, hr, s, hs, hrs⟩, hexp⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.t112m_sylow_cover hq.1.commutator_eq_top hZ e hQ hm S
  exact ⟨r, hr, s, hs, hexp r hr, hexp s hs, hrs⟩

section Certified


theorem card_center_three_of {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    (hS : Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    Nat.card (Subgroup.center J) = 3 := by
  have hd : Nat.card (Subgroup.center J) ∣ 3 := by
    refine CFSG.RankThree.PartTwo.Sec4.diag_coverCenterThree_holds J hq hZ3 ?_
    rcases hS with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
  · exact absurd (Subgroup.card_eq_one.mp h1) hZ
  · exact h3

theorem fa_alt6 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 6)) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hZc : Nat.card (Subgroup.center J) = 3 :=
    card_center_three_of hq hZ3 hZ (Or.inl ⟨e⟩)
  have hQ : Nat.card (alternatingGroup (Fin 6)) = 3 ^ 2 * 40 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  exact fa_sylow_of_card hq hZc e hQ (by norm_num) S

theorem fa_alt7 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* alternatingGroup (Fin 7)) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hZc : Nat.card (Subgroup.center J) = 3 :=
    card_center_three_of hq hZ3 hZ (Or.inr (Or.inl ⟨e⟩))
  have hQ : Nat.card (alternatingGroup (Fin 7)) = 3 ^ 2 * 280 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  exact fa_sylow_of_card hq hZc e hQ (by norm_num) S

theorem fa_M22 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    (hZ3 : IsPGroup 3 (Subgroup.center J)) (hZ : Subgroup.center J ≠ ⊥)
    (e : J ⧸ Subgroup.center J ≃* CFSG.Blueprint.NativeSporadic.M22) (S : Sylow 3 J) :
    ∃ x ∈ (S : Subgroup J), ∃ y ∈ (S : Subgroup J), x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y ≠ y * x := by
  have hZc : Nat.card (Subgroup.center J) = 3 :=
    card_center_three_of hq hZ3 hZ (Or.inr (Or.inr ⟨e⟩))
  have hQ : Nat.card CFSG.Blueprint.NativeSporadic.M22 = 3 ^ 2 * 49280 :=
    CFSG.CGT.PushingUpLit.T2KSW.card_nativeM22_eq.trans (by norm_num)
  exact fa_sylow_of_card hq hZc e hQ (by norm_num) S

end Certified

end CFSG.RankThree.PartTwo.Sec11
