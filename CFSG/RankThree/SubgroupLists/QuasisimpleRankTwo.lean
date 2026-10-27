module

public import CFSG.RankThree.SubgroupLists.SL3Involutions
public import CFSG.Milestones.LR_rank_two_isomorphism_types
public import CFSG.Assembly.LowTwoRank
public import CFSG.GroupTheory.PRankCoprimeQuotient

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K]

theorem two_ne_zero_of_odd_card (hK : Odd (Nat.card K)) : (2 : K) ≠ 0 :=
  CFSG.Wreathed.OddLinearThreeCentralizerCore.two_ne_zero K hK

theorem twoRank_le_two_of_det_eq_one (hK : Odd (Nat.card K)) {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    CFSG.Assembly.twoRank H ≤ 2 := by
  classical
  have h2 := two_ne_zero_of_odd_card hK
  unfold CFSG.Assembly.twoRank CFSG.Assembly.pRank
  refine csSup_le ⟨0, ⊥, bot_le, ?_, by simp⟩ ?_
  · refine ⟨⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => ?_⟩
    rw [Subgroup.mem_bot] at hx
    rw [hx, one_pow]
  rintro k ⟨E, -, ⟨-, hE2⟩, hcard⟩
  have hle : Nat.card (E.map H.subtype) ≤ 4 := by
    apply card_le_four_of_sq_eq_one_sl3 h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_mul, ← sq, hE2 x hx, map_one]
    · rintro _ ⟨x, -, rfl⟩
      exact hdet _ x.2
  have hc : Nat.card (E.map H.subtype) = Nat.card E :=
    Nat.card_congr (E.equivMapOfInjective _ H.subtype_injective).symm.toEquiv
  rw [hc, hcard] at hle
  by_contra hk
  push Not at hk
  have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  omega

theorem twoRank_quotient_center_eq_two (hK : Odd (Nat.card K)) {H : Subgroup (GL (Fin 3) K)}
    (hq : CFSG.IsQuasisimple H) (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) :
    CFSG.Assembly.twoRank (H ⧸ Subgroup.center H) = 2 := by
  obtain ⟨hperf, hsimple, hnonab⟩ := hq
  apply le_antisymm
  · have h2Z : ¬ 2 ∣ Nat.card (Subgroup.center H) := fun h => by
      have := Nat.dvd_trans h hZ
      norm_num at this
    have heq := CFSG.GroupTheory.PRankCoprimeQuotient.assembly_pRank_quotient_eq_of_not_dvd
      Nat.prime_two (Subgroup.center H) h2Z
    unfold CFSG.Assembly.twoRank
    rw [heq]
    exact twoRank_le_two_of_det_eq_one hK hdet
  · apply two_le_twoRank _ hnonab
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Nontrivial (H ⧸ Subgroup.center H) := hsimple.toNontrivial
    exact Group.IsPerfect.not_isSolvable (H ⧸ Subgroup.center H) hsolv

theorem quotient_center_rank_two_cases (hK : Odd (Nat.card K)) {H : Subgroup (GL (Fin 3) K)}
    (hq : CFSG.IsQuasisimple H) (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hZ : Nat.card (Subgroup.center H) ∣ 3) :
    (∃ r f : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ f ∧
        StatedClassicalModel (H ⧸ Subgroup.center H) .PSL 2 r f) ∨
      (∃ r f : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ f ∧
        StatedClassicalModel (H ⧸ Subgroup.center H) .PSL 3 r f) ∨
      (∃ r f : ℕ, r.Prime ∧ r ≠ 2 ∧ 1 ≤ f ∧
        StatedClassicalModel (H ⧸ Subgroup.center H) .PSU 3 r f) ∨
      StatedClassicalModel (H ⧸ Subgroup.center H) .PSU 3 2 2 ∨
      Nonempty ((H ⧸ Subgroup.center H) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((H ⧸ Subgroup.center H) ≃* StatedM11) := by
  have hsimple : IsSimpleGroup (H ⧸ Subgroup.center H) := hq.2.1
  exact CFSG.Milestones.lr_rank_two_isomorphism_types (H ⧸ Subgroup.center H) hq.2.2
    (twoRank_quotient_center_eq_two hK hq hdet hZ)

theorem pow_three_eq_one_of_mem_center {G : Type*} [Group G] [Finite G]
    (hZ : Nat.card (Subgroup.center G) ∣ 3) {z : G} (hz : z ∈ Subgroup.center G) :
    z ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hZ
  have h : (⟨z, hz⟩ : Subgroup.center G) ^ Nat.card (Subgroup.center G) = 1 := pow_card_eq_one'
  have : (⟨z, hz⟩ : Subgroup.center G) ^ 3 = 1 := by
    rw [hk, pow_mul, h, one_pow]
  simpa using congrArg Subtype.val this

end CFSG.RankThree.SubgroupLists
