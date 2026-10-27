module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFSimple
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFWeyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omqnf_exists_acts_nW {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (w : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group) :
    ∃ (π : Equiv.Perm (Fin (n - 1))) (s : Fin (n - 1) → ℤ), SpIsSign s ∧
      omqnfRealizes (n - 1) w π s ∧
      omqnfActs n b c π s
        (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirr).nW w)) := by
  let cs := (coxeterMatrix (isFiniteType_cartanB (n - 1))).toCoxeterSystem
  have key : ∀ m, ∀ w : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group, cs.length w ≤ m →
      ∃ (π : Equiv.Perm (Fin (n - 1))) (s : Fin (n - 1) → ℤ), SpIsSign s ∧
        omqnfRealizes (n - 1) w π s ∧
        omqnfActs n b c π s
          (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirr).nW w)) := by
    intro m
    induction m with
    | zero =>
      intro w hwle
      have hw1 : w = 1 := cs.length_eq_zero_iff.mp (Nat.le_zero.mp hwle)
      subst hw1
      refine ⟨1, 1, spIsSign_one, omqnfRealizes_one _, ?_⟩
      rw [(SmallO8mCurtis.curtisDatum n hn hirr).nW_one, map_one]
      exact omqnfActs_one n b c
    | succ m ih =>
      intro w hwle
      by_cases hw1 : w = 1
      · subst hw1
        refine ⟨1, 1, spIsSign_one, omqnfRealizes_one _, ?_⟩
        rw [(SmallO8mCurtis.curtisDatum n hn hirr).nW_one, map_one]
        exact omqnfActs_one n b c
      · obtain ⟨k, hk⟩ := cs.exists_leftDescent_of_ne_one hw1
        set w' : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group := cs.simple k * w
          with hw'def
        have hww' : cs.simple k * w' = w := cs.simple_mul_simple_cancel_left (w := w) k
        have hlen' : cs.length w' < cs.length w := hk
        have hlenle : cs.length w' ≤ m := by omega
        obtain ⟨π', s', hs', hr', ha'⟩ := ih w' hlenle
        have hcond : cs.length (cs.simple k * w') = cs.length w' + 1 := by
          have hA : cs.length (cs.simple k * w') = cs.length w := by rw [hww']
          have hB : cs.length w' < cs.length (cs.simple k * w') := by rw [hA]; exact hlen'
          rcases cs.length_simple_mul w' k with h | h <;> omega
        rw [show w = cs.simple k * w' from hww'.symm]
        have hnW := (SmallO8mCurtis.curtisDatum n hn hirr).nW_simple_mul w' k hcond
        by_cases hlt : k.val + 1 < n - 1
        · refine ⟨_, _, hs'.mul spIsSign_one _, (omqnfRealizes_simple_of_lt hlt).mul hr', ?_⟩
          rw [hnW, map_mul]
          exact (omqnfActs_minusWeyl_of_lt hirr hlt).mul ha' spIsSign_one hs'
        · refine ⟨_, _, hs'.mul (spIsSign_spSgn k) _,
            (omqnfRealizes_simple_of_not_lt hlt).mul hr', ?_⟩
          rw [hnW, map_mul]
          exact (omqnfActs_minusWeyl_of_not_lt hirr hlt).mul ha' (spIsSign_spSgn k) hs'
  exact key (cs.length w) w le_rfl

theorem omqnf_spinAction_nW {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group} {π : Equiv.Perm (Fin (n - 1))}
    {s : Fin (n - 1) → ℤ} (hx : omqnfRealizes (n - 1) x π s) (hs : SpIsSign s) :
    omqnfActs n b c π s
      (spinAction (quadMinus n K b c) ((SmallO8mCurtis.curtisDatum n hn hirr).nW x)) := by
  obtain ⟨π', s', hs', hx', hact⟩ := omqnf_exists_acts_nW hn hirr x
  obtain ⟨rfl, rfl⟩ := omqnfRealizes_unique hx hx' hs
  exact hact

end CFSG.LocalAnalysis.WeakClosure81
