module

public import CFSG.RankThree.PartOne.S12K.OrdRigid

public section

namespace CFSG.RankThree.PartOne.FLM

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartOne.S12K (charTwoOrder)

theorem profile_exp_eq {m N a r : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) (hr : Odd r)
    (hm : m = 2 ^ a * r) : N = a := by
  by_contra hne
  exact h.ne_of_ne hr hne hm

theorem profile_exp_small {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z)
    (hm : m = 168 ∨ m = 20160) : N = 3 ∨ N = 6 := by
  rcases hm with rfl | rfl
  · exact Or.inl (profile_exp_eq h (r := 21) (by decide) (by norm_num))
  · exact Or.inr (profile_exp_eq h (r := 315) (by decide) (by norm_num))

theorem ordA_two_one : ordA 2 (2 ^ 1) = 168 := by decide

theorem ordA_three_one : ordA 3 (2 ^ 1) = 20160 := by decide

theorem ordA_two_two : ordA 2 (2 ^ 2) = 20160 := by decide

theorem charTwoOrder_psl_three_one : charTwoOrder .PSL 3 1 = 168 := ordA_two_one

theorem charTwoOrder_psl_four_one : charTwoOrder .PSL 4 1 = 20160 := ordA_three_one

theorem charTwoOrder_psl_three_two : charTwoOrder .PSL 3 2 = 20160 := ordA_two_two

theorem ten_le_tri {n : ℕ} (hn : 5 ≤ n) : 10 ≤ (n - 1) * (n - 1 + 1) / 2 := by
  have h : 4 * 5 ≤ (n - 1) * (n - 1 + 1) := Nat.mul_le_mul (by omega) (by omega)
  omega

theorem ordTwistedA_two_four : ordTwistedA 2 (2 ^ 2) = 62400 := by decide

theorem ordSuzuki_eight : ordSuzuki (2 ^ 3) = 29120 := by decide

theorem small_of_charTwoOrder {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f)
    (h : charTwoOrder t n f = 168 ∨ charTwoOrder t n f = 20160) :
    (t = .PSL ∧ n = 3 ∧ f = 1) ∨ (t = .PSL ∧ n = 4 ∧ f = 1) ∨ (t = .PSL ∧ n = 3 ∧ f = 2) := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    have h' : ordA (n - 1) (2 ^ f) = 168 ∨ ordA (n - 1) (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordA (n := n - 1) (by omega) hf) h'
    by_cases hn5 : 5 ≤ n
    · exfalso
      have h10 := ten_le_tri hn5
      have : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
        Nat.le_mul_of_pos_left _ hf
      omega
    · have hn4 : n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hn4 with rfl | rfl | rfl
      · exfalso
        have hf' : f = 3 ∨ f = 6 := by norm_num at hN; omega
        rcases hf' with rfl | rfl <;> revert h' <;> decide
      · have hf' : f = 1 ∨ f = 2 := by norm_num at hN; omega
        rcases hf' with rfl | rfl
        · exact Or.inl ⟨rfl, rfl, rfl⟩
        · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
      · have hf' : f = 1 := by norm_num at hN; omega
        subst hf'
        exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
  case PSU =>
    exfalso
    obtain ⟨hn, hne⟩ := hrest
    have h' : ordTwistedA (n - 1) (2 ^ f) = 168 ∨ ordTwistedA (n - 1) (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordTwistedA (n := n - 1) (by omega) hf) h'
    by_cases hn5 : 5 ≤ n
    · have h10 := ten_le_tri hn5
      have : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
        Nat.le_mul_of_pos_left _ hf
      omega
    · have hn4 : n = 3 ∨ n = 4 := by omega
      rcases hn4 with rfl | rfl
      · have hf' : f = 1 ∨ f = 2 := by norm_num at hN; omega
        rcases hf' with rfl | rfl
        · exact hne rfl
        · revert h'
          rw [ordTwistedA_two_four]
          decide
      · have hf' : f = 1 := by norm_num at hN; omega
        subst hf'
        revert h'
        rw [show ordTwistedA (4 - 1) (2 ^ 1) = ordTwistedA 3 2 from rfl, ordTwistedA_three_two]
        decide
  case PSp =>
    exfalso
    obtain ⟨hn, -⟩ := hrest
    have h' : ordBC n (2 ^ f) = 168 ∨ ordBC n (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordBC (n := n) hf) h'
    have h4 : 4 ≤ n * n := Nat.mul_le_mul hn hn
    by_cases hn3 : 3 ≤ n
    · have h9 : 9 ≤ n * n := Nat.mul_le_mul hn3 hn3
      have : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ hf
      omega
    · obtain rfl : n = 2 := by omega
      omega
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    exfalso
    have h' : ordD n (2 ^ f) = 168 ∨ ordD n (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordD (n := n) (by omega) hf) h'
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    omega
  case POmegaMinus =>
    exfalso
    have h' : ordTwistedD n (2 ^ f) = 168 ∨ ordTwistedD n (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordTwistedD (n := n) (by omega) hf) h'
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    omega
  case G2 =>
    exfalso
    have h' : ordG2 (2 ^ f) = 168 ∨ ordG2 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordG2 hf) h'
    have hf1 : f = 1 := by omega
    subst hf1
    exact absurd hrest.2 (by norm_num)
  case F4 =>
    exfalso
    have h' : ordF4 (2 ^ f) = 168 ∨ ordF4 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordF4 hf) h'
    omega
  case E6 =>
    exfalso
    have h' : ordE6 (2 ^ f) = 168 ∨ ordE6 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordE6 hf) h'
    omega
  case E7 =>
    exfalso
    have h' : ordE7 (2 ^ f) = 168 ∨ ordE7 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordE7 hf) h'
    omega
  case E8 =>
    exfalso
    have h' : ordE8 (2 ^ f) = 168 ∨ ordE8 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordE8 hf) h'
    omega
  case twistedE6 =>
    exfalso
    have h' : ordTwistedE6 (2 ^ f) = 168 ∨ ordTwistedE6 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordTwistedE6 hf) h'
    omega
  case trialityD4 =>
    exfalso
    have h' : ordTrialityD4 (2 ^ f) = 168 ∨ ordTrialityD4 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordTrialityD4 hf) h'
    omega
  case twistedB2 =>
    exfalso
    obtain ⟨-, -, -, hf3⟩ := hrest
    have h' : ordSuzuki (2 ^ f) = 168 ∨ ordSuzuki (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordSuzuki hf) h'
    have hf3' : f = 3 := by omega
    subst hf3'
    revert h'
    rw [ordSuzuki_eight]
    decide
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    exfalso
    have h' : ordTwistedF4 (2 ^ f) = 168 ∨ ordTwistedF4 (2 ^ f) = 20160 := h
    have hN := profile_exp_small (profile_ordTwistedF4 hf) h'
    omega
  case Tits =>
    exfalso
    have h' : ordTits = 168 ∨ ordTits = 20160 := h
    rw [ordTits_eq] at h'
    revert h'
    decide

end CFSG.RankThree.PartOne.FLM
