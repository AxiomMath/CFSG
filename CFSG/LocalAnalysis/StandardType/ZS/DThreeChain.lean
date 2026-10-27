module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.ZMod.Defs
import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.StandardType.ZS

@[expose] def bitVec (n k : ℕ) : Fin n → ZMod 2 :=
  fun i => if k.testBit i then 1 else 0

private theorem ite_testBit_zero_eq_natCast {b : ℕ} (hb : b < 2) :
    (if b.testBit 0 then (1 : ZMod 2) else 0) = (b : ZMod 2) := by
  have hb01 : b = 0 ∨ b = 1 := by omega
  rcases hb01 with rfl | rfl <;> simp

theorem bitVec_xor (n a b : ℕ) : bitVec n (a ^^^ b) = bitVec n a + bitVec n b := by
  funext i
  simp only [bitVec, Pi.add_apply, Nat.testBit_xor]
  generalize a.testBit i = p
  generalize b.testBit i = q
  revert p q
  decide

theorem exists_lt_bitVec_eq {n : ℕ} (v : Fin n → ZMod 2) : ∃ k < 2 ^ n, bitVec n k = v := by
  induction n with
  | zero =>
    refine ⟨0, by simp, ?_⟩
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨k', hk'lt, hk'v⟩ := ih (fun i => v i.succ)
    have hb : (v 0).val < 2 := ZMod.val_lt _
    have hb' : (v 0).val < 2 ^ 1 := hb
    refine ⟨2 * k' + (v 0).val, ?_, ?_⟩
    · rw [pow_succ]
      omega
    · funext i
      refine Fin.cases ?_ ?_ i
      · simp only [bitVec, Fin.val_zero]
        rw [show 2 * k' + (v 0).val = 2 ^ 1 * k' + (v 0).val by rw [pow_one]]
        have hbit : (2 ^ 1 * k' + (v 0).val).testBit 0 = (v 0).val.testBit 0 := by
          rw [Nat.testBit_two_pow_mul_add (a := k') (b := (v 0).val) (i := 1) hb'
            (j := 0)]
          simp
        simp only [hbit, ite_testBit_zero_eq_natCast hb, ZMod.natCast_zmod_val]
      · intro j
        simp only [bitVec, Fin.val_succ]
        rw [show 2 * k' + (v 0).val = 2 ^ 1 * k' + (v 0).val by rw [pow_one]]
        have hbit : (2 ^ 1 * k' + (v 0).val).testBit ((j : ℕ) + 1) =
            k'.testBit (j : ℕ) := by
          rw [Nat.testBit_two_pow_mul_add (a := k') (b := (v 0).val) (i := 1) hb'
            (j := (j : ℕ) + 1)]
          have hj : ¬ (j : ℕ) + 1 < 1 := by omega
          rw [if_neg hj, show (j : ℕ) + 1 - 1 = (j : ℕ) by omega]
        simp only [hbit]
        exact congrFun hk'v j

@[expose] def chainOK (next : ℕ → ℕ → ℕ) (ok : ℕ → ℕ → Bool) : List ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | known, (a, b) :: rest =>
    (decide (a ∈ known ∧ b ∈ known) && ok a b) && chainOK next ok (next a b :: known) rest

@[expose] def chainLabels (next : ℕ → ℕ → ℕ) (known : List ℕ) (steps : List (ℕ × ℕ)) :
    List ℕ :=
  known ++ steps.map fun s => next s.1 s.2

theorem mem_of_chainOK {G : Type*} [Group G] (H : Subgroup G) (τ : ℕ → G)
    (next : ℕ → ℕ → ℕ) (ok : ℕ → ℕ → Bool)
    (hstep : ∀ a b, τ a ∈ H → τ b ∈ H → ok a b = true → τ (next a b) ∈ H)
    (steps : List (ℕ × ℕ)) (known : List ℕ) (hk : ∀ k ∈ known, τ k ∈ H)
    (hok : chainOK next ok known steps = true) :
    ∀ k ∈ chainLabels next known steps, τ k ∈ H := by
  revert known
  induction steps with
  | nil =>
    intro known hk _
    simpa [chainLabels] using hk
  | cons s rest ih =>
    intro known hk hok
    obtain ⟨a, b⟩ := s
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hok
    obtain ⟨ha, hb, hab, hrest⟩ := hok
    have hc : τ (next a b) ∈ H := hstep a b (hk a ha) (hk b hb) hab
    intro k hk'
    have hall := ih (next a b :: known) (by
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hc
      · exact hk n hn) hrest
    exact hall k (by
      simp only [chainLabels, List.mem_append, List.map_cons, List.mem_cons] at hk' ⊢
      tauto)

end CFSG.StandardType.ZS
