module

public import CFSG.Permutation.FinPackWalk
public import CFSG.Permutation.FinPackList

public section

namespace CFSG.RankThree.PartTwo.Sec15.LiebeckY4Pack

open Equiv CFSG.Permutation.FinPack

theorem h16 : 6 ≤ 16 := by norm_num

theorem enc_one : enc (1 : Perm (Fin 6)) = 5517840 := by decide +kernel

theorem enc_t1 : enc (swap (0 : Fin 6) 1 * swap 1 2) = 5517345 := by decide +kernel

theorem enc_t2 : enc (swap (0 : Fin 6) 1 * swap 1 2 * (swap 3 4 * swap 4 5)) = 3489825 := by
  decide +kernel

@[expose] def cjCodes : List ℕ :=
  [5517840, 5514000, 5391120, 2442000, 5517600, 5509920, 5325600, 1393440, 5513520, 5390640,
    2441520, 5509680, 5325360, 1393200, 5379120, 2430000, 5317680, 1385520, 2184240, 1201200,
    5509635, 5325315, 1393155, 5317635, 1385475, 1201155, 5316675, 1384515, 1200195, 1180995,
    4534560, 4526880, 4281120, 1332000, 4526640, 4280880, 1331760, 4269360, 1320240, 1197360,
    5513475, 5390595, 2441475, 5379075, 2429955, 2184195, 5378115, 2428995, 2183235, 2164035]

theorem valid_check : allK (permValidK 6) cjCodes = true := by decide +kernel

@[expose] noncomputable def qConj (g : ℕ) : Bool :=
  !(Nat.beq (mulK 6 g (mulK 6 g g)) 5517840 && !Nat.beq g 5517840) ||
    anyK (fun d => Nat.beq (mulK 6 d g) (mulK 6 5517345 d) ||
      Nat.beq (mulK 6 d g) (mulK 6 3489825 d)) cjCodes

theorem conj_walk : walkK 6 qConj 6 0 0 0 = true := by decide +kernel

theorem conj_six_K : ∀ g : Perm (Fin 6), g ^ 3 = 1 → g ≠ 1 →
    ∃ c : Perm (Fin 6), c * g * c⁻¹ = swap 0 1 * swap 1 2 ∨
      c * g * c⁻¹ = swap 0 1 * swap 1 2 * (swap 3 4 * swap 4 5) := by
  intro g h3 h1
  have hw := walkK_sound conj_walk g
  have hc : Nat.beq (mulK 6 (enc g) (mulK 6 (enc g) (enc g))) 5517840 = true := by
    rw [← enc_mul h16, ← enc_mul h16, ← enc_one, ← pow_three]
    exact (beq_enc_iff h16).2 h3
  have hn : Nat.beq (enc g) 5517840 = false := by
    rw [← enc_one]
    exact beq_enc_false h16 h1
  rw [qConj.eq_1, hc, hn] at hw
  simp only [Bool.not_false, Bool.and_self, Bool.not_true, Bool.false_or] at hw
  obtain ⟨d, hd, hdc⟩ := anyK_iff.1 hw
  obtain ⟨c, rfl⟩ := exists_enc_of_permValidK (allK_iff.1 valid_check d hd)
  refine ⟨c, ?_⟩
  rw [← enc_t1, ← enc_t2] at hdc
  simp only [← enc_mul h16, Bool.or_eq_true, beq_enc_iff h16] at hdc
  rcases hdc with e | e
  · left
    rw [e, mul_inv_cancel_right]
  · right
    rw [e, mul_inv_cancel_right]

end CFSG.RankThree.PartTwo.Sec15.LiebeckY4Pack
