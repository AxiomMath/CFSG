module

public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofThree
public import CFSG.RankThree.PartTwo.Sec4.Item4Res7ProofSix
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofSp4
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofU4
public import CFSG.RankThree.PartTwo.Sec4.Item424Res5ProofL4

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem Item424Res5.three_ne_zero_galoisField {p n : ℕ} [Fact p.Prime] (hp : 3 < p) :
    (3 : GaloisField p n) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : GaloisField p n) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (GaloisField p n) p] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

theorem Item424Res5.three_ne_zero_galoisField_two (n : ℕ) : (3 : GaloisField 2 n) ≠ 0 := by
  have h2 : (2 : GaloisField 2 n) = 0 := by
    have : ((2 : ℕ) : GaloisField 2 n) = 0 := CharP.cast_eq_zero (GaloisField 2 n) 2
    exact_mod_cast this
  have h31 : (3 : GaloisField 2 n) = 1 := by linear_combination h2
  rw [h31]
  exact one_ne_zero

theorem Item424Res5.no_root_galoisField {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (h2 : p % 3 = 2) :
    ∀ c : GaloisField p 1, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := Item424Res5.three_ne_zero_galoisField (n := 1) hp3
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have hc3 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply h3
    linear_combination hc
  let u : (GaloisField p 1)ˣ := Units.mk0 c hc0
  have hu3 : u ^ 3 = 1 := Units.ext (by simp [u, hc3])
  have hu1 : u ≠ 1 := fun h => hc1 (by simpa [u] using congrArg Units.val h)
  have hord : orderOf u = 3 := orderOf_eq_prime hu3 hu1
  have hdvd : 3 ∣ Nat.card (GaloisField p 1)ˣ := hord ▸ orderOf_dvd_natCard u
  rw [Nat.card_units, GaloisField.card p 1 (by norm_num), pow_one] at hdvd
  omega

theorem k424ThreeSp4_holds : K424ThreeSp4 := by
  intro X _ _ p _ hp3 ⟨eX⟩
  exact Item424Res5.census424_of_projSp (Item424Res5.three_ne_zero_galoisField hp3) eX

theorem k424ThreeL4_holds : K424ThreeL4 := by
  intro X _ _ p _ hp3 h
  rcases h with ⟨h1, ⟨eX⟩⟩ | ⟨h2, ⟨eX⟩⟩
  · exact Item424Res5.census424_of_projSU_four (f := 1) le_rfl (by rw [pow_one]; omega) eX
  · exact Item424Res5.census424_of_projSL_four (Item424Res5.three_ne_zero_galoisField hp3)
      (Item424Res5.no_root_galoisField hp3 h2) eX

theorem k424SixSp4Odd_holds : K424SixSp4Odd := by
  intro X _ _ n _ ⟨eX⟩ _
  exact Item424Res5.census424_of_projSp (Item424Res5.three_ne_zero_galoisField_two n) eX

end CFSG.RankThree.PartTwo.Sec4
