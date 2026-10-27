module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermLabelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBTorRowAt_perm_of_card
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) {r m N : ℕ}
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt p lab r m N C M) {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card M.Group = n.factorial) :
    GGSecFiveBPermLabel n p lab ∨
      (n = 4 ∧ lab.rank = 3 ∧
        ((lab.tag = .D ∧ p ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1))) := by
  have hfac_ne : ∀ {c a : ℕ}, a.factorial < c → c < (a + 1).factorial → c ≠ n.factorial := by
    intro c a h1 h2 hc
    have hn1 : (n - 1) + 1 = n := by omega
    exact factorial_succ_ne_of_between (k := n - 1) h1 h2 (by rw [hn1]; exact hc.symm)
  cases hrow with
  | aDep htag _ _ hp _ | aInd htag _ hp =>
      rw [l05nK3a_card_coxeterA] at hcard
      have hrank : lab.rank = n - 1 := by
        have h1 : lab.rank + 1 = n :=
          (Nat.factorial_inj' (Or.inr (by omega : 1 < n))).mp hcard
        omega
      rcases htag with htag | htag
      · exact Or.inl (Or.inl ⟨htag, hrank, by simpa [ggTorM, htag] using hp⟩)
      · exact Or.inl (Or.inr ⟨htag, hrank, by simpa [ggTorM, htag] using hp⟩)
  | c htag _ =>
      exfalso
      have h2 : 2 ≤ lab.rank := by
        have h := hlab.2
        rcases htag with htag | htag <;> rw [htag] at h <;> exact h.1
      rw [ggCoxeterB_card lab.rank h2] at hcard
      exact SignedPermCount.not_factorial_eq_two_pow_mul_factorial h2 hcard.symm
  | d hdisj =>
      have h3 : 3 ≤ lab.rank := by
        have h := hlab.2
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -, ⟨j, hj⟩⟩
        · rw [hD] at h
          exact h
        · rw [htwD] at h
          omega
      rcases (show lab.rank = 3 ∨ 4 ≤ lab.rank by omega) with hrank | h4
      · have hle : Nat.card (ggCoxeterMatrixD lab.rank).Group ≤ 24 := by
          rw [hrank]
          have h := SpJoinRefl.card_coxeterD_le 3 (by norm_num)
          norm_num [Nat.factorial] at h ⊢
          exact h
        rw [hcard] at hle
        have hn4 : n = 4 := by
          by_contra h5
          have h120 : 120 ≤ n.factorial := by
            have h := Nat.factorial_le (show 5 ≤ n by omega)
            norm_num [Nat.factorial] at h ⊢
            exact h
          omega
        refine Or.inr ⟨hn4, hrank, ?_⟩
        rcases hdisj with ⟨hD, hp | ⟨_, ⟨j, hj⟩⟩⟩ | ⟨htwD, hp, -⟩
        · exact Or.inl ⟨hD, hp⟩
        · omega
        · exact Or.inr ⟨htwD, hp⟩
      · exfalso
        rw [OrthF3.card_coxeterD_eq lab.rank h4] at hcard
        exact factorial_succ_ne_two_pow_pred_mul_factorial (k := n - 1) h4
          (by rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]; exact hcard.symm)
  | e6Three | e6Ind =>
      exfalso
      rw [card_coxeterE6_group] at hcard
      exact hfac_ne (c := 51840) (a := 8) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hcard
  | e7 =>
      exfalso
      rw [card_coxeterE7_group] at hcard
      exact hfac_ne (c := 2903040) (a := 9) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hcard
  | e8Three | e8Ind =>
      exfalso
      rw [card_coxeterE8_group] at hcard
      exact hfac_ne (c := 696729600) (a := 12) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hcard
  | f4 | relE6 =>
      exfalso
      rw [l04fFRC_ord_card_coxeterF4] at hcard
      exact hfac_ne (c := 1152) (a := 6) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hcard
  | g2 =>
      exfalso
      rw [l04fFRC_card_coxeterG2] at hcard
      exact hfac_ne (c := 12) (a := 3) (by norm_num [Nat.factorial])
        (by norm_num [Nat.factorial]) hcard
  | relD hdisj =>
      exfalso
      have h1 : 1 ≤ lab.rank - 1 := by
        have h := hlab.2
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -⟩
        · rw [hD] at h
          omega
        · rw [htwD] at h
          omega
      rcases (show lab.rank - 1 = 1 ∨ 2 ≤ lab.rank - 1 by omega) with hone | h2
      · rw [hone] at hcard
        have hle : Nat.card (CoxeterMatrix.B 1).Group ≤ 2 := by
          have h := card_coxeterB_le 1
          norm_num [Nat.factorial] at h
          exact h
        rw [hcard] at hle
        have h24 : 24 ≤ n.factorial := by
          have h := Nat.factorial_le hn
          norm_num [Nat.factorial] at h ⊢
          exact h
        omega
      · rw [ggCoxeterB_card (lab.rank - 1) h2] at hcard
        exact SignedPermCount.not_factorial_eq_two_pow_mul_factorial h2 hcard.symm
  | relA5 =>
      exfalso
      rw [ggCoxeterB_card 3 (by norm_num)] at hcard
      exact SignedPermCount.not_factorial_eq_two_pow_mul_factorial (by norm_num) hcard.symm

end CFSG.StandardType

end
