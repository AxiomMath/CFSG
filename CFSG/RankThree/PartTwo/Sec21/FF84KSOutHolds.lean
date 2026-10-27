module

public import CFSG.RankThree.PartTwo.Sec21.FF84S23KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG
open CFSG.Assembly (InCatalog)


private theorem coe_pow_iterate
    {X : Type} [Group X] (α : MulAut X) (n : ℕ) :
    ⇑(α ^ n) = (⇑α)^[n] := by
  induction n with
  | zero => ext x; simp
  | succ n ih => ext x; rw [pow_succ, MulAut.mul_apply, ih, Function.iterate_succ_apply]

private theorem factorization_three_eq_one
    {n : ℕ} (hn : n ≠ 0) (h3 : 3 ∣ n) (h9 : ¬ 9 ∣ n) :
    n.factorization 3 = 1 := by
  have h1 : 1 ≤ n.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).1 (by simpa using h3)
  have h2 : ¬ 2 ≤ n.factorization 3 := fun h =>
    h9 (by simpa using (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hn).2 h)
  omega

theorem ff84KSOut_holds
    : FF84KSOut := by
  intro C _ _ hs hnab hcat h3 h9 α hα
  have hf : (Nat.card C).factorization 3 = 1 :=
    factorization_three_eq_one Nat.card_pos.ne' h3 h9
  obtain ⟨a, ha⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.autThreePowInner_of_catalog
    hs hnab hcat hf α 1 (by
      intro x
      have := congrArg (fun β : MulAut C => β x) hα
      simpa [coe_pow_iterate] using this)
  exact ⟨a, MulEquiv.ext fun x => by simpa using ha x⟩

end CFSG.RankThree.PartTwo.Sec21.FF84
