module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveSzCenter
public import CFSG.GH74.Uniqueness.Bender.Out
public import CFSG.CGT.Timmesfeld75.ListWCSzU3

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Open Subgroup

theorem card_elemAbelian_two_aut_PSU3
    {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hY : IsPSUGp Y 3 n)
    (A : Subgroup (MulAut Y)) (hA : IsElemAbelian 2 A) :
    Nat.card A ≤ 2 ^ (n + 1) := by
  have hadm := LieModel.admissible hY
  have hn : 2 ≤ n := by
    have h1 : 1 ≤ n := hadm.2.1
    by_contra hlt
    have hn1 : n = 1 := by omega
    subst hn1
    exact hadm.2.2.2 rfl
  have hcl : StatedClassicalModel Y .PSU 3 2 n :=
    LieModel.statedClassicalModel hY (by decide)
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn hcl
  have hB : CFSG.GH74.Uniqueness.Bender.BenderType Y n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    CFSG.GH74.Uniqueness.Bender.BenderType.unitary n hn
      (e.trans (MulEquiv.subgroupCongr
        (show CFSG.Open.PSU3 2 n = CFSG.Theory.Comparator.PSU3Model n from rfl)))
  exact (hB.card_le_of_sq_eq_one_aut A fun x hx => by
    simpa [pow_two] using hA.2 x hx).1

theorem w3Lem85TwoGap1_holds : W3Lem85TwoGap1 :=
  w3Lem85TwoGap1_of_PSU3 (fun Y _ _ n hY A hA => card_elemAbelian_two_aut_PSU3 hY A hA)

end CFSG.LocalAnalysis.WeakClosure81
