module

public import CFSG.LocalAnalysis.StandardType.GGE78LocalRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTablePKnownRK_b36JExc_E78 (hR : GGE78LocalRankThree) :
    GGTablePKnownRK fun p n labJ labX =>
      GGRegimeB36J p n labJ labX ∧ (labX.tag = .E7 ∨ labX.tag = .E8) := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  obtain ⟨⟨hp3, hn, labL, htagL, hlabL⟩, htagX⟩ := hr
  subst hp3
  subst hn
  obtain ⟨hlocCore, hflat, hcardAb3, hrank, hnum, hself, honly, hm⟩ := hd.1
  obtain ⟨hAbA, -, -, -⟩ := hflat
  obtain ⟨hnum1, -⟩ := hnum
  have hcardA : Nat.card A ≤ 3 ^ 5 := by
    have h36 : (3 : ℕ) ^ 6 = 3 * 3 ^ 5 := by norm_num
    rw [h36] at hnum1
    exact Nat.le_of_mul_le_mul_left hnum1 (by norm_num)
  have hcardAb : Nat.card Ab ≤ 3 ^ 5 := (Subgroup.card_le_of_le hAbA).trans hcardA
  obtain ⟨m, hmcard, hmrank⟩ := hrank
  have hm5 : m ≤ 5 := by
    rw [hmcard] at hcardAb
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hcardAb
  have hperf : commutator X = ⊤ := by
    unfold GGTPNMarked at hm
    exact hm.1
  have h6 : 6 + (if 3 ∣ Nat.card (Subgroup.center X) then 1 else 0) ≤
      LargeEvenTwoLocalRank 3 X := hR X labX hΛX htagX hhX hperf
  omega

end CFSG.StandardType

end
