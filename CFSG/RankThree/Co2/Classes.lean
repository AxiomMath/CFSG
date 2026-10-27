module

public import CFSG.RankThree.Co2.ClassesCertInputs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.Co2

open CFSG.Monster CFSG.Monster.B.Co2 CFSG.Monster.B.Short CFSG.Monster.B.TwoA
  CFSG.Monster.B.TwoA.Census CFSG.Monster.B.TwoA.Co2Inv

theorem repWords_letters : ∀ k < repWords.size, ∀ l ∈ repWords[k]!, l < 42 := by
  decide +kernel

@[expose] def rep (i : ℕ) : Cr := wordCr repWords[i]!

theorem repWords_size : repWords.size = 10 := rfl

theorem hasRows_rep {i : ℕ} (hi : i < 10) :
    HasRows (rep i : Kstab v0) (wordRows repWords[i]!) :=
  hasRows_wordCr (repWords_letters i (by rw [repWords_size]; exact hi))

theorem rep_zero : rep 0 = rCr := by
  apply Subtype.ext
  change ((1 * letterCr 9 : Cr) : Kstab v0) = rK
  rw [one_mul, letterCr, if_pos (by norm_num : (9 : ℕ) < 21), gC,
    dif_pos (by norm_num : (9 : ℕ) < 21)]
  change cGen ⟨9, by norm_num⟩ = rK
  rw [cGen, dif_neg (by norm_num)]
  rfl

attribute [irreducible] rep

end CFSG.RankThree.Co2
