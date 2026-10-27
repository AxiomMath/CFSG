module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowTools
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowCard
public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowsS
public import CFSG.RankThree.PartTwo.Sec8.Hering418L2
public import CFSG.RankThree.PartTwo.Sec4.RonanK432L2Outer

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.GorensteinWalter
open CFSG.Assembly.RankThreeEven (projSL)

theorem autNoE27_psl2 {F : Type} [Field F] [Finite F] (h3 : ringChar F ≠ 3)
    (h4 : 4 ≤ Nat.card F) : AutNoE27 (PSL2 F) := fun A hA => by
  have := Hering418L2.card_le_nine_of_mulAut_PSL2 h3 h4 A hA.1
  rw [hA.2] at this
  omega

theorem noCfgS429_projSL_two
    {F : Type} [Field F] [Finite F]
    (h : ringChar F ≠ 3 ∨ Nat.card F ≤ 9) {S : Type} [Group S] [Finite S]
    (e : S ≃* projSL 2 F) : NoCfgS429 S := by
  have e' : S ≃* PSL2 F := e.trans (projSLEquivPSL F)
  by_cases h4 : 4 ≤ Nat.card F ∧ ringChar F ≠ 3
  · exact noCfgS429_of_autNoE27 ((autNoE27_psl2 h4.2 h4.1).of_mulEquiv e')
  · apply noCfgS429_of_card_lt
    have hc := RonanK432.card_psl2_mul_gcd F
    rw [← Nat.card_congr e'.toEquiv] at hc
    have hF : Nat.card F ≤ 9 := by
      rcases h with h | h
      · have : ¬ 4 ≤ Nat.card F := fun h4' => h4 ⟨h4', h⟩
        omega
      · exact h
    have hg : 0 < Nat.gcd 2 (Nat.card F - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have h1 : Nat.card S ≤ Nat.card F * (Nat.card F ^ 2 - 1) :=
      hc ▸ Nat.le_mul_of_pos_right _ hg
    have h2 : Nat.card F ^ 2 ≤ 81 := by
      calc Nat.card F ^ 2 ≤ 9 ^ 2 := Nat.pow_le_pow_left hF 2
        _ = 81 := by norm_num
    have h3 : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 9 * 80 :=
      Nat.mul_le_mul hF (by omega)
    omega

section Rows


theorem rowSOf429_one (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (h : p ≠ 3 ∨ e ≤ 2) :
    RowSOf429 (projSL 2 (GaloisField p e)) := by
  refine rowSOf429_of_noCfg fun _ _ _ _ _ ⟨eS⟩ => noCfgS429_projSL_two ?_ eS
  have hchar : ringChar (GaloisField p e) = p := ringChar.eq (GaloisField p e) p
  rcases h with h | h
  · exact Or.inl (by rw [hchar]; exact h)
  · by_cases hp3 : p = 3
    · subst hp3
      refine Or.inr ?_
      rw [GaloisField.card 3 e (by omega)]
      calc 3 ^ e ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) h
        _ = 9 := by norm_num
    · exact Or.inl (by rw [hchar]; exact hp3)

theorem rowSOf429_seven_SL2 (n : ℕ) (hn : 1 ≤ n) : RowSOf429 (projSL 2 (GaloisField 2 n)) :=
  rowSOf429_one 2 n hn (Or.inl (by norm_num))

end Rows

end CFSG.RankThree.PartTwo.Sec4.RonanK429
