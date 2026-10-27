module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

theorem linShape_rank_cards
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {X : Type} [Group X] [Finite X]
    {A : Subgroup (MulAut X)}
    {Ā : Subgroup (MulAut (PSLg N K))} {j : ℕ} (hcardĀ : Nat.card Ā = Nat.card A)
    {lam : Ā →* Kˣ} (hc : Nat.card (Ā ⧸ lam.ker) ≤ 3) (hk : Nat.card (lam.ker) ≤ 9)
    (hlam1 : j ≠ 3 → lam = 1) :
    (j = 3 → Nat.card A ≤ 3 ^ 3) ∧ (j ≠ 3 → Nat.card A < 3 ^ 3) := by
  have hcard : Nat.card A = Nat.card (Ā ⧸ lam.ker) * Nat.card lam.ker :=
    hcardĀ.symm.trans (Subgroup.card_eq_card_quotient_mul_card_subgroup lam.ker)
  constructor
  · intro _
    rw [hcard]
    calc Nat.card (Ā ⧸ lam.ker) * Nat.card lam.ker ≤ 3 * 9 := Nat.mul_le_mul hc hk
      _ = 3 ^ 3 := by norm_num
  · intro hjne
    have hker : lam.ker = ⊤ := by rw [hlam1 hjne, MonoidHom.ker_one]
    have hq : Nat.card (Ā ⧸ lam.ker) = 1 := by
      rw [hker]
      haveI : Subsingleton (Ā ⧸ (⊤ : Subgroup Ā)) := QuotientGroup.subsingleton_quotient_top
      exact Nat.card_of_subsingleton 1
    rw [hcard, hq, one_mul]
    calc Nat.card lam.ker ≤ 9 := hk
      _ < 3 ^ 3 := by norm_num

end CFSG.StandardType.TablePThreeKG

end
