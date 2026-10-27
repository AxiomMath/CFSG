module

public import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.Quasithin.SBd19F

theorem eq_of_orderThree_centralizes {H : Type} [Group H] [Finite H]
    (hsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin H) {L₂ : Subgroup H}
    (hrk : CFSG.Open.pRank 3 L₂ = 2) {a : H} (ha : orderOf a = 3)
    (hc : ∀ l ∈ L₂, a * l = l * a) : a ∈ L₂ := by
  by_contra hna
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEL, hEel, hEcard⟩ := CFSG.RankThree.PartTwo.Sec5.exists_elemAbelian_le_of_le_pRank
    Nat.prime_three (show 2 ≤ CFSG.Assembly.pRank 3 L₂ from hrk.ge)
  have hnaE : a ∉ E := fun h => hna (hEL h)
  have ha3 : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have hyA : ∀ e ∈ E, e * a = a * e := fun e he => (hc e (hEL he)).symm
  obtain ⟨hel, hcard⟩ := CFSG.RankThree.PartTwo.Sec5.isElemAbelian_sup_zpowers hEel hnaE ha3 hyA
  have h3 : 3 ≤ CFSG.Assembly.pRank 3 (⊤ : Subgroup H) :=
    CFSG.RankThree.PartTwo.Sec5.le_pRank_of_elemAbelian Nat.prime_three le_top hel
      (by rw [hcard, hEcard]; norm_num)
  have h2 : CFSG.Assembly.pRank 3 (⊤ : Subgroup H) ≤ 2 := hsq 3 Nat.prime_three (by norm_num)
  omega

end CFSG.Quasithin.SBd19F
