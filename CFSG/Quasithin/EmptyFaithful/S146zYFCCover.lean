module

public import CFSG.Quasithin.EmptyFaithful.S146zYList
public import CFSG.Quasithin.EmptyFaithful.S146zYFCOrd
public import CFSG.Quasithin.EmptyFaithful.S146zYFCCase

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique.Vol2Native CFSG.Assembly.LowTwoRank

theorem coverL35_of_a36 (h36 : A36ForSQTKCat) : CoverL35Fact := by
  intro p _ hp5 A _ _ L Y _ hA hL he hY
  subst hp5
  obtain ⟨e⟩ := he
  have hY372 : Nat.card Y = 372000 := card_eq_of_statedPSL_three_five hY
  have hLc : L ∈ cComp (⊤ : Subgroup A) := mem_cComp_top_of_isComponent hL
  rcases (h36 A hA L hLc).1 with ⟨-, hs, -⟩ | ⟨-, hZ, hlist⟩ | h3 | h4
  · exact center_eq_bot_of_isSimpleGroup_of_isQuasisimple hL.1 hs
  · exfalso
    rcases hlist with ⟨s, q, f, hq, hf, -, hsl⟩ | h6 | h7 | h22
    · refine not_isSLEps3_of_card_eq hq hf hsl ?_
      have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      rw [Nat.card_congr e.toEquiv, hY372, hZ] at hmul
      omega
    · have h := card_eq_of_isHat h6 e
      rw [card_alternatingGroup_fin_eq (by norm_num), hY372] at h
      norm_num [Nat.factorial] at h
    · have h := card_eq_of_isHat h7 e
      rw [card_alternatingGroup_fin_eq (by norm_num), hY372] at h
      norm_num [Nat.factorial] at h
    · have h := card_eq_of_isHat h22 e
      have hM : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
        card_nativeM22_eq
      omega
  · exact (not_a36Case3_of_isQuasisimple hL.1 h3).elim
  · exact (not_a36Case4_of_isQuasisimple hL.1 h4).elim

end CFSG.Quasithin.S146zY
