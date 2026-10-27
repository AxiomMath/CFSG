module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatMany
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3OutTab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1FbSyl

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_case163_5_of_sum_three_l3
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 2)
    (hL : IsL3 ↥(lBar V₀ V hV L) 1)
    (hS : SumOfNat (fun H U Z => BinaryNaturalSL H U Z 3 1)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    Case163_5 D V₀ V hV L :=
  ⟨Or.inl ⟨hL, s168e3_sumOfNat_binarySL_star c hS⟩, hs⟩

theorem s168e3_case163_5_of_sum_three_a5
    (c : S168e3Ctx D V₀ V L hV)
    (hs : s15 D.M V₀ V hV L = 2)
    (hL : UC22.IsAlt ↥(lBar V₀ V hV L) 5)
    (hS : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3) :
    Case163_5 D V₀ V hV L :=
  ⟨Or.inr ⟨hL, s168e3_sumOfNat_alternating_star c hS⟩, hs⟩

theorem s168e3_threeNat_of_s15_eq_one
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))), I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1) :
    ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Vtil V₀ V hV) := inferInstance
  have hwT : wTil V₀ V hV L = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hcomm : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) = ⊤ := by
    simpa [wTil, lBar] using hwT
  have hsum' : SumOfNatShape (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) 3 := by
    simpa [hwT] using hsum
  have hnormal : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) := by
    intro g hg
    exact Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)
  have hle : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV := by
    simpa [lBar] using barSub_mono V₀ V hV c.setting.hyp151.le
  have helem : ∀ w : Vtil V₀ V hV, w * w = 1 := fun w => by
    simpa [pow_two] using s15_Infra_vtil_sq_eq_one V₀ V hV w
  have hT : CFSG.ABGLocalTools.IsSylowOf 2 (barSub V₀ V hV D.T) (Mbar D.M V₀ V hV) := by
    have hTin : IsSylowIn 2 D.T D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM
    have hbar : IsSylowIn 2 (barSub V₀ V hV D.T) (barSub V₀ V hV D.M) :=
      s16c1_barSub_sylow c.m_le_stabTil hTin
    refine (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).2 ⟨?_, ?_, ?_⟩
    · simpa [Mbar] using hbar.1
    · simpa [Mbar] using hbar.2.1
    · simpa [Mbar] using hbar.2.2
  exact threeNat_of_component_data helem hle hnormal hT hcomp.2.2 hcomm hsum' htrans

theorem s168e3_irrSet_seven_of_bounded
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))), I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hbound : ∃ n : ℕ,
      (IsSLn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsSpn ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaPlus ↥(lBar V₀ V hV L) n 1 ∧ n < 8) ∨
      (IsOmegaMinus ↥(lBar V₀ V hV L) n 1 ∧ n < 10) ∨
      (UC22.IsAlt ↥(lBar V₀ V hV L) n ∧ n < 12)) :
    Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  rcases hT.card_irrSet_eq with h3 | h7
  · exact False.elim
      ((s16t3_not_three_dvd_outer hT.quasi hbound) (hT.three_dvd_card_outer h3))
  · exact h7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
