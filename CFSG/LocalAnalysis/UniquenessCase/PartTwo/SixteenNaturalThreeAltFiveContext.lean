module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeArithmetic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Shapes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZResTrans
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeNatThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_threeNat_data_of_sum_three_alt_five_of_s15_eq_one
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar V₀ V hV L) ≤ 1)
    (hA5 : UC22.IsAlt ↥(lBar V₀ V hV L) 5)
    (hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 5)
      (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (hs : s15 D.M V₀ V hV L = 1) :
    ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
        (barSub V₀ V hV D.T) ∧
      Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 ∧
      D.sig = {3} ∧
      MBarGT D.M V₀ V 2 := by
  obtain ⟨t, ht, ht2, ht1, htr, hconc⟩ := c.conc
  have hc : s16h_H5Cfg (Mbar D.M V₀ V hV) (lBar V₀ V hV L) t :=
    ⟨s15_Infra_vtil_sq_eq_one V₀ V hV, ht, ht2, ht1, htr, hconc, hcomp, hthin⟩
  have htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L), ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom := by
    rcases hc.conc.2.2 with h1 | h2 | h3 | h4
    · exact (s16h_H5_not_pgroup hc h1).elim
    · exact (s16h_H5_not_tensor hc h2).elim
    · exact h3.2.2
    · exact s16h_trans_of_commSub_mem_irrSet hc.comp.2.2 h4.1
  have hshape : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3 :=
    ⟨5, Or.inr (Or.inr (Or.inr (Or.inr ⟨hA5, hsum⟩)))⟩
  have hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T) :=
    s168e3_threeNat_of_s15_eq_one c hcomp hshape htrans hs
  have h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7 :=
    s168e3_irrSet_seven_of_bounded c hcomp hshape htrans hs
      ⟨5, Or.inr (Or.inr (Or.inr (Or.inr ⟨hA5, by norm_num⟩)))⟩
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 60 := by
    rw [s15k_six_alt_card hA5 (by norm_num : 2 ≤ 5)]
    norm_num [Nat.factorial]
  have harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := by
    intro p hp hp2 hp3
    rw [hcard]
    exact s168e3_not_sq_dvd_336_mul hp hp2 hp3 (by norm_num)
  have hsig : D.sig = {3} :=
    s168e3_sig_eq_three_of_threeNat_card c hT h7 harith
  have hgt : MBarGT D.M V₀ V 2 := mBarGT_two_of_threeNat c.setting hT
  exact ⟨hT, h7, hsig, hgt⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
