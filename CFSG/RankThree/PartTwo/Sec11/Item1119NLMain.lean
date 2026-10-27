module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymInputs
public import CFSG.RankThree.PartTwo.Sec11.Item1119NLFam
import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarLocal

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec11.Item1119NL
open Item1120V0Bar (imgJ)

section Main


theorem sym1119NotLThree_holds : Sym1119NotLThree := by
  intro G _ _ A c L a R Y d x s r g hctx hex
  obtain ⟨m, hm1, hL⟩ := hex
  have hbig := hctx.big
  have h := hbig.toSec11Data
  have hstd := h.toSec11Std
  have haN := h.toHyp81.a_mem_normalizer
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  set τ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have h1 : (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using ha3)
    rw [hτ, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hout : ¬ KFacts.IsInnerAut τ := h.toHyp81.not_isInnerAut_induced
  obtain ⟨hZ, hQ, -⟩ := fixedPoints_facts_of_isList1016 h.isList1016 hτ3 hout
  obtain ⟨eK⟩ := nonempty_sec11K_quotient_mulEquiv haN ha3 hQ hZ
  have hKL : Sec8.IsoLThreeMinusPi (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a)) 2 m :=
    isoLThreeMinusPi_of_mulEquiv eK (KFacts.isoLThreeMinusPi_eqLocus hm1 hL hτ3 hout)
  have hxR : x ∈ R := (Item1116Proof.mem_R h).2.1
  have hxL : x ∈ L := (show x ∈ R ⊓ L by rw [h.inf_L_eq]; exact Subgroup.mem_zpowers x).2
  obtain ⟨k, hk⟩ := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hxo := orderOf_mk_eq_of_three_element hxL ⟨k, hk⟩
  have hxk : (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨x, hxL⟩) ^ 3 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨x, hxL⟩ : L) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  have hm3 : 3 ≤ m :=
    three_le_of_large_three_element hm1 hL ⟨k, hxk⟩ (by rw [hxo]; exact hbig.orderOf_x_gt)
  have hca : c * a = a * c := congrArg Subtype.val
    (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    (mem_thetaComponentsIn_iff.mp h.mem_thetaComponentsAt).1
  have hcL : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G) (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) :=
    hstd.mem_normalizer_Y (Item1119StepsProof.sec11K_ne_bot h) hcL hca
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  have hK' := mem_thetaComponentsIn_sec11K_inf hstd
  have hKY : sec11K L a ≤ Y := h.sec11K_le
  obtain ⟨eKJ⟩ := Sec4.Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJL : Sec8.IsoLThreeMinusPi (imgJ Y L a ⧸ aschbacherSolvableCore 3 (imgJ Y L a)) 2 m :=
    isoLThreeMinusPi_of_mulEquiv eKJ.symm hKL
  have hKT : IsType424 (sec11K L a ⧸ aschbacherSolvableCore 3 (sec11K L a)) :=
    Or.inr (Or.inr ⟨m, hm1, hKL⟩)
  have hJT : IsType424 (imgJ Y L a ⧸ aschbacherSolvableCore 3 (imgJ Y L a)) :=
    Or.inr (Or.inr ⟨m, hm1, hJL⟩)
  have hα3 := Sec4.Item426.thetaAut_pow_eq_one Y hcN hc3
  have hJα := Sec4.Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK'
  rcases hbig.isList with hY | hY | hY
  · exact false_of_isSL2 (isSL2_G2 hY hα3 hJα hJT) hm3 hJL
  · exact false_of_isSL2 (isSL2_D4 hY hα3 hJα hJT) hm3 hJL
  · exact false_of_isSL2 (isSL2_L3 hcN hc3 hK' hY hKT) hm3 hJL

end Main

end CFSG.RankThree.PartTwo.Sec11

end
