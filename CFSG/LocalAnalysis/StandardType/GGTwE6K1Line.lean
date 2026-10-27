module

public import CFSG.LocalAnalysis.StandardType.GGTwE6K1ThreeA2Two
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
import CFSG.LocalAnalysis.StandardType.GGTwE6K1Mark
import CFSG.LocalAnalysis.StandardType.GGTwE6K1A5
import CFSG.LocalAnalysis.StandardType.GGTwE6K1D4
import CFSG.LocalAnalysis.StandardType.GGTwE6K1Toral
import CFSG.LocalAnalysis.StandardType.GGTwE6K1A2InnerRank
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24A2CubeOuter
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.Goldschmidt.Steps.G37Core
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Basic
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcCtx
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcPlumb
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcSmall
import CFSG.HardMathSupport.Solomon.Coordinator.C25Borel
import CFSG.HardMathSupport.Solomon.Coordinator.L3FATArith
import CFSG.HardMathSupport.Solomon.Coordinator.L3G515Core
import CFSG.HardMathSupport.Solomon.Coordinator.L3NoSLInner
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28b
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma55
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
import CFSG.Quasithin.Background.A3Structure314
import CFSG.Quasithin.Background.B15P4LayerDict
import CFSG.Quasithin.Background.C1GNSolvConnect
import CFSG.Quasithin.Background.E2Statements
import CFSG.Quasithin.Background.F6CatRecogL2
import CFSG.Quasithin.Background.F6CatRecogTools2
import CFSG.Quasithin.Background.FFC7G
import CFSG.Quasithin.Background.FFC8A
import CFSG.Quasithin.Background.InternalSecB56B
import CFSG.Quasithin.EmptyFaithful.Insp9Cases4
import CFSG.Quasithin.EmptyFaithful.S153D44
import CFSG.Quasithin.H13.A5S136b
import CFSG.Quasithin.H13.A5S136c
import CFSG.Quasithin.H13.A5Y1367c
import CFSG.Quasithin.Vol2.Ch10SecA1011
import CFSG.Quasithin.Vol2.Ch10SecB5Easy
import CFSG.Quasithin.Vol2.Ch10SecB6C27
import CFSG.Quasithin.Vol2.Ch10SecB6Lt
import CFSG.Quasithin.Vol2.Ch10SecB6Prep
import CFSG.Quasithin.Vol2.Ch10SecB6Rank
import CFSG.Quasithin.Vol2.Ch10SecB6S21
import CFSG.Quasithin.Vol2.Ch10SecB6Syl
import CFSG.Quasithin.Vol2.Ch10SecKGC27b
import CFSG.Quasithin.Vol2.Ch11SecAFacts12b
import CFSG.Quasithin.Vol2.Ch11SecQ9bKGC
import CFSG.Quasithin.Vol2.Ch9KGFFQR
import CFSG.Quasithin.Vol2.Ch9KGFFQRCase
import CFSG.Walter.J1Props
import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24


theorem ggTwE6K1LineLabels_of (hS : E6LeviThreeToralBar) (hQ2 : GGTwE6K1ThreeA2Two) :
    GGTwE6K1LineLabels := by
  intro n hn h3 K _ _ σ hK hσ h hh1 hh3 E hE hcard hfE hEI hnt J hJ hEJ hCJ
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hK3 : ringChar K ≠ 3 := by
    rw [hchar]
    decide
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ (2 ^ n) hσ hK hq2
  obtain ⟨D⟩ := nonempty_twE6LineLang K σ (2 ^ n) hK3 hσ hK hq2 h hh1 hh3
  have he : D.e = n := by
    have h1 := D.hqe
    rw [hchar] at h1
    exact (Nat.pow_right_injective (le_refl 2) h1).symm
  obtain ⟨i, hqs, hJi⟩ := D.exists_rationalComponent hJ
  have hP := hqs.1.commutator_eq_top
  let eJ := (J.equivMapOfInjective D.ι D.hinj).trans (MulEquiv.subgroupCongr hJi)
  have hmem := twE6MatFixDim_mem_of_pow_three hK3 hh3 hh1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h24 | h28 | h30 | h36 | h46
  ·
    rcases Nat.lt_or_ge n 2 with hn1 | hn2
    · obtain rfl : n = 1 := by omega
      exact hQ2 K σ hK hσ h hh1 hh3 h24 E hE hcard hfE hEI hnt J hJ hEJ hCJ
    have hq2' : 2 ^ n ≠ 2 := by
      intro h22
      have h21 : 2 ^ n = 2 ^ 1 := h22.trans (pow_one 2).symm
      have := Nat.pow_right_injective (le_refl 2) h21
      omega
    by_cases hin : twistedE6InndiagConj K σ h ∈ twistedE6Inn K σ
    · obtain ⟨s, hs, hs3, -, hsd⟩ := exists_inner_of_mem_twistedE6Inn hσ hK hq2 hh3 hh1 hin
      rw [← hs] at hfE hJ hCJ
      exact (false_of_inner_threeA2 hK3 hσ hK h3 hq2' hs3 (hsd.trans h24) hE hcard hEI hfE hJ
        hEJ hCJ).elim
    obtain ⟨-, -, hm⟩ := D.rationalComponent_a2out h24 h3 hq2' hin i
    rw [hchar, he, mul_comm n 3] at hm
    exact largeEvenMarking_of_mulEquiv eJ
      (largeEvenMarking_k1Labels_of_lieModel hP (Or.inr (Or.inr (Or.inl (Or.inl ⟨by decide, hm⟩)))))
  ·
    exact absurd (e6AdToral_of_conn_line hS D (Or.inl h28) (isElemAbelian_baseChange_comap hinj hE)
      (baseChange_comap_le_adjointGroup E) (baseChange_comap_commute hinj hE hfE)) hnt
  ·
    rcases lieModel_rationalComponent_d4t2 D h3 h30 i with hm | hm
    · rw [hchar, he] at hm
      exact largeEvenMarking_of_mulEquiv eJ (largeEvenMarking_k1Labels_of_lieModel hP (Or.inl hm))
    · rw [hchar, he] at hm
      exact largeEvenMarking_of_mulEquiv eJ
        (largeEvenMarking_k1Labels_of_lieModel hP (Or.inr (Or.inl hm)))
  ·
    have hm := statedClassicalModel_rationalComponent_a5t1 D h3 h36 i
    rw [hchar, he] at hm
    exact largeEvenMarking_of_mulEquiv eJ
      (largeEvenMarking_k1Labels_of_lieModel hP (Or.inr (Or.inr (Or.inr (Or.inl ⟨by decide, hm⟩)))))
  ·
    exact absurd (e6AdToral_of_conn_line hS D (Or.inr h46) (isElemAbelian_baseChange_comap hinj hE)
      (baseChange_comap_le_adjointGroup E) (baseChange_comap_commute hinj hE hfE)) hnt

theorem ggTwE6SCFourLabelsKnown_of_inputs (hS : E6LeviThreeToralBar)
    (hQ2 : GGTwE6K1ThreeA2Two) : GGTwE6SCFourLabelsKnown :=
  ggTwE6SCFourLabelsKnown_of_ad (ggTwE6SCFourLabelsAd_of_line (ggTwE6K1LineLabels_of hS hQ2))

end CFSG.StandardType.SCFourCover

end
