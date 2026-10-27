module

public import CFSG.LocalAnalysis.StandardType.GGTwE6A5KTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviDefs
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KType
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KModel
import CFSG.LocalAnalysis.StandardType.GGTwE6A5KToral
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LineAux
import CFSG.LocalAnalysis.StandardType.GGTwE6K1LeviMain
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24ConnLine

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.NoOffTwE6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24


theorem ggTwE6A5KLine_of (hS : E6LeviThreeToralBar) : GGTwE6A5KLine := by
  intro n hn h3 K _ _ σ hK hσ h hh1 hh3 E hE hcard hfE hEI hnt J hJ hEJ hCJ hmark hCL
  have hq2 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h36 := twE6MatFixDim_eq_36_of_twA5 hS hn h3 hK hσ hh1 hh3 hE hcard hfE hEI hnt hJ hEJ hCJ
    hmark
  obtain ⟨C, hC, ψ, σ', B, hψ, hXM, hB, hBc⟩ :=
    exists_frame_commute_of_commLifts hn h3 hK hσ hh1 hh3 h36 hE hfE hJ hEJ hCL
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hL3 : ((3 : ℕ) : AlgebraicClosure K) ≠ 0 := by
    intro h0
    have h23 := (CharP.cast_eq_zero_iff (AlgebraicClosure K) 2 3).1 h0
    omega
  have hinj : Function.Injective (twistedE6InndiagConj K σ) :=
    twE6_conj_injective K σ (2 ^ n) hσ hK hq2
  exact hnt ((e6AdToral_map_conj hC _).1 (e6AdToral_of_frame_commute hL3 hψ
    ((isElemAbelian_baseChange_comap hinj hE).map _) hXM B hB hBc))

theorem ggTwE6A5KKnown_of_inputs (hS : E6LeviThreeToralBar) : GGTwE6A5KKnown :=
  ggTwE6A5KKnown_of_ad (ggTwE6A5KAd_of_line (ggTwE6A5KLine_of hS))

theorem ggTwE6A5KKnown_holds : GGTwE6A5KKnown :=
  ggTwE6A5KKnown_of_inputs e6LeviThreeToralBar

end CFSG.StandardType.SCFourCover

end
