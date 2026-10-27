module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150SporCore
import CFSG.Quasithin.Background.A318POutHe
import CFSG.RankThree.PartTwo.KFacts.K426RestMcL
import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHComp
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThreeData
public import CFSG.Sporadic.HeldB.CertPChain
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeTc

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem k150s_mcl {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .McL) := by
  refine k150s_row_of_native CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  have : Finite (Blueprint.NativeSporadic.Carrier .McL) := Finite.of_equiv S e.toEquiv
  refine k150s_noCfg_of_model (G' := Blueprint.NativeSporadic.McL) e
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (RonanK429H.not_three_dvd_outer_of_mulEquiv e
      (RonanK429H.not_three_dvd_outer_of_le_two Sec4.card_outer_McL))
    fun y hy => k150s_goodFor_of_prime_not_dvd hJ.seven_dvd ?_
  rcases KFacts.K426Rest.mclThreeCentralizerCard y hy with h | h <;> rw [h] <;> norm_num

section He

open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He (bOf heThreeWordsA heThreeWordsB bigDataA bigDataB
  orderOf_bOf three_conj_cases card_cent_B)
open CFSG.AGLEmbeddingD2.Wilson.Census219 (heTcQ heTcQ_eq heTc_spec)
open CFSG.Sporadic.HeldB (heP heEquivP)
open CFSG.Sporadic.Schreier (centralizerIn centralizerIn_conj)

theorem k150s_he {J : Type} [Group J] (hJ : K150sTgt J) :
    RowOfK150 J (Spor .He) := by
  have := hJ.simple.toNontrivial
  refine k150s_row_of_native CFSG.Sporadic.Bridge.He.nonempty_mulEquiv ?_
  intro S _ _ hs hna ⟨e⟩
  have := hs
  refine k150s_noCfg_of_subgroupModel (e.trans heEquivP)
    (RonanK429H.center_eq_bot_of_simple_nonab hna)
    (CFSG.Quasithin.A318P.not_dvd_outer_He e Nat.prime_three (by norm_num)) fun x hx hx3 => ?_
  rcases three_conj_cases hx hx3 with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  ·
    have hA3 : bOf heThreeWordsA ^ 3 = 1 := by
      have := pow_orderOf_eq_one (bOf heThreeWordsA)
      rwa [orderOf_bOf bigDataA] at this
    have hQ : Subgroup.centralizer ({bOf heThreeWordsA} : Set (Equiv.Perm (Fin 8330))) ⊓ heP =
        heTcQ := by
      rw [inf_comm]
      exact heTcQ_eq.symm
    have hbase : GoodFor J (Subgroup.centralizer
        ({bOf heThreeWordsA} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) := by
      rw [hQ]
      obtain ⟨-, hq, hc3, -⟩ := heTc_spec
      exact k150s_goodFor_of_isQuasisimple hq (by rw [hc3])
    simpa using k150s_goodFor_conj (J := J) hc hA3 (e := 1) (Or.inl rfl) hbase
  ·
    have h504 : Nat.card ↥(Subgroup.centralizer
        ({c * bOf heThreeWordsB * c⁻¹} : Set (Equiv.Perm (Fin 8330))) ⊓ heP) = 504 := by
      rw [inf_comm]
      change Nat.card ↥(centralizerIn heP (c * bOf heThreeWordsB * c⁻¹)) = 504
      rw [centralizerIn_conj _ hc, Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact card_cent_B
    refine k150s_goodFor_of_not_dvd (hJ.not_dvd ?_ ?_) <;> rw [h504] <;> norm_num

end He

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
