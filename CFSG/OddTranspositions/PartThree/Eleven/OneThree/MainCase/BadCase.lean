module

public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.Timmesfeld.Bridge.Asc72Local
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.SixOne
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.WreathKey
import CFSG.OddTranspositions.PartThree.Eleven.OneThree.MainCase.OFourLine
import CFSG.OddTranspositions.PartThree.EightEight.ClosedBlocks
import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc73Quotient

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

theorem commute_of_mem_alpha_of_commute
    (h86 : Lemma8_6) (h87 : Theorem8_7) {X : Type} [Group X]
    [Finite X] {E : Set X} (hY : HypothesisC E)
    (hrad : ∀ N : Subgroup X, N.Normal → Group.IsSolvable N → N = ⊥) {N : Subgroup X}
    (hN : Odd (Nat.card N)) (hle : N ≤ Subgroup.closure (commSet E hY.d))
    (hnorm : ∀ t ∈ centSet E hY.d, ∀ n ∈ N, t * n * t⁻¹ ∈ N)
    (hdN : ∀ n ∈ N, Commute hY.d n) {a : X} (ha : a ∈ hY.alpha) (had : a ≠ hY.d)
    (hcomm : Commute a hY.d) : ∀ n ∈ N, Commute a n := by
  intro n hn
  by_cases hO4 : O4PairData X E
  ·
    have hNbot : N = ⊥ :=
      eq_bot_of_o4PairData hO4 hY.hd hN hle
        (fun t ht n hn => hnorm t ⟨ht.1, ht.2.1⟩ n hn)
    have hn1 : n = 1 := by simpa [hNbot] using hn
    rw [hn1]
    exact Commute.one_right a
  ·
    have hSodd : IsOddTransp (centSet E hY.d) := hY.setup.oddT.mono fun _ hx => hx.1
    have hstab : ∀ n ∈ N, n * a * n⁻¹ ∈ centSet E hY.d := by
      intro n hn
      refine ⟨hY.setup.normal n a (hY.isBlock_alpha.subset ha), ?_⟩
      have hnd : Commute n hY.d := (hdN n hn).symm
      exact (hnd.mul_left hcomm).mul_left hnd.inv_left
    have hu : a ∈ centSet E hY.d := ⟨hY.isBlock_alpha.subset ha, hcomm⟩
    have hgen : a ∈ Subgroup.closure (commSet (centSet E hY.d) a) := by
      by_cases hK : blockKernel hY.alpha = ⊥
      ·
        have hF : FaithfulOnBlocks hY.alpha :=
          faithfulOnBlocks_iff_blockKernel_eq_bot.mpr hK
        have hmul : a * hY.d ∈ E :=
          EightEight.mul_mem_of_commute_of_mem_of_mem h86 h87 hY hrad hO4 hF
            (mem_blockClass_self hY.alpha) ha hY.d_mem_alpha had hcomm
        exact mem_closure_commSet_centSet_of_mul_mem hY.hd
          (hY.setup.oddT.ne_one hY.hd) had hcomm hmul
      · exact mem_closure_commSet_centSet_of_blockKernel_ne_bot hY hrad hK ha
          hY.d_mem_alpha had hcomm
    exact commute_of_mem_closure_commSet_of_odd hSodd hN hnorm hu hstab hgen n hn

end CFSG.OddTranspositions.PartThree.ElevenThree
