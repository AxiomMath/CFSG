module

public import CFSG.OddTranspositions.PartThree.EightEight.Star
public import CFSG.OddTranspositions.WreathBase
public import CFSG.OddTranspositions.PartThree.Ten.WreathEndgame
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.EightEight.WreathBlocks
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.OddTranspositions.PartThree.HalphaConj

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ
open CFSG.OddTranspositions.PartThree.WreathEndgame

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_rebase_of_l2Wreath (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f k : ℕ} (hf : 2 ≤ f) (hk : k = 3 ∨ k = 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f k)
    {x w y : G} (ht : IsTriangle D x w y) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha)
    (hx : x ∈ DalphaStar D ρ) (hw : w ∈ DalphaStar D ρ) (hy : y ∈ DalphaStar D ρ)
    {n : ℕ} (hn : Odd n) (hord : orderOf (x * y * w) = 2 * n) :
    ∃ (hC' : HypothesisC D)
      (φ' : (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) ≃* L2Wreath f k)
      (t : Halpha D hC'.alpha),
      hC'.alpha = ρ ∧ (t : G) = (x * y * w) ^ n ∧
        φ' (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC'.alpha)) t) ∈ swapSet f k := by
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hρ
  let hC' : HypothesisC D := hC.conj g
  have hα' : hC'.alpha = ρ := (HypothesisC.conj_alpha hC g).trans hg.symm
  have hns' : ¬ Group.IsSolvable (Halpha D hC'.alpha) :=
    not_isSolvable_Halpha_conj hC g hns
  have hF' : FaithfulOnBlocks hC'.alpha := faithfulOnBlocks_conj_alpha hC g hF
  have hne' : derivedSeries (Halpha D hC'.alpha) 1 ≠ derivedSeries (Halpha D hC'.alpha) 2 :=
    derivedSeries_Halpha_conj_ne hC g hne
  let e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) :=
    QuotientGroup.congr _ _ (conjEquiv hC g) (conjRadical_map hC g)
  let φ' : (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) ≃*
      L2Wreath f k := e.symm.trans φ
  have hx' : x ∈ DalphaStar D hC'.alpha := by rw [hα']; exact hx
  have hw' : w ∈ DalphaStar D hC'.alpha := by rw [hα']; exact hw
  have hy' : y ∈ DalphaStar D hC'.alpha := by rw [hα']; exact hy
  exact ⟨hC', φ', ⟨(x * y * w) ^ n, mul_mul_pow_mem_Halpha hC' hx' hw' hy' n⟩, hα', rfl,
    mem_swapSet_of_l2Wreath h86 h87 hC' hrad hO4 hF' hne' hns' hf hk φ' ht hx' hw' hy'
      hn hord rfl⟩

end CFSG.OddTranspositions.PartThree.EightEight
