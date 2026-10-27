module

public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.PartThree.Statements
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourFibres
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourPropagation
import CFSG.OddTranspositions.PartThree.EightEight.WreathFourComponent
import CFSG.OddTranspositions.PartThree.EightEight.Kernel
import CFSG.OddTranspositions.PartThree.HalphaConj
import CFSG.OddTranspositions.PartThree.Eleven.OneOne.ConjShared
import CFSG.OddTranspositions.PartFour.Line
import CFSG.Timmesfeld.Bridge.Asc72Minimal

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem commute_of_reflTransGen_w4t (hC : HypothesisC D)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha)
    {β β' : Set G} (hβ : β ∈ Dalpha D hC.alpha) (hβ' : β' ∈ Dalpha D hC.alpha)
    {b b' : Halpha D hC.alpha} (hb : (b : G) ∈ β) (hb' : (b' : G) ∈ β')
    (hbb' : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) b') :
    ∀ γ : Set G, Relation.ReflTransGen (DalphaAdj D β) hC.alpha γ →
      ∀ x ∈ γ, Commute (b' : G) x := by
  intro γ hγ x hx
  have hγ' : γ ∈ Dalpha D β' :=
    (mem_Dalpha_and_mk_eq_of_reflTransGen hC hns hf (Or.inr rfl) φ hB hA hβ hβ'
      hb hb' hbb' hγ).1
  exact (mem_Dalpha_iff.mp hγ').2.2.2 (b' : G) hb' x hx

theorem solvableRadical_le_center_of_l2Wreath_four (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ QZ.O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hns : ¬ Group.IsSolvable (Halpha D hC.alpha)) {f : ℕ} (hf : 2 ≤ f)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f 4)
    (hB : BlocksInCosets D hC.alpha) (hA : FibresAnticlique D hC.alpha) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha) := by
  by_contra hMZ
  obtain ⟨β, hβ, β', hβ', hne, b, b', hb, hb', hbb'⟩ :=
    exists_ne_mem_Dalpha_mk_eq_of_not_le_center h87 hC hrad hO4 hF hMZ
  have hZ : Subgroup.center G = ⊥ := eq_bot_of_le_center hrad le_rfl
  have hcomm := commute_of_reflTransGen_w4t hC hns hf φ hB hA hβ hβ' hb hb' hbb'
  obtain ⟨g, hgα, -⟩ := exists_conj_alpha_eq_and_d_eq hC hβ.1 hb
  let hC' : HypothesisC D := hC.conj g
  have hC'α : hC'.alpha = β := hgα
  have hB' : BlocksInCosets D hC'.alpha := by
    rw [hC'α]
    exact BlocksInCosets.of_mem_blockClass hC.setup.normal hB hβ.1
  have hA' : FibresAnticlique D hC'.alpha := by
    rw [hC'α]
    exact FibresAnticlique.of_mem_blockClass hC.setup.normal hA hβ.1
  have hns' : ¬ Group.IsSolvable (Halpha D hC'.alpha) :=
    not_isSolvable_Halpha_conj hC g hns
  let e : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃*
      (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) :=
    QuotientGroup.congr _ _ (conjEquiv hC g) (conjRadical_map hC g)
  let φ' : (Halpha D hC'.alpha ⧸ CFSG.solvableRadical (Halpha D hC'.alpha)) ≃*
      L2Wreath f 4 := e.symm.trans φ
  have hδα : hC.alpha ∈ Dalpha D β :=
    CFSG.OddTranspositions.PartFour.mem_Dalpha_symm hβ hC.isBlock_alpha.1
  have hmem : (b' : G) ∈ hC'.alpha ∪ DalphaStar D hC'.alpha :=
    mem_union_DalphaStar_of_commute_reflTransGen (hC := hC') hZ hns' hf φ' hB' hA'
      (δ := hC.alpha) (by rw [hC'α]; exact hδα)
      (d := (b' : G)) ((mem_Dalpha_iff.mp hβ').2.1 hb')
      (by
        intro ρ hρ x hx
        exact hcomm ρ (by rwa [hC'α] at hρ) x hx)
  rw [hC'α] at hmem
  exact notMem_union_DalphaStar_of_mk_eq hC.isBlock_alpha hA hβ hβ' hne hb hb' hbb' hmem

end CFSG.OddTranspositions.PartThree.EightEight
