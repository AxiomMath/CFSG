module

public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C5
public import CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp.SL364C8

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.Sec4.Res6L364 (K64 card_K64)

theorem ks1012AutHyp_sl364_K64 (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K64)))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) : Conc (CFSG.Open.StatedSL 3 K64) F := by
  by_cases h : ∃ g ∈ F, Dhom K64 g ∉ linearAutGroup 3 K64
  · exact conc_of_not_linear hF h
  · push Not at h
    exact conc_of_linear hF h

@[expose] noncomputable def statedSLEquivOfRingEquiv {K K' : Type} [Field K] [Field K']
    (e : K ≃+* K') : CFSG.Open.StatedSL 3 K ≃* CFSG.Open.StatedSL 3 K' :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm.trans
    ((CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldEquiv (Fin 3) e).trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K'))

theorem ks1012AutHyp_sl364 {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64)
    (F : Subgroup (MulAut (CFSG.Open.StatedSL 3 K))) (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup (CFSG.Open.StatedSL 3 K),
      V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card K64 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, card_K64]
  let ε : K ≃+* K64 := FiniteField.ringEquivOfCardEq hcard
  refine conc_of_conc_map (statedSLEquivOfRingEquiv ε) F ?_
  exact ks1012AutHyp_sl364_K64 _ (CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map _ hF)

theorem ks1012AutHyp_sl364_of_mulEquiv {K : Type} [Field K] [Finite K] (hK : Nat.card K = 64)
    (Q : Type) [Group Q] (e : Q ≃* CFSG.Open.StatedSL 3 K) (F : Subgroup (MulAut Q))
    (hF : CFSG.Assembly.IsElemAbelian 3 F) :
    ∃ F' ≤ F, Nat.card F ≤ 3 * Nat.card F' ∧ ∃ V : Subgroup Q, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ f ∈ F', ∀ v ∈ V, f v ∈ V := by
  refine conc_of_conc_map e F ?_
  exact ks1012AutHyp_sl364 hK _ (CFSG.RankThree.PartTwo.Sec4.isElemAbelian_map _ hF)

end CFSG.RankThree.PartTwo.Sec10.KS1012AutHyp

end
