module

public import CFSG.Quasithin.Background.GoldschmidtTDE68L2pPsl
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8L33
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.LieType.SteinbergBROddLinearThreeInvolution
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin.E6.L2p

open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.K1
  CFSG.ComponentClassification.CatLeaf CFSG.Assembly.LowTwoRank

theorem psl2_five_facts {X : Type} [Group X]
    (hmodel : StatedClassicalModel X .PSL 2 5 1) :
    SylowCentralizingAutInner X ∧ InvolutionCentralizersComponentFree X := by
  have h4 : StatedClassicalModel X .PSL 2 2 2 :=
    Ch1.statedClassicalModel_psl_two_four_of_alternating_five X
      (Setup.Family.alternating_five_of_model_five hmodel)
  exact ⟨Ch1.sylowCentralizingAutInner_of_stated_psl_two (by norm_num) h4,
    involutionCentralizersComponentFree_psl h4⟩

theorem psl3_three_facts
    {X : Type} [Group X] [Finite X]
    (hmodel : StatedClassicalModel X .PSL 3 3 1) :
    SylowCentralizingAutInner X ∧ InvolutionCentralizersComponentFree X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfix := (Unc25L33.l33_facts X hmodel).2
  obtain ⟨-, ⟨θ⟩⟩ :=
    CFSG.ComponentClassification.ClassicalModelStatedBridge.classicalModel_psl_of_stated hmodel
  let e : X ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 3 1) :=
    θ.trans (LocalAnalysis.ComponentInitial.LinearFieldFour.pslModelEquivProjectiveSL 3 3 1)
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero, pow_one]
  refine ⟨L2p.sylowCentralizingAutInner_of_fixPointwiseInner hfix,
    InvolutionCentralizersComponentFree.of_mulEquiv e
      (involutionCentralizersComponentFree_of_solvable fun t ht => ?_)⟩
  obtain ⟨-, hcard, -, -⟩ :=
    (LieType.unique_odd_linear_three_involution_centralizer_component_or_unique_core_involution
      (K := GaloisField 3 1) (by rw [hK3]; exact ⟨1, rfl⟩) (by rw [hK3]) t ht).2 hK3
  have := Fintype.ofFinite ↥(centralizer ({t} : Set
    (LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 3 1))))
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (p := 2) (q := 3)
    (a := 4) (b := 1) Nat.prime_two Nat.prime_three (by norm_num)
    (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)

end CFSG.Quasithin.E6.L2p
