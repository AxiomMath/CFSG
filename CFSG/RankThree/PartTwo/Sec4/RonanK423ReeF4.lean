module

public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofHelpers
public import CFSG.RankThree.PartTwo.Sec19.SeitzG2F4ReeF4Three
public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
public import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.ReeF4ThreeAux.SU3
public import CFSG.RankThree.PartTwo.Sec4.Item417Res6ProofU4

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK423

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Res423Two
open CFSG.LieType.Ree CFSG.Blueprint.Chevalley CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Sec8 CFSG.RankThree.PartTwo.Sec21
open CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

theorem census423_of_twistedF4
    {X : Type} [Group X] [Finite X] {f : ℕ} (hX : Blueprint.ReeTitsModel X .twistedF4 2 f) :
    Census423 X := by
  classical
  obtain ⟨-, a, ha, hfa, K, _, _, hchar, hK, ⟨e⟩⟩ := exists_mulEquiv_reeGamma hX
  have hfin : Finite (ModGL ReeTag.F4.tag K) := CFSG.LieType.Chevalley.finite_modGL
  have hfinΓ : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hZ : Subgroup.center (ReeTag.F4.reeGamma K a) = ⊥ :=
    ReeTag.large_Ree_fixed_group_center_trivial a K hK
  refine census423_of_alphaVanishes fun D hD hD9 => alphaVanishes_of_mulEquiv e ?_
  have hE : CFSG.Assembly.IsElemAbelian 3 D := hD.prop
  have hE' := isElemAbelian_map' e.toMonoidHom hE
  have hD'9 : Nat.card (D.map e.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective e.injective, hD9]
  have hq : CFSG.IsQuasisimple (unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) :=
    ReeF4ThreeAux.su3_isQuasisimple (by omega) (Res417Six.card_galoisField_two_mul (by omega))
  refine alphaVanishes_of_core hZ (comm_of_isElemAbelian hE') ?_ ?_
  · intro b hb hb1
    have hb3 : orderOf b = 3 :=
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      orderOf_eq_prime (hE'.2 b hb) hb1
    obtain ⟨φ⟩ := Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK b hb3
    refine Item21Res7Proof.theta_eq_bot_of_mulEquiv φ
      (Item21Res7Proof.theta_eq_bot_of_center hq fun z hz => ?_)
    exact ReeF4ThreeAux.pow_three_eq_one_of_mem_center_su3 (by omega)
      (Res417Six.card_galoisField_two_mul (by omega)) hz
  · exact (Sec19.reeF4_cenGen_eq_top_three ha hK _ hE' hD'9).ge

end CFSG.RankThree.PartTwo.Sec4.RonanK423
