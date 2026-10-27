module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalCritical
public import CFSG.RankThree.PartOne.S9.Sylow.GlobalRelative

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem sylowTwoAlternatives_of (hIcrA : InitialCriticalAction)
    (hI1 : SelectedPrimeMinimalTwoActionReduction) (hCTCB : CentralizerTwoCoreCommutatorBound)
    (hTGTCA : TrivialGlobalTwoCoreAction) : SylowTwoAlternatives := by
  intro G _ _ p hG A hA hAcard c hcA hc1 T hT hAT
  have hp : p.Prime := hG.prime
  have hp3 : 3 < p := hG.three_lt
  have hp2 : p ≠ 2 := by omega
  by_cases h3 : p = 7 ∧ ∃ q ∈ sigmaA G, 7 < q ∧ 3 < CFSG.pRank q G
  · exact Or.inr (Or.inr h3)
  have hgood : GoodGlobalRank G p := fun h7 q hq hq7 =>
    not_lt.mp fun hlt => h3 ⟨h7, q, hq, hq7, hlt⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  by_cases h1 : ⁅T, A⁆ ≤ inSubgroup (pCore 2) H
  · exact Or.inl h1
  by_cases hex : ∃ a ∈ A, a ≠ 1 ∧ ⁅inSubgroup (pCore 2) (Subgroup.centralizer ({a} : Set G)), A⁆ ≠ ⊥
  swap
  · exfalso
    have hz := hTGTCA G p hG hgood A hA hAcard
      (fun a ha ha1 => by_contra fun hne => hex ⟨a, ha, ha1, hne⟩) c hcA hc1 T hT hAT
    exact h1 (hz ▸ bot_le)
  refine Or.inr (Or.inl ⟨?_, fun b hbA hb1 => hCTCB G p hG hgood A hA hAcard c hcA hc1 b hbA hb1,
    hex⟩)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := (Sec9B.isElementaryAbelian_iff_forall.mp hA).1
  have hAH : A ≤ H := fun x hx => Sec9B.mem_normalizer_zpowers_of_commute (hcomm x hx c hcA)
  have hTH : T ≤ H := hT.1.trans (Subgroup.map_subtype_le _)
  obtain ⟨q, hq, hq2, hqp, R, Q, D, hRT, hcrit⟩ :=
    Sec9B.relative_initialCriticalAction hIcrA H A T hp hp2 hAH hTH hA hAcard hT hAT h1
  have hR2 : IsPGroup 2 ↥R := hT.2.1.to_le hRT
  have hR1 : R ≠ ⊥ := fun h => hcrit.comm_D_ne (by rw [h, Subgroup.commutator_bot_left])
  have hND : ∀ g ∈ Subgroup.normalizer (Q : Set G), g ∈ Subgroup.normalizer (D : Set G) :=
    fun g hg => Sec9B.mem_normalizer_of_characteristic hcrit.D_le_Q hcrit.D_char hg
  have hRAD : R ⊔ A ≤ Subgroup.normalizer (D : Set G) :=
    sup_le (fun r hr => hND r (hcrit.R_normalizes_Q hr))
      (fun a ha => hND a (hcrit.A_normalizes_Q ha))
  have hDD : ⁅⁅D, D⁆, D⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact (Subgroup.commutator_mono le_rfl hcrit.D_le_Q).trans
      (hcrit.comm_D_Q.trans inf_le_right)
  have hidx := Sec9B.relIndex_inf_centralizer_eq hp hAcard hcrit.card_B
  have hpB : p ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (R : Set G)) := by
    rw [hcrit.card_B]
    exact Nat.le_self_pow (by norm_num) p
  exact (hI1 G hG.evenRank_eq p hp hG.mem_sigma hp3 q hq hq2 hqp A R D hA hcrit.A_normalizes hR2
    hcrit.comm_eq hR1 hRAD (Sec9B.isPGroup_of_forall_pow_eq_one hcrit.D_exp) hcrit.D_exp hDD
    hcrit.comm_D_ne hidx hpB (fun U hU hAU hUA => (hcrit.minimal U hU hAU hUA).2) hgood).1

end CFSG.RankThree.PartOne
