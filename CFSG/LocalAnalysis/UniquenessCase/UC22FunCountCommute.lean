module

public import CFSG.ClassicalInvolution.RouteD.MultiStarModel
import CFSG.ClassicalInvolution.ModelFacts.FundamentalSL2All
import CFSG.ClassicalInvolution.ModelFacts.CF3A
import CFSG.ClassicalInvolution.Q3.Q3WASTLift
import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.ExcModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD


theorem commutes_modelFund_of_commutes_map {p : ℕ} [Fact p.Prime] {t : StatedLieTag}
    {n f : ℕ} (hp2 : p ≠ 2) (hfund : IsFundTag t)
    (hadm : StatedLieAdmissible t n p f) {X : Type} [Group X]
    (ψ : (modelUniv t n p f Fact.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p f Fact.out).K)
    {R S : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ ModelFund p t n f) (hc : Commutes (R.map ψ) (S.map ψ)) :
    Commutes R S := by
  by_cases hq : 5 ≤ p ^ f
  · exact CFSG.ClassicalInvolution.Asc77.ih8_commutes_of_commutes_map ψ hker
      (CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core t n p f hp2 hfund hadm
        (by omega) R hR) hc
  · obtain ⟨hp3, hf1⟩ := Nat.prime_three.pow_eq_iff.mp
      ((CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.eq_three_or_five_le_of_odd_prime_pow
        Fact.out hp2 hadm.2.1).resolve_right hq)
    subst p
    subst f
    have hcop := CFSG.ClassicalInvolution.Q3.Q3W.ker_not_dvd_three_model hfund hadm ψ hker
    have hker3 : ∀ x ∈ ψ.ker, x ^ 3 = 1 → x = 1 := by
      intro x hx hx3
      have hord : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
      rcases (Nat.dvd_prime Nat.prime_three).mp hord with h | h
      · exact orderOf_eq_one_iff.mp h
      · exact (hcop x hx (by rw [h])).elim
    have hgen : CFSG.ClassicalInvolution.ModelFacts.Gen3 R := by
      rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
          (by omega) hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
      · exact CFSG.ClassicalInvolution.ModelFacts.gen3_of_equiv_sl2 eR
      · exact CFSG.ClassicalInvolution.ModelFacts.gen3_of_equiv_sl2 eR
    intro a ha b hb
    exact CFSG.ClassicalInvolution.ModelFacts.commute_of_map_commute_of_gen3 ψ hker hker3 hgen
      (fun a' ha' => hc (ψ a') (Subgroup.mem_map_of_mem ψ ha') (ψ b)
        (Subgroup.mem_map_of_mem ψ hb)) a ha

end CFSG.LocalAnalysis.UniquenessCase.UC22
