module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFIdDisp

public section

namespace CFSG.Quasithin.SBd19F

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.OddCover CFSG.Quasithin

theorem identOddL2_holds : IdentOddL2 := by
  intro S _ _ p f hp hp2 hf _ _ ⟨Q, hQ⟩ hmod ⟨w, _, K, _, hK⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := hmod
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hcard, -, -, -, hcyc⟩ := odd_psl_two_sylow_data hp2 hF
  by_cases hp3 : p = 3
  · subst hp3
    have hS : Nat.card S = 3 ^ f * (((3 ^ f) ^ 2 - 1) / 2) := by
      rw [Nat.card_congr e.toEquiv, hcard]
    have hdvd : 168 ∣ Nat.card S := by
      rw [← SBc11.card_of_isPSL_three_two hK]
      exact Subgroup.card_subgroup_dvd_card _
    rcases hf with rfl | rfl <;> norm_num at hS <;> omega
  · apply hQ
    have hR := hcyc 3 Nat.prime_three (by norm_num) (Ne.symm hp3)
      (Q.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hR' : IsCyclic ↥((Q : Subgroup S).map e.toMonoidHom) := hR
    let e' := (Q : Subgroup S).equivMapOfInjective e.toMonoidHom e.injective
    have := hR'
    exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

end CFSG.Quasithin.SBd19F
