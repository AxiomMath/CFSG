module

public import CFSG.Quasithin.EmptyFaithful.S1421QA22Defs
public import CFSG.LargeExtraspecial.S8CBFL3

public section

namespace CFSG.Quasithin

open Subgroup Matrix CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification.OutcomeLocal

theorem isSolvable_centralizer_sl_three {K : Type} [Field K] [Finite K] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) [CharP K 2] {s : SpecialLinearGroup (Fin 3) K}
    (hs : s * s = 1) (hs1 : s ≠ 1) :
    Group.IsSolvable (centralizer ({s} : Set (SpecialLinearGroup (Fin 3) K))) := by
  obtain ⟨hW, hL⟩ := LargeExtraspecial.S8.finrank_dispRange_dispKer hs hs1
  have hB := LieType.SteinbergBR.isSolvable_stabilizer_inf_stabilizer Nat.prime_two hK
    (dispRange_le_dispKer hs) hW hL
  have hle : centralizer ({s} : Set (SpecialLinearGroup (Fin 3) K)) ≤
      stabilizer (dispRange s) ⊓ stabilizer (dispKer s) := fun c hc =>
    LargeExtraspecial.S8.mem_stabilizer_inf_of_commute (mem_centralizer_singleton_iff.mp hc)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)

theorem l3InvCentSolvable_holds : L3InvCentSolvable := by
  intro n Y _ _ hn hY t ht1 ht2
  have hto : orderOf t = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  rcases hY with hpsl | ⟨K, _, _, hK, ⟨e⟩⟩
  · exact LargeExtraspecial.S8.isSolvable_centralizer_of_lieModel_psl_three (f := n)
      (Or.inl ⟨by decide, hpsl⟩) hto
  · have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn hK
    let e' : Y ≃* SpecialLinearGroup (Fin 3) K :=
      e.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    refine LargeExtraspecial.S8.isSolvable_centralizer_of_mulEquiv e' ?_
    exact isSolvable_centralizer_sl_three hK (by rw [← map_mul, ht2, map_one])
      (fun h => ht1 (e'.injective (by rw [h, map_one])))

end CFSG.Quasithin
