module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieG2Trans
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieD4Trans

public section

open CFSG.Blueprint

namespace CFSG.Quasithin.H13.NQCore

theorem d4Even_simple :
    ∀ n : ℕ, NoOddCfg fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n := by
  intro n A _ _ p _ L P T hp5 hL hcfg
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U⟩ : Nonempty (Sylow 2 ↥L) := inferInstance
  refine G2.false_of_borel_data hp5 hcfg (MulEquiv.refl ↥L) (U := (U : Subgroup ↥L))
    (B := Subgroup.normalizer ((U : Subgroup ↥L) : Set ↥L)) U.isPGroup' U.not_dvd_index ?_ ?_ ?_
  · intro a H ha hUH hH
    exact D4.le_normalizer_of_card_eq_prime hL U (Fact.out : p.Prime) hp5 ha hUH hH
  · exact D4.commutator_mem_of_mem_normalizer hL U
  · intro α hα
    exact CFSG.Quasithin.F134.LieD4.exists_inv_mul_pow_mem_of_map_eq hL U α hα

end CFSG.Quasithin.H13.NQCore
