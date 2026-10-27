module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147Excl
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147

open CFSG.Open

theorem orderOf_two_zmod_nineteen : orderOf (2 : ZMod 19) = 18 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

private theorem facts_walterJ1 : Facts walterJ1 19 where
  simple := CFSG.Walter.J1Props.J1_simple
  exists_involution := by
    haveI : Finite walterJ1 :=
      Nat.finite_of_card_ne_zero (by rw [CFSG.Walter.J1Props.J1_card]; norm_num)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_prime_orderOf_dvd_card' 2 (by rw [CFSG.Walter.J1Props.J1_card]; norm_num)
  inverts s hs := by
    obtain ⟨hss, hs1⟩ := mul_self_and_ne_one hs
    obtain ⟨c, hc⟩ := CFSG.QuasithinUnique.Setup.X1.walterJ1_dihedral s hss hs1
    refine ⟨s * (c * s * c⁻¹), hc, ?_⟩
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    calc s * (s * (c * s * c⁻¹)) * s⁻¹ = (s * s) * (c * s * c⁻¹) * s⁻¹ := by group
      _ = c * s * c⁻¹ * s⁻¹ := by rw [hss, one_mul]
      _ = c * s⁻¹ * c⁻¹ * s⁻¹ := by rw [hsinv]
      _ = (s * (c * s * c⁻¹))⁻¹ := by group
  inner α _ := CFSG.QuasithinUnique.Setup.X1.walterJ1_autInner α

theorem facts_of_isJ1 {X : Type} [Group X] (hX : IsJ1 X) : Facts X 19 := by
  obtain ⟨e⟩ := hX
  exact facts_walterJ1.of_mulEquiv (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm

end CFSG.LocalAnalysis.UniquenessCase.UC22.Excl147
