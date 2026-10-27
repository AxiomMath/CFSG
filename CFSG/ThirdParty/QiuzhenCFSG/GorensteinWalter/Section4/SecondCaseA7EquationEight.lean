module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaStrictIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaEqualityIndex
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaInversionEndpoint
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7OmegaTrichotomy

namespace CFSG
end CFSG
open CFSG

/-! # Equation (8) in the A7 branch -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The equation-(6) fixed subgroup together with `F(U)` has relative index
at most three in `U`. -/
public theorem secondCase_a7_equation_eight
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseA7OmegaData c w d) :
    (od.B ⊔ c.FU).relIndex c.U ≤ 3 := by
  rcases secondCase_a7_omega_trichotomy c w d od with
    heq | ⟨hlt, _hcard⟩ | ⟨hFnotleQ, hinvQ⟩
  · exact secondCase_a7_omega_equality_relIndex_le_three c w d od heq
  · exact secondCase_a7_omega_strict_relIndex_le_three c w d od hlt
  · have hUeq :=
      secondCase_a7_omega_inversion_eq c w d od hFnotleQ hinvQ
    rw [← hUeq]
    simp

end CFSG.GorensteinWalter
