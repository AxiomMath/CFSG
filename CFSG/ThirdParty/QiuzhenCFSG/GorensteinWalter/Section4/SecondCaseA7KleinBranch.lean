module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseA7KleinFourLeTwoCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26

namespace CFSG
end CFSG
open CFSG

/-!
# Selecting the Klein-four branch of Theorem 2.6
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The A7 component forces Theorem 2.6's Klein-four / `D6` alternative. -/
public theorem secondCase_a7_klein_branch
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (hA7 : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃*
      alternatingGroup (Fin 7)))
    (hmodel : d.model = ComponentQuotientModel.alternating hA7) :
    IsKleinFour (pCore 2 c.Hhat) ∧
      Nonempty
        ((c.Hhat ⧸ (pCore 2 c.Hhat ⊔ pPrimeCore 2 c.Hhat)) ≃*
          DihedralGroup 3) := by
  have h26 : CentralizerStructure c := theorem_2_6 hmin c
  rcases h26.2.2 with hcyclic | hklein
  · obtain ⟨V, hVK, hVleCore⟩ :=
      secondCase_a7_exists_kleinFour_le_twoCore_Hhat
        hmin c w d hA7 hmodel
    have hVleS0 : V ≤ c.S0 := hVleCore.trans hcyclic.1
    let : IsCyclic c.S0 := c.S0_cyclic
    have hVcyclic : IsCyclic V := Subgroup.isCyclic_of_le hVleS0
    let : IsKleinFour V := hVK
    exact False.elim (IsKleinFour.not_isCyclic hVcyclic)
  · exact hklein

end CFSG.GorensteinWalter
