module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationNine

namespace CFSG
end CFSG
open CFSG

/-!
# The equation-(3) subgroup embeds in the quotient torus
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The quotient map embeds `K₀` in the selected reflected torus, so
`|K₀|` divides the torus cardinality. -/
public theorem secondCase_linear_K0_card_dvd_quotientTorus
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (Kfield : Type u) [Field Kfield] [Finite Kfield]
    (od : SecondCaseLinearOmegaData c w d)
    (torus : SecondCasePSL2QuotientTorusCard d Kfield) :
    Nat.card od.K0 ∣ Nat.card torus.T := by
  classical
  have hK0leE : od.K0 ≤ d.E := by
    rw [od.K0_eq]
    exact inf_le_right.trans od.K_le_E
  let qE : d.E →* d.E ⧸ Subgroup.center d.E :=
    QuotientGroup.mk' (Subgroup.center d.E)
  let K0bar : Subgroup (d.E ⧸ Subgroup.center d.E) :=
    (od.K0.subgroupOf d.E).map qE
  have hK0bar_le_T : K0bar ≤ torus.T := by
    exact secondCase_equationNine_K0_quotient_le_torus c w d od.s od.K od.K0
      od.K_inverted od.K0_eq hK0leE torus.T torus.T_odd_centralized_le
  let fK0 : od.K0 →* torus.T :=
    { toFun := fun x => ⟨qE ⟨(x : G), hK0leE x.2⟩,
        hK0bar_le_T (Subgroup.mem_map.mpr
          ⟨⟨(x : G), hK0leE x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩)⟩
      map_one' := by
        apply Subtype.ext
        change qE (1 : d.E) = 1
        exact map_one qE
      map_mul' := by
        intro x y
        apply Subtype.ext
        change qE (⟨((x : G) * (y : G)),
          hK0leE (od.K0.mul_mem x.2 y.2)⟩ : d.E) =
            qE (⟨(x : G), hK0leE x.2⟩ : d.E) *
              qE (⟨(y : G), hK0leE y.2⟩ : d.E)
        exact (map_mul qE (⟨(x : G), hK0leE x.2⟩ : d.E)
          (⟨(y : G), hK0leE y.2⟩ : d.E)).symm.trans (by rfl) }
  have hsIE : IsInvolution od.s := by
    constructor
    · intro h
      exact od.s_involution.1 (congrArg Subtype.val h)
    · apply Subtype.ext
      exact od.s_involution.2
  have hfK0inj : Function.Injective fK0 := by
    intro x y hxy
    apply secondCase_equationNine_quotient_injective_on_K0
      c w d od.s od.K od.K0 od.K_inverted od.K0_eq hK0leE hsIE
    exact congrArg Subtype.val hxy
  exact Subgroup.card_dvd_of_injective fK0 hfK0inj

end CFSG.GorensteinWalter
