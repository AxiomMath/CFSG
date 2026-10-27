module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearCenterless

namespace CFSG
end CFSG
open CFSG

/-!
# The external prime factor meets the linear component trivially
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Since `P ≤ F ≤ C_G(E)` and the linear component is centerless,
`P ∩ E = 1`. -/
public theorem secondCase_linear_P_inf_E_eq_bot
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (e : Nonempty ((d.E ⧸ Subgroup.center d.E) ≃* PSL2 K))
    (post : SecondCaseLinearPostNineData c w d K) :
    post.od.P ⊓ d.E = ⊥ := by
  have hZ : Subgroup.center d.E = ⊥ :=
    secondCase_linear_center_eq_bot hmin c w d K hK e post
  apply le_bot_iff.mp
  intro x hx
  have hxcent : x ∈ Subgroup.centralizer (d.E : Set G) :=
    post.od.F_centralizes_E (post.od.P_le_F hx.1)
  have hxZ : (⟨x, hx.2⟩ : d.E) ∈ Subgroup.center d.E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hxcent (y : G) y.2
  rw [hZ] at hxZ
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hxZ))

end CFSG.GorensteinWalter
