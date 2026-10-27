module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearPNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The fixed-factor centralizer of the selected order-`p` subgroup

The centralizer of `P` inside `F(U)` is `F ⊔ K₀`: the forward inclusion
uses `N_G(P)=M` and the equation-(3) decomposition
`F(U) ∩ M = K₀ ⊔ F`; the reverse inclusion follows from
`P ≤ F ≤ C_G(E)` and `K₀ ≤ E`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The `F(U)`-centralizer of the selected order-`p` subgroup is the
fixed/inverted-factor join. -/
public theorem secondCase_linear_P_centralizer_FU_eq_sup
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    (Subgroup.centralizer (od.P : Set G)) ⊓ c.FU = od.F ⊔ od.K0 := by
  let : Fact (Nat.Prime od.p) := ⟨od.hp_prime⟩
  have hPnorm : Subgroup.normalizer (od.P : Set G) = w.M :=
    secondCase_linear_P_normalizer_eq_M c w d od
  have hFleFU : od.F ≤ c.FU := by
    intro x hx
    rw [od.F_fixed] at hx
    exact hx.1.1
  have hK0leFU : od.K0 ≤ c.FU := by
    rw [od.K0_eq]
    exact inf_le_left
  have hK0leE : od.K0 ≤ d.E := by
    rw [od.K0_eq]
    exact inf_le_right.trans od.K_le_E
  have hPcentF : od.F ≤ Subgroup.centralizer (od.P : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpF : p ∈ od.F := od.P_le_F hp
    let : IsCyclic (↥od.F) := od.F_cyclic
    let : CommGroup (↥od.F) := IsCyclic.commGroup
    have hfP : (⟨f, hf⟩ : od.F) * ⟨p, hpF⟩ =
        ⟨p, hpF⟩ * ⟨f, hf⟩ := mul_comm _ _
    exact (congrArg Subtype.val hfP).symm
  have hPcentK0 : od.K0 ≤ Subgroup.centralizer (od.P : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    have hpcent : p ∈ Subgroup.centralizer (d.E : Set G) :=
      od.F_centralizes_E (od.P_le_F hp)
    exact ((Subgroup.mem_centralizer_iff.mp hpcent) (k : G) (hK0leE hk)).symm
  apply le_antisymm
  · intro x hx
    have hxN : x ∈ Subgroup.normalizer (od.P : Set G) :=
      (Subgroup.centralizer_le_normalizer (od.P : Set G)) hx.1
    have hxM : x ∈ w.M := hPnorm ▸ hxN
    have hx' : x ∈ c.FU ⊓ w.M := ⟨hx.2, hxM⟩
    rw [← od.FU_inter_M_eq] at hx'
    simpa [sup_comm] using hx'
  · intro x hx
    refine ⟨(sup_le hPcentF hPcentK0) hx,
      (sup_le hFleFU hK0leFU) hx⟩

end CFSG.GorensteinWalter
