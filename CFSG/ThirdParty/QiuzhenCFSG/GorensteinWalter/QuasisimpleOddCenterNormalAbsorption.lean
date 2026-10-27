module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore

namespace CFSG
end CFSG
open CFSG

/-!
# Absorption into a normal subgroup from an involution intersection

A normal subgroup of a quasisimple group is central or total.  If the center
has odd order, an involution in the normal subgroup rules out the central
case.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A quasisimple subgroup with odd center is absorbed by a normal subgroup
of an overgroup when their intersection contains an involution. -/
public theorem quasisimple_le_of_normal_intersection_involution
    {G : Type u} [Group G]
    (E L N : Subgroup G) (hE : IsQuasisimple E)
    (hZodd : Odd (Nat.card (Subgroup.center E)))
    (hEN : E ≤ N) (hLnormal : IsNormalIn L N)
    (hinv : ∃ v : G, v ∈ E ⊓ L ∧ IsInvolution v) :
    E ≤ L := by
  classical
  let I : Subgroup G := E ⊓ L
  have hI_normal_E : IsNormalIn I E := by
    refine ⟨inf_le_left, ?_⟩
    intro e he x hx
    exact ⟨E.mul_mem (E.mul_mem he hx.1) (E.inv_mem he),
      hLnormal.2 e (hEN he) x hx.2⟩
  let IE : Subgroup E := I.subgroupOf E
  have hIE_normal : IE.Normal :=
    (Subgroup.normal_subgroupOf_iff (show I ≤ E from inf_le_left)).2
      (fun h k hh hk => hI_normal_E.2 k hk h hh)
  have hIE_inv : ∃ v : E, v ∈ IE ∧ IsInvolution v := by
    rcases hinv with ⟨v, hvI, hv⟩
    refine ⟨⟨v, hvI.1⟩, Subgroup.mem_subgroupOf.mpr hvI, ?_⟩
    exact ⟨fun h1 => hv.1 (congrArg Subtype.val h1), Subtype.ext hv.2⟩
  have hIE_top : IE = ⊤ := by
    rcases normal_subgroup_le_center_or_eq_top hE IE hIE_normal with hIEc | htop
    · exfalso
      rcases hIE_inv with ⟨v, hvIE, hv⟩
      have hvZ : v ∈ Subgroup.center E := hIEc hvIE
      have hord2 : orderOf v = 2 := orderOf_eq_prime hv.2 hv.1
      have htwo_dvd : 2 ∣ Nat.card (Subgroup.center E) := by
        have hord_eq : orderOf (⟨v, hvZ⟩ : Subgroup.center E) = orderOf v :=
          (orderOf_injective (Subgroup.center E).subtype
            (Subgroup.center E).subtype_injective ⟨v, hvZ⟩).symm
        have hdvd : orderOf (⟨v, hvZ⟩ : Subgroup.center E) ∣
            Nat.card (Subgroup.center E) :=
          orderOf_dvd_natCard (⟨v, hvZ⟩ : Subgroup.center E)
        simpa [hord_eq, hord2] using hdvd
      exact hZodd.not_two_dvd_nat htwo_dvd
    · exact htop
  intro e he
  have hIE_mem : (⟨e, he⟩ : E) ∈ IE := by
    rw [hIE_top]
    trivial
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hIE_mem)).2

end CFSG.GorensteinWalter
