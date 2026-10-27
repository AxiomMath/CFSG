module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseSylowIntersectionEscape
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseCentralizerSylow

namespace CFSG
end CFSG
open CFSG

/-!
# The aligned PSL₂ ambient-Sylow escape endpoint

The source first re-chooses the ambient Sylow so that its intersection with
`M` is a Sylow subgroup of `M`.  Since `CentralizerSetup` stores a fixed
ambient Sylow, that alignment is made explicit here.
-/

namespace CFSG.GorensteinWalter

universe u

/-- In the source-aligned PSL₂ setup, failure of `S ≤ E` forces an element
of `S ∩ M` outside `E`. -/
public theorem secondCase_psl2_aligned_sylow_intersection_escape
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (SM : Sylow 2 (↥w.M))
    (hSMleS : (SM : Subgroup w.M).map w.M.subtype ≤ (c.S : Subgroup G))
    (SE : Sylow 2 (↥d.E))
    (hSEamb : (SE : Subgroup d.E).map d.E.subtype =
      ((SM : Subgroup w.M).map w.M.subtype) ⊓ d.E)
    (F : Subgroup G)
    (hF_eq : F = c.FU ⊓ Subgroup.centralizer
      (((SE : Subgroup d.E).map d.E.subtype : Subgroup G) : Set G))
    (hNF : Subgroup.normalizer (F : Set G) = w.M)
    (hSnotE : ¬ (c.S : Subgroup G) ≤ d.E) :
    ¬ ((c.S : Subgroup G) ⊓ w.M) ≤ d.E := by
  let Iamb : Subgroup G := (c.S : Subgroup G) ⊓ w.M
  let IM : Subgroup w.M := Iamb.subgroupOf w.M
  have hIMp : IsPGroup 2 IM := by
    have hIp : IsPGroup 2 Iamb := c.S.isPGroup'.to_inf_left
    exact hIp.comap_subtype
  have hSMleIM : (SM : Subgroup w.M) ≤ IM := by
    intro x hx
    apply Subgroup.mem_subgroupOf.mpr
    exact ⟨hSMleS (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hIMeq : IM = (SM : Subgroup w.M) := SM.is_maximal' hIMp hSMleIM
  have hSMamb : (SM : Subgroup w.M).map w.M.subtype =
      (c.S : Subgroup G) ⊓ w.M := by
    apply le_antisymm
    · exact le_inf hSMleS (Subgroup.map_subtype_le (SM : Subgroup w.M))
    · intro x hx
      let xM : w.M := ⟨x, hx.2⟩
      have hxIM : xM ∈ IM := Subgroup.mem_subgroupOf.mpr hx
      rw [hIMeq] at hxIM
      exact Subgroup.mem_map.mpr ⟨xM, hxIM, rfl⟩
  have hSEeq : (SE : Subgroup d.E).map d.E.subtype =
      (c.S : Subgroup G) ⊓ d.E := by
    rw [hSEamb, hSMamb]
    apply le_antisymm
    · exact inf_le_inf inf_le_left le_rfl
    · intro x hx
      exact ⟨⟨hx.1, d.E_component.1 hx.2⟩, hx.2⟩
  apply secondCase_sylow_intersection_not_le_component_of_fitting_centralizer
    c w d F ?_ hNF hSnotE
  rw [← hSEeq]
  exact hF_eq

end CFSG.GorensteinWalter
