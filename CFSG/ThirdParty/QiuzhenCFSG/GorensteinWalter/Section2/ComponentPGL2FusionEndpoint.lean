module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalSubgroupInvolutionOfOddQuotientImage
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddCenterOfOddQuotientKernel
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentNormalOfInvariantPerfectImage
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentPSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalOfLinearDerivedModel

namespace CFSG
end CFSG
open CFSG

/-!
# The internal-fusion endpoint for a `PGL₂` component image

This assembles the reusable group-theoretic endpoint of the surviving
`PGL₂` branch in Gorenstein--Walter Theorem 2.6.  The only remaining
model-specific input is that the distinguished involution maps into the
selected component image modulo the odd core.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Suppose a component maps to the derived subgroup of a normal `PGL₂(K)`
model modulo an odd normal kernel, and its quotient kernel is its center.
If an involution `t` maps into that component image, then the component is
normal, contains `t`, and all of its involutions are conjugate to `t` by
elements of the component. -/
public theorem component_normal_and_involutions_fused_of_pgl2_quotient_data
    {H : Type u} [Group H] [Finite H]
    (E O : Subgroup H) (hE : IsComponentOf E (⊤ : Subgroup H))
    (hOnormal : O.Normal) (hOodd : Odd (Nat.card O))
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (e : L ≃* PGL2 K)
    (hcenterQuotient : Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2 K))
    {t : H} (htI : IsInvolution t) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    let f : E →* Ebar :=
      (q.comp E.subtype).codRestrict Ebar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    Ebar ≤ L →
    Ebar ≠ ⊥ →
    Group.IsPerfect Ebar →
    (Ebar.subgroupOf L).map e.toMonoidHom = commutator (PGL2 K) →
    f.ker = Subgroup.center E →
    q t ∈ Ebar →
    E.Normal ∧ t ∈ E ∧
      ∀ z : H, z ∈ E → IsInvolution z →
        ∃ g : H, g ∈ E ∧ g * z * g⁻¹ = t := by
  dsimp
  intro hEbarL hEbarne hEbarperf hmodel hker htbar
  let : O.Normal := hOnormal
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let Ebar : Subgroup (H ⧸ O) := E.map q
  have hEbarNormal : Ebar.Normal :=
    normal_of_subgroupOf_map_eq_commutator
      L Ebar hLnormal hEbarL e hmodel
  have hEnormal : E.Normal :=
    component_normal_of_nontrivial_perfect_normal_image
      E hE q hEbarne hEbarperf hEbarNormal
  have htE : t ∈ E :=
    involution_mem_normal_subgroup_of_quotient_mem_map_odd_kernel
      E O hEnormal hOnormal hOodd htI htbar
  have hZodd : Odd (Nat.card (Subgroup.center E)) :=
    center_odd_of_quotient_restriction_ker_eq_center
      E O hOodd hker
  exact ⟨hEnormal, htE,
    component_involutions_fused_of_central_quotient_psl2
      E K hK hZodd hcenterQuotient htE htI⟩

end CFSG.GorensteinWalter
