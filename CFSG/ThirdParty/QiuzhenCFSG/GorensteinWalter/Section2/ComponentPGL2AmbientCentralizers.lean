module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentPGL2FusionEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ComponentInvolutionCentralizer

namespace CFSG
end CFSG
open CFSG

/-!
# Ambient centralizers from the internal `PGL₂` component endpoint

This transports the completed internal component-fusion endpoint through a
subgroup embedding.  It is the direct interface needed in the surviving
`PGL₂` branch of Gorenstein--Walter Theorem 2.6: once the distinguished
involution maps into the component image modulo the odd core, every ambient
involution centralizer of the component lies in the chosen ambient subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Suppose a component of a finite subgroup `H` satisfies the complete
`PGL₂(K)` quotient data and the distinguished ambient involution maps into
its quotient image.  Then the component is normal in `H`, the distinguished
involution belongs to its ambient image, all ambient component involutions
fuse to it through that image, and their full ambient centralizers lie in
`H`. -/
public theorem
    component_normal_ambient_fusion_and_centralizers_of_pgl2_quotient_data
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (E O : Subgroup H) (hE : IsComponentOf E (⊤ : Subgroup H))
    (hOnormal : O.Normal) (hOodd : Odd (Nat.card O))
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (L : Subgroup (H ⧸ O)) (hLnormal : L.Normal)
    (e : L ≃* PGL2 K)
    (hcenterQuotient : Nonempty ((E ⧸ Subgroup.center E) ≃* PSL2 K))
    {t : G} (htH : t ∈ H) (htI : IsInvolution t)
    (hcentralizer : Subgroup.centralizer ({t} : Set G) ≤ H) :
    let q : H →* H ⧸ O := QuotientGroup.mk' O
    let Ebar : Subgroup (H ⧸ O) := E.map q
    let f : E →* Ebar :=
      (q.comp E.subtype).codRestrict Ebar (fun x =>
        Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩)
    let Eambient : Subgroup G := E.map H.subtype
    Ebar ≤ L →
    Ebar ≠ ⊥ →
    Group.IsPerfect Ebar →
    (Ebar.subgroupOf L).map e.toMonoidHom = commutator (PGL2 K) →
    f.ker = Subgroup.center E →
    q (⟨t, htH⟩ : H) ∈ Ebar →
    E.Normal ∧
      t ∈ Eambient ∧
      (∀ z : G, z ∈ Eambient → IsInvolution z →
        ∃ g : G, g ∈ Eambient ∧ g * z * g⁻¹ = t) ∧
      ∀ z : G, z ∈ Eambient → IsInvolution z →
        Subgroup.centralizer ({z} : Set G) ≤ H := by
  dsimp
  intro hEbarL hEbarne hEbarperf hmodel hker htbar
  let tH : H := ⟨t, htH⟩
  have htHI : IsInvolution tH := by
    constructor
    · intro htone
      apply htI.1
      exact congrArg Subtype.val htone
    · exact Subtype.ext htI.2
  obtain ⟨hEnormal, htE, hfusionH⟩ :=
    component_normal_and_involutions_fused_of_pgl2_quotient_data
      E O hE hOnormal hOodd K hK L hLnormal e hcenterQuotient htHI
        hEbarL hEbarne hEbarperf hmodel hker htbar
  let Eambient : Subgroup G := E.map H.subtype
  have hEambientH : Eambient ≤ H := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨xH, _hxE, rfl⟩
    exact xH.2
  have htEambient : t ∈ Eambient := by
    exact Subgroup.mem_map.mpr ⟨tH, htE, rfl⟩
  have hfusionG :
      ∀ z : G, z ∈ Eambient → IsInvolution z →
        ∃ g : G, g ∈ Eambient ∧ g * z * g⁻¹ = t := by
    intro z hzE hzI
    rcases Subgroup.mem_map.mp hzE with ⟨zH, hzHE, hzval⟩
    change (zH : G) = z at hzval
    have hzHI : IsInvolution zH := by
      constructor
      · intro hzone
        apply hzI.1
        calc
          z = H.subtype zH := hzval.symm
          _ = H.subtype 1 := congrArg H.subtype hzone
          _ = 1 := map_one H.subtype
      · apply Subtype.ext
        simpa [hzval] using hzI.2
    obtain ⟨gH, hgHE, hgz⟩ := hfusionH zH hzHE hzHI
    refine ⟨(gH : G), Subgroup.mem_map.mpr ⟨gH, hgHE, rfl⟩, ?_⟩
    simpa [tH, hzval] using congrArg Subtype.val hgz
  refine ⟨hEnormal, htEambient, hfusionG, ?_⟩
  intro z hzE hzI
  apply component_involution_centralizer_le_of_internal_fusion
    H Eambient t hcentralizer
  · intro y hyE hyI
    obtain ⟨g, hgE, hgy⟩ := hfusionG y hyE hyI
    exact ⟨g, hEambientH hgE, hgy⟩
  · exact hzE
  · exact hzI

end CFSG.GorensteinWalter
