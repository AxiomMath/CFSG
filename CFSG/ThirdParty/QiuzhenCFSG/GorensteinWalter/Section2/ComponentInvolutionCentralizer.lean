module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Centralizers of internally fused component involutions

This isolates the final centralizer-containment step in the component branch
of Gorenstein--Walter Theorem 2.6.  Once an involution in the selected
component is fused to the distinguished involution by an element of the
ambient subgroup, its full ambient centralizer is carried into that subgroup.
-/

namespace CFSG.GorensteinWalter

universe u

/-- Suppose every involution of `E` is conjugate to `t` by an element of
`H`.  If `C_G(t) ≤ H`, then the ambient centralizer of every involution of
`E` is contained in `H`. -/
public theorem component_involution_centralizer_le_of_internal_fusion
    {G : Type u} [Group G]
    (H E : Subgroup G) (t : G)
    (hcentralizer : Subgroup.centralizer ({t} : Set G) ≤ H)
    (hfusion : ∀ z : G, z ∈ E → IsInvolution z →
      ∃ g : G, g ∈ H ∧ g * z * g⁻¹ = t)
    {z : G} (hzE : z ∈ E) (hzI : IsInvolution z) :
    Subgroup.centralizer ({z} : Set G) ≤ H := by
  obtain ⟨g, hgH, hgz⟩ := hfusion z hzE hzI
  intro x hx
  have hxcomm : Commute x z :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hxconjcomm : Commute (g * x * g⁻¹) t := by
    have hconj := hxcomm.conj g
    simpa [hgz] using hconj
  have hxconjH : g * x * g⁻¹ ∈ H :=
    hcentralizer
      (Subgroup.mem_centralizer_singleton_iff.mpr hxconjcomm)
  have hxrecover : g⁻¹ * (g * x * g⁻¹) * g ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hgH) hxconjH) hgH
  simpa [mul_assoc] using hxrecover

end CFSG.GorensteinWalter
