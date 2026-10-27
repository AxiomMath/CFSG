module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionQuotSub

private theorem tqs_inv_mul_mem_center {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (δ : MulAut X) (x : X)
    (hx : ggInducedAut θ δ (θ (x : X ⧸ Subgroup.center X)) = θ (x : X ⧸ Subgroup.center X)) :
    x⁻¹ * δ x ∈ Subgroup.center X := by
  have h1 : θ (((x⁻¹ * δ x : X) : X ⧸ Subgroup.center X)) = 1 := by
    have hm : ((x⁻¹ * δ x : X) : X ⧸ Subgroup.center X)
        = (x : X ⧸ Subgroup.center X)⁻¹ * (δ x : X ⧸ Subgroup.center X) := by simp
    rw [hm, map_mul, map_inv, ← ggInducedAut_apply θ δ x, hx, inv_mul_cancel]
  exact (QuotientGroup.eq_one_iff (x⁻¹ * δ x)).mp ((MulEquiv.map_eq_one_iff θ).mp h1)

theorem ggTorsion_subnormal_image {X : Type} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) {δ : MulAut X} {J : Subgroup X}
    (hJ : IsSubnormal J (ggAutFixedSubgroup δ)) :
    IsSubnormal
      (J.map ((θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))))
      (ggAutFixedSubgroup (ggInducedAut θ δ)) := by
  let π : X →* R :=
    (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))
  let C : Subgroup X := ggAutFixedSubgroup δ
  let P : Subgroup X := (ggAutFixedSubgroup (ggInducedAut θ δ)).comap π
  have hsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center X))
  have hPmap : P.map π = ggAutFixedSubgroup (ggInducedAut θ δ) :=
    Subgroup.map_comap_eq_self_of_surjective hsurj _
  have hCP : C ≤ P := by
    intro x hx
    change π x ∈ ggAutFixedSubgroup (ggInducedAut θ δ)
    rw [mem_ggAutFixedSubgroup]
    change ggInducedAut θ δ (θ (x : X ⧸ Subgroup.center X)) = θ (x : X ⧸ Subgroup.center X)
    rw [ggInducedAut_apply, hx]
  have hnorm : (C.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCP]
    intro c g hc hg
    show δ (g * c * g⁻¹) = g * c * g⁻¹
    have hc' : δ c = c := hc
    have hg' : ggInducedAut θ δ (θ (g : X ⧸ Subgroup.center X))
        = θ (g : X ⧸ Subgroup.center X) := hg
    set z : X := g⁻¹ * δ g with hzdef
    have hz : z ∈ Subgroup.center X := by
      rw [hzdef]
      exact tqs_inv_mul_mem_center θ δ g hg'
    have hzc : z * c = c * z := ((Subgroup.mem_center_iff.mp hz) c).symm
    have hdg : δ g = g * z := by
      rw [hzdef]
      group
    rw [map_mul, map_mul, map_inv, hc', hdg, mul_assoc g z c, hzc]
    group
  have hsub : IsSubnormal C P := IsSubnormal.step hCP hnorm (IsSubnormal.refl P)
  have hsubJ : IsSubnormal J P := hJ.trans hsub
  have hmap := hsubJ.map π
  rwa [hPmap] at hmap

end TorsionQuotSub

end CFSG.StandardType
