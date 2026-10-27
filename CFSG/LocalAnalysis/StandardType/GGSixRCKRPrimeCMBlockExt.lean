module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeCMBlockCore

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
open CFSG.Open (StatedLieTag)

section Genuine


private theorem exists_rckLift_of_map_range {U V : Type} [Group U] [Group V] {ι : U →* V}
    (hι : Function.Injective ι) {J' : Subgroup U} {G : Subgroup V} (hJ'G : J'.map ι ≤ G)
    {t : StatedLieTag} {m g : ℕ} {κ : (ggU t m g).K →* G}
    (hκrange : κ.range = (J'.map ι).subgroupOf G) :
    ∃ σ : (ggU t m g).K →* ↥J', σ.range = ⊤ ∧ ∀ z, ι ((σ z : ↥J') : U) = (κ z : V) := by
  have hκmem : ∀ z, ((κ z : G) : V) ∈ J'.map ι := by
    intro z
    have hz : κ z ∈ ((J'.map ι).subgroupOf G : Subgroup G) := by
      rw [← hκrange]
      exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hz
  let κ' : (ggU t m g).K →* ↥(J'.map ι) := (G.subtype.comp κ).codRestrict (J'.map ι) hκmem
  let eJ : ↥J' ≃* ↥(J'.map ι) := Subgroup.equivMapOfInjective J' ι hι
  let σ : (ggU t m g).K →* ↥J' := eJ.symm.toMonoidHom.comp κ'
  refine ⟨σ, ?_, ?_⟩
  · rw [MonoidHom.range_eq_top]
    have hκ'surj : Function.Surjective κ' := by
      intro x
      have hx : (x : V) ∈ (G.subtype.comp κ).range := by
        rw [MonoidHom.range_comp, hκrange, Subgroup.map_subgroupOf_eq_of_le hJ'G]
        exact x.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hx
      exact ⟨z, Subtype.ext hz⟩
    exact eJ.symm.surjective.comp hκ'surj
  · intro z
    have h := Subgroup.coe_equivMapOfInjective_apply J' ι hι (σ z)
    rw [show eJ (σ z) = κ' z from eJ.apply_symm_apply (κ' z)] at h
    exact h.symm

theorem rckClassicalModelID_of_blockExt {X U V : Type} [Group X] [Group U] [Group V]
    {ψ : U →* X} (hker : ψ.ker ≤ Subgroup.center U) {ι : U →* V} (hι : Function.Injective ι)
    {J' : Subgroup U} {G : Subgroup V} (hJ'G : J'.map ι ≤ G) {t : StatedLieTag} {m g : ℕ}
    {κ : (ggU t m g).K →* G} (hκ : RCKModelConverse ((J'.map ι).subgroupOf G) t m g κ)
    (ht : RCKClassicalTag t) (hg : 1 ≤ g) {K B : Subgroup X} (hK : J'.map ψ = K)
    (hB : ∀ b ∈ B, ∃ s ∈ G, s ∈ Subgroup.normalizer ((J'.map ι : Subgroup V) : Set V) ∧
      ∀ y ∈ J', ∀ y' ∈ J', ι y' = s * ι y * s⁻¹ → b⁻¹ * ψ y * b = ψ y') :
    RCKClassicalModelID K B := by
  obtain ⟨hκinj, hκrange, hκconv⟩ := hκ
  obtain ⟨σ, hσtop, hσval⟩ := exists_rckLift_of_map_range hι hJ'G hκrange
  let φ : (ggU t m g).K →* X := ψ.comp (J'.subtype.comp σ)
  have hφrange : φ.range = K := by
    dsimp only [φ]
    rw [MonoidHom.range_comp, MonoidHom.range_comp, hσtop, Subgroup.map_top,
      Subgroup.range_subtype, hK]
  have hφker : φ.ker ≤ Subgroup.center (ggU t m g).K := by
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzψ : ((σ z : ↥J') : U) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker]
      simpa only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype] using hz
    have hzc : ∀ u : U, u * ((σ z : ↥J') : U) = ((σ z : ↥J') : U) * u :=
      Subgroup.mem_center_iff.mp (hker hzψ)
    rw [Subgroup.mem_center_iff]
    intro w
    apply hκinj
    have hcomm : κ z * κ w = κ w * κ z := by
      apply Subtype.ext
      have h := congrArg ι (hzc ((σ w : ↥J') : U))
      simp only [map_mul, hσval w, hσval z, Subgroup.coe_mul] at h
      exact h.symm
    simpa only [map_mul] using hcomm.symm
  have hφconv : ∀ b ∈ B, GGPsiInnerDiag (ggU t m g).D φ b := by
    intro b hb
    obtain ⟨s, hsG, hsN, hconj⟩ := hB b hb
    let c : G := ⟨s, hsG⟩
    have hcN : c ∈ Subgroup.normalizer (((J'.map ι).subgroupOf G : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have hcoe : ((c * n * c⁻¹ : G) : V) = s * (n : V) * s⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hcoe]
      exact Subgroup.mem_normalizer_iff.mp hsN (n : V)
    refine hκconv c hcN X φ b ?_
    intro z z' hzz'
    have hz' : ι ((σ z' : ↥J') : U) = s * ι ((σ z : ↥J') : U) * s⁻¹ := by
      have h := congrArg (fun x : G => (x : V)) hzz'
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [← hσval z', ← hσval z] at h
      exact h
    have h := hconj ((σ z : ↥J')) (σ z).2 ((σ z' : ↥J')) (σ z').2 hz'
    simpa only [φ, MonoidHom.comp_apply, Subgroup.coe_subtype] using h
  exact ⟨t, m, g, φ, ht, hg, hφrange, hφker, hφconv⟩

end Genuine

end CFSG.StandardType.RCKRP
