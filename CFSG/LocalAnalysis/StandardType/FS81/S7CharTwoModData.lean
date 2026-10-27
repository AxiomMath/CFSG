module

public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7TrivOnW
import CFSG.LocalAnalysis.StandardType.FS81.S7CentModSigma
import CFSG.LocalAnalysis.StandardType.FS81.S7NormalizerW
import CFSG.LocalAnalysis.StandardType.FS81.S7CharTwoMod

public section

namespace CFSG.StandardType.FrameRoute.FS81

private theorem conj_mem_zpowers_of_comm {G : Type} [Group G] {t x z : G}
    (hx : x * t = t * x) (hz : z ∈ Subgroup.zpowers t) :
    x * z * x⁻¹ ∈ Subgroup.zpowers t := by
  have hle : Subgroup.zpowers t ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hx
  have hcomm : x * z = z * x :=
    (Subgroup.mem_centralizer_iff.mp (hle hz)) x (Set.mem_singleton x)
  have : x * z * x⁻¹ = z := by rw [hcomm]; group
  rw [this]
  exact hz

theorem charTwoMod_of_data {G : Type} [Group G] [Finite G] {H U L P J D : Subgroup G}
    [(U.subgroupOf H).Normal] {t₀ σ b : G} (hUH : U ≤ H) (hU : IsPGroup 2 U) (hLH : L ≤ H)
    (hLU : ∀ x ∈ L, x ∈ U → x = 1) (ht₀H : ∀ h ∈ H, h * t₀ = t₀ * h)
    (hlev : E7LeviData L σ b P J D) (hmod : E7ModuleData U t₀ σ L P)
    (hmem : ∀ g ∈ H, g * b * g⁻¹ ∈ L ⊔ U → g ∈ L ⊔ U) :
    CharTwoMod H U ⟨σ, hLH (hlev.P_le hlev.σ_mem)⟩ := by
  have hσH : σ ∈ H := hLH (hlev.P_le hlev.σ_mem)
  have hUn : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U := by
    intro h hh u hu
    exact (Subgroup.normal_subgroupOf_iff hUH).mp
      (inferInstance : (U.subgroupOf H).Normal) u h hu hh
  have hPH : P ≤ H := hlev.P_le.trans hLH
  have hP : IsPGroup 2 P := hlev.P_two
  have hPσ : ∀ x ∈ P, x * σ * x⁻¹ * σ⁻¹ ∈ U := by
    intro x hx
    have h2 : x * σ * x⁻¹ * σ⁻¹ = 1 := by rw [hlev.P_cent x hx]; group
    rw [h2]
    exact U.one_mem
  have hcent : ∀ x ∈ H, (∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ U) → x ∈ P ⊔ U := by
    intro x hxH hxP
    have hx := mem_sup_of_centralizes_mod hUH hU hLH hLU hlev hmem hxH hxP
    exact (sup_le_sup_right (Subgroup.zpowers_le.2 hlev.σ_mem) U) hx
  have hnorm : ∀ x ∈ H, x * σ * x⁻¹ * σ⁻¹ ∈ U → ∀ y ∈ P, x * y * x⁻¹ ∈ P ⊔ U := by
    intro x hxH hxσ y hy
    have hxyH : x * y * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hxH (hPH hy)) (H.inv_mem hxH)
    have hc'U : x⁻¹ * σ * x * σ⁻¹ ∈ U := by
      have heq : x⁻¹ * σ * x * σ⁻¹ = x⁻¹ * (x * σ * x⁻¹ * σ⁻¹)⁻¹ * x := by
        group
      rw [heq]
      simpa only [inv_inv] using hUn x⁻¹ (H.inv_mem hxH) _ (U.inv_mem hxσ)
    have hc''U : x * (y * (x⁻¹ * σ * x * σ⁻¹) * y⁻¹) * x⁻¹ ∈ U := by
      exact hUn x hxH _ (hUn y (hPH hy) _ hc'U)
    have hxyσ : (x * y * x⁻¹) * σ * (x * y * x⁻¹)⁻¹ * σ⁻¹ ∈ U := by
      have hyinvσ : σ * y⁻¹ = y⁻¹ * σ :=
        (show Commute y σ from hlev.P_cent y hy).inv_left.symm
      have hc1 : (x * y * x⁻¹) * σ * (x * y * x⁻¹)⁻¹
          = x * (y * (x⁻¹ * σ * x) * y⁻¹) * x⁻¹ := by group
      have hsub : x⁻¹ * σ * x = (x⁻¹ * σ * x * σ⁻¹) * σ := by group
      have hmove : y * ((x⁻¹ * σ * x * σ⁻¹) * σ) * y⁻¹
          = y * (x⁻¹ * σ * x * σ⁻¹) * y⁻¹ * σ := by
        conv_lhs =>
          rw [show y * ((x⁻¹ * σ * x * σ⁻¹) * σ) * y⁻¹
              = y * (x⁻¹ * σ * x * σ⁻¹) * (σ * y⁻¹) from by group]
        conv_lhs => rw [hyinvσ]
        group
      have hc2 : x * (y * (x⁻¹ * σ * x) * y⁻¹) * x⁻¹
          = (x * (y * (x⁻¹ * σ * x * σ⁻¹) * y⁻¹) * x⁻¹) * (x * σ * x⁻¹) := by
        conv_lhs => rw [hsub]
        conv_lhs => rw [hmove]
        group
      have hsplit : (x * y * x⁻¹) * σ * (x * y * x⁻¹)⁻¹ * σ⁻¹
          = (x * (y * (x⁻¹ * σ * x * σ⁻¹) * y⁻¹) * x⁻¹)
            * (x * σ * x⁻¹ * σ⁻¹) := by
        rw [hc1, hc2]
        group
      rw [hsplit]
      exact U.mul_mem hc''U hxσ
    have hxnorm : x ∈ Subgroup.normalizer (modW U t₀ σ : Set G) :=
      mem_normalizer_commutator_sup hUn hmod.t₀_mem ht₀H hmod.U_comm hσH hxH hxσ
    have hxinvnorm : x⁻¹ ∈ Subgroup.normalizer (modW U t₀ σ : Set G) :=
      Subgroup.inv_mem _ hxnorm
    have hxW : ∀ w ∈ modW U t₀ σ,
        (x * y * x⁻¹) * w * (x * y * x⁻¹)⁻¹ * w⁻¹ ∈ Subgroup.zpowers t₀ := by
      intro w hw
      set w₁ := x⁻¹ * w * x with hw₁def
      have hw₁ : w₁ ∈ modW U t₀ σ := by
        simpa only [hw₁def, inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hxinvnorm w).mp hw
      have hyw₁ : y * w₁ * y⁻¹ * w₁⁻¹ ∈ Subgroup.zpowers t₀ := hmod.P_W y hy w₁ hw₁
      have hconj : (x * y * x⁻¹) * w * (x * y * x⁻¹)⁻¹ * w⁻¹
          = x * (y * w₁ * y⁻¹ * w₁⁻¹) * x⁻¹ := by
        rw [hw₁def]
        group
      rw [hconj]
      exact conj_mem_zpowers_of_comm (ht₀H x hxH) hyw₁
    exact mem_sup_of_trivial_on_W hUH hU hLH hLU ht₀H hlev hmod hmem hxyH hxyσ hxW
  exact charTwoMod_of_normal_pGroup_mod hUH hσH hPH hP hPσ hnorm hcent

end CFSG.StandardType.FrameRoute.FS81

end
