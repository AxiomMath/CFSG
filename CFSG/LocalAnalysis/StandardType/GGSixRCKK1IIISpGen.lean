module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LocalAnalysis.PreuniquenessRankFour.Helpers

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1 CFSG.Open

theorem rckK1b_of_inner {G : Type*} [Group G] [Finite G] (hZ : Subgroup.center G = ⊥)
    (hinn : ∀ σ : MulAut G, ∃ c : G, σ = MulAut.conj c) (r : G) (V : Subgroup G)
    (hN : ∀ y ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)), ∀ v ∈ V,
      y * v * y⁻¹ * v⁻¹ ∈ Subgroup.zpowers r) :
    K1Lift.K1b r V := by
  have hinj : Function.Injective (MulAut.conj : G →* MulAut G) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker] at hz
    have hzc : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h : z * g * z⁻¹ = g := by
        have h' := congrArg (fun f : MulAut G => f g) hz
        simpa only [MulAut.conj_apply, MulAut.one_apply] using h'
      have hzg : z * g = g * z := by
        calc z * g = z * g * z⁻¹ * z := by group
          _ = g * z := by rw [h]
      exact hzg.symm
    rwa [hZ] at hzc
  intro Y hY hfix hnorm v hv φ hφ
  let H : Subgroup G := Subgroup.centralizer ({r} : Set G)
  let Y' : Subgroup G := Y.comap (MulAut.conj : G →* MulAut G)
  have hY'pg : IsPGroup 2 Y' := by
    simpa only [Y'] using
      IsPGroup.comap_of_injective hY (MulAut.conj : G →* MulAut G) hinj
  have hY'le : Y' ≤ H := by
    intro g hg
    change g ∈ Subgroup.centralizer ({r} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have hgY : MulAut.conj g ∈ Y := hg
    have h1 : (MulAut.conj g : MulAut G) r = r := hfix (MulAut.conj g) hgY
    rw [MulAut.conj_apply] at h1
    have h2 : g * r = r * g := by
      calc g * r = g * r * g⁻¹ * g := by group
        _ = r * g := by rw [h1]
    exact h2.symm
  have hY'norm : (Y'.subgroupOf H).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    rw [Subgroup.le_normalizer_iff]
    intro c hc g hg
    have hgY : MulAut.conj g ∈ Y := hg
    have hc' : MulAut.conj c ∈ Subgroup.normalizer (Y : Set (MulAut G)) :=
      hnorm c ((Subgroup.mem_centralizer_iff.mp hc r (by simp)).symm)
    have hmem := (Subgroup.mem_normalizer_iff.mp hc' (MulAut.conj g)).mp hgY
    show MulAut.conj (c * g * c⁻¹) ∈ Y
    rwa [map_mul, map_mul, map_inv]
  have hY'pcore : Y' ≤ pCoreOf 2 H :=
    CFSG.PreuniquenessRankFour.Helpers.normal_pSubgroup_le_pCoreOf 2 hY'le hY'norm hY'pg
  obtain ⟨c₀, hc₀⟩ := hinn φ
  have hc₀Y' : c₀ ∈ Y' := by
    show MulAut.conj c₀ ∈ Y
    rw [← hc₀]
    exact hφ
  have hc₀mem : c₀ ∈ pCoreOf 2 (Subgroup.centralizer ({r} : Set G)) := hY'pcore hc₀Y'
  rw [hc₀, MulAut.conj_apply]
  exact hN c₀ hc₀mem v hv

end CFSG.StandardType.RCKK1IIISp
