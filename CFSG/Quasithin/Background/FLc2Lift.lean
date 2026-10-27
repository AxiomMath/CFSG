module

public import CFSG.Quasithin.EmptyFaithful.S1565A

public section

namespace CFSG.Quasithin.FLc

variable {G : Type}  [Group G]

theorem exists_fixed_mul [Finite G] {H SL U A : Subgroup G}
    (hHU : H ≤ Subgroup.normalizer (U : Set G)) (hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (hU2 : ∀ a ∈ U, a ^ 2 = 1) (hodd : Odd (SL.relIndex H)) {w : G} (hwU : w ∈ U) (hw : ∀ h ∈ H, h * w * h⁻¹ * w⁻¹ ∈ A)
    (hwB : ∀ s ∈ SL, s * w * s⁻¹ = w) :
    ∃ u ∈ A, ∀ h ∈ H, h * (w * u) * h⁻¹ = w * u := by
  let _ : CommGroup ↥U :=
    { (inferInstance : Group ↥U) with mul_comm := fun a b => Subtype.ext (hUc _ a.2 _ b.2) }
  let φ : ↥H →* MulAut ↥U := (U.normalizerMonoidHom).comp (Subgroup.inclusion hHU)
  have hφ : ∀ (h : ↥H) (u : ↥U), ((φ h u : ↥U) : G) = (h : G) * (u : G) * (h : G)⁻¹ := fun h u =>
    Subgroup.normalizerMonoidHom_apply_apply_coe U (Subgroup.inclusion hHU h) u
  have hinv : S1565.InvSub φ (⊥ : Subgroup ↥U) := by
    intro x a ha
    rw [Subgroup.mem_bot] at ha ⊢
    rw [ha, map_one]
  have hw'' : S1565.FixMod φ ⊤ (A.subgroupOf U) (⟨w, hwU⟩ : ↥U) := by
    intro s _
    show (φ s ⟨w, hwU⟩ * (⟨w, hwU⟩ : ↥U)⁻¹ : ↥U) ∈ A.subgroupOf U
    rw [Subgroup.mem_subgroupOf]
    show ((φ s ⟨w, hwU⟩ : ↥U) : G) * w⁻¹ ∈ A
    rw [hφ]
    exact hw s s.2
  have hwB' : S1565.FixMod φ (SL.subgroupOf H) (⊥ : Subgroup ↥U) (⟨w, hwU⟩ : ↥U) := by
    intro s hs
    show (φ s ⟨w, hwU⟩ * (⟨w, hwU⟩ : ↥U)⁻¹ : ↥U) ∈ (⊥ : Subgroup ↥U)
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    show ((φ s ⟨w, hwU⟩ : ↥U) : G) * w⁻¹ = 1
    rw [hφ]
    have := hwB (s : G) (Subgroup.mem_subgroupOf.1 hs)
    rw [this]
    group
  obtain ⟨u, hu, hu1, -⟩ := S1565.norm_step φ (fun w => Subtype.ext (by simpa using hU2 w w.2))
    (SL.subgroupOf H) hodd hinv hw'' hwB'
  refine ⟨(u : G), Subgroup.mem_subgroupOf.1 hu, fun h hh => ?_⟩
  have h2 := hu1 ⟨h, hh⟩ (Subgroup.mem_top _)
  have h3 : (φ ⟨h, hh⟩ (⟨w, hwU⟩ * u) * (⟨w, hwU⟩ * u)⁻¹ : ↥U) = 1 := by
    simpa using h2
  have h4 := congrArg Subtype.val h3
  have h5 : ((φ ⟨h, hh⟩ (⟨w, hwU⟩ * u) : ↥U) : G) = w * (u : G) := by
    have := (mul_inv_eq_one.1 h3)
    rw [this]
    rfl
  rw [hφ] at h5
  exact h5

end CFSG.Quasithin.FLc
