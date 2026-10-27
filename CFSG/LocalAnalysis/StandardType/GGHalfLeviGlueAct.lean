module

public import CFSG.LocalAnalysis.StandardType.GGHalfLeviGlueTorus
public import CFSG.LocalAnalysis.StandardType.GGHalfStageADefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

theorem ggHalf_eq_of_conj_eq {N : ℕ} {s s' : SpecialLinearGroup (Fin N) F2}
    (h : ∀ w, s * w * s⁻¹ = s' * w * s'⁻¹) : s = s' := by
  have h1 : s'⁻¹ * s = 1 := by
    refine eq_one_of_commute_range (ψ := MonoidHom.id _) Function.injective_id (fun t => ?_)
    simp only [MonoidHom.id_apply]
    calc s'⁻¹ * s * t = s'⁻¹ * (s * t * s⁻¹) * s := by group
      _ = s'⁻¹ * (s' * t * s'⁻¹) * s := by rw [h t]
      _ = t * (s'⁻¹ * s) := by group
  exact (inv_mul_eq_one.mp h1).symm

variable {G : Type} [Group G] {Bs L K : Subgroup G} {m : ℕ}
  {ψ₁ ψ₂ : SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2 →* G}

theorem GGHalfTorusFrame.levi_action_lower
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψ₁) {b : G} (hb : b ∈ Bs) :
    ∃ s ∈ halfTorus m, ∀ w : SpecialLinearGroup (Fin (m + 1)) F2,
      b * ψ₁ (slLower2Hom m w) * b⁻¹ = ψ₁ (slLower2Hom m (s * w * s⁻¹)) := by
  obtain ⟨t, ht, hact⟩ := hL.act b hb
  obtain ⟨s, hs, hconj⟩ := exists_levi_conj_lower ht
  refine ⟨s, hs, fun w => ?_⟩
  have hmem : ψ₁ (slLower2Hom m w) ∈ L := by
    rw [← hL.range]
    exact ⟨_, rfl⟩
  rw [hact _ hmem, ← map_inv, ← map_mul, ← map_mul, hconj w]

theorem GGHalfTorusFrame.levi_action_upper
    (hK : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂) {b : G} (hb : b ∈ Bs) :
    ∃ s ∈ halfTorus m, ∀ w : SpecialLinearGroup (Fin (m + 1)) F2,
      b * ψ₂ (slUpper2Hom m w) * b⁻¹ = ψ₂ (slUpper2Hom m (s * w * s⁻¹)) := by
  obtain ⟨t, ht, hact⟩ := hK.act b hb
  obtain ⟨s, hs, hconj⟩ := exists_levi_conj_upper ht
  refine ⟨s, hs, fun w => ?_⟩
  have hmem : ψ₂ (slUpper2Hom m w) ∈ K := by
    rw [← hK.range]
    exact ⟨_, rfl⟩
  rw [hact _ hmem, ← map_inv, ← map_mul, ← map_mul, hconj w]

private theorem levi_conj_mem_right
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψ₁)
    (hK : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂)
    {c : SpecialLinearGroup (Fin (m + 1)) F2}
    (hc : ∀ w, ψ₂ (slUpper2Hom m w) = ψ₁ (slLower2Hom m (c * w * c⁻¹))) :
    ∀ s ∈ halfTorus m, c * s * c⁻¹ ∈ halfTorus m := by
  intro s hs
  have hb : ψ₂ (slUpper2Hom m s) ∈ Bs :=
    hK.torus_le (Subgroup.mem_map_of_mem ψ₂ (slUpper2Hom_mem_halfTorusK hs))
  obtain ⟨s₁, hs₁, hact⟩ := hL.levi_action_lower hb
  have hcs : c * s = s₁ * c := by
    apply ggHalf_eq_of_conj_eq
    intro w
    have harg : c * (s * w * s⁻¹) * c⁻¹ = s₁ * (c * w * c⁻¹) * s₁⁻¹ := by
      apply slLower2Hom_injective m
      apply hL.inj
      calc ψ₁ (slLower2Hom m (c * (s * w * s⁻¹) * c⁻¹))
          = ψ₂ (slUpper2Hom m (s * w * s⁻¹)) := (hc (s * w * s⁻¹)).symm
        _ = ψ₂ (slUpper2Hom m s) * ψ₂ (slUpper2Hom m w) * (ψ₂ (slUpper2Hom m s))⁻¹ := by
              simp only [map_mul, map_inv]
        _ = ψ₂ (slUpper2Hom m s) * ψ₁ (slLower2Hom m (c * w * c⁻¹)) *
              (ψ₂ (slUpper2Hom m s))⁻¹ := by rw [hc w]
        _ = ψ₁ (slLower2Hom m (s₁ * (c * w * c⁻¹) * s₁⁻¹)) := hact (c * w * c⁻¹)
    calc (c * s) * w * (c * s)⁻¹ = c * (s * w * s⁻¹) * c⁻¹ := by group
      _ = s₁ * (c * w * c⁻¹) * s₁⁻¹ := harg
      _ = (s₁ * c) * w * (s₁ * c)⁻¹ := by group
  have hconj : c * s * c⁻¹ = s₁ := by
    rw [hcs]
    group
  rw [hconj]
  exact hs₁

private theorem levi_conj_mem_left
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψ₁)
    (hK : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂)
    {c : SpecialLinearGroup (Fin (m + 1)) F2}
    (hc : ∀ w, ψ₂ (slUpper2Hom m w) = ψ₁ (slLower2Hom m (c * w * c⁻¹))) :
    ∀ s ∈ halfTorus m, c⁻¹ * s * c ∈ halfTorus m := by
  intro s hs
  have hb : ψ₁ (slLower2Hom m s) ∈ Bs :=
    hL.torus_le (Subgroup.mem_map_of_mem ψ₁ (slLower2Hom_mem_halfTorus hs))
  obtain ⟨s₂, hs₂, hact⟩ := hK.levi_action_upper hb
  have hcs : s * c = c * s₂ := by
    apply ggHalf_eq_of_conj_eq
    intro w
    have harg : s * (c * w * c⁻¹) * s⁻¹ = c * (s₂ * w * s₂⁻¹) * c⁻¹ := by
      apply slLower2Hom_injective m
      apply hL.inj
      calc ψ₁ (slLower2Hom m (s * (c * w * c⁻¹) * s⁻¹))
          = ψ₁ (slLower2Hom m s) * ψ₁ (slLower2Hom m (c * w * c⁻¹)) *
              (ψ₁ (slLower2Hom m s))⁻¹ := by simp only [map_mul, map_inv]
        _ = ψ₁ (slLower2Hom m s) * ψ₂ (slUpper2Hom m w) * (ψ₁ (slLower2Hom m s))⁻¹ := by
              rw [← hc w]
        _ = ψ₂ (slUpper2Hom m (s₂ * w * s₂⁻¹)) := hact w
        _ = ψ₁ (slLower2Hom m (c * (s₂ * w * s₂⁻¹) * c⁻¹)) := hc (s₂ * w * s₂⁻¹)
    calc (s * c) * w * (s * c)⁻¹ = s * (c * w * c⁻¹) * s⁻¹ := by group
      _ = c * (s₂ * w * s₂⁻¹) * c⁻¹ := harg
      _ = (c * s₂) * w * (c * s₂)⁻¹ := by group
  have hconj : c⁻¹ * s * c = s₂ := by
    rw [mul_assoc, hcs, inv_mul_cancel_left]
  rw [hconj]
  exact hs₂

theorem levi_torus_conj_mem
    (hL : GGHalfTorusFrame Bs L (halfTorus (m + 1 + 1)) ψ₁)
    (hK : GGHalfTorusFrame Bs K (halfTorusK (m + 1 + 1)) ψ₂)
    {c : SpecialLinearGroup (Fin (m + 1)) F2}
    (hc : ∀ w, ψ₂ (slUpper2Hom m w) = ψ₁ (slLower2Hom m (c * w * c⁻¹))) :
    ∀ s ∈ halfTorus m, c * s * c⁻¹ ∈ halfTorus m ∧ c⁻¹ * s * c ∈ halfTorus m :=
  fun s hs => ⟨levi_conj_mem_right hL hK hc s hs, levi_conj_mem_left hL hK hc s hs⟩

end CFSG.StandardType

end
