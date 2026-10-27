module

public import CFSG.Quasithin.Recognition.F112Crit.LocalAction
public import CFSG.Quasithin.Recognition.F112Crit.Lemma63

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

structure IsLocalRegGrp (G₁ G₂ X : Subgroup G) (p : ℕ) : Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  ker_le : coreIn (G₁ ⊓ G₂) G₂ ≤ X
  le : X ≤ G₂
  normal : G₂ ≤ Subgroup.normalizer (X : Set G)
  relIndex_eq : (coreIn (G₁ ⊓ G₂) G₂).relIndex X = p
  inf_le : X ⊓ (G₁ ⊓ G₂) ≤ coreIn (G₁ ⊓ G₂) G₂
  sup_eq : X ⊔ (G₁ ⊓ G₂) = G₂
  not_le : ¬ G₁ ⊓ G₂ ≤ coreIn (G₁ ⊓ G₂) G₂

theorem IsLocalRegGrp.isLocalReg (hc : CritAmalgam G₀ G₁ G₂ T Z) {X : Subgroup G} {p : ℕ}
    (h : IsLocalRegGrp G₁ G₂ X p) : IsLocalReg (γ₁ G₀ G₁ G₂) p X := by
  have hG := hc.amalgam.gen
  have hN : ballStab 1 (γ₁ G₀ G₁ G₂) = coreIn (G₁ ⊓ G₂) G₂ := (CosetGeom.ballStab_one_γ₁ hG).1
  have hst : stab (γ₁ G₀ G₁ G₂) = G₂ := hc.stab_γ₁_eq
  have hst₀ : stab (γ₀ G₀ G₁ G₂) = G₁ := hc.stab_γ₀_eq
  have hXG₀ : X ≤ G₀ := h.le.trans hc.amalgam.le₂
  have hnb : ∀ γ ∈ nbrs (γ₁ G₀ G₁ G₂), ∃ g : ↥G₀, (g : G) ∈ G₂ ∧ g • γ₀ G₀ G₁ G₂ = γ := by
    intro γ hγ
    obtain ⟨g, hg, hgγ⟩ := CosetGeom.stab_transitive_on_nbrs
      (show γ₀ G₀ G₁ G₂ ∈ nbrs (γ₁ G₀ G₁ G₂) from
        (CosetGeom.adj_γ₀_γ₁ (G₀ := G₀) (G₁ := G₁) (G₂ := G₂)).symm) hγ
    rw [hst] at hg
    exact ⟨g, hg, hgγ⟩
  refine ⟨h.prime, h.ne_two, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hN]; exact h.ker_le
  · rw [hst]; exact h.le
  · rw [hst]; exact h.normal
  · rw [hN]; exact h.relIndex_eq
  · intro γ hγ
    obtain ⟨g, hgG₂, rfl⟩ := hnb γ hγ
    rw [CosetGeom.stab_smul, hst₀, hN]
    rintro x ⟨hxX, hxg⟩
    have hxg' : x ∈ conjSub (g : G) G₁ := hxg
    rw [mem_conjSub] at hxg'
    have hxG₂ : x ∈ G₂ := h.le hxX
    have h1 : (g : G)⁻¹ * x * g ∈ X ⊓ (G₁ ⊓ G₂) := by
      refine ⟨?_, hxg', ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (h.normal (G₂.inv_mem hgG₂)) x).mp hxX
        simpa using this
      · exact G₂.mul_mem (G₂.mul_mem (G₂.inv_mem hgG₂) hxG₂) hgG₂
    have h2 := h.inf_le h1
    have h3 := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_coreIn (G₁ ⊓ G₂) G₂ hgG₂) _).mp h2
    have e : (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x := by group
    rwa [e] at h3
  · intro γ hγ γ' hγ'
    obtain ⟨g₁, hg₁, rfl⟩ := hnb γ hγ
    obtain ⟨g₂, hg₂, rfl⟩ := hnb γ' hγ'
    have hu : (g₂ : G)⁻¹ * g₁ ∈ X ⊔ (G₁ ⊓ G₂) := by
      rw [h.sup_eq]; exact G₂.mul_mem (G₂.inv_mem hg₂) hg₁
    obtain ⟨x₁, hx₁, m₁, hm₁, hxm⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (show G₁ ⊓ G₂ ≤ Subgroup.normalizer (X : Set G) from inf_le_right.trans h.normal)).mp hu
    have hx : (g₂ : G) * x₁⁻¹ * (g₂ : G)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (h.normal hg₂) _).mp (X.inv_mem hx₁)
    have hm₁G₀ : m₁ ∈ G₀ := hc.amalgam.le₂ hm₁.2
    refine ⟨⟨(g₂ : G) * x₁⁻¹ * (g₂ : G)⁻¹, hXG₀ hx⟩, hx, ?_⟩
    have hk : (⟨m₁, hm₁G₀⟩ : ↥G₀) • γ₀ G₀ G₁ G₂ = γ₀ G₀ G₁ G₂ :=
      CosetGeom.smul_eq_of_mem_stab (by rw [hst₀]; exact hm₁.1)
    have e : (⟨(g₂ : G) * x₁⁻¹ * (g₂ : G)⁻¹, hXG₀ hx⟩ : ↥G₀) * g₁ = g₂ * ⟨m₁, hm₁G₀⟩ := by
      apply Subtype.ext
      show (g₂ : G) * x₁⁻¹ * (g₂ : G)⁻¹ * (g₁ : G) = (g₂ : G) * m₁
      have e1 : m₁ = x₁⁻¹ * ((g₂ : G)⁻¹ * g₁) := by rw [hxm]; group
      rw [e1]; group
    rw [← mul_smul, e, mul_smul, hk]
  · intro γ hγ
    obtain ⟨g, hgG₂, rfl⟩ := hnb γ hγ
    obtain ⟨m, hm, hmN⟩ := SetLike.not_le_iff_exists.mp h.not_le
    refine ⟨(g : G) * m * (g : G)⁻¹, ⟨?_, ?_⟩, ?_⟩
    · rw [hst]; exact G₂.mul_mem (G₂.mul_mem hgG₂ hm.2) (G₂.inv_mem hgG₂)
    · rw [CosetGeom.stab_smul, hst₀]
      show (g : G) * m * (g : G)⁻¹ ∈ conjSub (g : G) G₁
      rw [mem_conjSub]
      have e : (g : G)⁻¹ * ((g : G) * m * (g : G)⁻¹) * g = m := by group
      rw [e]; exact hm.1
    · rw [hN]
      intro hs
      exact hmN ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_coreIn (G₁ ⊓ G₂) G₂ hgG₂) m).mpr hs)

end CFSG.Quasithin.F112Crit
