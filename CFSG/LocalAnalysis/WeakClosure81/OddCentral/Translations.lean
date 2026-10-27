module
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public section
namespace CFSG.LocalAnalysis.WeakClosure81.OddCentral
open Subgroup

private theorem fin3_third : ∀ a b : Fin 3, a ≠ b →
    ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧ ∀ d : Fin 3, d = a ∨ d = b ∨ d = c := by decide

theorem false_of_translations {G : Type*} [Group G] {Z : Subgroup G} {V : Fin 3 → Subgroup G}
    {y : Fin 3 → G} {𝒦 : Subgroup G → Prop}
    (hconj : ∀ a K, 𝒦 K → 𝒦 (K.map (MulAut.conj (y a)).toMonoidHom))
    (hP : ∀ K, 𝒦 K → ∃ a b, a ≠ b ∧ V a ≤ K ∧ V b ≤ K)
    (hZ : ∀ K, 𝒦 K → ∀ z ∈ Z, z ∈ K → z = 1)
    (hfix : ∀ a b, a ≠ b → ∀ v ∈ V b, y a * v * (y a)⁻¹ = v)
    (hZfix : ∀ a, ∀ z ∈ Z, y a * z * (y a)⁻¹ = z)
    (hmove : ∀ a, ∃ v ∈ V a, y a * v * (y a)⁻¹ * v⁻¹ ∈ Z ∧ y a * v * (y a)⁻¹ * v⁻¹ ≠ 1)
    {K₀ : Subgroup G} (hK₀ : 𝒦 K₀) : False := by
  have hmem : ∀ (g : G) (K : Subgroup G) (x : G), x ∈ K →
      g * x * g⁻¹ ∈ K.map (MulAut.conj g).toMonoidHom := fun g K x hx =>
    ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hout : ∀ a K, 𝒦 (K.map (MulAut.conj (y a)).toMonoidHom) → V a ≤ K →
      ¬ V a ≤ K.map (MulAut.conj (y a)).toMonoidHom := by
    intro a K hK' hVK hle
    obtain ⟨v, hv, hvZ, hv1⟩ := hmove a
    have h1 : y a * v * (y a)⁻¹ ∈ K.map (MulAut.conj (y a)).toMonoidHom := hmem _ _ _ (hVK hv)
    have h2 : v⁻¹ ∈ K.map (MulAut.conj (y a)).toMonoidHom := (Subgroup.inv_mem _ (hle hv))
    exact hv1 (hZ _ hK' _ hvZ (Subgroup.mul_mem _ h1 h2))
  obtain ⟨a, b, hab, haK, hbK⟩ := hP K₀ hK₀
  obtain ⟨c, hca, hcb, hall⟩ := fin3_third a b hab
  set K₁ := K₀.map (MulAut.conj (y a)).toMonoidHom with hK₁
  have hK₁𝒦 : 𝒦 K₁ := hconj a K₀ hK₀
  have hbK₁ : V b ≤ K₁ := fun v hv => by
    have := hmem (y a) K₀ v (hbK hv)
    rwa [hfix a b hab v hv] at this
  have haK₁ := hout a K₀ hK₁𝒦 haK
  have hcK₁ : V c ≤ K₁ := by
    obtain ⟨a', b', hab', ha', hb'⟩ := hP K₁ hK₁𝒦
    have ha'a : a' ≠ a := fun h => by subst h; exact haK₁ ha'
    have hb'a : b' ≠ a := fun h => by subst h; exact haK₁ hb'
    rcases hall a' with h | h | h
    · exact absurd h ha'a
    · rcases hall b' with h' | h' | h'
      · exact absurd h' hb'a
      · exact absurd (h.trans h'.symm) hab'
      · exact h' ▸ hb'
    · exact h ▸ ha'
  set K₂ := K₁.map (MulAut.conj (y c)).toMonoidHom with hK₂
  have hK₂𝒦 : 𝒦 K₂ := hconj c K₁ hK₁𝒦
  have hcK₂ := hout c K₁ hK₂𝒦 hcK₁
  have haK₂ : ¬ V a ≤ K₂ := by
    intro hle
    obtain ⟨v, hv, hvZ, hv1⟩ := hmove a
    have h1 : y a * v * (y a)⁻¹ ∈ K₁ := hmem _ _ _ (haK hv)
    have h2 : y c * (y a * v * (y a)⁻¹) * (y c)⁻¹ ∈ K₂ := hmem _ _ _ h1
    have e : y c * (y a * v * (y a)⁻¹) * (y c)⁻¹ = y a * v * (y a)⁻¹ := by
      have hd : y a * v * (y a)⁻¹ = (y a * v * (y a)⁻¹ * v⁻¹) * v := by group
      rw [hd, show y c * ((y a * v * (y a)⁻¹ * v⁻¹) * v) * (y c)⁻¹ =
        (y c * (y a * v * (y a)⁻¹ * v⁻¹) * (y c)⁻¹) * (y c * v * (y c)⁻¹) by group,
        hZfix c _ hvZ, hfix c a hca v hv]
    rw [e] at h2
    exact hv1 (hZ _ hK₂𝒦 _ hvZ (Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ (hle hv))))
  obtain ⟨a'', b'', hab'', ha'', hb''⟩ := hP K₂ hK₂𝒦
  have h1 : a'' = b := by
    rcases hall a'' with h | h | h
    · subst h; exact absurd ha'' haK₂
    · exact h
    · subst h; exact absurd ha'' hcK₂
  have h2 : b'' = b := by
    rcases hall b'' with h | h | h
    · subst h; exact absurd hb'' haK₂
    · exact h
    · subst h; exact absurd hb'' hcK₂
  exact hab'' (h1.trans h2.symm)

end CFSG.LocalAnalysis.WeakClosure81.OddCentral

