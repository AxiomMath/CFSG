module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma l48mH_unique {G : Type} [Group G] {B L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hψ : Function.Surjective ψ)
    {b : ↥B} {g g' : LargeEvenProj (LargeEvenSpGroup K r)}
    (hg : ∀ l : ↥L,
      ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = g * ψ l * g⁻¹)
    (hg' : ∀ l : ↥L,
      ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = g' * ψ l * g'⁻¹) :
    g = g' := by
  have hc : g⁻¹ * g' ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K r)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    obtain ⟨l, rfl⟩ := hψ x
    have h1 := hg l
    have h2 := hg' l
    calc ψ l * (g⁻¹ * g') = g⁻¹ * (g * ψ l * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * ψ l * g'⁻¹) * g' := by rw [← h1, h2]
      _ = (g⁻¹ * g') * ψ l := by group
  have h1 : g⁻¹ * g' = 1 := by
    have hmem : g⁻¹ * g' ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K r))) := by
      rwa [← TableBSymp.center_spProj_eq_bot]
    exact Subgroup.mem_bot.mp hmem
  have h2 : g' = g := by
    calc g' = g * (g⁻¹ * g') := by group
      _ = g * 1 := by rw [h1]
      _ = g := by rw [mul_one]
  exact h2.symm

theorem ggB2der_beta_of_exists {G : Type} [Group G] {B L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    {r : ℕ} [NeZero r] {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K r)}
    (hψ : Function.Surjective ψ)
    (h : ∀ b : ↥B, ∃ g : LargeEvenProj (LargeEvenSpGroup K r), ∀ l : ↥L,
      ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = g * ψ l * g⁻¹) :
    ∃ β : ↥B →* LargeEvenProj (LargeEvenSpGroup K r), ∀ (b : ↥B) (l : ↥L),
      ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b)) l) = β b * ψ l * (β b)⁻¹ := by
  classical
  choose β hβ using h
  have hmul : ∀ b c : ↥B, β (b * c) = β b * β c := by
    intro b c
    refine l48mH_unique (hBL := hBL) hψ (b := b * c) (g := β (b * c)) (g' := β b * β c) ?_ ?_
    · intro l
      exact hβ (b * c) l
    · intro l
      have hincl : Subgroup.inclusion hBL (b * c) =
          Subgroup.inclusion hBL b * Subgroup.inclusion hBL c :=
        map_mul (Subgroup.inclusion hBL) b c
      have hnm : L.normalizerMonoidHom (Subgroup.inclusion hBL (b * c)) =
          L.normalizerMonoidHom (Subgroup.inclusion hBL b) *
            L.normalizerMonoidHom (Subgroup.inclusion hBL c) := by
        rw [hincl, map_mul]
      calc ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL (b * c))) l)
          = ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL b))
                ((L.normalizerMonoidHom (Subgroup.inclusion hBL c)) l)) := by
              rw [hnm, MulAut.mul_apply]
        _ = β b * ψ ((L.normalizerMonoidHom (Subgroup.inclusion hBL c)) l) * (β b)⁻¹ :=
              hβ b _
        _ = β b * (β c * ψ l * (β c)⁻¹) * (β b)⁻¹ := by rw [hβ c l]
        _ = (β b * β c) * ψ l * (β b * β c)⁻¹ := by group
  refine ⟨MonoidHom.mk' β hmul, ?_⟩
  intro b l
  simpa only [MonoidHom.mk'_apply] using hβ b l

end CFSG.StandardType
