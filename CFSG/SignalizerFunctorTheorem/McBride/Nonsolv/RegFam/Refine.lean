module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

variable {G : Type*} [Group G]

theorem le_normalizer_sSup {M : Subgroup G} {T : Set (Subgroup G)}
    (h : ∀ Z ∈ T, M ≤ Subgroup.normalizer (Z : Set G)) :
    M ≤ Subgroup.normalizer ((sSup T : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg
  have hle : sSup T ≤ (sSup T).comap (MulAut.conj g).toMonoidHom := by
    refine sSup_le fun Z hZ z hz => ?_
    exact le_sSup hZ ((Subgroup.le_normalizer_iff.mp (h Z hZ)) g hg z hz)
  exact fun k hk => hle hk

theorem commutatorElement_mem_inf {X Y : Subgroup G} {x y : G} (hx : x ∈ X) (hy : y ∈ Y)
    (hyX : y ∈ Subgroup.normalizer (X : Set G)) (hxY : x ∈ Subgroup.normalizer (Y : Set G)) :
    ⁅x, y⁆ ∈ X ⊓ Y := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have h : y * x⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hyX x⁻¹).mp (inv_mem hx)
    have e : ⁅x, y⁆ = x * (y * x⁻¹ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem hx h
  · have h : x * y * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hxY y).mp hy
    have e : ⁅x, y⁆ = x * y * x⁻¹ * y⁻¹ := rfl
    rw [e]
    exact mul_mem h (inv_mem hy)

theorem IsDirectProduct.refine_of_perfect [Finite G] {M : Subgroup G} {Ω Ω' : Set (Subgroup G)}
    (hΩ : IsDirectProduct Ω M) (hΩ' : IsDirectProduct Ω' M) (hM : ⁅M, M⁆ = M) :
    IsDirectProduct {Z | ∃ X ∈ Ω, ∃ Y ∈ Ω', Z = X ⊓ Y} M := by
  set R : Set (Subgroup G) := {Z | ∃ X ∈ Ω, ∃ Y ∈ Ω', Z = X ⊓ Y} with hR
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨X₁, hX₁, Y₁, hY₁, rfl⟩ _ ⟨X₂, hX₂, Y₂, hY₂, rfl⟩ hne x hx y hy
    by_cases hX : X₁ = X₂
    · have hY : Y₁ ≠ Y₂ := fun hY => hne (by rw [hX, hY])
      exact hΩ'.commute Y₁ hY₁ Y₂ hY₂ hY x (Subgroup.mem_inf.mp hx).2 y
        (Subgroup.mem_inf.mp hy).2
    · exact hΩ.commute X₁ hX₁ X₂ hX₂ hX x (Subgroup.mem_inf.mp hx).1 y
        (Subgroup.mem_inf.mp hy).1
  · rintro _ ⟨X₀, hX₀, Y₀, hY₀, rfl⟩
    have hle : sSup (R \ {X₀ ⊓ Y₀}) ≤ sSup (Ω \ {X₀}) ⊔ (X₀ ⊓ sSup (Ω' \ {Y₀})) := by
      refine sSup_le ?_
      rintro _ ⟨⟨X, hX, Y, hY, rfl⟩, hne⟩
      by_cases hXX : X = X₀
      · subst hXX
        have hYY : Y ≠ Y₀ := fun h => hne (by rw [h]; rfl)
        exact le_sup_of_le_right (le_inf inf_le_left (inf_le_right.trans (le_sSup ⟨hY, hYY⟩)))
      · exact le_sup_of_le_left (inf_le_left.trans (le_sSup ⟨hX, hXX⟩))
    refine Disjoint.mono_right hle ?_
    rw [Subgroup.disjoint_def]
    intro u hu hu'
    have hcomm : ∀ x ∈ sSup (Ω \ {X₀}), ∀ y ∈ X₀ ⊓ sSup (Ω' \ {Y₀}), Commute x y :=
      fun x hx y hy => (hΩ.commute_sSup_diff hX₀ y (Subgroup.mem_inf.mp hy).1 x hx).symm
    obtain ⟨a, ha, b, hb, hab⟩ := (mem_sup_iff_of_commute hcomm).mp hu'
    have hbX : b ∈ X₀ := (Subgroup.mem_inf.mp hb).1
    have huX : u ∈ X₀ := (Subgroup.mem_inf.mp hu).1
    have haX : a ∈ X₀ := by
      have e : a = u * b⁻¹ := by rw [← hab]; group
      rw [e]
      exact mul_mem huX (inv_mem hbX)
    have ha1 : a = 1 := by
      have h : a ∈ X₀ ⊓ sSup (Ω \ {X₀}) := Subgroup.mem_inf.mpr ⟨haX, ha⟩
      rw [disjoint_iff.mp (hΩ.indep hX₀), Subgroup.mem_bot] at h
      exact h
    have hub : u = b := by rw [← hab, ha1, one_mul]
    have hu2 : u ∈ Y₀ ⊓ sSup (Ω' \ {Y₀}) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu).2, hub ▸ (Subgroup.mem_inf.mp hb).2⟩
    rw [disjoint_iff.mp (hΩ'.indep hY₀), Subgroup.mem_bot] at hu2
    exact hu2
  · refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨X, hX, Y, hY, rfl⟩
      exact inf_le_left.trans (hΩ.le hX)
    · have hnorm : M ≤ Subgroup.normalizer ((sSup R : Subgroup G) : Set G) := by
        refine le_normalizer_sSup ?_
        rintro _ ⟨X, hX, Y, hY, rfl⟩
        exact le_trans (le_inf (hΩ.le_normalizer hX) (hΩ'.le_normalizer hY))
          Subgroup.inf_normalizer_le_normalizer_inf
      have hstep : ∀ Y ∈ Ω', M ≤ sectionCentralizer (sSup R) Y := by
        intro Y hY
        refine (le_of_eq hΩ.sSup_eq.symm).trans (sSup_le fun X hX x hx => ?_)
        have hxM : x ∈ M := hΩ.le hX hx
        refine mem_sectionCentralizer_iff.mpr
          ⟨hnorm hxM, hΩ'.le_normalizer hY hxM, fun y hy => ?_⟩
        have hmem : X ⊓ Y ∈ R := ⟨X, hX, Y, hY, rfl⟩
        exact le_sSup hmem (commutatorElement_mem_inf hx hy
          (hΩ.le_normalizer hX (hΩ'.le hY hy)) (hΩ'.le_normalizer hY hxM))
      have hstep2 : M ≤ sectionCentralizer (sSup R) M := by
        refine (le_of_eq hΩ'.sSup_eq.symm).trans (sSup_le fun Y hY y hy => ?_)
        have hyM : y ∈ M := hΩ'.le hY hy
        refine mem_sectionCentralizer_iff.mpr
          ⟨hnorm hyM, Subgroup.le_normalizer hyM, fun m hm => ?_⟩
        have h := (mem_sectionCentralizer_iff.mp (hstep Y hY hm)).2.2 y hy
        rw [← commutatorElement_inv]
        exact inv_mem h
      have hcomm : ⁅M, M⁆ ≤ sSup R := Subgroup.commutator_le.mpr fun g₁ hg₁ g₂ hg₂ =>
        (mem_sectionCentralizer_iff.mp (hstep2 hg₁)).2.2 g₂ hg₂
      rw [hM] at hcomm
      exact hcomm

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
