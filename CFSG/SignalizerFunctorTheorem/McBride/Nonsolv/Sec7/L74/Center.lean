module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.GroupBasic
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.DirectProduct

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

namespace L74

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem zOf_le_zOf_of_mem {Ω : Set (Subgroup G)} {P X : Subgroup G} (hΩ : IsDirectProduct Ω P)
    (hX : X ∈ Ω) : zOf X ≤ zOf P := by
  intro w hw
  refine mem_zOf_iff.mpr ⟨hΩ.le hX (zOf_le X hw), fun v hv => ?_⟩
  have hle : sSup Ω ≤ Subgroup.centralizer ({w} : Set G) := by
    refine sSup_le fun Y hY y hy => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hYX : Y = X
    · subst hYX
      exact (mem_zOf_iff.mp hw).2 y hy
    · exact (hΩ.commute Y hY X hX hYX y hy w (zOf_le X hw)).eq
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hΩ.sSup_eq ▸ hv))

theorem isDirectProduct_zOf {Ω : Set (Subgroup G)} {P : Subgroup G} (hΩ : IsDirectProduct Ω P) :
    IsDirectProduct {Y | ∃ X ∈ Ω, Y = zOf X} (zOf P) where
  commute := by
    rintro _ ⟨X, hX, rfl⟩ _ ⟨X', hX', rfl⟩ hne x hx y hy
    exact hΩ.commute X hX X' hX' (fun h => hne (h ▸ rfl)) x (zOf_le X hx) y (zOf_le X' hy)
  indep := by
    rintro _ ⟨X, hX, rfl⟩
    refine (hΩ.indep hX).mono (zOf_le X) (sSup_le ?_)
    rintro _ ⟨⟨X', hX', rfl⟩, hne⟩
    exact (zOf_le X').trans (le_sSup ⟨hX', fun h => hne (by rw [h]; rfl)⟩)
  sSup_eq := by
    refine le_antisymm (sSup_le ?_) fun w hw => ?_
    · rintro _ ⟨X, hX, rfl⟩
      exact zOf_le_zOf_of_mem hΩ hX
    · obtain ⟨hwP, hwc⟩ := mem_zOf_iff.mp hw
      refine hΩ.mem_of_coord_mem (M := sSup {Y | ∃ X ∈ Ω, Y = zOf X}) hwP fun J hJ => ?_
      have hcoord : ∀ x ∈ J, x * (hΩ.coord hJ ⟨w, hwP⟩ : G) = (hΩ.coord hJ ⟨w, hwP⟩ : G) * x := by
        intro x hx
        have h1 : (⟨x, hΩ.le hJ hx⟩ : P) * ⟨w, hwP⟩ = ⟨w, hwP⟩ * ⟨x, hΩ.le hJ hx⟩ :=
          Subtype.ext (hwc x (hΩ.le hJ hx))
        have h2 := congrArg (hΩ.coord hJ) h1
        have h3 : hΩ.coord hJ ⟨x, hΩ.le hJ hx⟩ = ⟨x, hx⟩ :=
          Subtype.ext (hΩ.coord_of_mem hJ hx)
        rw [map_mul, map_mul, h3] at h2
        exact congrArg Subtype.val h2
      have hmem : (hΩ.coord hJ ⟨w, hwP⟩ : G) ∈ zOf J :=
        mem_zOf_iff.mpr ⟨(hΩ.coord hJ ⟨w, hwP⟩).2, fun v hv => hcoord v hv⟩
      exact le_sSup (show zOf J ∈ {Y | ∃ X ∈ Ω, Y = zOf X} from ⟨J, hJ, rfl⟩) hmem

end L74

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
