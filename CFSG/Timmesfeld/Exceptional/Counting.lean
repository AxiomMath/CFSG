module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Timmesfeld.Basic

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def collinearSet (D : Set G) (d : G) : Set G := {x | x ∈ D ∧ Commute d x ∧ d * x ∈ D}

theorem ncard_collinearSet_conj (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (g d : G) :
    (collinearSet D (g * d * g⁻¹)).ncard = (collinearSet D d).ncard := by
  have himg : collinearSet D (g * d * g⁻¹) = (fun x => g * x * g⁻¹) '' collinearSet D d := by
    ext y
    constructor
    · rintro ⟨hy, hdy, hdyD⟩
      refine ⟨g⁻¹ * y * g, ⟨by simpa using conj_mem_of_isClass hclass g⁻¹ hy, ?_, ?_⟩,
        by group⟩
      · have := (Commute.conj_iff g⁻¹).2 hdy
        simpa [mul_assoc] using this
      · have := conj_mem_of_isClass hclass g⁻¹ hdyD
        simpa [mul_assoc] using this
    · rintro ⟨x, ⟨hx, hdx, hdxD⟩, rfl⟩
      refine ⟨conj_mem_of_isClass hclass g hx, (Commute.conj_iff g).2 hdx, ?_⟩
      have := conj_mem_of_isClass hclass g hdxD
      simpa [mul_assoc] using this
  rw [himg, Set.ncard_image_of_injective _ fun x y h => by simpa using h]

end CFSG.Timmesfeld.Moufang
