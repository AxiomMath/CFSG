module

public import CFSG.LocalAnalysis.WeakClosure81.W15TenZStar
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Cfg1511

variable {M V₀ V U S H P : Subgroup G}

theorem exists_of_inputs (hI : NamedInputs15 G) (hW : W15Eight1 G)
    (h2b : W15Ten2b G) (hS : Std15 G) (h : Cex15 M V₀ V U S) (hP : Hyp1510 V₀ V U S H P) :
    ∃ (Q₀ : Subgroup G) (p : ℕ), Cfg1511 M V₀ V U S H P Q₀ p := by
  obtain ⟨Q₀, hQ⟩ := hP.exists_oddCore hI hW hS h
  obtain ⟨p, hp, hshape⟩ := h2b M V₀ V U S H P Q₀ hS h hP hQ
  exact ⟨Q₀, p, ⟨hS, hI, hW, h, hP, hQ, hp, hshape⟩⟩

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
