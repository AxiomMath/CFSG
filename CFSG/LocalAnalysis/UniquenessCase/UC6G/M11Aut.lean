module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6M11Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)


theorem kc633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KC633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  refine m.kc633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) ?_
  rw [hr3]
  exact M11K.absKC_m11

theorem kn633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KN633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  refine m.kn633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) ?_
  exact M11K.absKN_m11_of_eq hr3 _

theorem kinv633_of_m11 (h620 : m.C620) (hr3 : m.r = 3)
    (hX : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor m.Lbar .M11) : m.KInv633 := by
  obtain ⟨φ0⟩ := hX
  let φ : m.Lbar ≃* M11K.S11 := φ0
  exact m.kinv633_of_model h620 φ (by rw [hr3]; exact M11K.factorization_S11)
    (E₀ := M11K.Eu) (by rw [hr3]; exact M11K.isSylowOf_Eu) M11K.absKInv_m11

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
