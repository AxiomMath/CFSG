module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.AutEbar
public import CFSG.LocalAnalysis.UniquenessCase.UC6A10Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm (S₀ card_S₀ factorization_A10)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

namespace Mz614

variable {G : Type} [Group G] [Finite G] {Dat : Data G} (m : Mz614 Dat)

theorem kc633_of_A10 (h620 : m.C620) (hr : m.r = 5) (hA : IsAlt m.Lbar 10) : m.KC633 := by
  obtain ⟨φ⟩ := hA
  exact m.kc633_of_model h620 φ (by rw [hr]; exact factorization_A10) (E₀ := S₀)
    (by rw [hr]; exact A10Aut.isSylowOf_S₀) (A10Aut.absKC_A10 m.r)

theorem kn633_of_A10 (h620 : m.C620) (hr : m.r = 5) (hA : IsAlt m.Lbar 10) : m.KN633 := by
  obtain ⟨φ⟩ := hA
  exact m.kn633_of_model h620 φ (by rw [hr]; exact factorization_A10) (E₀ := S₀)
    (by rw [hr]; exact A10Aut.isSylowOf_S₀) (A10Aut.absKN_A10 hr _ S₀ card_S₀)

theorem kinv633_of_A10 (h620 : m.C620) (hr : m.r = 5) (hA : IsAlt m.Lbar 10) : m.KInv633 := by
  obtain ⟨φ⟩ := hA
  exact m.kinv633_of_model h620 φ (by rw [hr]; exact factorization_A10) (E₀ := S₀)
    (by rw [hr]; exact A10Aut.isSylowOf_S₀) A10Aut.absKInv_A10

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6G
