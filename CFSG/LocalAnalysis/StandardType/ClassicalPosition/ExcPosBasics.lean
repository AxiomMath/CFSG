module

public import CFSG.LocalAnalysis.StandardType.GGSixExcPosRangeDefs
public import Mathlib.Dynamics.PeriodicPts.Defs

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

theorem exc_neighbour_in_range {X : Type} [Group X]
    (K R : Subgroup X)
    (h :
      (∃ (m g : ℕ) (β : Fin (ggU .PSL (m + 1) g).D.rank → ℤ),
        ((4 ≤ m ∧ 1 ≤ g) ∨ (m = 3 ∧ 2 ≤ g)) ∧ β ∈ (ggU .PSL (m + 1) g).D.roots ∧
          GGRootVia (ggU .PSL (m + 1) g) K R β) ∨
      (∃ (n g : ℕ) (β : Fin (ggU .PSU n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
        β ∈ (ggU .PSU n g).D.roots ∧ GGLongRoot (ggU .PSU n g).D β ∧
          GGRootVia (ggU .PSU n g) K R β) ∨
      (∃ (g : ℕ) (β : Fin (ggU .PSU 6 g).D.rank → ℤ), 2 ≤ g ∧ β ∈ (ggU .PSU 6 g).D.roots ∧
        2 • β ∉ (ggU .PSU 6 g).D.roots ∧ GGRootVia (ggU .PSU 6 g) K R β) ∨
      (∃ (n g : ℕ) (β : Fin (ggU .POmegaPlus n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
        β ∈ (ggU .POmegaPlus n g).D.roots ∧ GGRootVia (ggU .POmegaPlus n g) K R β) ∨
      (∃ (n g : ℕ) (β : Fin (ggU .POmegaMinus n g).D.rank → ℤ), 4 ≤ n ∧ 1 ≤ g ∧
        β ∈ (ggU .POmegaMinus n g).D.roots ∧ GGLongRoot (ggU .POmegaMinus n g).D β ∧
        GGRootVia (ggU .POmegaMinus n g) K R β) ∨
      (∃ (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F) (g : ℕ)
          (β : Fin (triD4Universal F σ).D.rank → ℤ), TriField F σ g ∧
        GGLongRoot (triD4Universal F σ).D β ∧ GGRootVia (triD4Universal F σ) K R β) ∨
      (∃ (t : StatedLieTag) (g : ℕ) (β : Fin (ggU t 0 g).D.rank → ℤ),
        (t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ 1 ≤ g ∧ β ∈ (ggU t 0 g).D.roots ∧
        GGRootVia (ggU t 0 g) K R β) ∨
      (∃ (g : ℕ) (β : Fin (ggU .twistedE6 0 g).D.rank → ℤ), 1 ≤ g ∧
        β ∈ (ggU .twistedE6 0 g).D.roots ∧ GGLongRoot (ggU .twistedE6 0 g).D β ∧
        GGRootVia (ggU .twistedE6 0 g) K R β)) :
    CFSG.StandardType.LieKnownR2.GGThmSRangeAt K R := by
  unfold CFSG.StandardType.LieKnownR2.GGThmSRangeAt
  rcases h with
    ⟨m, g, β, hmg, hβ, hvia⟩ | ⟨n, g, β, hn, hg, hβ, hlong, hvia⟩ |
    ⟨g, β, hg, hβ, h2β, hvia⟩ | ⟨n, g, β, hn, hg, hβ, hvia⟩ |
    ⟨n, g, β, hn, hg, hβ, hlong, hvia⟩ | ⟨F, hF, hFfin, σ, g, β, htri, hlong, hvia⟩ |
    ⟨t, g, β, ht, hg, hβ, hvia⟩ | ⟨g, β, hg, hβ, hlong, hvia⟩
  · refine Or.inl ⟨m, g, β, ?_, hβ, hvia⟩
    rcases hmg with ⟨hm, hg⟩ | ⟨hm, hg⟩
    · by_cases hg1 : g = 1
      · exact Or.inl ⟨hg1, hm⟩
      · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    · exact Or.inr (Or.inl ⟨hg, by omega⟩)
  · exact Or.inr (Or.inl ⟨n, g, β, by omega, by omega, hβ, Or.inl hlong, hvia⟩)
  · exact Or.inr (Or.inl ⟨6, g, β, by omega, by omega, hβ, Or.inr ⟨le_rfl, hg, h2β⟩, hvia⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, g, β, hn, hβ, hvia⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, g, β, hn, hβ, hlong, hvia⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨F, hF, hFfin, σ, g, β, htri, hlong, hvia⟩)))))
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨t, g, β, ?_, hg, hβ, hvia⟩))))))
    rcases ht with rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨g, β, hβ, Or.inl ⟨hg, hlong⟩, hvia⟩))))))

end CFSG.StandardType.LieKnownR2.ExcPos
