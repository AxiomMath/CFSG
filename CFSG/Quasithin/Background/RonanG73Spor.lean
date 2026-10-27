module

public import CFSG.Quasithin.Background.RonanG73SporM12
public import CFSG.Quasithin.Background.RonanG73SporM22
public import CFSG.Quasithin.Background.RonanG73SporExcl

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem clause2
    {G L Γ A : Subgroup (GLV V)} {m : ℕ} [Finite ↥G] (h : G93Hyp Γ A L L m)
    (hΓG : Γ ≤ G) (hLG : L ≤ G) (hnorm : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hcent : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g ∈ L) (hq : CFSG.IsQuasisimple ↥L)
    (hSQT : CFSG.IsStronglyQuasithin ↥L)
    (hs : ∃ s : TauCeti.SporadicName, IsSporadic s (↥L ⧸ Subgroup.center ↥L)) :
    ((Nonempty (↥G ≃* MulAut ↥NativeSporadic.M12) ∧ IsPermCoreModule L NativeSporadic.M12) ∨
      (Nonempty (↥L ≃* ↥NativeSporadic.M22) ∧ Module.finrank (ZMod 2) V = 10 ∧
        IsMathieu22CodeOrCocode L) ∨
      (Nonempty (↥L ≃* ↥NativeSporadic.M24) ∧ Module.finrank (ZMod 2) V = 11 ∧
        IsMathieu24CodeOrCocode L) ∨
      (∃ N : Subgroup ↥G, N.Normal ∧ N.index = 2 ∧ IsHat ↥N ↥NativeSporadic.M22 ∧
        Module.finrank (ZMod 2) V = 12)) := by
  obtain ⟨s, he⟩ := hs
  by_cases hs12 : s = .M12
  · subst hs12
    obtain ⟨-, hperm, hG⟩ := sporadic_M12 h hΓG hLG hnorm hcent he
    exact Or.inl ⟨hG, hperm⟩
  by_cases hs22 : s = .M22
  · subst hs22
    rcases sporadic_M22 h hΓG hLG hnorm hcent he with ⟨hg, hd, hreal⟩ | ⟨hd, N, hN, hidx, hhat⟩
    · exact Or.inr (Or.inl ⟨hg, hd, hreal⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨N, hN, hidx, hhat, hd⟩))
  by_cases hs24 : s = .M24
  · subst hs24
    obtain ⟨hg, hd, hreal⟩ := sporadic_M24 h he
    exact Or.inr (Or.inr (Or.inl ⟨hg, hd, hreal⟩))
  exact (false_of_sporadic_excluded h hq hSQT s hs12 hs22 hs24 he).elim

end CFSG.Quasithin.RonanG73
