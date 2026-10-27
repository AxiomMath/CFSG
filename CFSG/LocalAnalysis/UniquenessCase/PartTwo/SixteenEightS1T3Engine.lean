module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1WCEngine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

theorem S16gRowCtx.false_of_t3Parab (h : S16gRowCtx D V₀ V L hV) (h3 : 3 ∈ D.sig)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hmult : ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) = 2 ^ k)
    {a : ℕ} (hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a) (ha : 2 ≤ a)
    (hcase : V₀ ≠ ⊥ ∨ 3 ≤ a ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  obtain ⟨J, hTJ, hJL, hJcard, hJexp⟩ := hP
  exact h.false_of_parabolic h3 (h.mBarGT_two hT) hsimple hmult hTJ hJL hJcard hJexp ha hcase

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
