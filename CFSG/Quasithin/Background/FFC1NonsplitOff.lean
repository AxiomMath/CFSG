module

public import CFSG.Quasithin.Background.FFC1NonsplitL3
public import CFSG.Quasithin.Background.FFC2Core
public import CFSG.Quasithin.Background.B5FinSp

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped commutatorElement

theorem false_of_binaryNaturalSp4_one {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {U Z : Subgroup V} (hq : CFSG.IsQuasisimple ↥L) (h : BinaryNaturalSp4 L U Z 1) : False := by
  obtain ⟨π, hπ⟩ := asSp4S6 V L U Z h
  have : Group.IsPerfect ↥L := hq.1
  have : Nontrivial ↥L := nontrivial_of_isQuasisimple hq
  exact not_surjective_perm_of_perfect (n := 6) (by norm_num) ⟨π, hπ.1⟩

@[expose] def AsB51NonsplitOffSp4 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L T : Subgroup (MulAut V), B51Hyp G L → commV L ∈ IrrPlus L ⊤ → IsSylowTwoOf T G →
      fixV L ⊓ commV L ≠ ⊥ → ∀ n : ℕ, 1 < n →
      BinaryNaturalSp4 L (commV L) (fixV L ⊓ commV L) n →
      ∀ A, IsFFStarOffenderOn T A (commV L) → A ≤ L

theorem asB51NonsplitOff_of_sp4 (h : AsB51NonsplitOffSp4) : AsB51NonsplitOff := by
  intro V _ _ hV G L T hHyp hU hT hC hcase A hA
  rcases hcase with hL3 | ⟨n, hn⟩
  · exact hA.1.trans (sylow_le_of_binaryNaturalSL_three hV hHyp hU hT hL3)
  · by_cases hn1 : n = 1
    · subst hn1
      exact (false_of_binaryNaturalSp4_one (B5.quasi_L hHyp) hn).elim
    · have h1 : 1 ≤ n := B5.one_le_of_binaryNaturalSp4 hn
      exact h V hV G L T hHyp hU hT hC n (by omega) hn A hA

end FFC

end CFSG.Quasithin
