module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddJ1Core
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native

theorem facts134Odd_j1Local :
    ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (p : ℕ) (y g : A),
      SQTKHypCat A → p.Prime → 5 ≤ p → IsSporadic .J1 ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) →
      (∃ k : ℕ, g ^ 2 ^ k = 1) → g * y * g⁻¹ = y := by
  intro A _ _ L B U p y g _ hp hp5 hL hUB hBL hU hB hyB hy hgL hgU hgy hg2
  obtain ⟨e⟩ := hL
  exact j1_local_of_odd_prime A L B U p y g e hp hp5 hUB hBL hU hB hyB hy hgL hgU hgy hg2

end CFSG.Quasithin.H13.NQCore
