module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPairs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLUnitaryCubic

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)


private theorem ggInndiagOnCompAt_of_recipeUnitary {lab : LargeEvenLabel} {d g : ℕ} (hg : 1 ≤ g)
    (hd : 3 ≤ d) (hd6 : d ≤ 6) (hdq : ¬(d = 3 ∧ 2 ^ g = 2))
    (hR : ∀ Q : LargeEvenRawCont, LargeEvenRawDatum lab Q = LargeEvenRecipeUnitary d (2 ^ g) Q) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ ∨
      l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  intro Q hQ
  rw [hR] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  intro _ _ hfin s t n hs3 _ ht3 hst hsI htI hn J₁ hJ₁ hmark
  have hJ : CFSG.Open.IsComponentOf J₁ (fixSubgroup s) := by
    have hfix : ggFix s = fixSubgroup s := Subgroup.ext fun _ => Iff.rfl
    rw [← hfix]
    exact CFSG.Assembly.isComponentOf_iff_open.1 hJ₁
  exact not_ggOutsideInndiag_of_recipeUnitary hg hK hd hd6 hdq hfin hsI htI hs3 ht3 hst hn hJ hmark

theorem ggInndiagOnCompAt_unitary {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : (lab.tag = .twA ∧ lab.rank ≤ 5) ∨ (lab.tag = .twD ∧ lab.rank = 3)) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ ∨
      l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ := by
  obtain ⟨tag, r, g⟩ := lab
  rcases htag with ⟨htag, hr⟩ | ⟨htag, hr⟩ <;> dsimp only at htag hr <;> subst htag
  · obtain ⟨hg, hr1, hr2⟩ := hlab
    have hg' : 1 ≤ g := hg
    have hr1' : 2 ≤ r := hr1
    have hr2' : r = 2 → 2 ≤ g := hr2
    have hdq : ¬(r + 1 = 3 ∧ 2 ^ g = 2) := fun ⟨h3, h2⟩ => by
      have : 2 ^ 2 ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) (hr2' (by omega))
      omega
    exact ggInndiagOnCompAt_of_recipeUnitary (d := r + 1) hg' (by omega) (by omega) hdq
      fun _ => rfl
  · subst hr
    obtain ⟨hg, -⟩ := hlab
    have hg' : 1 ≤ g := hg
    exact ggInndiagOnCompAt_of_recipeUnitary (d := 4) hg' (by norm_num) (by norm_num)
      (fun h => absurd h.1 (by decide)) fun _ => rfl

theorem ggInndiagOnCompAt_unitary_dPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : (lab.tag = .twA ∧ lab.rank ≤ 5) ∨ (lab.tag = .twD ∧ lab.rank = 3)) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ :=
  ggInndiagOnCompAt_mono (fun _ _ h => h.elim Or.inl fun h => Or.inr (Or.inl h))
    (ggInndiagOnCompAt_unitary hlab htag)

theorem ggInndiagOnCompAt_unitary_aPair {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : (lab.tag = .twA ∧ lab.rank ≤ 5) ∨ (lab.tag = .twD ∧ lab.rank = 3)) :
    GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩ :=
  ggInndiagOnCompAt_mono (fun _ _ h => Or.inr (Or.inr h)) (ggInndiagOnCompAt_unitary hlab htag)

end CFSG.StandardType.SCFourCover

end
