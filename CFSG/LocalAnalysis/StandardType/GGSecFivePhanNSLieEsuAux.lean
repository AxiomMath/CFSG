module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggNSLieN3A_esuRecipe {p : ℕ} {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (hrow : ggRowP_ESU p lab) (hraw : LargeEvenRawDatum lab Q) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (d : ℕ),
      Nat.card K = (2 ^ lab.n) ^ 2 ∧ 4 ≤ d ∧ d = lab.rank + 1 ∧
      Q (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ lab.n)))
        (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGUSet (Fin d) K (2 ^ lab.n)))
        (LargeEvenMatFieldImage (LargeEvenProjMk _)) := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases hrow.1 with ⟨htwA, hr⟩ | ⟨htwD, hr3⟩
  · obtain rfl : tag = .twA := htwA
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
    have hr' : 3 ≤ rank := hr
    exact ⟨K, hf, hfin, rank + 1, by simpa using hK, by omega, by simp, hQ⟩
  · obtain rfl : rank = 3 := hr3
    obtain rfl : tag = .twD := htwD
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hraw
    simp only [show ¬ (3 : ℕ) = 2 by norm_num, if_false, if_true] at hraw
    obtain ⟨K, hf, hfin, hK, hQ⟩ := hraw
    exact ⟨K, hf, hfin, 4, by simpa using hK, by norm_num, by simp, hQ⟩

theorem ggNSLieN3A_esuCore {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    {P : ℕ → LargeEvenLabel → Prop} (h : GGInnerDiagOnLabel P p Bs X)
    (hP : ∀ p lab, P p lab → ggRowP_ESU p lab) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (lab : LargeEvenLabel) (m : ℕ)
      (θ : ↥X ⧸ Subgroup.center ↥X ≃*
        LargeEvenProj (LargeEvenSUGroup (Fin m) K (2 ^ lab.n))),
      Nat.card K = (2 ^ lab.n) ^ 2 ∧ 4 ≤ m ∧ m = lab.rank + 1 ∧ P p lab ∧
      p ∣ 2 ^ lab.n + 1 ∧ commutator X = ⊤ ∧ LargeEvenInLambda2 lab ∧
      Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
          (LargeEvenProjMk (LargeEvenSUGroup (Fin m) K (2 ^ lab.n)))
          (LargeEvenGUSet (Fin m) K (2 ^ lab.n)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, hRgrp, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hs, hna, θ, hlabP, hBsN, hbs⟩ := hQ
  have hrow : ggRowP_ESU p lab := hP p lab hlabP
  obtain ⟨K, hf, hfin, m, hK, h4m, hmrank, hQ'⟩ := ggNSLieN3A_esuRecipe hrow hraw
  obtain ⟨hs', hna', θ', hrow', hBsN', hbs'⟩ := hQ'
  exact ⟨K, hf, hfin, lab, m, θ', hK, h4m, hmrank, hlabP, hrow.2, hperf, hlab, hBsN', hbs'⟩

end CFSG.StandardType

end
