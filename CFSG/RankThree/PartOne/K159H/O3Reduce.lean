module

public import CFSG.RankThree.PartOne.K159H.O3Step

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ} {qA : QuadraticForm K A}
  (S : Subgroup (Fin r → Kˣ))

open _root_.Classical in
@[expose] def bad (g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :
    Finset (Fin r ⊕ Fin r) :=
  Finset.univ.filter fun j => ¬ TrivOn S j ∧ g (hypVec K A j) ≠ hypVec K A j

variable {S}

theorem mem_bad {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} {j : Fin r ⊕ Fin r} :
    j ∈ bad S g ↔ ¬ TrivOn S j ∧ g (hypVec K A j) ≠ hypVec K A j := by
  simp [bad]

theorem reduce [CharP K 2] (n : ℕ) :
    ∀ g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A), g ∈ CO qA S → (bad S g).card = n →
      ∃ h ∈ Rts qA S ⊔ Tor K A r, ∃ g' ∈ CO qA S, g = h * g' ∧
        ∀ j, ¬ TrivOn S j → g' (hypVec K A j) = hypVec K A j := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g hg hn
    by_cases hbad : ∃ j, ¬ TrivOn S j ∧ g (hypVec K A j) ≠ hypVec K A j
    · obtain ⟨j₀, hj₀, hne⟩ := hbad
      obtain ⟨h₁, hh₁, g₁, hg₁, hgeq, hcls, hfix⟩ := step hj₀ hg
      have hj₀bad : j₀ ∈ bad S g := mem_bad.2 ⟨hj₀, hne⟩
      have hsub : bad S g₁ ⊆ (bad S g).erase j₀ := by
        intro j hj
        obtain ⟨hjt, hjne⟩ := mem_bad.1 hj
        rw [Finset.mem_erase]
        refine ⟨?_, mem_bad.2 ⟨hjt, fun hjg => hjne (hfix j hjg)⟩⟩
        rintro rfl
        exact hjne (hcls j (SimOn.refl S j)).1
      have hlt : (bad S g₁).card < n :=
        hn ▸ (Finset.card_le_card hsub).trans_lt (Finset.card_erase_lt_of_mem hj₀bad)
      obtain ⟨h₂, hh₂, g₂, hg₂, hg₁eq, hfix₂⟩ := ih _ hlt g₁ hg₁ rfl
      exact ⟨h₁ * h₂, mul_mem hh₁ hh₂, g₂, hg₂, by rw [hgeq, hg₁eq, mul_assoc], hfix₂⟩
    · push Not at hbad
      exact ⟨1, one_mem _, g, hg, (one_mul g).symm, hbad⟩

end CFSG.RankThree.PartOne.K159H
