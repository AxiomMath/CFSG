module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParityAt
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLBridgeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLPlusOfKnown
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

private theorem odd_of_three_dvd_two_pow_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ho
  · have : 2 ^ (k + k) % 3 = 1 := by
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  · exact ho

private theorem exists_label_of_largeEvenMarking {X : Type*} [Group X]
    {S : LargeEvenLabel → Prop} (h : LargeEvenMarking X fun l _ _ _ _ _ => S l) :
    ∃ l, S l ∧ LargeEvenMarking X fun l' _ _ _ _ _ => l' = l := by
  obtain ⟨hX, l, hl, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := largeEvenRawDatum_exists hraw
  exact ⟨l, hS, hX, l, hl,
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem ne_top_of_isComponentOf_ggFix {R : Type} [Group R] {s : MulAut R} (hs : s ≠ 1)
    {J₁ : Subgroup R} (hJ : IsComponentOf J₁ (ggFix s)) : J₁ ≠ ⊤ := by
  rintro rfl
  exact hs (MulEquiv.ext fun r => by simpa using mem_ggFix.1 (hJ.1 (Subgroup.mem_top r)))


private theorem largeEvenLabelAll_three_dvd_of_odd_label {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      Finite R → ∀ s ∈ I, s ^ 3 = 1 → s ≠ 1 → ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
        ∀ S : LargeEvenLabel → Prop, (∀ l, S l → l.tag ≠ .twD ∧ Odd l.n) →
          LargeEvenMarking ↥J₁ (fun l _ _ _ _ _ => S l) → 3 ∣ 2 ^ lab.n + 1 := by
  refine (largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix hlab).mono
    fun R _ I _ h hR hna hfin s hsI hs3 hs1 J₁ hJ₁ S hS hmark => ?_
  obtain ⟨l, hl, hmark'⟩ := exists_label_of_largeEvenMarking hmark
  have hdvd := h hR hna hfin 3 Nat.prime_three (by norm_num) s hsI hs3 hs1 J₁ hJ₁ l
    (fun h' => absurd h' (hS l hl).1) hmark'
  simpa using Odd.nat_add_dvd_pow_add_pow 2 1 ((hS l hl).2.of_dvd_nat hdvd)

theorem ggTwE6OfOutsideAt_of_three_dvd {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : 3 ∣ 2 ^ lab.n + 1 → LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → Finite R →
      ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I →
        t ∈ I → 3 ∣ 2 ^ n + 1 →
        ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
          LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ =>
            lab' = ⟨.D, 4, n⟩ ∨ lab' = ⟨.triD4, 0, n⟩ ∨ lab' = ⟨.A, 2, 3 * n⟩ ∨
              lab' = ⟨.twA, 2, 3 * n⟩) →
          ¬ GGOutsideInndiag J₁ t) :
    GGTwE6OfOutsideAt lab := by
  by_cases h3 : 3 ∣ 2 ^ lab.n + 1
  · exact ggTwE6OfOutsideAt_of_ne_one hlab (h h3)
  refine ggTwE6OfOutsideAt_of_ne_one hlab
    ((largeEvenLabelAll_three_dvd_of_odd_label hlab).mono ?_)
  intro R _ I _ hp hR hna hfin s t n hs3 hs1 _ _ hsI _ hn J₁ hJ₁ hmark
  have hodd := odd_of_three_dvd_two_pow_add_one hn
  refine absurd (hp hR hna hfin s hsI hs3 hs1 J₁ hJ₁ _ ?_ hmark) h3
  rintro l (rfl | rfl | rfl | rfl)
  all_goals exact ⟨by simp, by first | exact hodd | exact Nat.odd_mul.2 ⟨⟨1, rfl⟩, hodd⟩⟩

theorem ggTwE6A5LAt_of_three_dvd {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : 3 ∣ 2 ^ lab.n + 1 → GGTwE6A5LAt lab) : GGTwE6A5LAt lab := by
  by_cases h3 : 3 ∣ 2 ^ lab.n + 1
  · exact h h3
  refine (largeEvenLabelAll_three_dvd_of_odd_label hlab).mono ?_
  intro R _ I _ hp hR hna hfin B' s n hB hBI hsB hs1 _ hn J₁ hJ₁ _ hmark
  refine absurd (hp hR hna hfin s (hBI s hsB) (hB.2 s hsB) hs1 J₁ hJ₁ _ ?_ hmark) h3
  rintro l rfl
  exact ⟨by simp, odd_of_three_dvd_two_pow_add_one hn⟩

theorem ggTwE6A5LAt_of_not_marking_twA_five {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (h : LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ → lab.n ∣ n →
      ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => lab' = ⟨.twA, 5, n⟩)) :
    GGTwE6A5LAt lab := by
  refine (largeEvenLabelAll_and (largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix hlab) h).mono ?_
  rintro R _ I _ ⟨hp, hno⟩ hR hna hfin B' s n hB hBI hsB hs1 _ _ J₁ hJ₁ _ hmark
  exact absurd hmark (hno J₁ n (ne_top_of_isComponentOf_ggFix hs1 hJ₁)
    (hp hR hna hfin 3 Nat.prime_three (by norm_num) s (hBI s hsB) (hB.2 s hsB) hs1 J₁ hJ₁ _
      (by simp) hmark))

end CFSG.StandardType.SCFourCover

end
