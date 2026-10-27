module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLParityCases
import CFSG.LocalAnalysis.StandardType.GGTableB
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.SCFourCover

open CFSG CFSG.Assembly CFSG.Blueprint TableB

@[expose] def GGInndiagOnCompAt (lab : LargeEvenLabel) (P : ℕ → LargeEvenLabel → Prop) : Prop :=
  LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    Finite R →
    ∀ (s t : MulAut R) (n : ℕ), s ^ 3 = 1 → s ≠ 1 → t ^ 3 = 1 → s * t = t * s → s ∈ I →
      t ∈ I → 3 ∣ 2 ^ n + 1 →
      ∀ J₁ : Subgroup R, IsComponentOf J₁ (ggFix s) →
        LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => P n lab') → ¬ GGOutsideInndiag J₁ t

private theorem exists_label_of_largeEvenMarking {X : Type*} [Group X]
    {S : LargeEvenLabel → Prop} (h : LargeEvenMarking X fun l _ _ _ _ _ => S l) :
    ∃ l, S l ∧ LargeEvenMarking X fun l' _ _ _ _ _ => l' = l := by
  obtain ⟨hX, l, hl, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := largeEvenRawDatum_exists hraw
  exact ⟨l, hS, hX, l, hl,
    largeEvenRawDatum_mono (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem largeEvenMarking_of_eq {X : Type*} [Group X] {S : LargeEvenLabel → Prop}
    {l : LargeEvenLabel} (hl : S l) (h : LargeEvenMarking X fun l' _ _ _ _ _ => l' = l) :
    LargeEvenMarking X fun l' _ _ _ _ _ => S l' := by
  obtain ⟨hX, l', hl', hraw⟩ := h
  exact ⟨hX, l', hl', largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, h⟩ => ⟨hs, hna, θ, by subst h; exact hl⟩) hraw⟩

private theorem ne_top_of_isComponentOf_ggFix {R : Type} [Group R] {s : MulAut R} (hs : s ≠ 1)
    {J₁ : Subgroup R} (hJ : IsComponentOf J₁ (ggFix s)) : J₁ ≠ ⊤ := by
  rintro rfl
  exact hs (MulEquiv.ext fun r => by simpa using mem_ggFix.1 (hJ.1 (Subgroup.mem_top r)))

theorem ggInndiagOnCompAt_mono {lab : LargeEvenLabel} {P Q : ℕ → LargeEvenLabel → Prop}
    (hQP : ∀ n l, Q n l → P n l) (h : GGInndiagOnCompAt lab P) : GGInndiagOnCompAt lab Q := by
  unfold GGInndiagOnCompAt at h ⊢
  refine h.mono fun R _ I _ hP hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ hmark => ?_
  obtain ⟨l, hl, hmark'⟩ := exists_label_of_largeEvenMarking hmark
  exact hP hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁
    (largeEvenMarking_of_eq (hQP n l hl) hmark')

theorem ggInndiagOnCompAt_or {lab : LargeEvenLabel} {P Q : ℕ → LargeEvenLabel → Prop}
    (hP : GGInndiagOnCompAt lab P) (hQ : GGInndiagOnCompAt lab Q) :
    GGInndiagOnCompAt lab fun n l => P n l ∨ Q n l := by
  unfold GGInndiagOnCompAt at hP hQ ⊢
  refine (largeEvenLabelAll_and hP hQ).mono
    fun R _ I _ ⟨hP', hQ'⟩ hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ hmark => ?_
  obtain ⟨l, hl | hl, hmark'⟩ := exists_label_of_largeEvenMarking hmark
  · exact hP' hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ (largeEvenMarking_of_eq hl hmark')
  · exact hQ' hR hna hfin s t n hs3 hs1 ht3 hst hsI htI hn J₁ hJ₁ (largeEvenMarking_of_eq hl hmark')

theorem ggInndiagOnCompAt_of_noJ1 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {P : ℕ → LargeEvenLabel → Prop} (f : ℕ → ℕ)
    (hP : ∀ n l, P n l → l.tag ≠ .twD ∧ l.n = f n)
    (h : LargeEvenLabelAll lab fun R _ _ _ => ∀ (J₁ : Subgroup R) (n : ℕ), J₁ ≠ ⊤ →
      3 ∣ 2 ^ n + 1 → lab.n ∣ f n → ¬ LargeEvenMarking ↥J₁ (fun lab' _ _ _ _ _ => P n lab')) :
    GGInndiagOnCompAt lab P := by
  unfold GGInndiagOnCompAt
  refine (largeEvenLabelAll_and (largeEvenLabelAll_n_dvd_of_isComponentOf_ggFix hlab) h).mono
    fun R _ I _ ⟨hpl, hno⟩ hR hna hfin s t n hs3 hs1 _ _ hsI _ hn J₁ hJ₁ hmark _ => ?_
  obtain ⟨l, hl, hmark'⟩ := exists_label_of_largeEvenMarking hmark
  have hdvd := hpl hR hna hfin 3 Nat.prime_three (by norm_num) s hsI hs3 hs1 J₁ hJ₁ l
    (fun h' => absurd h' (hP n l hl).1) hmark'
  rw [(hP n l hl).2] at hdvd
  exact hno J₁ n (ne_top_of_isComponentOf_ggFix hs1 hJ₁) hn hdvd hmark

theorem ggTwE6OfOutsideAt_of_inndiagOnCompAt {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab)
    (hD : 3 ∣ 2 ^ lab.n + 1 →
      GGInndiagOnCompAt lab fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩)
    (hA : 3 ∣ 2 ^ lab.n + 1 →
      GGInndiagOnCompAt lab fun n l => l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩) :
    GGTwE6OfOutsideAt lab := by
  refine ggTwE6OfOutsideAt_of_three_dvd hlab fun h3 => ?_
  have h := ggInndiagOnCompAt_mono (Q := fun n l => l = ⟨.D, 4, n⟩ ∨ l = ⟨.triD4, 0, n⟩ ∨
    l = ⟨.A, 2, 3 * n⟩ ∨ l = ⟨.twA, 2, 3 * n⟩) (fun _ _ h => or_assoc.2 h)
    (ggInndiagOnCompAt_or (hD h3) (hA h3))
  exact h

end CFSG.StandardType.SCFourCover

end
