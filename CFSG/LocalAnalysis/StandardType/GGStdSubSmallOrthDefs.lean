module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeLift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonal

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGStdSubSmallOrthLabel (_p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank

namespace SmallOrth

@[expose] def DSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def DTwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .D ∧ 4 ≤ lab.rank ∧ lab.n = 1 ∧ p = 3

@[expose] def TwDSplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1

@[expose] def TwDUnitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ ¬ (lab.rank = 4 ∧ 2 ≤ lab.n)

@[expose] def TwDFourLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twD ∧ lab.rank = 4 ∧ 2 ≤ lab.n ∧ p ∣ 2 ^ lab.n + 1

theorem orthLabel_cases {p : ℕ} {lab : LargeEvenLabel} (h : GGStdSubSmallOrthLabel p lab)
    (hs : LargeEvenSplit p lab) :
    DSplitLabel p lab ∨ DTwoLabel p lab ∨ TwDSplitLabel p lab ∨ TwDUnitLabel p lab ∨
      TwDFourLabel p lab := by
  obtain ⟨ht | ht, hl⟩ := h
  · rcases (largeEvenSplit_D_iff ht).mp hs with h1 | ⟨h1, h2⟩
    · exact Or.inl ⟨ht, hl, h1⟩
    · exact Or.inr (Or.inl ⟨ht, hl, h1, h2⟩)
  · rcases (largeEvenSplit_twD_iff ht).mp hs with h1 | h1 | ⟨h1, h2⟩
    · by_cases h4 : lab.rank = 4 ∧ 2 ≤ lab.n
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, h4.1, h4.2, h1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl, h1, h4⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨ht, hl, h1⟩))
    · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, hl, ?_, fun h4 => ?_⟩)))
      · rw [h1, h2]
        norm_num
      · omega

@[expose] def PlusSplitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ), Nat.card K = 2 ^ n → 4 ≤ m → p.Prime →
    p ∣ 2 ^ n - 1 → GGStdSubTwoTorusEltNormSmall p m (OrthRest.RPlus K m)

@[expose] def PlusTwoInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 → 4 ≤ m →
    GGStdSubTwoTorusEltNormSmall 3 (m - 1) (OrthRest.RPlus K m)

@[expose] def MinusSplitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n - 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGStdSubTwoTorusEltNormSmall p m (OrthRest.RMinus K m b c)

@[expose] def MinusUnitInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ¬ (m = 3 ∧ 2 ≤ n) →
      GGStdSubTwoTorusEltNormSmall p m (OrthRest.RMinus K m b c)

end SmallOrth

@[expose] def GGStdSubTwoTorusInnerConcl (p : ℕ) {L' : Type} [Group L']
    (A : Subgroup (MulAut L')) (a : MulAut L') : Prop :=
  ∃ t ∈ LargeEvenLayer (ggFix a), t ^ p = 1 ∧ (∀ a' ∈ A, a' t = t) ∧ MulAut.conj t ∈ A ∧
    ∃ j ∈ LargeEvenLayer (ggFix a), t * j ≠ j * t

@[expose] def GGStdSubTwoTorusInnerSmall (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
      ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
        (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
        GGStdSubSmallHyp p A a → GGStdSubTwoTorusInnerConcl p A a

@[expose] def GGStdSubTwoTorusEltInnerSmall (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    ∀ a ∈ A, a ≠ 1 → ∀ D : Subgroup R, D ≤ Subgroup.centralizer ({a} : Set R) →
      (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) →
      CFSG.IsQuasisimple D → (∀ b ∈ A, (∀ d ∈ D, b * d = d * b) → b ∈ Subgroup.zpowers a) →
      (∀ E : Subgroup R, IsElemAbelian p E → E ≤ D → E ≤ A → Nat.card E < p ^ 3) →
      ∃ t ∈ D, t ∈ A ∧ ∃ j ∈ D, t * j ≠ j * t

namespace SmallOrth

@[expose] def TwDFourInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ) (b c : K), Nat.card K = 2 ^ n → 2 ≤ n →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      GGStdSubTwoTorusEltInnerSmall p 3 (OrthRest.RMinus K 3 b c)

end SmallOrth

end CFSG.StandardType

end
