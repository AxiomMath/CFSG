module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylRest13Label

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGFixCompCyclic (p : ℕ) {L' : Type} [Group L'] (a : MulAut L') : Prop :=
  ∃ J₁ : Subgroup L', IsComponentOf J₁ (ggFix a) ∧
    ∀ P : Subgroup L', IsPGroup p P →
      P ≤ (⨆ (J₂ : Subgroup L') (_ : IsComponentOf J₂ (ggFix a) ∧ J₂ ≠ J₁ ∧ p ∣ Nat.card J₂),
        J₂) → IsCyclic P

@[expose] def GGTorusNoLineComp (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → GGFixCompCyclic p a₀ →
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

theorem ggTorusNoLineComp_of_ggTorusNoLine {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGTorusNoLine p r R I) : GGTorusNoLineComp p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨W, h1, h2⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc
  exact ⟨W, h1, fun hN a₀ ha₀ h1' _ => h2 hN a₀ ha₀ h1'⟩

theorem ggTorusNoLineComp_of_le {p r r' : ℕ} (hp : 0 < p) (hr : r ≤ r') {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusNoLineComp p r R I) : GGTorusNoLineComp p r' R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr' h3 hsc
  exact h L' ψ hψ hker hperf A hA hAI ((Nat.pow_le_pow_right hp hr).trans hr') h3 hsc

@[expose] def GGTorusNoLineFieldComp (p r : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) :
    Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ (r + 1) ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ((∀ n ∈ W, ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A) →
          ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
            ∃ n ∈ W, MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀)

@[expose] def GGTorusLiftFix (p r : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ f : MulAut L', f ^ p = 1 →
      (∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (f l)) →
      (¬ ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (f l)) →
      ∃ U E : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set L') ∧
        IsElemAbelian p E ∧ Nat.card E = p ^ r ∧ E ⊓ ψ.ker = ⊥ ∧
        (∀ l ∈ U, f l = l) ∧ (∀ l ∈ E, f l = l)

@[expose] def GGNbrWeylFieldKLevelComp (p : ℕ) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
    (∀ g : R, MulAut.conj g ∈ I) ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusLiftFix p r R I F ∧ GGTorusNoLineComp p r R I ∧
        GGTorusNoLineFieldComp p r R I F

@[expose] def GGNbrKGE6ThreeDvd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    GGTorusNoLineComp 3 5 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K)

@[expose] def GGNbrKGTwE6ThreeDvd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 →
    3 ∣ 2 ^ n - 1 → GGTorusNoLineComp 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGNbrKGTwE6AddLarge : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n p : ℕ), 1 ≤ n → Nat.card K = (2 ^ n) ^ 2 → p.Prime →
    5 ≤ p → p ∣ 2 ^ n + 1 →
      GGTorusNoLineComp p 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)

@[expose] def GGNbrKGE7SmallAdd : Prop :=
  ∀ (p : ℕ), (p = 3 ∨ p = 5) → ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    p ∣ Nat.card K + 1 →
      GGTorusNoLineComp p 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K)

@[expose] def GGNbrKGE8SmallAdd : Prop :=
  ∀ (p : ℕ), (p = 3 ∨ p = 5) → ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    p ∣ Nat.card K + 1 →
      GGTorusNoLineComp p 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K)

@[expose] def GGNbrKGF4ThreeAdd : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K + 1 →
    GGTorusNoLineComp 3 3 (TableBF4.RecipeGroup K) (TableBF4.RecipeID K)

@[expose] def GGNbrKGUnitSixThree : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .twA → lab.rank = 5 →
    3 ∣ 2 ^ lab.n + 1 →
      LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusNoLineComp 3 0 R I

@[expose] def GGNbrWeylFieldRowLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
    (lab.tag = .twE6 ∧ ((p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (5 ≤ p ∧ p ∣ 2 ^ lab.n + 1))) ∨
    ((lab.tag = .E7 ∨ lab.tag = .E8) ∧ (p = 3 ∨ p = 5) ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .F4 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨
    (lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGNbrKGFieldRow (S : ℕ → LargeEvenLabel → Prop) (r : ℕ → ℕ) : Prop :=
  ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → p ≠ 2 → LargeEvenInLambda2 lab → S p lab →
    p ∣ lab.n → LargeEvenLabelAll lab fun R _ I F =>
      IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
        GGTorusLiftFix p (r p) R I F ∧ GGTorusNoLineFieldComp p (r p) R I F

@[expose] def GGNbrKGFieldE6 : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .E6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) fun _ => 5

@[expose] def GGNbrKGFieldTwE6ThreeDvd : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .twE6 ∧ p = 3 ∧ 3 ∣ 2 ^ lab.n - 1) fun _ => 4

@[expose] def GGNbrKGFieldTwE6AddLarge : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .twE6 ∧ 5 ≤ p ∧ p ∣ 2 ^ lab.n + 1) fun _ => 5

@[expose] def GGNbrKGFieldE7 : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .E7 ∧ (p = 3 ∨ p = 5) ∧ p ∣ 2 ^ lab.n + 1) fun _ => 6

@[expose] def GGNbrKGFieldE8 : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .E8 ∧ (p = 3 ∨ p = 5) ∧ p ∣ 2 ^ lab.n + 1) fun _ => 7

@[expose] def GGNbrKGFieldF4 : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .F4 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) fun _ => 3

@[expose] def GGNbrKGFieldUnitSix : Prop :=
  GGNbrKGFieldRow (fun p lab => lab.tag = .twA ∧ lab.rank = 5 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)
    fun _ => 3

@[expose] def GGNbrKGFieldTriD4Two : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → lab.tag = .triD4 → lab.n = 1 →
    LargeEvenLabelAll lab (GGNbrWeylFieldKLevelComp 3)

@[expose] def GGNbrWeylKGInput : Prop :=
  GGNbrKGE6ThreeDvd ∧ GGNbrKGTwE6ThreeDvd ∧ GGNbrKGTwE6AddLarge ∧ GGNbrKGE7SmallAdd ∧
    GGNbrKGE8SmallAdd ∧ GGNbrKGF4ThreeAdd ∧ GGNbrKGUnitSixThree ∧ GGNbrKGFieldE6 ∧
    GGNbrKGFieldTwE6ThreeDvd ∧ GGNbrKGFieldTwE6AddLarge ∧ GGNbrKGFieldE7 ∧ GGNbrKGFieldE8 ∧
    GGNbrKGFieldF4 ∧ GGNbrKGFieldUnitSix ∧ GGNbrKGFieldTriD4Two

@[expose] def GGNbrWeylOpenFamily (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .twE6 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .triD4 ∧ p = 3 ∧ 2 ≤ lab.n)

@[expose] def GGNbrWeylResidualLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylRest13Label p lab ∧ GGNbrWeylOpenFamily p lab

@[expose] def GGNbrWeylTriD4TwoLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldRestLabel p lab ∧ lab.tag = .triD4 ∧ p = 3 ∧ lab.n = 1

@[expose] def GGNbrWeylTwE6KnownLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylTwE6RestLabel p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGNbrWeylFieldOtherLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGNbrWeylFieldRestLabel p lab ∧ ¬ GGNbrWeylFieldRowLabel p lab ∧ ¬ GGNbrWeylTriD4TwoLabel p lab ∧
    ¬ GGNbrWeylOpenFamily p lab

theorem ggNbrWeylFieldRowLabel_dvd {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrWeylFieldRestLabel p lab) (hrow : GGNbrWeylFieldRowLabel p lab) : p ∣ lab.n := by
  by_contra hn
  refine h.1.2.1 ⟨?_, ?_⟩
  · rcases hrow with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -, hp3, -⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ht, hn⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr ht, hn⟩))))
    · rcases ht with ht | ht
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl ht)), hn⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inl ht))), hn⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl ht), hn⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨by omega, Or.inr (Or.inr ⟨Or.inl ht, hn⟩)⟩))))
  · rintro ⟨hD, -⟩
    rcases hrow with ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩ | ⟨ht, -⟩
    · rw [ht] at hD; cases hD
    · rw [ht] at hD; cases hD
    · rcases ht with ht | ht <;> (rw [ht] at hD; cases hD)
    · rw [ht] at hD; cases hD
    · rw [ht] at hD; cases hD

theorem ggNbrWeylRest13Label_cover_known {p : ℕ} {lab : LargeEvenLabel}
    (h : GGNbrWeylRest13Label p lab) :
    GGNbrWeylUnitSixThreeLabel p lab ∨ GGNbrWeylE6ThreeDvdLabel p lab ∨
      GGNbrWeylTwE6KnownLabel p lab ∨ GGNbrWeylExcPlusSmallPrimeLabel p lab ∨
      (GGNbrWeylFieldRestLabel p lab ∧ GGNbrWeylFieldRowLabel p lab) ∨
      GGNbrWeylTriD4TwoLabel p lab ∨ GGNbrWeylFieldOtherLabel p lab ∨
      GGNbrWeylResidualLabel p lab := by
  obtain ⟨-, hF | hU | hE | hT | hX⟩ := id h
  · by_cases hrow : GGNbrWeylFieldRowLabel p lab
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hF, hrow⟩))))
    · by_cases htri : GGNbrWeylTriD4TwoLabel p lab
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl htri)))))
      · by_cases hopen : GGNbrWeylOpenFamily p lab
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, hopen⟩))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hF, hrow, htri, hopen⟩))))))
  · exact Or.inl hU
  · exact Or.inr (Or.inl hE)
  · by_cases hres : p = 3 ∧ p ∣ 2 ^ lab.n + 1
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h, Or.inl ⟨hT.2.1, hres⟩⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨hT, hres⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hX)))

end CFSG.StandardType
