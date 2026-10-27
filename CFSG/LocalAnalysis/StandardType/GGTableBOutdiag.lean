module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagUnitary
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagSp
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LocalAnalysis.StandardType.GGTableB

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Twisted

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]
  (H : Subgroup (LargeEvenChevGL A K))

@[expose] def GGDiagCyclicInput : Prop :=
  ∀ a a' : Fin r → Kˣ, (∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) →
    (∀ h ∈ H, TableB.diagHom A K a' * h * (TableB.diagHom A K a')⁻¹ ∈ H) →
    TableB.diagHom A K a' ∉ H → ∃ k : ℕ, TableB.diagHom A K (a * (a' ^ k)⁻¹) ∈ H

@[expose] def GGDiagRealizedInput : Prop :=
  ∀ a : Fin r → Kˣ, (∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) →
    TableB.diagHom A K a ∈ H

variable {A K H}

theorem GGDiagRealizedInput.diagCyclic (h : GGDiagRealizedInput A K H) :
    GGDiagCyclicInput A K H :=
  fun _ a' _ ha' hn => absurd (h a' ha') hn

theorem ggOutdiagCyclic_of_diagCyclicInput (h : GGDiagCyclicInput A K H) :
    GGOutdiagCyclic (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) :=
  TableB.ggOutdiagCyclic_chevID (H.comap (TableB.diagHom A K)) (fun _ ht => ht)
    (fun a a' ha ha' hn => h a a' ha ha' hn)

end Twisted

section Recipes

theorem recipeChevalley_outdiag {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ} {derived : Bool}
    {Q : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q →
      GGOutdiagCyclic (LargeEvenCenterQuot (LargeEvenChevH A K derived))
        (LargeEvenChevIDImage A K (LargeEvenChevH A K derived)))
    (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

theorem recipeTwisted_and {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {ρ : Equiv.Perm (Fin r)}
    {m n : ℕ} {Q P : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ m →
      P (LargeEvenCenterQuot (LargeEvenTwistedH A K ρ n)) (LargeEvenChevIDImage A K _)
        (LargeEvenChevFieldImage A K _))
    (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n fun R _ I F => Q R I F ∧ P R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

theorem recipeTwF4_and {a : ℕ} {Q P : LargeEvenRawCont}
    (hA : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
      P (LargeEvenCenterQuot (LargeEvenTwF4H a K)) (LargeEvenChevIDImage LargeEvenCartanF4 K _)
        (LargeEvenChevFieldImage LargeEvenCartanF4 K _))
    (h : LargeEvenRecipeTwF4 a Q) :
    LargeEvenRecipeTwF4 a fun R _ I F => Q R I F ∧ P R I F := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, hA K hK⟩

theorem ggOutdiagCyclic_chevID_of_card_two {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = 2) (H : Subgroup (LargeEvenChevGL A K)) :
    GGOutdiagCyclic (LargeEvenCenterQuot H) (LargeEvenChevIDImage A K H) := by
  have := CFSG.Monster.Existence.Compat.subsingleton_units_of_card_two hK
  exact TableB.ggOutdiagCyclic_chevID_of_subsingleton H

end Recipes

section Labels

@[expose] def GGOutdiagTwistedLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twF4


theorem largeEvenLabelAll_outdiag_of_not_twisted {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : ¬ GGOutdiagTwistedLabel lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I := by
  by_cases hp : GGOutdiagPilotLabel lab
  · exact largeEvenLabelAll_outdiag_pilot hlab hp
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  intro Q hQ
  cases t with
  | A => exact absurd (Or.inl rfl) hp
  | twA => exact recipeUnitary_outdiag hQ
  | B => exact absurd (Or.inr (Or.inl rfl)) hp
  | C => exact absurd (Or.inr (Or.inr (Or.inl rfl))) hp
  | D => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hp
  | twD =>
    have hl3 : l = 3 := by
      by_contra h3
      exact hp (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩)))))
    subst hl3
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    exact recipeUnitary_outdiag hQ
  | E6 => exact recipeChevalley_outdiag (fun K _ _ _ => TableB.ggOutdiagCyclic_E6 K) hQ
  | E7 =>
    exact recipeChevalley_outdiag (fun K _ _ hK => by
      have := charP_two_of_card hK
      exact TableB.ggOutdiagCyclic_E7 K) hQ
  | E8 => exact recipeChevalley_outdiag (fun K _ _ _ => TableB.ggOutdiagCyclic_E8 K) hQ
  | F4 => exact recipeChevalley_outdiag (fun K _ _ _ => TableB.ggOutdiagCyclic_F4 K) hQ
  | twE6 => exact absurd (Or.inl rfl) h
  | triD4 => exact absurd (Or.inr (Or.inl rfl)) h
  | G2 => exact recipeChevalley_outdiag (fun K _ _ _ => TableB.ggOutdiagCyclic_G2 K) hQ
  | twB2 => exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) hp
  | twF4 => exact absurd (Or.inr (Or.inr rfl)) h
  | B2der => exact recipeB2der_outdiag hQ
  | G2der =>
    exact recipeChevalley_outdiag (fun K _ _ hK => ggOutdiagCyclic_chevID_of_card_two _ hK _) hQ
  | twF4der =>
    obtain ⟨-, hn1⟩ := hl
    subst hn1
    exact recipeTwF4_and (P := fun R _ I _ => GGOutdiagCyclic R I)
      (fun K _ _ hK => ggOutdiagCyclic_chevID_of_card_two _ (by simpa using hK) _) hQ

theorem ggLNoncyclicInputOn_not_twisted :
    GGLNoncyclicInputOn fun lab => ¬ GGOutdiagTwistedLabel lab :=
  ggLNoncyclicInputOn_of_labels fun _ hlab h => largeEvenLabelAll_outdiag_of_not_twisted hlab h

abbrev LargeEvenSimpleGuard (P : LargeEvenRawCont) : LargeEvenRawCont :=
  fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → P R I F

theorem largeEvenMarking_and_labelAll_simple {X : Type*} [Group X] {P : LargeEvenMarkProp X}
    {S : LargeEvenLabel → Prop} {P' : LargeEvenRawCont}
    (hall : ∀ lab, LargeEvenInLambda2 lab → S lab → LargeEvenLabelAll lab (LargeEvenSimpleGuard P'))
    (hS : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), P lab R I F θ → S lab)
    (h : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ P' R I F := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hraw' := hall lab hlab (hS lab R I F θ hP) _ hraw
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
  rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hP'⟩
  exact ⟨hs, hna, θ, hθ, hP' hs hna⟩

theorem ggLNoncyclicInputOn_of_labels_simple {S : LargeEvenLabel → Prop}
    (h : ∀ lab, LargeEvenInLambda2 lab → S lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)) :
    GGLNoncyclicInputOn S := by
  intro G _ _ p B x L hT hM
  obtain ⟨-, -, -, -, -, hβ, hS, -⟩ := hT
  have hM' := largeEvenMarking_and_labelAll_simple h (fun _ _ _ _ _ _ hP => hP.1) hM
  exact exists_noncyclic_of_marking_outdiag hβ.1 hS hβ.2.2.2
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1.2.2, h.2⟩) hM')

theorem ggLNoncyclicInput_of_twisted
    (h : ∀ lab, LargeEvenInLambda2 lab → GGOutdiagTwistedLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)) :
    GGLNoncyclicInput := by
  intro G _ _ p B x L hT
  have hon := ggLNoncyclicInputOn_of_labels_simple (S := fun _ => True) fun lab hlab _ => by
    by_cases ht : GGOutdiagTwistedLabel lab
    · exact h lab hlab ht
    · exact (largeEvenLabelAll_outdiag_of_not_twisted hlab ht).mono fun _ _ _ _ hO _ _ => hO
  exact hon G p B x L hT
    (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hT.2.2.2.2.2.2.2.1)

@[expose] def GGTwistedE6DiagInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 2 →
    IsSimpleGroup
      (LargeEvenCenterQuot (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)) →
    GGDiagCyclicInput (LargeEvenCartanE 6) K
      (LargeEvenTwistedH (LargeEvenCartanE 6) K LargeEvenRhoE6 n)

@[expose] def GGTwistedD4DiagInput : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ 3 →
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)) →
    GGDiagRealizedInput LargeEvenCartanD4 K
      (LargeEvenTwistedH LargeEvenCartanD4 K LargeEvenRhoD4 n)

@[expose] def GGTwistedF4DiagInput : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) →
    IsSimpleGroup (LargeEvenCenterQuot (LargeEvenTwF4H a K)) →
    GGDiagRealizedInput LargeEvenCartanF4 K (LargeEvenTwF4H a K)

theorem largeEvenLabelAll_outdiag_twE6 (hE6 : GGTwistedE6DiagInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twE6) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)
    (fun K _ _ hK hs _ => ggOutdiagCyclic_of_diagCyclicInput (hE6 n hn K hK hs)) hQ

theorem largeEvenLabelAll_outdiag_triD4_of_diag (hD4 : GGTwistedD4DiagInput)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .triD4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and (P := LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)
    (fun K _ _ hK hs _ => ggOutdiagCyclic_of_diagCyclicInput (hD4 n hn K hK hs).diagCyclic) hQ

theorem largeEvenLabelAll_outdiag_twF4 (hF4 : GGTwistedF4DiagInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twF4) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, -, h3⟩ := hl
  intro Q hQ
  exact recipeTwF4_and (P := LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I)
    (fun K _ _ hK hs _ =>
      ggOutdiagCyclic_of_diagCyclicInput (hF4 _ (by omega) K hK hs).diagCyclic) hQ

theorem largeEvenLabelAll_outdiag_twisted (hE6 : GGTwistedE6DiagInput)
    (hD4 : GGTwistedD4DiagInput) (hF4 : GGTwistedF4DiagInput) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : GGOutdiagTwistedLabel lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I) := by
  rcases ht with ht | ht | ht
  · exact largeEvenLabelAll_outdiag_twE6 hE6 hlab ht
  · exact largeEvenLabelAll_outdiag_triD4_of_diag hD4 hlab ht
  · exact largeEvenLabelAll_outdiag_twF4 hF4 hlab ht

theorem ggLNoncyclicInput_of_twistedDiag (hE6 : GGTwistedE6DiagInput)
    (hD4 : GGTwistedD4DiagInput) (hF4 : GGTwistedF4DiagInput) : GGLNoncyclicInput :=
  ggLNoncyclicInput_of_twisted fun _ hlab ht =>
    largeEvenLabelAll_outdiag_twisted hE6 hD4 hF4 hlab ht

theorem ggTableBInputs_of_twisted
    (h₀ : ∀ lab, LargeEvenInLambda2 lab → GGOutdiagTwistedLabel lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ => GGOutdiagCyclic R I))
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab →
      LargeEvenSplit p lab → LargeEvenLabelAll lab fun R _ I _ =>
        ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I ∧ GGEndNode p r R I) :
    GGLNoncyclicInput ∧ GGBstarInput ∧ GGStdSubPreInput := by
  have ha₀ := ggLNoncyclicInput_of_twisted h₀
  refine ⟨ha₀, ggBstarInput_of_labels ha₀ fun p lab hp hlab hs => ?_,
    ggStdSubPreInput_of_labels fun p lab hp hlab hs => ?_⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩
  · exact (h p lab hp hlab hs).mono fun _ _ _ _ ⟨r, h1, _, h3⟩ => ⟨r, h1, h3⟩

end Labels

end CFSG.StandardType
