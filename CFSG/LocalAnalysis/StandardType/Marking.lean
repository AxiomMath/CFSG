module

public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.MarkingSmall

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley

section Recipes

variable {Q Q' : LargeEvenRawCont}

theorem recipeLinear_imp {d N : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = N → ∀ I F,
      Q (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) I F →
        Q' (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) I F)
    (h : LargeEvenRecipeLinear d N Q) : LargeEvenRecipeLinear d N Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeUnitary_imp {d q : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q ^ 2 → ∀ I F,
      Q (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) I F →
        Q' (LargeEvenProj (LargeEvenSUGroup (Fin d) K q)) I F)
    (h : LargeEvenRecipeUnitary d q Q) : LargeEvenRecipeUnitary d q Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeSymplectic_imp {m q : ℕ} {der : Bool}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → ∀ I F,
      Q (LargeEvenProj
          (if der then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m))
        I F →
      Q' (LargeEvenProj
          (if der then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m))
        I F)
    (h : LargeEvenRecipeSymplectic m q der Q) : LargeEvenRecipeSymplectic m q der Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeOmegaPlus_imp {m q : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → ∀ I F,
      Q (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) I F →
        Q' (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) I F)
    (h : LargeEvenRecipeOmegaPlus m q Q) : LargeEvenRecipeOmegaPlus m q Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeOmegaMinus_imp {m q : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → ∀ b c : K,
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) → ∀ I F,
      Q (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) I F →
        Q' (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) I F)
    (h : LargeEvenRecipeOmegaMinus m q Q) : LargeEvenRecipeOmegaMinus m q Q' := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hM K hK b c hbc _ _ hQK⟩

theorem recipeChevalley_imp {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {q : ℕ} {der : Bool}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenChevH A K der)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenChevH A K der)) I F)
    (h : LargeEvenRecipeChevalley A q der Q) : LargeEvenRecipeChevalley A q der Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeTwisted_imp {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {ρ : Equiv.Perm (Fin r)}
    {m n : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ n) ^ m → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenTwistedH A K ρ n)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenTwistedH A K ρ n)) I F)
    (h : LargeEvenRecipeTwisted A ρ m n Q) : LargeEvenRecipeTwisted A ρ m n Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeSuzuki_imp {a : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenSzGroup a K)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenSzGroup a K)) I F)
    (h : LargeEvenRecipeSuzuki a Q) : LargeEvenRecipeSuzuki a Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

theorem recipeTwF4_imp {a : ℕ}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenTwF4H a K)) I F)
    (h : LargeEvenRecipeTwF4 a Q) : LargeEvenRecipeTwF4 a Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

end Recipes

section Arith

theorem four_le_two_pow {n : ℕ} (hn : 2 ≤ n) : 4 ≤ 2 ^ n :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem two_pow_ne_three (n : ℕ) : 2 ^ n ≠ 3 := by
  rcases n with _ | _ | n
  · decide
  · decide
  · have := four_le_two_pow (n := n + 2) (by omega)
    omega

theorem two_le_two_pow {n : ℕ} (hn : 1 ≤ n) : 2 ≤ 2 ^ n :=
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])

end Arith

section Exceptional

variable {K : Type} [Field K] [Finite K]

theorem untwistedChevalleyModel_largeEven (τ : Tag) {q : ℕ} (hK : Nat.card K = q) :
    UntwistedChevalleyModel (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)) τ q :=
  ⟨K, inferInstance, inferInstance, hK, centerQuot_chevGroup_equiv K τ⟩

theorem twistedChevalleyModel_largeEven (t : TwistTag) {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ t.order) :
    TwistedChevalleyModel (LargeEvenCenterQuot (LargeEvenTwistedH t.tag.cartan K t.perm n)) t
      (2 ^ n) := by
  have : CharP K 2 := charP_two_of_card (m := n * t.order) (by rw [hK, pow_mul])
  exact ⟨K, inferInstance, inferInstance, hK, iterateFrobenius K 2 n, fun _ => rfl,
    centerQuot_twistedH_equiv K t n _ fun _ => rfl⟩

theorem reeTitsRelationModel_largeEven (a : ℕ) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ReeTitsRelationModel (LargeEvenCenterQuot (LargeEvenTwF4H a K)) .F4 reeF4Perm reeF4Long 2
      (2 * a + 1) a :=
  ⟨K, inferInstance, inferInstance, hK, centerQuot_twF4H_equiv K a⟩

end Exceptional

section Main


theorem largeEvenRawDatum_imp {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q Q' : LargeEvenRawCont}
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → ∃ a b : R, a * b ≠ b * a)
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → MarkedModel lab R →
      Q' R I F)
    (h : LargeEvenRawDatum lab Q) : LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar, markDeg]
    at hn hl h hQQ' ⊢
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  case B =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case G2 =>
    obtain ⟨-, hn2⟩ := hl
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, by
      have := four_le_two_pow hn2; omega⟩, untwistedChevalleyModel_largeEven .G2 hK⟩)
  case F4 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  case E6 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)
  case E7 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E7 hK⟩)
  case E8 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E8 hK⟩)
  case twE6 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .E6 hK⟩)
  case triD4 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeSuzuki_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    have hSz := suzukiModel_largeEvenSz (a := (n - 1) / 2) (by omega) K hK (hQ _ I F hq)
    rwa [← hn'] at hSz
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  case B2der =>
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inl ⟨by decide, statedClassicalModel_b2der hK⟩
  case G2der =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact lieModel_g2der K hK (hQ _ I F hq)
  case twF4der =>
    obtain ⟨-, rfl⟩ := hl
    refine recipeTwF4_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      0, rfl, reeTitsRelationModel_largeEven 0 hK⟩))

theorem largeEvenRawDatum_markedModel {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q : LargeEvenRawCont}
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → ∃ a b : R, a * b ≠ b * a)
    (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ MarkedModel lab R :=
  largeEvenRawDatum_imp hlab hQ (fun _ _ _ _ hq hm => ⟨hq, hm⟩) h

theorem largeEvenMarking_markedModel {L : Type*} [Group L] {P : LargeEvenMarkProp L}
    (h : LargeEvenMarking L P) :
    LargeEvenMarking L fun lab R _ I F θ => P lab R I F θ ∧ MarkedModel lab R := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  refine ⟨hL, lab, hlab, largeEvenRawDatum_imp hlab (fun R _ I F hq => hq.2.1) ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩ hm
  exact ⟨hs, hna, θ, hθ, hm⟩

end Main

theorem largeEvenRawDatum_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

section Main


theorem largeEvenMarking_exists_markedModel {L : Type*} [Group L] {P : LargeEvenMarkProp L}
    (h : LargeEvenMarking L P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : L ⧸ Subgroup.center L ≃* R),
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ P lab R I F θ ∧ MarkedModel lab R := by
  obtain ⟨-, lab, hlab, hraw⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, hs, hna, θ, hθ, hm⟩ := largeEvenRawDatum_exists hraw
  exact ⟨lab, hlab, R, inferInstance, I, F, θ, hs, hna, hθ, hm⟩

theorem largeEvenMarking_markedModel_centerQuot {L : Type} [Group L] {P : LargeEvenMarkProp L}
    (h : LargeEvenMarking L P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ MarkedModel lab (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, -, hm⟩ := largeEvenMarking_exists_markedModel h
  exact ⟨lab, hlab, MarkedModel.of_mulEquiv θ.symm hm⟩

theorem largeEvenMarking_catalog_centerQuot {L : Type} [Group L] {P : LargeEvenMarkProp L}
    (h : LargeEvenMarking L P) : Catalog (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, -, hm⟩ := largeEvenMarking_markedModel_centerQuot h
  exact MarkedModel.catalog hm

variable {G : Type} [Group G] [Finite G]

theorem largeEvenStandardType_marking_markedModel {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : LargeEvenStandardType p B x L) :
    LargeEvenMarking L fun lab R _ I _ θ =>
      (LargeEvenSplit p lab ∧ B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      MarkedModel lab R :=
  largeEvenMarking_markedModel h.1

theorem largeEvenStandardType_neighbor_markedModel {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : LargeEvenStandardType p B x L) {y : G} {J : Subgroup G}
    (hJ : LargeEvenIsNeighborOf p B x L y J) :
    B ≤ Subgroup.normalizer (J : Set G) ∧
      LargeEvenMarking J fun lab R _ I F θ =>
        (LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
          LargeEvenPrimeField p lab I F
            (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) ∧
        MarkedModel lab R :=
  ⟨(h.2.2.1 y J hJ).1, largeEvenMarking_markedModel (h.2.2.1 y J hJ).2⟩

end Main

namespace Legacy
abbrev largeEvenRawDatum_imp := @CFSG.StandardType.largeEvenRawDatum_imp
abbrev largeEvenRawDatum_markedModel := @CFSG.StandardType.largeEvenRawDatum_markedModel
abbrev largeEvenRawDatum_exists := @CFSG.StandardType.largeEvenRawDatum_exists
abbrev largeEvenMarking_markedModel := @CFSG.StandardType.largeEvenMarking_markedModel
abbrev largeEvenMarking_exists_markedModel := @CFSG.StandardType.largeEvenMarking_exists_markedModel
abbrev largeEvenMarking_markedModel_centerQuot :=
  @CFSG.StandardType.largeEvenMarking_markedModel_centerQuot
abbrev largeEvenMarking_catalog_centerQuot := @CFSG.StandardType.largeEvenMarking_catalog_centerQuot
abbrev largeEvenStandardType_marking_markedModel :=
  @CFSG.StandardType.largeEvenStandardType_marking_markedModel
abbrev largeEvenStandardType_neighbor_markedModel :=
  @CFSG.StandardType.largeEvenStandardType_neighbor_markedModel
end Legacy

namespace Canonical

private theorem recipeG2Derived_imp {Q Q' : LargeEvenRawCont}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanG2 K true)) I F)
    (h : LargeEvenRecipeG2Derived Q) : LargeEvenRecipeG2Derived Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

private theorem recipeTwF4Inherited_imp {a : ℕ} {Q Q' : LargeEvenRawCont}
    (hM : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * a + 1) → ∀ I F,
      Q (LargeEvenCenterQuot (LargeEvenTwF4H a K)) I F →
        Q' (LargeEvenCenterQuot (LargeEvenTwF4H a K)) I F)
    (h : LargeEvenRecipeTwF4Inherited a Q) : LargeEvenRecipeTwF4Inherited a Q' := by
  obtain ⟨K, _, _, hK, hQK⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hM K hK _ _ hQK⟩

section Main

theorem largeEvenRawDatum_imp
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q Q' : LargeEvenRawCont}
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → ∃ a b : R, a * b ≠ b * a)
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → MarkedModel lab R →
      Q' R I F)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) : CFSG.Assembly.LargeEvenRawDatum lab Q' := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum, MarkedModel, markTag, markRank, markChar,
    markDeg] at hn hl h hQQ' ⊢
  case A =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_linear (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_, fun h => ?_⟩⟩
    · simp only [Prod.mk.injEq] at h
      have := four_le_two_pow (hl2 (by omega))
      omega
    · simp only [Prod.mk.injEq] at h
      exact two_pow_ne_three n h.2
  case twA =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 (by omega))
    omega
  case B =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case C =>
    obtain ⟨hl1, hl2⟩ := hl
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inl ⟨by decide, statedClassicalModel_symplectic l n hK
      ⟨Nat.prime_two, hn, hl1, fun h => ?_⟩⟩
    simp only [Prod.mk.injEq] at h
    have := four_le_two_pow (hl2 h.1)
    omega
  case D =>
    split_ifs at h hQQ' ⊢ with h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_linear 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp, by simp⟩⟩
    · refine recipeOmegaPlus_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaPlus l n hK
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case twD =>
    split_ifs at h hQQ' ⊢ with h2 h3
    · refine recipeLinear_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      have hK' : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
      have h4 := four_le_two_pow (n := 2 * n) (by omega)
      exact Or.inl ⟨by decide, statedClassicalModel_linear 2 (2 * n) hK'
        ⟨Nat.prime_two, by omega, le_rfl, fun h => by simp only [Prod.mk.injEq] at h; omega,
          fun h => by simp only [Prod.mk.injEq] at h; omega⟩⟩
    · refine recipeUnitary_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_unitary 4 n hK
        ⟨Nat.prime_two, hn, by omega, by simp⟩⟩
    · refine recipeOmegaMinus_imp (fun K _ _ hK b c hbc I F hq => hQQ' _ I F hq ?_) h
      exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
        ⟨Nat.prime_two, hn, by omega⟩⟩
  case G2 =>
    obtain ⟨-, hn2⟩ := hl
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, by
      have := four_le_two_pow hn2; omega⟩, untwistedChevalleyModel_largeEven .G2 hK⟩)
  case F4 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .F4 hK⟩)
  case E6 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E6 hK⟩)
  case E7 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E7 hK⟩)
  case E8 =>
    refine recipeChevalley_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      untwistedChevalleyModel_largeEven .E8 hK⟩)
  case twE6 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .E6 hK⟩)
  case triD4 =>
    refine recipeTwisted_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl⟩,
      twistedChevalleyModel_largeEven .D4 hK⟩)
  case twB2 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeSuzuki_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    refine Or.inr (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    have hSz := suzukiModel_largeEvenSz (a := (n - 1) / 2) (by omega) K hK (hQ _ I F hq)
    rwa [← hn'] at hSz
  case twF4 =>
    obtain ⟨-, ⟨k, hk⟩, hn3⟩ := hl
    have hn' : n = 2 * ((n - 1) / 2) + 1 := by omega
    refine recipeTwF4Inherited_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    have hRee := reeTitsRelationModel_largeEven ((n - 1) / 2) hK
    rw [← hn'] at hRee
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, hn, rfl, rfl, ⟨k, hk⟩, hn3⟩,
      (n - 1) / 2, hn', hRee⟩))
  case B2der =>
    refine recipeSymplectic_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inl ⟨by decide, statedClassicalModel_b2der hK⟩
  case G2der =>
    refine recipeG2Derived_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact lieModel_g2der K hK (hQ _ I F hq)
  case twF4der =>
    obtain ⟨-, rfl⟩ := hl
    refine recipeTwF4Inherited_imp (fun K _ _ hK I F hq => hQQ' _ I F hq ?_) h
    exact Or.inr (Or.inr (Or.inl ⟨rfl, by decide, ⟨Nat.prime_two, le_rfl, rfl, rfl, rfl⟩,
      0, rfl, reeTitsRelationModel_largeEven 0 hK⟩))

theorem largeEvenRawDatum_markedModel {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {Q : LargeEvenRawCont}
    (hQ : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → ∃ a b : R, a * b ≠ b * a)
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    CFSG.Assembly.LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ MarkedModel lab R :=
  largeEvenRawDatum_imp hlab hQ (fun _ _ _ _ hq hm => ⟨hq, hm⟩) h

theorem largeEvenMarking_markedModel {L : Type*} [Group L] {P : LargeEvenMarkProp L}
    (h : CFSG.Assembly.LargeEvenMarking L P) :
    CFSG.Assembly.LargeEvenMarking L fun lab R _ I F θ =>
      P lab R I F θ ∧ MarkedModel lab R := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  refine ⟨hL, lab, hlab, largeEvenRawDatum_imp hlab (fun R _ I F hq => hq.2.1) ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩ hm
  exact ⟨hs, hna, θ, hθ, hm⟩
end Main

theorem largeEvenRawDatum_exists {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : CFSG.Assembly.LargeEvenRawDatum lab Q) :
    ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)), Q R I F := by
  obtain ⟨t, l, n⟩ := lab
  cases t
  all_goals dsimp only [CFSG.Assembly.LargeEvenRawDatum] at h
  all_goals try split_ifs at h
  all_goals first
    | (obtain ⟨K, _, _, -, b, c, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)
    | (obtain ⟨K, _, _, -, hq⟩ := h; exact ⟨_, _, _, _, hq⟩)

theorem largeEvenMarking_exists {L : Type*} [Group L] {P : LargeEvenMarkProp L}
    (h : CFSG.Assembly.LargeEvenMarking L P) :
    commutator L = ⊤ ∧ ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : L ⧸ Subgroup.center L ≃* R),
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ P lab R I F θ := by
  obtain ⟨hL, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, hs, hna, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  exact ⟨hL, lab, hlab, R, inferInstance, I, F, θ, hs, hna, hθ⟩

section Main

theorem largeEvenMarking_exists_markedModel {L : Type*} [Group L] {P : LargeEvenMarkProp L}
    (h : CFSG.Assembly.LargeEvenMarking L P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ∃ (R : Type) (_ : Group R) (I F : Set (MulAut R)) (θ : L ⧸ Subgroup.center L ≃* R),
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧ P lab R I F θ ∧ MarkedModel lab R := by
  obtain ⟨-, lab, hlab, hraw⟩ := largeEvenMarking_markedModel h
  obtain ⟨R, _, I, F, hs, hna, θ, hθ, hm⟩ := largeEvenRawDatum_exists hraw
  exact ⟨lab, hlab, R, inferInstance, I, F, θ, hs, hna, hθ, hm⟩

theorem largeEvenMarking_markedModel_centerQuot {L : Type} [Group L] {P : LargeEvenMarkProp L}
    (h : CFSG.Assembly.LargeEvenMarking L P) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ MarkedModel lab (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, hlab, R, _, I, F, θ, -, -, -, hm⟩ := largeEvenMarking_exists_markedModel h
  exact ⟨lab, hlab, MarkedModel.of_mulEquiv θ.symm hm⟩

theorem largeEvenMarking_catalog_centerQuot {L : Type} [Group L] {P : LargeEvenMarkProp L}
    (h : CFSG.Assembly.LargeEvenMarking L P) : Catalog (L ⧸ Subgroup.center L) := by
  obtain ⟨lab, -, hm⟩ := largeEvenMarking_markedModel_centerQuot h
  exact MarkedModel.catalog hm

variable {G : Type} [Group G] [Finite G]

theorem largeEvenStandardType_marking_markedModel {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : CFSG.Assembly.LargeEvenStandardType p B x L) :
    CFSG.Assembly.LargeEvenMarking L fun lab R _ I _ θ =>
      (LargeEvenSplit p lab ∧ B ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      MarkedModel lab R :=
  largeEvenMarking_markedModel h.1

theorem largeEvenStandardType_neighbor_markedModel {p : ℕ} {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : CFSG.Assembly.LargeEvenStandardType p B x L) {y : G} {J : Subgroup G}
    (hJ : LargeEvenIsNeighborOf p B x L y J) :
    B ≤ Subgroup.normalizer (J : Set G) ∧
      CFSG.Assembly.LargeEvenMarking J fun lab R _ I F θ =>
        (LargeEvenHalfSplit p lab (Subgroup.center J = ⊥) ∨
          LargeEvenPrimeField p lab I F
            (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) ∧
        MarkedModel lab R :=
  ⟨(h.2.2.1 y J hJ).1, largeEvenMarking_markedModel (h.2.2.1 y J hJ).2⟩
end Main
end Canonical

end CFSG.StandardType
