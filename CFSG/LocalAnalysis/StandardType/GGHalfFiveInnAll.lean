module

public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem innSet_subset_matConjImage {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] (H : Subgroup (GL ι K)) (S : Set (GL ι K))
    (hS : ∀ h ∈ H, h ∈ S) :
    LargeEvenInnSet (LargeEvenProj H) ⊆ LargeEvenMatConjImage (LargeEvenProjMk H) S := by
  rintro _ ⟨r, rfl⟩
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk_surjective r
  refine ⟨(h₀ : GL ι K), hS _ h₀.2, fun h h' hh' => ?_⟩
  show (h₀ : LargeEvenProj H) * (h : LargeEvenProj H) * (h₀ : LargeEvenProj H)⁻¹ =
    (h' : LargeEvenProj H)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (by rw [hh']; rfl)

private theorem innSet_subset_chevID {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {K : Type} [Field K] (H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenInnSet (LargeEvenCenterQuot H) ⊆ LargeEvenChevIDImage A K H :=
  fun _ hφ => Subgroup.subset_closure (Or.inl hφ)

private theorem ggCharP_two_of_card {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = (2 ^ n) ^ 2) : CharP K 2 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hc⟩ := CharP.exists K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K p
  have hcard : Fintype.card K = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, h, ← pow_mul, mul_comm]
  have hdvd : p ∣ 2 ^ (2 * n) := by
    rw [← hcard, hk]
    exact dvd_pow_self p (PNat.ne_zero k)
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  subst hp2
  exact hc

private theorem su_mem_gu {K : Type} [Field K] [CharP K 2] {d n : ℕ} {g : GL (Fin d) K}
    (hg : g ∈ LargeEvenSUGroup (Fin d) K (2 ^ n)) : g ∈ LargeEvenGUSet (Fin d) K (2 ^ n) := by
  have hmap : ∀ M : Matrix (Fin d) (Fin d) K,
      M.map (fun x => x ^ 2 ^ n) = M.map (iterateFrobenius K 2 n) := by
    intro M
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, iterateFrobenius_def]
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨_, hid⟩ := hx
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    rw [one_smul]
    exact hid
  | one =>
    refine ⟨1, one_ne_zero, one_pow _, ?_⟩
    simp
  | mul x y _ _ hx hy =>
    obtain ⟨μx, hμx0, hμx1, hμx⟩ := hx
    obtain ⟨μy, hμy0, hμy1, hμy⟩ := hy
    refine ⟨μx * μy, mul_ne_zero hμx0 hμy0, by rw [mul_pow, hμx1, hμy1], ?_⟩
    rw [hmap] at hμx hμy ⊢
    simp only [Units.val_mul]
    rw [Matrix.map_mul, Matrix.transpose_mul]
    calc (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          (Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((x : Matrix (Fin d) (Fin d) K) * (y : Matrix (Fin d) (Fin d) K))
        = (Matrix.map (y : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
          ((Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n)).transpose *
            (x : Matrix (Fin d) (Fin d) K)) * (y : Matrix (Fin d) (Fin d) K) := by
          simp only [Matrix.mul_assoc]
      _ = (μx * μy) • (1 : Matrix (Fin d) (Fin d) K) := by
          rw [hμx, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hμy, smul_smul]
  | inv x _ hx =>
    obtain ⟨μ, hμ0, hμ1, hX⟩ := hx
    rw [hmap] at hX
    have hXZ : (x : Matrix (Fin d) (Fin d) K) *
        ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hXfZf : Matrix.map (x : Matrix (Fin d) (Fin d) K) (iterateFrobenius K 2 n) *
        Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
          (iterateFrobenius K 2 n) = 1 := by
      rw [← Matrix.map_mul, hXZ, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = 1 := by
      rw [← Matrix.transpose_mul, hXfZf, Matrix.transpose_one]
    have h2 : μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = (x : Matrix (Fin d) (Fin d) K) := by
      calc μ • (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose
          = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (μ • (1 : Matrix (Fin d) (Fin d) K)) := by
            rw [Matrix.mul_smul, Matrix.mul_one]
        _ = (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * ((Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (x : Matrix (Fin d) (Fin d) K)) := by rw [hX]
        _ = ((Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose * (Matrix.map (x : Matrix (Fin d) (Fin d) K)
            (iterateFrobenius K 2 n)).transpose) * (x : Matrix (Fin d) (Fin d) K) := by
            rw [Matrix.mul_assoc]
        _ = (x : Matrix (Fin d) (Fin d) K) := by rw [h1, Matrix.one_mul]
    have h3 : (Matrix.map ((x⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
        (iterateFrobenius K 2 n)).transpose = μ⁻¹ • (x : Matrix (Fin d) (Fin d) K) := by
      rw [← h2, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    refine ⟨μ⁻¹, inv_ne_zero hμ0, by rw [inv_pow, hμ1], ?_⟩
    rw [hmap]
    rw [h3, Matrix.smul_mul, hXZ]

private theorem recipeLinear_inn {d N : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    innSet_subset_matConjImage _ _ (fun _ _ => Set.mem_univ _)⟩

private theorem recipeUnitary_inn {d n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hcard, hQ⟩ := h
  haveI : CharP K 2 := ggCharP_two_of_card hcard
  refine ⟨K, inferInstance, inferInstance, hcard, hQ, ?_⟩
  exact innSet_subset_matConjImage _ _ (fun g hg => su_mem_gu hg)

private theorem recipeSymplecticDerived_inn {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m q true Q) :
    LargeEvenRecipeSymplectic m q true fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have hle : ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ ≤ LargeEvenSpGroup K m :=
    Subgroup.commutator_le_self _
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  exact innSet_subset_matConjImage _ _ (fun g hg => ⟨1, one_ne_zero, by
    rw [one_smul]; exact spForm_of_mem_spGroup (hle hg)⟩)

private theorem recipeTwisted_inn {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {ρ : Equiv.Perm (Fin r)} {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, innSet_subset_chevID _⟩

private theorem recipeG2Derived_inn {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeChevalley LargeEvenCartanG2 2 true Q) :
    LargeEvenRecipeChevalley LargeEvenCartanG2 2 true
      fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I :=
  recipeChevalley_inn h

private theorem recipeTwF4_inn {a : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeTwF4 a Q) :
    LargeEvenRecipeTwF4 a fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, innSet_subset_chevID _⟩

private theorem recipeSuzuki_inn {a : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, subset_rfl⟩

theorem largeEvenRawDatum_inn_all {lab : LargeEvenLabel} {Q : LargeEvenRawCont}
    (h : LargeEvenRawDatum lab Q) :
    LargeEvenRawDatum lab fun R _ I F => Q R I F ∧ LargeEvenInnSet R ⊆ I := by
  obtain ⟨tg, l, n⟩ := lab
  cases tg with
  | A => exact recipeLinear_inn h
  | twA => exact recipeUnitary_inn h
  | B => exact recipeSymplectic_inn h
  | C => exact recipeSymplectic_inn h
  | B2der => exact recipeSymplecticDerived_inn h
  | D =>
    by_cases hl : l = 3
    · have h' : LargeEvenRecipeLinear 4 (2 ^ n) Q := by
        simpa only [LargeEvenRawDatum, if_pos hl] using h
      show (if l = 3 then _ else _)
      rw [if_pos hl]
      exact recipeLinear_inn h'
    · have h' : LargeEvenRecipeOmegaPlus l (2 ^ n) Q := by
        simpa only [LargeEvenRawDatum, if_neg hl] using h
      show (if l = 3 then _ else _)
      rw [if_neg hl]
      exact recipeOmegaPlus_inn h'
  | twD =>
    by_cases hl2 : l = 2
    · have h' : LargeEvenRecipeLinear 2 ((2 ^ n) ^ 2) Q := by
        simpa only [LargeEvenRawDatum, if_pos hl2] using h
      show (if l = 2 then _ else _)
      rw [if_pos hl2]
      exact recipeLinear_inn h'
    · by_cases hl3 : l = 3
      · have h' : LargeEvenRecipeUnitary 4 (2 ^ n) Q := by
          simpa only [LargeEvenRawDatum, if_neg hl2, if_pos hl3] using h
        show (if l = 2 then _ else if l = 3 then _ else _)
        rw [if_neg hl2, if_pos hl3]
        exact recipeUnitary_inn h'
      · have h' : LargeEvenRecipeOmegaMinus (l - 1) (2 ^ n) Q := by
          simpa only [LargeEvenRawDatum, if_neg hl2, if_neg hl3] using h
        show (if l = 2 then _ else if l = 3 then _ else _)
        rw [if_neg hl2, if_neg hl3]
        exact recipeOmegaMinus_inn h'
  | E6 => exact recipeChevalley_inn h
  | E7 => exact recipeChevalley_inn h
  | E8 => exact recipeChevalley_inn h
  | F4 => exact recipeChevalley_inn h
  | G2 => exact recipeChevalley_inn h
  | G2der =>
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact recipeG2Derived_inn h
  | twE6 => exact recipeTwisted_inn h
  | triD4 => exact recipeTwisted_inn h
  | twB2 => exact recipeSuzuki_inn h
  | twF4 =>
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact recipeTwF4_inn h
  | twF4der =>
    dsimp only [LargeEvenRawDatum] at h ⊢
    exact recipeTwF4_inn h

theorem ggInnerDiagOn_of_inner {G : Type} [Group G] {Bs X : Subgroup G}
    (hmark : LargeEvenMarking ↥X fun _ _ _ _ _ _ => True)
    (hnorm : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinn : ∀ c ∈ Bs, ∃ n ∈ X, ∀ l ∈ X, c⁻¹ * l * c = n⁻¹ * l * n) :
    GGInnerDiagOn Bs X := by
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  refine ⟨hcomm, lab, hlab, ?_⟩
  refine largeEvenRawDatum_mono ?_ (largeEvenRawDatum_inn_all hraw)
  rintro R _ I F ⟨⟨hs, hna, θ, -⟩, hInn⟩
  refine ⟨hs, hna, θ, hnorm, fun c hc => ?_⟩
  obtain ⟨n, hnX, hn⟩ := hinn c hc
  let nX : ↥X := ⟨n, hnX⟩
  refine ⟨MulAut.conj ((θ (QuotientGroup.mk nX))⁻¹), hInn ⟨_, rfl⟩, ?_⟩
  intro l l' hl
  have hl' : l' = nX⁻¹ * l * nX := by
    apply Subtype.ext
    show (l' : G) = ((nX : ↥X)⁻¹ : G) * (l : G) * (nX : G)
    rw [hl, hn (l : G) l.2]
  calc (MulAut.conj ((θ (QuotientGroup.mk nX))⁻¹)) (θ (QuotientGroup.mk l))
      = (θ (QuotientGroup.mk nX))⁻¹ * θ (QuotientGroup.mk l) * θ (QuotientGroup.mk nX) := by
        rw [MulAut.conj_apply, inv_inv]
    _ = θ ((QuotientGroup.mk nX)⁻¹ * QuotientGroup.mk l * QuotientGroup.mk nX) := by
        rw [← map_inv, ← map_mul, ← map_mul]
    _ = θ (QuotientGroup.mk (nX⁻¹ * l * nX)) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    _ = θ (QuotientGroup.mk l') := by rw [hl']

end CFSG.StandardType

end
