module

public import CFSG.LocalAnalysis.StandardType.GGNbrLSideDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem ggInnDiagPSL3_of_conjAut_apply {X : Type} [Group X] {α : MulAut X} {Q : ℕ} {F : Type}
    [Field F] [Finite F] (hQ : Nat.card F = Q) (e : X ≃* projectiveSL 3 F) (g : GL (Fin 3) F)
    (h : ∀ x, e (α x) = conjAut 3 F g (e x)) : GGInnDiagPSL3 Q X α := by
  refine ⟨F, inferInstance, inferInstance, e, hQ, ?_⟩
  have : MulAut.congr e α = conjAut 3 F g := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [MulAut.congr_apply]
    simp [h]
  rw [this]
  exact conjAut_mem_linearAutGroup g

theorem ggNbrLSideInduces_mem {R : Type} [Group R] {ψ : MulAut R} {J : Subgroup R}
    {α : MulAut (↥J ⧸ Subgroup.center ↥J)} (h : GGNbrLSideInduces ψ J α) (j : ↥J) :
    ψ (j : R) ∈ J := by
  obtain ⟨j', hj', -⟩ := h j
  rw [← hj']
  exact j'.2

theorem ggNbrLSide_three_dvd_two_pow_sub_one_iff (e : ℕ) : 3 ∣ 2 ^ e - 1 ↔ Even e := by
  have key : ∀ m : ℕ, 2 ^ (2 * m) % 3 = 1 := fun m => by
    rw [pow_mul, Nat.pow_mod]
    simp
  have hpos : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rcases Nat.even_or_odd' e with ⟨m, rfl | rfl⟩
  · have := key m
    simp only [even_two_mul, iff_true]
    omega
  · have h := key m
    have : 2 ^ (2 * m + 1) % 3 = 2 := by
      rw [pow_succ, Nat.mul_mod, h]
    simp only [Nat.not_even_two_mul_add_one, iff_false]
    omega

theorem ggNbrLSide_even_of_odd_three_dvd {n k : ℕ} (hn : Odd n) (h : 3 ∣ (2 ^ n) ^ k - 1) :
    Even k := by
  rw [← pow_mul, ggNbrLSide_three_dvd_two_pow_sub_one_iff] at h
  exact (Nat.even_mul.1 h).resolve_left (Nat.not_even_iff_odd.2 hn)

theorem ggNbrLSideLargeRank_of_pow {lab : LargeEvenLabel} {k : ℕ} (hk : 0 < k) (h3k : 3 ∣ k)
    (hQ : 3 ∣ (2 ^ lab.n) ^ k - 1) (hr : 2 * k ≤ ggNbrLSideRank lab) :
    GGNbrLSideLargeRank lab := by
  rcases Nat.even_or_odd lab.n with he | ho
  · left
    obtain ⟨t, rfl⟩ := h3k
    exact ⟨he, by omega⟩
  · right
    refine ⟨ho, ?_⟩
    have hev := ggNbrLSide_even_of_odd_three_dvd ho hQ
    obtain ⟨t, rfl⟩ := h3k
    obtain ⟨u, hu⟩ := hev
    omega

theorem ggNbrLSideFamilyOf_eq_linear_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .linear ↔
      lab.tag = .A ∨ (lab.tag = .D ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 2) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_unitary_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .unitary ↔ lab.tag = .twA ∨ (lab.tag = .twD ∧ lab.rank = 3) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_symplectic_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .symplectic ↔ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .B2der := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_orthogonal_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .orthogonal ↔
      (lab.tag = .D ∧ lab.rank ≠ 3) ∨ (lab.tag = .twD ∧ lab.rank ≠ 2 ∧ lab.rank ≠ 3) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_excUntwisted_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .excUntwisted ↔ lab.tag = .G2 ∨ lab.tag = .G2der ∨ lab.tag = .F4 ∨
      lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_excTwisted_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .excTwisted ↔ lab.tag = .twE6 ∨ lab.tag = .triD4 := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

theorem ggNbrLSideFamilyOf_eq_suzukiRee_iff {lab : LargeEvenLabel} :
    ggNbrLSideFamilyOf lab = .suzukiRee ↔
      lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .twF4der := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggNbrLSideFamilyOf] <;> (try split_ifs) <;> simp_all

@[expose] def GGNbrLSideLinearData : Prop :=
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.A, ℓ, n⟩ → LargeEvenSplit 3 ⟨.A, ℓ, n⟩ → Nat.card K = 2 ^ n →
      GGNbrLSideDich ⟨.A, ℓ, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin (ℓ + 1)) K)) Set.univ)) ∧
  (∀ (n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.D, 3, n⟩ → LargeEvenSplit 3 ⟨.D, 3, n⟩ → Nat.card K = 2 ^ n →
      GGNbrLSideDich ⟨.D, 3, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin 4) K)) Set.univ)) ∧
  (∀ (n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.twD, 2, n⟩ → LargeEvenSplit 3 ⟨.twD, 2, n⟩ → Nat.card K = (2 ^ n) ^ 2 →
      GGNbrLSideDich ⟨.twD, 2, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSLGroup (Fin 2) K)) Set.univ))

theorem ggNbrLSideRSFamily_linear_of_data (h : GGNbrLSideLinearData) :
    GGNbrLSideRSFamily .linear := by
  obtain ⟨hA, hD, hT⟩ := h
  intro lab hf hlab hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases ggNbrLSideFamilyOf_eq_linear_iff.1 hf with ht | ⟨ht, hl⟩ | ⟨ht, hl⟩ <;>
    dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hA l n K hlab hs hK⟩
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hD n K hlab hs hK⟩
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hT n K hlab hs hK⟩

@[expose] def GGNbrLSideUnitaryData : Prop :=
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.twA, ℓ, n⟩ → LargeEvenSplit 3 ⟨.twA, ℓ, n⟩ → Nat.card K = (2 ^ n) ^ 2 →
      GGNbrLSideDich ⟨.twA, ℓ, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin (ℓ + 1)) K (2 ^ n)))
        (LargeEvenGUSet (Fin (ℓ + 1)) K (2 ^ n)))) ∧
  (∀ (n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.twD, 3, n⟩ → LargeEvenSplit 3 ⟨.twD, 3, n⟩ → Nat.card K = (2 ^ n) ^ 2 →
      GGNbrLSideDich ⟨.twD, 3, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSUGroup (Fin 4) K (2 ^ n))) (LargeEvenGUSet (Fin 4) K (2 ^ n))))

theorem ggNbrLSideRSFamily_unitary_of_data (h : GGNbrLSideUnitaryData) :
    GGNbrLSideRSFamily .unitary := by
  obtain ⟨hA, hD⟩ := h
  intro lab hf hlab hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases ggNbrLSideFamilyOf_eq_unitary_iff.1 hf with ht | ⟨ht, hl⟩ <;>
    dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hA l n K hlab hs hK⟩
  · dsimp only at hl
    subst hl
    simp only [LargeEvenRawDatum, ↓reduceIte, show (3 : ℕ) ≠ 2 by norm_num] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hD n K hlab hs hK⟩

@[expose] def GGNbrLSideSymplecticData : Prop :=
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.B, ℓ, n⟩ → LargeEvenSplit 3 ⟨.B, ℓ, n⟩ → Nat.card K = 2 ^ n →
      GGNbrLSideDich ⟨.B, ℓ, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) (LargeEvenGSpSet K ℓ))) ∧
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.C, ℓ, n⟩ → LargeEvenSplit 3 ⟨.C, ℓ, n⟩ → Nat.card K = 2 ^ n →
      GGNbrLSideDich ⟨.C, ℓ, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk (LargeEvenSpGroup K ℓ)) (LargeEvenGSpSet K ℓ))) ∧
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.B2der, ℓ, n⟩ → LargeEvenSplit 3 ⟨.B2der, ℓ, n⟩ → Nat.card K = 2 →
      GGNbrLSideDich ⟨.B2der, ℓ, n⟩ (LargeEvenMatConjImage
        (LargeEvenProjMk ⁅LargeEvenSpGroup K 2, LargeEvenSpGroup K 2⁆) (LargeEvenGSpSet K 2)))

theorem ggNbrLSideRSFamily_symplectic_of_data (h : GGNbrLSideSymplecticData) :
    GGNbrLSideRSFamily .symplectic := by
  obtain ⟨hB, hC, hD⟩ := h
  intro lab hf hlab hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases ggNbrLSideFamilyOf_eq_symplectic_iff.1 hf with ht | ht | ht <;>
    dsimp only at ht <;> subst ht
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hB l n K hlab hs hK⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hC l n K hlab hs hK⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hD l n K hlab hs hK⟩

@[expose] def GGNbrLSideOrthogonalData : Prop :=
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 ⟨.D, ℓ, n⟩ → 4 ≤ ℓ → LargeEvenSplit 3 ⟨.D, ℓ, n⟩ → Nat.card K = 2 ^ n →
      GGNbrLSideDich ⟨.D, ℓ, n⟩ (LargeEvenInnSet
        (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K ℓ))))) ∧
  (∀ (ℓ n : ℕ) (K : Type) [Field K] [Finite K] (b c : K),
    LargeEvenInLambda2 ⟨.twD, ℓ, n⟩ → 4 ≤ ℓ → LargeEvenSplit 3 ⟨.twD, ℓ, n⟩ →
      Nat.card K = 2 ^ n → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        GGNbrLSideDich ⟨.twD, ℓ, n⟩ (LargeEvenInnSet
          (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (ℓ - 1) b c)))))

theorem ggNbrLSideRSFamily_orthogonal_of_data (h : GGNbrLSideOrthogonalData) :
    GGNbrLSideRSFamily .orthogonal := by
  obtain ⟨hP, hM⟩ := h
  intro lab hf hlab hs Q hQ
  obtain ⟨t, l, n⟩ := lab
  rcases ggNbrLSideFamilyOf_eq_orthogonal_iff.1 hf with ⟨ht, hl⟩ | ⟨ht, hl2, hl3⟩
  · dsimp only at ht hl
    subst ht
    have hl4 : 4 ≤ l := by
      have : 3 ≤ l := hlab.2
      omega
    simp only [LargeEvenRawDatum, hl, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hP l n K hlab hl4 hs hK⟩
  · dsimp only at ht hl2 hl3
    subst ht
    have hl4 : 4 ≤ l := by
      have : 2 ≤ l := hlab.2
      omega
    simp only [LargeEvenRawDatum, hl2, hl3, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ',
      hM l n K b c hlab hl4 hs hK hbc⟩

@[expose] def GGNbrLSideChevDatum {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (derived : Bool) (q : ℕ)
    (lab : LargeEvenLabel) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
    Nat.card K = q → GGNbrLSideDich lab (LargeEvenChevIDImage A K (LargeEvenChevH A K derived))

@[expose] def GGNbrLSideExcUntwData : Prop :=
  (∀ lab : LargeEvenLabel, lab.tag = .G2 →
    GGNbrLSideChevDatum LargeEvenCartanG2 false (2 ^ lab.n) lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .G2der → GGNbrLSideChevDatum LargeEvenCartanG2 true 2 lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .F4 →
    GGNbrLSideChevDatum LargeEvenCartanF4 false (2 ^ lab.n) lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .E6 →
    GGNbrLSideChevDatum (LargeEvenCartanE 6) false (2 ^ lab.n) lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .E7 →
    GGNbrLSideChevDatum (LargeEvenCartanE 7) false (2 ^ lab.n) lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .E8 →
    GGNbrLSideChevDatum (LargeEvenCartanE 8) false (2 ^ lab.n) lab)

theorem ggNbrLSideRSFamily_excUntwisted_of_data (h : GGNbrLSideExcUntwData) :
    GGNbrLSideRSFamily .excUntwisted := by
  obtain ⟨hG, hGd, hF, hE6, hE7, hE8⟩ := h
  intro lab hf hlab hs Q hQ
  have key : ∀ {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {derived : Bool} {q : ℕ},
      GGNbrLSideChevDatum A derived q lab → LargeEvenRecipeChevalley A q derived Q →
      LargeEvenRecipeChevalley A q derived fun R _ I F => Q R I F ∧ GGNbrLSideDich lab I := by
    intro r A derived q hd hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hd K hlab hs hK⟩
  rcases ggNbrLSideFamilyOf_eq_excUntwisted_iff.1 hf with ht | ht | ht | ht | ht | ht
  · have hd := hG lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hGd lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hF lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hE6 lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hE7 lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hE8 lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ

@[expose] def GGNbrLSideTwistedDatum {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (ρ : Equiv.Perm (Fin r)) (m : ℕ) (lab : LargeEvenLabel) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
    Nat.card K = (2 ^ lab.n) ^ m →
      GGNbrLSideDich lab (LargeEvenChevIDImage A K (LargeEvenTwistedH A K ρ lab.n))

@[expose] def GGNbrLSideExcTwData : Prop :=
  (∀ lab : LargeEvenLabel, lab.tag = .twE6 →
    GGNbrLSideTwistedDatum (LargeEvenCartanE 6) LargeEvenRhoE6 2 lab) ∧
  (∀ lab : LargeEvenLabel, lab.tag = .triD4 →
    GGNbrLSideTwistedDatum LargeEvenCartanD4 LargeEvenRhoD4 3 lab)

theorem ggNbrLSideRSFamily_excTwisted_of_data (h : GGNbrLSideExcTwData) :
    GGNbrLSideRSFamily .excTwisted := by
  obtain ⟨hE, hD⟩ := h
  intro lab hf hlab hs Q hQ
  have key : ∀ {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {ρ : Equiv.Perm (Fin r)} {m : ℕ},
      GGNbrLSideTwistedDatum A ρ m lab → LargeEvenRecipeTwisted A ρ m lab.n Q →
      LargeEvenRecipeTwisted A ρ m lab.n fun R _ I F => Q R I F ∧ GGNbrLSideDich lab I := by
    intro r A ρ m hd hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hd K hlab hs hK⟩
  rcases ggNbrLSideFamilyOf_eq_excTwisted_iff.1 hf with ht | ht
  · have hd := hE lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ
  · have hd := hD lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    exact key hd hQ

@[expose] def GGNbrLSideSuzukiReeData : Prop :=
  (∀ lab : LargeEvenLabel, lab.tag = .twB2 → ∀ (K : Type) [Field K] [Finite K],
    LargeEvenInLambda2 lab → LargeEvenSplit 3 lab → Nat.card K = 2 ^ (2 * ((lab.n - 1) / 2) + 1) →
      GGNbrLSideDich lab (LargeEvenInnSet
        (LargeEvenCenterQuot (LargeEvenSzGroup ((lab.n - 1) / 2) K)))) ∧
  (∀ lab : LargeEvenLabel, (lab.tag = .twF4 ∨ lab.tag = .twF4der) → ∀ (K : Type) [Field K]
    [Finite K], LargeEvenInLambda2 lab → LargeEvenSplit 3 lab →
      Nat.card K = 2 ^ (2 * ((lab.n - 1) / 2) + 1) →
        GGNbrLSideDich lab (LargeEvenChevIDImage LargeEvenCartanF4 K
          (LargeEvenTwF4H ((lab.n - 1) / 2) K)))

theorem ggNbrLSideRSFamily_suzukiRee_of_data (h : GGNbrLSideSuzukiReeData) :
    GGNbrLSideRSFamily .suzukiRee := by
  obtain ⟨hS, hR⟩ := h
  intro lab hf hlab hs Q hQ
  rcases ggNbrLSideFamilyOf_eq_suzukiRee_iff.1 hf with ht | ht | ht
  · have hd := hS lab ht
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeSuzuki] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hd K hlab hs hK⟩
  · have hd := hR lab (Or.inl ht)
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hd K hlab hs hK⟩
  · have hd := hR lab (Or.inr ht)
    obtain ⟨t, l, n⟩ := lab
    dsimp only at ht
    subst ht
    dsimp only [LargeEvenRawDatum, LargeEvenRecipeTwF4] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ', hd K hlab hs hK⟩

theorem ggNbrLSideRS_of_data (h1 : GGNbrLSideLinearData) (h2 : GGNbrLSideUnitaryData)
    (h3 : GGNbrLSideSymplecticData) (h4 : GGNbrLSideOrthogonalData)
    (h5 : GGNbrLSideExcUntwData) (h6 : GGNbrLSideExcTwData) (h7 : GGNbrLSideSuzukiReeData) :
    GGNbrLSideRS :=
  ggNbrLSideRS_of_families fun f => by
    cases f
    exacts [ggNbrLSideRSFamily_linear_of_data h1, ggNbrLSideRSFamily_unitary_of_data h2,
      ggNbrLSideRSFamily_symplectic_of_data h3, ggNbrLSideRSFamily_orthogonal_of_data h4,
      ggNbrLSideRSFamily_excUntwisted_of_data h5, ggNbrLSideRSFamily_excTwisted_of_data h6,
      ggNbrLSideRSFamily_suzukiRee_of_data h7]

end CFSG.StandardType

end
