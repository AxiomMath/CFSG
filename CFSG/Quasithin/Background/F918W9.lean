module

public import CFSG.Quasithin.Background.F918V0

public section

namespace CFSG.Quasithin

@[expose] def permS1 : Equiv.Perm (Fin 6) := Equiv.swap 1 2 * Equiv.swap 3 5

@[expose] def permS2 : Equiv.Perm (Fin 6) := Equiv.swap 1 4 * Equiv.swap 3 5

@[expose] def permS3 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 3 4

theorem permS_even : permS1 ∈ alternatingGroup (Fin 6) ∧ permS2 ∈ alternatingGroup (Fin 6) ∧
    permS3 ∈ alternatingGroup (Fin 6) := by
  refine ⟨?_, ?_, ?_⟩ <;> (rw [Equiv.Perm.mem_alternatingGroup]; decide)

theorem permS_rel :
    permS1 * permS1 = 1 ∧ permS2 * permS2 = 1 ∧ permS3 * permS3 = 1 ∧ permS1 ≠ 1 ∧ permS2 ≠ 1 ∧ permS3 ≠ 1 ∧
    permS1 ≠ permS2 ∧ permS1 ≠ permS3 ∧ permS2 ≠ permS3 ∧ (permS1 * permS2) ^ 3 = 1 ∧ (permS1 * permS3) ^ 3 = 1 ∧
    (permS2 * permS3) ^ 4 = 1 ∧ (permS1 * permS2 * permS3) ^ 5 = 1 := by
  unfold permS1 permS2 permS3
  decide

theorem exists_lift_invol {G : Type*} [Group G] (hZ3 : ∀ z ∈ Subgroup.center G, z ^ 3 = 1)
    (x : G ⧸ Subgroup.center G) (hx : x * x = 1) : ∃ y : G, y * y = 1 ∧ QuotientGroup.mk y = x := by
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  have hl : l * l ∈ Subgroup.center G := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hx
  have h3 := hZ3 _ hl
  refine ⟨l ^ 3, ?_, ?_⟩
  · calc l ^ 3 * l ^ 3 = l ^ 6 := by rw [← pow_add]
      _ = (l * l) ^ 3 := by rw [← pow_two, ← pow_mul]
      _ = 1 := h3
  · have : (QuotientGroup.mk l : G ⧸ Subgroup.center G) ^ 3 = QuotientGroup.mk l := by
      have h2 : (QuotientGroup.mk l : G ⧸ Subgroup.center G) ^ 2 = 1 := by simpa [pow_two] using hx
      calc (QuotientGroup.mk l : G ⧸ Subgroup.center G) ^ 3 = (QuotientGroup.mk l) ^ 2 * QuotientGroup.mk l := by
            rw [pow_succ]
        _ = QuotientGroup.mk l := by rw [h2, one_mul]
    simpa using this

theorem valentiner_center_pow_three {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hv : IsValentiner K Γ) :
    ∀ z ∈ Subgroup.center ↥Γ, z ^ 3 = 1 := by
  intro z hz
  have h3 : Nat.card (Subgroup.center ↥Γ) = 3 := hv.2.2.1.2.1
  have := pow_card_eq_one' (G := ↥(Subgroup.center ↥Γ)) (x := ⟨z, hz⟩)
  rw [h3] at this
  exact congrArg Subtype.val this

theorem exists_triple {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hv : IsValentiner K Γ) :
    ∃ x₁ x₂ x₃ : ↥Γ, x₁ * x₁ = 1 ∧ x₂ * x₂ = 1 ∧ x₃ * x₃ = 1 ∧ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ ∧
      x₁ ≠ 1 ∧ x₂ ≠ 1 ∧ x₃ ≠ 1 ∧ (x₁ * x₂) ^ 3 ∈ Subgroup.center ↥Γ ∧ (x₁ * x₃) ^ 3 ∈ Subgroup.center ↥Γ ∧
      (x₂ * x₃) ^ 4 ∈ Subgroup.center ↥Γ ∧ (x₁ * x₂ * x₃) ^ 5 ∈ Subgroup.center ↥Γ := by
  obtain ⟨ι⟩ := hv.2.2.1.2.2
  have hZ3 := valentiner_center_pow_three hv
  obtain ⟨he1, he2, he3⟩ := permS_even
  obtain ⟨r11, r22, r33, rn1, rn2, rn3, r12', r13', r23', r12, r13, r23, r123⟩ := permS_rel
  let s1 : alternatingGroup (Fin 6) := ⟨permS1, he1⟩
  let s2 : alternatingGroup (Fin 6) := ⟨permS2, he2⟩
  let s3 : alternatingGroup (Fin 6) := ⟨permS3, he3⟩
  have e11 : s1 * s1 = 1 := Subtype.ext r11
  have e22 : s2 * s2 = 1 := Subtype.ext r22
  have e33 : s3 * s3 = 1 := Subtype.ext r33
  have n1 : s1 ≠ 1 := fun h => rn1 (congrArg Subtype.val h)
  have n2 : s2 ≠ 1 := fun h => rn2 (congrArg Subtype.val h)
  have n3 : s3 ≠ 1 := fun h => rn3 (congrArg Subtype.val h)
  have d12 : s1 ≠ s2 := fun h => r12' (congrArg Subtype.val h)
  have d13 : s1 ≠ s3 := fun h => r13' (congrArg Subtype.val h)
  have d23 : s2 ≠ s3 := fun h => r23' (congrArg Subtype.val h)
  have q12 : (s1 * s2) ^ 3 = 1 := Subtype.ext r12
  have q13 : (s1 * s3) ^ 3 = 1 := Subtype.ext r13
  have q23 : (s2 * s3) ^ 4 = 1 := Subtype.ext r23
  have q123 : (s1 * s2 * s3) ^ 5 = 1 := Subtype.ext r123
  have hinv : ∀ s : alternatingGroup (Fin 6), s * s = 1 → ι.symm s * ι.symm s = 1 := fun s hs => by
    rw [← map_mul, hs, map_one]
  obtain ⟨x₁, hx₁, hm₁⟩ := exists_lift_invol hZ3 (ι.symm s1) (hinv s1 e11)
  obtain ⟨x₂, hx₂, hm₂⟩ := exists_lift_invol hZ3 (ι.symm s2) (hinv s2 e22)
  obtain ⟨x₃, hx₃, hm₃⟩ := exists_lift_invol hZ3 (ι.symm s3) (hinv s3 e33)
  have hne : ∀ {a b : ↥Γ} {s t : alternatingGroup (Fin 6)}, QuotientGroup.mk a = ι.symm s →
      QuotientGroup.mk b = ι.symm t → s ≠ t → a ≠ b := by
    intro a b s t ha hb hst hab
    apply hst
    apply ι.symm.injective
    rw [← ha, ← hb, hab]
  have hn1 : ∀ {a : ↥Γ} {s : alternatingGroup (Fin 6)}, QuotientGroup.mk a = ι.symm s → s ≠ 1 → a ≠ 1 := by
    intro a s ha hs h1
    apply hs
    apply ι.symm.injective
    rw [← ha, h1, map_one]
    rfl
  have hrel : ∀ (a b : ↥Γ) (s t : alternatingGroup (Fin 6)) (n : ℕ), QuotientGroup.mk a = ι.symm s →
      QuotientGroup.mk b = ι.symm t → (s * t) ^ n = 1 → (a * b) ^ n ∈ Subgroup.center ↥Γ := by
    intro a b s t n ha hb h
    rw [← QuotientGroup.eq_one_iff]
    have : (QuotientGroup.mk ((a * b) ^ n) : ↥Γ ⧸ Subgroup.center ↥Γ) = (ι.symm s * ι.symm t) ^ n := by
      rw [QuotientGroup.mk_pow, QuotientGroup.mk_mul, ha, hb]
    rw [this, ← map_mul, ← map_pow, h, map_one]
  have hm12 : (QuotientGroup.mk (x₁ * x₂) : ↥Γ ⧸ Subgroup.center ↥Γ) = ι.symm (s1 * s2) := by
    rw [QuotientGroup.mk_mul, hm₁, hm₂, map_mul]
  exact ⟨x₁, x₂, x₃, hx₁, hx₂, hx₃, hne hm₁ hm₂ d12, hne hm₁ hm₃ d13, hne hm₂ hm₃ d23, hn1 hm₁ n1, hn1 hm₂ n2,
    hn1 hm₃ n3, hrel _ _ _ _ 3 hm₁ hm₂ q12, hrel _ _ _ _ 3 hm₁ hm₃ q13, hrel _ _ _ _ 4 hm₂ hm₃ q23,
    hrel _ _ _ _ 5 hm12 hm₃ q123⟩

theorem card_valentiner {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) K)} (hv : IsValentiner K Γ) : Nat.card ↥Γ = 1080 := by
  obtain ⟨-, hcard, ⟨ι⟩⟩ := hv.2.2.1
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥Γ)
  have h2 : Nat.card (↥Γ ⧸ Subgroup.center ↥Γ) = 360 := by
    rw [Nat.card_congr ι.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  rw [h1, h2, hcard]

end CFSG.Quasithin
