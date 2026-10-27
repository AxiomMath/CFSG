module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Gen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

theorem s16g_fixOrd_of_conj (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ}
    {g : Matrix.GeneralLinearGroup ι K} (hgΓ : g ∈ Γ) (hg : orderOf g = p) {κ : Type}
    (w : κ → ι → K) (hw : ∀ k, (g : Matrix ι ι K) *ᵥ w k = w k)
    (hconj : ∀ a : ι → K, a ≠ 0 → ∃ k, ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ w k = a) :
    FixOrd Γ p := by
  intro a ha
  have ha0 : Multiplicative.toAdd a ≠ 0 := fun h => ha (by rw [← ofAdd_toAdd a, h, ofAdd_zero])
  obtain ⟨k, A, hA, hAw⟩ := hconj (Multiplicative.toAdd a) ha0
  have hmem : A * g * A⁻¹ ∈ Γ := Γ.mul_mem (Γ.mul_mem hA hgΓ) (Γ.inv_mem hA)
  refine ⟨⟨A * g * A⁻¹, hmem⟩, ?_, ?_⟩
  · rw [Subgroup.orderOf_mk, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hg
  · have hAinv : ((A⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ
        ((A : Matrix ι ι K) *ᵥ w k) = w k := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    change Multiplicative.ofAdd
      ((((A * g * A⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)) *ᵥ
        Multiplicative.toAdd a) = a
    rw [← hAw, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hAinv, hw k, hAw, ofAdd_toAdd]

theorem s16g_fixNc_of_fixed_vector (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ}
    (hp : p.Prime)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {B : Subgroup (Matrix.GeneralLinearGroup ι K)} (hBΓ : B ≤ Γ) (hBc : Nat.card B = p ^ 2)
    (hBe : ∀ x ∈ B, x ^ p = 1) {u : ι → K} (hu : u ≠ 0)
    (hfix : ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ u = u) : FixNc Γ p :=
  s16g_fixNc_of_conj Γ hp B hBΓ hBc hBe (fun _ : Unit => u) (fun _ => hfix)
    fun a ha => ⟨(), htr u a hu ha⟩

theorem s16g_fixOrd_of_fixed_vector (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) {p : ℕ}
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {g : Matrix.GeneralLinearGroup ι K} (hgΓ : g ∈ Γ) (hg : orderOf g = p) {u : ι → K}
    (hu : u ≠ 0) (hfix : (g : Matrix ι ι K) *ᵥ u = u) : FixOrd Γ p :=
  s16g_fixOrd_of_conj Γ hgΓ hg (fun _ : Unit => u) (fun _ => hfix)
    fun a ha => ⟨(), htr u a hu ha⟩

theorem s16g_fixNc_of_fixed_singular [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΓQ : ∀ A ∈ Γ, ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {B : Subgroup (Matrix.GeneralLinearGroup ι K)} (hBΓ : B ≤ Γ) (hBc : Nat.card B = p ^ 2)
    (hBe : ∀ x ∈ B, x ^ p = 1) {u : ι → K} (hu : u ≠ 0) (hQu : Q u = 0)
    (hfix : ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ u = u) : FixNc Γ p := by
  have hBp : IsPGroup p B := IsPGroup.of_card hBc
  have key : ∀ c : K, ∃ w : ι → K, w ≠ 0 ∧ Q w = c ∧ ∀ b ∈ B, (b : Matrix ι ι K) *ᵥ w = w :=
    fun c => s16g_orth_values_of_singular Q hQ hp hp2 B hBp
      (fun b hb v => hΓQ b (hBΓ hb) v) hu hQu hfix c
  choose w hw0 hwQ hwfix using key
  refine s16g_fixNc_of_conj Γ hp B hBΓ hBc hBe w hwfix fun a ha => ?_
  obtain ⟨A, hA, hAw⟩ := htr (w (Q a)) a (hw0 _) ha (hwQ _)
  exact ⟨Q a, A, hA, hAw⟩

theorem s16g_fixOrd_of_fixed_singular [CharP K 2] (Q : QuadraticForm K (ι → K))
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (Γ : Subgroup (Matrix.GeneralLinearGroup ι K))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hΓQ : ∀ A ∈ Γ, ∀ v : ι → K, Q ((A : Matrix ι ι K) *ᵥ v) = Q v)
    (htr : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q x = Q y → ∃ A ∈ Γ, (A : Matrix ι ι K) *ᵥ x = y)
    {g : Matrix.GeneralLinearGroup ι K} (hgΓ : g ∈ Γ) (hg : orderOf g = p) {u : ι → K}
    (hu : u ≠ 0) (hQu : Q u = 0) (hfix : (g : Matrix ι ι K) *ᵥ u = u) : FixOrd Γ p := by
  have hle : Subgroup.zpowers g ≤ Γ := (Subgroup.zpowers_le).2 hgΓ
  have hBp : IsPGroup p (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg, pow_one])
  let S : Subgroup (Matrix.GeneralLinearGroup ι K) :=
    { carrier := {b | (b : Matrix ι ι K) *ᵥ u = u}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change ((a * b : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u = u
        rw [Units.val_mul, ← Matrix.mulVec_mulVec]
        change (a : Matrix ι ι K) *ᵥ u = u at ha
        change (b : Matrix ι ι K) *ᵥ u = u at hb
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        change ((a⁻¹ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K) *ᵥ u = u
        change (a : Matrix ι ι K) *ᵥ u = u at ha
        conv_lhs => rw [← ha]
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec] }
  have hSg : g ∈ S := hfix
  have hfixB : ∀ b ∈ Subgroup.zpowers g, (b : Matrix ι ι K) *ᵥ u = u :=
    fun b hb => (Subgroup.zpowers_le.2 hSg) hb
  have key : ∀ c : K, ∃ w : ι → K, w ≠ 0 ∧ Q w = c ∧
      ∀ b ∈ Subgroup.zpowers g, (b : Matrix ι ι K) *ᵥ w = w :=
    fun c => s16g_orth_values_of_singular Q hQ hp hp2 (Subgroup.zpowers g) hBp
      (fun b hb v => hΓQ b (hle hb) v) hu hQu hfixB c
  choose w hw0 hwQ hwfix using key
  refine s16g_fixOrd_of_conj Γ hgΓ hg w (fun k => hwfix k g (Subgroup.mem_zpowers g))
    fun a ha => ?_
  obtain ⟨A, hA, hAw⟩ := htr (w (Q a)) a (hw0 _) ha (hwQ _)
  exact ⟨Q a, A, hA, hAw⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
