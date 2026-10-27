module

public import CFSG.LocalAnalysis.StandardType.GGPGLToralityBasic

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] {p : ℕ}

theorem exists_conj_diagonal [NeZero p] {ζ : K} (hζ : IsPrimitiveRoot ζ p) (S : Set (GL ι K))
    [Finite S] (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hpow : ∀ x ∈ S, x ^ p = 1) :
    ∃ A : GL ι K, ∀ x ∈ S, ∀ i j, i ≠ j →
      ((A : Matrix ι ι K) * (x : Matrix ι ι K) * ((A⁻¹ : GL ι K) : Matrix ι ι K)) i j = 0 := by
  classical
  let f : S → Module.End K (ι → K) := fun x => Matrix.toLinAlgEquiv' ((x : GL ι K) : Matrix ι ι K)
  have hf_comm : ∀ x y, Commute (f x) (f y) := fun x y => by
    have h2 : ((x : GL ι K) : Matrix ι ι K) * ((y : GL ι K) : Matrix ι ι K) =
        ((y : GL ι K) : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm x x.2 y y.2]
    show f x * f y = f y * f x
    simp only [f, ← map_mul, h2]
  have hf_pow : ∀ x, f x ^ p = 1 := fun x => by
    have h2 : ((x : GL ι K) : Matrix ι ι K) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hpow x x.2, Units.val_one]
    simp only [f, ← map_pow, h2, map_one]
  obtain ⟨b, μ, hb⟩ :=
    CFSG.RankThree.PartOne.exists_basis_common_eigenvectors_of_pow_eq_one hζ f hf_comm hf_pow
  let e : Fin (Module.finrank K (ι → K)) ≃ ι :=
    (finCongr (Module.finrank_fintype_fun_eq_card K)).trans (Fintype.equivFin ι).symm
  let b' : Module.Basis ι K (ι → K) := b.reindex e
  have hb' : ∀ (x : S) (j : ι), f x (b' j) = μ x (e.symm j) • b' j := fun x j => by
    simp only [b', Module.Basis.reindex_apply]
    exact hb x _
  let P : Matrix ι ι K := (Pi.basisFun K ι).toMatrix b'
  have hPi : Invertible P := (Pi.basisFun K ι).invertibleToMatrix b'
  let Pu : GL ι K := unitOfInvertible P
  refine ⟨Pu⁻¹, fun x hx i j hij => ?_⟩
  have hcol : ∀ j : ι, ((x : GL ι K) : Matrix ι ι K) *ᵥ (b' j) = μ ⟨x, hx⟩ (e.symm j) • b' j :=
    fun j => by
      have := hb' ⟨x, hx⟩ j
      simpa [f] using this
  have hxP : ((x : GL ι K) : Matrix ι ι K) * P =
      P * diagonal (fun j => μ ⟨x, hx⟩ (e.symm j)) := by
    ext a j
    have h := congrFun (hcol j) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h
    rw [Matrix.mul_diagonal]
    simp only [P, Matrix.mul_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h, mul_comm]
  have h1 : ((Pu⁻¹ : GL ι K) : Matrix ι ι K) = ⅟P := rfl
  have h2 : (((Pu⁻¹)⁻¹ : GL ι K) : Matrix ι ι K) = P := by simp [Pu]
  rw [h1, h2, Matrix.mul_assoc, hxP, ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul,
    diagonal_apply_ne _ hij]

section Blocks

variable {β : Type*}

@[expose] def IsBlockDiag (w : ι → β) (M : Matrix ι ι K) : Prop :=
  ∀ i j, w i ≠ w j → M i j = 0

omit [DecidableEq ι] in
theorem IsBlockDiag.mul {w : ι → β} {M N : Matrix ι ι K} (hM : IsBlockDiag w M)
    (hN : IsBlockDiag w N) : IsBlockDiag w (M * N) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : w i = w k
  · rw [hN k j (hk ▸ hij), mul_zero]
  · rw [hM i k hk, zero_mul]

theorem isBlockDiag_of_commute_diagonal {t : ι → K} {M : Matrix ι ι K}
    (h : M * diagonal t = diagonal t * M) : IsBlockDiag t M := by
  intro i j hij
  have h1 := congrFun (congrFun h i) j
  rw [mul_diagonal, diagonal_mul] at h1
  have h2 : M i j * (t j - t i) = 0 := by rw [mul_sub, h1]; ring
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hij

variable [DecidableEq β]

omit [DecidableEq ι] in
theorem toSquareBlock_mul_of_isBlockDiag {w : ι → β} {M : Matrix ι ι K} (hM : IsBlockDiag w M)
    (N : Matrix ι ι K) (b : β) :
    (M * N).toSquareBlock w b = M.toSquareBlock w b * N.toSquareBlock w b := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [toSquareBlock_def, of_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k => w k = b) (fun k => M i k * N k j)]
  have h0 : ∑ k : {k // ¬ w k = b}, M i k * N k j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [hM i k (by rw [hi]; exact Ne.symm k.2), zero_mul]
  rw [h0, add_zero]

omit [Fintype ι] [DecidableEq β] in
theorem toSquareBlock_one (w : ι → β) (b : β) :
    (1 : Matrix ι ι K).toSquareBlock w b = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [toSquareBlock_def, of_apply, one_apply, Subtype.mk.injEq]

theorem toSquareBlock_scalar (w : ι → β) (b : β) (c : K) :
    (scalar ι c).toSquareBlock w b = scalar {i // w i = b} c := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  simp only [toSquareBlock_def, of_apply, scalar_apply, diagonal_apply, Subtype.mk.injEq]

theorem toSquareBlock_pow_of_isBlockDiag {w : ι → β} {M : Matrix ι ι K} (hM : IsBlockDiag w M)
    (b : β) (n : ℕ) : (M ^ n).toSquareBlock w b = (M.toSquareBlock w b) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, toSquareBlock_one]
  | succ n ih => rw [pow_succ', toSquareBlock_mul_of_isBlockDiag hM, ih, pow_succ']

end Blocks

theorem exists_pow_eq_of_pow_eq_scalar {S : Type*} [Fintype S] [DecidableEq S] (hp : p.Prime)
    {M : Matrix S S K} {μ : Kˣ} (hM : M ^ p = scalar S (μ : K)) (hS : ¬ p ∣ Fintype.card S) :
    ∃ c : Kˣ, c ^ p = μ := by
  have hdet : M.det ^ p = (μ : K) ^ Fintype.card S := by
    rw [← det_pow, hM, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ]
  have hdet0 : M.det ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hdet
    exact (pow_ne_zero _ μ.ne_zero) hdet.symm
  set δ : Kˣ := Units.mk0 M.det hdet0 with hδ
  have h1 : δ ^ p = μ ^ Fintype.card S := Units.ext (by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hδ, Units.val_mk0, hdet])
  set q : PowQuot K p := QuotientGroup.mk μ with hq
  have hq1 : q ^ Fintype.card S = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, powQuot_mk_eq_one_iff]
    exact ⟨δ, h1⟩
  have hq2 : q ^ p = 1 := by
    rw [hq, ← QuotientGroup.mk_pow, powQuot_mk_eq_one_iff]
    exact ⟨μ, rfl⟩
  have hcop : Nat.gcd (Fintype.card S) p = 1 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hS)
  have h3 := pow_gcd_eq_one.mpr ⟨hq1, hq2⟩
  rw [hcop, pow_one, hq, powQuot_mk_eq_one_iff] at h3
  exact h3

theorem diag_ne_zero_of_eq_diagonal {D : GL ι K} {δ : ι → K}
    (hD : (D : Matrix ι ι K) = diagonal δ) (i : ι) : δ i ≠ 0 := by
  intro h0
  have h1 := D.isUnit.map (Matrix.detMonoidHom (n := ι) (R := K))
  rw [Matrix.coe_detMonoidHom, hD, det_diagonal,
    Finset.prod_eq_zero (Finset.mem_univ i) h0] at h1
  exact not_isUnit_zero h1

theorem card_le_of_diag [Finite K] [NeZero p] {G : Subgroup (GL ι K)} (A : GL ι K) {β : Type*}
    [DecidableEq β] (w : ι → β) (i₀ : ι)
    (hD : ∀ x ∈ G, ∃ δ : ι → K, (A : Matrix ι ι K) * (x : Matrix ι ι K) *
        ((A⁻¹ : GL ι K) : Matrix ι ι K) = diagonal δ ∧
      (∀ i j, w i = w j → δ i = δ j) ∧ ∀ i, δ i ^ p = δ i₀ ^ p) :
    Nat.card G ≤ (Nat.card K - 1) * p ^ ((Finset.univ.image w).card - 1) := by
  classical
  choose δ hδ hconst hroot using fun x : G => hD x x.2
  have hδ0 : ∀ (x : G) i, δ x i ≠ 0 := fun x i =>
    diag_ne_zero_of_eq_diagonal (D := A * (x : GL ι K) * A⁻¹)
      (by rw [Units.val_mul, Units.val_mul]; exact hδ x) i
  set T : Finset β := (Finset.univ.image w).erase (w i₀) with hT
  have hrep : ∀ b : T, ∃ i, w i = b := fun b => by
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase b.2)
    exact ⟨i, hi⟩
  choose rep hrep using hrep
  let F : G → Kˣ × (T → rootsOfUnity p K) := fun x =>
    (Units.mk0 (δ x i₀) (hδ0 x i₀), fun b =>
      ⟨Units.mk0 (δ x (rep b) / δ x i₀) (div_ne_zero (hδ0 x _) (hδ0 x i₀)), by
        rw [mem_rootsOfUnity]
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, Units.val_mk0, div_pow, hroot x,
          div_self (pow_ne_zero _ (hδ0 x i₀)), Units.val_one]⟩)
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : δ x i₀ = δ y i₀ := by
      have := congrArg (fun z => ((z.1 : Kˣ) : K)) hxy
      simpa [F] using this
    have hb : ∀ b : T, δ x (rep b) = δ y (rep b) := fun b => by
      have := congrArg (fun z => (((z.2 b : rootsOfUnity p K) : Kˣ) : K)) hxy
      simp only [F, Units.val_mk0] at this
      rw [h0] at this
      exact (div_left_inj' (hδ0 y i₀)).mp this
    have hall : δ x = δ y := funext fun i => by
      by_cases hi : w i = w i₀
      · rw [hconst x i i₀ hi, hconst y i i₀ hi, h0]
      · have hmem : w i ∈ T :=
          Finset.mem_erase.mpr ⟨hi, Finset.mem_image_of_mem w (Finset.mem_univ i)⟩
        have h1 := hrep ⟨w i, hmem⟩
        rw [hconst x i (rep ⟨w i, hmem⟩) h1.symm, hconst y i (rep ⟨w i, hmem⟩) h1.symm, hb]
    have hmat : (A : Matrix ι ι K) * ((x : GL ι K) : Matrix ι ι K) *
        ((A⁻¹ : GL ι K) : Matrix ι ι K) = (A : Matrix ι ι K) * ((y : GL ι K) : Matrix ι ι K) *
        ((A⁻¹ : GL ι K) : Matrix ι ι K) := by
      rw [hδ x, hδ y, hall]
    have hunits : A * (x : GL ι K) * A⁻¹ = A * (y : GL ι K) * A⁻¹ :=
      Units.ext (by simpa only [Units.val_mul] using hmat)
    exact Subtype.ext (mul_left_cancel (mul_right_cancel hunits))
  have hcard : Nat.card (Kˣ × (T → rootsOfUnity p K)) ≤
      (Nat.card K - 1) * p ^ ((Finset.univ.image w).card - 1) := by
    rw [Nat.card_prod, Nat.card_units, Nat.card_fun]
    have hTc : Nat.card T = (Finset.univ.image w).card - 1 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, hT,
        Finset.card_erase_of_mem (Finset.mem_image_of_mem w (Finset.mem_univ i₀))]
    rw [hTc]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (card_rootsOfUnity K p) _)
  exact (Nat.card_le_card_of_injective F hinj).trans hcard

end CFSG.StandardType.TypeA.PGLTor
