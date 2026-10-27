module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUNorm
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm
import CFSG.LieType.Steinberg.CentralExt.HermitianBasis
import CFSG.RankThree.Classical.SemilinearFixedBasis
import CFSG.RankThree.SteinbergR3ELinearTwoFieldDescent
import CFSG.LocalAnalysis.ComponentInitial.FieldUnitaryNorm
public import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard

public section

namespace CFSG.StandardType

namespace RecipeFieldSpU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem map_bar_mul' (X Y : Matrix (Fin n) (Fin n) K) :
    (X * Y).map h.bar = X.map h.bar * Y.map h.bar :=
  Matrix.map_mul (f := h.bar)

theorem map_bar_smul' (c : K) (X : Matrix (Fin n) (Fin n) K) :
    (c • X).map h.bar = h.bar c • X.map h.bar := by
  ext i j
  simp

theorem bar_transpose_bar' (X : Matrix (Fin n) (Fin n) K) :
    (((X.map h.bar)ᵀ).map h.bar)ᵀ = X := by
  ext i j
  simp [UnitaryFieldData.bar_bar]

theorem transpose_map_bar_map' (σ : K ≃+* K) (X : Matrix (Fin n) (Fin n) K) :
    ((X.map h.bar)ᵀ).map σ = ((X.map σ).map h.bar)ᵀ := by
  ext i j
  simp [map_bar_comm h σ]

variable {h}

theorem exists_unitary_mul_map_eq_smul [NeZero n] {σ : K ≃+* K} {ℓ : ℕ} (hσ : orderOf σ = ℓ)
    (hℓ : Odd ℓ) (A : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) {c : K}
    (hc : twNorm σ ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ℓ =
      c • (1 : Matrix (Fin n) (Fin n) K)) :
    ∃ (H : primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (d : Kˣ),
      (A : GL (Fin n) K) * glAut σ (H : GL (Fin n) K) =
        GeneralLinearGroup.scalar (Fin n) d * H := by
  classical
  have := h.finite
  have : Fact p.Prime := ⟨h.prime⟩
  have : CharP K p := h.charP
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have hσℓ : σ ^ ℓ = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hℓ0 : 0 < ℓ := hℓ.pos
  set M : Matrix (Fin n) (Fin n) K := ((A : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) with hM
  obtain ⟨X, d₁, hXu, hd₁0, hXσ⟩ :=
    exists_mul_map_eq_smul_of_twNorm hσ (Matrix.isUnits_det_units (A : GL (Fin n) K)) hc
  have hMu : (M.map h.bar)ᵀ * M = 1 := by
    have h1 : (M.map h.bar)ᵀ * ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M =
        ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := mem_primeFormUnitary.mp A.2
    rwa [Units.val_one, Matrix.mul_one] at h1
  have hMu' : M * (M.map h.bar)ᵀ = 1 := mul_eq_one_comm.mp hMu
  have hXσ' : X.map σ = d₁ • ((M.map h.bar)ᵀ * X) := by
    calc X.map σ = (M.map h.bar)ᵀ * (M * X.map σ) := by
          rw [← Matrix.mul_assoc, hMu, Matrix.one_mul]
      _ = _ := by rw [hXσ, Matrix.mul_smul]
  set B : Matrix (Fin n) (Fin n) K := (X.map h.bar)ᵀ * X with hB
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = h.bar d₁ * d₁ := ⟨_, rfl⟩
  have hBσ : B.map σ = μ • B := by
    rw [hμ, hB, map_mul_ringEquiv, transpose_map_bar_map', hXσ', map_bar_smul',
      Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_bar_mul',
      Matrix.transpose_mul, bar_transpose_bar', Matrix.mul_assoc, ← Matrix.mul_assoc M, hMu',
      Matrix.one_mul]
  have hXdet : X.det ≠ 0 := hXu.ne_zero
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hXdet) hXdet
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, Matrix.det_zero] at hBdet
    exact hBdet rfl
  have hμℓ : ∏ i ∈ Finset.range ℓ, (σ ^ i) μ = 1 := by
    have h1 := map_pow_eq_prod_smul σ hBσ ℓ
    have hone : B.map ⇑(σ ^ ℓ) = B := by
      rw [hσℓ]
      ext i j
      rfl
    rw [hone] at h1
    exact smul_left_injective K hB0 (h1.symm.trans (one_smul K B).symm)
  have hμ0 : μ ≠ 0 := by
    rw [hμ]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hd₁0) hd₁0
  let a : K ≃+ K :=
    { toFun := fun x => μ * σ x
      invFun := fun x => σ.symm (μ⁻¹ * x)
      left_inv := fun x => by
        simp only
        rw [inv_mul_cancel_left₀ hμ0, RingEquiv.symm_apply_apply]
      right_inv := fun x => by
        simp only
        rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hμ0]
      map_add' := fun x y => by simp only [map_add, mul_add] }
  have ha : ∀ (c v : K), a (c • v) = σ c • a v := fun c v => by
    change μ * σ (c * v) = σ c * (μ * σ v)
    rw [map_mul]
    ring
  have hah : ∀ v, (⇑a)^[ℓ] v = v := fun v => by
    change (fun y : K => μ * σ y)^[ℓ] v = v
    rw [iterate_mul_map_apply, hμℓ, one_mul, hσℓ]
    rfl
  have hcard : Nat.card K = p ^ (2 * f) := h.card
  obtain ⟨hℓdvd, k₀, hk₀, hk₀card, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis h.prime (by have := h.one_le; omega) hcard σ
      hσ (Module.finrank_self K) a ha hah
  have hw0 : b 0 ≠ 0 := b.ne_zero 0
  have hw : μ * σ (b 0) = b 0 := hb 0
  have hbarμ : h.bar μ = μ := by rw [hμ, map_mul, UnitaryFieldData.bar_bar, mul_comm]
  have hS : ∀ x, μ * σ x = x → μ * σ (h.bar x) = h.bar x := fun x hx => by
    rw [map_bar_comm h σ, ← hbarμ, ← map_mul, hx]
  have he : ∃ e, σ e = e ∧ h.bar e ≠ e := by
    by_contra hall
    push Not at hall
    have hτ : ∀ x, CFSG.LieType.BorelTits.unitaryInvolution K p f x = h.bar x := fun x => by
      rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, UnitaryFieldData.bar_apply]
    have hmem := CFSG.RankThree.LinearTwo.mem_zpowers_of_forall_fixed h.prime
      (by have := h.one_le; omega : 1 ≤ 2 * f) hcard σ
      (CFSG.LieType.BorelTits.unitaryInvolution K p f) fun x hx => by rw [hτ]; exact hall x hx
    have hdvd := orderOf_dvd_of_mem_zpowers hmem
    have hτ2 : orderOf (CFSG.LieType.BorelTits.unitaryInvolution K p f) = 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine orderOf_eq_prime ?_ ?_
      · ext x
        rw [pow_two, RingAut.mul_apply, hτ, hτ, UnitaryFieldData.bar_bar]
        rfl
      · intro h1
        obtain ⟨c, hc⟩ := h.exists_bar_ne
        apply hc
        rw [← hτ, h1]
        rfl
    rw [hτ2, hσ] at hdvd
    exact (Nat.not_even_iff_odd.mpr hℓ) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨e, hσe, hbare⟩ := he
  obtain ⟨t, ht0, hbart, hμt⟩ : ∃ t : K, t ≠ 0 ∧ h.bar t = t ∧ μ * σ t = t := by
    by_cases hwb : b 0 + h.bar (b 0) = 0
    · have hew : μ * σ (e * b 0) = e * b 0 := by
        rw [map_mul, hσe, mul_left_comm, hw]
      refine ⟨e * b 0 + h.bar (e * b 0), ?_, ?_, ?_⟩
      · have h1 : e * b 0 + h.bar (e * b 0) = (e - h.bar e) * b 0 := by
          rw [map_mul, show h.bar (b 0) = -b 0 by linear_combination hwb]
          ring
        rw [h1]
        exact mul_ne_zero (sub_ne_zero.mpr (Ne.symm hbare)) hw0
      · rw [map_add, UnitaryFieldData.bar_bar, add_comm]
      · rw [map_add, mul_add, hew, hS _ hew]
    · refine ⟨b 0 + h.bar (b 0), hwb, ?_, ?_⟩
      · rw [map_add, UnitaryFieldData.bar_bar, add_comm]
      · rw [map_add, mul_add, hw, hS _ hw]
  have hBherm : (B.map h.bar)ᵀ = B := by
    rw [hB, map_bar_mul', Matrix.transpose_mul, bar_transpose_bar']
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin n) (Fin n) K, B' = t • B := ⟨_, rfl⟩
  have hB'σ : B'.map σ = B' := by
    rw [hB', map_smul_ringEquiv, hBσ, smul_smul, show σ t * μ = t by rw [mul_comm]; exact hμt]
  have hB'herm : (B'.map h.bar)ᵀ = B' := by
    rw [hB', map_bar_smul', hbart, Matrix.transpose_smul, hBherm]
  have hB'det : B'.det ≠ 0 := by
    rw [hB', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht0) hBdet
  have hk₀mem : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk₀]
    rfl
  obtain ⟨g, hg⟩ : ℓ ∣ f := (Nat.coprime_two_right.mpr hℓ).dvd_of_dvd_mul_left hℓdvd
  have hk₀card' : Nat.card k₀ = (p ^ g) ^ 2 := by
    rw [hk₀card, ← pow_mul, hg, show 2 * (ℓ * g) = ℓ * (2 * g) by ring,
      Nat.mul_div_cancel_left _ hℓ0, mul_comm]
  have : CharP k₀ p := ⟨fun m => by
    rw [← k₀.subtype_injective.eq_iff, map_natCast, map_zero]
    exact CharP.cast_eq_zero_iff K p m⟩
  have hbarpow : ∀ x : k₀, h.bar (x : K) = (x : K) ^ p ^ g := fun x => by
    have : Fintype k₀ := Fintype.ofFinite k₀
    have hx : x ^ Fintype.card k₀ = x := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hk₀card'] at hx
    have hx' : (x : K) ^ (p ^ g) ^ 2 = x := by
      have h1 := congrArg Subtype.val hx
      rwa [SubmonoidClass.coe_pow] at h1
    have hiter : ∀ i : ℕ, (x : K) ^ ((p ^ g) ^ 2) ^ i = x := by
      intro i
      induction i with
      | zero => rw [pow_zero, pow_one]
      | succ i ih => rw [pow_succ, pow_mul, ih, hx']
    obtain ⟨j, hj⟩ := hℓ
    rw [UnitaryFieldData.bar_apply, hg, hj,
      show p ^ ((2 * j + 1) * g) = ((p ^ g) ^ 2) ^ j * p ^ g by ring, pow_mul, hiter]
  have hB'mem : ∀ i j, B' i j ∈ k₀ := fun i j =>
    (hk₀mem _).mpr (congrFun (congrFun hB'σ i) j)
  let B₀ : Matrix (Fin n) (Fin n) k₀ := fun i j => ⟨B' i j, hB'mem i j⟩
  have hτ₀ : ∀ x : k₀, (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g x : K) =
      h.bar (x : K) := fun x => by
    rw [hbarpow, CFSG.LieType.BorelTits.unitaryInvolution_apply, SubmonoidClass.coe_pow]
  have hB₀herm : CFSG.LieType.Universal.Unitary.conjTr
      (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g) B₀ = B₀ := by
    ext i j
    change (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g (B₀ j i) : K) = B' i j
    rw [hτ₀]
    exact congrFun (congrFun hB'herm i) j
  have hB₀map : B₀.map k₀.subtype = B' := by
    ext i j
    rfl
  have hB₀det : B₀.det ≠ 0 := by
    intro h0
    apply hB'det
    rw [← hB₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one (F := k₀) (p := p)
    (f := g) hk₀card' hB₀herm hB₀det
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin n) (Fin n) K,
      P = (P₀ : Matrix (Fin n) (Fin n) k₀).map k₀.subtype := ⟨_, rfl⟩
  have hPσ : P.map σ = P := by
    rw [hP]
    ext i j
    exact (hk₀mem _).mp ((P₀ : Matrix (Fin n) (Fin n) k₀) i j).2
  have hPu : (P.map h.bar)ᵀ * B' * P = 1 := by
    have h1 := congrArg k₀.subtype.mapMatrix hP₀
    rw [map_mul, map_mul, map_one] at h1
    have hc : k₀.subtype.mapMatrix (CFSG.LieType.Universal.Unitary.conjTr
        (CFSG.LieType.BorelTits.unitaryInvolution k₀ p g) (P₀ : Matrix (Fin n) (Fin n) k₀)) =
          (P.map h.bar)ᵀ := by
      rw [hP]
      ext i j
      exact hτ₀ _
    rw [hc, RingHom.mapMatrix_apply, hB₀map, RingHom.mapMatrix_apply, ← hP] at h1
    exact h1
  obtain ⟨s, hs⟩ := (unitary_field_norm h).1 ⟨t, (UnitaryFieldData.mem_fixedField h).mpr hbart⟩
  have hs' : s * h.bar s = t := by
    have h1 := congrArg Subtype.val hs
    rwa [UnitaryFieldData.coe_normHom, UnitaryFieldData.norm] at h1
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hs'
    exact ht0 hs'.symm
  set Xgl : GL (Fin n) K := ((Matrix.isUnit_iff_isUnit_det X).mpr hXu).unit with hXgl
  set Hgl : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) (Units.mk0 s hs0) * Xgl *
    Matrix.GeneralLinearGroup.map k₀.subtype P₀ with hHgl
  have hHmat : (Hgl : Matrix (Fin n) (Fin n) K) = s • (X * P) := by
    rw [hHgl, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Units.val_mk0,
      Matrix.scalar_apply, ← smul_eq_diagonal_mul, Matrix.smul_mul, hP, hXgl]
    rfl
  have hHu : Hgl ∈ primeFormUnitary h ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [mem_primeFormUnitary, Units.val_one, Matrix.mul_one, hHmat, map_bar_smul', map_bar_mul',
      Matrix.transpose_smul, Matrix.transpose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← hPu, hB', hB]
    rw [show h.bar s * s = t by rw [mul_comm]; exact hs']
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hd0 : σ s * d₁ * s⁻¹ ≠ 0 :=
    mul_ne_zero (mul_ne_zero ((map_ne_zero σ).mpr hs0) hd₁0) (inv_ne_zero hs0)
  have key : M * (Hgl : Matrix (Fin n) (Fin n) K).map σ =
      (σ s * d₁ * s⁻¹) • (Hgl : Matrix (Fin n) (Fin n) K) := by
    rw [hHmat, map_smul_ringEquiv, map_mul_ringEquiv, hPσ, Matrix.mul_smul, ← Matrix.mul_assoc,
      hXσ, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    field_simp
  refine ⟨⟨Hgl, hHu⟩, Units.mk0 _ hd0, ?_⟩
  apply Units.ext
  change M * ((Hgl : Matrix (Fin n) (Fin n) K).map σ) =
    Matrix.scalar (Fin n) (σ s * d₁ * s⁻¹) * (Hgl : Matrix (Fin n) (Fin n) K)
  rw [Matrix.scalar_apply, ← smul_eq_diagonal_mul]
  exact key

end RecipeFieldSpU

end CFSG.StandardType
