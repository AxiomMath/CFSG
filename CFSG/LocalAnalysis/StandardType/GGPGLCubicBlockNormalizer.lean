module

public import CFSG.LocalAnalysis.StandardType.GGPGLCubicNormalizer
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseA
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseB
public import TauCeti.LinearAlgebra.Matrix.Block
meta import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

theorem exists_cubic_kernel_normalizer_of_diagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) {G : Subgroup (GL ι K)}
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hcard : (Nat.card G : K) ≠ 0)
    {X z : GL ι K} (hXG : X ∈ G) (hzG : z ∈ G) {l : Kˣ}
    (hX : X ^ 3 = GeneralLinearGroup.scalar ι l) (hl : ∀ μ : Kˣ, μ ^ 3 ≠ l)
    (hz3 : z ^ 3 = 1) {t : ι → K} (hz : (z : Matrix ι ι K) = diagonal t) :
    ∃ E : GL ι K, (E : Matrix ι ι K).det = 1 ∧
      (∀ Y ∈ G, Y ^ 3 = 1 → E * Y * E⁻¹ = Y) ∧ E * X * E⁻¹ = X * z := by
  classical
  let β := Set.range t
  let : Fintype β := Fintype.ofFinite β
  let w : ι → β := fun i => ⟨t i, ⟨i, rfl⟩⟩
  let Fib : β → Type _ := fun b => {i : ι // w i = b}
  have hdiag : ∀ Y ∈ G, IsBlockDiag t (Y : Matrix ι ι K) := by
    intro Y hY
    apply isBlockDiag_of_commute_diagonal
    rw [← hz, ← Units.val_mul, ← Units.val_mul, hcomm Y hY z hzG]
  have hdiagW : ∀ Y ∈ G, IsBlockDiag w (Y : Matrix ι ι K) := by
    intro Y hY i j hij
    exact hdiag Y hY i j (fun h => hij (Subtype.ext h))
  let ρ : ∀ b : β, G →* GL (Fib b) K := fun b => blockHom w b G hdiagW
  let X' : G := ⟨X, hXG⟩
  let z' : G := ⟨z, hzG⟩
  have ht3 : ∀ i, t i ^ 3 = 1 := by
    have h : (diagonal t) ^ 3 = (1 : Matrix ι ι K) := by
      rw [← hz, ← Units.val_pow_eq_pow_val, hz3, Units.val_one]
    intro i
    have hi := congrArg (fun M : Matrix ι ι K => M i i) h
    simpa [Matrix.diagonal_pow] using hi
  have hb3 : ∀ b : β, (b : K) ^ 3 = 1 := by
    intro b
    obtain ⟨i, hi⟩ := b.property
    rw [← hi]
    exact ht3 i
  let ζ : β → Kˣ := fun b =>
    ⟨b, (b : K) ^ 2, by rw [← pow_succ', hb3 b], by rw [← pow_succ, hb3 b]⟩
  have hζ3 : ∀ b, ζ b ^ 3 = 1 := fun b => Units.ext (hb3 b)
  have hρz : ∀ b, ρ b z' = GeneralLinearGroup.scalar (Fib b) (ζ b) := by
    intro b
    apply Units.ext
    rw [coe_blockHom, hz, GeneralLinearGroup.coe_scalar]
    ext i j
    change (diagonal t) (i : ι) (j : ι) = (Matrix.scalar (Fib b) (b : K)) i j
    have hi : t i = (b : K) := congrArg Subtype.val i.property
    have hij : (i : ι) = (j : ι) ↔ i = j := Subtype.val_injective.eq_iff
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hi, hij]
  have hρX : ∀ b, ρ b X' ^ 3 = GeneralLinearGroup.scalar (Fib b) l := by
    intro b
    apply Units.ext
    rw [← map_pow, coe_blockHom]
    change ((X ^ 3 : GL ι K) : Matrix ι ι K).toSquareBlock w b = _
    rw [hX, GeneralLinearGroup.coe_scalar, toSquareBlock_scalar, GeneralLinearGroup.coe_scalar]
  have hblocks : ∀ b : β, ∃ E : GL (Fib b) K, (E : Matrix (Fib b) (Fib b) K).det = 1 ∧
      (∀ (Y : GL ι K) (hY : Y ∈ G), Y ^ 3 = 1 →
        E * ρ b ⟨Y, hY⟩ * E⁻¹ = ρ b ⟨Y, hY⟩) ∧
      E * ρ b X' * E⁻¹ = ρ b z' * ρ b X' := by
    intro b
    have hcommB : ∀ x ∈ (ρ b).range, ∀ y ∈ (ρ b).range, x * y = y * x := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hcomm x x.property y y.property
    have hcardB : (Nat.card (ρ b).range : K) ≠ 0 := by
      intro hzero
      apply hcard
      rw [← Subgroup.card_ker_mul_card_range (ρ b), Nat.cast_mul, hzero, mul_zero]
    obtain ⟨E, hdet, hfix, hshift⟩ := exists_cubic_normalizer_of_commute h3 hcommB hcardB
      (MonoidHom.mem_range.mpr ⟨X', rfl⟩) (hρX b) hl (hζ3 b)
    refine ⟨E, hdet, ?_, ?_⟩
    · intro Y hY hY3
      have hy3 : (⟨Y, hY⟩ : G) ^ 3 = 1 := Subtype.ext hY3
      exact hfix _ (MonoidHom.mem_range.mpr ⟨⟨Y, hY⟩, rfl⟩)
        (by rw [← map_pow, hy3, map_one])
    · rw [hρz]
      exact hshift
  choose E hEdet hEfix hEX using hblocks
  let Q := ∀ b : β, GL (Fib b) K
  let e := Equiv.sigmaFiberEquiv w
  let re : Matrix (Σ b : β, Fib b) (Σ b : β, Fib b) K ≃+* Matrix ι ι K :=
    Matrix.reindexRingEquiv K e
  let emb : Q →* GL ι K :=
    (Units.map re.toMonoidHom).comp
      ((Units.map (Matrix.blockDiagonal'RingHom Fib K).toMonoidHom).comp
        (MulEquiv.piUnits : (∀ b : β, Matrix (Fib b) (Fib b) K)ˣ ≃* Q).symm.toMonoidHom)
  have hemb : ∀ D : Q, (emb D : Matrix ι ι K) =
      re (Matrix.blockDiagonal' (fun b => (D b : Matrix (Fib b) (Fib b) K))) := by
    intro D
    rfl
  have hrep : ∀ Y : G, emb (fun b => ρ b Y) = (Y : GL ι K) := by
    intro Y
    apply Units.ext
    rw [hemb]
    have hM : Matrix.blockDiagonal' (fun b => (ρ b Y : Matrix (Fib b) (Fib b) K)) =
        re.symm ((Y : GL ι K) : Matrix ι ι K) := by
      change Matrix.blockDiagonal' (fun b => (ρ b Y : Matrix (Fib b) (Fib b) K)) =
        Matrix.reindex e.symm e.symm ((Y : GL ι K) : Matrix ι ι K)
      ext ⟨b, i⟩ ⟨b', j⟩
      by_cases h : b = b'
      · subst b'
        simp [Matrix.blockDiagonal', Matrix.reindex_apply, e, ρ]
        exact congrFun (congrFun (coe_blockHom w b G hdiagW Y) i) j
      · have hij : w i ≠ w j := by simpa only [i.property, j.property] using h
        have hzero := hdiagW Y Y.property i j hij
        simp [Matrix.blockDiagonal', h, Matrix.reindex_apply, e, hzero]
    rw [hM, RingEquiv.apply_symm_apply]
  have hembdet : ∀ D : Q, (emb D : Matrix ι ι K).det =
      ∏ b, (D b : Matrix (Fib b) (Fib b) K).det := by
    intro D
    rw [hemb]
    change (Matrix.reindex e e (Matrix.blockDiagonal'
      (fun b => (D b : Matrix (Fib b) (Fib b) K)))).det = _
    rw [Matrix.det_reindex_self, Matrix.det_blockDiagonal']
  refine ⟨emb E, ?_, ?_, ?_⟩
  · rw [hembdet]
    simp only [hEdet, Finset.prod_const_one]
  · intro Y hY hY3
    have h : (E : Q) * (fun b => ρ b ⟨Y, hY⟩) * (E : Q)⁻¹ =
        (fun b => ρ b ⟨Y, hY⟩) := by
      funext b
      exact hEfix b Y hY hY3
    have hm := congrArg emb h
    rw [map_mul, map_mul, map_inv, hrep] at hm
    exact hm
  · have h : (E : Q) * (fun b => ρ b X') * (E : Q)⁻¹ =
        (fun b => ρ b z') * (fun b => ρ b X') := by
      funext b
      exact hEX b
    have hm := congrArg emb h
    rw [map_mul, map_mul, map_inv, map_mul, hrep, hrep] at hm
    change emb E * X * (emb E)⁻¹ = z * X at hm
    rw [hcomm z hzG X hXG] at hm
    exact hm

theorem exists_cubic_kernel_normalizer
    {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) {G : Subgroup (GL ι K)}
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hcard : (Nat.card G : K) ≠ 0)
    {X z : GL ι K} (hXG : X ∈ G) (hzG : z ∈ G) {l : Kˣ}
    (hX : X ^ 3 = GeneralLinearGroup.scalar ι l) (hl : ∀ μ : Kˣ, μ ^ 3 ≠ l)
    (hz3 : z ^ 3 = 1) :
    ∃ E : GL ι K, (E : Matrix ι ι K).det = 1 ∧
      (∀ Y ∈ G, Y ^ 3 = 1 → E * Y * E⁻¹ = Y) ∧ E * X * E⁻¹ = X * z := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_of_dvd (by decide) h3
  obtain ⟨P, hP⟩ := exists_conj_diagonal hζ ({z} : Set (GL ι K))
    (by rintro x rfl y rfl; rfl) (by rintro x rfl; exact hz3)
  let B := G.map (MulAut.conj P).toMonoidHom
  let X' : GL ι K := P * X * P⁻¹
  let z' : GL ι K := P * z * P⁻¹
  have hXB : X' ∈ B := ⟨X, hXG, rfl⟩
  have hzB : z' ∈ B := ⟨z, hzG, rfl⟩
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hcardB : (Nat.card B : K) ≠ 0 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj P).injective]
    exact hcard
  have hX' : X' ^ 3 = GeneralLinearGroup.scalar ι l := by
    change (P * X * P⁻¹) ^ 3 = _
    rw [conj_pow, hX, ← (commute_scalar l P).eq, mul_inv_cancel_right]
  have hz' : z' ^ 3 = 1 := by
    change (P * z * P⁻¹) ^ 3 = 1
    rw [conj_pow, hz3, mul_one, mul_inv_cancel]
  have hzdiag : (z' : Matrix ι ι K) = diagonal (fun i => (z' : Matrix ι ι K) i i) :=
    eq_diagonal_of_offDiag_eq_zero fun i j hij => by
      change ((P : Matrix ι ι K) * (z : Matrix ι ι K) *
        ((P⁻¹ : GL ι K) : Matrix ι ι K)) i j = 0
      exact hP z (by simp) i j hij
  obtain ⟨E, hdet, hfix, hmove⟩ := exists_cubic_kernel_normalizer_of_diagonal
    h3 hcommB hcardB hXB hzB hX' hl hz' hzdiag
  let F : GL ι K := P⁻¹ * E * P
  refine ⟨F, ?_, ?_, ?_⟩
  · have hdetU : GeneralLinearGroup.det E = 1 := Units.ext hdet
    change (GeneralLinearGroup.det (P⁻¹ * E * P) : K) = 1
    simp [map_mul, map_inv, hdetU]
  · intro Y hY hY3
    have hYB : P * Y * P⁻¹ ∈ B := ⟨Y, hY, rfl⟩
    have hY' : (P * Y * P⁻¹) ^ 3 = 1 := by rw [conj_pow, hY3, mul_one, mul_inv_cancel]
    calc F * Y * F⁻¹ = P⁻¹ * (E * (P * Y * P⁻¹) * E⁻¹) * P := by dsimp [F]; group
      _ = Y := by rw [hfix _ hYB hY']; group
  · calc F * X * F⁻¹ = P⁻¹ * (E * X' * E⁻¹) * P := by dsimp [F, X']; group
      _ = P⁻¹ * (X' * z') * P := by rw [hmove]
      _ = X * z := by dsimp [X', z']; group

end CFSG.StandardType.TypeA.PGLTor
