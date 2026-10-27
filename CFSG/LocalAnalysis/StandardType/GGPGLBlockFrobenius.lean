module

public import CFSG.LocalAnalysis.StandardType.GGPGLCentralKernel
public import CFSG.LocalAnalysis.StandardType.GGPGLToralityCaseA
public import CFSG.LinearAlgebra.FrobeniusPowerNormalizer
public import CFSG.Mathlib.LinearAlgebra.Matrix.BlockDiagonalGroups
public import CFSG.Mathlib.GroupTheory.CyclicPowers

public section

namespace CFSG.StandardType.TypeA.PGLTor

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    [Finite K] [CharP K 2] {p : ℕ} {G : Subgroup (GL ι K)}

omit [Finite K] [CharP K 2] in
theorem blockReindex_supported_scalar {κ : Type*} [DecidableEq κ]
    (β : ι → κ) (b : κ) (u : Kˣ) :
    GeneralLinearGroup.blockReindex β b
        (blockScalarHom β (fun j => if j = b then u else 1)) =
      GeneralLinearGroup.blockDiagonal
        (GeneralLinearGroup.scalar {i // β i = b} u) (1 : GL {i // β i ≠ b} K) := by
  classical
  apply Units.ext
  rw [GeneralLinearGroup.coe_blockReindex, blockScalarHom_coe,
    GeneralLinearGroup.coe_blockDiagonal]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · by_cases hij : i = j
    · subst j
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_apply_eq, i.2]
    · have hval : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, GeneralLinearGroup.coe_scalar,
        Matrix.scalar_apply, Matrix.diagonal_apply_ne, hij, hval]
  · have hij : (i : ι) ≠ (j : ι) := fun h => j.2 (h ▸ i.2)
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, hij]
  · have hij : (i : ι) ≠ (j : ι) := fun h => i.2 (h.symm ▸ j.2)
    simp [Matrix.reindex_apply, Matrix.submatrix_apply, hij]
  · by_cases hij : i = j
    · subst j
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply_eq, i.2]
    · have hval : (i : ι) ≠ (j : ι) := fun h => hij (Subtype.ext h)
      simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply_ne,
        Matrix.one_apply_ne, hij, hval]

omit [Finite K] [CharP K 2] in
theorem commute_blockScalarHom_of_blockReindex
    {κ : Type*} [DecidableEq κ] (β : ι → κ) (b : κ)
    (F : GL {i // β i = b} K) (E : GL ι K)
    (hE : GeneralLinearGroup.blockReindex β b E = GeneralLinearGroup.blockDiagonal F
      (1 : GL {i // β i ≠ b} K)) (f : κ → Kˣ) :
    Commute E (blockScalarHom β f) := by
  classical
  let C := blockScalarHom β f
  let Φ := GeneralLinearGroup.blockReindex (R := K) β b
  have hblock : IsBlockDiag β (C : Matrix ι ι K) := by
    intro i j hij
    have hne : i ≠ j := fun he => hij (he ▸ rfl)
    rw [blockScalarHom_coe, Matrix.diagonal_apply_ne _ hne]
  have hsel : (C : Matrix ι ι K).toSquareBlock β b =
      scalar {i // β i = b} (f b : K) := by
    change (blockScalarHom β f : Matrix ι ι K).toSquareBlock β b = _
    rw [blockScalarHom_coe]
    ext i j
    simp only [Matrix.toSquareBlock]
    change (diagonal (fun k => (f (β k) : K))) (i : ι) (j : ι) =
      scalar {i // β i = b} (f b : K) i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.scalar_apply, i.2]
    · have hval : (i : ι) ≠ (j : ι) := fun he => hij (Subtype.ext he)
      simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne, hij, hval]
  have hΦC := GeneralLinearGroup.coe_blockReindex_of_isBlockDiag β b C hblock
  rw [hsel] at hΦC
  have hFC : (F : Matrix {i // β i = b} {i // β i = b} K) *
      scalar {i // β i = b} (f b : K) =
      scalar {i // β i = b} (f b : K) * (F : Matrix {i // β i = b} {i // β i = b} K) := by
    simpa only [Units.val_mul, GeneralLinearGroup.coe_scalar] using
      congrArg (fun x : GL {i // β i = b} K =>
        (x : Matrix {i // β i = b} {i // β i = b} K)) (commute_scalar (f b) F).eq.symm
  change E * C = C * E
  apply Φ.injective
  rw [map_mul, map_mul, hE]
  apply Units.ext
  dsimp only [Φ]
  simp only [Units.val_mul, GeneralLinearGroup.coe_blockDiagonal, hΦC,
    Matrix.fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rw [hFC]

omit [CharP K 2] in
theorem exists_partial_power_normalizer_blockReindex {κ : Type*} [DecidableEq κ]
    (β : ι → κ) (b : κ) (G : Subgroup (GL ι K))
    (hblock : ∀ x ∈ G, IsBlockDiag β ((x : GL ι K) : Matrix ι ι K))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hcard : (Nat.card G : K) ≠ 0) :
    ∃ (F : GL {i // β i = b} K) (E : GL ι K),
      GeneralLinearGroup.blockReindex β b E = GeneralLinearGroup.blockDiagonal F
        (1 : GL {i // β i ≠ b} K) ∧
      (E : Matrix ι ι K).det = 1 ∧
      ∀ (x : G) (u : Kˣ), (x : GL ι K) ^ Nat.card K =
          GeneralLinearGroup.scalar ι u * (x : GL ι K) →
        E * (x : GL ι K) * E⁻¹ =
          blockScalarHom β (fun j => if j = b then u else 1) * (x : GL ι K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let f := blockHom β b G hblock
  let S := f.range
  have hcardS : (Nat.card S : K) ≠ 0 := by
    intro h0
    apply hcard
    rw [← Subgroup.card_ker_mul_card_range f, Nat.cast_mul, h0, mul_zero]
  have hcommS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (Subtype.ext (hcomm x x.2 y y.2))
  obtain ⟨F, hFdet, hF⟩ := CFSG.LinearAlgebra.exists_conj_eq_pow_card_GL_of_fintype
    hcommS hcardS
  let Φ := GeneralLinearGroup.blockReindex (R := K) β b
  let H := GeneralLinearGroup.blockDiagonal F (1 : GL {i // β i ≠ b} K)
  let E := Φ.symm H
  have hΦE : Φ E = H := Φ.apply_symm_apply H
  have hEdet : (E : Matrix ι ι K).det = 1 := by
    have h := GeneralLinearGroup.det_blockReindex β b E
    rw [hΦE] at h
    rw [GeneralLinearGroup.det_blockDiagonal, hFdet] at h
    simpa [H] using h.symm
  refine ⟨F, E, hΦE, hEdet, ?_⟩
  intro x u hxq
  let c : G := x ^ Nat.card K * x⁻¹
  have hc : (c : GL ι K) = GeneralLinearGroup.scalar ι u := by
    change (x : GL ι K) ^ Nat.card K * (x : GL ι K)⁻¹ = _
    rw [hxq, mul_assoc, mul_inv_cancel, mul_one]
  have hfc : f c = GeneralLinearGroup.scalar {i // β i = b} u := by
    apply Units.ext
    simp only [f, coe_blockHom, hc, GeneralLinearGroup.coe_scalar, toSquareBlock_scalar]
  have hcx : c * x = x ^ Nat.card K := by dsimp only [c]; group
  have hleft : F * f x * F⁻¹ = GeneralLinearGroup.scalar {i // β i = b} u * f x := by
    calc F * f x * F⁻¹ = f (x ^ Nat.card K) := by
          rw [map_pow, Nat.card_eq_fintype_card]
          exact hF (f x) ⟨x, rfl⟩
      _ = f c * f x := by rw [← map_mul, hcx]
      _ = _ := by rw [hfc]
  have hΦx : (Φ (x : GL ι K) : Matrix ({i // β i = b} ⊕ {i // β i ≠ b})
        ({i // β i = b} ⊕ {i // β i ≠ b}) K) =
      fromBlocks (((x : GL ι K) : Matrix ι ι K).toSquareBlock β b) 0 0
        (((x : GL ι K) : Matrix ι ι K).submatrix
          (fun i : {i // β i ≠ b} => (i : ι)) (fun i : {i // β i ≠ b} => (i : ι))) :=
    GeneralLinearGroup.coe_blockReindex_of_isBlockDiag β b (x : GL ι K)
      (fun i j hij => hblock x x.2 i j hij)
  have hm : (F : Matrix {i // β i = b} {i // β i = b} K) *
      (((x : GL ι K) : Matrix ι ι K).toSquareBlock β b) *
        ((F⁻¹ : GL {i // β i = b} K) : Matrix {i // β i = b} {i // β i = b} K) =
      (GeneralLinearGroup.scalar {i // β i = b} u : Matrix {i // β i = b} {i // β i = b} K) *
        (((x : GL ι K) : Matrix ι ι K).toSquareBlock β b) := by
    simpa only [Units.val_mul, f, coe_blockHom] using
      congrArg (fun a : GL {i // β i = b} K => (a : Matrix {i // β i = b} {i // β i = b} K)) hleft
  apply Φ.injective
  rw [map_mul, map_mul, map_inv, map_mul, hΦE]
  rw [blockReindex_supported_scalar]
  apply Units.ext
  simp only [Units.val_mul, H, GeneralLinearGroup.blockDiagonal_inv,
    GeneralLinearGroup.coe_blockDiagonal, hΦx, fromBlocks_multiply,
    Units.val_one, inv_one, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
    Matrix.one_mul, Matrix.mul_one]
  rw [hm]

omit [CharP K 2] in
theorem exists_partial_power_normalizer_commute_blocks {κ : Type*} [DecidableEq κ]
    (β : ι → κ) (b : κ) (G : Subgroup (GL ι K))
    (hblock : ∀ x ∈ G, IsBlockDiag β ((x : GL ι K) : Matrix ι ι K))
    (hcomm : ∀ x ∈ G, ∀ y ∈ G, x * y = y * x) (hcard : (Nat.card G : K) ≠ 0) :
    ∃ E : GL ι K, (E : Matrix ι ι K).det = 1 ∧
      (∀ f : κ → Kˣ, Commute E (blockScalarHom β f)) ∧
      ∀ (x : G) (u : Kˣ), (x : GL ι K) ^ Nat.card K =
          GeneralLinearGroup.scalar ι u * (x : GL ι K) →
        E * (x : GL ι K) * E⁻¹ =
          blockScalarHom β (fun j => if j = b then u else 1) * (x : GL ι K) := by
  obtain ⟨F, E, hblockE, hdet, hcontrol⟩ :=
    exists_partial_power_normalizer_blockReindex β b G hblock hcomm hcard
  exact ⟨E, hdet, fun f => commute_blockScalarHom_of_blockReindex β b F E hblockE f, hcontrol⟩

theorem isProjElem_card_cast_ne_zero [Nonempty ι] (hp : p.Prime) (hp2 : p ≠ 2)
    (hG : IsProjElem p G) : (Nat.card G : K) ≠ 0 := by
  classical
  intro hzero
  have hdiv : 2 ∣ Nat.card G := (CharP.cast_eq_zero_iff K 2 _).mp hzero
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 hdiv
  have hmod : p % 2 = 1 := by
    rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩ <;> omega
  have hxp : x ^ p = x := by simpa only [hx, hmod, pow_one] using (pow_mod_orderOf x p).symm
  have hxp' : (x : GL ι K) ^ p = (x : GL ι K) := by
    simpa only [Subgroup.coe_pow] using congrArg (fun a : G => (a : GL ι K)) hxp
  have hx2 : (x : GL ι K) ^ 2 = 1 := by
    have h : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    simpa only [Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg (fun a : G => (a : GL ι K)) h
  obtain ⟨u, hu⟩ := hG.pow_scalar x x.2
  rw [hxp'] at hu
  have hu2 : u ^ 2 = 1 := scalar_injective (ι := ι) (by
    rw [map_pow, ← hu, hx2, map_one])
  have hu1 : u = 1 := by
    apply Units.ext
    apply CharTwo.sq_inj.mp
    simpa using congrArg (fun a : Kˣ => (a : K)) hu2
  have hx1 : x = 1 := by
    apply Subtype.ext
    rw [hu, hu1, map_one]
    rfl
  rw [hx1, orderOf_one] at hx
  norm_num at hx

omit [CharP K 2] in
theorem CentralBlockModel.exists_raw_SL_block_operator
    (D : CentralBlockModel p G)
    (hcard : (Nat.card G : K) ≠ 0) (b : Fin D.numBlocks) :
    ∃ E : SpecialLinearGroup ι K,
      (∀ f : Fin D.numBlocks → Kˣ, Commute (SpecialLinearGroup.toGL E) (D.scalarBlocks f)) ∧
      ∀ (x : G) (u : Kˣ), (x : GL ι K) ^ Nat.card K =
          GeneralLinearGroup.scalar ι u * (x : GL ι K) →
        SpecialLinearGroup.toGL E * (x : GL ι K) * (SpecialLinearGroup.toGL E)⁻¹ =
          D.scalarBlocks (fun j => if j = b then u else 1) * (x : GL ι K) := by
  classical
  let B := G.map (MulAut.conj D.basis).toMonoidHom
  have hblock : ∀ x ∈ B, IsBlockDiag D.block (x : Matrix ι ι K) := by
    rintro _ ⟨x, hx, rfl⟩
    exact D.isBlockDiag x hx
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg (MulAut.conj D.basis)
      (congrArg Subtype.val (D.commutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  have hcardB : (Nat.card B : K) ≠ 0 := by
    dsimp only [B]
    rw [Subgroup.card_map_of_injective (MulAut.conj D.basis).injective]
    exact hcard
  obtain ⟨E₀, hE₀det, hE₀comm, hE₀⟩ :=
    exists_partial_power_normalizer_commute_blocks D.block b B hblock hcomm hcardB
  let E := D.basis⁻¹ * E₀ * D.basis
  have hEdet : (E : Matrix ι ι K).det = 1 := by
    have hi : (((D.basis⁻¹ * D.basis : GL ι K) : Matrix ι ι K)).det = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.det_one]
    rw [Units.val_mul, Matrix.det_mul] at hi
    change (((D.basis⁻¹ * E₀ * D.basis : GL ι K) : Matrix ι ι K)).det = 1
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hE₀det, mul_one, hi]
  let E' : SpecialLinearGroup ι K := ⟨(E : Matrix ι ι K), hEdet⟩
  have hE' : SpecialLinearGroup.toGL E' = E := by apply Units.ext; rfl
  refine ⟨E', ?_, ?_⟩
  · intro f
    rw [hE', D.scalarBlocks_apply]
    simpa only [E, MulAut.conj_apply, inv_inv, MulEquiv.coe_toMonoidHom] using
      (hE₀comm f).map (MulAut.conj D.basis⁻¹).toMonoidHom
  · intro x u hxq
    let y : B := ⟨(MulAut.conj D.basis) x, x, x.2, rfl⟩
    have hconjscalar : (MulAut.conj D.basis) (GeneralLinearGroup.scalar ι u) =
        GeneralLinearGroup.scalar ι u := by
      rw [MulAut.conj_apply, ← scalar_mul_comm u D.basis, mul_assoc, mul_inv_cancel, mul_one]
    have hyq : (y : GL ι K) ^ Nat.card K = GeneralLinearGroup.scalar ι u * y := by
      change (MulAut.conj D.basis) x ^ Nat.card K =
        GeneralLinearGroup.scalar ι u * (MulAut.conj D.basis) x
      rw [← map_pow, hxq, map_mul, hconjscalar]
    have hr := hE₀ y u hyq
    change E₀ * (D.basis * (x : GL ι K) * D.basis⁻¹) * E₀⁻¹ =
      blockScalarHom D.block (fun j => if j = b then u else 1) *
        (D.basis * (x : GL ι K) * D.basis⁻¹) at hr
    rw [hE', D.scalarBlocks_apply]
    calc E * (x : GL ι K) * E⁻¹ = D.basis⁻¹ *
          (E₀ * (D.basis * (x : GL ι K) * D.basis⁻¹) * E₀⁻¹) * D.basis := by
            dsimp only [E]
            group
      _ = D.basis⁻¹ * (blockScalarHom D.block (fun j => if j = b then u else 1) *
          (D.basis * (x : GL ι K) * D.basis⁻¹)) * D.basis := by rw [hr]
      _ = (D.basis⁻¹ * blockScalarHom D.block (fun j => if j = b then u else 1) * D.basis) *
          (x : GL ι K) := by group

omit [CharP K 2] in
theorem CentralBlockModel.isPrimitiveRoot_scalar_pow_card_sub_one_div
    (D : CentralBlockModel p G) (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) :
    IsPrimitiveRoot (D.scalar ^ ((Nat.card K - 1) / p)) p := by
  let μ := D.scalar ^ ((Nat.card K - 1) / p)
  have hμp : μ ^ p = 1 := by
    dsimp only [μ]
    rw [← pow_mul, Nat.div_mul_cancel hpK]
    simpa only [Nat.card_units] using (pow_card_eq_one' (x := D.scalar))
  have hμne : μ ≠ 1 := by
    intro h0
    have hdiv : p ∣ Nat.card Kˣ := by simpa only [Nat.card_units] using hpK
    have hpow : D.scalar ^ (Nat.card Kˣ / p) = 1 := by
      simpa only [μ, Nat.card_units] using h0
    obtain ⟨u, hu⟩ := IsCyclic.exists_pow_eq_of_pow_card_div_eq_one hp.pos hdiv hpow
    exact D.scalar_not_pow u hu
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hμp) with h1 | hpμ
  · exact (hμne (orderOf_eq_one_iff.mp h1)).elim
  · exact hpμ

theorem CentralBlockModel.exists_SL_normalizer_fix_kernel_move
    (D : CentralBlockModel p G) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpK : p ∣ Nat.card K - 1) (hG : IsProjElem p G) (hn : D.numBlocks = 3)
    (hcard : p ^ 2 * (Nat.card K - 1) ≤ Nat.card D.kernel) :
    ∃ E : SpecialLinearGroup ι K,
      (∀ x ∈ G, SpecialLinearGroup.toGL E * x * (SpecialLinearGroup.toGL E)⁻¹ ∈ G) ∧
      (∀ x ∈ D.kernel, SpecialLinearGroup.toGL E * x *
        (SpecialLinearGroup.toGL E)⁻¹ = x) ∧
      ∀ u : Kˣ, SpecialLinearGroup.toGL E * (D.primitive : GL ι K) *
        (SpecialLinearGroup.toGL E)⁻¹ ≠
          GeneralLinearGroup.scalar ι u * (D.primitive : GL ι K) := by
  classical
  have : Nonempty ι := ⟨D.point⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨Eraw, _hcommBlocks, hRaw⟩ :=
    D.exists_raw_SL_block_operator (isProjElem_card_cast_ne_zero hp hp2 hG) (D.block D.point)
  let E := SpecialLinearGroup.toGL Eraw
  have hEdet : (E : Matrix ι ι K).det = 1 := Eraw.property
  let k := (Nat.card K - 1) / p
  have hpk : p * k = Nat.card K - 1 := by
    have h := Nat.mod_add_div (Nat.card K - 1) p
    rw [Nat.mod_eq_zero_of_dvd hpK, zero_add] at h
    exact h
  have hq : Nat.card K = p * k + 1 := by have := Finite.one_lt_card (α := K); omega
  have hunitpow : ∀ u : Kˣ, u ^ (Nat.card K - 1) = 1 := by
    intro u
    simpa only [Nat.card_units] using (pow_card_eq_one' (x := u))
  let μ : G → Kˣ := fun x => lam hp hp2 hG x ^ k
  have hμp : ∀ x, μ x ^ p = 1 := by
    intro x
    dsimp only [μ]
    rw [← pow_mul, mul_comm k p, hpk]
    exact hunitpow _
  have hxq : ∀ x : G, (x : GL ι K) ^ Nat.card K =
      GeneralLinearGroup.scalar ι (μ x) * (x : GL ι K) := by
    intro x
    rw [hq, pow_add, pow_mul, pow_one, lam_spec hp hp2 hG x, ← map_pow]
  let b := D.block D.point
  have htrans : ∀ x : G, E * (x : GL ι K) * E⁻¹ =
      D.scalarBlocks (fun j => if j = b then μ x else 1) * (x : GL ι K) :=
    fun x => hRaw x (μ x) (hxq x)
  have hmax : p ^ (D.numBlocks - 1) * (Nat.card K - 1) ≤ Nat.card D.kernel := by
    rw [hn]
    exact hcard
  have hmem : ∀ x : G, D.scalarBlocks (fun j => if j = b then μ x else 1) ∈ D.kernel := by
    intro x
    apply D.scalarBlocks_mem_kernel hmax
    intro j
    have hj : (if j = b then μ x else 1) ^ p = 1 := by
      split_ifs <;> simp only [hμp, one_pow]
    have hb : (if D.block D.point = b then μ x else 1) ^ p = 1 := by
      split_ifs <;> simp only [hμp, one_pow]
    exact hj.trans hb.symm
  have hLam : lam hp hp2 hG D.primitive = D.scalar := by
    apply scalar_injective (ι := ι) (K := K)
    calc GeneralLinearGroup.scalar ι (lam hp hp2 hG D.primitive) =
        (D.primitive : GL ι K) ^ p := (lam_spec hp hp2 hG D.primitive).symm
      _ = GeneralLinearGroup.scalar ι D.scalar := D.primitive_pow
  have hμne : μ D.primitive ≠ 1 := by
    dsimp only [μ, k]
    rw [hLam]
    exact (D.isPrimitiveRoot_scalar_pow_card_sub_one_div hp hpK).ne_one hp.one_lt
  let E' : SpecialLinearGroup ι K := ⟨(E : Matrix ι ι K), hEdet⟩
  have hE' : SpecialLinearGroup.toGL E' = E := by apply Units.ext; rfl
  refine ⟨E', ?_, ?_, ?_⟩
  · intro x hx
    rw [hE', htrans ⟨x, hx⟩]
    exact G.mul_mem (D.kernel_le (hmem ⟨x, hx⟩)) hx
  · intro x hx
    let z : G := ⟨x, D.kernel_le hx⟩
    obtain ⟨c, hc⟩ := (D.kernel_mem_iff x z.2).mp hx
    have hLamx : lam hp hp2 hG z = c ^ p := by
      apply scalar_injective (ι := ι) (K := K)
      calc GeneralLinearGroup.scalar ι (lam hp hp2 hG z) =
          (z : GL ι K) ^ p := (lam_spec hp hp2 hG z).symm
        _ = GeneralLinearGroup.scalar ι (c ^ p) := hc
    have hμx : μ z = 1 := by
      dsimp only [μ]
      rw [hLamx, ← pow_mul, hpk]
      exact hunitpow c
    rw [hE', htrans z]
    simp only [hμx, ite_self, D.scalarBlocks_const, map_one, one_mul, z]
  · intro u he
    rw [hE', htrans D.primitive] at he
    have hs : D.scalarBlocks (fun j => if j = b then μ D.primitive else 1) =
        GeneralLinearGroup.scalar ι u := mul_right_cancel he
    have hf := D.scalarBlocks_injective
      (show D.scalarBlocks (fun j => if j = b then μ D.primitive else 1) =
        D.scalarBlocks (fun _ => u) by rw [D.scalarBlocks_const]; exact hs)
    let a : Fin D.numBlocks := ⟨if b.val = 0 then 1 else 0, by split_ifs <;> omega⟩
    have hab : a ≠ b := by
      intro h
      have hv := congrArg Fin.val h
      dsimp only [a] at hv
      split_ifs at hv <;> omega
    have hb : μ D.primitive = u := by simpa using congrFun hf b
    have ha : 1 = u := by simpa only [if_neg hab] using congrFun hf a
    exact hμne (hb.trans ha.symm)

end CFSG.StandardType.TypeA.PGLTor
