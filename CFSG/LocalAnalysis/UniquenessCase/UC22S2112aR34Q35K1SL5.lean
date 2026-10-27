module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1M4
import CFSG.Adapters.StatedClassicalOrders
import CFSG.CGT.Stroth77.L4Sylow.EmbedSU
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.CGT.Stroth77.L4Sylow CFSG.LocalAnalysis.Mason73 CFSG.GH74.GLS.Stage1.Thm3.Sec8
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Matrix Equiv

private theorem uc22s2112r34q35_prime_not_dvd_480 {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ 480 := by
  intro hd
  have hfac : 480 = 2 ^ 5 * 3 * 5 := by norm_num
  rw [hfac] at hd
  rcases (Nat.Prime.dvd_mul hs).mp hd with h | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h3
    · have : s = 2 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
      omega
    · have : s = 3 := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp h3
      omega
  · have : s = 5 :=
      (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 5)).mp h5
    omega

private theorem uc22s2112r34q35_prime_not_dvd_5760 {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    ¬ s ∣ 5760 := by
  intro hd
  have hfac : 5760 = 2 ^ 7 * 3 ^ 2 * 5 := by norm_num
  rw [hfac] at hd
  rcases (Nat.Prime.dvd_mul hs).mp hd with h | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h with h2 | h3
    · have : s = 2 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp (hs.dvd_of_dvd_pow h2)
      omega
    · have : s = 3 :=
        (Nat.prime_dvd_prime_iff_eq hs Nat.prime_three).mp (hs.dvd_of_dvd_pow h3)
      omega
  · have : s = 5 :=
      (Nat.prime_dvd_prime_iff_eq hs (by norm_num : Nat.Prime 5)).mp h5
    omega

private theorem uc22s2112r34q35_blk5_eq {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    uc22s2112r34q35_blk5 A c =
      Matrix.reindexAlgEquiv K K finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (Matrix.scalar (Fin 1) c)) := by
  rw [uc22s2112r34q35_blk5, ← Matrix.coe_reindexAlgEquiv K K finSumFinEquiv]

private theorem uc22s2112r34q35_blk5_castAdd {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (i j : Fin 4) :
    uc22s2112r34q35_blk5 A c (Fin.castAdd 1 i) (Fin.castAdd 1 j) = A i j := by
  rw [uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₁₁]

private theorem uc22s2112r34q35_blockDet_castAdd {K : Type} [Field K]
    (A : GL (Fin 4) K) (i j : Fin 4) :
    ((uc22s2112r34q35_blockDet K A : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) (Fin.castAdd 1 i) (Fin.castAdd 1 j) =
      ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j := by
  change uc22s2112r34q35_blk5 ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) (Fin.castAdd 1 i) (Fin.castAdd 1 j) =
    ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j
  rw [uc22s2112r34q35_blk5_castAdd]

private theorem uc22s2112r34q35_blk5_det {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    (uc22s2112r34q35_blk5 A c).det = A.det * c := by
  rw [uc22s2112r34q35_blk5, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.scalar_apply, Matrix.det_diagonal]
  simp

private theorem uc22s2112r34q35_blk5_mul {K : Type} [Field K]
    (A B : Matrix (Fin 4) (Fin 4) K) (c d : K) :
    uc22s2112r34q35_blk5 A c * uc22s2112r34q35_blk5 B d =
      uc22s2112r34q35_blk5 (A * B) (c * d) := by
  rw [uc22s2112r34q35_blk5_eq, uc22s2112r34q35_blk5_eq, uc22s2112r34q35_blk5_eq,
    ← map_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

private theorem uc22s2112r34q35_blk5_map {K : Type} [Field K] (σ : K → K)
    (h0 : σ 0 = 0) (_h1 : σ 1 = 1) (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    (uc22s2112r34q35_blk5 A c).map σ =
      uc22s2112r34q35_blk5 (A.map σ) (σ c) := by
  rw [uc22s2112r34q35_blk5, uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.reindex_apply,
    ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ h0, Matrix.map_zero _ h0]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

private theorem uc22s2112r34q35_blk5_transpose {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    (uc22s2112r34q35_blk5 A c)ᵀ = uc22s2112r34q35_blk5 Aᵀ c := by
  rw [uc22s2112r34q35_blk5, uc22s2112r34q35_blk5, Matrix.transpose_reindex,
    Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_zero]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

private theorem uc22s2112r34q35_blk5_one {K : Type} [Field K] :
    uc22s2112r34q35_blk5 (1 : Matrix (Fin 4) (Fin 4) K) (1 : K) = 1 := by
  rw [uc22s2112r34q35_blk5_eq]
  simp

private theorem uc22s2112r34q35_det_blockDet {K : Type} [Field K]
    (A : GL (Fin 4) K) :
    ((uc22s2112r34q35_blockDet K A : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K).det = 1 := by
  change (uc22s2112r34q35_blk5 ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
    (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K)).det = 1
  rw [uc22s2112r34q35_blk5_det]
  simpa using Units.mul_inv (Matrix.GeneralLinearGroup.det A)

private theorem uc22s2112r34q35_unitary_blockDet {K : Type} [Field K] (D : L4Data K 2)
    (a : L4Hat 2) :
    (((uc22s2112r34q35_blockDet K (D.embed a) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).map (· ^ 3))ᵀ *
      ((uc22s2112r34q35_blockDet K (D.embed a) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = 1 := by
  let A : Matrix (Fin 4) (Fin 4) K := (D.embed a : GL (Fin 4) K)
  let c : K := (((Matrix.GeneralLinearGroup.det (D.embed a))⁻¹ : Kˣ) : K)
  change (((uc22s2112r34q35_blk5 A c).map (· ^ 3))ᵀ * uc22s2112r34q35_blk5 A c) = 1
  have hζ4 : (D.ζ : K) ^ 4 = 1 := by
    have h := pow_orderOf_eq_one D.ζ
    rw [D.orderOf_ζ] at h
    have h' := congrArg (fun u : Kˣ => (u : K)) h
    simpa using h'
  have hdet4 : A.det ^ 4 = 1 := by
    dsimp [A]
    rw [D.det_embed (by norm_num) a, ← pow_mul,
      mul_comm (Multiplicative.toAdd (detL4 2 a)).val 4, pow_mul, hζ4, one_pow]
  have hc4 : c ^ 4 = 1 := by
    have hc : c = A.det⁻¹ := by
      dsimp [c, A]
      rw [Units.val_inv_eq_inv_val]
      rfl
    rw [hc, inv_pow, hdet4, inv_one]
  have hc : c ^ 3 * c = 1 := by
    rw [← pow_succ, show (3 : ℕ) + 1 = 4 by norm_num, hc4]
  have hA : (A.map (· ^ 3))ᵀ * A = 1 := by
    dsimp [A]
    exact D.embed_map_pow_transpose_mul (by norm_num) (by norm_num) a
  rw [uc22s2112r34q35_blk5_map (fun x => x ^ 3) (by norm_num) (by norm_num),
    uc22s2112r34q35_blk5_transpose, uc22s2112r34q35_blk5_mul, hA, hc,
    uc22s2112r34q35_blk5_one]

private theorem uc22s2112r34q35_mem_statedSL_five_blockDet {K : Type} [Field K]
    (D : L4Data K 2) (a : L4Hat 2) :
    uc22s2112r34q35_blockDet K (D.embed a) ∈ StatedSL 5 K :=
  StatedAPI.mem_statedSL_of_det (uc22s2112r34q35_det_blockDet (D.embed a))

private theorem uc22s2112r34q35_mem_statedSU_five_blockDet {K : Type} [Field K]
    (hK : Nat.card K = (3 ^ 1) ^ 2) (D : L4Data K 2) (a : L4Hat 2) :
    uc22s2112r34q35_blockDet K (D.embed a) ∈ StatedSU 5 (3 ^ 1) K := by
  have hset := (CFSG.LinearGroups.unitary_scalar_kernel (p := 3) (f := 1) Nat.prime_three
    hK (n := 5) (by norm_num)).1
  change uc22s2112r34q35_blockDet K (D.embed a) ∈
    (StatedSU 5 (3 ^ 1) K : Set (GL (Fin 5) K))
  rw [hset]
  exact ⟨uc22s2112r34q35_det_blockDet (D.embed a),
    uc22s2112r34q35_unitary_blockDet D a⟩

private theorem uc22s2112r34q35_factorization_statedSL_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) :
    (Nat.card (StatedSL 5 K)).factorization 2 = 11 := by
  have hcard := StatedAPI.card_statedSL_eq_prod (K := K) (d := 5) (by norm_num)
  have hprod : (∏ j ∈ Finset.Icc 2 5, (5 ^ j - 1)) =
      (5 ^ 2 - 1) * (5 ^ 3 - 1) * (5 ^ 4 - 1) * (5 ^ 5 - 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 5),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    simp
  have hform : Nat.card (StatedSL 5 K) = 2 ^ 11 * (5 ^ 10 * 3 * 31 * 39 * 781) := by
    rw [hcard, hK, hprod]
    norm_num
  have hodd : Odd (5 ^ 10 * 3 * 31 * 39 * 781) := by decide
  rw [hform, Nat.factorization_mul (by positivity) hodd.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

private theorem uc22s2112r34q35_card_statedSU_five {K : Type} [Field K] {p f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (StatedSU 5 (p ^ f) K) = (p ^ f) ^ 10 * ((p ^ f) ^ 2 - 1) *
      ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) * ((p ^ f) ^ 5 + 1) := by
  have h : UnitaryFieldData p f K := ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have := h.finite
  have hU := (CFSG.LinearGroups.unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin 5) (Fin 5) K)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun K) (by norm_num)).2.1
  have h1 : (Nat.card (StatedSU 5 (p ^ f) K) : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 10 *
      ∏ i ∈ Finset.Icc 2 5, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
    rw [show StatedSU 5 (p ^ f) K = unitarySU p f K 5 from rfl, unitarySU_eq_gramSU h,
      card_gramSU, hU]
  have hprod : ∏ i ∈ Finset.Icc 2 5, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) =
      (((p ^ f : ℕ) : ℤ) ^ 2 - 1) * (((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1) * (((p ^ f : ℕ) : ℤ) ^ 5 + 1) := by
    rw [Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 5),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 4),
      Finset.prod_Icc_succ_top (by norm_num : 2 ≤ 3)]
    norm_num
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have e2 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
  have e4 : 1 ≤ (p ^ f) ^ 4 := Nat.one_le_pow _ _ hq1
  rw [hprod] at h1
  zify [e2, e4]
  rw [h1]
  norm_num
  ring

private theorem uc22s2112r34q35_factorization_statedSU_five {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ 1) ^ 2) :
    (Nat.card (StatedSU 5 3 K)).factorization 2 = 11 := by
  have hcard := uc22s2112r34q35_card_statedSU_five (K := K) (p := 3) (f := 1)
    Nat.prime_three (by norm_num) hK
  have hcard3 : Nat.card (StatedSU 5 3 K) =
      3 ^ 10 * (3 ^ 2 - 1) * (3 ^ 3 + 1) * (3 ^ 4 - 1) * (3 ^ 5 + 1) := by
    simpa using hcard
  have hform : Nat.card (StatedSU 5 3 K) = 2 ^ 11 * (3 ^ 10 * 7 * 5 * 61) := by
    rw [hcard3]
    norm_num
  have hodd : Odd (3 ^ 10 * 7 * 5 * 61) := by decide
  rw [hform, Nat.factorization_mul (by positivity) hodd.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, add_zero]

theorem uc22s2112r34q35_alpha_psl5_five {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSL 5 5 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  let H := StatedSL 5 K
  let Z := (StatedScalars (Fin 5) K).subgroupOf H
  have hZ : IsPGroup 2 Z := by
    have hZcard : Nat.card Z ∣ Nat.card K - 1 := by
      let f : Z →* StatedScalars (Fin 5) K :=
        { toFun := fun g => ⟨((g : H) : GL (Fin 5) K), g.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun g g' h => by
        have := congrArg (fun z : StatedScalars (Fin 5) K =>
          ((z : GL (Fin 5) K))) h
        exact Subtype.ext (Subtype.ext this)
      have h1 : Nat.card Z ∣ Nat.card (StatedScalars (Fin 5) K) :=
        Subgroup.card_dvd_of_injective f hf
      have h2 : Nat.card (StatedScalars (Fin 5) K) ∣ Nat.card Kˣ :=
        Subgroup.card_range_dvd _
      rw [Nat.card_units] at h2
      exact h1.trans h2
    have h5 : Nat.card K - 1 = 4 := by rw [hK]; norm_num
    exact IsPGroup.of_card_dvd_pow (n := 2) (by
      rw [h5] at hZcard
      simpa using hZcard)
  obtain ⟨D⟩ : Nonempty (L4Data K 2) :=
    exists_l4Data_of_dvd (n := 2) (by rw [hK]; norm_num)
  let φ : L4Hat 2 →* H :=
    ((uc22s2112r34q35_blockDet K).comp D.embed).codRestrict H fun a =>
      uc22s2112r34q35_mem_statedSL_five_blockDet D a
  have hφinj : Function.Injective φ := by
    intro a b h
    have hval := congrArg (fun z : H => ((z : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) h
    have hAB : ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((D.embed b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      have := congrArg (fun M : Matrix (Fin 5) (Fin 5) K =>
        M (Fin.castAdd 1 i) (Fin.castAdd 1 j)) hval
      simpa [φ, uc22s2112r34q35_blockDet_castAdd] using this
    exact D.embed_injective (Units.ext hAB)
  have hK5 : Nat.card K = 5 := by rw [hK]; norm_num
  have hHcard : (Nat.card H).factorization 2 = 11 := by
    dsimp [H]
    exact uc22s2112r34q35_factorization_statedSL_five hK5
  have hcard : Nat.card φ.range = 2 ^ (Nat.card H).factorization 2 := by
    have h1 : Nat.card φ.range = Nat.card (L4Hat 2) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, card_L4Hat, hHcard]
  let S : Sylow 2 H := Sylow.ofCard φ.range hcard
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hS : (S : Subgroup H) = φ.range := Sylow.coe_ofCard _ _
  have hN : ∀ a ∈ (⊤ : Subgroup (L4Hat 2)), ∃ a' ∈ (⊤ : Subgroup (L4Hat 2)),
      (h : GL (Fin 5) K) * uc22s2112r34q35_blockDet K (D.embed a) *
        (h : GL (Fin 5) K)⁻¹ = uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have hφmem : φ a ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨a, rfl⟩
    have hmem : h * φ a * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN (φ a)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, Subgroup.mem_top b, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 5) K))) hb
    simpa [φ] using hb'.symm
  have hN' : ∀ a ∈ (⊤ : Subgroup (L4Hat 2)), ∃ a' ∈ (⊤ : Subgroup (L4Hat 2)),
      (h : GL (Fin 5) K)⁻¹ * uc22s2112r34q35_blockDet K (D.embed a) *
        (h : GL (Fin 5) K) = uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hφmem : φ a ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨a, rfl⟩
    have hmem : h⁻¹ * φ a * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' (φ a)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, Subgroup.mem_top b, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 5) K))) hb
    simpa [φ] using hb'.symm
  have hhGL : (h : GL (Fin 5) K) ^ s = 1 := by
    have := congrArg (fun z : H => ((z : GL (Fin 5) K))) hhs
    simpa using this
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) := by
    let := Fintype.ofFinite K
    have hq5 : Fintype.card K = 5 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    have hcardGL : Nat.card (GL (Fin 2) K) = 480 := by
      rw [Matrix.card_GL_field, hq5, Fin.prod_univ_two]
      norm_num
    rw [hcardGL]
    exact uc22s2112r34q35_prime_not_dvd_480 hs hs7
  have hKnot : ¬ s ∣ Nat.card K - 1 := by
    intro hd
    have h4 : Nat.card K - 1 = 4 := by rw [hK]; norm_num
    rw [h4] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) -
        (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2))) ∨
      ¬ IsConst (pv (π : Perm (Fin 4)) (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) -
        (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2))) := by
    unfold IsConst pv
    decide
  let y₀₁ : L4Hat 2 := hat 0 uc22s2112r34q35_r01
  let y₂₃ : L4Hat 2 := hat 0 uc22s2112r34q35_r23
  let y₀₂ : L4Hat 2 := hat 0 uc22s2112r34q35_r02
  have hy₀₁ : y₀₁ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hy₂₃ : y₂₃ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hy₀₂ : y₀₂ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hz : hat (uc22s2112r34q35_zvec 2) 1 ∈ (⊤ : Subgroup (L4Hat 2)) :=
    Subgroup.mem_top _
  have hc : hat (uc22s2112r34q35_cvec 2) 1 ∈ (⊤ : Subgroup (L4Hat 2)) :=
    Subgroup.mem_top _
  have hgl : (h : GL (Fin 5) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_blockDet_embed (n := 2) (by norm_num) D ⊤ hsep
      (Subgroup.mem_top _) (Subgroup.mem_top _) hy₀₁ hy₂₃ hy₀₂ (by rfl) (by rfl) (by rfl)
      hz hc hs (by omega) hhGL hGL hKnot hN hN'
  exact hh1 (Subtype.ext hgl)

theorem uc22s2112r34q35_alpha_psu5_three {X : Type} [Group X] [Finite X]
    (hX : LieModel X .PSU 5 3 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s) :
    orderOf x ≠ s := by
  intro hxs
  obtain ⟨-, K, hField, hFinite, hK, ⟨eX⟩⟩ :=
    hX.statedClassicalModel_of_ne_zero (by norm_num)
  let := hField
  let := hFinite
  let H := StatedSU 5 (3 ^ 1) K
  let Z := (StatedScalars (Fin 5) K).subgroupOf H
  have hZ : IsPGroup 2 Z := by
    have hZcard : Nat.card Z ∣ Nat.card K - 1 := by
      let f : Z →* StatedScalars (Fin 5) K :=
        { toFun := fun g => ⟨((g : H) : GL (Fin 5) K), g.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hf : Function.Injective f := fun g g' h => by
        have := congrArg (fun z : StatedScalars (Fin 5) K =>
          ((z : GL (Fin 5) K))) h
        exact Subtype.ext (Subtype.ext this)
      have h1 : Nat.card Z ∣ Nat.card (StatedScalars (Fin 5) K) :=
        Subgroup.card_dvd_of_injective f hf
      have h2 : Nat.card (StatedScalars (Fin 5) K) ∣ Nat.card Kˣ :=
        Subgroup.card_range_dvd _
      rw [Nat.card_units] at h2
      exact h1.trans h2
    have h9 : Nat.card K - 1 = 8 := by rw [hK]; norm_num
    exact IsPGroup.of_card_dvd_pow (n := 3) (by
      rw [h9] at hZcard
      simpa using hZcard)
  obtain ⟨D⟩ : Nonempty (L4Data K 2) :=
    exists_l4Data_of_card_eq_sq (n := 2) (q := 3) hK (by norm_num)
  let φ : L4Hat 2 →* H :=
    ((uc22s2112r34q35_blockDet K).comp D.embed).codRestrict H fun a =>
      uc22s2112r34q35_mem_statedSU_five_blockDet hK D a
  have hφinj : Function.Injective φ := by
    intro a b h
    have hval := congrArg (fun z : H => ((z : GL (Fin 5) K) :
      Matrix (Fin 5) (Fin 5) K)) h
    have hAB : ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((D.embed b : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      ext i j
      have := congrArg (fun M : Matrix (Fin 5) (Fin 5) K =>
        M (Fin.castAdd 1 i) (Fin.castAdd 1 j)) hval
      simpa [φ, uc22s2112r34q35_blockDet_castAdd] using this
    exact D.embed_injective (Units.ext hAB)
  have hHcard : (Nat.card H).factorization 2 = 11 := by
    dsimp [H]
    exact uc22s2112r34q35_factorization_statedSU_five hK
  have hcard : Nat.card φ.range = 2 ^ (Nat.card H).factorization 2 := by
    have h1 : Nat.card φ.range = Nat.card (L4Hat 2) :=
      (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
    rw [h1, card_L4Hat, hHcard]
  let S : Sylow 2 H := Sylow.ofCard φ.range hcard
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hS : (S : Subgroup H) = φ.range := Sylow.coe_ofCard _ _
  have hN : ∀ a ∈ (⊤ : Subgroup (L4Hat 2)), ∃ a' ∈ (⊤ : Subgroup (L4Hat 2)),
      (h : GL (Fin 5) K) * uc22s2112r34q35_blockDet K (D.embed a) *
        (h : GL (Fin 5) K)⁻¹ = uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have hφmem : φ a ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨a, rfl⟩
    have hmem : h * φ a * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN (φ a)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, Subgroup.mem_top b, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 5) K))) hb
    simpa [φ] using hb'.symm
  have hN' : ∀ a ∈ (⊤ : Subgroup (L4Hat 2)), ∃ a' ∈ (⊤ : Subgroup (L4Hat 2)),
      (h : GL (Fin 5) K)⁻¹ * uc22s2112r34q35_blockDet K (D.embed a) *
        (h : GL (Fin 5) K) = uc22s2112r34q35_blockDet K (D.embed a') := by
    intro a ha
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hφmem : φ a ∈ (S : Subgroup H) := by
      rw [hS]
      exact ⟨a, rfl⟩
    have hmem : h⁻¹ * φ a * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' (φ a)).mp hφmem
    rw [hS] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, Subgroup.mem_top b, ?_⟩
    have hb' := congrArg (fun z : H => ((z : GL (Fin 5) K))) hb
    simpa [φ] using hb'.symm
  have hhGL : (h : GL (Fin 5) K) ^ s = 1 := by
    have := congrArg (fun z : H => ((z : GL (Fin 5) K))) hhs
    simpa using this
  have hGL : ¬ s ∣ Nat.card (GL (Fin 2) K) := by
    let := Fintype.ofFinite K
    have hq9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]; norm_num
    have hcardGL : Nat.card (GL (Fin 2) K) = 5760 := by
      rw [Matrix.card_GL_field, hq9, Fin.prod_univ_two]
      norm_num
    rw [hcardGL]
    exact uc22s2112r34q35_prime_not_dvd_5760 hs hs7
  have hKnot : ¬ s ∣ Nat.card K - 1 := by
    intro hd
    have h8 : Nat.card K - 1 = 8 := by rw [hK]; norm_num
    rw [h8] at hd
    have h2 : s = 2 :=
      (Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp
        (hs.dvd_of_dvd_pow (n := 3) (by simpa using hd))
    omega
  have hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2)) -
        (![1, 3, 0, 0] : Fin 4 → ZMod (2 ^ 2))) ∨
      ¬ IsConst (pv (π : Perm (Fin 4)) (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2)) -
        (![0, 0, 1, 3] : Fin 4 → ZMod (2 ^ 2))) := by
    unfold IsConst pv
    decide
  let y₀₁ : L4Hat 2 := hat 0 uc22s2112r34q35_r01
  let y₂₃ : L4Hat 2 := hat 0 uc22s2112r34q35_r23
  let y₀₂ : L4Hat 2 := hat 0 uc22s2112r34q35_r02
  have hy₀₁ : y₀₁ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hy₂₃ : y₂₃ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hy₀₂ : y₀₂ ∈ (⊤ : Subgroup (L4Hat 2)) := Subgroup.mem_top _
  have hz : hat (uc22s2112r34q35_zvec 2) 1 ∈ (⊤ : Subgroup (L4Hat 2)) :=
    Subgroup.mem_top _
  have hc : hat (uc22s2112r34q35_cvec 2) 1 ∈ (⊤ : Subgroup (L4Hat 2)) :=
    Subgroup.mem_top _
  have hgl : (h : GL (Fin 5) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_blockDet_embed (n := 2) (by norm_num) D ⊤ hsep
      (Subgroup.mem_top _) (Subgroup.mem_top _) hy₀₁ hy₂₃ hy₀₂ (by rfl) (by rfl) (by rfl)
      hz hc hs (by omega) hhGL hGL hKnot hN hN'
  exact hh1 (Subtype.ext hgl)

end CFSG.LocalAnalysis.UniquenessCase.UC22
