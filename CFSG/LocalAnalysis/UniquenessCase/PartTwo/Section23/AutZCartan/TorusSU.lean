module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.LineTorus
public import CFSG.Open.StatedDefs
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open Matrix

variable {K : Type} [Field K]

private theorem exists_pow_two_eq [Finite K] [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    ∃ a : ℕ, q = 2 ^ a := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨p, hpchar, n, hprime, hcard⟩ := FiniteField.card' K
  have hp2 : p = 2 := CharP.eq K hpchar ‹CharP K 2›
  subst hp2
  have hdvd : q ∣ 2 ^ (n : ℕ) := by
    rw [← hcard, ← Nat.card_eq_fintype_card, hK]
    exact ⟨q, by ring⟩
  obtain ⟨a, -, hq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  exact ⟨a, hq⟩

private theorem exists_add_pow_eq_one [Finite K] [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a)
    (hK : Nat.card K = q ^ 2) : ∃ s : K, s ^ q + s = 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ≤ q := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    rw [hK] at h1
    nlinarith
  have hq1 : ¬ (1 = q) := by omega
  have hf : (Polynomial.X ^ q + Polynomial.X : Polynomial K) ≠ 0 := by
    intro h
    have hc := congrArg (fun p : Polynomial K => p.coeff q) h
    rw [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_zero,
      if_pos rfl, if_neg hq1, add_zero] at hc
    exact one_ne_zero hc
  have hdeg : ((Polynomial.X ^ q + Polynomial.X : Polynomial K).natDegree : Cardinal) <
      Cardinal.mk K := by
    have hle : (Polynomial.X ^ q + Polynomial.X : Polynomial K).natDegree ≤ q := by
      refine (Polynomial.natDegree_add_le _ _).trans ?_
      rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      omega
    have hcard : Cardinal.mk K = (q : Cardinal) ^ 2 := by
      rw [← Nat.cast_card, hK, Nat.cast_pow]
    rw [hcard]
    calc ((Polynomial.X ^ q + Polynomial.X : Polynomial K).natDegree : Cardinal) ≤
          (q : Cardinal) := by exact_mod_cast hle
      _ < (q : Cardinal) ^ 2 := by
          rw [← Nat.cast_pow, Nat.cast_lt]
          nlinarith
  obtain ⟨r, hr⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card _ hf hdeg
  have hr' : r ^ q + r ≠ 0 := by
    simpa [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X] using hr
  have hφ : ∀ x : K, iterateFrobenius K 2 a x = x ^ q := fun x => by
    rw [iterateFrobenius_def, hq]
  have hpow : ∀ x : K, x ^ (q * q) = x := fun x => by
    rw [show q * q = Nat.card K by rw [hK]; ring, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  set t0 : K := r ^ q + r with ht0
  have ht0ne : t0 ≠ 0 := by rw [ht0]; exact hr'
  have h3 : (r ^ q) ^ q = r := by rw [← pow_mul, hpow r]
  have ht0q : t0 ^ q = t0 := by
    rw [← hφ t0, ht0, map_add, map_pow, hφ, h3, add_comm]
  refine ⟨r / t0, ?_⟩
  have h1 : (r / t0) ^ q = r ^ q / t0 := by rw [div_pow, ht0q]
  rw [h1, ← add_div]
  exact div_self ht0ne

private theorem frob_eq_pow [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) (x : K) :
    iterateFrobenius K 2 a x = x ^ q := by
  rw [iterateFrobenius_def, hq]

private theorem frob_one_add [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s : K}
    (hs : s ^ q + s = 1) : iterateFrobenius K 2 a (1 + s) = s := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hsq : s ^ q = 1 + s := by linear_combination hs - s * h2
  rw [map_add, map_one, frob_eq_pow hq, hsq]
  linear_combination h2

private theorem frob_s [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s : K}
    (hs : s ^ q + s = 1) : iterateFrobenius K 2 a s = 1 + s := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  rw [frob_eq_pow hq]
  linear_combination hs - s * h2

private def hp (s : K) : Matrix (Fin 2) (Fin 2) K := !![1, 1 + s; 1, s]

private def hpInv (s : K) : Matrix (Fin 2) (Fin 2) K := !![s, 1 + s; 1, 1]

private def hJ : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

private def hD (T T' : K) : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![T, T']

private theorem hp_mul_hpInv [CharP K 2] (s : K) : hp s * hpInv s = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hp, hpInv, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two] <;>
    (try ring_nf) <;> simp [h2]

private theorem hJ_mul_hJ : (hJ : Matrix (Fin 2) (Fin 2) K) * hJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hJ, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two]

private theorem hp_frob_transpose [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s : K}
    (hs : s ^ q + s = 1) :
    ((hp s).map (⇑(iterateFrobenius K 2 a)))ᵀ * hp s = hJ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hp, hJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_two,
      frob_one_add hq hs, frob_s hq hs] <;>
    (try ring_nf) <;> simp [h2]

private theorem hpInv_frob_transpose [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s : K}
    (hs : s ^ q + s = 1) :
    ((hpInv s).map (⇑(iterateFrobenius K 2 a)))ᵀ = hp s * hJ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hp, hpInv, hJ, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
      Fin.sum_univ_two, frob_one_add hq hs, frob_s hq hs] <;>
    (try ring_nf) <;> simp [h2]

private theorem hD_frob [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) (T T' : K) :
    (hD T T').map (⇑(iterateFrobenius K 2 a)) = hD (T ^ q) (T' ^ q) := by
  simp only [hD]
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  fin_cases i <;> simp [frob_eq_pow hq]

private theorem hD_J [CharP K 2] {q : ℕ} {T T' : K} (h1 : T ^ q * T' = 1)
    (h2 : T' ^ q * T = 1) :
    (hD (T ^ q) (T' ^ q)).transpose * hJ * hD T T' = hJ := by
  simp only [hD, Matrix.diagonal_transpose]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hJ, Matrix.diagonal_mul, Matrix.mul_diagonal, h1, h2]

private def block (q : ℕ) (s T T' : K) : Matrix (Fin 2) (Fin 2) K := hp s * hD T T' * hpInv s

private theorem block_det [CharP K 2] (q : ℕ) (s T T' : K) :
    (block q s T T').det = T * T' := by
  have hdetP : (hp s).det * (hpInv s).det = 1 := by
    rw [← Matrix.det_mul, hp_mul_hpInv, Matrix.det_one]
  have hdetD : (hD T T').det = T * T' := by
    simp [hD, Matrix.det_diagonal, Fin.prod_univ_two]
  rw [block, Matrix.det_mul, Matrix.det_mul, hdetD]
  calc (hp s).det * (T * T') * (hpInv s).det
      = ((hp s).det * (hpInv s).det) * (T * T') := by ring
    _ = T * T' := by rw [hdetP, one_mul]

private theorem block_mulVec [CharP K 2] (q : ℕ) (s T T' : K) :
    block q s T T' *ᵥ ![1, 1] = T • ![1, 1] := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h1 : hpInv s *ᵥ ![1, 1] = ![1, 0] := by
    ext i
    fin_cases i <;> simp [hpInv, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
      (try ring_nf) <;> simp [h2]
  have h2v : hD T T' *ᵥ ![1, 0] = ![T, 0] := by
    ext i
    fin_cases i <;>
      simp [hD, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Fin.sum_univ_two]
  have h3 : hp s *ᵥ ![T, 0] = T • ![1, 1] := by
    ext i
    fin_cases i <;> simp [hp, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [block, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2v, h3]

private theorem block_iso [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s T T' : K}
    (hs : s ^ q + s = 1) (h1 : T ^ q * T' = 1) (h2 : T' ^ q * T = 1) :
    ((block q s T T').map (⇑(iterateFrobenius K 2 a)))ᵀ * block q s T T' = 1 := by
  have hPJ := hp_frob_transpose hq hs
  have hPin := hpInv_frob_transpose hq hs
  have hDJ := hD_J h1 h2
  have hJJ := hJ_mul_hJ (K := K)
  have hPQ := hp_mul_hpInv s
  have hmap : (block q s T T').map (⇑(iterateFrobenius K 2 a)) =
      (hp s).map (⇑(iterateFrobenius K 2 a)) * hD (T ^ q) (T' ^ q) *
        (hpInv s).map (⇑(iterateFrobenius K 2 a)) := by
    rw [block, Matrix.map_mul, Matrix.map_mul, hD_frob hq]
  rw [hmap, Matrix.transpose_mul, Matrix.transpose_mul]
  calc ((hpInv s).map ⇑(iterateFrobenius K 2 a))ᵀ *
        ((hD (T ^ q) (T' ^ q))ᵀ * ((hp s).map ⇑(iterateFrobenius K 2 a))ᵀ) *
        (hp s * hD T T' * hpInv s)
      = (((hpInv s).map ⇑(iterateFrobenius K 2 a))ᵀ * (hD (T ^ q) (T' ^ q))ᵀ) *
          (((hp s).map ⇑(iterateFrobenius K 2 a))ᵀ * hp s) *
          (hD T T' * hpInv s) := by noncomm_ring
    _ = (((hpInv s).map ⇑(iterateFrobenius K 2 a))ᵀ * (hD (T ^ q) (T' ^ q))ᵀ) * hJ *
          (hD T T' * hpInv s) := by rw [hPJ]
    _ = ((hpInv s).map ⇑(iterateFrobenius K 2 a))ᵀ *
          ((hD (T ^ q) (T' ^ q))ᵀ * hJ * hD T T') * hpInv s := by noncomm_ring
    _ = ((hpInv s).map ⇑(iterateFrobenius K 2 a))ᵀ * hJ * hpInv s := by rw [hDJ]
    _ = (hp s * hJ) * hJ * hpInv s := by rw [hPin]
    _ = hp s * (hJ * hJ) * hpInv s := by noncomm_ring
    _ = hp s * 1 * hpInv s := by rw [hJJ]
    _ = 1 := by rw [Matrix.mul_one, hPQ]

private def e0 : Fin 4 → K := Pi.single 0 1 + Pi.single 1 1

private def gammaBlocks (q : ℕ) (s : K) (t : Kˣ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  Matrix.fromBlocks (block q s (t : K) ((t : K) ^ q)⁻¹) 0 0
    (block q s ((t : K)⁻¹) (((t : K)⁻¹) ^ q)⁻¹)

private def gamma (q : ℕ) (s : K) (t : Kˣ) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (gammaBlocks q s t)

private theorem gamma_det [CharP K 2] (q : ℕ) (s : K) (t : Kˣ) :
    (gamma q s t).det = 1 := by
  have ht : (t : K) ≠ 0 := Units.ne_zero t
  have hinv : (((t : K)⁻¹) ^ q)⁻¹ = (t : K) ^ q := by rw [inv_pow, inv_inv]
  rw [gamma, Matrix.det_reindex_self, gammaBlocks, Matrix.det_fromBlocks_zero₁₂,
    block_det, block_det, hinv]
  field_simp

private theorem gamma_iso [CharP K 2] {q a : ℕ} (hq : q = 2 ^ a) {s : K}
    (hs : s ^ q + s = 1) (t : Kˣ) (hpow : ∀ x : K, x ^ (q * q) = x) :
    ((gamma q s t).map (⇑(iterateFrobenius K 2 a)))ᵀ * gamma q s t = 1 := by
  have ht : (t : K) ≠ 0 := Units.ne_zero t
  have h1a : (t : K) ^ q * ((t : K) ^ q)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero q ht)
  have h2a : (((t : K) ^ q)⁻¹) ^ q * (t : K) = 1 := by
    rw [inv_pow, ← pow_mul, hpow, inv_mul_cancel₀ ht]
  have h1b : ((t : K)⁻¹) ^ q * (((t : K)⁻¹) ^ q)⁻¹ = 1 :=
    mul_inv_cancel₀ (pow_ne_zero q (inv_ne_zero ht))
  have hx : ((((t : K)⁻¹) ^ q)⁻¹) ^ q = (t : K) := by
    rw [inv_pow, ← pow_mul, hpow, inv_inv]
  have h2b : ((((t : K)⁻¹) ^ q)⁻¹) ^ q * (t : K)⁻¹ = 1 := by
    rw [hx, mul_inv_cancel₀ ht]
  have hgam : gamma q s t = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (block q s (t : K) ((t : K) ^ q)⁻¹) 0 0
        (block q s ((t : K)⁻¹) (((t : K)⁻¹) ^ q)⁻¹)) := rfl
  have hmap : (gamma q s t).map (⇑(iterateFrobenius K 2 a)) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks ((block q s (t : K) ((t : K) ^ q)⁻¹).map
          (⇑(iterateFrobenius K 2 a))) 0 0
          ((block q s ((t : K)⁻¹) (((t : K)⁻¹) ^ q)⁻¹).map
            (⇑(iterateFrobenius K 2 a)))) := by
    rw [hgam, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map,
      Matrix.fromBlocks_map]
    simp
  rw [hmap, hgam, Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [block_iso hq hs h1a h2a, block_iso hq hs h1b h2b]
  rw [show (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) K) 0 0 1) =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) from by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply]]
  exact Matrix.submatrix_one_equiv finSumFinEquiv.symm

private theorem gamma_mulVec [CharP K 2] (q : ℕ) (s : K) (t : Kˣ) :
    gamma q s t *ᵥ e0 = (t : K) • e0 := by
  have hsum0 : finSumFinEquiv (m := 2) (n := 2) (Sum.inl (0 : Fin 2)) = (0 : Fin 4) := rfl
  have hsum1 : finSumFinEquiv (m := 2) (n := 2) (Sum.inl (1 : Fin 2)) = (1 : Fin 4) := rfl
  have hsum2 : finSumFinEquiv (m := 2) (n := 2) (Sum.inr (0 : Fin 2)) = (2 : Fin 4) := rfl
  have hsum3 : finSumFinEquiv (m := 2) (n := 2) (Sum.inr (1 : Fin 2)) = (3 : Fin 4) := rfl
  have hw : e0 ∘ ⇑(finSumFinEquiv (m := 2) (n := 2)) =
      Sum.elim (![1, 1] : Fin 2 → K) (fun _ => 0) := by
    funext k
    rcases k with i | i <;> fin_cases i <;>
      simp [hsum0, hsum1, hsum2, hsum3, e0, Pi.single_apply]
  have hinl : ((Sum.elim (![1, 1] : Fin 2 → K) (fun _ => 0)) ∘
      (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)) = ![1, 1] := by
    funext i; rfl
  have hinr : ((Sum.elim (![1, 1] : Fin 2 → K) (fun _ => 0)) ∘
      (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)) = (fun _ : Fin 2 => 0) := by
    funext i; rfl
  have hMw : gammaBlocks q s t *ᵥ Sum.elim (![1, 1] : Fin 2 → K) (fun _ => 0) =
      Sum.elim ((t : K) • ![1, 1]) (fun _ => 0) := by
    rw [gammaBlocks, Matrix.fromBlocks_mulVec, hinl, hinr, block_mulVec]
    ext k
    rcases k with i | i <;> fin_cases i <;> simp
  rw [gamma, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
  simp only [Equiv.symm_symm]
  rw [hw, hMw]
  funext i
  obtain ⟨k, rfl⟩ := (finSumFinEquiv (m := 2) (n := 2)).surjective i
  simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rcases k with j | j <;> fin_cases j <;>
    simp [hsum0, hsum1, hsum2, hsum3, e0, Pi.single_apply]

theorem lineTorus_statedSU_four [Finite K] [CharP K 2] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    LineTorus (StatedSU 4 q K) (Pi.single 0 1 + Pi.single 1 1 : Fin 4 → K) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨a, hq⟩ := exists_pow_two_eq hK
  obtain ⟨s, hs⟩ := exists_add_pow_eq_one hq hK
  have hpow : ∀ x : K, x ^ (q * q) = x := fun x => by
    rw [show q * q = Nat.card K by rw [hK]; ring, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  have hfun : (fun x : K => x ^ q) = ⇑(iterateFrobenius K 2 a) := by
    funext x; exact (frob_eq_pow hq x).symm
  intro c
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (gamma q s c) ?_, ?_, ?_⟩
  · rw [gamma_det]; exact one_ne_zero
  · unfold StatedSU
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, gamma_det]
    · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hfun]
      exact gamma_iso hq hs c hpow
  · rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact gamma_mulVec q s c

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
