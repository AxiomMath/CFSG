module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Pred
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8Out
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverR119

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.RankThree.GF2n.Stroth80 Matrix
open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] {n : ℕ}

private theorem s16k_prod_update₂ {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι}
    (hij : i ≠ j) (c d : K) :
    ∏ k, Function.update (Function.update (1 : ι → K) i c) j d k = c * d := by
  classical
  rw [Finset.prod_update_of_mem (s := Finset.univ) (i := j)
    (f := Function.update (1 : ι → K) i c) (b := d) (Finset.mem_univ j)]
  rw [Finset.prod_update_of_mem (s := Finset.univ \ {j}) (i := i)
    (f := (1 : ι → K)) (b := c) (by simpa using hij)]
  simp [mul_comm]

private noncomputable def s16k_diagGL (d : Fin n → K) (hd : ∀ i, d i ≠ 0) : GL (Fin n) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d)
    (by rw [Matrix.det_diagonal]; exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i)

private theorem s16k_diagGL_val (d : Fin n → K) (hd : ∀ i, d i ≠ 0) :
    ((s16k_diagGL d hd : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem s16k_pow_three_eq_one (hK : Nat.card K = 4) (x : K) (hx : x ≠ 0) :
    x ^ 3 = 1 := by
  letI : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card_sub_one_eq_one x hx
  rw [← Nat.card_eq_fintype_card, hK] at h
  simpa using h

private theorem s16k_single_eq_smul (i : Fin n) (x : K) :
    (Pi.single i x : Fin n → K) = x • (Pi.single i (1 : K) : Fin n → K) := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

private theorem s16k_diagGL_mem_statedSU (hK : Nat.card K = 4) (d : Fin n → K)
    (hd : ∀ i, d i ≠ 0) (hd3 : ∀ i, d i ^ 3 = 1) (hprod : ∏ i, d i = 1) :
    s16k_diagGL d hd ∈ StatedSU n 2 K := by
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · rw [s16k_diagGL_val, Matrix.det_diagonal]; exact hprod
  · rw [s16k_diagGL_val, Matrix.diagonal_map (by norm_num), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal]
    have hfun : (fun i => d i ^ 2 * d i) = fun _ => (1 : K) := by
      funext i
      rw [← pow_succ, hd3 i]
    rw [hfun, Matrix.diagonal_one]

private theorem s16k_transvection_swap (hK : Nat.card K = 4) {i j : Fin n} (hij : i ≠ j) :
    ∃ A ∈ StatedSU n 2 K,
      (A : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i (1 : K) = Pi.single j (1 : K) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nonempty (Fin n) := ⟨i⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  let x : Fin n → K := Pi.single i (1 : K) + Pi.single j (1 : K)
  have hx : (unitaryForm 2 1 hF n).β x x = 0 := by
    change herm (unitaryInvolution K 2 1) x x = 0
    dsimp only [x]
    rw [herm_add_left, herm_add_right, herm_add_right]
    rw [herm_single_left, herm_single_left, herm_single_left, herm_single_left]
    rw [map_one, one_mul]
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij 1, Pi.single_eq_of_ne (Ne.symm hij) 1,
      Pi.single_eq_same]
    simp [CharTwo.add_self_eq_zero]
  have hc : unitaryInvolution K 2 1 (1 : K) = -(1 : K) := by
    rw [unitaryInvolution_apply, CharTwo.neg_eq]
    norm_num
  obtain ⟨A, hA, hAact⟩ := exists_mem_statedSU_transvection (p := 2) (f := 1) hF hx hc
  refine ⟨A, hA, ?_⟩
  have hxi : (unitaryForm 2 1 hF n).β x (Pi.single i (1 : K)) = 1 := by
    change herm (unitaryInvolution K 2 1) x (Pi.single i (1 : K)) = 1
    dsimp only [x]
    rw [herm_add_left, herm_single_left, herm_single_left, Pi.single_eq_same,
      Pi.single_eq_of_ne (Ne.symm hij) 1, map_one, mul_one, mul_zero, add_zero]
  rw [hAact, hxi, mul_one, one_smul]
  dsimp only [x]
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

theorem s16k_addCommutantScalar_statedSU {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n) : AddCommutantScalar (StatedSU n 2 K) := by
  intro f hf
  classical
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcu : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  have hgord : orderOf g = 3 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcu]
  set ω : K := (g : K) with hωdef
  have hω3 : ω ^ 3 = 1 := by
    rw [hωdef, ← Units.val_pow_eq_pow_val, ← hgord, pow_orderOf_eq_one, Units.val_one]
  have hω0 : ω ≠ 0 := by rw [hωdef]; exact g.ne_zero
  have hω1 : ω ≠ 1 := by
    intro h
    have h1 : g = 1 := Units.ext (by rw [← hωdef]; exact h)
    rw [h1, orderOf_one] at hgord
    omega
  have hthird : ∀ i j : Fin n, ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
    intro i j
    have hs : ({i, j} : Finset (Fin n)).card ≤ 2 := by
      have := Finset.card_insert_le i ({j} : Finset (Fin n))
      simpa using this
    have ht : ({i, j} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      rw [Finset.card_univ, Fintype.card_fin]; omega
    obtain ⟨k, _, hk⟩ := Finset.exists_mem_notMem_of_card_lt_card ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact ⟨k, hk.1, hk.2⟩
  have hoff : ∀ i j : Fin n, j ≠ i → (f (Pi.single i (1 : K))) j = 0 := by
    intro i j hji
    obtain ⟨k, hki, hkj⟩ := hthird i j
    have hjk : j ≠ k := fun h => hkj h.symm
    let d : Fin n → K := Function.update (Function.update (1 : Fin n → K) j ω) k ω⁻¹
    have hdj : d j = ω := by
      dsimp only [d]
      rw [Function.update_apply, if_neg hjk, Function.update_apply, if_pos rfl]
    have hdi : d i = 1 := by
      dsimp only [d]
      rw [Function.update_apply, if_neg (Ne.symm hki), Function.update_apply,
        if_neg (Ne.symm hji)]
      rfl
    have hd0 : ∀ m, d m ≠ 0 := by
      intro m
      dsimp only [d]
      rw [Function.update_apply, Function.update_apply]
      split_ifs with hmk hmj
      · exact inv_ne_zero hω0
      · exact hω0
      · exact one_ne_zero
    have hd3 : ∀ m, d m ^ 3 = 1 := by
      intro m
      dsimp only [d]
      rw [Function.update_apply, Function.update_apply]
      split_ifs with hmk hmj
      · rw [inv_pow, hω3, inv_one]
      · exact hω3
      · simp
    have hprod : ∏ m, d m = 1 := by
      dsimp only [d]
      rw [s16k_prod_update₂ hjk ω ω⁻¹, mul_inv_cancel₀ hω0]
    have hDmem : s16k_diagGL d hd0 ∈ StatedSU n 2 K :=
      s16k_diagGL_mem_statedSU hK d hd0 hd3 hprod
    have hact : ((s16k_diagGL d hd0 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
        Pi.single i (1 : K) = Pi.single i (1 : K) := by
      rw [s16k_diagGL_val, Matrix.diagonal_mulVec_single, hdi, one_mul]
    have h := hf _ hDmem (Pi.single i (1 : K))
    rw [hact] at h
    have hj := congrFun h j
    rw [s16k_diagGL_val, Matrix.mulVec_diagonal, hdj] at hj
    have hzero : (1 - ω) * (f (Pi.single i (1 : K))) j = 0 := by
      rw [sub_mul, one_mul]
      exact sub_eq_zero.mpr hj
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr (Ne.symm hω1))
  have hdiag : ∀ i : Fin n,
      f (Pi.single i (1 : K)) = (f (Pi.single i (1 : K))) i • Pi.single i (1 : K) := by
    intro i
    ext j
    by_cases hji : j = i
    · subst hji; simp
    · rw [hoff i j hji]
      simp [Pi.single_eq_of_ne hji]
  have hconst : ∀ i j : Fin n, i ≠ j →
      (f (Pi.single i (1 : K))) i = (f (Pi.single j (1 : K))) j := by
    intro i j hij
    obtain ⟨A, hA, hAact⟩ := s16k_transvection_swap (K := K) hK hij
    have h := hf A hA (Pi.single i (1 : K))
    rw [hAact] at h
    rw [hdiag i] at h
    rw [Matrix.mulVec_smul, hAact, hdiag j] at h
    have hj := congrFun h j
    simpa [Pi.smul_apply, Pi.single_eq_same] using hj.symm
  have hhom : ∀ (i : Fin n) (x : K),
      f (x • Pi.single i (1 : K)) = x • f (Pi.single i (1 : K)) := by
    intro i x
    by_cases hx : x = 0
    · rw [hx, zero_smul, map_zero, zero_smul]
    · have hn1 : 1 < Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
      obtain ⟨k, hk⟩ := Fintype.exists_ne_of_one_lt_card hn1 i
      have hik : i ≠ k := fun h => hk h.symm
      let d : Fin n → K := Function.update (Function.update (1 : Fin n → K) i x) k x⁻¹
      have hdi : d i = x := by
        dsimp only [d]
        rw [Function.update_apply, if_neg hik, Function.update_apply, if_pos rfl]
      have hd0 : ∀ m, d m ≠ 0 := by
        intro m
        dsimp only [d]
        rw [Function.update_apply, Function.update_apply]
        split_ifs with hmk hmi
        · exact inv_ne_zero hx
        · exact hx
        · exact one_ne_zero
      have hd3 : ∀ m, d m ^ 3 = 1 := by
        intro m
        dsimp only [d]
        rw [Function.update_apply, Function.update_apply]
        split_ifs with hmk hmi
        · rw [inv_pow, s16k_pow_three_eq_one hK x hx, inv_one]
        · exact s16k_pow_three_eq_one hK x hx
        · simp
      have hprod : ∏ m, d m = 1 := by
        dsimp only [d]
        rw [s16k_prod_update₂ hik x x⁻¹, mul_inv_cancel₀ hx]
      have hDmem : s16k_diagGL d hd0 ∈ StatedSU n 2 K :=
        s16k_diagGL_mem_statedSU hK d hd0 hd3 hprod
      have hact : ((s16k_diagGL d hd0 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ
          Pi.single i (1 : K) = x • Pi.single i (1 : K) := by
        rw [s16k_diagGL_val, Matrix.diagonal_mulVec_single, hdi, mul_one]
        exact s16k_single_eq_smul i x
      have h := hf _ hDmem (Pi.single i (1 : K))
      rw [hact] at h
      rw [h]
      let ci : K := (f (Pi.single i (1 : K))) i
      have hci : f (Pi.single i (1 : K)) = ci • Pi.single i (1 : K) := hdiag i
      rw [s16k_diagGL_val, hci, Matrix.mulVec_smul, Matrix.diagonal_mulVec_single, hdi,
        mul_one]
      rw [s16k_single_eq_smul i x]
      rw [smul_smul, smul_smul, mul_comm]
  let i0 : Fin n := ⟨0, by omega⟩
  set c : K := (f (Pi.single i0 (1 : K))) i0 with hcdef
  have hceq : ∀ i : Fin n, (f (Pi.single i (1 : K))) i = c := by
    intro i
    by_cases hi : i = i0
    · subst hi; rw [hcdef]
    · exact hconst i i0 hi
  refine ⟨c, fun v => ?_⟩
  have hv : v = ∑ i, v i • Pi.single i (1 : K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hhom i (v i), hdiag i, hceq i, smul_smul, smul_smul, mul_comm (v i) c]

private theorem s16k_conjTr_mem_statedSU {σ : K ≃+* K} (hσ : ∀ x : K, σ x = x ^ 2)
    {A : GL (Fin n) K} (hA : A ∈ StatedSU n 2 K) :
    conjTr σ (A : Matrix (Fin n) (Fin n) K) * (A : Matrix (Fin n) (Fin n) K) = 1 := by
  have hle : StatedSU n 2 K ≤ SUid σ n := by
    rw [StatedSU, Subgroup.closure_le]
    intro B hB
    change B ∈ SUid σ n
    rw [mem_SUid]
    refine ⟨hB.1, ?_⟩
    rw [conjTr]
    have hmap : (↑B : Matrix (Fin n) (Fin n) K).map ⇑σ =
        (↑B : Matrix (Fin n) (Fin n) K).map (fun x => x ^ 2) := by
      ext i j
      simp only [Matrix.map_apply, hσ]
    rw [hmap]
    exact hB.2
  exact (mem_SUid.mp (hle hA)).2

theorem s16k_normalizer_statedSU_unitary {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 3 ≤ n) {g : Matrix.GeneralLinearGroup (Fin n) K}
    (hg : g ∈ Subgroup.normalizer (StatedSU n 2 K : Set (Matrix.GeneralLinearGroup (Fin n) K))) :
    ((g : Matrix (Fin n) (Fin n) K).map (fun x => x ^ 2))ᵀ *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
      rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  have hσsq : ∀ x : K, unitaryInvolution K 2 1 x = x ^ 2 := by
    intro x; rw [unitaryInvolution_apply]; norm_num
  have hσ2 : ∀ x : K, unitaryInvolution K 2 1 (unitaryInvolution K 2 1 x) = x :=
    unitaryInvolution_involutive (p := 2) (f := 1) hF
  let i0 : Fin n := ⟨0, by omega⟩
  set G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hG
  set Ginv : Matrix (Fin n) (Fin n) K := ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hGinv
  have hGGinv : G * Ginv = 1 := by
    rw [hGinv, hG, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have hGinvG : Ginv * G = 1 := by
    rw [hGinv, hG, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  set S : Matrix (Fin n) (Fin n) K := conjTr (unitaryInvolution K 2 1) G with hS
  set Si : Matrix (Fin n) (Fin n) K := conjTr (unitaryInvolution K 2 1) Ginv with hSi
  have hSSi : S * Si = 1 := by
    rw [hS, hSi, ← conjTr_mul, hGinvG, conjTr_one]
  set H : Matrix (Fin n) (Fin n) K := S * G with hH
  have hHA : ∀ A ∈ StatedSU n 2 K,
      H * (A : Matrix (Fin n) (Fin n) K) = (A : Matrix (Fin n) (Fin n) K) * H := by
    intro A hA
    set Am : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hAm
    have hAconj : conjTr (unitaryInvolution K 2 1) Am * Am = 1 := by
      rw [hAm]; exact s16k_conjTr_mem_statedSU hσsq hA
    have hAconj' : Am * conjTr (unitaryInvolution K 2 1) Am = 1 := by
      have h1 : conjTr (unitaryInvolution K 2 1) Am = Am⁻¹ :=
        (Matrix.inv_eq_left_inv hAconj).symm
      rw [h1, hAm, ← Matrix.GeneralLinearGroup.coe_inv,
        ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
        Matrix.GeneralLinearGroup.coe_one]
    have hBmem : g * A * g⁻¹ ∈ StatedSU n 2 K := (Subgroup.mem_normalizer_iff.1 hg A).1 hA
    have hBconj : conjTr (unitaryInvolution K 2 1)
        ((g * A * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g * A * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 :=
      s16k_conjTr_mem_statedSU hσsq hBmem
    have hBmat : ((g * A * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        G * Am * Ginv := by
      simp only [hG, hGinv, hAm, Matrix.GeneralLinearGroup.coe_mul]
    have hexp : conjTr (unitaryInvolution K 2 1) (G * Am * Ginv) =
        Si * conjTr (unitaryInvolution K 2 1) Am * S := by
      rw [hSi, hS, conjTr_mul, conjTr_mul]
      simp only [Matrix.mul_assoc]
    have hB' : Si * (conjTr (unitaryInvolution K 2 1) Am * (S * (G * (Am * Ginv)))) = 1 := by
      rw [hBmat, hexp] at hBconj
      simpa only [Matrix.mul_assoc] using hBconj
    have h2 : conjTr (unitaryInvolution K 2 1) Am * (S * (G * (Am * Ginv))) = S := by
      have h1 : S * (Si * (conjTr (unitaryInvolution K 2 1) Am * (S * (G * (Am * Ginv))))) =
          S := by
        have := congrArg (fun M : Matrix (Fin n) (Fin n) K => S * M) hB'
        simpa using this
      rwa [← Matrix.mul_assoc, hSSi, Matrix.one_mul] at h1
    have h3 : conjTr (unitaryInvolution K 2 1) Am * (S * (G * Am)) = S * G := by
      have h4 : (conjTr (unitaryInvolution K 2 1) Am * (S * (G * (Am * Ginv)))) * G = S * G :=
        congrArg (fun M : Matrix (Fin n) (Fin n) K => M * G) h2
      simp only [Matrix.mul_assoc] at h4
      rw [hGinvG, Matrix.mul_one] at h4
      exact h4
    have h5 : conjTr (unitaryInvolution K 2 1) Am * H * Am = H := by
      simpa only [hH, Matrix.mul_assoc] using h3
    calc H * Am = (Am * conjTr (unitaryInvolution K 2 1) Am) * H * Am := by
          rw [hAconj', Matrix.one_mul]
      _ = Am * (conjTr (unitaryInvolution K 2 1) Am * H * Am) := by
          simp only [Matrix.mul_assoc]
      _ = Am * H := by rw [h5]
  obtain ⟨c, hc⟩ := s16k_addCommutantScalar_statedSU (K := K) hK hn
    (Matrix.mulVecLin H).toAddMonoidHom (fun A hA v => by
      simp only [LinearMap.toAddMonoidHom_coe, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [hHA A hA])
  have hHc : H = c • (1 : Matrix (Fin n) (Fin n) K) :=
    Matrix.ext_iff_mulVec.2 fun v => by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]; exact hc v
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : H * (Ginv * Si) = 1 := by
      rw [hH, Matrix.mul_assoc, ← Matrix.mul_assoc G Ginv Si, hGGinv, Matrix.one_mul, hSSi]
    rw [hHc, h0, zero_smul, Matrix.zero_mul] at h1
    have h2 : (0 : K) = 1 := by
      have h3 := congrFun (congrFun h1 i0) i0
      simpa using h3
    exact one_ne_zero h2.symm
  have hconjH : conjTr (unitaryInvolution K 2 1) H = H := by
    have hconjS : conjTr (unitaryInvolution K 2 1) S = G := by
      have hcomp : (unitaryInvolution K 2 1 ∘ unitaryInvolution K 2 1) = id := by
        funext x; exact hσ2 x
      simp only [hS, conjTr, Matrix.transpose_map, Matrix.map_map, hcomp, Matrix.map_id,
        Matrix.transpose_transpose]
    rw [hH, conjTr_mul, hconjS, hS]
  have hconjc : conjTr (unitaryInvolution K 2 1) (c • (1 : Matrix (Fin n) (Fin n) K)) =
      unitaryInvolution K 2 1 c • 1 := by
    rw [conjTr, Matrix.map_smul' (unitaryInvolution K 2 1) c 1 (map_mul _),
      Matrix.map_one (unitaryInvolution K 2 1) (map_zero _) (map_one _),
      Matrix.transpose_smul, Matrix.transpose_one]
  have hc1 : c = 1 := by
    have h := hconjH
    rw [hHc, hconjc] at h
    have h2 : unitaryInvolution K 2 1 c = c := by
      have h3 := congrArg (fun M : Matrix (Fin n) (Fin n) K => M i0 i0) h
      simpa using h3
    rw [hσsq] at h2
    have h3 : c * (1 - c) = 0 := by rw [mul_sub, mul_one, ← pow_two, h2, sub_self]
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd h4 hc0
    · exact (sub_eq_zero.mp h4).symm
  have hgoal : conjTr (unitaryInvolution K 2 1) G * G = 1 := by
    rw [← hS, ← hH, hHc, hc1, one_smul]
  have hmap : G.map (fun x => x ^ 2) = G.map (unitaryInvolution K 2 1) := by
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, hσsq]
  rw [hmap]
  exact hgoal

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
