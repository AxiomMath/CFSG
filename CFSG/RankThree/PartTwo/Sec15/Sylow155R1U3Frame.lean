module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
import CFSG.RankThree.PartTwo.Sec4.LThreePiEigen
import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.LocalAnalysis.ComponentInitial Matrix

variable {n : ℕ} {K : Type} [Field K]

private theorem res1U3_pow_mod_three {n : ℕ} (hn : Even n) : 2 ^ n % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hn
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem res1U3_eq_one_or_eq_bar (h : UnitaryFieldData 2 n K) {s : K ≃+* K} (hs : s ^ 2 = 1) :
    s = 1 ∨ ∀ x, s x = h.bar x := by
  classical
  have := h.finite
  obtain ⟨hcard, hcyc⟩ := card_ringAut_and_isCyclic h.prime K h.card
  have hc : Nat.card (K ≃+* K) = 2 * n := hcard
  have : Finite (K ≃+* K) := Nat.finite_of_card_ne_zero (by rw [hc]; have := h.one_le; omega)
  have := Fintype.ofFinite (K ≃+* K)
  set β : K ≃+* K := RingEquiv.ofBijective h.bar
    ⟨h.bar.injective, fun c => ⟨h.bar c, h.bar_bar c⟩⟩ with hβ
  have hβa : ∀ x, β x = h.bar x := fun x => rfl
  have hβ1 : β ≠ 1 := by
    obtain ⟨c, hc⟩ := h.exists_bar_ne
    intro h1
    apply hc
    rw [← hβa, h1]
    rfl
  have hβ2 : β ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [pow_two]
    change β (β x) = x
    rw [hβa, hβa, h.bar_bar]
  have hle : (Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hT : ({1, β} : Finset (K ≃+* K)) ⊆
      Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl
    · exact one_pow 2
    · exact hβ2
  have hTc : ({1, β} : Finset (K ≃+* K)).card = 2 := Finset.card_pair (Ne.symm hβ1)
  have heq := Finset.eq_of_subset_of_card_le hT (by rw [hTc]; exact hle)
  have hsS : s ∈ Finset.univ.filter (fun x : K ≃+* K => x ^ 2 = 1) := by simp [hs]
  rw [← heq] at hsS
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsS
  rcases hsS with h1 | h1
  · exact Or.inl h1
  · exact Or.inr fun x => by rw [h1, hβa]

theorem res1U3_exists_cubeRoot (h : UnitaryFieldData 2 n K) (heven : Even n) :
    ∃ τ : K, τ ^ 3 = 1 ∧ τ ≠ 1 ∧ h.bar τ = τ := by
  have := h.finite
  have hmod : 2 ^ (2 * n) % 3 = 1 := res1U3_pow_mod_three (even_two_mul n)
  have hpos : 0 < 2 ^ (2 * n) := by positivity
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card]
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
  have hu3 : (u : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hu, pow_orderOf_eq_one, Units.val_one]
  refine ⟨u, hu3, ?_, ?_⟩
  · intro h1
    have : u = 1 := Units.ext h1
    rw [this, orderOf_one] at hu
    norm_num at hu
  · rw [h.bar_apply]
    have hm := res1U3_pow_mod_three heven
    obtain ⟨m, hm'⟩ : ∃ m, 2 ^ n = 3 * m + 1 := ⟨2 ^ n / 3, by omega⟩
    rw [hm', pow_succ, pow_mul, hu3, one_pow, one_mul]

private theorem res1U3_eq_one_of_mul_self [CharP K 2] {x : K} (hx : x * x = 1) : x = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : (x + 1) * (x + 1) = 0 := by linear_combination hx + (x + 1) * h2
  have hx1 := mul_self_eq_zero.mp this
  linear_combination hx1 - h2

private theorem res1U3_map_mul (s : K ≃+* K) (M N : Matrix (Fin 3) (Fin 3) K) :
    (M * N).map s = M.map s * N.map s := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul]

private theorem res1U3_diag_ne {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (i j : Fin 3)
    (hij : i ≠ j) : (![τ, 1, τ ^ 2] : Fin 3 → K) i ≠ ![τ, 1, τ ^ 2] j := by
  have hτ2 : τ ^ 2 ≠ 1 := fun h => hτ1 (by linear_combination hτ - τ * h)
  have hτ12 : τ ≠ τ ^ 2 := fun h => hτ1 (by linear_combination (τ + 1) * h + hτ)
  fin_cases i <;> fin_cases j <;> first
    | exact absurd rfl hij
    | exact hτ1 | exact hτ1.symm | exact hτ12 | exact hτ12.symm | exact hτ2 | exact hτ2.symm

theorem res1U3_eq_mul_diagonal {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {X g N : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    (hXg : X * g = g * diagonal ![τ, 1, τ ^ 2]) (hXN : X * N = N * diagonal ![τ, 1, τ ^ 2]) :
    ∃ μ : Fin 3 → K, N = g * diagonal μ := by
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, 1, τ ^ 2] with hD
  set M := g⁻¹ * N with hM
  have hgX : g⁻¹ * X = D * g⁻¹ := by
    calc g⁻¹ * X = g⁻¹ * X * (g * g⁻¹) := by rw [Matrix.mul_nonsing_inv g hgd, Matrix.mul_one]
      _ = g⁻¹ * (X * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = g⁻¹ * (g * D) * g⁻¹ := by rw [hXg]
      _ = D * g⁻¹ := by
        rw [← Matrix.mul_assoc g⁻¹, Matrix.nonsing_inv_mul g hgd, Matrix.one_mul]
  have hMD : M * D = D * M := by
    calc M * D = g⁻¹ * (N * D) := by rw [hM, Matrix.mul_assoc]
      _ = g⁻¹ * (X * N) := by rw [hXN]
      _ = (g⁻¹ * X) * N := by rw [Matrix.mul_assoc]
      _ = D * M := by rw [hgX, hM, Matrix.mul_assoc]
  have hMdiag : M = diagonal (fun i => M i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact Sec4.entry_eq_zero_of_commute_diagonal hMD (res1U3_diag_ne hτ hτ1 i j hij)
  refine ⟨fun i => M i i, ?_⟩
  calc N = g * (g⁻¹ * N) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgd, Matrix.one_mul]
    _ = g * diagonal (fun i => M i i) := by rw [← hM, ← hMdiag]

theorem res1U3_mul_eq_diagonal {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {X W g : Matrix (Fin 3) (Fin 3) K} (hg : IsUnit g)
    (hXg : X * g = g * diagonal ![τ, 1, τ ^ 2]) (hWX : W * X = X * W) :
    ∃ δ : Fin 3 → K, W * g = g * diagonal δ :=
  res1U3_eq_mul_diagonal hτ hτ1 hg hXg (by
    rw [← Matrix.mul_assoc, ← hWX, Matrix.mul_assoc, hXg, Matrix.mul_assoc])

private theorem res1U3_exists_perm (k : Fin 3 → Fin 3)
    (hsum : ((k 0 : ℕ) + k 1 + k 2) % 3 = 0) (hk : ¬ (k 0 = k 1 ∧ k 1 = k 2)) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ i, k (σ i) = ![1, 0, 2] i := by
  revert k
  decide

theorem res1U3_exists_frame (h : UnitaryFieldData 2 n K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hτb : h.bar τ = τ) {X : Matrix (Fin 3) (Fin 3) K} (hX3 : X ^ 3 = 1) (hXdet : X.det = 1)
    (hXu : (X.map h.bar)ᵀ * X = 1) (hX1 : X ≠ 1) :
    ∃ (g : Matrix (Fin 3) (Fin 3) K) (c : K), IsUnit g ∧
      X * g = g * diagonal ![τ, 1, τ ^ 2] ∧
      (g.map h.bar)ᵀ * g = !![0, 0, 1; 0, c, 0; 1, 0, 0] := by
  have : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hτo : orderOf τ = 3 := orderOf_eq_prime hτ hτ1
  obtain ⟨b, hb, hk⟩ := Sec4.exists_eigenbasis hτ hτ1 h3 hX3
  choose k hk using hk
  set P := Sec4.colMat b with hP
  have hPu : IsUnit P := Sec4.isUnit_colMat hb
  have hPd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPu
  have hXP : X * P = P * diagonal (fun i => τ ^ (k i : ℕ)) := Sec4.mul_colMat_eq hk
  have hsum : ((k 0 : ℕ) + k 1 + k 2) % 3 = 0 := by
    have e := congrArg Matrix.det hXP
    rw [Matrix.det_mul, Matrix.det_mul, hXdet, one_mul, Matrix.det_diagonal,
      Fin.prod_univ_three] at e
    have e2 : τ ^ ((k 0 : ℕ) + k 1 + k 2) = 1 := by
      rw [pow_add, pow_add]
      refine mul_left_cancel₀ hPd.ne_zero ?_
      rw [mul_one]
      exact e.symm
    refine Nat.mod_eq_zero_of_dvd ?_
    have hdvd := orderOf_dvd_of_pow_eq_one e2
    rwa [hτo] at hdvd
  have hne : ¬ (k 0 = k 1 ∧ k 1 = k 2) := by
    rintro ⟨h01, h12⟩
    set t := τ ^ (k 0 : ℕ) with ht
    have hdiag : diagonal (fun i => τ ^ (k i : ℕ)) = t • (1 : Matrix (Fin 3) (Fin 3) K) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        fin_cases i <;> simp [ht, h01, h12]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    have hXt : X = t • (1 : Matrix (Fin 3) (Fin 3) K) := by
      calc X = X * P * P⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv P hPd, Matrix.mul_one]
        _ = t • (1 : Matrix (Fin 3) (Fin 3) K) := by
            rw [hXP, hdiag, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
              Matrix.mul_nonsing_inv P hPd]
    have htb : h.bar t = t := by rw [ht, map_pow, hτb]
    have hu00 := congrFun (congrFun hXu 0) 0
    rw [hXt] at hu00
    simp [Matrix.mul_apply, Fin.sum_univ_three, htb] at hu00
    have ht1 : t = 1 := res1U3_eq_one_of_mul_self hu00
    exact hX1 (by rw [hXt, ht1, one_smul])
  obtain ⟨σ, hσ⟩ := res1U3_exists_perm k hsum hne
  set g₀ := Sec4.colMat (b ∘ σ) with hg₀
  have hg₀u : IsUnit g₀ := Sec4.isUnit_colMat (hb.comp σ σ.injective)
  have hg₀d : IsUnit g₀.det := (Matrix.isUnit_iff_isUnit_det g₀).mp hg₀u
  have hXg₀ : X * g₀ = g₀ * diagonal ![τ, 1, τ ^ 2] := by
    refine Sec4.mul_colMat_eq fun i => ?_
    rw [Function.comp_apply, hk, hσ i]
    fin_cases i <;> simp
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, 1, τ ^ 2] with hD
  set H := (g₀.map h.bar)ᵀ * g₀ with hH
  have hDb : D.map h.bar = D := by
    rw [hD, Matrix.diagonal_map (map_zero h.bar)]
    congr 1
    ext i
    fin_cases i <;> simp [hτb]
  have hDHD : D * H * D = H := by
    have e : ((X * g₀).map h.bar)ᵀ * (X * g₀) = (g₀.map h.bar)ᵀ * g₀ := by
      rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ X,
        hXu, Matrix.one_mul]
    rw [hXg₀, Matrix.map_mul, hDb, Matrix.transpose_mul, hD, Matrix.diagonal_transpose,
      ← hD, ← hH] at e
    calc D * H * D = D * (g₀.map h.bar)ᵀ * (g₀ * D) := by
          rw [hH]; simp only [Matrix.mul_assoc]
      _ = H := e
  have hHij : ∀ i j, (![τ, 1, τ ^ 2] : Fin 3 → K) i * ![τ, 1, τ ^ 2] j ≠ 1 → H i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hDHD i) j
    rw [hD, Matrix.mul_diagonal, Matrix.diagonal_mul] at e
    have : H i j * ((![τ, 1, τ ^ 2] : Fin 3 → K) i * ![τ, 1, τ ^ 2] j - 1) = 0 := by
      linear_combination e
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hij)
  have hτ2 : τ ^ 2 ≠ 1 := fun h => hτ1 (by linear_combination hτ - τ * h)
  have hτ4 : τ ^ 2 * τ ^ 2 ≠ 1 := by
    intro h4
    apply hτ1
    linear_combination h4 - τ * hτ
  have H00 : H 0 0 = 0 := hHij 0 0 (by simpa [← sq] using hτ2)
  have H01 : H 0 1 = 0 := hHij 0 1 (by simpa using hτ1)
  have H10 : H 1 0 = 0 := hHij 1 0 (by simpa using hτ1)
  have H12 : H 1 2 = 0 := hHij 1 2 (by simpa using hτ2)
  have H21 : H 2 1 = 0 := hHij 2 1 (by simpa using hτ2)
  have H22 : H 2 2 = 0 := hHij 2 2 (by simpa using hτ4)
  have hHerm : H 2 0 = h.bar (H 0 2) := by
    simp only [hH, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Fin.sum_univ_three,
      map_add, map_mul, h.bar_bar]
    ring
  set a := H 0 2 with ha
  have hHd : H.det ≠ 0 := by
    rw [hH, Matrix.det_mul, Matrix.det_transpose]
    have e : (g₀.map h.bar).det = h.bar g₀.det := (RingHom.map_det h.bar g₀).symm
    rw [e]
    exact mul_ne_zero ((map_ne_zero h.bar).mpr hg₀d.ne_zero) hg₀d.ne_zero
  have ha0 : a ≠ 0 := by
    intro ha0
    apply hHd
    rw [Matrix.det_fin_three, H00, H01, ← ha, ha0]
    ring
  set E : Matrix (Fin 3) (Fin 3) K := diagonal ![1, 1, a⁻¹] with hE
  have hEu : IsUnit E := by
    rw [Matrix.isUnit_iff_isUnit_det, hE, Matrix.det_diagonal, Fin.prod_univ_three]
    simp [ha0]
  refine ⟨g₀ * E, H 1 1, hg₀u.mul hEu, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, hXg₀, Matrix.mul_assoc, Matrix.mul_assoc, hE, hD,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 2
    ext i
    exact mul_comm _ _
  · rw [Matrix.map_mul, Matrix.transpose_mul, hE, Matrix.diagonal_map (map_zero h.bar),
      Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc (g₀.map h.bar)ᵀ, ← hH]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hba : h.bar a ≠ 0 := (map_ne_zero h.bar).mpr ha0
    fin_cases i <;> fin_cases j <;>
      simp [H00, H01, H10, H12, H21, H22, hHerm, ← ha, ha0, hba]

theorem res1U3_pow_eq_one (h : UnitaryFieldData 2 n K) {W g : Matrix (Fin 3) (Fin 3) K}
    (hg : IsUnit g) {δ : Fin 3 → K} (hWg : W * g = g * diagonal δ)
    (hδ : ∀ i, δ i * h.bar (δ i) = 1) : W ^ (2 ^ n + 1) = 1 := by
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hpow : ∀ m : ℕ, W ^ m * g = g * diagonal (δ ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, Matrix.mul_assoc, hWg, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
        Matrix.diagonal_mul_diagonal, pow_succ]
      try rfl
  have hδq : δ ^ (2 ^ n + 1) = 1 := by
    ext i
    rw [Pi.pow_apply, Pi.one_apply, pow_succ, ← h.bar_apply, mul_comm]
    exact hδ i
  have e := hpow (2 ^ n + 1)
  have hd1 : diagonal (1 : Fin 3 → K) = 1 := Matrix.diagonal_one
  rw [hδq, hd1, Matrix.mul_one] at e
  calc W ^ (2 ^ n + 1) = W ^ (2 ^ n + 1) * g * g⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgd, Matrix.mul_one]
    _ = 1 := by rw [e, Matrix.mul_nonsing_inv g hgd]

theorem res1U3_torus_inv (h : UnitaryFieldData 2 n K) {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hτb : h.bar τ = τ) {X W g A : Matrix (Fin 3) (Fin 3) K} {c : K} (hg : IsUnit g)
    (hA : IsUnit A) (hgram : (g.map h.bar)ᵀ * g = !![0, 0, 1; 0, c, 0; 1, 0, 0])
    (hXg : X * g = g * diagonal ![τ, 1, τ ^ 2]) {δ : Fin 3 → K}
    (hWg : W * g = g * diagonal δ) (hWu : (W.map h.bar)ᵀ * W = 1) (hW1 : W ≠ 1)
    {s : K ≃+* K} (hs : s = 1 ∨ ∀ x, s x = h.bar x) (hAX : A * X.map s = X * A)
    (hAW : W * A * W.map s = A) :
    δ 0 = δ 2 ∧ ∀ i, δ i * h.bar (δ i) = 1 := by
  have : CharP K 2 := h.charP
  have hgd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).mp hg
  have hAd : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![τ, 1, τ ^ 2] with hD
  have hsτ : s τ = τ := by
    rcases hs with rfl | hs
    · rfl
    · rw [hs, hτb]
  have hDs : D.map s = D := by
    rw [hD, Matrix.diagonal_map (map_zero s)]
    congr 1
    ext i
    fin_cases i <;> simp [hsτ]
  set N := A * g.map s with hN
  have hXN : X * N = N * D := by
    calc X * N = A * X.map s * g.map s := by rw [hN, ← Matrix.mul_assoc, hAX]
      _ = A * (X * g).map s := by rw [res1U3_map_mul, Matrix.mul_assoc]
      _ = N * D := by rw [hXg, res1U3_map_mul, hDs, hN, Matrix.mul_assoc]
  obtain ⟨μ, hNμ⟩ := res1U3_eq_mul_diagonal hτ hτ1 hg hXg hXN
  have hμ : ∀ i, μ i ≠ 0 := by
    have hNd : N.det ≠ 0 := by
      rw [hN, Matrix.det_mul]
      have e : (g.map s).det = s g.det := (RingHom.map_det (s : K →+* K) g).symm
      rw [e]
      exact mul_ne_zero hAd.ne_zero ((map_ne_zero s).mpr hgd.ne_zero)
    rw [hNμ, Matrix.det_mul, Matrix.det_diagonal] at hNd
    intro i
    exact Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hNd) i (Finset.mem_univ i)
  have hδs : ∀ i, δ i * s (δ i) = 1 := by
    have e1 : g.map s * diagonal (fun i => s (δ i)) = W.map s * g.map s := by
      rw [← res1U3_map_mul, hWg, res1U3_map_mul, Matrix.diagonal_map (map_zero s)]
      try rfl
    have e2 : W * N * diagonal (fun i => s (δ i)) = N := by
      calc W * N * diagonal (fun i => s (δ i)) =
          W * A * (g.map s * diagonal (fun i => s (δ i))) := by
            rw [hN]; simp only [Matrix.mul_assoc]
        _ = (W * A * W.map s) * g.map s := by rw [e1]; simp only [Matrix.mul_assoc]
        _ = N := by rw [hAW]; try rfl
    rw [hNμ, ← Matrix.mul_assoc, hWg, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal] at e2
    have e3 := congrArg (fun M => g⁻¹ * M) e2
    simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hgd, Matrix.one_mul] at e3
    intro i
    have e4 : δ i * (μ i * s (δ i)) = μ i := congrFun (Matrix.diagonal_injective e3) i
    have : (δ i * s (δ i) - 1) * μ i = 0 := by linear_combination e4
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (hμ i))
  rcases hs with rfl | hsb
  ·
    exfalso
    apply hW1
    have hδ1 : δ = 1 := funext fun i => res1U3_eq_one_of_mul_self (hδs i)
    have hd1 : diagonal (1 : Fin 3 → K) = 1 := Matrix.diagonal_one
    rw [hδ1, hd1, Matrix.mul_one] at hWg
    calc W = W * g * g⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv g hgd, Matrix.mul_one]
      _ = 1 := by rw [hWg, Matrix.mul_nonsing_inv g hgd]
  · have hδb : ∀ i, δ i * h.bar (δ i) = 1 := fun i => by rw [← hsb]; exact hδs i
    refine ⟨?_, hδb⟩
    have e : ((W * g).map h.bar)ᵀ * (W * g) = !![0, 0, 1; 0, c, 0; 1, 0, 0] := by
      rw [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ W, hWu,
        Matrix.one_mul, hgram]
    rw [hWg, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ g,
      hgram, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose] at e
    have e02 := congrFun (congrFun e 0) 2
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at e02
    simp at e02
    have h0 := hδb 0
    calc δ 0 = δ 0 * (h.bar (δ 0) * δ 2) := by rw [e02, mul_one]
      _ = (δ 0 * h.bar (δ 0)) * δ 2 := by ring
      _ = δ 2 := by rw [h0, one_mul]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
