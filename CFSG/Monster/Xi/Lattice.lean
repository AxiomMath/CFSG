module

public import CFSG.Monster.Xi.Defs
public import CFSG.Monster.Code.LatticeGen

public noncomputable section

namespace CFSG.Monster.Xi

open CFSG.Monster CFSG.Monster.Code Matrix

@[expose] def coordEquiv : Fin 4 × Fin 6 ≃ Fin 24 where
  toFun p := coord p.1 p.2
  invFun i := (row i, col i)
  left_inv p := by simp
  right_inv i := by simp

theorem sum_fin24 {M : Type*} [AddCommMonoid M] (f : Fin 24 → M) :
    ∑ i, f i = ∑ j : Fin 6, ∑ r : Fin 4, f (coord r j) := by
  rw [← Equiv.sum_comp coordEquiv, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

@[expose] def colBlock (A : Matrix (Fin 4) (Fin 4) ℚ) : Matrix (Fin 24) (Fin 24) ℚ :=
  Matrix.of fun i i' => if col i = col i' then A (row i) (row i') else 0

theorem gXi_eq_colBlock : gXi = colBlock C4 := rfl

theorem colBlock_mul (A B : Matrix (Fin 4) (Fin 4) ℚ) :
    colBlock A * colBlock B = colBlock (A * B) := by
  ext i i'
  rw [mul_apply, sum_fin24, Finset.sum_eq_single (col i)]
  · by_cases h : col i = col i' <;> simp [colBlock, h, mul_apply]
  · intro k _ hk
    simp [colBlock, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem colBlock_one : colBlock 1 = 1 := by
  ext i i'
  simp only [colBlock, of_apply, one_apply]
  by_cases h : i = i'
  · subst h; simp
  · by_cases hc : col i = col i'
    · have hr : row i ≠ row i' := fun hr =>
        h (by rw [← coord_row_col i, ← coord_row_col i', hc, hr])
      simp [hc, hr, h]
    · simp [hc, h]

theorem colBlock_transpose (A : Matrix (Fin 4) (Fin 4) ℚ) : (colBlock A)ᵀ = colBlock Aᵀ := by
  ext i i'
  simp only [colBlock, transpose_apply, of_apply, eq_comm]

theorem colBlock_pow (A : Matrix (Fin 4) (Fin 4) ℚ) (n : ℕ) : colBlock A ^ n = colBlock (A ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, colBlock_one]
  | succ n ih => rw [pow_succ, ih, colBlock_mul, ← pow_succ]

theorem trace_colBlock (A : Matrix (Fin 4) (Fin 4) ℚ) : trace (colBlock A) = 6 * trace A := by
  simp only [trace, diag_apply]
  rw [sum_fin24]
  simp only [colBlock, of_apply, row_coord, col_coord, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem C4_transpose_mul_self : C4ᵀ * C4 = 1 := by
  rw [C4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four, one_apply] <;> norm_num

theorem C4_mul_transpose_self : C4 * C4ᵀ = 1 := by
  rw [C4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four, one_apply] <;> norm_num

theorem C4_pow_three : C4 ^ 3 = 1 := by
  rw [pow_succ, pow_two, C4_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_four, one_apply] <;> norm_num

theorem trace_C4 : trace C4 = 1 := by
  rw [C4_eq]
  simp [trace, Fin.sum_univ_four]
  norm_num

theorem gXi_transpose_mul_self : gXiᵀ * gXi = 1 := by
  rw [gXi_eq_colBlock, colBlock_transpose, colBlock_mul, C4_transpose_mul_self, colBlock_one]

theorem gXi_mul_transpose_self : gXi * gXiᵀ = 1 := by
  rw [gXi_eq_colBlock, colBlock_transpose, colBlock_mul, C4_mul_transpose_self, colBlock_one]

theorem gXi_pow_three : gXi ^ 3 = 1 := by
  rw [gXi_eq_colBlock, colBlock_pow, C4_pow_three, colBlock_one]

theorem trace_gXi : trace gXi = 6 := by
  rw [gXi_eq_colBlock, trace_colBlock, trace_C4, mul_one]

theorem gXi_ne_one : gXi ≠ 1 := fun h => by
  have := trace_gXi
  rw [h, trace_one, Fintype.card_fin] at this
  norm_num at this

theorem orderOf_gXi : orderOf gXi = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime gXi_pow_three gXi_ne_one

theorem vecMul_gXi_coord (v : Fin 24 → ℚ) (r' : Fin 4) (j : Fin 6) :
    (v ᵥ* gXi) (coord r' j) = ∑ r, v (coord r j) * C4 r r' := by
  rw [vecMul, dotProduct, sum_fin24, Finset.sum_eq_single j]
  · simp only [gXi_coord, ite_true]
  · intro k _ hk
    simp [gXi_coord, hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def rowSign : Fin 4 → ℤ := ![-1, 1, 1, 1]

theorem rowSign_zero : rowSign 0 = -1 := rfl

theorem rowSign_of_ne_zero : ∀ {r : Fin 4}, r ≠ 0 → rowSign r = 1 := by decide

theorem vecMul_gXi_coord' (v : Fin 24 → ℚ) (r' : Fin 4) (j : Fin 6) :
    (v ᵥ* gXi) (coord r' j) =
      (rowSign r' : ℚ) * (v (coord r' j) - (∑ r, v (coord r j)) / 2) := by
  rw [vecMul_gXi_coord, C4_eq]
  fin_cases r' <;> simp [Fin.sum_univ_four, rowSign] <;> ring

@[expose] def colSum (u : Fin 24 → ℤ) (j : Fin 6) : ℤ := ∑ r, u (coord r j)

@[expose] def xiInt (u : Fin 24 → ℤ) : Fin 24 → ℤ :=
  fun i => rowSign (row i) * (u i - colSum u (col i) / 2)

@[expose] def toQ (u : Fin 24 → ℤ) : Fin 24 → ℚ := fun i => (u i : ℚ)

theorem toQ_add (u w : Fin 24 → ℤ) : toQ (u + w) = toQ u + toQ w := by
  funext i; simp [toQ]

theorem toQ_sub (u w : Fin 24 → ℤ) : toQ (u - w) = toQ u - toQ w := by
  funext i; simp [toQ]

theorem toQ_neg (u : Fin 24 → ℤ) : toQ (-u) = -toQ u := by
  funext i; simp [toQ]

theorem toQ_xiInt {u : Fin 24 → ℤ} (hu : ∀ j, colSum u j % 2 = 0) :
    toQ (xiInt u) = toQ u ᵥ* gXi := by
  funext i
  rw [← coord_row_col i]
  generalize row i = r, col i = j
  rw [vecMul_gXi_coord']
  have hdiv : ((colSum u j / 2 : ℤ) : ℚ) = (colSum u j : ℚ) / 2 :=
    Int.cast_div (Int.dvd_of_emod_eq_zero (hu j)) (by norm_num)
  simp only [toQ, xiInt, row_coord, col_coord, Int.cast_mul, Int.cast_sub]
  rw [hdiv, colSum, Int.cast_sum]

private theorem emod_two_of_cast_eq {a b : ℤ} (h : (a : ZMod 2) = (b : ZMod 2)) :
    (a - b) % 2 = 0 := by
  have := (ZMod.intCast_eq_intCast_iff a b 2).1 h
  unfold Int.ModEq at this
  omega

private theorem cast_sum_bitLift {ι : Type*} (s : Finset ι) (x : ι → ZMod 2) :
    ((∑ i ∈ s, bitLift (x i) : ℤ) : ZMod 2) = ∑ i ∈ s, x i := by
  push_cast [bitLift_cast]
  rfl

private theorem g_coord_val : ∀ (j k : Fin 6) (r : Fin 4),
    g j (coord r k) = (if k = j then 1 else 0) + (if r = 0 then 1 else 0) := by
  decide +kernel

private theorem codeword_parities {d : Fin 24 → ZMod 2} (hd : d ∈ C) :
    (∀ k : Fin 6, (∑ r, bitLift (d (coord r k)) - bitLift (topParity d)) % 2 = 0) ∧
    (∑ k, bitLift (d (coord 0 k)) - bitLift (topParity d)) % 2 = 0 := by
  refine ⟨fun k => emod_two_of_cast_eq ?_, emod_two_of_cast_eq ?_⟩
  · rw [cast_sum_bitLift, bitLift_cast, ((mem_C_iff d).1 hd).2 k]
  · rw [cast_sum_bitLift, bitLift_cast]
    rfl

theorem colSum_emod_four {u : Fin 24 → ℤ} {m : ℤ} {d : Fin 24 → ZMod 2} (hd : d ∈ C)
    (hud : ∀ i, u i ≡ m + 2 * bitLift (d i) [ZMOD 4]) (k : Fin 6) :
    (colSum u k - 2 * bitLift (topParity d)) % 4 = 0 := by
  have hc := (codeword_parities hd).1 k
  have h0 := hud (coord 0 k)
  have h1 := hud (coord 1 k)
  have h2 := hud (coord 2 k)
  have h3 := hud (coord 3 k)
  have b0 := bitLift_zero_or_one (d (coord 0 k))
  have b1 := bitLift_zero_or_one (d (coord 1 k))
  have b2 := bitLift_zero_or_one (d (coord 2 k))
  have b3 := bitLift_zero_or_one (d (coord 3 k))
  simp only [colSum, Fin.sum_univ_four] at hc ⊢
  unfold Int.ModEq at h0 h1 h2 h3
  omega

theorem colSum_emod_two {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) (k : Fin 6) :
    colSum u k % 2 = 0 := by
  obtain ⟨m, -, d, hd, hud, -⟩ := hu
  have := colSum_emod_four hd hud k
  omega

private theorem arith_row0 {m t m' U T κ K B B' S : ℤ}
    (hm' : m' = (m + t) % 2) (hU : (U - m - 2 * B) % 4 = 0)
    (hS : (S - 2 * t) % 4 = 0) (hT : 2 * T = S) (hκ : 2 * κ = m - T - m')
    (hK : (K - m') % 2 = 0) (hBB : (B' - B - κ - K) % 2 = 0) :
    (-1 * (U - T)) % 4 = (m' + 2 * B') % 4 := by
  omega

private theorem arith_row {m m' U T κ B B' : ℤ} (hU : (U - m - 2 * B) % 4 = 0)
    (hκ : 2 * κ = m - T - m') (hBB : (B' - B - κ) % 2 = 0) :
    (1 * (U - T)) % 4 = (m' + 2 * B') % 4 := by
  omega

theorem xiInt_mem {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) : xiInt u ∈ codeLattice C := by
  obtain ⟨m, hm, d, hd, hud, hus⟩ := hu
  obtain ⟨-, htop⟩ := codeword_parities hd
  set t : ℤ := bitLift (topParity d) with ht
  have ht01 : t = 0 ∨ t = 1 := bitLift_zero_or_one _
  have hσ := colSum_emod_four hd hud
  set τ : Fin 6 → ℤ := fun k => colSum u k / 2 with hτdef
  have hτ : ∀ k, 2 * τ k = colSum u k := fun k => by
    have := hσ k
    simp only [hτdef]
    omega
  set m' : ℤ := (m + t) % 2 with hm'
  set κ : Fin 6 → ℤ := fun k => (m - τ k - m') / 2 with hκdef
  have hκ : ∀ k, 2 * κ k = m - τ k - m' := fun k => by
    have h1 := hσ k
    have h2 := hτ k
    simp only [hκdef]
    rcases hm with rfl | rfl <;> omega
  set K : ℤ := ∑ k, κ k with hKdef
  have hK : (K - m') % 2 = 0 := by
    have hsum : ∑ i, u i = 2 * ∑ k, τ k := by
      rw [sum_fin24, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => (hτ k).symm
    have h2K : 2 * K = 6 * m - ∑ k, τ k - 6 * m' := by
      rw [hKdef, Finset.mul_sum, Finset.sum_congr rfl fun k _ => hκ k, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    unfold Int.ModEq at hus
    rw [hsum] at hus
    rcases hm with rfl | rfl <;> omega
  set d' : Fin 24 → ZMod 2 := d + ∑ k, ((κ k : ℤ) : ZMod 2) • g k with hd'def
  have hd' : d' ∈ C :=
    C.add_mem hd (C.sum_mem fun k _ => C.smul_mem _ (g_mem_C k))
  have hd'val : ∀ (r : Fin 4) (k : Fin 6), d' (coord r k) =
      d (coord r k) + ((κ k : ℤ) : ZMod 2) + (if r = 0 then ((K : ℤ) : ZMod 2) else 0) := by
    intro r k
    simp only [hd'def, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g_coord_val,
      mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, hKdef, Int.cast_sum]
    rw [add_assoc]
    congr 1
    split_ifs <;> simp
  have hb' : ∀ (r : Fin 4) (k : Fin 6), (bitLift (d' (coord r k)) - bitLift (d (coord r k)) -
      κ k - (if r = 0 then K else 0)) % 2 = 0 := by
    intro r k
    have h := emod_two_of_cast_eq (a := bitLift (d' (coord r k)))
      (b := bitLift (d (coord r k)) + κ k + (if r = 0 then K else 0)) (by
        rw [bitLift_cast, hd'val]
        push_cast [bitLift_cast]
        split_ifs <;> simp)
    omega
  refine ⟨m', by omega, d', hd', fun i => ?_, ?_⟩
  · rw [← coord_row_col i]
    generalize row i = r, col i = k
    have hxi : xiInt u (coord r k) = rowSign r * (u (coord r k) - τ k) := by
      simp only [xiInt, row_coord, col_coord]
      rfl
    unfold Int.ModEq
    rw [hxi]
    have h1 : (u (coord r k) - m - 2 * bitLift (d (coord r k))) % 4 = 0 := by
      have := hud (coord r k)
      unfold Int.ModEq at this
      omega
    have h2 := hb' r k
    by_cases hr : r = 0
    · subst hr
      rw [ite_eq_left rfl] at h2
      rw [rowSign_zero]
      exact arith_row0 hm' h1 (hσ k) (hτ k) (hκ k) hK h2
    · rw [ite_eq_right hr, sub_zero] at h2
      rw [rowSign_of_ne_zero hr]
      exact arith_row h1 (hκ k) h2
  ·
    have hcol : ∀ k, ∑ r, xiInt u (coord r k) = -2 * u (coord 0 k) := by
      intro k
      have h := hτ k
      have e : ∀ r, xiInt u (coord r k) = rowSign r * (u (coord r k) - τ k) := fun r => by
        simp only [xiInt, row_coord, col_coord]
        rfl
      simp only [e, Fin.sum_univ_four, rowSign_zero,
        rowSign_of_ne_zero (show (1 : Fin 4) ≠ 0 by decide),
        rowSign_of_ne_zero (show (2 : Fin 4) ≠ 0 by decide),
        rowSign_of_ne_zero (show (3 : Fin 4) ≠ 0 by decide)]
      simp only [colSum, Fin.sum_univ_four] at h
      linarith
    have hv : ∑ i, xiInt u i = -2 * ∑ k, u (coord 0 k) := by
      rw [sum_fin24, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => hcol k
    have hU : (∑ k, u (coord 0 k) - 6 * m - 2 * ∑ k, bitLift (d (coord 0 k))) % 4 = 0 := by
      have hdvd : (4 : ℤ) ∣ ∑ k, (u (coord 0 k) - m - 2 * bitLift (d (coord 0 k))) :=
        Finset.dvd_sum fun k _ => by
          have := hud (coord 0 k)
          unfold Int.ModEq at this
          exact Int.dvd_of_emod_eq_zero (by omega)
      have e : ∑ k, (u (coord 0 k) - m - 2 * bitLift (d (coord 0 k))) =
          ∑ k, u (coord 0 k) - 6 * m - 2 * ∑ k, bitLift (d (coord 0 k)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
      rw [← e]
      exact Int.emod_eq_zero_of_dvd hdvd
    unfold Int.ModEq
    rw [hv]
    rcases hm with rfl | rfl <;> omega

@[expose] def latticeQ : Set (Fin 24 → ℚ) := toQ '' codeLattice C

theorem toQ_mem_latticeQ_vecMul {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    toQ u ᵥ* gXi = toQ (xiInt u) :=
  (toQ_xiInt (colSum_emod_two hu)).symm

theorem image_latticeQ : (fun x => x ᵥ* gXi) '' latticeQ = latticeQ := by
  refine Set.Subset.antisymm ?_ fun x hx => ?_
  · rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨xiInt u, xiInt_mem hu, (toQ_mem_latticeQ_vecMul hu).symm⟩
  · obtain ⟨u, hu, rfl⟩ := hx
    have h2 := xiInt_mem (xiInt_mem hu)
    refine ⟨toQ (xiInt (xiInt u)), ⟨_, h2, rfl⟩, ?_⟩
    show toQ (xiInt (xiInt u)) ᵥ* gXi = toQ u
    rw [← toQ_mem_latticeQ_vecMul (xiInt_mem hu), ← toQ_mem_latticeQ_vecMul hu, vecMul_vecMul,
      vecMul_vecMul, ← pow_three, gXi_pow_three, vecMul_one]

@[expose] def lamGamma (j : Fin 6) : Fin 24 → ℤ := fun i => 1 - 4 * eℤ (coord 0 j) i

theorem lamGamma_zero : lamGamma 0 = lam0 := by decide +kernel

private theorem colSum_two_g : ∀ j k : Fin 6, colSum ((2 : ℤ) • liftℤ (g j)) k % 2 = 0 := by
  decide +kernel

private theorem colSum_lamGamma : ∀ j k : Fin 6, colSum (lamGamma j) k % 2 = 0 := by
  decide +kernel

private theorem colSum_lowerDiff : ∀ (j k : Fin 6) (r s : Fin 4),
    colSum (eℤ (coord r j) - eℤ (coord s j)) k % 2 = 0 := by
  decide +kernel

private theorem xiInt_two_g : ∀ j : Fin 6, xiInt ((2 : ℤ) • liftℤ (g j)) = -lamGamma j := by
  decide +kernel

private theorem xiInt_lamGamma : ∀ j : Fin 6,
    xiInt (lamGamma j) = (2 : ℤ) • liftℤ (g j) - lamGamma j := by
  decide +kernel

private theorem xiInt_lowerDiff : ∀ (j : Fin 6) (r s : Fin 4), r ≠ 0 → s ≠ 0 → r ≠ s →
    xiInt (eℤ (coord r j) - eℤ (coord s j)) = eℤ (coord r j) - eℤ (coord s j) := by
  decide +kernel

theorem two_g_vecMul_gXi (j : Fin 6) :
    toQ ((2 : ℤ) • liftℤ (g j)) ᵥ* gXi = -toQ (lamGamma j) := by
  rw [← toQ_xiInt (colSum_two_g j), xiInt_two_g, toQ_neg]

theorem lamGamma_vecMul_gXi (j : Fin 6) :
    toQ (lamGamma j) ᵥ* gXi = toQ ((2 : ℤ) • liftℤ (g j)) - toQ (lamGamma j) := by
  rw [← toQ_xiInt (colSum_lamGamma j), xiInt_lamGamma, toQ_sub]

theorem lowerDiff_vecMul_gXi (j : Fin 6) {r s : Fin 4} (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    toQ (eℤ (coord r j) - eℤ (coord s j)) ᵥ* gXi = toQ (eℤ (coord r j) - eℤ (coord s j)) := by
  rw [← toQ_xiInt (colSum_lowerDiff j · r s), xiInt_lowerDiff j r s hr hs hrs]

theorem xi_coordinate_lattice_preservation :
    gXiᵀ * gXi = 1 ∧ gXi * gXiᵀ = 1 ∧ gXi ^ 3 = 1 ∧ orderOf gXi = 3 ∧ trace gXi = 6 ∧
    (fun x => x ᵥ* gXi) '' ((fun u : Fin 24 → ℤ => fun i => (u i : ℚ)) '' codeLattice C) =
      (fun u : Fin 24 → ℤ => fun i => (u i : ℚ)) '' codeLattice C ∧
    (∀ j : Fin 6, lamGamma j = (fun i => 1 - 4 * eℤ (coord 0 j) i) ∧
      toQ ((2 : ℤ) • liftℤ (g j)) ᵥ* gXi = -toQ (lamGamma j) ∧
      toQ (lamGamma j) ᵥ* gXi = toQ ((2 : ℤ) • liftℤ (g j)) - toQ (lamGamma j)) ∧
    (∀ (j : Fin 6) (r s : Fin 4), r ≠ 0 → s ≠ 0 → r ≠ s →
      toQ (eℤ (coord r j) - eℤ (coord s j)) ᵥ* gXi = toQ (eℤ (coord r j) - eℤ (coord s j))) :=
  ⟨gXi_transpose_mul_self, gXi_mul_transpose_self, gXi_pow_three, orderOf_gXi, trace_gXi,
    image_latticeQ, fun j => ⟨rfl, two_g_vecMul_gXi j, lamGamma_vecMul_gXi j⟩,
    fun j _ _ hr hs hrs => lowerDiff_vecMul_gXi j hr hs hrs⟩

end CFSG.Monster.Xi
