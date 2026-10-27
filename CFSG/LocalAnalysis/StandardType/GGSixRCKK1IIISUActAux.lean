module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoordRoot
public import CFSG.LieType.Universal.Unitary.Hermitian

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {k : ℕ}

noncomputable abbrev rckSUc_J (k : ℕ) : Matrix (Fin k) (Fin k) SUF := antidiag k

noncomputable abbrev rckSUc_alpha (z : ZMod 2) : SUF := algebraMap (ZMod 2) SUF z

theorem rckSUc_two (x : SUF) : x + x = 0 := by
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have h : (2 : SUF) * x = 0 := by rw [h2, zero_mul]
  simpa [two_mul] using h

theorem rckSUc_card : Nat.card SUF = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

theorem rckSUc_card_sq : Nat.card SUF = (2 ^ 1) ^ 2 := by
  rw [rckSUc_card]; norm_num

theorem rckSUc_sigma_involutive : ∀ c : SUF, SUσ (SUσ c) = c :=
  unitaryInvolution_involutive rckSUc_card_sq

theorem rckSUc_sigma_apply (c : SUF) : SUσ c = c ^ 2 := by
  rw [SUσ, unitaryInvolution_apply]
  norm_num

theorem rckSUc_sigma_alpha (z : ZMod 2) : SUσ (rckSUc_alpha z) = rckSUc_alpha z := by
  rw [rckSUc_sigma_apply]
  change (algebraMap (ZMod 2) SUF z) ^ 2 = algebraMap (ZMod 2) SUF z
  rw [← map_pow]
  congr 1
  exact (by decide : ∀ z : ZMod 2, z ^ 2 = z) z

theorem rckSUc_alpha_inj : Function.Injective rckSUc_alpha :=
  (algebraMap (ZMod 2) SUF).injective

theorem rckSUc_sigma_fixed (x : SUF) (hx : SUσ x = x) :
    ∃ z : ZMod 2, rckSUc_alpha z = x := by
  have h2 : x ^ 2 = x := by rw [← rckSUc_sigma_apply, hx]
  have h3 : x * (x - 1) = 0 := by
    have h4 : x * (x - 1) = x ^ 2 - x := by ring
    rw [h4, h2, sub_self]
  rcases mul_eq_zero.1 h3 with h | h
  · exact ⟨0, by rw [h, rckSUc_alpha, map_zero]⟩
  · exact ⟨1, by rw [sub_eq_zero.1 h, rckSUc_alpha, map_one]⟩

theorem rckSUc_omega_sq : suOmega ^ 2 = suOmega + 1 := by
  have h : suOmega ^ 2 + (suOmega + 1) = 0 := by
    rw [show suOmega ^ 2 + (suOmega + 1) = suOmega ^ 2 + suOmega + 1 by ring]
    exact suOmega_spec
  rw [eq_neg_iff_add_eq_zero.mpr h,
    neg_eq_of_add_eq_zero_left (rckSUc_two (suOmega + 1))]

theorem rckSUc_omega_ne_zero : suOmega ≠ 0 := by
  intro h
  have hspec := suOmega_spec
  rw [h] at hspec
  exact one_ne_zero (show (1 : SUF) = 0 from by simpa using hspec)

theorem rckSUc_sigma_omega : SUσ suOmega = suOmega + 1 := by
  rw [rckSUc_sigma_apply, rckSUc_omega_sq]

theorem rckSUc_omega_add_sigma_omega : suOmega + SUσ suOmega = 1 := by
  rw [rckSUc_sigma_omega, ← add_assoc, rckSUc_two, zero_add]

theorem rckSUc_omega_notMem (z : ZMod 2) : rckSUc_alpha z ≠ suOmega := by
  intro h
  have hfix : SUσ suOmega = suOmega := by rw [← h, rckSUc_sigma_alpha]
  have h1 : suOmega + SUσ suOmega = 1 := rckSUc_omega_add_sigma_omega
  rw [hfix] at h1
  have hone : (0 : SUF) = 1 := (rckSUc_two suOmega).symm.trans h1
  exact one_ne_zero hone.symm

theorem rckSUc_omega_ne_sigma_omega : suOmega ≠ SUσ suOmega := by
  intro h
  have h1 : suOmega + suOmega = 1 := by
    have := rckSUc_omega_add_sigma_omega
    rw [← h] at this
    exact this
  have hone : (0 : SUF) = 1 := (rckSUc_two suOmega).symm.trans h1
  exact one_ne_zero hone.symm

@[expose] noncomputable def rckSUc_L : (Fin 2 → ZMod 2) →ₗ[ZMod 2] SUF where
  toFun p := rckSUc_alpha (p 0) + rckSUc_alpha (p 1) * suOmega
  map_add' p q := by
    simp only [Pi.add_apply, map_add, add_mul]
    ring
  map_smul' c p := by
    rcases (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) c with hc | hc <;> rw [hc] <;> simp

theorem rckSUc_L_apply (p : Fin 2 → ZMod 2) :
    rckSUc_L p = rckSUc_alpha (p 0) + rckSUc_alpha (p 1) * suOmega := rfl

theorem rckSUc_L_injective : Function.Injective rckSUc_L := by
  intro p q h
  have h' : algebraMap (ZMod 2) SUF (p 0) + algebraMap (ZMod 2) SUF (p 1) * suOmega
      = algebraMap (ZMod 2) SUF (q 0) + algebraMap (ZMod 2) SUF (q 1) * suOmega := h
  have hzero : rckSUc_alpha (p 0 - q 0) + rckSUc_alpha (p 1 - q 1) * suOmega = 0 := by
    change algebraMap (ZMod 2) SUF (p 0 - q 0)
      + algebraMap (ZMod 2) SUF (p 1 - q 1) * suOmega = 0
    rw [map_sub, map_sub]
    linear_combination h'
  have hbits : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hbits (p 1 - q 1) with hb | hb
  · have h1 : rckSUc_alpha (p 0 - q 0) = 0 := by
      rw [hb] at hzero
      simpa using hzero
    have h0 : p 0 = q 0 :=
      sub_eq_zero.mp (rckSUc_alpha_inj (by rw [h1, rckSUc_alpha, map_zero]))
    have h2 : p 1 = q 1 := sub_eq_zero.mp hb
    funext i
    fin_cases i
    · exact h0
    · exact h2
  · exfalso
    have h1 : rckSUc_alpha (p 0 - q 0) = suOmega := by
      have hsum : rckSUc_alpha (p 0 - q 0) + suOmega = 0 := by
        rw [hb] at hzero
        simpa using hzero
      calc rckSUc_alpha (p 0 - q 0) = -suOmega := eq_neg_of_add_eq_zero_left hsum
        _ = suOmega := neg_eq_of_add_eq_zero_left (rckSUc_two suOmega)
    exact rckSUc_omega_notMem (p 0 - q 0) h1

theorem rckSUc_L_surjective : Function.Surjective rckSUc_L := by
  haveI : Fintype SUF := Fintype.ofFinite SUF
  have hcard : Fintype.card (Fin 2 → ZMod 2) = Fintype.card SUF := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, ← Nat.card_eq_fintype_card,
      rckSUc_card]
    norm_num
  exact ((Fintype.bijective_iff_injective_and_card rckSUc_L).mpr
    ⟨rckSUc_L_injective, hcard⟩).2

noncomputable abbrev rckSUc_beta (v : Fin 4 → ZMod 2) : SUF :=
  rckSUc_alpha (v 1) + rckSUc_alpha (v 2) * suOmega

theorem rckSUc_beta_eq_L (v : Fin 4 → ZMod 2) :
    rckSUc_beta v = rckSUc_L ![v 1, v 2] := by
  simp [rckSUc_beta, rckSUc_L_apply]

theorem rckSUc_beta_inj {v w : Fin 4 → ZMod 2} (h : rckSUc_beta v = rckSUc_beta w) :
    v 1 = w 1 ∧ v 2 = w 2 := by
  have hL : rckSUc_L ![v 1, v 2] = rckSUc_L ![w 1, w 2] := by
    rw [← rckSUc_beta_eq_L, ← rckSUc_beta_eq_L, h]
  have hp : ![v 1, v 2] = ![w 1, w 2] := rckSUc_L_injective hL
  exact ⟨congrFun hp 0, congrFun hp 1⟩

@[expose] def rckSUc_e (hk : 4 ≤ k) : Fin 2 → Fin k := ![sI0 hk, sI1 hk]

@[expose] def rckSUc_e' (hk : 4 ≤ k) : Fin 2 → Fin k := fun r => Fin.rev (rckSUc_e hk r)

theorem rckSUc_e_injective (hk : 4 ≤ k) : Function.Injective (rckSUc_e hk) := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [rckSUc_e, sI0, sI1]

theorem rckSUc_e'_injective (hk : 4 ≤ k) : Function.Injective (rckSUc_e' hk) :=
  Fin.rev_injective.comp (rckSUc_e_injective hk)

theorem rckSUc_e_zero_ne_one (hk : 4 ≤ k) : rckSUc_e hk 0 ≠ rckSUc_e hk 1 :=
  fun h => (by decide : (0 : Fin 2) ≠ 1) (rckSUc_e_injective hk h)

theorem rckSUc_e_one_ne_zero (hk : 4 ≤ k) : rckSUc_e hk 1 ≠ rckSUc_e hk 0 :=
  fun h => (by decide : (1 : Fin 2) ≠ 0) (rckSUc_e_injective hk h)

theorem rckSUc_e'_zero_ne_one (hk : 4 ≤ k) : rckSUc_e' hk 0 ≠ rckSUc_e' hk 1 :=
  fun h => (by decide : (0 : Fin 2) ≠ 1) (rckSUc_e'_injective hk h)

theorem rckSUc_e'_one_ne_zero (hk : 4 ≤ k) : rckSUc_e' hk 1 ≠ rckSUc_e' hk 0 :=
  fun h => (by decide : (1 : Fin 2) ≠ 0) (rckSUc_e'_injective hk h)

theorem rckSUc_e_ne_e' (hk : 4 ≤ k) (a b : Fin 2) :
    rckSUc_e hk a ≠ rckSUc_e' hk b := by
  intro h
  have hv := congrArg Fin.val h
  fin_cases a <;> fin_cases b <;>
    simp [rckSUc_e, rckSUc_e', sI0, sI1, Fin.val_rev] at hv <;> omega

@[expose] noncomputable def rckSUc_M (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    Matrix (Fin k) (Fin k) SUF :=
  Matrix.single (rckSUc_e hk 0) (rckSUc_e' hk 0) (rckSUc_alpha (v 0))
    + Matrix.single (rckSUc_e hk 0) (rckSUc_e' hk 1) (rckSUc_beta v)
    + Matrix.single (rckSUc_e hk 1) (rckSUc_e' hk 0) (SUσ (rckSUc_beta v))
    + Matrix.single (rckSUc_e hk 1) (rckSUc_e' hk 1) (rckSUc_alpha (v 3))

@[expose] noncomputable def rckSUc_A (v : Fin 4 → ZMod 2) : Matrix (Fin 2) (Fin 2) SUF :=
  !![rckSUc_alpha (v 0), rckSUc_beta v; SUσ (rckSUc_beta v), rckSUc_alpha (v 3)]

theorem rckSUc_M_eq_suCorner (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v = 1 + rckSUc_M hk v := by
  simp only [suCorner, rckSUc_M]
  abel

@[expose] noncomputable def rckSUc_N (hk : 4 ≤ k) : Matrix (Fin k) (Fin k) SUF :=
  Matrix.single (rckSUc_e hk 0) (rckSUc_e' hk 1) 1
    + Matrix.single (rckSUc_e hk 1) (rckSUc_e' hk 0) 1

theorem rckSUc_beta_s5R : rckSUc_beta s5R = 1 := by
  simp [rckSUc_beta, s5R]

theorem rckSUc_M_s5R (hk : 4 ≤ k) : rckSUc_M hk s5R = rckSUc_N hk := by
  have h0 : rckSUc_alpha (s5R 0) = 0 := by simp [s5R]
  have h3 : rckSUc_alpha (s5R 3) = 0 := by simp [s5R]
  simp only [rckSUc_M, rckSUc_N, h0, h3, rckSUc_beta_s5R, map_one, Matrix.single_zero,
    zero_add, add_zero]

theorem rckSUc_suR_eq (hk : 4 ≤ k) :
    ((suR hk : SUG k) : GL (Fin k) SUF) = 1 + rckSUc_N hk := by
  change (suZ hk s5R : GL (Fin k) SUF) = 1 + rckSUc_N hk
  rw [suZ_val, rckSUc_M_eq_suCorner, rckSUc_M_s5R]

theorem rckSUc_map_single (τ : SUF ≃+* SUF) (a b : Fin k) (c : SUF) :
    (Matrix.single a b c).map τ = Matrix.single a b (τ c) := by
  ext i j
  by_cases h : a = i ∧ b = j <;> simp [Matrix.map_apply, Matrix.single_apply, h]

theorem rckSUc_map_add (τ : SUF ≃+* SUF) (M N : Matrix (Fin k) (Fin k) SUF) :
    (M + N).map τ = M.map τ + N.map τ := by
  ext i j
  simp [Matrix.map_apply, Matrix.add_apply, map_add]

theorem rckSUc_N_map (hk : 4 ≤ k) (τ : SUF ≃+* SUF) :
    (rckSUc_N hk).map τ = rckSUc_N hk := by
  rw [rckSUc_N, rckSUc_map_add, rckSUc_map_single, rckSUc_map_single]
  simp

theorem rckSUc_M_map (hk : 4 ≤ k) (τ : SUF ≃+* SUF) (v : Fin 4 → ZMod 2) :
    (rckSUc_M hk v).map τ =
      Matrix.single (rckSUc_e hk 0) (rckSUc_e' hk 0) (τ (rckSUc_alpha (v 0)))
        + Matrix.single (rckSUc_e hk 0) (rckSUc_e' hk 1) (τ (rckSUc_beta v))
        + Matrix.single (rckSUc_e hk 1) (rckSUc_e' hk 0) (τ (SUσ (rckSUc_beta v)))
        + Matrix.single (rckSUc_e hk 1) (rckSUc_e' hk 1) (τ (rckSUc_alpha (v 3))) := by
  rw [rckSUc_M, rckSUc_map_add, rckSUc_map_add, rckSUc_map_add, rckSUc_map_single,
    rckSUc_map_single, rckSUc_map_single, rckSUc_map_single]

theorem rckSUc_single_mul_apply (c : SUF) (a b : Fin k)
    (M : Matrix (Fin k) (Fin k) SUF) (x y : Fin k) :
    (Matrix.single a b c * M) x y = if x = a then c * M b y else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : x = a
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single b]
    · simp
    · intro m _ hm
      rw [Matrix.single_apply, if_neg (fun hc => hm hc.2.symm), zero_mul]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m _
    rw [Matrix.single_apply, if_neg (fun hc => h hc.1.symm), zero_mul]

theorem rckSUc_mul_single_apply (M : Matrix (Fin k) (Fin k) SUF) (a b : Fin k) (c : SUF)
    (x y : Fin k) :
    (M * Matrix.single a b c) x y = if y = b then M x a * c else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : y = b
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single a]
    · simp
    · intro m _ hm
      rw [Matrix.single_apply, if_neg (fun hc => hm hc.1.symm), mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro m _
    rw [Matrix.single_apply, if_neg (fun hc => h hc.2.symm), mul_zero]

theorem rckSUc_hBN_apply (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (i j : Fin k) :
    (if j = rckSUc_e' hk 1 then B i (rckSUc_e hk 0) else 0)
      + (if j = rckSUc_e' hk 0 then B i (rckSUc_e hk 1) else 0)
    = (if i = rckSUc_e hk 0 then B (rckSUc_e' hk 1) j else 0)
      + (if i = rckSUc_e hk 1 then B (rckSUc_e' hk 0) j else 0) := by
  have h := congrFun (congrFun hBN i) j
  rw [rckSUc_N, Matrix.mul_add, Matrix.add_mul] at h
  simp only [Matrix.add_apply, rckSUc_mul_single_apply, rckSUc_single_mul_apply,
    mul_one] at h
  simpa using h

theorem rckSUc_B_col_of_ne (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (i : Fin k)
    (hi0 : i ≠ rckSUc_e hk 0) (hi1 : i ≠ rckSUc_e hk 1) :
    B i (rckSUc_e hk 0) = 0 ∧ B i (rckSUc_e hk 1) = 0 := by
  constructor
  · have h := rckSUc_hBN_apply hk B hBN i (rckSUc_e' hk 1)
    simp [rckSUc_e'_one_ne_zero hk, hi0, hi1] at h
    exact h
  · have h := rckSUc_hBN_apply hk B hBN i (rckSUc_e' hk 0)
    simp [rckSUc_e'_zero_ne_one hk, hi0, hi1] at h
    exact h

theorem rckSUc_B_row_of_ne (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) (j : Fin k)
    (hj0 : j ≠ rckSUc_e' hk 0) (hj1 : j ≠ rckSUc_e' hk 1) :
    B (rckSUc_e' hk 0) j = 0 ∧ B (rckSUc_e' hk 1) j = 0 := by
  constructor
  · have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 1) j
    simp [rckSUc_e_one_ne_zero hk, hj0, hj1] at h
    exact h.symm
  · have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 0) j
    simp [rckSUc_e_zero_ne_one hk, hj0, hj1] at h
    exact h.symm

theorem rckSUc_B_eq_00 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    B (rckSUc_e hk 0) (rckSUc_e hk 0) = B (rckSUc_e' hk 1) (rckSUc_e' hk 1) := by
  have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 0) (rckSUc_e' hk 1)
  simp [rckSUc_e'_one_ne_zero hk, rckSUc_e_zero_ne_one hk] at h
  exact h

theorem rckSUc_B_eq_01 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    B (rckSUc_e hk 0) (rckSUc_e hk 1) = B (rckSUc_e' hk 1) (rckSUc_e' hk 0) := by
  have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 0) (rckSUc_e' hk 0)
  simp [rckSUc_e'_zero_ne_one hk, rckSUc_e_zero_ne_one hk] at h
  exact h

theorem rckSUc_B_eq_10 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    B (rckSUc_e hk 1) (rckSUc_e hk 0) = B (rckSUc_e' hk 0) (rckSUc_e' hk 1) := by
  have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 1) (rckSUc_e' hk 1)
  simp [rckSUc_e'_one_ne_zero hk, rckSUc_e_one_ne_zero hk] at h
  exact h

theorem rckSUc_B_eq_11 (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    B (rckSUc_e hk 1) (rckSUc_e hk 1) = B (rckSUc_e' hk 0) (rckSUc_e' hk 0) := by
  have h := rckSUc_hBN_apply hk B hBN (rckSUc_e hk 1) (rckSUc_e' hk 0)
  simp [rckSUc_e'_zero_ne_one hk, rckSUc_e_one_ne_zero hk] at h
  exact h

@[expose] noncomputable def rckSUc_g (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    Matrix (Fin 2) (Fin 2) SUF := B.submatrix (rckSUc_e hk) (rckSUc_e hk)

@[expose] noncomputable def rckSUc_h (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    Matrix (Fin 2) (Fin 2) SUF := B.submatrix (rckSUc_e' hk) (rckSUc_e' hk)

@[expose] noncomputable def rckSUc_gstar (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF) :
    Matrix (Fin 2) (Fin 2) SUF := conjTr SUσ (rckSUc_g hk B)

theorem rckSUc_conjTr_BJB_apply (B : Matrix (Fin k) (Fin k) SUF) (i j : Fin k) :
    (conjTr SUσ B * rckSUc_J k * B) i j =
      ∑ p, SUσ (B p i) * B (Fin.rev p) j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro p _
  have h1 : (rckSUc_J k * B) p j = B (Fin.rev p) j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev p)]
    · simp [rckSUc_J, antidiag, Fin.rev_rev]
    · intro q _ hq; simp [rckSUc_J, antidiag, hq]
    · intro hp; exact absurd (Finset.mem_univ (Fin.rev p)) hp
  rw [h1, conjTr_apply]

theorem rckSUc_sum_e {M : Type*} [AddCommMonoid M] (hk : 4 ≤ k) (f : Fin k → M)
    (h : ∀ p, p ≠ rckSUc_e hk 0 → p ≠ rckSUc_e hk 1 → f p = 0) :
    ∑ p, f p = f (rckSUc_e hk 0) + f (rckSUc_e hk 1) := by
  have hsub : ({rckSUc_e hk 0, rckSUc_e hk 1} : Finset (Fin k)) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_subset hsub (by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    push Not at hx
    exact h x hx.1 hx.2)]
  rw [Finset.sum_pair (rckSUc_e_zero_ne_one hk)]

theorem rckSUc_gstar_mul_h (hk : 4 ≤ k) (B : Matrix (Fin k) (Fin k) SUF)
    (hB : conjTr SUσ B * rckSUc_J k * B = rckSUc_J k)
    (hBN : B * rckSUc_N hk = rckSUc_N hk * B) :
    rckSUc_gstar hk B * rckSUc_h hk B = 1 := by
  ext a b
  have hiso := congrFun (congrFun hB (rckSUc_e hk a)) (rckSUc_e' hk b)
  rw [rckSUc_conjTr_BJB_apply] at hiso
  have hanti : rckSUc_J k (rckSUc_e hk a) (rckSUc_e' hk b) = if b = a then 1 else 0 := by
    change (if rckSUc_e' hk b = rckSUc_e' hk a then (1 : SUF) else 0) = if b = a then 1 else 0
    by_cases hab : b = a
    · subst hab; simp
    · have hne : rckSUc_e' hk b ≠ rckSUc_e' hk a := fun hh =>
        hab (rckSUc_e'_injective hk hh)
      simp [hab, hne]
  rw [hanti] at hiso
  have hcollapse :
      (∑ p, SUσ (B p (rckSUc_e hk a)) * B (Fin.rev p) (rckSUc_e' hk b))
        = SUσ (B (rckSUc_e hk 0) (rckSUc_e hk a)) * B (rckSUc_e' hk 0) (rckSUc_e' hk b)
          + SUσ (B (rckSUc_e hk 1) (rckSUc_e hk a))
            * B (rckSUc_e' hk 1) (rckSUc_e' hk b) := by
    refine rckSUc_sum_e hk (fun p =>
      SUσ (B p (rckSUc_e hk a)) * B (Fin.rev p) (rckSUc_e' hk b)) ?_
    intro p hp0 hp1
    have hpa : B p (rckSUc_e hk a) = 0 := by
      fin_cases a
      · exact (rckSUc_B_col_of_ne hk B hBN p hp0 hp1).1
      · exact (rckSUc_B_col_of_ne hk B hBN p hp0 hp1).2
    rw [hpa, map_zero, zero_mul]
  rw [hcollapse] at hiso
  rw [Matrix.mul_apply]
  simp only [rckSUc_gstar, rckSUc_h, rckSUc_g, conjTr_apply, Matrix.submatrix_apply,
    Fin.sum_univ_two, Matrix.one_apply]
  rw [hiso]
  by_cases hab : a = b <;> simp [hab, eq_comm]

end CFSG.StandardType.RCKK1IIISU
