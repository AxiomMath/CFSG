module

public import CFSG.LocalAnalysis.WeakClosure81.SixFourteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.WeakClosure81
open scoped TensorProduct

theorem s16c1610_card_GL_two (m : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) =
      ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ)) := by
  rw [Matrix.card_GL_field]
  simp only [ZMod.card]

theorem s16c1610_card_SL_four (m : ℕ) (hm : 1 ≤ m) :
    3 * Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) =
      ∏ i : Fin m, (4 ^ m - 4 ^ (i : ℕ)) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  have hqcard : Nat.card (GaloisField 2 2) = 4 := by
    rw [Nat.card_eq_fintype_card, hq]
  have hunits : Nat.card (GaloisField 2 2)ˣ = 3 := by
    rw [Nat.card_units, hqcard]
  have hSL := Matrix.card_SL_mul_card_units (n := Fin m) (R := GaloisField 2 2)
  rw [Matrix.card_GL_field, hq, hunits, mul_comm] at hSL
  exact hSL

private def s16c1610_gltwo (m : ℕ) : ℕ := ∏ i : Fin m, (2 ^ m - 2 ^ (i : ℕ))

private theorem s16c1610_gltwo_succ (m : ℕ) :
    s16c1610_gltwo (m + 1) = (2 ^ (m + 1) - 1) * 2 ^ m * s16c1610_gltwo m := by
  unfold s16c1610_gltwo
  rw [Fin.prod_univ_succAbove _ (0 : Fin (m + 1))]
  have h0 : 2 ^ (m + 1) - 2 ^ ((0 : Fin (m + 1)) : ℕ) = 2 ^ (m + 1) - 1 := by simp
  rw [h0]
  have hinner : ∀ j : Fin m,
      2 ^ (m + 1) - 2 ^ ((Fin.succAbove (0 : Fin (m + 1)) j : Fin (m + 1)) : ℕ) =
        2 * (2 ^ m - 2 ^ (j : ℕ)) := by
    intro j
    have hj : ((Fin.succAbove (0 : Fin (m + 1)) j : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := by
      simp [Fin.succAbove_zero]
    rw [hj, pow_succ, pow_succ]
    simp only [Nat.mul_sub, Nat.sub_mul]
    ring
  simp only [hinner]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem s16c1610_gltwo_step (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k + 1) * 2 ^ (k * k) + 2 ^ k * 2 ^ (k * k - k + 1) ≤
      (2 ^ (k + 1) - 1) * (2 ^ (k * k) + 2 ^ (k * k - k + 1)) := by
  set A := 2 ^ (k * k) with hA
  set B := 2 ^ (k * k - k + 1) with hB
  have hkM : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
  have hexp : k + (k * k - k + 1) = k * k + 1 := by omega
  have hAB : 2 ^ k * B = 2 * A := by
    rw [hA, hB, ← pow_add, hexp, pow_succ]
    ring
  have hBA : B ≤ A := by
    rw [hA, hB]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : (2 ^ (k + 1) - 1) * (A + B) = 2 ^ (k + 1) * (A + B) - (A + B) := by
    rw [Nat.sub_mul, one_mul]
  rw [hsub]
  have hle : A + B ≤ 2 ^ (k + 1) * (A + B) := Nat.le_mul_of_pos_left _ (by positivity)
  rw [Nat.le_sub_iff_add_le hle, mul_add]
  have hP : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ']
  have hk2 : 2 ≤ 2 ^ k := by
    rw [show (2 : ℕ) = 2 ^ 1 from rfl]
    exact Nat.pow_le_pow_right (by norm_num) hk
  nlinarith [hAB, hBA, hP, hk2]

private theorem s16c1610_gltwo_key (k : ℕ) (hk : 1 ≤ k) :
    2 ^ (k * k + 2 * k + 1) + 2 ^ (k * k + k + 1) ≤
      (2 ^ (k + 1) - 1) * 2 ^ k * (2 ^ (k * k) + 2 ^ (k * k - k + 1)) := by
  have hstep := s16c1610_gltwo_step k hk
  have hmul := Nat.mul_le_mul_left (2 ^ k) hstep
  have e1 : k * k + 2 * k + 1 = k * k + (k + (k + 1)) := by ring
  have e2 : k * k + k + 1 = (k * k - k + 1) + (k + k) := by
    have h : k ≤ k * k := Nat.le_mul_of_pos_left k (by omega)
    omega
  calc 2 ^ (k * k + 2 * k + 1) + 2 ^ (k * k + k + 1)
      = 2 ^ k * (2 ^ (k + 1) * 2 ^ (k * k) + 2 ^ k * 2 ^ (k * k - k + 1)) := by
        rw [e1, e2]
        simp only [pow_add]
        ring
    _ ≤ 2 ^ k * ((2 ^ (k + 1) - 1) * (2 ^ (k * k) + 2 ^ (k * k - k + 1))) := hmul
    _ = (2 ^ (k + 1) - 1) * 2 ^ k * (2 ^ (k * k) + 2 ^ (k * k - k + 1)) := by ring

private theorem s16c1610_gltwo_bound (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (m * m) + 2 ^ (m * m - m + 1) ≤ 4 * s16c1610_gltwo m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [s16c1610_gltwo, Fin.prod_univ_two]
  | succ k hk ih =>
    have hkey := s16c1610_gltwo_key k (by omega)
    rw [s16c1610_gltwo_succ]
    have h1 : 4 * ((2 ^ (k + 1) - 1) * 2 ^ k * s16c1610_gltwo k) =
        (2 ^ (k + 1) - 1) * 2 ^ k * (4 * s16c1610_gltwo k) := by ring
    rw [h1]
    have hexp1 : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    have hexp2 : (k + 1) * (k + 1) - (k + 1) + 1 = k * k + k + 1 := by
      have h : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      rw [h, Nat.add_sub_cancel]
      ring
    rw [hexp2, hexp1]
    exact le_trans hkey (Nat.mul_le_mul_left ((2 ^ (k + 1) - 1) * 2 ^ k) ih)

theorem s16c1610_two_pow_le_card_GL_two (m : ℕ) :
    2 ^ (m * m - 2) ≤ Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
  rw [s16c1610_card_GL_two]
  rcases Nat.lt_or_ge m 2 with hm | hm
  · interval_cases m <;> norm_num [Fin.prod_univ_one, Fin.prod_univ_zero]
  · have hbound := s16c1610_gltwo_bound m hm
    have h4 : 2 ^ (m * m) ≤ 4 * s16c1610_gltwo m :=
      le_trans (Nat.le_add_right _ _) hbound
    have hm2 : 2 ≤ m * m := by nlinarith
    have hpow : 4 * 2 ^ (m * m - 2) = 2 ^ (m * m) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
      congr 1
      omega
    have : 4 * 2 ^ (m * m - 2) ≤ 4 * s16c1610_gltwo m := by rw [hpow]; exact h4
    exact Nat.le_of_mul_le_mul_left this (by norm_num)

private def s16c1610_slfour (m : ℕ) : ℕ := ∏ i : Fin m, (4 ^ m - 4 ^ (i : ℕ))

private theorem s16c1610_slfour_succ (m : ℕ) :
    s16c1610_slfour (m + 1) = (4 ^ (m + 1) - 1) * 4 ^ m * s16c1610_slfour m := by
  unfold s16c1610_slfour
  rw [Fin.prod_univ_succAbove _ (0 : Fin (m + 1))]
  have h0 : 4 ^ (m + 1) - 4 ^ ((0 : Fin (m + 1)) : ℕ) = 4 ^ (m + 1) - 1 := by simp
  rw [h0]
  have hinner : ∀ j : Fin m,
      4 ^ (m + 1) - 4 ^ ((Fin.succAbove (0 : Fin (m + 1)) j : Fin (m + 1)) : ℕ) =
        4 * (4 ^ m - 4 ^ (j : ℕ)) := by
    intro j
    have hj : ((Fin.succAbove (0 : Fin (m + 1)) j : Fin (m + 1)) : ℕ) = (j : ℕ) + 1 := by
      simp [Fin.succAbove_zero]
    rw [hj, pow_succ, pow_succ]
    simp only [Nat.mul_sub, Nat.sub_mul]
    ring
  simp only [hinner]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

private theorem s16c1610_sl_exp (k : ℕ) (hk : 2 ≤ k) :
    2 * k + (2 * (k * k) - 2 * k - 1) = 2 * (k * k) - 1 := by
  have h : 2 * k + 1 ≤ 2 * (k * k) := by nlinarith
  rw [Nat.sub_sub, ← Nat.add_sub_assoc h, Nat.add_sub_add_left]

private theorem s16c1610_slfour_step (k : ℕ) (hk : 2 ≤ k) :
    2 ^ (2 * k + 2) * (3 * 2 ^ (2 * (k * k) - 1)) +
        2 ^ (2 * k) * (3 * 2 ^ (2 * (k * k) - 2 * k - 1)) ≤
      (2 ^ (2 * k + 2) - 1) *
        (3 * 2 ^ (2 * (k * k) - 1) + 3 * 2 ^ (2 * (k * k) - 2 * k - 1)) := by
  set A := 3 * 2 ^ (2 * (k * k) - 1) with hA
  set B := 3 * 2 ^ (2 * (k * k) - 2 * k - 1) with hB
  have hYB : 2 ^ (2 * k) * B = A := by
    rw [hA, hB, ← mul_assoc, mul_comm (2 ^ (2 * k)) 3, mul_assoc, ← pow_add,
      s16c1610_sl_exp k hk]
  have hBA : B ≤ A := by rw [← hYB]; exact Nat.le_mul_of_pos_left B (by positivity)
  have hP : 2 ^ (2 * k + 2) = 4 * 2 ^ (2 * k) := by
    rw [show 2 * k + 2 = 2 * k + 2 by omega, pow_add]
    ring
  have hsub : (2 ^ (2 * k + 2) - 1) * (A + B) = 2 ^ (2 * k + 2) * (A + B) - (A + B) := by
    rw [Nat.sub_mul, one_mul]
  rw [hsub]
  have hle : A + B ≤ 2 ^ (2 * k + 2) * (A + B) := Nat.le_mul_of_pos_left _ (by positivity)
  rw [Nat.le_sub_iff_add_le hle, mul_add]
  nlinarith [hYB, hBA, hP]

private theorem s16c1610_slfour_key (k : ℕ) (hk : 2 ≤ k) :
    3 * 2 ^ (2 * ((k + 1) * (k + 1)) - 1) +
        3 * 2 ^ (2 * ((k + 1) * (k + 1)) - 2 * (k + 1) - 1) ≤
      (4 ^ (k + 1) - 1) * 4 ^ k *
        (3 * 2 ^ (2 * (k * k) - 1) + 3 * 2 ^ (2 * (k * k) - 2 * k - 1)) := by
  have hstep := s16c1610_slfour_step k hk
  have hmul := Nat.mul_le_mul_left (2 ^ (2 * k)) hstep
  have hh : 2 * ((k + 1) * (k + 1)) = 2 * (k * k) + 4 * k + 2 := by ring
  have e1 : 2 * ((k + 1) * (k + 1)) - 1 = 2 * k + (2 * k + 2 + (2 * (k * k) - 1)) := by
    have hM : 1 ≤ 2 * (k * k) := by nlinarith
    rw [hh]
    omega
  have e2 : 2 * ((k + 1) * (k + 1)) - 2 * (k + 1) - 1 =
      2 * k + (2 * k + (2 * (k * k) - 2 * k - 1)) := by
    have hM : 2 * k + 1 ≤ 2 * (k * k) := by nlinarith
    have h2 : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hh, h2]
    omega
  calc 3 * 2 ^ (2 * ((k + 1) * (k + 1)) - 1) +
        3 * 2 ^ (2 * ((k + 1) * (k + 1)) - 2 * (k + 1) - 1)
      = 2 ^ (2 * k) * (2 ^ (2 * k + 2) * (3 * 2 ^ (2 * (k * k) - 1)) +
          2 ^ (2 * k) * (3 * 2 ^ (2 * (k * k) - 2 * k - 1))) := by
        rw [e1, e2]
        simp only [pow_add]
        ring
    _ ≤ 2 ^ (2 * k) * ((2 ^ (2 * k + 2) - 1) *
          (3 * 2 ^ (2 * (k * k) - 1) + 3 * 2 ^ (2 * (k * k) - 2 * k - 1))) := hmul
    _ = (4 ^ (k + 1) - 1) * 4 ^ k *
          (3 * 2 ^ (2 * (k * k) - 1) + 3 * 2 ^ (2 * (k * k) - 2 * k - 1)) := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_mul,
          show 2 * (k + 1) = 2 * k + 2 by ring]
        ring

private theorem s16c1610_slfour_bound (m : ℕ) (hm : 2 ≤ m) :
    3 * 2 ^ (2 * (m * m) - 1) + 3 * 2 ^ (2 * (m * m) - 2 * m - 1) ≤
      4 * s16c1610_slfour m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [s16c1610_slfour, Fin.prod_univ_two]
  | succ k hk ih =>
    have hkey := s16c1610_slfour_key k hk
    rw [s16c1610_slfour_succ]
    have h1 : 4 * ((4 ^ (k + 1) - 1) * 4 ^ k * s16c1610_slfour k) =
        (4 ^ (k + 1) - 1) * 4 ^ k * (4 * s16c1610_slfour k) := by ring
    rw [h1]
    exact le_trans hkey (Nat.mul_le_mul_left ((4 ^ (k + 1) - 1) * 4 ^ k) ih)

theorem s16c1610_two_pow_le_card_SL_four (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (2 * m * m - 3) ≤ Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
  rw [show 2 * m * m = 2 * (m * m) by ring]
  have hf : s16c1610_slfour m =
      3 * Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
    rw [s16c1610_slfour]
    exact (s16c1610_card_SL_four m (by omega)).symm
  have hbound := s16c1610_slfour_bound m hm
  have hA : 3 * 2 ^ (2 * (m * m) - 1) ≤
      12 * Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) := by
    have h := le_trans (Nat.le_add_right _ _) hbound
    rw [hf] at h
    nlinarith
  have h4 : 4 * 2 ^ (2 * (m * m) - 3) = 2 ^ (2 * (m * m) - 1) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]
    congr 1
    have : 3 ≤ 2 * (m * m) := by nlinarith
    omega
  have h12 : 3 * 2 ^ (2 * (m * m) - 1) = 12 * 2 ^ (2 * (m * m) - 3) := by
    rw [← h4]
    ring
  rw [h12] at hA
  exact Nat.le_of_mul_le_mul_left hA (by norm_num)

section Concl

variable {W : Type} [CommGroup W]

theorem s16c1610_rk_eq_of_card {m : ℕ} (h : Nat.card W = 4 ^ m) : rk W = 2 * m := by
  unfold rk
  rw [h, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, padicValNat.prime_pow]

private noncomputable def s16c1610_permCore3Proj :
    ↥(CFSG.Quasithin.permCore 3) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun y := fun i => (y : Fin 3 → ZMod 2) i.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem s16c1610_permCore3Proj_bijective :
    Function.Bijective s16c1610_permCore3Proj := by
  have key : ∀ p0 p1 p2 : ZMod 2, p0 + p1 + p2 = 0 → p2 = p0 + p1 := by decide
  constructor
  · intro y y' h
    apply Subtype.ext
    have hy : ∑ i, (y : Fin 3 → ZMod 2) i = 0 := y.2
    have hy' : ∑ i, (y' : Fin 3 → ZMod 2) i = 0 := y'.2
    rw [Fin.sum_univ_three] at hy hy'
    have h0 : (y : Fin 3 → ZMod 2) 0 = (y' : Fin 3 → ZMod 2) 0 := congrFun h 0
    have h1 : (y : Fin 3 → ZMod 2) 1 = (y' : Fin 3 → ZMod 2) 1 := congrFun h 1
    have h2 := key _ _ _ hy
    have h2' := key _ _ _ hy'
    funext j
    fin_cases j
    · exact h0
    · exact h1
    · show (y : Fin 3 → ZMod 2) 2 = (y' : Fin 3 → ZMod 2) 2
      rw [h2, h2', h0, h1]
  · intro a
    refine ⟨⟨![a 0, a 1, a 0 + a 1], ?_⟩, ?_⟩
    · change ∑ i, (![a 0, a 1, a 0 + a 1] : Fin 3 → ZMod 2) i = 0
      rw [Fin.sum_univ_three]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      generalize a 0 = p0
      generalize a 1 = p1
      revert p0 p1
      decide
    · funext i
      fin_cases i <;> rfl

private noncomputable def s16c1610_permCore3Equiv :
    ↥(CFSG.Quasithin.permCore 3) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofBijective s16c1610_permCore3Proj s16c1610_permCore3Proj_bijective

theorem s16c1610_card_of_isTensorS3L2 {G : Subgroup (MulAut W)} {m : ℕ}
    (h : IsTensorS3L2 W G m) :
    Nat.card G = 6 * Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) ∧
      Nat.card W = 4 ^ m := by
  obtain ⟨φ, ψ, -⟩ := h
  constructor
  · calc Nat.card G
        = Nat.card (Equiv.Perm (Fin 3) ×
            Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := Nat.card_congr φ.toEquiv
      _ = Nat.card (Equiv.Perm (Fin 3)) *
            Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) :=
          Nat.card_prod _ _
      _ = 6 * Nat.card (Matrix.GeneralLinearGroup (Fin m) (ZMod 2)) := by
          rw [Nat.card_perm, Nat.card_fin]
          have : Nat.factorial 3 = 6 := by decide
          rw [this]
  · have eT : (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) ≃ₗ[ZMod 2]
        ((Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin m → ZMod 2)) :=
      TensorProduct.congr s16c1610_permCore3Equiv
        (LinearEquiv.refl (ZMod 2) (Fin m → ZMod 2))
    have b : Module.Basis (Fin 2 × Fin m) (ZMod 2)
        ((Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin m → ZMod 2)) :=
      (Pi.basisFun (ZMod 2) (Fin 2)).tensorProduct (Pi.basisFun (ZMod 2) (Fin m))
    have e : (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) ≃ₗ[ZMod 2]
        (Fin 2 × Fin m → ZMod 2) := eT.trans b.equivFun
    calc Nat.card W = Nat.card (Multiplicative
          (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2))) :=
          Nat.card_congr ψ.toEquiv
      _ = Nat.card (↥(CFSG.Quasithin.permCore 3) ⊗[ZMod 2] (Fin m → ZMod 2)) :=
          Nat.card_congr Multiplicative.toAdd
      _ = Nat.card (Fin 2 × Fin m → ZMod 2) := Nat.card_congr e.toEquiv
      _ = Nat.card (ZMod 2) ^ Nat.card (Fin 2 × Fin m) := Nat.card_fun
      _ = 2 ^ (2 * m) := by
          rw [Nat.card_zmod]
          simp only [Nat.card_prod, Nat.card_fin]
      _ = 4 ^ m := by rw [show (4 : ℕ) = 2 ^ 2 from rfl, pow_mul]

theorem s16c1610_card_of_isNatGL4 {H : Subgroup (MulAut W)} {m : ℕ} (h : IsNatGL4 W H m) :
    Nat.card H = Nat.card (Matrix.GeneralLinearGroup (Fin m) (GaloisField 2 2)) ∧
      Nat.card W = 4 ^ m := by
  obtain ⟨φ, ψ, -⟩ := h
  constructor
  · exact Nat.card_congr φ.toEquiv
  · calc Nat.card W = Nat.card (Multiplicative (Fin m → GaloisField 2 2)) :=
          Nat.card_congr ψ.toEquiv
      _ = Nat.card (Fin m → GaloisField 2 2) := Nat.card_congr Multiplicative.toAdd
      _ = Nat.card (GaloisField 2 2) ^ Nat.card (Fin m) := Nat.card_fun
      _ = 4 ^ m := by
          rw [Nat.card_fin, GaloisField.card 2 2 (by norm_num)]
          rfl

theorem s16c1610_card_of_isNatSL4 {H : Subgroup (MulAut W)} {m : ℕ} (h : IsNatSL4 W H m) :
    Nat.card H = Nat.card (Matrix.SpecialLinearGroup (Fin m) (GaloisField 2 2)) ∧
      Nat.card W = 4 ^ m := by
  obtain ⟨φ, ψ, -⟩ := h
  constructor
  · exact Nat.card_congr φ.toEquiv
  · calc Nat.card W = Nat.card (Multiplicative (Fin m → GaloisField 2 2)) :=
          Nat.card_congr ψ.toEquiv
      _ = Nat.card (Fin m → GaloisField 2 2) := Nat.card_congr Multiplicative.toAdd
      _ = Nat.card (GaloisField 2 2) ^ Nat.card (Fin m) := Nat.card_fun
      _ = 4 ^ m := by
          rw [Nat.card_fin, GaloisField.card 2 2 (by norm_num)]
          rfl

theorem s16c1610_card_of_isS6Cover {G X : Subgroup (MulAut W)} (hXG : X ≤ G)
    (h : IsS6Cover W G X) : Nat.card G = 720 * Nat.card X := by
  obtain ⟨φ, hsurj, hker⟩ := h
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hrange : Nat.card φ.range = 720 := by
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_perm, Nat.card_fin]
    have : Nat.factorial 6 = 720 := by decide
    rw [this]
  have hker' : Nat.card φ.ker = Nat.card X := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXG).toEquiv
  rw [hker', hrange, mul_comm] at hcard
  exact hcard.symm

theorem s16c1610_not_concl614_of_rk_odd {G X : Subgroup (MulAut W)} (hodd : Odd (rk W)) :
    ¬ Concl614 W G X := by
  rintro ((⟨m, h⟩ | ⟨m, h⟩ | ⟨-, h⟩) | ⟨m, h⟩)
  · exact (Nat.not_even_iff_odd.2 hodd)
      ⟨m, by rw [s16c1610_rk_eq_of_card (s16c1610_card_of_isTensorS3L2 h).2]; ring⟩
  · exact (Nat.not_even_iff_odd.2 hodd)
      ⟨m, by rw [s16c1610_rk_eq_of_card (s16c1610_card_of_isNatGL4 h).2]; ring⟩
  · have h6 : rk W = 2 * 3 := s16c1610_rk_eq_of_card (m := 3) (by rw [h]; norm_num)
    exact (Nat.not_even_iff_odd.2 hodd) ⟨3, by rw [h6]⟩
  · exact (Nat.not_even_iff_odd.2 hodd)
      ⟨m, by rw [s16c1610_rk_eq_of_card (s16c1610_card_of_isNatSL4 h).2]; ring⟩

end Concl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
