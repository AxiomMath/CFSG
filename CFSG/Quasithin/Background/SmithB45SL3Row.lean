module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.SmithB45SL3Herm
public import CFSG.Quasithin.Background.HL3NineM
public import CFSG.Quasithin.Background.SmithB42SL3Aut

public section

namespace CFSG.Quasithin

namespace B45SL3

open CFSG.QuasithinUnique.Setup.X7a
open scoped MatrixGroups Matrix

section Quad

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem rhoT_mem_img_of_mul_self (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : GL (Fin 3) K} (h : rhoT hK A * rhoT hK A = 1) : rhoT hK A ∈ img hK := by
  obtain ⟨A', hA', hA'2⟩ := exists_sq_eq_one hn hK h
  have hdet : (A' : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    apply eq_one_of_sq_eq_one
    rw [← Matrix.det_mul, ← Units.val_mul, hA'2, Units.val_one, Matrix.det_one]
  rw [← hA', ← rho_mk hK hdet]
  exact ⟨_, rfl⟩

theorem false_of_quadratic_twisted (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (A : GL (Fin 3) K)
    (hq : ∀ X : HMod n K, (rhoT hK A * fldAut (bar n) : MulAut (HMod n K))
      (rho hK (up3 0 0 1) X * X⁻¹) = rho hK (up3 0 0 1) X * X⁻¹) : False := by
  obtain ⟨l, hl⟩ := exists_bar_ne hn hK
  have hY₁ : (conjM n !![0, 0, 0; 0, 0, 1; 0, 1, (0 : K)])ᵀ = !![0, 0, 0; 0, 0, 1; 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM]
  have hY₂ : (conjM n !![0, 0, 0; 0, 0, l; 0, bar n l, (0 : K)])ᵀ =
      !![0, 0, 0; 0, 0, l; 0, bar n l, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM, bar_bar hK]
  have hY₃ : (conjM n !![0, 0, 0; 0, 1, 0; 0, 0, (0 : K)])ᵀ = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [conjM]
  have e₁ := congrArg mat (hq (mkH _ hY₁))
  have e₂ := congrArg mat (hq (mkH _ hY₂))
  have e₃ := congrArg mat (hq (mkH _ hY₃))
  have e100 := congrFun (congrFun e₁ 0) 0
  have e120 := congrFun (congrFun e₁ 2) 0
  have e200 := congrFun (congrFun e₂ 0) 0
  have e220 := congrFun (congrFun e₂ 2) 0
  have e300 := congrFun (congrFun e₃ 0) 0
  simp only [MulAut.mul_apply, mat_rhoT, mat_fldAut, mat_mul, mat_inv, mat_rho, mat_mkH, tw,
    up3_coe, upMat, conjM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.add_apply, Matrix.neg_apply] at e100 e120 e200 e220 e300
  simp at e100 e120 e200 e220 e300
  rw [bar_bar hK] at e200 e220
  have hl' : l - bar n l ≠ 0 := sub_ne_zero.mpr (Ne.symm hl)
  have hu :
      (A : Matrix (Fin 3) (Fin 3) K) 0 0 * bar n ((A : Matrix (Fin 3) (Fin 3) K) 0 2) = 0 := by
    have : ((A : Matrix (Fin 3) (Fin 3) K) 0 0 * bar n ((A : Matrix (Fin 3) (Fin 3) K) 0 2)) *
        (l - bar n l) = 0 := by linear_combination l * e100 - e200
    exact (mul_eq_zero.mp this).resolve_right hl'
  have hp :
      (A : Matrix (Fin 3) (Fin 3) K) 2 0 * bar n ((A : Matrix (Fin 3) (Fin 3) K) 0 2) = 1 := by
    have : ((A : Matrix (Fin 3) (Fin 3) K) 2 0 * bar n ((A : Matrix (Fin 3) (Fin 3) K) 0 2) - 1) *
        (l - bar n l) = 0 := by linear_combination l * e120 - e220
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hl')
  have hb : bar n ((A : Matrix (Fin 3) (Fin 3) K) 0 2) ≠ 0 := fun h => by
    rw [h, mul_zero] at hp
    exact zero_ne_one hp
  have h00 : (A : Matrix (Fin 3) (Fin 3) K) 0 0 = 0 := (mul_eq_zero.mp hu).resolve_right hb
  rw [h00, map_zero] at e300
  simp at e300

theorem mem_img_of_quadratic (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {t : SL(3, K)}
    (ht1 : t ≠ 1) (ht2 : t * t = 1) {x : MulAut (HMod n K)} (hx : x ∈ norm hK)
    (hx2 : x * x = 1) (hq : ∀ X : HMod n K, x (rho hK t X * X⁻¹) = rho hK t X * X⁻¹) :
    x ∈ img hK := by
  obtain ⟨g, hg⟩ := exists_conj_transvection t ht1 ht2
  set x₀ := (rho hK g)⁻¹ * x * rho hK g with hx₀
  have himg : ∀ h : SL(3, K), rho hK h ∈ norm hK := fun h =>
    Subgroup.le_normalizer ⟨h, rfl⟩
  have hx₀n : x₀ ∈ norm hK :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (himg g)) hx) (himg g)
  have hx₀2 : x₀ * x₀ = 1 := by
    rw [hx₀]
    calc (rho hK g)⁻¹ * x * rho hK g * ((rho hK g)⁻¹ * x * rho hK g) =
        (rho hK g)⁻¹ * (x * x) * rho hK g := by group
      _ = 1 := by rw [hx2, mul_one, inv_mul_cancel]
  have hq₀ : ∀ X : HMod n K, x₀ (rho hK (up3 0 0 1) X * X⁻¹) = rho hK (up3 0 0 1) X * X⁻¹ := by
    intro X
    have hcomm : rho hK g * rho hK (up3 0 0 1) = rho hK t * rho hK g := by
      rw [← hg, ← map_mul, ← map_mul]
      congr 1
      group
    have h1 : rho hK g (rho hK (up3 0 0 1) X * X⁻¹) =
        rho hK t (rho hK g X) * (rho hK g X)⁻¹ := by
      rw [map_mul, map_inv, ← MulAut.mul_apply, hcomm, MulAut.mul_apply]
    show (rho hK g)⁻¹ (x (rho hK g (rho hK (up3 0 0 1) X * X⁻¹))) = _
    rw [h1, hq, ← h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hxeq : x = rho hK g * x₀ * (rho hK g)⁻¹ := by rw [hx₀]; group
  obtain ⟨A, h | h⟩ := exists_of_involution hn hK hx₀n hx₀2
  · rw [hxeq, h]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ⟨g, rfl⟩ ?_) (Subgroup.inv_mem _ ⟨g, rfl⟩)
    refine rhoT_mem_img_of_mul_self hn hK ?_
    rw [← h]
    exact hx₀2
  · exact (false_of_quadratic_twisted hn hK A (fun X => by rw [← h]; exact hq₀ X)).elim

end Quad

section Radical

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3

@[expose] def radSub (K : Type) [Field K] [CharP K 2] : Subgroup SL(3, K) where
  carrier := {g | ∃ x y : K, g = up3 x y 0}
  one_mem' := ⟨0, 0, up3_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨x, y, rfl⟩ ⟨X, Y, rfl⟩
    exact ⟨x + X, y + Y, by rw [up3_mul, zero_mul, add_zero, add_zero]⟩
  inv_mem' := by
    rintro _ ⟨x, y, rfl⟩
    refine ⟨x, y, inv_eq_of_mul_eq_one_right ?_⟩
    simp only [up3_mul, CharTwo.add_self_eq_zero, zero_mul, up3_zero]

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] in
theorem card_radSub : Nat.card ↥(radSub K) = Nat.card K ^ 2 := by
  have e : K × K ≃ ↥(radSub K) :=
    Equiv.ofBijective (fun p => ⟨up3 p.1 p.2 0, p.1, p.2, rfl⟩)
      ⟨fun p q h => by
        have := up3_inj (congrArg Subtype.val h)
        exact Prod.ext this.1 this.2.1,
       fun ⟨g, x, y, hg⟩ => ⟨(x, y), Subtype.ext hg.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, pow_two]

@[expose] def hermV1 (n : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 2 2 = 0}
  one_mem' := by simp [mat_one]
  mul_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_ofPred_eq, mat_mul, Matrix.add_apply] at hX hY ⊢
    rw [hX, hY, add_zero]
  inv_mem' := fun {X} hX => by
    simp only [Set.mem_ofPred_eq, mat_inv, Matrix.neg_apply] at hX ⊢
    rw [hX, neg_zero]

@[expose] def hermV0 (n : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup (HMod n K) where
  carrier := {X | mat X 2 2 = 0 ∧ mat X 0 2 = 0 ∧ mat X 1 2 = 0}
  one_mem' := by simp [mat_one]
  mul_mem' := fun {X Y} hX hY => by
    simp only [Set.mem_ofPred_eq, mat_mul, Matrix.add_apply] at hX hY ⊢
    rw [hX.1, hY.1, hX.2.1, hY.2.1, hX.2.2, hY.2.2, add_zero]
    exact ⟨rfl, rfl, rfl⟩
  inv_mem' := fun {X} hX => by
    simp only [Set.mem_ofPred_eq, mat_inv, Matrix.neg_apply] at hX ⊢
    rw [hX.1, hX.2.1, hX.2.2, neg_zero]
    exact ⟨rfl, rfl, rfl⟩

theorem mat_rho_up3 (hK : Nat.card K = (2 ^ n) ^ 2) (x y : K) (X : HMod n K) (i j : Fin 3) :
    mat (rho hK (up3 x y 0) X) i j = ∑ k, ∑ l, upMat x y 0 i k * mat X k l *
      bar n (upMat x y 0 j l) := by
  rw [mat_rho, tw, up3_coe, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, conjM, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem rho_up3_22 (hK : Nat.card K = (2 ^ n) ^ 2) (x y : K) (X : HMod n K) :
    mat (rho hK (up3 x y 0) X) 2 2 = mat X 2 2 := by
  rw [mat_rho_up3]
  simp [Fin.sum_univ_three, upMat]

theorem rho_up3_col (hK : Nat.card K = (2 ^ n) ^ 2) (x y : K) {X : HMod n K}
    (h : mat X 2 2 = 0) (i : Fin 3) : mat (rho hK (up3 x y 0) X) i 2 = mat X i 2 := by
  rw [mat_rho_up3]
  fin_cases i <;> simp [Fin.sum_univ_three, upMat, h]

theorem rho_up3_of_mem_hermV0 (hK : Nat.card K = (2 ^ n) ^ 2) (x y : K) {X : HMod n K}
    (hX : X ∈ hermV0 n K) : rho hK (up3 x y 0) X = X := by
  obtain ⟨h22, h02, h12⟩ := hX
  have h20 : mat X 2 0 = 0 := by rw [← herm_apply, h02, map_zero]
  have h21 : mat X 2 1 = 0 := by rw [← herm_apply, h12, map_zero]
  apply mat_injective
  ext i j
  rw [mat_rho_up3]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_three, upMat, h22, h02, h12, h20, h21]

theorem le_card_hermV0 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ (4 * n) ≤ Nat.card ↥(hermV0 n K) := by
  classical
  let Fq := {b : K // bar n b = b}
  let φ : Fq × Fq × K → ↥(hermV0 n K) := fun p =>
    ⟨mkH !![(p.1 : K), p.2.2, 0; bar n p.2.2, (p.2.1 : K), 0; 0, 0, 0] (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [conjM, p.1.2, p.2.1.2, bar_bar hK]),
      by simp [hermV0, mat_mkH]⟩
  have hφ : Function.Injective φ := by
    rintro ⟨a, d, b⟩ ⟨a', d', b'⟩ h
    have h' := congrArg (fun X : ↥(hermV0 n K) => mat (X : HMod n K)) h
    have h00 := congrFun (congrFun h' 0) 0
    have h11 := congrFun (congrFun h' 1) 1
    have h01 := congrFun (congrFun h' 0) 1
    simp only [φ, mat_mkH] at h00 h11 h01
    simp at h00 h11 h01
    exact Prod.ext (Subtype.ext h00) (Prod.ext (Subtype.ext h11) h01)
  have h := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod, Nat.card_prod, card_fixed hn hK, hK] at h
  calc 2 ^ (4 * n) = 2 ^ n * (2 ^ n * (2 ^ n) ^ 2) := by ring
    _ ≤ _ := h

noncomputable abbrev radImg (hK : Nat.card K = (2 ^ n) ^ 2) : Subgroup (MulAut (HMod n K)) :=
  (radSub K).map (rho hK)

theorem card_radImg (hK : Nat.card K = (2 ^ n) ^ 2) :
    Nat.card ↥(radImg hK) = Nat.card K ^ 2 := by
  have hinj : Function.Injective ((rho hK).comp (radSub K).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨g, x, y, rfl⟩ hg
    obtain ⟨c, -, hc⟩ := mem_scalars_of_rho_eq_one hK hg
    have h02 := congrFun (congrFun hc 0) 2
    have h12 := congrFun (congrFun hc 1) 2
    simp [up3_coe, upMat] at h02 h12
    apply Subtype.ext
    simp [h02, h12, up3_zero]
  have hrange : radImg hK = ((rho hK).comp (radSub K).subtype).range := by
    rw [radImg, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, card_radSub]

theorem hermV0_le_fixV (hK : Nat.card K = (2 ^ n) ^ 2) : hermV0 n K ≤ fixV (radImg hK) := by
  intro X hX
  rintro _ ⟨g, ⟨x, y, rfl⟩, rfl⟩
  exact rho_up3_of_mem_hermV0 hK x y hX

theorem commSeries_radImg_three (hK : Nat.card K = (2 ^ n) ^ 2) :
    commSeries (radImg hK) 3 = ⊥ := by
  have h1 : commSub ⊤ (radImg hK) ≤ hermV1 n K := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨_, ⟨g, ⟨x, y, rfl⟩, rfl⟩, w, -, rfl⟩
    show mat (rho hK (up3 x y 0) w * w⁻¹) 2 2 = 0
    rw [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply, rho_up3_22, add_neg_cancel]
  have h2 : commSub (hermV1 n K) (radImg hK) ≤ hermV0 n K := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨_, ⟨g, ⟨x, y, rfl⟩, rfl⟩, w, hw, rfl⟩
    have hw' : mat w 2 2 = 0 := hw
    refine ⟨?_, ?_, ?_⟩ <;> simp only [mat_mul, mat_inv, Matrix.add_apply, Matrix.neg_apply]
    · rw [rho_up3_22, add_neg_cancel]
    · rw [rho_up3_col hK x y hw', add_neg_cancel]
    · rw [rho_up3_col hK x y hw', add_neg_cancel]
  have h3 : commSub (hermV0 n K) (radImg hK) = ⊥ :=
    commSub_eq_bot_iff.mpr (hermV0_le_fixV hK)
  show commSub (commSub (commSub ⊤ (radImg hK)) (radImg hK)) (radImg hK) = ⊥
  rw [eq_bot_iff, ← h3]
  exact commSub_mono ((commSub_mono h1 le_rfl).trans h2) le_rfl

theorem isElemAbelian2_radImg (hK : Nat.card K = (2 ^ n) ^ 2) : IsElemAbelian2 (radImg hK) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g, ⟨x, y, rfl⟩, rfl⟩ _ ⟨g', ⟨x', y', rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, up3_mul, up3_mul]
    congr 2 <;> ring
  · rintro _ ⟨g, ⟨x, y, rfl⟩, rfl⟩
    rw [← map_pow, pow_two, up3_mul, CharTwo.add_self_eq_zero, zero_mul, add_zero,
      CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, up3_zero, map_one]

end Radical

section Transport

open CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H

variable {V W : Type} [CommGroup V] [CommGroup W]

theorem commSeries_map_congrHom (e : V ≃* W) (A : Subgroup (MulAut V)) (k : ℕ) :
    commSeries (A.map (congrHom e)) k = (commSeries A k).map e.toMonoidHom :=
  commSeries_map_mulAutCongr e A k

theorem congrHom_symm_comp (e : V ≃* W) :
    (congrHom e.symm).comp (congrHom e) = MonoidHom.id (MulAut V) := by
  ext x v
  simp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} [Finite V]

theorem qhatOf_le_of_model (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {G : Subgroup (MulAut V)} (e : V ≃* HMod n K) (himg : img hK ≤ G.map (congrHom e)) :
    qhatOf G ≤ (((5 / 4 : ℚ)) : WithTop ℚ) := by
  classical
  set A := (radImg hK).map (congrHom e.symm) with hA
  have hAG : A ≤ G := by
    have h1 : radImg hK ≤ G.map (congrHom e) :=
      (Subgroup.map_le_range (rho hK) (radSub K)).trans himg
    have h3 : (G.map (congrHom e)).map (congrHom e.symm) = G := by
      rw [Subgroup.map_map, congrHom_symm_comp, Subgroup.map_id]
    calc A ≤ (G.map (congrHom e)).map (congrHom e.symm) := Subgroup.map_mono h1
      _ = G := h3
  have hcard : Nat.card ↥A = 2 ^ (4 * n) := by
    rw [hA, card_map_congrHom, card_radImg, hK]
    ring
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    have : 1 < 2 ^ (4 * n) := Nat.one_lt_two_pow (by omega)
    omega
  have hA2 : IsA2 G A :=
    ⟨hAG, hA1, (isElemAbelian2_map_congrHom e.symm).2 (isElemAbelian2_radImg hK)⟩
  have hcub : commSeries A 3 = ⊥ := by
    rw [hA, commSeries_map_congrHom, commSeries_radImg_three, Subgroup.map_bot]
  refine kq_le_iff.2 ⟨A, hA2, hcub, ?_⟩
  have hrkA : rk ↥A = 4 * n := by
    unfold rk
    rw [hcard, padicValNat.prime_pow]
  have hrkV : rk (HMod n K) = 9 * n := by
    unfold rk
    rw [card_HMod hn hK, padicValNat.prime_pow]
  have hfix : 4 * n ≤ rk ↥(fixV (radImg hK)) := by
    have hle := Subgroup.card_le_of_le (hermV0_le_fixV hK)
    have h4 := (le_card_hermV0 hn hK).trans hle
    obtain ⟨j, hj⟩ : ∃ j, Nat.card ↥(fixV (radImg hK)) = 2 ^ j := by
      have hdvd : Nat.card ↥(fixV (radImg hK)) ∣ 2 ^ (9 * n) := by
        rw [← card_HMod hn hK]
        exact Subgroup.card_subgroup_dvd_card _
      exact (Nat.dvd_prime_pow Nat.prime_two).mp hdvd |>.imp fun j hj => hj.2
    unfold rk
    rw [hj, padicValNat.prime_pow]
    rw [hj] at h4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
  have hidx : rkIdx (fixV A) ≤ 5 * n := by
    rw [hA, rkIdx_fixV_map_congrHom]
    have := rk_add_rkIdx (fixV (radImg hK))
    omega
  unfold rAV
  rw [hrkA]
  have hpos : (0 : ℚ) < (4 * n : ℕ) := by exact_mod_cast (show 0 < 4 * n by omega)
  rw [div_le_iff₀ hpos]
  have : (rkIdx (fixV A) : ℚ) ≤ 5 * n := by exact_mod_cast hidx
  push_cast
  linarith

end Transport

section QuadBound

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open CFSG.Quasithin.B42SL3 (innerPart exists_lift_of_inner isTransvection_of_involution
  commute_of_rep quad_of_sub eq_smul_of_quadratic IsSingle locRep_sub_one_mul quadratic_entries
  frK_injective)

variable {F : Type} [Field F] [CharP F 2]

theorem locRep_sub_one_cases {ℓ : Bool × Bool} (hℓ : IsSingle ℓ) :
    ∃ h3 : locDim ℓ.1 ℓ.2 = 3,
      (∀ (j : ℕ) (t : SL(3, F)), t * t = 1 → ∀ c d, (locRep F ℓ.1 ℓ.2 j t - 1) c d =
          frK F j (((t : Matrix (Fin 3) (Fin 3) F) - 1) (Fin.cast h3 c) (Fin.cast h3 d))) ∨
      (∀ (j : ℕ) (t : SL(3, F)), t * t = 1 → ∀ c d, (locRep F ℓ.1 ℓ.2 j t - 1) c d =
          frK F j (((t : Matrix (Fin 3) (Fin 3) F) - 1) (Fin.cast h3 d) (Fin.cast h3 c))) := by
  rcases hℓ with rfl | rfl
  · refine ⟨rfl, Or.inl fun j t _ c d => ?_⟩
    have e : ∀ c' d' : Fin 3, (twistMat F j t - 1) c' d' =
        frK F j (((t : Matrix (Fin 3) (Fin 3) F) - 1) c' d') := by
      intro c' d'
      rw [Matrix.sub_apply, Matrix.sub_apply, twistMat_apply, map_sub, Matrix.one_apply]
      split_ifs <;> simp
    exact e c d
  · refine ⟨rfl, Or.inr fun j t ht c d => ?_⟩
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have e : ∀ c' d' : Fin 3, ((twistMat F j t⁻¹)ᵀ - 1) c' d' =
        frK F j (((t : Matrix (Fin 3) (Fin 3) F) - 1) d' c') := by
      intro c' d'
      rw [htinv, Matrix.sub_apply, Matrix.sub_apply, Matrix.transpose_apply, twistMat_apply,
        map_sub, Matrix.one_apply, Matrix.one_apply]
      by_cases h : c' = d'
      · subst h
        simp
      · simp [h, Ne.symm h]
    exact e c d

theorem locRep_sub_one_cast {ℓ ℓ' : Bool × Bool} (h : ℓ = ℓ') (j : ℕ) (g : SL(3, F))
    (c d : Fin (locDim ℓ.1 ℓ.2)) :
    (locRep F ℓ.1 ℓ.2 j g - 1) c d =
      (locRep F ℓ'.1 ℓ'.2 j g - 1) (Fin.cast (by rw [h]) c) (Fin.cast (by rw [h]) d) := by
  subst h
  rfl

variable [Fintype F] {f : ℕ}

theorem pow_eq_of_quadratic_row (hF : Fintype.card F = 2 ^ f) {m : ℕ} {a b : Fin f → Bool}
    {i i' : Fin f} (hii' : i ≠ i') (hi' : (i' : ℕ) = ((i : ℕ) + m) % f)
    (hsi : IsSingle (a i, b i)) (hsame : (a i', b i') = (a i, b i))
    (hrest : ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false))
    {t₁ t₂ : SL(3, F)} (ht1 : t₁ ≠ 1) (h1 : t₁ * t₁ = 1) (h2 : t₂ * t₂ = 1)
    (hcomm : t₁ * t₂ = t₂ * t₁)
    (hquad : (tensorRep (F := F) F a b t₂ - 1) * (tensorRep (F := F) F a b t₁ - 1) = 0)
    {μ : F} (hμ : (t₂ : Matrix (Fin 3) (Fin 3) F) - 1 = μ • ((t₁ : Matrix (Fin 3) (Fin 3) F) - 1)) :
    μ ^ 2 ^ m = μ := by
  classical
  have hsi' : IsSingle (a i', b i') := hsame ▸ hsi
  have hent : ∀ (c d : Fin (locDim (a i) (b i))) (c' d' : Fin (locDim (a i') (b i'))),
      (locRep F (a i) (b i) (i : ℕ) t₁ - 1) c d * (locRep F (a i') (b i') (i' : ℕ) t₂ - 1) c' d' +
        (locRep F (a i) (b i) (i : ℕ) t₂ - 1) c d *
          (locRep F (a i') (b i') (i' : ℕ) t₁ - 1) c' d' = 0 :=
    quadratic_entries (F := F) (fun p => (a p, b p)) (fun p => (p : ℕ)) hii' hrest
      (locRep_sub_one_mul hsi (i : ℕ) h1 h2 hcomm) (locRep_sub_one_mul hsi' (i' : ℕ) h1 h2 hcomm)
      hquad
  obtain ⟨h3, hcase⟩ := locRep_sub_one_cases (F := F) hsi
  have h3' : locDim (a i') (b i') = 3 := by
    have := congrArg (fun ℓ : Bool × Bool => locDim ℓ.1 ℓ.2) hsame
    simp only at this
    rw [this]
    exact h3
  set N := (t₁ : Matrix (Fin 3) (Fin 3) F) - 1 with hN
  have hN0 : N ≠ 0 := fun h => ht1 (Subtype.ext (sub_eq_zero.mp h))
  obtain ⟨r, s, hrs⟩ : ∃ r s, N r s ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN0 (Matrix.ext hcon)
  have hfr : ∀ (j : ℕ) (x : F), frK F j x = x ^ 2 ^ j := fun j x => by
    rw [frK_apply]
    rfl
  have hcast : locDim (a i') (b i') = locDim (a i) (b i) :=
    congrArg (fun ℓ : Bool × Bool => locDim ℓ.1 ℓ.2) hsame
  have hloc' : ∀ (t : SL(3, F)) (c d : Fin (locDim (a i') (b i'))),
      (locRep F (a i') (b i') (i' : ℕ) t - 1) c d =
        (locRep F (a i) (b i) (i' : ℕ) t - 1) (Fin.cast hcast c) (Fin.cast hcast d) :=
    fun t c d => locRep_sub_one_cast (F := F) hsame (i' : ℕ) t c d
  have hX : frK F i (N r s) * frK F i' (N r s) ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ (frK_injective (F := F) i)).mpr hrs)
      ((map_ne_zero_iff _ (frK_injective (F := F) i')).mpr hrs)
  have hN2 : ((t₂ : Matrix (Fin 3) (Fin 3) F) - 1) r s = μ * N r s := by
    rw [hμ]
    rfl
  have key : frK F i' μ = frK F i μ := by
    have hsum : (frK F i' μ + frK F i μ) * (frK F i (N r s) * frK F i' (N r s)) = 0 := by
      rcases hcase with hnat | hdual
      · have e := hent (Fin.cast h3.symm r) (Fin.cast h3.symm s) (Fin.cast h3'.symm r)
          (Fin.cast h3'.symm s)
        rw [hloc', hloc', hnat (i : ℕ) t₁ h1, hnat (i : ℕ) t₂ h2, hnat (i' : ℕ) t₁ h1,
          hnat (i' : ℕ) t₂ h2] at e
        simp only [Fin.cast_cast, Fin.cast_eq_self] at e
        rw [hN2, map_mul, map_mul] at e
        linear_combination e
      · have e := hent (Fin.cast h3.symm s) (Fin.cast h3.symm r) (Fin.cast h3'.symm s)
          (Fin.cast h3'.symm r)
        rw [hloc', hloc', hdual (i : ℕ) t₁ h1, hdual (i : ℕ) t₂ h2, hdual (i' : ℕ) t₁ h1,
          hdual (i' : ℕ) t₂ h2] at e
        simp only [Fin.cast_cast, Fin.cast_eq_self] at e
        rw [hN2, map_mul, map_mul] at e
        linear_combination e
    have h := (mul_eq_zero.mp hsum).resolve_right hX
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
    exact h
  rw [hfr, hfr, hi', ← pow_two_pow_mod hF, pow_add, pow_mul] at key
  apply frK_injective (F := F) i
  rw [hfr, hfr, ← pow_mul, mul_comm, pow_mul]
  exact key

end QuadBound

section RowBound

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply)
open CFSG.QuasithinUnique.Setup.X7b (toMatRep)
open CFSG.Quasithin.B42SL3 (innerPart exists_lift_of_inner isTransvection_of_involution
  commute_of_rep quad_of_sub eq_smul_of_quadratic IsSingle)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type} [Field F] [Fintype F] [CharP F 2] {f : ℕ}
  {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) SL(3, F) U) (hker : ∀ x : SL(3, F), ρ x = 1 → x ∈ scalars 3 F)
  (A : Subgroup (U ≃ₗ[ZMod 2] U)) (hA : ∀ a ∈ A, ∀ x : SL(3, F), ∃ y, Intertwines ρ a x y)
  [CFSG.IsElementaryAbelian 2 A]

theorem card_innerPart_le_of_row (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card F = (2 ^ m) ^ 2) (hirr : ρ.IsIrreducible)
    (hquad : ∀ a ∈ A, ∀ b ∈ A, ∀ w, b (a w - w) = a w - w) {n : ℕ}
    (bas : Module.Basis (Fin n) (ZMod 2) U) {a b : Fin f → Bool} {i i' : Fin f}
    (hii' : i ≠ i') (hi' : (i' : ℕ) = ((i : ℕ) + m) % f)
    (hsi : IsSingle (a i, b i)) (hsame : (a i', b i') = (a i, b i))
    (hrest : ∀ p, p ≠ i → p ≠ i' → (a p, b p) = (false, false))
    (W₀ : Subrepresentation (matRep (matMap (ZMod.castHom (dvd_refl 2) F) (toMatRep ρ bas))))
    (e₀ : W₀.toRepresentation.Equiv (matRep (tensorRep (F := F) F a b))) :
    Nat.card ↥(innerPart ρ hker A hA) ≤ 2 ^ m := by
  classical
  have hNat : Nat.card F = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  set I := innerPart ρ hker A hA with hI
  by_cases hbot : I = ⊥
  · rw [hbot, Subgroup.card_bot]
    exact Nat.one_le_two_pow
  obtain ⟨⟨a₀, ha₀I⟩, ha₀1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hbot
  have ha₀1 : a₀ ≠ 1 := fun h => ha₀1' (Subtype.ext h)
  have hlift : ∀ x : ↥I, ∃ t : SL(3, F), t * t = 1 ∧
      ∀ u, ((x : ↥A) : U ≃ₗ[ZMod 2] U) u = ρ t u :=
    fun x => exists_lift_of_inner ρ hker A hA hf hNat hirr x x.2
  choose t ht2 htρ using hlift
  set t₀ := t ⟨a₀, ha₀I⟩ with ht₀
  have ht₀1 : t₀ ≠ 1 := by
    intro h1
    apply ha₀1
    apply Subtype.ext
    refine LinearEquiv.ext fun u => ?_
    have := htρ ⟨a₀, ha₀I⟩ u
    rw [← ht₀, h1, map_one] at this
    exact this
  have ht₀tr := isTransvection_of_involution ht₀1 (ht2 ⟨a₀, ha₀I⟩)
  have hsi' : IsSingle (a i', b i') := hsame ▸ hsi
  have hμ : ∀ x : ↥I, ∃ μ : F, μ ^ 2 ^ m = μ ∧ ((t x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
      μ • ((t₀ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - μ • 1 := by
    intro x
    have hcommρ : ρ (t x) * ρ t₀ = ρ t₀ * ρ (t x) := by
      have hc := CFSG.QuasithinUnique.Setup.Layer.Actor.comm_of_isElementaryAbelian_two
        inferInstance _ (x : ↥A).2 _ a₀.2
      refine LinearMap.ext fun u => ?_
      have h1 := LinearEquiv.congr_fun hc u
      simp only [LinearEquiv.mul_apply] at h1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← htρ x, ← htρ ⟨a₀, ha₀I⟩,
        ← htρ x, ← htρ ⟨a₀, ha₀I⟩]
      exact h1
    have hcomm : t₀ * t x = t x * t₀ := (commute_of_rep ρ hker ht₀tr hcommρ).symm
    have hq : (ρ (t x) - 1) ∘ₗ (ρ t₀ - 1) = 0 := by
      refine LinearMap.ext fun u => ?_
      have h1 := hquad _ a₀.2 _ (x : ↥A).2 u
      simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply,
        LinearMap.zero_apply]
      rw [← htρ x, ← htρ ⟨a₀, ha₀I⟩, h1, sub_self]
    have hT := quad_of_sub ρ bas W₀ e₀ hq
    obtain ⟨μ, hμ⟩ := eq_smul_of_quadratic (fun p : Fin f => (a p, b p)) (fun p => (p : ℕ))
      hii' hsi hsi' hrest ht₀1 (ht2 ⟨a₀, ha₀I⟩) (ht2 x) hcomm hT
    refine ⟨μ, pow_eq_of_quadratic_row hF hii' hi' hsi hsame hrest ht₀1 (ht2 ⟨a₀, ha₀I⟩)
      (ht2 x) hcomm hT hμ, by rw [hμ, smul_sub]⟩
  choose μ hμfix hμeq using hμ
  let μ' : ↥I → {x : F // CFSG.Quasithin.H.SU3.bar m x = x} := fun x =>
    ⟨μ x, by rw [CFSG.Quasithin.H.SU3.bar_apply]; exact hμfix x⟩
  have hinj : Function.Injective μ' := by
    intro x y hxy
    have hxy' : μ x = μ y := congrArg Subtype.val hxy
    have h1 : ((t x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 =
        ((t y : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) - 1 := by
      rw [hμeq x, hμeq y, hxy']
    have h2 : t x = t y := Subtype.ext (sub_left_injective h1)
    apply Subtype.ext
    apply Subtype.ext
    refine LinearEquiv.ext fun u => ?_
    rw [htρ x, htρ y, h2]
  have := Nat.card_le_card_of_injective μ' hinj
  rwa [CFSG.Quasithin.H.SU3.card_fixed hm hK] at this

end RowBound

end B45SL3

end CFSG.Quasithin
