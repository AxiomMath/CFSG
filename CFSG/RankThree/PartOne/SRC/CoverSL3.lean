module

public import CFSG.RankThree.PartOne.SLB4B.Cover
public import CFSG.RankThree.PartOne.SRC.RankOneSL2
public import CFSG.LieType.Steinberg.CentralExt.SLCentrallyClosed
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix Subgroup
open scoped MatrixGroups

section SL3

variable {F : Type*} [Field F]

@[expose] def uMat3 (a b : F) : Matrix (Fin 3) (Fin 3) F := !![1, a, b; 0, 1, 0; 0, 0, 1]

theorem uMat3_mul (a b a' b' : F) : uMat3 a b * uMat3 a' b' = uMat3 (a + a') (b + b') := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat3, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem det_uMat3 (a b : F) : (uMat3 a b).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [uMat3]

@[expose] def uSL3 (x : F × F) : SpecialLinearGroup (Fin 3) F := ⟨uMat3 x.1 x.2, det_uMat3 _ _⟩

theorem coe_uSL3 (x : F × F) :
    ((uSL3 x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = uMat3 x.1 x.2 := rfl

@[expose] def uHom3 : Multiplicative F × Multiplicative F →* SpecialLinearGroup (Fin 3) F where
  toFun x := uSL3 (Multiplicative.toAdd x.1, Multiplicative.toAdd x.2)
  map_one' := by
    apply Subtype.ext
    rw [coe_uSL3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uMat3]
  map_mul' x y := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_uSL3, coe_uSL3, coe_uSL3, uMat3_mul]
    simp [toAdd_mul]

theorem uHom3_injective : Function.Injective (uHom3 (F := F)) := by
  intro x y h
  have h' := congrArg (fun M : SpecialLinearGroup (Fin 3) F => (M : Matrix (Fin 3) (Fin 3) F)) h
  have e1 := congrFun (congrFun h' 0) 1
  have e2 := congrFun (congrFun h' 0) 2
  simp [uHom3, uSL3, uMat3] at e1 e2
  exact Prod.ext (Multiplicative.toAdd.injective e1) (Multiplicative.toAdd.injective e2)

@[expose] def torus3 (ζ : Fˣ) : SpecialLinearGroup (Fin 3) F :=
  ⟨!![(ζ : F), 0, 0; 0, ((ζ⁻¹ : Fˣ) : F), 0; 0, 0, 1], by
    rw [Matrix.det_fin_three]
    simp⟩

theorem coe_torus3 (ζ : Fˣ) :
    ((torus3 ζ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![(ζ : F), 0, 0; 0, ((ζ⁻¹ : Fˣ) : F), 0; 0, 0, 1] := rfl

@[expose] def torus3Hom : Fˣ →* SpecialLinearGroup (Fin 3) F where
  toFun := torus3
  map_one' := by
    apply Subtype.ext
    rw [coe_torus3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_torus3, coe_torus3, coe_torus3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem torus3_not_mem_center {ζ : Fˣ} (hζ : (ζ : F) ^ 2 ≠ 1) :
    torus3 ζ ∉ Subgroup.center (SpecialLinearGroup (Fin 3) F) := by
  intro hc
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have e := fun i j => congrFun (congrFun hr i) j
  have e00 := e 0 0
  have e22 := e 2 2
  simp [coe_torus3, Matrix.scalar_apply] at e00 e22
  apply hζ
  rw [← e00, e22]
  norm_num

theorem orderOf_torus3_dvd (ζ : Fˣ) :
    orderOf (torus3 ζ : SpecialLinearGroup (Fin 3) F) ∣ orderOf ζ :=
  orderOf_map_dvd (torus3Hom : Fˣ →* SpecialLinearGroup (Fin 3) F) ζ

theorem center_SL3_eq_bot [CharP F 3] : Subgroup.center (SpecialLinearGroup (Fin 3) F) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
  rw [Fintype.card_fin] at hr
  have h3 : (3 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 3
  have h1 : (r - 1) ^ 3 = 0 := by
    have e : (r - 1) ^ 3 = (r ^ 3 - 1) - 3 * (r ^ 2 - r) := by ring
    rw [e, hr, h3]
    ring
  have h2 : r = 1 := sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrz, h2, map_one]
  rfl

end SL3

theorem rank_four_of_cover_SL3_char3 {e : ℕ} {F : Type} [Field F] [Finite F] [CharP F 3]
    (hF : Nat.card F = 3 ^ e) (he : 2 ≤ e) {W : Type} [Group W] [Finite W]
    (ρ : W →* SpecialLinearGroup (Fin 3) F) (hρ : Function.Surjective ρ)
    (hker : IsPGroup 3 ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hF9 : 9 ≤ 3 ^ e := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
  have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 3) F) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
      (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num))
  obtain ⟨ζ, hζ2, hζo⟩ := exists_torus_gen (F := F) 3 e (by norm_num) he hF
  have hZ : Nat.Coprime 3 (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F))) := by
    rw [center_SL3_eq_bot]
    simp
  have hpow : ∀ a : Multiplicative F × Multiplicative F, a ^ 3 = 1 := by
    intro a
    refine Prod.ext ?_ ?_
    · show a.1 ^ 3 = 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
      have : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
      rw [this, zero_mul]
    · show a.2 ^ 3 = 1
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, nsmul_eq_mul]
      have : ((3 : ℕ) : F) = 0 := CharP.cast_eq_zero F 3
      rw [this, zero_mul]
  have hE₀ : IsElementaryAbelian 3 (uHom3 (F := F)).range := isElementaryAbelian_range uHom3 hpow
  have hcard : Nat.card (uHom3 (F := F)).range = 3 ^ (2 * e) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective uHom3_injective).toEquiv, Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd, hF, ← pow_add]
    congr 1
    omega
  exact CFSG.RankThree.PartOne.SLB4B.rank_four_of_cover_quasisimple (by norm_num) hQ hZ (torus3 ζ)
    (torus3_not_mem_center hζ2) (Nat.Coprime.coprime_dvd_left (orderOf_torus3_dvd ζ) hζo)
    (fun _ _ _ π hπ hcen _ =>
      CFSG.LieType.Steinberg.CentralExt.SLClosed.sl_exists_section_of_central (m := 2) le_rfl
        (by omega) hπ hcen)
    hE₀ (k := 2 * e) (by omega) hcard ρ hρ hker

end CFSG.RankThree.PartOne.SRC
