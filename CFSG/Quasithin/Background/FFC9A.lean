module

public import CFSG.Quasithin.Background.HDefs

public section

namespace CFSG.Quasithin

namespace FFC

namespace SumNat

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H
open scoped Matrix

variable {F : Type} [Field F]

abbrev PV (F : Type) := Fin 2 → Fin 3 → F

abbrev PM (F : Type) := Multiplicative (PV F)

abbrev adP (g : MulAut (PM F)) (v : PV F) : PV F :=
  Multiplicative.toAdd (g (Multiplicative.ofAdd v))

theorem adP_add (g : MulAut (PM F)) (v w : PV F) : adP g (v + w) = adP g v + adP g w := by
  unfold adP
  rw [ofAdd_add, map_mul, toAdd_mul]

theorem adP_zero (g : MulAut (PM F)) : adP g 0 = 0 := by
  unfold adP
  rw [ofAdd_zero, map_one, toAdd_one]

theorem adP_mul (g h : MulAut (PM F)) (v : PV F) : adP (g * h) v = adP g (adP h v) := rfl

theorem adP_one (v : PV F) : adP (1 : MulAut (PM F)) v = v := rfl

theorem adP_apply_inv (g : MulAut (PM F)) (v : PV F) : adP g⁻¹ (adP g v) = v := by
  unfold adP
  rw [ofAdd_toAdd, ← MulAut.mul_apply, inv_mul_cancel]
  rfl

theorem adP_ext {g h : MulAut (PM F)} (hgh : ∀ v, adP g v = adP h v) : g = h :=
  MulEquiv.ext fun x => congrArg Multiplicative.ofAdd (hgh (Multiplicative.toAdd x))

theorem adP_sum (g : MulAut (PM F)) {ι : Type*} (s : Finset ι) (f : ι → PV F) :
    adP g (∑ i ∈ s, f i) = ∑ i ∈ s, adP g (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adP_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, adP_add, ih]

theorem adP_eq_zero_iff (g : MulAut (PM F)) {v : PV F} : adP g v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have := congrArg (adP g⁻¹) h
    rwa [adP_apply_inv, adP_zero] at this
  · rintro rfl
    exact adP_zero g

@[expose] def diagAut (γ : GL (Fin 3) F) : MulAut (PM F) where
  toFun x := Multiplicative.ofAdd
    (fun i => (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd x i)
  invFun x := Multiplicative.ofAdd
    (fun i => ((γ⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd x i)
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_mul, toAdd_ofAdd, Pi.add_apply, Matrix.mulVec_add]

theorem adP_diagAut (γ : GL (Fin 3) F) (v : PV F) (i : Fin 2) :
    adP (diagAut γ) v i = (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ v i := rfl

@[expose] def cAct (c : Matrix (Fin 2) (Fin 2) F) (v : PV F) : PV F := fun i => ∑ j, c i j • v j

theorem cAct_add (c : Matrix (Fin 2) (Fin 2) F) (v w : PV F) :
    cAct c (v + w) = cAct c v + cAct c w := by
  funext i
  simp [cAct, smul_add, Finset.sum_add_distrib]

theorem cAct_mul (c d : Matrix (Fin 2) (Fin 2) F) (v : PV F) :
    cAct (c * d) v = cAct c (cAct d v) := by
  funext i
  simp only [cAct, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

theorem cAct_one (v : PV F) : cAct 1 v = v := by
  funext i
  simp [cAct, Matrix.one_apply]

theorem cAct_smul (c : Matrix (Fin 2) (Fin 2) F) (a : F) (v : PV F) :
    cAct c (a • v) = a • cAct c v := by
  funext i
  simp only [cAct, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

@[expose] def cAut (c : GL (Fin 2) F) : MulAut (PM F) where
  toFun x := Multiplicative.ofAdd (cAct (c : Matrix (Fin 2) (Fin 2) F) (Multiplicative.toAdd x))
  invFun x := Multiplicative.ofAdd
    (cAct ((c⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) (Multiplicative.toAdd x))
  left_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [← cAct_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, cAct_one]
  right_inv x := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    rw [← cAct_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, cAct_one]
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_ofAdd]
    rw [cAct_add]

theorem adP_cAut (c : GL (Fin 2) F) (v : PV F) :
    adP (cAut c) v = cAct (c : Matrix (Fin 2) (Fin 2) F) v := rfl

theorem diagAut_comm_cAut (γ : GL (Fin 3) F) (c : GL (Fin 2) F) :
    diagAut γ * cAut c = cAut c * diagAut γ := by
  refine adP_ext fun v => ?_
  funext i
  simp only [adP_mul, adP_diagAut, adP_cAut, cAct, Matrix.mulVec_sum, Matrix.mulVec_smul]

@[expose] def diagHom : GL (Fin 3) F →* MulAut (PM F) where
  toFun := diagAut
  map_one' := adP_ext fun v => by
    funext i
    rw [adP_diagAut, Units.val_one, Matrix.one_mulVec]
    rfl
  map_mul' g h := adP_ext fun v => by
    funext i
    rw [adP_mul, adP_diagAut, adP_diagAut, adP_diagAut, Units.val_mul, Matrix.mulVec_mulVec]

@[expose] def cHom : GL (Fin 2) F →* MulAut (PM F) where
  toFun := cAut
  map_one' := adP_ext fun v => by
    rw [adP_cAut, Units.val_one, cAct_one]
    rfl
  map_mul' g h := adP_ext fun v => by
    rw [adP_mul, adP_cAut, adP_cAut, adP_cAut, Units.val_mul, cAct_mul]

@[expose] def modelHom : ↥(StatedSL 3 F) × GL (Fin 2) F →* MulAut (PM F) :=
  MonoidHom.noncommCoprod (diagHom.comp (StatedSL 3 F).subtype) cHom
    (fun s c => (diagAut_comm_cAut (s : GL (Fin 3) F) c : _))

theorem modelHom_apply (s : ↥(StatedSL 3 F)) (c : GL (Fin 2) F) :
    modelHom (s, c) = diagAut (s : GL (Fin 3) F) * cAut c := by
  simp [modelHom, MonoidHom.noncommCoprod_apply, diagHom, cHom]

@[expose] def natImage (F : Type) [Field F] : Subgroup (MulAut (PM F)) :=
  (diagHom.comp (StatedSL 3 F).subtype).range

theorem det_eq_one_of_mem_statedSL {n : ℕ} {A : GL (Fin n) F} (h : A ∈ StatedSL n F) :
    (A : Matrix (Fin n) (Fin n) F).det = 1 :=
  CFSG.Open.StatedAPI.det_of_mem_statedSL h

theorem mem_statedSL_of_det_eq_one {n : ℕ} {A : GL (Fin n) F}
    (h : (A : Matrix (Fin n) (Fin n) F).det = 1) : A ∈ StatedSL n F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

theorem pow_three_eq_one_iff [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : Odd m) (μ : F)
    (h : μ ^ 3 = 1) : μ = 1 := by
  have hfin : Fintype F := Fintype.ofFinite F
  have hμ : μ ≠ 0 := by
    rintro rfl
    simp at h
  have h1 : μ ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one μ hμ
  have hcard : Fintype.card F = 2 ^ m := by rw [← Nat.card_eq_fintype_card, hF]
  have hmod : (2 ^ m) % 3 = 2 := by
    obtain ⟨k, rfl⟩ := hm
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hcop : Nat.gcd 3 (Fintype.card F - 1) = 1 := by
    rw [hcard]
    have h2 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    have h3 : (2 ^ m - 1) % 3 = 1 := by omega
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have := pow_gcd_eq_one.2 ⟨h, h1⟩
  rwa [hcop, pow_one] at this

theorem exists_scalar_of_diagAut_mul_cAut_eq_one {B : GL (Fin 3) F} {M : GL (Fin 2) F}
    (h : diagAut B * cAut M = 1) :
    ∃ μ : F, μ ≠ 0 ∧ (B : Matrix (Fin 3) (Fin 3) F) = μ • (1 : Matrix (Fin 3) (Fin 3) F) ∧
      (M : Matrix (Fin 2) (Fin 2) F) = μ⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hv : ∀ (v : PV F) (i : Fin 2),
      (B : Matrix (Fin 3) (Fin 3) F) *ᵥ (∑ j, (M : Matrix (Fin 2) (Fin 2) F) i j • v j) = v i := by
    intro v i
    have := congrArg (fun g => adP g v i) h
    simpa [adP_mul, adP_diagAut, adP_cAut, cAct, adP_one] using this
  set e₀ : Fin 3 → F := Pi.single 0 1 with he₀
  have hsingle : ∀ (j₀ : Fin 2) (n : Fin 3 → F) (i : Fin 2),
      (M : Matrix (Fin 2) (Fin 2) F) i j₀ • ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ n) =
        (Pi.single j₀ n : PV F) i := by
    intro j₀ n i
    have := hv (Pi.single j₀ n) i
    rw [Finset.sum_eq_single j₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun h => absurd (Finset.mem_univ _) h)] at this
    simpa [Pi.single_eq_same, Matrix.mulVec_smul] using this
  have he0 : e₀ ≠ 0 := by
    intro h0
    have := congrFun h0 0
    simp [he₀] at this
  have hdiag : ∀ j : Fin 2, (M : Matrix (Fin 2) (Fin 2) F) j j ≠ 0 := by
    intro j h0
    have := hsingle j e₀ j
    rw [h0, zero_smul] at this
    simp only [Pi.single_eq_same] at this
    exact he0 this.symm
  have hB : ∀ j : Fin 2, ∀ n, (B : Matrix (Fin 3) (Fin 3) F) *ᵥ n =
      ((M : Matrix (Fin 2) (Fin 2) F) j j)⁻¹ • n := by
    intro j n
    have := hsingle j n j
    simp only [Pi.single_eq_same] at this
    calc (B : Matrix (Fin 3) (Fin 3) F) *ᵥ n
        = ((M : Matrix (Fin 2) (Fin 2) F) j j)⁻¹ • (((M : Matrix (Fin 2) (Fin 2) F) j j) •
            ((B : Matrix (Fin 3) (Fin 3) F) *ᵥ n)) := by
          rw [smul_smul, inv_mul_cancel₀ (hdiag j), one_smul]
      _ = ((M : Matrix (Fin 2) (Fin 2) F) j j)⁻¹ • n := by rw [this]
  have hμ01 : (M : Matrix (Fin 2) (Fin 2) F) 0 0 = (M : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h0 := hB 0 e₀
    have h1 := hB 1 e₀
    rw [h0] at h1
    have h2 : ((M : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹ = ((M : Matrix (Fin 2) (Fin 2) F) 1 1)⁻¹ := by
      have h3 := congrFun h1 0
      simp only [Pi.smul_apply, smul_eq_mul, he₀, Pi.single_eq_same, mul_one] at h3
      exact h3
    exact inv_injective h2
  have hoff : ∀ i j : Fin 2, i ≠ j → (M : Matrix (Fin 2) (Fin 2) F) i j = 0 := by
    intro i j hij
    have := hsingle j e₀ i
    rw [Pi.single_eq_of_ne hij] at this
    have hBe : (B : Matrix (Fin 3) (Fin 3) F) *ᵥ e₀ ≠ 0 := by
      rw [hB j e₀]
      intro h0
      rcases smul_eq_zero.1 h0 with h1 | h1
      · exact inv_ne_zero (hdiag j) h1
      · exact he0 h1
    rcases smul_eq_zero.1 this with h1 | h1
    · exact h1
    · exact absurd h1 hBe
  refine ⟨((M : Matrix (Fin 2) (Fin 2) F) 0 0)⁻¹, inv_ne_zero (hdiag 0), ?_, ?_⟩
  · ext i j
    have := congrFun (hB 0 (Pi.single j 1)) i
    simpa [Matrix.mulVec_single_one, Matrix.smul_apply, Pi.single_apply, Matrix.one_apply,
      eq_comm] using this
  · ext i j
    rw [inv_inv]
    fin_cases i <;> fin_cases j
    · simp
    · simpa using hoff 0 1 (by decide)
    · simpa using hoff 1 0 (by decide)
    · simp [hμ01.symm]

theorem modelHom_eq_one_iff [Finite F] (hF3 : ∀ μ : F, μ ^ 3 = 1 → μ = 1) (s : ↥(StatedSL 3 F))
    (c : GL (Fin 2) F) (h : modelHom (s, c) = 1) : s = 1 ∧ c = 1 := by
  rw [modelHom_apply] at h
  obtain ⟨μ, hμ0, hs, hc⟩ := exists_scalar_of_diagAut_mul_cAut_eq_one h
  have hdet : μ ^ 3 = 1 := by
    have := det_eq_one_of_mem_statedSL s.2
    rw [hs, Matrix.det_smul, Matrix.det_one, Fintype.card_fin] at this
    simpa using this
  have hμ1 : μ = 1 := hF3 μ hdet
  subst hμ1
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    apply Units.ext
    rw [hs, one_smul]
    rfl
  · apply Units.ext
    rw [hc, inv_one, one_smul]
    rfl

theorem modelHom_injective [Finite F] (hF3 : ∀ μ : F, μ ^ 3 = 1 → μ = 1) :
    Function.Injective (modelHom : ↥(StatedSL 3 F) × GL (Fin 2) F →* MulAut (PM F)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨s, c⟩ h
  obtain ⟨hs, hc⟩ := modelHom_eq_one_iff hF3 s c h
  rw [hs, hc]
  rfl

end SumNat

end FFC

end CFSG.Quasithin
