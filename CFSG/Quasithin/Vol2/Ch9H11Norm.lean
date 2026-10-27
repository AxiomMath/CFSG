module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticSL2Automorphisms
public import CFSG.Quasithin.Background.HL3WrNorm

public section

noncomputable section

namespace CFSG.Quasithin.H13.H11P

open CFSG.RankThree.PartOne.KCRootAxis (SL₂ slFieldAut slFieldAut_apply exists_conj_mul_slFieldAut
  sl2_isSimpleGroup)
open scoped Matrix commutatorElement

variable {K : Type} [Field K]

abbrev Mat (K : Type) [Field K] : Type := Matrix (Fin 2) (Fin 2) K

abbrev VM (K : Type) [Field K] : Type := Multiplicative (Mat K)

@[expose] def addMap (ψ : MulAut (VM K)) : Mat K →+ Mat K :=
  AddMonoidHom.toMultiplicative.symm ψ.toMonoidHom

theorem addMap_apply (ψ : MulAut (VM K)) (X : Mat K) :
    addMap ψ X = Multiplicative.toAdd (ψ (Multiplicative.ofAdd X)) := rfl

theorem addMap_mul (ψ φ : MulAut (VM K)) (X : Mat K) :
    addMap (ψ * φ) X = addMap ψ (addMap φ X) := rfl

theorem addMap_one (X : Mat K) : addMap (1 : MulAut (VM K)) X = X := rfl

theorem addMap_injective (ψ : MulAut (VM K)) : Function.Injective (addMap ψ) := by
  intro X Y h
  have h1 := ψ.injective (Multiplicative.toAdd.injective h)
  exact Multiplicative.ofAdd.injective h1

theorem eq_of_addMap {ψ φ : MulAut (VM K)} (h : ∀ X, addMap ψ X = addMap φ X) : ψ = φ :=
  MulEquiv.ext fun X => Multiplicative.toAdd.injective (h (Multiplicative.toAdd X))

theorem addMap_inv_apply (ψ : MulAut (VM K)) (X : Mat K) : addMap ψ (addMap ψ⁻¹ X) = X := by
  rw [← addMap_mul, mul_inv_cancel, addMap_one]

theorem coe_inv_mul (g : SL₂ K) : ((g⁻¹ : SL₂ K) : Mat K) * (g : Mat K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem coe_mul_inv (g : SL₂ K) : (g : Mat K) * ((g⁻¹ : SL₂ K) : Mat K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

@[expose] def uu (s : K) : SL₂ K := ⟨!![1, s; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def dd (l : K) (hl : l ≠ 0) : SL₂ K :=
  ⟨!![l, 0; 0, l⁻¹], by simp [Matrix.det_fin_two_of, hl]⟩

@[expose] def ww (l : K) (hl : l ≠ 0) : SL₂ K :=
  ⟨!![0, -l⁻¹; l, 0], by simp [Matrix.det_fin_two_of, hl]⟩

theorem coe_uu (s : K) : ((uu s : SL₂ K) : Mat K) = !![1, s; 0, 1] := rfl

theorem coe_dd (l : K) (hl : l ≠ 0) : ((dd l hl : SL₂ K) : Mat K) = !![l, 0; 0, l⁻¹] := rfl

theorem coe_ww (l : K) (hl : l ≠ 0) : ((ww l hl : SL₂ K) : Mat K) = !![0, -l⁻¹; l, 0] := rfl

abbrev E11 (K : Type) [Field K] : Mat K := Matrix.single 0 0 1

theorem E11_eq : E11 K = !![1, 0; 0, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem exists_single_eq (i j : Fin 2) {l : K} (hl : l ≠ 0) :
    ∃ g h : SL₂ K, (g : Mat K) * E11 K * (h : Mat K)ᵀ = Matrix.single i j l := by
  have h1 : (1 : K) ≠ 0 := one_ne_zero
  fin_cases i <;> fin_cases j
  · refine ⟨dd l hl, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [E11_eq, coe_dd, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨dd l hl, ww 1 h1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [E11_eq, coe_dd, coe_ww, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨ww l hl, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [E11_eq, coe_ww, Matrix.mul_apply, Fin.sum_univ_two]
  · refine ⟨ww l hl, ww 1 h1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [E11_eq, coe_ww, Matrix.mul_apply, Fin.sum_univ_two]

theorem uu_mul_E11 (s : K) : ((uu s : SL₂ K) : Mat K) * E11 K = E11 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [E11_eq, coe_uu, Matrix.mul_apply, Fin.sum_univ_two]

theorem E11_mul_uu (s : K) : E11 K * ((uu s : SL₂ K) : Mat K)ᵀ = E11 K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [E11_eq, coe_uu, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_smul_E11 {Y : Mat K} (h1 : ((uu 1 : SL₂ K) : Mat K) * Y = Y)
    (h2 : Y * ((uu 1 : SL₂ K) : Mat K)ᵀ = Y) : Y = Y 0 0 • E11 K := by
  have e1 := fun b => congrFun (congrFun h1 0) b
  have e2 := fun a => congrFun (congrFun h2 a) 0
  simp [coe_uu, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2
  ext a b
  fin_cases a <;> fin_cases b <;> simp_all

theorem dd_mul_E11 (l : K) (hl : l ≠ 0) : ((dd l hl : SL₂ K) : Mat K) * E11 K = l • E11 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [E11_eq, coe_dd, Matrix.mul_apply, Fin.sum_univ_two]

theorem E11_mul_dd (l : K) (hl : l ≠ 0) : E11 K * ((dd l hl : SL₂ K) : Mat K)ᵀ = l • E11 K := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [E11_eq, coe_dd, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_slFieldAut (σ : K ≃+* K) (g : SL₂ K) :
    ((slFieldAut K σ g : SL₂ K) : Mat K) = σ.mapMatrix (g : Mat K) := by
  ext a b
  exact slFieldAut_apply σ g a b

theorem mapMatrix_uu (σ : K ≃+* K) (s : K) :
    σ.mapMatrix ((uu s : SL₂ K) : Mat K) = ((uu (σ s) : SL₂ K) : Mat K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_uu]

theorem mapMatrix_dd (σ : K ≃+* K) (l : K) (hl : l ≠ 0) :
    σ.mapMatrix ((dd l hl : SL₂ K) : Mat K) =
      ((dd (σ l) ((map_ne_zero σ).mpr hl) : SL₂ K) : Mat K) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [coe_dd, map_inv₀]

theorem mapMatrix_transpose (σ : K ≃+* K) (M : Mat K) : σ.mapMatrix Mᵀ = (σ.mapMatrix M)ᵀ := by
  ext a b
  rfl

theorem mapMatrix_smul (σ : K ≃+* K) (c : K) (M : Mat K) :
    σ.mapMatrix (c • M) = σ c • σ.mapMatrix M := by
  ext a b
  simp

theorem symm_mapMatrix_apply (σ : K ≃+* K) (M : Mat K) :
    σ.symm.mapMatrix (σ.mapMatrix M) = M := by
  ext a b
  simp

theorem mapMatrix_symm_apply (σ : K ≃+* K) (M : Mat K) :
    σ.mapMatrix (σ.symm.mapMatrix M) = M := by
  ext a b
  simp

@[expose] def tAct (g h : SL₂ K) : Mat K ≃+ Mat K where
  toFun X := (g : Mat K) * X * (h : Mat K)ᵀ
  invFun X := ((g⁻¹ : SL₂ K) : Mat K) * X * ((h⁻¹ : SL₂ K) : Mat K)ᵀ
  left_inv X := by
    show ((g⁻¹ : SL₂ K) : Mat K) * ((g : Mat K) * X * (h : Mat K)ᵀ) *
      ((h⁻¹ : SL₂ K) : Mat K)ᵀ = X
    calc ((g⁻¹ : SL₂ K) : Mat K) * ((g : Mat K) * X * (h : Mat K)ᵀ) * ((h⁻¹ : SL₂ K) : Mat K)ᵀ
        = (((g⁻¹ : SL₂ K) : Mat K) * (g : Mat K)) * X *
          (((h⁻¹ : SL₂ K) : Mat K) * (h : Mat K))ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = X := by rw [coe_inv_mul, coe_inv_mul, Matrix.transpose_one, Matrix.one_mul,
          Matrix.mul_one]
  right_inv X := by
    show (g : Mat K) * (((g⁻¹ : SL₂ K) : Mat K) * X * ((h⁻¹ : SL₂ K) : Mat K)ᵀ) *
      (h : Mat K)ᵀ = X
    calc (g : Mat K) * (((g⁻¹ : SL₂ K) : Mat K) * X * ((h⁻¹ : SL₂ K) : Mat K)ᵀ) * (h : Mat K)ᵀ
        = ((g : Mat K) * ((g⁻¹ : SL₂ K) : Mat K)) * X *
          ((h : Mat K) * ((h⁻¹ : SL₂ K) : Mat K))ᵀ := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = X := by rw [coe_mul_inv, coe_mul_inv, Matrix.transpose_one, Matrix.one_mul,
          Matrix.mul_one]
  map_add' X Y := by
    show (g : Mat K) * (X + Y) * (h : Mat K)ᵀ = (g : Mat K) * X * (h : Mat K)ᵀ +
      (g : Mat K) * Y * (h : Mat K)ᵀ
    rw [Matrix.mul_add, Matrix.add_mul]

@[expose] def rho : SL₂ K × SL₂ K →* MulAut (VM K) where
  toFun p := AddEquiv.toMultiplicative (tAct p.1 p.2)
  map_one' := by
    refine MulEquiv.ext fun X => ?_
    show Multiplicative.ofAdd (((1 : SL₂ K) : Mat K) * Multiplicative.toAdd X *
      ((1 : SL₂ K) : Mat K)ᵀ) = X
    simp
  map_mul' p q := by
    refine MulEquiv.ext fun X => ?_
    show Multiplicative.ofAdd (((p.1 * q.1 : SL₂ K) : Mat K) * Multiplicative.toAdd X *
      ((p.2 * q.2 : SL₂ K) : Mat K)ᵀ) = Multiplicative.ofAdd ((p.1 : Mat K) *
      ((q.1 : Mat K) * Multiplicative.toAdd X * (q.2 : Mat K)ᵀ) * (p.2 : Mat K)ᵀ)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]

theorem addMap_rho (p : SL₂ K × SL₂ K) (X : Mat K) :
    addMap (rho p) X = (p.1 : Mat K) * X * (p.2 : Mat K)ᵀ := rfl

abbrev Lm (K : Type) [Field K] : Subgroup (MulAut (VM K)) := (rho (K := K)).range

@[expose] def trn : MulAut (VM K) :=
  AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) K)

theorem addMap_trn (X : Mat K) : addMap trn X = Xᵀ := rfl

theorem trn_mul_trn : (trn : MulAut (VM K)) * trn = 1 :=
  eq_of_addMap fun X => by rw [addMap_mul, addMap_trn, addMap_trn, Matrix.transpose_transpose,
    addMap_one]

theorem trn_inv : (trn : MulAut (VM K))⁻¹ = trn :=
  inv_eq_of_mul_eq_one_right trn_mul_trn

theorem trn_rho (p : SL₂ K × SL₂ K) : trn * rho p * trn = rho (p.2, p.1) :=
  eq_of_addMap fun X => by
    rw [addMap_mul, addMap_mul, addMap_trn, addMap_rho, addMap_trn, addMap_rho,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.mul_assoc]

variable [CharP K 2]

theorem eq_one_of_sq_eq_one {c : K} (h : c ^ 2 = 1) : c = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have : (c - 1) ^ 2 = 0 := by linear_combination h + (1 - c) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp this)

theorem rho_injective : Function.Injective (rho (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, h⟩ hp
  rw [MonoidHom.mem_ker] at hp
  have key : ∀ X : Mat K, (g : Mat K) * X * (h : Mat K)ᵀ = X := fun X => by
    have := congrArg (fun φ : MulAut (VM K) => addMap φ X) hp
    exact this
  have h1 : (g : Mat K) * (h : Mat K)ᵀ = 1 := by simpa using key 1
  have h2 : (h : Mat K)ᵀ * (g : Mat K) = 1 := mul_eq_one_comm.mp h1
  have hcomm : ∀ X : Mat K, Commute (g : Mat K) X := fun X => by
    show (g : Mat K) * X = X * g
    calc (g : Mat K) * X = (g : Mat K) * X * ((h : Mat K)ᵀ * g) := by rw [h2, Matrix.mul_one]
      _ = ((g : Mat K) * X * (h : Mat K)ᵀ) * g := by simp only [Matrix.mul_assoc]
      _ = X * g := by rw [key]
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_of_commute_single (M := (g : Mat K))
    fun i j _ => (hcomm _).symm
  have hdet : ((g : Mat K)).det = 1 := g.2
  rw [← hc, Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two] at hdet
  have hc1 : c = 1 := eq_one_of_sq_eq_one (by rw [sq]; exact hdet)
  have hg : g = 1 := Subtype.ext (by
    rw [← hc, hc1, Matrix.SpecialLinearGroup.coe_one]
    simp)
  have hh : h = 1 := by
    rw [hg, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at h1
    exact Subtype.ext (by
      rw [← Matrix.transpose_transpose (h : Mat K), h1, Matrix.transpose_one,
        Matrix.SpecialLinearGroup.coe_one])
  rw [Subgroup.mem_bot, hg, hh]
  rfl

omit [CharP K 2] in
theorem eq_smul_of_comm (ψ : Mat K →+ Mat K)
    (hψ : ∀ (g h : SL₂ K) (X : Mat K), ψ ((g : Mat K) * X * (h : Mat K)ᵀ) =
      (g : Mat K) * ψ X * (h : Mat K)ᵀ) :
    ∃ c : K, ∀ X, ψ X = c • X := by
  have hl : ((uu 1 : SL₂ K) : Mat K) * ψ (E11 K) = ψ (E11 K) := by
    have h := hψ (uu 1) 1 (E11 K)
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.transpose_one, Matrix.mul_one,
      uu_mul_E11] at h
    exact h.symm
  have hr : ψ (E11 K) * ((uu 1 : SL₂ K) : Mat K)ᵀ = ψ (E11 K) := by
    have h := hψ 1 (uu 1) (E11 K)
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, E11_mul_uu] at h
    exact h.symm
  obtain ⟨c, hc⟩ : ∃ c, ψ (E11 K) = c • E11 K := ⟨_, eq_smul_E11 hl hr⟩
  have hs : ∀ (i j : Fin 2) (l : K), ψ (Matrix.single i j l) = c • Matrix.single i j l := by
    intro i j l
    by_cases hl0 : l = 0
    · rw [hl0, Matrix.single_zero, map_zero, smul_zero]
    obtain ⟨g, h, hgh⟩ := exists_single_eq i j hl0
    rw [← hgh, hψ, hc, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨c, fun X => ?_⟩
  rw [Matrix.matrix_eq_sum_single X, map_sum]
  simp only [map_sum, hs, Finset.smul_sum]

omit [CharP K 2] in
theorem eq_smul_map_of_semi (ψ : Mat K →+ Mat K) (σ₁ σ₂ : K ≃+* K) (hψ0 : ψ (E11 K) ≠ 0)
    (hψ : ∀ (g h : SL₂ K) (X : Mat K), ψ ((g : Mat K) * X * (h : Mat K)ᵀ) =
      σ₁.mapMatrix (g : Mat K) * ψ X * (σ₂.mapMatrix (h : Mat K))ᵀ) :
    σ₁ = σ₂ ∧ ∃ c : K, c ≠ 0 ∧ ∀ X, ψ X = c • σ₁.mapMatrix X := by
  have hl : ((uu 1 : SL₂ K) : Mat K) * ψ (E11 K) = ψ (E11 K) := by
    have h := hψ (uu (σ₁.symm 1)) 1 (E11 K)
    simp only [mapMatrix_uu, Matrix.SpecialLinearGroup.coe_one, map_one, Matrix.transpose_one,
      Matrix.mul_one, uu_mul_E11] at h
    exact h.symm
  have hr : ψ (E11 K) * ((uu 1 : SL₂ K) : Mat K)ᵀ = ψ (E11 K) := by
    have h := hψ 1 (uu (σ₂.symm 1)) (E11 K)
    simp only [mapMatrix_uu, Matrix.SpecialLinearGroup.coe_one, map_one, Matrix.one_mul,
      E11_mul_uu] at h
    exact h.symm
  obtain ⟨c, hc⟩ : ∃ c, ψ (E11 K) = c • E11 K := ⟨_, eq_smul_E11 hl hr⟩
  have hc0 : c ≠ 0 := fun h0 => hψ0 (by rw [hc, h0, zero_smul])
  have hσ : σ₁ = σ₂ := by
    refine RingEquiv.ext fun l => ?_
    by_cases hl0 : l = 0
    · rw [hl0, map_zero, map_zero]
    have e1 := hψ (dd l hl0) 1 (E11 K)
    have e2 := hψ 1 (dd l hl0) (E11 K)
    simp only [mapMatrix_dd, Matrix.SpecialLinearGroup.coe_one, map_one, Matrix.transpose_one,
      Matrix.mul_one, dd_mul_E11, hc, Matrix.mul_smul] at e1
    simp only [mapMatrix_dd, Matrix.SpecialLinearGroup.coe_one, map_one, Matrix.one_mul,
      E11_mul_dd, hc, Matrix.smul_mul] at e2
    have e3 := congrFun (congrFun (e1.symm.trans e2) 0) 0
    simp only [Matrix.smul_apply, Matrix.single_apply_same, smul_eq_mul, mul_one] at e3
    exact mul_left_cancel₀ hc0 e3
  refine ⟨hσ, c, hc0, ?_⟩
  subst hσ
  set ψ' : Mat K →+ Mat K := ((σ₁.symm.mapMatrix : Mat K ≃+* Mat K) : Mat K →+ Mat K).comp ψ
    with hψ'
  have hψ'_apply : ∀ X, ψ' X = σ₁.symm.mapMatrix (ψ X) := fun X => rfl
  have hcomm : ∀ (g h : SL₂ K) (X : Mat K), ψ' ((g : Mat K) * X * (h : Mat K)ᵀ) =
      (g : Mat K) * ψ' X * (h : Mat K)ᵀ := by
    intro g h X
    rw [hψ'_apply, hψ'_apply, hψ, map_mul, map_mul, ← mapMatrix_transpose, symm_mapMatrix_apply,
      symm_mapMatrix_apply]
  obtain ⟨c', hc'⟩ := eq_smul_of_comm ψ' hcomm
  have hcc : c = σ₁ c' := by
    have h1 := hc' (E11 K)
    rw [hψ'_apply, hc, mapMatrix_smul] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp only [Matrix.smul_apply, smul_eq_mul, RingEquiv.mapMatrix_apply, Matrix.map_apply,
      Matrix.single_apply_same, map_one, mul_one] at h2
    rw [← h2, RingEquiv.apply_symm_apply]
  intro X
  have h1 := hc' X
  rw [hψ'_apply] at h1
  have h2 := congrArg σ₁.mapMatrix h1
  rw [mapMatrix_symm_apply, mapMatrix_smul] at h2
  rw [h2, hcc]

omit [CharP K 2] in
@[expose] def ul (s : K) : SL₂ K := ⟨!![1, 0; s, 1], by simp [Matrix.det_fin_two_of]⟩

omit [CharP K 2] in
theorem coe_ul (s : K) : ((ul s : SL₂ K) : Mat K) = !![1, 0; s, 1] := rfl

omit [CharP K 2] in
theorem uu_mul_ul_ne : uu (1 : K) * ul 1 ≠ ul 1 * uu 1 := by
  intro h
  have h1 := congrArg (fun g : SL₂ K => (g : Mat K) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_uu, coe_ul, Matrix.mul_apply,
    Fin.sum_univ_two] at h1
  simp at h1

theorem commutator_sl2 (h4 : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (SL₂ K)), (⊤ : Subgroup (SL₂ K))⁆ = (⊤ : Subgroup (SL₂ K)) := by
  have hs := sl2_isSimpleGroup (K := K) h4
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _
    (Subgroup.commutator_normal (⊤ : Subgroup (SL₂ K)) ⊤) with h | h
  · exfalso
    apply uu_mul_ul_ne (K := K)
    have hc : ⁅uu (1 : K), ul 1⁆ ∈ ⁅(⊤ : Subgroup (SL₂ K)), (⊤ : Subgroup (SL₂ K))⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

abbrev fac1 (K : Type) [Field K] : Subgroup (SL₂ K × SL₂ K) := (⊤ : Subgroup (SL₂ K)).prod ⊥

abbrev fac2 (K : Type) [Field K] : Subgroup (SL₂ K × SL₂ K) := (⊥ : Subgroup (SL₂ K)).prod ⊤

@[expose] def PresF (x : MulAut (VM K)) : Prop :=
  (∀ g : SL₂ K, ∃ g' : SL₂ K, x * rho (g, 1) * x⁻¹ = rho (g', 1)) ∧
    ∀ h : SL₂ K, ∃ h' : SL₂ K, x * rho (1, h) * x⁻¹ = rho (1, h')

@[expose] def SwapF (x : MulAut (VM K)) : Prop :=
  (∀ g : SL₂ K, ∃ g' : SL₂ K, x * rho (g, 1) * x⁻¹ = rho (1, g')) ∧
    ∀ h : SL₂ K, ∃ h' : SL₂ K, x * rho (1, h) * x⁻¹ = rho (h', 1)

omit [CharP K 2] in
theorem rho_mul_mk (g g' h h' : SL₂ K) : rho (g, h) * rho (g', h') = rho (g * g', h * h') := by
  rw [← map_mul, Prod.mk_mul_mk]

variable [Finite K]

theorem presF_or_swapF (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)}
    (hx : x ∈ Subgroup.normalizer ((Lm K : Subgroup (MulAut (VM K))) : Set (MulAut (VM K)))) :
    PresF x ∨ SwapF x := by
  have hmem : ∀ p : SL₂ K × SL₂ K, x * rho p * x⁻¹ ∈ Lm K := fun p =>
    (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨p, rfl⟩
  choose f hf using hmem
  have hinj := rho_injective (K := K)
  have hfmul : ∀ p q, f (p * q) = f p * f q := fun p q => hinj (by
    rw [hf, map_mul, map_mul, hf, hf]
    group)
  have hf1 : f 1 = 1 := hinj (by rw [hf, map_one, mul_one, mul_inv_cancel])
  let F : SL₂ K × SL₂ K →* SL₂ K × SL₂ K :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul }
  have hFinj : Function.Injective F := fun p q hpq => by
    have h1 : x * rho p * x⁻¹ = x * rho q * x⁻¹ := by rw [← hf, ← hf]; exact congrArg rho hpq
    exact hinj (by simpa using h1)
  have hFsurj : Function.Surjective F := Finite.surjective_of_injective hFinj
  set α : MulAut (SL₂ K × SL₂ K) := MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩ with hα
  have hαf : ∀ p, α p = f p := fun p => rfl
  have hs := sl2_isSimpleGroup (K := K) h4
  have hp := commutator_sl2 (K := K) h4
  have hne : fac1 K ≠ fac2 K := by
    intro h
    have h1 : ((uu 1 : SL₂ K), (1 : SL₂ K)) ∈ fac1 K :=
      Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
    rw [h, Subgroup.mem_prod] at h1
    have h2 := Subgroup.mem_bot.mp h1.1
    have h3 := congrArg (fun g : SL₂ K => (g : Mat K) 0 1) h2
    simp [coe_uu] at h3
  have hmapinj := Subgroup.map_injective (f := α.toMonoidHom) α.injective
  have hfst : ∀ (N : Subgroup (SL₂ K × SL₂ K)), (fac1 K).map
      α.toMonoidHom = N → ∀ g : SL₂ K, f (g, 1) ∈ N := by
    intro N hN g
    rw [← hN, ← hαf]
    exact ⟨(g, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩, rfl⟩
  have hsnd : ∀ (N : Subgroup (SL₂ K × SL₂ K)), (fac2 K).map
      α.toMonoidHom = N → ∀ h : SL₂ K, f (1, h) ∈ N := by
    intro N hN h
    rw [← hN, ← hαf]
    exact ⟨(1, h), Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩, rfl⟩
  have hTB : ∀ q : SL₂ K × SL₂ K, q ∈ fac1 K → q = (q.1, 1) := by
    intro q hq
    exact Prod.ext rfl (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hq).2)
  have hBT : ∀ q : SL₂ K × SL₂ K, q ∈ fac2 K → q = (1, q.2) := by
    intro q hq
    exact Prod.ext (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hq).1) rfl
  rcases CFSG.Quasithin.H.L3Wr.map_prod_eq_or hs hp α with h1 | h1 <;>
    rcases CFSG.Quasithin.H.L3Wr.map_prod_eq_or' hs hp α with h2 | h2
  · exact absurd (hmapinj (h2.trans h1.symm)) hne.symm
  · left
    refine ⟨fun g => ⟨(f (g, 1)).1, ?_⟩, fun h => ⟨(f (1, h)).2, ?_⟩⟩
    · rw [← hf, ← hTB _ (hfst _ h1 g)]
    · rw [← hf, ← hBT _ (hsnd _ h2 h)]
  · right
    refine ⟨fun g => ⟨(f (g, 1)).2, ?_⟩, fun h => ⟨(f (1, h)).1, ?_⟩⟩
    · rw [← hf, ← hBT _ (hfst _ h1 g)]
    · rw [← hf, ← hTB _ (hsnd _ h2 h)]
  · exact absurd (hmapinj (h2.trans h1.symm)) hne.symm

omit [CharP K 2] [Finite K] in
theorem presF_mul_trn {x : MulAut (VM K)} (hx : SwapF x) : PresF (x * trn) := by
  have hconj : ∀ p : SL₂ K × SL₂ K, x * trn * rho p * (x * trn)⁻¹ = x * rho (p.2, p.1) * x⁻¹ := by
    intro p
    rw [mul_inv_rev, trn_inv, ← trn_rho p]
    group
  refine ⟨fun g => ?_, fun h => ?_⟩
  · obtain ⟨h', hh'⟩ := hx.2 g
    exact ⟨h', by rw [hconj]; exact hh'⟩
  · obtain ⟨g', hg'⟩ := hx.1 h
    exact ⟨g', by rw [hconj]; exact hg'⟩

omit [CharP K 2] in
theorem exists_conj_of_hom [CharP K 2] {a : SL₂ K → SL₂ K} (hmul : ∀ g g', a (g * g') = a g * a g')
    (hinj : Function.Injective a) :
    ∃ (M : SL₂ K) (σ : K ≃+* K), ∀ g, a g = M * slFieldAut K σ g * M⁻¹ := by
  have hone : a 1 = 1 := by
    have h1 := hmul 1 1
    rw [one_mul] at h1
    exact mul_eq_left.mp h1.symm
  let A : SL₂ K →* SL₂ K := { toFun := a, map_one' := hone, map_mul' := hmul }
  have hAbij : Function.Bijective A := ⟨hinj, Finite.surjective_of_injective hinj⟩
  obtain ⟨M, σ, hMσ⟩ := exists_conj_mul_slFieldAut (MulEquiv.ofBijective A hAbij)
  exact ⟨M, σ, fun g => congrArg (fun φ : MulAut (SL₂ K) => φ g) hMσ⟩

omit [CharP K 2] [Finite K] in
theorem E11_ne_zero : E11 K ≠ 0 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp at this

theorem nf_of_presF {x : MulAut (VM K)} (hx : PresF x) :
    ∃ (c : K) (_ : c ≠ 0) (P Q : SL₂ K) (σ : K ≃+* K),
      ∀ X, addMap x X = c • ((P : Mat K) * σ.mapMatrix X * (Q : Mat K)ᵀ) := by
  have hinj := rho_injective (K := K)
  choose a₁ ha₁ using hx.1
  choose a₂ ha₂ using hx.2
  have hconj : ∀ u v : MulAut (VM K), x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) :=
    fun u v => by group
  have hcancel : ∀ u v : MulAut (VM K), x * u * x⁻¹ = x * v * x⁻¹ → u = v :=
    fun u v h => mul_left_cancel (mul_right_cancel h)
  have hmul₁ : ∀ g g', a₁ (g * g') = a₁ g * a₁ g' := fun g g' => by
    have h : rho (a₁ (g * g'), 1) = rho (a₁ g * a₁ g', 1) := by
      calc rho (a₁ (g * g'), 1) = x * (rho (g, 1) * rho (g', 1)) * x⁻¹ := by
            rw [← ha₁, rho_mul_mk, mul_one]
        _ = rho (a₁ g * a₁ g', 1) := by rw [hconj, ha₁, ha₁, rho_mul_mk, mul_one]
    exact congrArg Prod.fst (hinj h)
  have hmul₂ : ∀ h h', a₂ (h * h') = a₂ h * a₂ h' := fun h h' => by
    have e : rho (1, a₂ (h * h')) = rho (1, a₂ h * a₂ h') := by
      calc rho (1, a₂ (h * h')) = x * (rho (1, h) * rho (1, h')) * x⁻¹ := by
            rw [← ha₂, rho_mul_mk, mul_one]
        _ = rho (1, a₂ h * a₂ h') := by rw [hconj, ha₂, ha₂, rho_mul_mk, mul_one]
    exact congrArg Prod.snd (hinj e)
  have hinj₁ : Function.Injective a₁ := fun g g' h => by
    have h2 := hcancel (rho (g, 1)) (rho (g', 1)) (by rw [ha₁, ha₁, h])
    exact congrArg Prod.fst (hinj h2)
  have hinj₂ : Function.Injective a₂ := fun g g' h => by
    have h2 := hcancel (rho (1, g)) (rho (1, g')) (by rw [ha₂, ha₂, h])
    exact congrArg Prod.snd (hinj h2)
  obtain ⟨M₁, σ₁, hM₁⟩ := exists_conj_of_hom hmul₁ hinj₁
  obtain ⟨M₂, σ₂, hM₂⟩ := exists_conj_of_hom hmul₂ hinj₂
  have hxρ : ∀ g h, x * rho (g, h) * x⁻¹ = rho (a₁ g, a₂ h) := fun g h => by
    have e : rho (g, h) = rho (g, 1) * rho (1, h) := by rw [rho_mul_mk, mul_one, one_mul]
    rw [e, hconj, ha₁, ha₂, rho_mul_mk, mul_one, one_mul]
  set ψ := (rho (M₁, M₂))⁻¹ * x with hψ
  have hψρ : ∀ g h, ψ * rho (g, h) = rho (slFieldAut K σ₁ g, slFieldAut K σ₂ h) * ψ := by
    intro g h
    have h1 : rho (a₁ g, a₂ h) = rho (M₁, M₂) * rho (slFieldAut K σ₁ g, slFieldAut K σ₂ h) *
        (rho (M₁, M₂))⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, Prod.inv_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, ← hM₁,
        ← hM₂]
    calc ψ * rho (g, h) = (rho (M₁, M₂))⁻¹ * (x * rho (g, h) * x⁻¹) * x := by rw [hψ]; group
      _ = (rho (M₁, M₂))⁻¹ * (rho (M₁, M₂) * rho (slFieldAut K σ₁ g, slFieldAut K σ₂ h) *
          (rho (M₁, M₂))⁻¹) * x := by rw [hxρ, h1]
      _ = rho (slFieldAut K σ₁ g, slFieldAut K σ₂ h) * ψ := by rw [hψ]; group
  have hsemi : ∀ (g h : SL₂ K) (X : Mat K), addMap ψ ((g : Mat K) * X * (h : Mat K)ᵀ) =
      σ₁.mapMatrix (g : Mat K) * addMap ψ X * (σ₂.mapMatrix (h : Mat K))ᵀ := by
    intro g h X
    have h1 := congrArg (fun φ : MulAut (VM K) => addMap φ X) (hψρ g h)
    simp only [addMap_mul, addMap_rho] at h1
    rw [h1, coe_slFieldAut, coe_slFieldAut]
  have hψ0 : addMap ψ (E11 K) ≠ 0 := fun h0 =>
    E11_ne_zero (addMap_injective ψ (h0.trans (map_zero _).symm))
  obtain ⟨-, c, hc0, hc⟩ := eq_smul_map_of_semi (addMap ψ) σ₁ σ₂ hψ0 hsemi
  refine ⟨c, hc0, M₁, M₂, σ₁, fun X => ?_⟩
  have hx' : x = rho (M₁, M₂) * ψ := by rw [hψ]; group
  rw [hx', addMap_mul, addMap_rho, hc, Matrix.mul_smul, Matrix.smul_mul]

theorem normal_form (h4 : 4 ≤ Nat.card K) {x : MulAut (VM K)}
    (hx : x ∈ Subgroup.normalizer ((Lm K : Subgroup (MulAut (VM K))) : Set (MulAut (VM K)))) :
    ∃ (c : K) (_ : c ≠ 0) (P Q : SL₂ K) (σ : K ≃+* K),
      (∀ X, addMap x X = c • ((P : Mat K) * σ.mapMatrix X * (Q : Mat K)ᵀ)) ∨
      (∀ X, addMap x X = c • ((P : Mat K) * σ.mapMatrix Xᵀ * (Q : Mat K)ᵀ)) := by
  rcases presF_or_swapF h4 hx with h | h
  · obtain ⟨c, hc0, P, Q, σ, hPQ⟩ := nf_of_presF h
    exact ⟨c, hc0, P, Q, σ, Or.inl hPQ⟩
  · obtain ⟨c, hc0, P, Q, σ, hPQ⟩ := nf_of_presF (presF_mul_trn h)
    refine ⟨c, hc0, P, Q, σ, Or.inr fun X => ?_⟩
    have hx' : x = x * trn * trn := by rw [mul_assoc, trn_mul_trn, mul_one]
    rw [hx', addMap_mul, addMap_trn, hPQ]

end CFSG.Quasithin.H13.H11P

end
