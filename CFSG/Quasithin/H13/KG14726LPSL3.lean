module

public import CFSG.Quasithin.H13.KG14726LSylow
public import CFSG.Quasithin.H13.KG14726CPar

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Matrices

variable {K : Type} [Field K]

@[expose] def rootE02 (c : K) : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, c; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def rootE01 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [det_fin_three]⟩

@[expose] def rootE12 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [det_fin_three]⟩

theorem coe_rootE02 (c : K) :
    (rootE02 c : Matrix (Fin 3) (Fin 3) K) = !![1, 0, c; 0, 1, 0; 0, 0, 1] := rfl

theorem coe_rootE01 :
    ((rootE01 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem coe_rootE12 :
    ((rootE12 : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, 1; 0, 0, 1] := rfl

theorem rootE01_mem : (rootE01 : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_rootE01] at hij ⊢
  · fin_cases i <;> simp [coe_rootE01]

theorem rootE12_mem : (rootE12 : SpecialLinearGroup (Fin 3) K) ∈ unitriangular 3 K := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_rootE12] at hij ⊢
  · fin_cases i <;> simp [coe_rootE12]

theorem rootE02_zero : (rootE02 0 : SpecialLinearGroup (Fin 3) K) = 1 := by
  apply Subtype.ext
  rw [coe_rootE02, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem eq_rootE02_of_commute {A : SpecialLinearGroup (Fin 3) K} (hA : A ∈ unitriangular 3 K)
    (h1 : A * rootE01 = rootE01 * A) (h2 : A * rootE12 = rootE12 * A) :
    A = rootE02 ((A : Matrix (Fin 3) (Fin 3) K) 0 2) := by
  obtain ⟨hl, hd⟩ := hA
  have a10 := hl 1 0 (by decide)
  have a20 := hl 2 0 (by decide)
  have a21 := hl 2 1 (by decide)
  have a00 := hd 0
  have a11 := hd 1
  have a22 := hd 2
  have m1 := congrArg Subtype.val h1
  have m2 := congrArg Subtype.val h2
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootE01] at m1
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootE12] at m2
  have e1 := congrFun (congrFun m1 0) 2
  have e2 := congrFun (congrFun m2 0) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at e1 e2
  have a12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by linear_combination -e1 + a22 - a22
  have a01 : (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by linear_combination e2 - a00 + a00
  apply Subtype.ext
  rw [coe_rootE02]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [a00, a01, a10, a11, a12, a20, a21, a22]

theorem commute_of_proj_commute_unitriangular {n : ℕ} {A B : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ unitriangular n K) (hB : B ∈ unitriangular n K)
    (h : proj n K A * proj n K B = proj n K B * proj n K A) : A * B = B * A := by
  have hs : (A * B)⁻¹ * (B * A) ∈ scalars n K := by
    rw [← proj_eq_proj_iff, map_mul, map_mul, h]
  have hu : (A * B)⁻¹ * (B * A) ∈ unitriangular n K :=
    (unitriangular n K).mul_mem ((unitriangular n K).inv_mem
      ((unitriangular n K).mul_mem hA hB)) ((unitriangular n K).mul_mem hB hA)
  have hm : (A * B)⁻¹ * (B * A) ∈ unitriangular n K ⊓ scalars n K := mem_inf.mpr ⟨hu, hs⟩
  rw [unitriangular_inf_scalars, mem_bot, inv_mul_eq_one] at hm
  exact hm

theorem exists_rootE02_of_mem_center {u : projectiveSL 3 K} (hu : u ∈ projUnitriangular 3 K)
    (huc : ∀ s ∈ projUnitriangular 3 K, s * u = u * s) (hu1 : u ≠ 1) :
    ∃ c : K, c ≠ 0 ∧ u = proj 3 K (rootE02 c) := by
  obtain ⟨A, hA, rfl⟩ := hu
  have h1 := commute_of_proj_commute_unitriangular hA rootE01_mem
    (huc _ ⟨_, rootE01_mem, rfl⟩).symm
  have h2 := commute_of_proj_commute_unitriangular hA rootE12_mem
    (huc _ ⟨_, rootE12_mem, rfl⟩).symm
  have hA' := eq_rootE02_of_commute hA h1 h2
  refine ⟨(A : Matrix (Fin 3) (Fin 3) K) 0 2, fun h0 => hu1 ?_, by rw [← hA']⟩
  rw [hA', h0, rootE02_zero, map_one]

@[expose] def torus3Elt (a : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨diagonal ![(a : K), ((a⁻¹ * a⁻¹ : Kˣ) : K), (a : K)], by
    rw [det_diagonal, Fin.prod_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← Units.val_mul, ← Units.val_mul, show a * (a⁻¹ * a⁻¹) * a = 1 by group,
      Units.val_one]⟩

theorem coe_torus3Elt (a : Kˣ) : ((torus3Elt a : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K), ((a⁻¹ * a⁻¹ : Kˣ) : K), (a : K)] := rfl

@[expose] def torus3 : Kˣ →* SpecialLinearGroup (Fin 3) K :=
  MonoidHom.mk' torus3Elt fun a b => by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_torus3Elt, coe_torus3Elt, coe_torus3Elt,
      diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm, mul_left_comm, mul_assoc]

theorem coe_torus3 (a : Kˣ) : ((torus3 a : SpecialLinearGroup (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) = diagonal ![(a : K), ((a⁻¹ * a⁻¹ : Kˣ) : K), (a : K)] := rfl

theorem torus3_commute_rootE02 (a : Kˣ) (c : K) :
    torus3 a * rootE02 c = rootE02 c * torus3 a := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torus3,
    coe_rootE02]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem exists_prime_commute_rootE02 [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 3 ≤ f)
    (c : K) : ∃ ℓ : projectiveSL 3 K, ℓ * proj 3 K (rootE02 c) = proj 3 K (rootE02 c) * ℓ ∧
      ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p := by
  obtain ⟨p, hp, hp5, hpd⟩ := exists_prime_dvd_two_pow_sub_one hf
  have : Fact p.Prime := ⟨hp⟩
  have hU : Nat.card Kˣ = 2 ^ f - 1 := by rw [Nat.card_units, hK]
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [hU]; exact hpd)
  refine ⟨proj 3 K (torus3 a), by rw [← map_mul, ← map_mul, torus3_commute_rootE02], p, hp,
    hp5, ?_⟩
  have h1 : orderOf (proj 3 K (torus3 a)) ∣ p := by
    rw [← ha]
    exact (orderOf_map_dvd (proj 3 K) _).trans (orderOf_map_dvd torus3 a)
  have h2 : proj 3 K (torus3 a) ≠ 1 := by
    rw [Ne, proj_eq_one_iff]
    rintro ⟨d, -, hd⟩
    rw [coe_torus3] at hd
    have e0 := congrFun (congrFun hd 0) 0
    have e1 := congrFun (congrFun hd 1) 1
    simp only [diagonal_apply_eq, scalar_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      at e0 e1
    have haa : a = a⁻¹ * a⁻¹ := Units.ext (e0.trans e1.symm)
    have h3 : a ^ 3 = 1 := by
      have : a * a * a = 1 := by
        calc a * a * a = a * a * (a⁻¹ * a⁻¹) := by rw [← haa]
          _ = 1 := by group
      rw [pow_three, ← mul_assoc]
      exact this
    have h4 := orderOf_dvd_of_pow_eq_one h3
    rw [ha] at h4
    have := Nat.le_of_dvd (by norm_num) h4
    omega
  rcases hp.eq_one_or_self_of_dvd _ h1 with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h2
  · exact h

theorem mem_projUnitriangular_of_commute_rootE02 [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {c : K} (hc : c ≠ 0) {y : projectiveSL 3 K}
    (hy : y * proj 3 K (rootE02 c) = proj 3 K (rootE02 c) * y) :
    y ∈ projUnitriangular 3 K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨Y, rfl⟩ := proj_surjective 3 K y
  have hE : rootE02 c * rootE02 c = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_rootE02, Matrix.SpecialLinearGroup.coe_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
    linear_combination c * h2
  have hYE := CFSG.ComponentClassification.OutcomeLocal.commute_of_proj_commute hE hy
  have m := congrArg Subtype.val hYE
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootE02] at m
  have f12 := congrFun (congrFun m 1) 2
  have f22 := congrFun (congrFun m 2) 2
  have f01 := congrFun (congrFun m 0) 1
  have f02 := congrFun (congrFun m 0) 2
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add] at f12 f22 f01 f02
  set M := (Y : Matrix (Fin 3) (Fin 3) K) with hM
  have y10 : M 1 0 = 0 := by
    have : M 1 0 * c = 0 := by linear_combination f12
    exact (mul_eq_zero.mp this).resolve_right hc
  have y20 : M 2 0 = 0 := by
    have : M 2 0 * c = 0 := by linear_combination f22
    exact (mul_eq_zero.mp this).resolve_right hc
  have y21 : M 2 1 = 0 := by
    have : c * M 2 1 = 0 := by linear_combination -f01
    exact (mul_eq_zero.mp this).resolve_left hc
  have y22 : M 2 2 = M 0 0 := by
    have : c * (M 2 2 - M 0 0) = 0 := by linear_combination -f02
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  have hdet : M 0 0 * M 0 0 * M 1 1 = 1 := by
    have := Y.2
    rw [Matrix.det_fin_three] at this
    rw [← hM, y10, y20, y21, y22] at this
    linear_combination this
  have ha0 : M 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  have ha3 : M 0 0 ^ 3 = 1 := by
    have := Fintype.ofFinite K
    have hc4 : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
    have := FiniteField.pow_card_sub_one_eq_one (M 0 0) ha0
    rwa [hc4] at this
  have y11 : M 1 1 = M 0 0 := by linear_combination (-(M 1 1)) * ha3 + M 0 0 * hdet
  set a : Kˣ := Units.mk0 (M 0 0) ha0 with hadef
  have hai : (a⁻¹) ^ 3 = 1 := by
    rw [inv_pow, inv_eq_one]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, hadef, Units.val_mk0, ha3, Units.val_one])
  set s := scalarElement (n := 3) a⁻¹ hai with hs
  have hsY : s * Y ∈ unitriangular 3 K := by
    have hcoe : ((s * Y : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        diagonal (fun _ => (M 0 0)⁻¹) * M := by
      rw [Matrix.SpecialLinearGroup.coe_mul, hs, coe_scalarElement, scalar_apply, hadef,
        Units.val_inv_eq_inv_val, Units.val_mk0]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hcoe, diagonal_mul]
      fin_cases i <;> fin_cases j <;> simp [y10, y20, y21] at hij ⊢
    · rw [hcoe, diagonal_mul]
      fin_cases i <;> simp [y11, y22, inv_mul_cancel₀ ha0]
  refine ⟨s * Y, hsY, ?_⟩
  rw [map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars _ hai), one_mul]

end Matrices

theorem noThree_conj {X : Type*} [Group X] {u : X} (g : X)
    (h : ∀ y : X, y * u = u * y → orderOf y ≠ 3) :
    ∀ y : X, y * (g * u * g⁻¹) = g * u * g⁻¹ * y → orderOf y ≠ 3 := by
  intro y hy
  have h1 : (g⁻¹ * y * g) * u = u * (g⁻¹ * y * g) := by
    calc (g⁻¹ * y * g) * u = g⁻¹ * (y * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹ * y) * g := by rw [hy]
      _ = u * (g⁻¹ * y * g) := by group
  have h2 : orderOf (g⁻¹ * y * g) = orderOf y := by
    rw [show g⁻¹ * y * g = MulAut.conj g⁻¹ y by simp, MulEquiv.orderOf_eq]
  rw [← h2]
  exact h _ h1

theorem kg115L3Input_holds : KG115L3Input := by
  intro f X _ hf h
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_PSL_simplicity X 3 2 f h).2
  obtain ⟨-, K, _, _, hK, ⟨eT⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  let e : X ≃* projectiveSL 3 K :=
    eT.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  refine kg115Excluded_of_mulEquiv e ?_
  have : IsSimpleGroup (projectiveSL 3 K) := e.symm.isSimpleGroup
  rcases (by omega : f = 1 ∨ 2 ≤ f) with rfl | hf2
  ·
    refine kg115Excluded_of_card (n := 2 * 9999360) ?_ (by decide)
    refine (card_mulAut_projectiveSL_dvd' (n := 3) (f := 1) (by norm_num) hK).trans ?_
    rw [mul_one]
    exact Nat.mul_dvd_mul_left 2 (card_GL_dvd_of_card_two (Or.inl rfl) (hK.trans (by norm_num)))
  · have hf1 : 1 ≤ f := by omega
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨P₀, hP₀⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
    have hS₀ : IsPGroup 2 (projUnitriangular 3 K) := by
      rw [← hP₀]
      exact P₀.isPGroup'
    have hS₀i : ¬ 2 ∣ (projUnitriangular 3 K).index := by
      rw [← hP₀]
      exact P₀.not_dvd_index
    have h4 : 4 ∣ Nat.card (projectiveSL 3 K) := by
      refine dvd_trans ?_ (card_subgroup_dvd_card (projUnitriangular 3 K))
      rw [card_projUnitriangular, hK, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact pow_dvd_pow 2 (by omega)
    have hno3 := sylowTwoNoThree_of_twoCentral
      (involutionConstrained_projectiveSL hf1 (by norm_num) hK).twoCentral h4
    refine kg115Excluded_of_simple fun hc => kg115Excluded_of_at hc hno3 ?_
    intro S hS hSi l hl hlc hl1
    rcases (by omega : f = 2 ∨ 3 ≤ f) with rfl | hf3
    ·
      refine kg115At_of_noThree (forall_center_of_conj hS₀ hS₀i
        (Q := fun u => ∀ y, y * u = u * y → orderOf y ≠ 3) (fun g _ hu => noThree_conj g hu) ?_
        S hS hSi l hl hlc hl1)
      intro u hu huc hu1 y hy
      obtain ⟨c, hc, rfl⟩ := exists_rootE02_of_mem_center hu huc hu1
      have hyU := mem_projUnitriangular_of_commute_rootE02 (hK.trans (by norm_num)) hc hy
      obtain ⟨k, hk⟩ := hS₀ ⟨y, hyU⟩
      have hyk : y ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      intro h3
      have h5 := orderOf_dvd_of_pow_eq_one hyk
      rw [h3] at h5
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5) (by norm_num)
    ·
      refine kg115At_of_prime (forall_center_of_conj hS₀ hS₀i
        (Q := fun u => ∃ ℓ : projectiveSL 3 K, ℓ * u = u * ℓ ∧
          ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ orderOf ℓ = p) (fun g _ hu => prime_conj g hu) ?_
        S hS hSi l hl hlc hl1)
      intro u hu huc hu1
      obtain ⟨c, -, rfl⟩ := exists_rootE02_of_mem_center hu huc hu1
      exact exists_prime_commute_rootE02 hK hf3 c

end CFSG.Quasithin.H13.KG14726

end
