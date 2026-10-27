module

public import CFSG.RankThree.PartTwo.KFacts.K73L27
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open scoped MatrixGroups

section Root

variable {K : Type*} [Field K]

theorem psl2Upper_mul_comm {x y : PSL2 K} (hx : x ∈ psl2UpperUnipotentSubgroup K)
    (hy : y ∈ psl2UpperUnipotentSubgroup K) : x * y = y * x := by
  obtain ⟨s, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
  obtain ⟨t, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff y).mp hy
  rw [← map_mul, ← map_mul, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul, add_comm]

theorem psl2Upper_pow_three [CharP K 3] {x : PSL2 K}
    (hx : x ∈ psl2UpperUnipotentSubgroup K) : x ^ 3 = 1 := by
  obtain ⟨s, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff x).mp hx
  rw [← map_pow, pow_succ, pow_two, sl2UpperUnipotent_mul, sl2UpperUnipotent_mul]
  have h3 : s + s + s = 0 := by
    have : (3 : K) = 0 := CharP.cast_eq_zero K 3
    calc s + s + s = 3 * s := by ring
      _ = 0 := by rw [this, zero_mul]
  rw [h3, sl2UpperUnipotent_zero, map_one]

theorem isElemAbelian_of_isPGroup_three_psl2 [Finite K] [CharP K 3] {n : ℕ}
    (hK : Nat.card K = 3 ^ n) {P : Subgroup (PSL2 K)} (hP : IsPGroup 3 P) :
    CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P ≤ Nat.card K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_map_conj_le_psl2UpperUnipotentSubgroup hK hP
  have hmem : ∀ x ∈ P, c * x * c⁻¹ ∈ psl2UpperUnipotentSubgroup K := fun x hx =>
    hc ⟨x, hx, rfl⟩
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have h := psl2Upper_mul_comm (hmem x x.2) (hmem y y.2)
    have h' : c * ((x : PSL2 K) * y) * c⁻¹ = c * ((y : PSL2 K) * x) * c⁻¹ := by
      calc c * ((x : PSL2 K) * y) * c⁻¹ = (c * x * c⁻¹) * (c * y * c⁻¹) := by group
        _ = (c * y * c⁻¹) * (c * x * c⁻¹) := h
        _ = c * ((y : PSL2 K) * x) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h')
  · have h := psl2Upper_pow_three (hmem x hx)
    rw [conj_pow] at h
    have h' : x ^ 3 = c⁻¹ * (c * x ^ 3 * c⁻¹) * c := by group
    rw [h', h]
    group
  · calc Nat.card P = Nat.card (P.map (MulAut.conj c).toMonoidHom) :=
          (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
      _ ≤ Nat.card (psl2UpperUnipotentSubgroup K) := Subgroup.card_le_of_le hc
      _ = Nat.card K := psl2UpperUnipotentSubgroup_card K

theorem isElemAbelian_of_isPGroup_three_of_mulEquiv [Finite K] [CharP K 3] {n : ℕ}
    (hK : Nat.card K = 3 ^ n) {X : Type*} [Group X] (e : X ≃* PSL2 K) {P : Subgroup X}
    (hP : IsPGroup 3 P) : CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P ≤ Nat.card K := by
  have h := isElemAbelian_of_isPGroup_three_psl2 hK (hP.map e.toMonoidHom)
  refine ⟨⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · have h1 : e (x : X) * e (y : X) = e (y : X) * e (x : X) :=
      congrArg Subtype.val (h.1.1.is_comm.comm ⟨e x, x, x.2, rfl⟩ ⟨e y, y, y.2, rfl⟩)
    apply e.injective
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact h1
  · apply e.injective
    rw [map_pow, map_one]
    exact h.1.2 (e x) ⟨x, hx, rfl⟩
  · rw [← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h.2

end Root

section Four

variable {K : Type*} [Field K]

theorem psl2QuotientMap_eq_of_coe_eq_neg {A B : SL(2, K)}
    (h : (B : Matrix (Fin 2) (Fin 2) K) = -(A : Matrix (Fin 2) (Fin 2) K)) :
    psl2QuotientMap K A = psl2QuotientMap K B := by
  rw [psl2QuotientMap, QuotientGroup.mk'_eq_mk']
  refine ⟨A⁻¹ * B, ?_, by group⟩
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by simp, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, h,
    Matrix.mul_neg, Matrix.adjugate_mul, A.2, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]

@[expose] def sl2QI (K : Type*) [Field K] : SL(2, K) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two_of]⟩

@[expose] def sl2QJ (K : Type*) [Field K] [CharP K 3] : SL(2, K) :=
  ⟨!![1, 1; 1, -1], by
    rw [Matrix.det_fin_two_of]
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    linear_combination (-1 : K) * h3⟩

variable [CharP K 3]

omit [CharP K 3] in
theorem coe_sl2QI_mul_self :
    ((sl2QI K * sl2QI K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      -((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QI, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_sl2QJ_mul_self :
    ((sl2QJ K * sl2QJ K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      -((1 : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QJ, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h3

theorem coe_sl2QJ_mul_sl2QI :
    ((sl2QJ K * sl2QI K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      -((sl2QI K * sl2QJ K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2QI, sl2QJ, Matrix.mul_apply, Fin.sum_univ_two]

theorem coe_conj_upper_sl2QI :
    ((sl2UpperUnipotent (1 : K) * sl2QI K * (sl2UpperUnipotent (1 : K))⁻¹ : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) = -((sl2QJ K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [sl2UpperUnipotent_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2QI, sl2QJ, sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h3

theorem coe_conj_upper_sl2QJ :
    ((sl2UpperUnipotent (1 : K) * sl2QJ K * (sl2UpperUnipotent (1 : K))⁻¹ : SL(2, K)) :
        Matrix (Fin 2) (Fin 2) K) =
      ((sl2QJ K * sl2QI K : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  rw [sl2UpperUnipotent_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2QI, sl2QJ, sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | ring1 | linear_combination h3 | linear_combination (-1 : K) * h3

abbrev psl2QI (K : Type*) [Field K] : PSL2 K := psl2QuotientMap K (sl2QI K)

abbrev psl2QJ (K : Type*) [Field K] [CharP K 3] : PSL2 K := psl2QuotientMap K (sl2QJ K)

abbrev psl2U1 (K : Type*) [Field K] : PSL2 K := psl2QuotientMap K (sl2UpperUnipotent (1 : K))

omit [CharP K 3] in
theorem psl2QI_sq : psl2QI K ^ 2 = 1 := by
  rw [pow_two, ← map_mul, ← map_one (psl2QuotientMap K)]
  exact (psl2QuotientMap_eq_of_coe_eq_neg coe_sl2QI_mul_self).symm

theorem psl2QJ_sq : psl2QJ K ^ 2 = 1 := by
  rw [pow_two, ← map_mul, ← map_one (psl2QuotientMap K)]
  exact (psl2QuotientMap_eq_of_coe_eq_neg coe_sl2QJ_mul_self).symm

theorem psl2QI_mul_comm : psl2QI K * psl2QJ K = psl2QJ K * psl2QI K := by
  rw [← map_mul, ← map_mul]
  exact psl2QuotientMap_eq_of_coe_eq_neg coe_sl2QJ_mul_sl2QI

theorem psl2U1_conj_QI : psl2U1 K * psl2QI K * (psl2U1 K)⁻¹ = psl2QJ K := by
  rw [← map_inv, ← map_mul, ← map_mul]
  exact (psl2QuotientMap_eq_of_coe_eq_neg coe_conj_upper_sl2QI).symm

theorem psl2U1_conj_QJ : psl2U1 K * psl2QJ K * (psl2U1 K)⁻¹ = psl2QJ K * psl2QI K := by
  rw [← map_inv, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg (psl2QuotientMap K) (Subtype.ext coe_conj_upper_sl2QJ)

omit [CharP K 3] in
theorem psl2QI_ne_one : psl2QI K ≠ 1 := by
  intro h
  rw [psl2QI, psl2QuotientMap, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff] at h
  obtain ⟨r, -, hr⟩ := h
  have h01 := congrFun (congrFun hr 0) 1
  simp [sl2QI, Matrix.scalar_apply] at h01

@[expose] def psl2FourGroup (K : Type*) [Field K] [CharP K 3] : Subgroup (PSL2 K) :=
  Subgroup.closure {psl2QI K, psl2QJ K}

theorem psl2FourGroup_pow_two {x : PSL2 K} (hx : x ∈ psl2FourGroup K) : x ^ 2 = 1 := by
  have hcomm : ({psl2QI K, psl2QJ K} : Set (PSL2 K)).Pairwise Commute := by
    rintro x (rfl | rfl) y (rfl | rfl) hxy
    · exact absurd rfl hxy
    · exact psl2QI_mul_comm
    · exact psl2QI_mul_comm.symm
    · exact absurd rfl hxy
  have hab := Subgroup.isMulCommutative_closure hcomm
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact psl2QI_sq
    · exact psl2QJ_sq
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
      exact this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem isPGroup_psl2FourGroup : IsPGroup 2 (psl2FourGroup K) := fun x =>
  ⟨1, Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_one]; exact psl2FourGroup_pow_two x.2)⟩

theorem psl2FourGroup_ne_bot : psl2FourGroup K ≠ ⊥ := by
  intro h
  have hI : psl2QI K ∈ psl2FourGroup K := Subgroup.subset_closure (by simp)
  rw [h, Subgroup.mem_bot] at hI
  exact psl2QI_ne_one hI

theorem psl2U1_mem_normalizer_psl2FourGroup [Finite K] :
    psl2U1 K ∈ Subgroup.normalizer (psl2FourGroup K : Set (PSL2 K)) := by
  have hle : (psl2FourGroup K).map (MulAut.conj (psl2U1 K)).toMonoidHom ≤ psl2FourGroup K := by
    rw [psl2FourGroup, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | rfl
    · change psl2U1 K * psl2QI K * (psl2U1 K)⁻¹ ∈ _
      rw [psl2U1_conj_QI]
      exact Subgroup.subset_closure (by simp)
    · change psl2U1 K * psl2QJ K * (psl2U1 K)⁻¹ ∈ _
      rw [psl2U1_conj_QJ]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj (psl2U1 K)).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

end Four

theorem mem_normalizer_map_conj_inv {X : Type*} [Group X] {V : Subgroup X} {c x : X}
    (h : c * x * c⁻¹ ∈ Subgroup.normalizer (V : Set X)) :
    x ∈ Subgroup.normalizer ((V.map (MulAut.conj c⁻¹).toMonoidHom : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro y
  constructor
  · rintro ⟨v, hv, rfl⟩
    refine ⟨c * x * c⁻¹ * v * (c * x * c⁻¹)⁻¹, (h v).mp hv, ?_⟩
    change c⁻¹ * (c * x * c⁻¹ * v * (c * x * c⁻¹)⁻¹) * c⁻¹⁻¹ =
      x * (c⁻¹ * v * c⁻¹⁻¹) * x⁻¹
    group
  · rintro ⟨v, hv, hvy⟩
    change c⁻¹ * v * c⁻¹⁻¹ = x * y * x⁻¹ at hvy
    refine ⟨c * y * c⁻¹, (h _).mpr ?_, ?_⟩
    · have : c * x * c⁻¹ * (c * y * c⁻¹) * (c * x * c⁻¹)⁻¹ = c * (x * y * x⁻¹) * c⁻¹ := by group
      rw [this, ← hvy, show c * (c⁻¹ * v * c⁻¹⁻¹) * c⁻¹ = v by group]
      exact hv
    · change c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y
      group

theorem exists_two_subgroup_of_card_eq_three_psl2 {K : Type*} [Field K] [Finite K] [CharP K 3]
    (hK : Nat.card K % 4 = 3) {P : Subgroup (PSL2 K)} (hP : Nat.card P = 3) :
    ∃ V : Subgroup (PSL2 K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
      P ≤ Subgroup.normalizer (V : Set (PSL2 K)) := by
  classical
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 3
  have hcard : Nat.card K = 3 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hsq : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff, not_not, ← Nat.card_eq_fintype_card]
    exact hK
  obtain ⟨c, hc⟩ := exists_map_conj_eq_zpowers_of_card_eq_three hcard hsq hP
  refine ⟨(psl2FourGroup K).map (MulAut.conj c⁻¹).toMonoidHom, ?_, ?_, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj c⁻¹).injective]
    exact psl2FourGroup_ne_bot
  · exact isPGroup_psl2FourGroup.map _
  · intro x hx
    apply mem_normalizer_map_conj_inv
    have hxc : c * x * c⁻¹ ∈ Subgroup.zpowers (psl2U1 K) := hc ▸ ⟨x, hx, rfl⟩
    exact Subgroup.zpowers_le.mpr psl2U1_mem_normalizer_psl2FourGroup hxc

theorem exists_two_subgroup_of_card_eq_three {X : Type*} [Group X]
    (e : X ≃* PSL2 (GaloisField 3 3)) {P : Subgroup X} (hP : Nat.card P = 3) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ P ≤ Subgroup.normalizer (V : Set X) := by
  obtain ⟨V, hV1, hV2, hPV⟩ := exists_two_subgroup_of_card_eq_three_psl2
    (K := GaloisField 3 3) (by rw [GaloisField.card 3 3 (by norm_num)]; norm_num)
    (P := P.map e.toMonoidHom) (by rw [Subgroup.card_map_of_injective e.injective, hP])
  refine ⟨V.map e.symm.toMonoidHom, ?_, hV2.map _, ?_⟩
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hV1
  · intro x hx
    have h1 := hPV ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff] at h1 ⊢
    intro y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨e x * v * (e x)⁻¹, (h1 v).mp hv, ?_⟩
      change e.symm (e x * v * (e x)⁻¹) = x * e.symm v * x⁻¹
      simp
    · rintro ⟨v, hv, hvy⟩
      change e.symm v = x * y * x⁻¹ at hvy
      refine ⟨e y, (h1 _).mpr ?_, by simp⟩
      have : e.toMonoidHom x * e y * (e.toMonoidHom x)⁻¹ = v := by
        change e x * e y * (e x)⁻¹ = v
        rw [← map_mul, ← map_inv, ← map_mul, ← hvy, MulEquiv.apply_symm_apply]
      rw [this]
      exact hv

section Aut

theorem card_eq_card_ker_mul_card_range {P Q : Type*} [Group P] [Group Q] (f : P →* Q) :
    Nat.card P = Nat.card f.ker * Nat.card f.range := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, mul_comm]

theorem card_ringAut_galoisField_three_three :
    Nat.card (GaloisField 3 3 ≃+* GaloisField 3 3) = 3 := by
  exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_three
    (GaloisField 3 3) (GaloisField.card 3 3 (by norm_num))).1

theorem card_le_of_isPGroup_three_mulAut_psl2_27
    {P : Subgroup (MulAut (PSL2 (GaloisField 3 3)))} (hP : IsPGroup 3 P) : Nat.card P ≤ 81 := by
  set K := GaloisField 3 3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card K = 3 ^ 3 := GaloisField.card 3 3 (by norm_num)
  set ψ : MulAut (PSL2 K) →* (K ≃+* K) :=
    SemidirectProduct.rightHom.comp (semilinearEquivAut K).symm.toMonoidHom with hψ
  set f : P →* (K ≃+* K) := ψ.comp P.subtype with hf
  have hinj : Function.Injective (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) := by
    intro x y hxy
    have hz : x⁻¹ * y ∈ Subgroup.center (PSL2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := DFunLike.congr_fun hxy g
      simp only [MulAut.conj_apply] at h
      calc g * (x⁻¹ * y) = x⁻¹ * (x * g * x⁻¹) * y := by group
        _ = x⁻¹ * (y * g * y⁻¹) * y := by rw [h]
        _ = x⁻¹ * y * g := by group
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at hz
    exact (inv_mul_eq_one.mp hz)
  have hker : P ⊓ ψ.ker ≤ (MulAut.conj : PSL2 K →* MulAut (PSL2 K)).range := by
    rintro σ ⟨hσP, hσψ⟩
    obtain ⟨g, rfl⟩ := mem_range_pglAction_of_rightHom_eq_one (MonoidHom.mem_ker.mp hσψ)
    obtain ⟨k, hk⟩ := hP ⟨_, hσP⟩
    have hk' : pglAction K g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : g ^ 3 ^ k = 1 := pglAction_injective (by rw [map_pow, hk', map_one])
    obtain ⟨x, rfl⟩ := exists_toPGL_eq_of_pow_odd (Odd.pow (by decide)) hg
    exact ⟨x, (pglAction_toPGL K x).symm⟩
  set Q := (P ⊓ ψ.ker).comap (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) with hQ
  have hQ3 : IsPGroup 3 Q := (hP.to_inf_left).comap_of_injective _ hinj
  have hQcard : Nat.card Q ≤ 27 := by
    have := (isElemAbelian_of_isPGroup_three_psl2 hK hQ3).2
    rw [hK] at this
    simpa using this
  have hmap : Q.map (MulAut.conj : PSL2 K →* MulAut (PSL2 K)) = P ⊓ ψ.ker := by
    rw [hQ, Subgroup.map_comap_eq, inf_eq_right.mpr hker]
  have hcard1 : Nat.card (P ⊓ ψ.ker : Subgroup _) ≤ 27 := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
    exact hQcard
  have hcard2 : Nat.card f.ker ≤ 27 := by
    have hle : f.ker.map P.subtype ≤ P ⊓ ψ.ker := by
      rintro _ ⟨σ, hσ, rfl⟩
      exact ⟨σ.2, hσ⟩
    rw [← Subgroup.card_map_of_injective P.subtype_injective]
    exact (Subgroup.card_le_of_le hle).trans hcard1
  have : Finite (K ≃+* K) :=
    Nat.finite_of_card_ne_zero (by rw [card_ringAut_galoisField_three_three]; norm_num)
  have hcard3 : Nat.card f.range ≤ 3 :=
    (Subgroup.card_le_card_group _).trans (le_of_eq card_ringAut_galoisField_three_three)
  rw [card_eq_card_ker_mul_card_range f]
  calc Nat.card f.ker * Nat.card f.range ≤ 27 * 3 := Nat.mul_le_mul hcard2 hcard3
    _ = 81 := by norm_num

theorem card_le_of_isPGroup_three_mulAut {X : Type*} [Group X]
    (e : X ≃* PSL2 (GaloisField 3 3)) {P : Subgroup (MulAut X)} (hP : IsPGroup 3 P) :
    Nat.card P ≤ 81 := by
  have h := card_le_of_isPGroup_three_mulAut_psl2_27 (hP.map (MulAut.congr e).toMonoidHom)
  rwa [Subgroup.card_map_of_injective (MulAut.congr e).injective] at h

end Aut

end CFSG.RankThree.PartTwo.KFacts
