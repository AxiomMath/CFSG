module

public import CFSG.RankThree.GF2n.Smith81.S81E7S4
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearOddCentralizer

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
open CFSG.BenderSuzuki.MatrixGroups CFSG.ShultStronglyClosedTI.TwoCoreGrowth

section Linear

theorem exists_eq_add_smul_of_comm {K : Type*} [Field K] {m X : Matrix (Fin 2) (Fin 2) K}
    (hm : ∀ c : K, m ≠ c • (1 : Matrix (Fin 2) (Fin 2) K)) (hX : X * m = m * X) :
    ∃ a b : K, X = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m := by
  have e00 : X 0 0 * m 0 0 + X 0 1 * m 1 0 = m 0 0 * X 0 0 + m 0 1 * X 1 0 := by
    have h := congrFun (congrFun hX 0) 0
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e01 : X 0 0 * m 0 1 + X 0 1 * m 1 1 = m 0 0 * X 0 1 + m 0 1 * X 1 1 := by
    have h := congrFun (congrFun hX 0) 1
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h
  have e10 : X 1 0 * m 0 0 + X 1 1 * m 1 0 = m 1 0 * X 0 0 + m 1 1 * X 1 0 := by
    have h := congrFun (congrFun hX 1) 0
    simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hent : ∃ a b : K, X 0 0 = a + b * m 0 0 ∧ X 0 1 = b * m 0 1 ∧
      X 1 0 = b * m 1 0 ∧ X 1 1 = a + b * m 1 1 := by
    by_cases hq : m 0 1 = 0
    · by_cases hr : m 1 0 = 0
      ·
        have hps : m 1 1 - m 0 0 ≠ 0 := by
          intro h
          apply hm (m 0 0)
          have hs : m 1 1 = m 0 0 := sub_eq_zero.mp h
          ext i j
          fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, hq, hr, hs]
        have hy : X 0 1 * (m 1 1 - m 0 0) = 0 := by
          linear_combination e01 + (X 1 1 - X 0 0) * hq
        have hz : X 1 0 * (m 1 1 - m 0 0) = 0 := by
          linear_combination -e10 + (X 1 1 - X 0 0) * hr
        have hy0 : X 0 1 = 0 := (mul_eq_zero.mp hy).resolve_right hps
        have hz0 : X 1 0 = 0 := (mul_eq_zero.mp hz).resolve_right hps
        obtain ⟨b, hb⟩ : ∃ b : K, b * (m 1 1 - m 0 0) = X 1 1 - X 0 0 :=
          ⟨(X 1 1 - X 0 0) / (m 1 1 - m 0 0), by field_simp⟩
        refine ⟨X 0 0 - b * m 0 0, b, by ring, ?_, ?_, ?_⟩
        · rw [hq, mul_zero, hy0]
        · rw [hr, mul_zero, hz0]
        · linear_combination -hb
      ·
        obtain ⟨b, hb⟩ : ∃ b : K, b * m 1 0 = X 1 0 :=
          ⟨X 1 0 / m 1 0, by field_simp⟩
        refine ⟨X 0 0 - b * m 0 0, b, by ring, ?_, ?_, ?_⟩
        · have h : m 1 0 * X 0 1 = m 1 0 * (b * m 0 1) := by
            linear_combination e00 + (X 1 0 - b * m 1 0) * hq
          exact mul_left_cancel₀ hr h
        · exact hb.symm
        · have h : m 1 0 * X 1 1 = m 1 0 * (X 0 0 - b * m 0 0 + b * m 1 1) := by
            linear_combination e10 + (m 0 0 - m 1 1) * hb
          exact mul_left_cancel₀ hr h
    ·
      obtain ⟨b, hb⟩ : ∃ b : K, b * m 0 1 = X 0 1 :=
        ⟨X 0 1 / m 0 1, by field_simp⟩
      refine ⟨X 0 0 - b * m 0 0, b, by ring, hb.symm, ?_, ?_⟩
      · have h : m 0 1 * X 1 0 = m 0 1 * (b * m 1 0) := by
          linear_combination -e00 - m 1 0 * hb
        exact mul_left_cancel₀ hq h
      · have h : m 0 1 * X 1 1 = m 0 1 * (X 0 0 - b * m 0 0 + b * m 1 1) := by
          linear_combination -e01 + (m 0 0 - m 1 1) * hb
        exact mul_left_cancel₀ hq h
  obtain ⟨a, b, h00, h01, h10, h11⟩ := hent
  refine ⟨a, b, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h00, h01, h10, h11]

theorem exists_comm_orderOf_card_pm_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K) {m : Matrix.SpecialLinearGroup (Fin 2) K} (hm1 : m ≠ 1)
    (hodd : Odd (orderOf m)) :
    ∃ m₀ : Matrix.SpecialLinearGroup (Fin 2) K, m₀ * m = m * m₀ ∧
      (orderOf m₀ = Nat.card K - 1 ∨ orderOf m₀ = Nat.card K + 1) := by
  have hKeven : Even (Nat.card K) := by
    let : Fintype K := Fintype.ofFinite K
    have hchar : ringChar K = 2 := ringChar.eq K 2
    rw [Nat.card_eq_fintype_card, Nat.even_iff]
    exact FiniteField.even_card_iff_char_two.mp hchar
  obtain ⟨f, hf, hcard⟩ := even_field_binary_size hKeven hq
  have hcentre : ∀ A : Matrix.SpecialLinearGroup (Fin 2) K,
      A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) → A = 1 := by
    intro A hA
    obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    rw [Fintype.card_fin] at hr
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr - (r - 1) * h2
    have hr1 : r = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_one, ← hAr, hr1, map_one]
  let π : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2MatrixGroup K :=
    QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro A hA
    exact hcentre A ((QuotientGroup.eq_one_iff
      (N := Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A).mp hA)
  have hx1 : π m ≠ 1 := by
    intro h
    apply hm1
    apply hπinj
    rw [h, map_one]
  have hxodd : Odd (orderOf (π m)) := Odd.of_dvd_nat hodd (orderOf_map_dvd π m)
  obtain ⟨hcyc, hCcard, -⟩ :=
    psl2_even_odd_element_full_centralizer f hf hcard (π m) hx1 hxodd
  haveI := hcyc
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard
    (α := ↥(Subgroup.centralizer ({π m} : Set (PSL2MatrixGroup K))))
  have hcomm : (g : PSL2MatrixGroup K) * π m = π m * (g : PSL2MatrixGroup K) :=
    Subgroup.mem_centralizer_singleton_iff.mp g.2
  obtain ⟨m₀, hm₀⟩ := QuotientGroup.mk_surjective (g : PSL2MatrixGroup K)
  have hπm₀ : π m₀ = (g : PSL2MatrixGroup K) := hm₀
  have hmm : π (m₀ * m) = π (m * m₀) := by
    rw [map_mul, map_mul, hπm₀]
    exact hcomm
  refine ⟨m₀, hπinj hmm, ?_⟩
  have hord : orderOf m₀ =
      Nat.card (Subgroup.centralizer ({π m} : Set (PSL2MatrixGroup K))) := by
    calc orderOf m₀ = orderOf (π m₀) := (orderOf_injective π hπinj m₀).symm
      _ = orderOf (g : PSL2MatrixGroup K) := by rw [hπm₀]
      _ = orderOf g := Subgroup.orderOf_coe g
      _ = Nat.card (Subgroup.centralizer ({π m} : Set (PSL2MatrixGroup K))) := hg
  rw [hord]
  exact hCcard

end Linear

section JOp

variable {K : Type} [Field K]

theorem jOp_poly [CharP K 2] {m : Matrix (Fin 2) (Fin 2) K} {τ : K} (hτ : τ ≠ 0)
    (hm : m * m = τ • m + 1) (a b : K) :
    jOp (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m) =
      (a + (1 + a + b) * τ⁻¹) • (1 : Module.End K (V K)) + (b + (1 + a + b)) • jOp m +
        ((1 + a + b) * τ⁻¹) • (jOp m * jOp m) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hτι : τ * τ⁻¹ = 1 := mul_inv_cancel₀ hτ
  have e00 : m 0 0 * m 0 0 + m 0 1 * m 1 0 = τ * m 0 0 + 1 := by
    have h := congrFun (congrFun hm 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have e01 : m 0 0 * m 0 1 + m 0 1 * m 1 1 = τ * m 0 1 := by
    have h := congrFun (congrFun hm 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have e10 : m 1 0 * m 0 0 + m 1 1 * m 1 0 = τ * m 1 0 := by
    have h := congrFun (congrFun hm 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have e11 : m 1 0 * m 0 1 + m 1 1 * m 1 1 = τ * m 1 1 + 1 := by
    have h := congrFun (congrFun hm 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] using h
  have hA00 : (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m) 0 0 = a + b * m 0 0 := by simp
  have hA01 : (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m) 0 1 = b * m 0 1 := by
    simp [Matrix.one_apply]
  have hA10 : (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m) 1 0 = b * m 1 0 := by
    simp [Matrix.one_apply]
  have hA11 : (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • m) 1 1 = a + b * m 1 1 := by simp
  apply LinearMap.ext
  intro v
  apply Finsupp.ext
  intro i
  have hw : ⇑(jOp m v) = jFun m ⇑v := funext fun c => jOp_apply m v c
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply,
    Module.End.one_apply, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, jOp_apply, hw]
  rcases pr_mem isRoot_theta i with h | h | h
  · simp only [jFun_of_neg h, jFun_of_pos (pr_shift_self isRoot_theta h),
      shift_neg_shift isRoot_theta h, hA00, hA01]
    linear_combination
      (-(((1 + a + b) * τ⁻¹ + (1 + a + b) * m 0 0) * v i + (1 + a + b) * m 0 1 * v (shift theta i)))
        * h2 +
      (-((1 + a + b) * m 0 0 * v i + (1 + a + b) * m 0 1 * v (shift theta i))) * hτι +
      (-((1 + a + b) * τ⁻¹ * v i)) * e00 +
      (-((1 + a + b) * τ⁻¹ * v (shift theta i))) * e01
  · simp only [jFun_of_zero h]
    linear_combination (-(a + b + (1 + a + b) * τ⁻¹) * v i) * h2
  · simp only [jFun_of_pos h, jFun_of_neg (pr_shift_neg isRoot_theta h),
      shift_shift_neg isRoot_theta h, hA10, hA11]
    linear_combination
      (-(((1 + a + b) * τ⁻¹ + (1 + a + b) * m 1 1) * v i + (1 + a + b) * m 1 0 * v (shift (-theta) i)))
        * h2 +
      (-((1 + a + b) * m 1 1 * v i + (1 + a + b) * m 1 0 * v (shift (-theta) i))) * hτι +
      (-((1 + a + b) * τ⁻¹ * v i)) * e11 +
      (-((1 + a + b) * τ⁻¹ * v (shift (-theta) i))) * e10

end JOp

section Regular

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem units_comm_iff {T w : (Module.End K (V K))ˣ} :
    T * w = w * T ↔ (T : Module.End K (V K)) * (w : Module.End K (V K)) =
      (w : Module.End K (V K)) * (T : Module.End K (V K)) := by
  constructor
  · intro h
    have := congrArg Units.val h
    simpa only [Units.val_mul] using this
  · intro h
    apply Units.ext
    simpa only [Units.val_mul] using h

theorem exists_regular_torus (hq : 4 ≤ Nat.card K) {v : (Module.End K (V K))ˣ} (hvJ : v ∈ Jgrp K)
    (hv1 : v ≠ 1) (hodd : Odd (orderOf v)) :
    ∃ v₀ ∈ Jgrp K, (orderOf v₀ = Nat.card K - 1 ∨ orderOf v₀ = Nat.card K + 1) ∧
      ∀ T : Module.End K (V K), T * (v : Module.End K (V K)) = (v : Module.End K (V K)) * T →
        T * (v₀ : Module.End K (V K)) = (v₀ : Module.End K (V K)) * T := by
  rw [Jgrp_eq_range] at hvJ
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hvJ
  have hm1 : m ≠ 1 := fun h => hv1 (by rw [h, map_one])
  have hmodd : Odd (orderOf m) := by
    rw [← orderOf_injective (jHom (K := K)) jHom_injective m]
    exact hodd
  obtain ⟨m₀, hcomm, hord⟩ := exists_comm_orderOf_card_pm_one hq hm1 hmodd
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hCH : (m : Matrix (Fin 2) (Fin 2) K) * (m : Matrix (Fin 2) (Fin 2) K) =
      Matrix.trace (m : Matrix (Fin 2) (Fin 2) K) • (m : Matrix (Fin 2) (Fin 2) K) + 1 := by
    have h := CFSG.SeitzReduction.F4Pilot.sq_eq_trace_smul_sub_one m
    rw [Matrix.SpecialLinearGroup.coe_pow, pow_two] at h
    rw [h, sub_eq_add_neg, CharTwo.neg_eq]
  have hτ : Matrix.trace (m : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
    intro h0
    have hmm : m * m = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hCH, h0, zero_smul, zero_add,
        Matrix.SpecialLinearGroup.coe_one]
    have hd : orderOf m ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hmm)
    have hc : Nat.Coprime (orderOf m) 2 := Nat.coprime_two_right.mpr hmodd
    have h1 : orderOf m = 1 := Nat.Coprime.eq_one_of_dvd hc hd
    exact hm1 (orderOf_eq_one_iff.mp h1)
  have hns : ∀ c : K, (m : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro c hc
    have hdet : ((m : Matrix (Fin 2) (Fin 2) K)).det = 1 := m.2
    rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
    have hsq : (c - 1) ^ 2 = 0 := by linear_combination hdet - (c - 1) * h2
    have hc1 : c = 1 := sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp hsq)
    apply hm1
    apply Subtype.ext
    rw [hc, hc1, one_smul, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨a, b, hab⟩ := exists_eq_add_smul_of_comm hns
    (show (m₀ : Matrix (Fin 2) (Fin 2) K) * (m : Matrix (Fin 2) (Fin 2) K) =
      (m : Matrix (Fin 2) (Fin 2) K) * (m₀ : Matrix (Fin 2) (Fin 2) K) from
      congrArg Subtype.val hcomm)
  have hm₀J : jHom m₀ ∈ Jgrp K := by
    rw [Jgrp_eq_range]
    exact ⟨m₀, rfl⟩
  refine ⟨jHom m₀, hm₀J, ?_, ?_⟩
  · rw [orderOf_injective (jHom (K := K)) jHom_injective m₀]
    exact hord
  · intro T hT
    have hu : Commute T (jOp (m : Matrix (Fin 2) (Fin 2) K)) := hT
    show T * jOp (m₀ : Matrix (Fin 2) (Fin 2) K) = jOp (m₀ : Matrix (Fin 2) (Fin 2) K) * T
    rw [hab, jOp_poly hτ hCH a b]
    exact (((Commute.one_right T).smul_right _).add_right (hu.smul_right _)).add_right
      ((hu.mul_right hu).smul_right _)

theorem rootPoint_of_commuting_rootElt_of_odd (hq : 4 ≤ Nat.card K) {v t : (Module.End K (V K))ˣ}
    (hvJ : v ∈ Jgrp K) (hv1 : v ≠ 1) (hodd : Odd (orderOf v)) (ht : IsRootElt t)
    (hcomm : t * v = v * t) :
    ∃ w : V K, w ≠ 0 ∧ w ∈ V0 K ∧ w ∈ LinearMap.range ((t : Module.End K (V K)) - 1) ∧
      IsHWVec w := by
  obtain ⟨v₀, hv₀J, hv₀ord, hv₀comm⟩ := exists_regular_torus hq hvJ hv1 hodd
  exact rootPoint_of_commuting_rootElt hq hv₀J hv₀ord ht
    (units_comm_iff.mpr (hv₀comm _ (units_comm_iff.mp hcomm)))

end Regular

end CFSG.RankThree.GF2n.Smith81.E7Model
