module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLieA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeDvdLieB
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
public import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusTop2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private theorem s16h_three_dvd_card_alternatingGroup {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  haveI : NeZero n := ⟨by omega⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have hac : a ≠ c := by simp [a, c, Fin.ext_iff]
  have hbc : b ≠ c := by simp [b, c, Fin.ext_iff]
  let σ : Equiv.Perm (Fin n) := Equiv.swap a b * Equiv.swap a c
  have hthree : Equiv.Perm.IsThreeCycle σ :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hmem : σ ∈ alternatingGroup (Fin n) := hthree.mem_alternatingGroup
  have hord : orderOf (⟨σ, hmem⟩ : alternatingGroup (Fin n)) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hthree.orderOf
  have hdvd : orderOf (⟨σ, hmem⟩ : alternatingGroup (Fin n)) ∣
      Nat.card (alternatingGroup (Fin n)) := orderOf_dvd_natCard _
  rwa [hord] at hdvd

theorem s16h_three_dvd_of_isSLn {X : Type} [Group X] {n a : ℕ} (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSLn X n a) : 3 ∣ Nat.card X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hnt : Nontrivial X := s16h_nontrivial_of_isQuasisimple hX
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n ≤ 1 := by omega
    haveI : Subsingleton ↥(StatedSL n K) := s16h_subsingleton_statedSL_of_le_one hn1
    haveI : Subsingleton X := ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  have hformula : Nat.card X = Nat.card K ^ (n * (n - 1) / 2) *
      ∏ i ∈ Finset.Icc 2 n, (Nat.card K ^ i - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL,
      CFSG.OrderReductions.LinearOrders.card_specialLinear K n (by omega)]
  rw [hformula]
  have hq : 3 ∣ Nat.card K ^ 2 - 1 := by
    rw [hKcard]
    exact s16h_three_dvd_two_pow_sq_sub_one
  exact dvd_mul_of_dvd_right (s16h_three_dvd_prod_Icc hq hn2) _

theorem s16h_three_dvd_of_isSpn {X : Type} [Group X] {n a : ℕ} (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSpn X n a) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hnt : Nontrivial X := s16h_nontrivial_of_isQuasisimple hX
  have hk1 : 1 ≤ n / 2 := by
    by_contra hlt
    have hk0 : n / 2 = 0 := by omega
    have hcard : Nat.card X = 1 := by
      rw [Nat.card_congr e.toEquiv, hk0, s16h_card_statedSp_zero K]
    haveI : Subsingleton X := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  have hformula : Nat.card X = Nat.card K ^ ((n / 2) ^ 2) *
      ∏ j ∈ Finset.Icc 1 (n / 2), (Nat.card K ^ (2 * j) - 1) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp]
  rw [hformula]
  have hq : 3 ∣ Nat.card K ^ (2 * 1) - 1 := by
    rw [hKcard]
    simpa using s16h_three_dvd_two_pow_sq_sub_one
  have hmem : 1 ∈ Finset.Icc 1 (n / 2) := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hk1⟩
  have hprod : 3 ∣ ∏ j ∈ Finset.Icc 1 (n / 2), (Nat.card K ^ (2 * j) - 1) :=
    dvd_trans hq (Finset.dvd_prod_of_mem (fun j => Nat.card K ^ (2 * j) - 1) hmem)
  exact dvd_mul_of_dvd_right hprod _

private def s16h_diag2 {K : Type} [Field K] (A : GL (Fin 1 ⊕ Fin 1) K) : Prop :=
  (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inr 0) = 0 ∧
    (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inl 0) = 0

private def s16h_anti2 {K : Type} [Field K] (A : GL (Fin 1 ⊕ Fin 1) K) : Prop :=
  (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inl 0) = 0 ∧
    (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inr 0) = 0

private lemma s16h_diag2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_diag2 B) : s16h_diag2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_diag2_comm {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_diag2 B) : Commute A B := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  rw [Commute, SemiconjBy]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2, mul_comm]

private lemma s16h_anti2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hB : s16h_anti2 B) : s16h_diag2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_diag2_anti2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hB : s16h_anti2 B) : s16h_anti2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_anti2_diag2_mul {K : Type} [Field K] {A B : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hB : s16h_diag2 B) : s16h_anti2 (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  refine ⟨?_, ?_⟩ <;>
    simp [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, hA1, hA2, hB1, hB2]

private lemma s16h_isometry_quadPlus_one_class {K : Type} [Field K]
    (g : GL (Fin 1 ⊕ Fin 1) K) (hg : g ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) :
    s16h_diag2 g ∨ s16h_anti2 g := by
  have hquad : ∀ v : Fin 1 ⊕ Fin 1 → K,
      StatedQuadPlus 1 K v = v (Sum.inl 0) * v (Sum.inr 0) := by
    intro v
    simp [StatedQuadPlus, CFSG.MatrixModel.plusQuadCore, Fin.sum_univ_one]
  set p := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inl 0) with hp
  set q := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inl 0) (Sum.inr 0) with hq
  set r := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inl 0) with hr
  set s := (g : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) (Sum.inr 0) (Sum.inr 0) with hs
  have h1 : p * r = 0 := by
    have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore hg
      (Pi.single (Sum.inl 0) 1)
    rw [hquad, hquad] at h
    simpa [Matrix.mulVec_single_one, hp, hr, Pi.single_apply] using h
  have h2 : q * s = 0 := by
    have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore hg
      (Pi.single (Sum.inr 0) 1)
    rw [hquad, hquad] at h
    simpa [Matrix.mulVec_single_one, hq, hs, Pi.single_apply] using h
  have h3 : (p + q) * (r + s) = 1 := by
    have h := CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore hg
      (Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1)
    rw [hquad, hquad] at h
    simp only [Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply,
      Pi.single_eq_same, Pi.single_eq_of_ne (by simp : (Sum.inl 0 : Fin 1 ⊕ Fin 1) ≠ Sum.inr 0),
      add_zero, mul_one, zero_mul, hp, hq, hr, hs] at h
    simpa using h
  have h3' : p * s + q * r = 1 := by
    have e : (p + q) * (r + s) = p * s + q * r + (p * r + q * s) := by ring
    rw [e, h1, h2, add_zero] at h3
    simpa using h3
  by_cases hp0 : p = 0
  · right
    refine ⟨hp0, ?_⟩
    have hqr : q * r = 1 := by rw [hp0, zero_mul, zero_add] at h3'; exact h3'
    have hq0 : q ≠ 0 := by intro h0; rw [h0, zero_mul] at hqr; exact zero_ne_one hqr
    exact (mul_eq_zero.mp h2).resolve_left hq0
  · left
    have hr0 : r = 0 := (mul_eq_zero.mp h1).resolve_left hp0
    refine ⟨?_, hr0⟩
    have hps : p * s = 1 := by rw [hr0, mul_zero, add_zero] at h3'; exact h3'
    have hs0 : s ≠ 0 := by intro h0; rw [h0, mul_zero] at hps; exact zero_ne_one hps
    exact (mul_eq_zero.mp h2).resolve_right hs0

private lemma s16h_not_diag2_and_anti2 {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (h1 : s16h_diag2 A) (h2 : s16h_anti2 A) : False := by
  have hzero : (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) = 0 := by
    ext i j
    rcases i with i | i <;> fin_cases i <;> rcases j with j | j <;> fin_cases j <;>
      simp [h1.1, h1.2, h2.1, h2.2]
  have h : ((A * A⁻¹ : GL (Fin 1 ⊕ Fin 1) K) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) =
      ((1 : GL (Fin 1 ⊕ Fin 1) K) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) :=
    congrArg Units.val (mul_inv_cancel A)
  rw [Units.val_mul, hzero, zero_mul, Units.val_one] at h
  exact zero_ne_one h

private lemma s16h_diag2_inv {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_diag2 A) (hAis : A ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) :
    s16h_diag2 A⁻¹ := by
  rcases s16h_isometry_quadPlus_one_class A⁻¹ (inv_mem hAis) with h | h
  · exact h
  · exfalso
    have h' := s16h_anti2_diag2_mul h hA
    rw [inv_mul_cancel] at h'
    exact s16h_not_diag2_and_anti2 (by simp [s16h_diag2]) h'

private lemma s16h_anti2_inv {K : Type} [Field K] {A : GL (Fin 1 ⊕ Fin 1) K}
    (hA : s16h_anti2 A) (hAis : A ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) :
    s16h_anti2 A⁻¹ := by
  rcases s16h_isometry_quadPlus_one_class A⁻¹ (inv_mem hAis) with h | h
  · exfalso
    have h' := s16h_diag2_anti2_mul h hA
    rw [inv_mul_cancel] at h'
    exact s16h_not_diag2_and_anti2 (by simp [s16h_diag2]) h'
  · exact h

private lemma s16h_diag2_commutator {K : Type} [Field K] {g h : GL (Fin 1 ⊕ Fin 1) K}
    (hg : g ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K))
    (hh : h ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K)) :
    s16h_diag2 ⁅g, h⁆ := by
  have dg := s16h_isometry_quadPlus_one_class g hg
  have dh := s16h_isometry_quadPlus_one_class h hh
  rw [commutatorElement_def]
  rcases dg with dg | dg <;> rcases dh with dh | dh
  · exact s16h_diag2_mul (s16h_diag2_mul (s16h_diag2_mul dg dh)
      (s16h_diag2_inv dg hg)) (s16h_diag2_inv dh hh)
  · exact s16h_anti2_mul (s16h_anti2_diag2_mul (s16h_diag2_anti2_mul dg dh)
      (s16h_diag2_inv dg hg)) (s16h_anti2_inv dh hh)
  · exact s16h_diag2_mul (s16h_anti2_mul (s16h_anti2_diag2_mul dg dh)
      (s16h_anti2_inv dg hg)) (s16h_diag2_inv dh hh)
  · exact s16h_anti2_mul (s16h_diag2_anti2_mul (s16h_anti2_mul dg dh)
      (s16h_anti2_inv dg hg)) (s16h_anti2_inv dh hh)

private lemma s16h_isMulCommutative_statedOmega_quadPlus_one {K : Type} [Field K] :
    IsMulCommutative ↥(StatedOmega (StatedQuadPlus 1 K)) := by
  have hC : ({g : GL (Fin 1 ⊕ Fin 1) K |
      ∃ g₁ ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K),
        ∃ g₂ ∈ CFSG.MatrixModel.isometryCore (StatedQuadPlus 1 K), ⁅g₁, g₂⁆ = g}).Pairwise
      Commute := by
    intro a ha b hb _
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := ha
    obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hb
    exact s16h_diag2_comm (s16h_diag2_commutator hg₁ hg₂) (s16h_diag2_commutator hh₁ hh₂)
  exact Subgroup.isMulCommutative_closure hC

private lemma s16h_three_dvd_statedOmega_quadPlus_two {K : Type} [Field K] [CharP K 2] :
    3 ∣ Nat.card (StatedOmega (StatedQuadPlus 2 K)) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  let σ : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩
  let M : Matrix.SpecialLinearGroup (Fin 2) K :=
    ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩
  have hA2 : A * A = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [A, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hσ2 : σ * σ = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [σ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hAinv : A⁻¹ = A := (mul_eq_one_iff_inv_eq).mp hA2
  have hσinv : σ⁻¹ = σ := (mul_eq_one_iff_inv_eq).mp hσ2
  have hM : M = ⁅A, σ⁆ := by
    rw [commutatorElement_def, hAinv, hσinv]
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [M, A, σ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hM3 : M ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;>
      simp [M, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, CharTwo.add_self_eq_zero]
  have hMne : M ≠ 1 := by
    intro h
    have h00 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp only [M, Units.val_one, Matrix.cons_val_zero, Matrix.of_apply, Matrix.one_apply_eq] at h00
    exact zero_ne_one h00
  have hmem : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M ∈
      StatedOmega (StatedQuadPlus 2 K) := by
    rw [hM, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1_mem_orthGroup A)
      (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1_mem_orthGroup σ)
  have hpow :
      (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M) ^ 3 = 1 := by
    rw [← map_pow, hM3, map_one]
  have hdvd :
      orderOf (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M) ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr hpow
  have hne :
      orderOf (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M) ≠ 1 := by
    intro h1
    have h2 : CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M = 1 :=
      orderOf_eq_one_iff.mp h1
    exact hMne (CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1_injective
      (by rw [h2, map_one]))
  have hd := orderOf_dvd_natCard
    (⟨CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaPlusCell.j1 M, hmem⟩ :
      ↥(StatedOmega (StatedQuadPlus 2 K)))
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h0 | h3
  · exact absurd h0 hne
  · rw [Subgroup.orderOf_mk, h3] at hd
    exact hd

private lemma s16h_card_proj_omega_quadPlus {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hk : 1 ≤ k) :
    Nat.card (StatedProj (StatedOmega (StatedQuadPlus k K))) =
      Nat.card (StatedOmega (StatedQuadPlus k K)) := by
  haveI : NeZero k := ⟨by omega⟩
  refine CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
    (Q := CFSG.LieType.Universal.Spin.quadPlus k K) (Q₀ := StatedQuadPlus k K)
    (CFSG.LieType.Universal.Spin.coe_quadPlus k K) ?_
  refine ⟨Pi.single (Sum.inl (0 : Fin k)) 1 + Pi.single (Sum.inr (0 : Fin k)) 1, ?_⟩
  rw [CFSG.LieType.Universal.Spin.quadPlus_apply]
  simp [Pi.single_apply, Finset.sum_eq_single]

private lemma s16h_three_dvd_proj_omegaPlus_ge_three {K : Type} [Field K] [Finite K] [CharP K 2]
    {a k : ℕ} (hK : Nat.card K = 2 ^ a) (hk : 3 ≤ k) :
    3 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadPlus k K))) := by
  have hZ := CFSG.RankThree.GF2n.Smith81.card_statedOmega_plus_eq (K := K) hk
  have h3N : 3 ∣ Nat.card (StatedOmega (StatedQuadPlus k K)) := by
    apply Int.natCast_dvd_natCast.mp
    rw [hZ]
    have hmem : 1 ∈ Finset.Icc 1 (k - 1) := by rw [Finset.mem_Icc]; omega
    have hfac : (3 : ℤ) ∣ ((Nat.card K : ℤ) ^ (2 * 1) - 1) := by
      have hnat : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact s16h_three_dvd_two_pow_sq_sub_one
      have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow 2 (Nat.card K) Nat.card_pos)]
        push_cast
        ring
      have := Int.natCast_dvd_natCast.mpr hnat
      rw [hcast] at this
      simpa using this
    exact dvd_mul_of_dvd_right
      (dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => (Nat.card K : ℤ) ^ (2 * i) - 1) hmem)) _
  rw [← s16h_card_proj_omega_quadPlus (K := K) (show 1 ≤ k by omega)] at h3N
  exact h3N

theorem s16h_three_dvd_of_isOmegaPlus {X : Type} [Group X] {n a : ℕ}
    (hX : CFSG.Open.IsQuasisimple X) (h : IsOmegaPlus X n a) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hnc := s16h_not_isMulCommutative_of_isQuasisimple hX
  by_cases hk1 : n / 2 ≤ 1
  · exfalso
    haveI hΩ : IsMulCommutative ↥(StatedOmega (StatedQuadPlus (n / 2) K)) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with h0 | h1
      · rw [h0]
        haveI : Subsingleton (GL (Fin 0 ⊕ Fin 0) K) :=
          Subsingleton.units_of_isUnit fun a _ => Subsingleton.elim a 1
        exact IsMulCommutative.of_comm fun x y => Subsingleton.elim _ _
      · rw [h1]
        exact s16h_isMulCommutative_statedOmega_quadPlus_one
    haveI hP : IsMulCommutative (StatedProj (StatedOmega (StatedQuadPlus (n / 2) K))) := by
      refine IsMulCommutative.of_comm fun x y => ?_
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact congrArg (QuotientGroup.mk' _) (mul_comm' x' y')
    exact hnc (IsMulCommutative.of_comm fun x y => e.injective (by
      rw [map_mul, map_mul]
      exact mul_comm' (e x) (e y)))
  · have ha1 : 1 ≤ a := by
      rcases Nat.eq_zero_or_pos a with h0 | h0
      · rw [h0, pow_zero] at hKcard
        have h1 := Finite.one_lt_card (α := K)
        omega
      · exact h0
    haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
    by_cases hk3 : 3 ≤ n / 2
    · have hproj := s16h_three_dvd_proj_omegaPlus_ge_three (K := K) (a := a) (k := n / 2)
        hKcard hk3
      rw [Nat.card_congr e.toEquiv]
      exact hproj
    · have hk2 : n / 2 = 2 := by omega
      have hproj2 : 3 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadPlus 2 K))) := by
        rw [s16h_card_proj_omega_quadPlus (K := K) (k := 2) (by norm_num)]
        exact s16h_three_dvd_statedOmega_quadPlus_two
      rw [Nat.card_congr e.toEquiv, hk2]
      exact hproj2

private lemma s16h_card_proj_omega_quadMinus {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (StatedProj (StatedOmega (StatedQuadMinus k K b c))) =
      Nat.card (StatedOmega (StatedQuadMinus k K b c)) := by
  refine CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedOmega
    (Q := CFSG.LieType.Universal.Spin.quadMinus k K b c) (Q₀ := StatedQuadMinus k K b c)
    (CFSG.LieType.Universal.Spin.coe_quadMinus k K b c) ?_
  refine ⟨Pi.single (Sum.inr (Sum.inr 0)) 1, ?_⟩
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  simp [Pi.single_apply, Finset.sum_eq_single]

private lemma s16h_three_dvd_proj_omegaMinus_ge_two {K : Type} [Field K] [Finite K] [CharP K 2]
    {a k : ℕ} (hK : Nat.card K = 2 ^ a) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hk : 2 ≤ k) :
    3 ∣ Nat.card (StatedProj (StatedOmega (StatedQuadMinus k K b c))) := by
  have hZ := CFSG.RankThree.GF2n.Smith81.card_statedOmega_minus_eq_of_two_le (K := K) hk hirr
  have h3N : 3 ∣ Nat.card (StatedOmega (StatedQuadMinus k K b c)) := by
    apply Int.natCast_dvd_natCast.mp
    rw [hZ]
    have hmem : 1 ∈ Finset.Icc 1 (k - 1) := by rw [Finset.mem_Icc]; omega
    have hfac : (3 : ℤ) ∣ ((Nat.card K : ℤ) ^ (2 * 1) - 1) := by
      have hnat : 3 ∣ Nat.card K ^ 2 - 1 := by rw [hK]; exact s16h_three_dvd_two_pow_sq_sub_one
      have hcast : ((Nat.card K ^ 2 - 1 : ℕ) : ℤ) = (Nat.card K : ℤ) ^ 2 - 1 := by
        rw [Nat.cast_sub (Nat.one_le_pow 2 (Nat.card K) Nat.card_pos)]
        push_cast
        ring
      have := Int.natCast_dvd_natCast.mpr hnat
      rw [hcast] at this
      simpa using this
    exact dvd_mul_of_dvd_right
      (dvd_trans hfac (Finset.dvd_prod_of_mem (fun i => (Nat.card K : ℤ) ^ (2 * i) - 1) hmem)) _
  rw [← s16h_card_proj_omega_quadMinus (K := K) (k := k) hirr] at h3N
  exact h3N

theorem s16h_three_dvd_of_isOmegaMinus {X : Type} [Group X] {n a : ℕ}
    (hX : CFSG.Open.IsQuasisimple X) (h : IsOmegaMinus X n a) : 3 ∣ Nat.card X := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hnc := s16h_not_isMulCommutative_of_isQuasisimple hX
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero] at hKcard
      have h1 := Finite.one_lt_card (α := K)
      omega
    · exact h0
  haveI hchar : CharP K 2 := CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  by_cases hk2 : 2 ≤ n / 2
  · have hproj := s16h_three_dvd_proj_omegaMinus_ge_two (K := K) (a := a) (k := n / 2)
      hKcard hirr hk2
    rw [Nat.card_congr e.toEquiv]
    exact hproj
  · have hkle : n / 2 ≤ 1 := Nat.lt_succ_iff.mp (not_le.1 hk2)
    haveI hΩ : IsMulCommutative ↥(StatedOmega (StatedQuadMinus (n / 2) K b c)) :=
      IsMulCommutative.of_comm fun a b => Subtype.ext
        (s16h_comm_statedOmega_quadMinus_of_le_one (k := n / 2) hirr hkle a a.2 b b.2)
    haveI hP : IsMulCommutative (StatedProj (StatedOmega (StatedQuadMinus (n / 2) K b c))) := by
      refine IsMulCommutative.of_comm fun x y => ?_
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact congrArg (QuotientGroup.mk' _) (mul_comm' x' y')
    exact absurd (IsMulCommutative.of_comm fun x y => e.injective (by
      rw [map_mul, map_mul]
      exact mul_comm' (e x) (e y))) hnc

theorem s16h_three_dvd_of_isSUn {X : Type} [Group X] {n a : ℕ} (hX : CFSG.Open.IsQuasisimple X)
    (h : IsSUn X n a) : 3 ∣ Nat.card X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI := hKf
  letI := hKfin
  have hnt : Nontrivial X := s16h_nontrivial_of_isQuasisimple hX
  have hn2 : 2 ≤ n := by
    by_contra hlt
    have hn1 : n ≤ 1 := by omega
    haveI : Subsingleton ↥(StatedSU n (2 ^ a) K) := s16h_subsingleton_statedSU_of_le_one hn1
    haveI : Subsingleton X := ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0, pow_zero] at hKcard
      have h1 := Finite.one_lt_card (α := K)
      omega
    · exact h0
  have hPSU := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (K := K)
    (p := 2) (f := a) Nat.prime_two ha1 hKcard hn2
  have hdiv : Nat.card (StatedProj (StatedSU n (2 ^ a) K)) ∣
      Nat.card ↥(StatedSU n (2 ^ a) K) := Subgroup.card_quotient_dvd_card _
  have h3 : 3 ∣ Nat.card (StatedProj (StatedSU n (2 ^ a) K)) := by
    rw [hPSU]
    set q : ℕ := 2 ^ a with hq
    set g : ℕ := Nat.gcd n (q + 1) with hg
    set F : ℕ → ℕ := fun i => (((q : ℤ) ^ i - (-1) ^ i)).toNat with hF
    have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow a 2 (by norm_num)
    have hF2 : F 2 = q ^ 2 - 1 := by
      simp only [hF]
      rw [show (-1 : ℤ) ^ 2 = 1 by norm_num]
      rw [show (q : ℤ) ^ 2 - 1 = ((q ^ 2 - 1 : ℕ) : ℤ) by
        rw [Nat.cast_sub (Nat.one_le_pow 2 q (by omega))]
        push_cast
        ring]
      exact Int.toNat_natCast _
    have hF3 : F 3 = q ^ 3 + 1 := by
      simp only [hF]
      rw [show (-1 : ℤ) ^ 3 = -1 by norm_num, sub_neg_eq_add]
      rw [show (q : ℤ) ^ 3 + 1 = ((q ^ 3 + 1 : ℕ) : ℤ) by
        push_cast
        ring]
      exact Int.toNat_natCast _
    have hmem2 : 2 ∈ Finset.Icc 2 n := by
      rw [Finset.mem_Icc]
      exact ⟨le_rfl, hn2⟩
    have h3F2 : 3 ∣ F 2 := by
      rw [hF2, hq]
      exact s16h_three_dvd_two_pow_sq_sub_one
    have h3P : 3 ∣ ∏ i ∈ Finset.Icc 2 n, F i :=
      dvd_trans h3F2 (Finset.dvd_prod_of_mem F hmem2)
    have h3N : 3 ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, F i :=
      dvd_mul_of_dvd_right h3P _
    have hgq : g ∣ q + 1 := by rw [hg]; exact Nat.gcd_dvd_right n (q + 1)
    have hgF2 : g ∣ F 2 := by
      rw [hF2]
      exact dvd_trans hgq (s16h_add_one_dvd_sq_sub_one hq1)
    have hgN : g ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, F i :=
      dvd_mul_of_dvd_right (dvd_trans hgF2 (Finset.dvd_prod_of_mem F hmem2)) _
    have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right n (by omega)
    by_cases h3g : 3 ∣ g
    · have h3g' : 3 ∣ Nat.gcd n (q + 1) := by rwa [hg] at h3g
      have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.mp h3g').1
      have h3q1 : 3 ∣ q + 1 := (Nat.dvd_gcd_iff.mp h3g').2
      have hn3 : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
      have hmem3 : 3 ∈ Finset.Icc 2 n := by
        rw [Finset.mem_Icc]
        exact ⟨by norm_num, hn3⟩
      have h3g3 : 3 * g ∣ F 3 := by
        rw [hF3]
        exact s16h_three_mul_dvd_pow_add_one hq1 hgq h3q1
      have h3gN : 3 * g ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, F i :=
        dvd_mul_of_dvd_right (dvd_trans h3g3 (Finset.dvd_prod_of_mem F hmem3)) _
      exact s16h_three_dvd_div_of_mul_dvd hg0 hgN h3gN
    · have hcop : Nat.Coprime 3 g := (Nat.prime_three.coprime_iff_not_dvd).mpr h3g
      exact s16h_three_dvd_div_of_coprime hgN h3N hcop
  rw [Nat.card_congr e.toEquiv]
  exact dvd_trans h3 hdiv

theorem s16h_three_dvd_of_isLn {X : Type} [Group X] {n a : ℕ} (h : IsLn X n a) :
    3 ∣ Nat.card X := by
  have hSCM : StatedClassicalModel X .PSL n 2 a :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by simp [CFSG.Blueprint.classicalTags])
  obtain ⟨hadm, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSCM
  letI := hKf
  letI := hKfin
  have hn2 : 2 ≤ n := hadm.2.2.1
  have hformula : Nat.card X = Nat.card K ^ (n * (n - 1) / 2) *
      (∏ i ∈ Finset.Icc 2 n, (Nat.card K ^ i - 1)) /
        Nat.gcd n (Nat.card K - 1) := by
    rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
      (K := K) (by omega)]
  rw [hformula]
  set q : ℕ := Nat.card K with hq
  set g : ℕ := Nat.gcd n (q - 1) with hg
  have ha1 : 1 ≤ a := hadm.2.1
  have hq2 : 2 ≤ q := by
    rw [hKcard]
    simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) ha1
  have hq1 : 1 ≤ q := by omega
  have hmem2 : 2 ∈ Finset.Icc 2 n := by
    rw [Finset.mem_Icc]
    exact ⟨le_rfl, hn2⟩
  have h3F2 : 3 ∣ q ^ 2 - 1 := by
    rw [hKcard]
    exact s16h_three_dvd_two_pow_sq_sub_one
  have h3P : 3 ∣ ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    dvd_trans h3F2 (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem2)
  have h3N : 3 ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    dvd_mul_of_dvd_right h3P _
  have hgq : g ∣ q - 1 := by rw [hg]; exact Nat.gcd_dvd_right n (q - 1)
  have hgF2 : g ∣ q ^ 2 - 1 := dvd_trans hgq (Nat.sub_one_dvd_pow_sub_one q 2)
  have hgN : g ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
    dvd_mul_of_dvd_right (dvd_trans hgF2 (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem2)) _
  have hg0 : 0 < g := by rw [hg]; exact Nat.gcd_pos_of_pos_right n (by omega)
  by_cases h3g : 3 ∣ g
  · have h3g' : 3 ∣ Nat.gcd n (q - 1) := by rwa [hg] at h3g
    have h3n : 3 ∣ n := (Nat.dvd_gcd_iff.mp h3g').1
    have h3q1 : 3 ∣ q - 1 := (Nat.dvd_gcd_iff.mp h3g').2
    have hn3 : 3 ≤ n := Nat.le_of_dvd (by omega) h3n
    have hmem3 : 3 ∈ Finset.Icc 2 n := by
      rw [Finset.mem_Icc]
      exact ⟨by norm_num, hn3⟩
    have h3g3 : 3 * g ∣ q ^ 3 - 1 := s16h_three_mul_dvd_pow_sub_one hq1 hgq h3q1
    have h3gN : 3 * g ∣ q ^ (n * (n - 1) / 2) * ∏ i ∈ Finset.Icc 2 n, (q ^ i - 1) :=
      dvd_mul_of_dvd_right (dvd_trans h3g3 (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) hmem3)) _
    exact s16h_three_dvd_div_of_mul_dvd hg0 hgN h3gN
  · have hcop : Nat.Coprime 3 g := (Nat.prime_three.coprime_iff_not_dvd).mpr h3g
    exact s16h_three_dvd_div_of_coprime hgN h3N hcop

theorem s16h_three_dvd_of_isAlt {X : Type} [Group X] {n : ℕ} (hX : CFSG.Open.IsQuasisimple X)
    (h : UC22.IsAlt X n) : 3 ∣ Nat.card X := by
  obtain ⟨e⟩ := h
  have hnt : Nontrivial X := s16h_nontrivial_of_isQuasisimple hX
  have hn3 : 3 ≤ n := by
    by_contra hlt
    have hcard : Nat.card (Fin n) ≤ 2 := by simp [Nat.card_fin]; omega
    have hbot : alternatingGroup (Fin n) = ⊥ := alternatingGroup.eq_bot_of_card_le_two hcard
    haveI : Subsingleton ↥(alternatingGroup (Fin n)) := by rw [hbot]; infer_instance
    haveI : Subsingleton X := ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
    exact (not_subsingleton_iff_nontrivial.mpr hnt) inferInstance
  rw [Nat.card_congr e.toEquiv]
  exact s16h_three_dvd_card_alternatingGroup hn3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
