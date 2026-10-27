module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Sp4
public import CFSG.Quasithin.Vol2.Ch10SecKHK3A
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFourSylow
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4D

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K]

theorem exists_sl2_mulVec_eq_single {u : Fin 2 → K} (hu : u ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      ext i
      fin_cases i <;> simp [h0, h1]
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h1]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], ?_⟩, ?_⟩
    · simp [Matrix.det_fin_two, h0]
    · ext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq {u v : Fin 2 → K} (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) K, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ u = v := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_eq_single hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_eq_single hv
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((a⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ u =
      ![1, 0] := by
    rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h1, hb]

theorem sl_mul_inv (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (A : Matrix (Fin 2) (Fin 2) K) *
      ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]

theorem spLevi_one_mul_tau_mul_inv (A : Matrix.SpecialLinearGroup (Fin 2) K)
    {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    spLevi 1 A * tau hC * (spLevi 1 A)⁻¹ =
      tau (C := (A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  apply statedSp_ext
  show spMat (spLevi 1 A * tau hC * (spLevi 1 A)⁻¹) = spMat (tau _)
  rw [← map_inv, spMat_mul, spMat_mul, spMat_leviSp_one, spMat_leviSp_one, inv_inv]
  rw [show spMat (tau hC) = fromBlocks 1 C 0 1 from coe_tau hC,
    show spMat (tau (C := (A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ)
      (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc])) =
      fromBlocks 1 ((A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ) 0 1
      from coe_tau _, fromBlocks_multiply,
    fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [sl_mul_inv, ← transpose_mul, sl_mul_inv, transpose_one]

theorem coe_sl_inv (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (A : Matrix (Fin 2) (Fin 2) K)⁻¹ :=
  (Matrix.inv_eq_right_inv (sl_mul_inv A)).symm

theorem tau_mem_Q2 (j : Fin 2) {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    tau hC ∈ Q2 K j :=
  borelSubgroup_le_Q2 j (unipotent_le_borelSubgroup (tau_mem_unipotent hC))

theorem eq_spLevi_mul_tau [Finite K] (n : ↥(perfectCore (Q2 K 1))) :
    ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C),
      (n : StatedSp 2 K) = spLevi 1 (blkN 1 n) * tau hC := by
  obtain ⟨C, hC, h⟩ := CFSG.QuasithinUnique.A5.G3.N1_shape n
  refine ⟨C, hC, statedSp_ext ?_⟩
  show spMat (n : StatedSp 2 K) = spMat (spLevi 1 (blkN 1 n) * tau hC)
  rw [h, blockMat_eq_mul, spMat_mul, spMat_leviSp_one,
    show spMat (tau hC) = fromBlocks 1 C 0 1 from coe_tau hC, coe_sl_inv]

theorem mul_tau_mul_inv_of_mem [Finite K] (n : ↥(perfectCore (Q2 K 1)))
    {D : Matrix (Fin 2) (Fin 2) K} (hD : Dᵀ = D) :
    (n : StatedSp 2 K) * tau hD * (n : StatedSp 2 K)⁻¹ =
      tau (C := ((blkN 1 n : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *
        D * ((blkN 1 n : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_mul, transpose_mul, transpose_transpose, hD, Matrix.mul_assoc]) := by
  obtain ⟨C, hC, h⟩ := eq_spLevi_mul_tau n
  rw [h, ← spLevi_one_mul_tau_mul_inv]
  have e : spLevi 1 (blkN 1 n) * tau hC * tau hD * (spLevi 1 (blkN 1 n) * tau hC)⁻¹ =
      spLevi 1 (blkN 1 n) * (tau hC * tau hD * (tau hC)⁻¹) * (spLevi 1 (blkN 1 n))⁻¹ := by
    group
  rw [e, tau_comm hC hD, mul_inv_cancel_right]

theorem commutator_tau_spLevi [CharP K 2] (A : Matrix.SpecialLinearGroup (Fin 2) K)
    {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    tau hC * spLevi 1 A * (tau hC)⁻¹ * (spLevi 1 A)⁻¹ =
      tau (C := C + (A : Matrix (Fin 2) (Fin 2) K) * C * (A : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, hC,
          Matrix.mul_assoc]) := by
  have hinv : (tau hC)⁻¹ = tau hC := by
    rw [inv_eq_iff_mul_eq_one, ← sq, tau_sq]
  have e : tau hC * spLevi 1 A * (tau hC)⁻¹ * (spLevi 1 A)⁻¹ =
      tau hC * (spLevi 1 A * (tau hC)⁻¹ * (spLevi 1 A)⁻¹) := by group
  rw [e, hinv, spLevi_one_mul_tau_mul_inv, tau_mul_tau]

theorem exists_units_sq_ne_one [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4) :
    ∃ α : Kˣ, (α : K) ^ 2 ≠ 1 := by
  classical
  obtain ⟨s, hs⟩ := hK4
  obtain ⟨x, hxs, hx⟩ : ∃ x ∈ s, x ≠ 0 ∧ x ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : s ⊆ {0, 1} := fun x hx => by
      by_cases h0 : x = 0
      · simp [h0]
      · simp [h x hx h0]
    have := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    omega
  refine ⟨Units.mk0 x hx.1, fun h => hx.2 ?_⟩
  have h1 : (x + 1) ^ 2 = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    simp only [Units.val_mk0] at h
    linear_combination h + (x + 1) * h2
  have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  have h4 : x = -1 := eq_neg_of_add_eq_zero_left h3
  rw [h4, CharTwo.neg_eq]

@[expose] noncomputable def dSL (α : Kˣ) : Matrix.SpecialLinearGroup (Fin 2) K :=
  ⟨!![(α : K), 0; 0, ((α⁻¹ : Kˣ) : K)], by simp [Matrix.det_fin_two]⟩

@[expose] def uniSL : Matrix.SpecialLinearGroup (Fin 2) K := ⟨unitri 1, det_unitri 1⟩

theorem dSL_sym2 (α : Kˣ) (a b c : K) :
    ((dSL α : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * sym2 a b c *
        ((dSL α : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)ᵀ =
      sym2 ((α : K) ^ 2 * a) b (((α⁻¹ : Kˣ) : K) ^ 2 * c) := by
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dSL, sym2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;>
    first
      | (rw [mul_comm (α : K) b, mul_assoc, mul_inv_cancel₀ hα0, mul_one])
      | (rw [mul_comm _ b, mul_assoc, inv_mul_cancel₀ hα0, mul_one])
      | ring

theorem tau_mem_of_comm [CharP K 2] (hK4 : ∃ s : Finset K, s.card = 4)
    {H : Subgroup (StatedSp 2 K)}
    (hH : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) K) (C : Matrix (Fin 2) (Fin 2) K)
      (hC : Cᵀ = C), tau (C := C + (A : Matrix (Fin 2) (Fin 2) K) * C *
        (A : Matrix (Fin 2) (Fin 2) K)ᵀ)
        (by rw [transpose_add, transpose_mul, transpose_mul, transpose_transpose, hC,
          Matrix.mul_assoc]) ∈ H)
    {E : Matrix (Fin 2) (Fin 2) K} (hE : Eᵀ = E) : tau hE ∈ H := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨α, hα⟩ := exists_units_sq_ne_one hK4
  have hα1 : (1 : K) + (α : K) ^ 2 ≠ 0 := by
    intro h
    apply hα
    linear_combination h - h2
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hd0 : ∀ a : K, tau (sym2_transpose a 0 0) ∈ H := by
    intro a
    have h := hH (dSL α) (sym2 (a / (1 + (α : K) ^ 2)) 0 0) (sym2_transpose _ _ _)
    convert h using 2
    rw [dSL_sym2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2]
    field_simp
  have hd1 : ∀ c : K, tau (sym2_transpose 0 0 c) ∈ H := by
    intro c
    have h := hH (dSL α⁻¹) (sym2 0 0 (c / (1 + (α : K) ^ 2))) (sym2_transpose _ _ _)
    convert h using 2
    rw [dSL_sym2]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2]
    field_simp
  have hbb : ∀ b : K, tau (sym2_transpose b b 0) ∈ H := by
    intro b
    have h := hH uniSL (sym2 0 0 b) (sym2_transpose _ _ _)
    convert h using 2
    rw [show ((uniSL : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      unitri 1 from rfl, unitri_mul_sym2_mul_transpose]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2]
    linear_combination -b * h2
  have hprod : tau hE = tau (sym2_transpose (E 0 0) 0 0) * tau (sym2_transpose 0 0 (E 1 1)) *
      tau (sym2_transpose (E 0 1) (E 0 1) 0) * tau (sym2_transpose (E 0 1) 0 0) := by
    rw [tau_mul_tau, tau_mul_tau, tau_mul_tau]
    apply tau_congr
    rw [eq_sym2 hE]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2]
    linear_combination (-E 0 1) * h2
  rw [hprod]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hd0 _) (hd1 _)) (hbb _)) (hd0 _)

section Finite

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem tau_mem_N1 (hK4 : ∃ s : Finset K, s.card = 4) {C : Matrix (Fin 2) (Fin 2) K}
    (hC : Cᵀ = C) : tau hC ∈ perfectCore (Q2 K 1) := by
  refine tau_mem_of_comm hK4 (fun A C' hC' => ?_) hC
  rw [← commutator_tau_spLevi A hC']
  have hl := spLevi_mem_perfectCore hK4 1 A
  have hN := Vol2.Ch11.SecS.C11P9A.mem_normalizer_N 1 (tau_mem_Q2 1 hC')
  exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 hN _).1 hl) (Subgroup.inv_mem _ hl)

theorem mem_pCoreOf_N1_iff (hK4 : ∃ s : Finset K, s.card = 4) {x : StatedSp 2 K} :
    x ∈ pCoreOf 2 (perfectCore (Q2 K 1)) ↔
      ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C), x = tau hC := by
  constructor
  · intro hx
    have hxN : x ∈ perfectCore (Q2 K 1) := Subgroup.map_subtype_le _ hx
    have hb := (Vol2.Ch11.SecS.C11P9A.mem_pCoreOf_N_iff hK4 1 hxN).1 hx
    obtain ⟨C, hC, h⟩ := eq_spLevi_mul_tau ⟨x, hxN⟩
    have hA : blkN 1 ⟨x, hxN⟩ = 1 := by
      apply Subtype.ext
      rw [blkN_coe]
      rw [blkQ_apply] at hb
      exact hb
    refine ⟨C, hC, ?_⟩
    have h' : x = spLevi 1 (blkN 1 ⟨x, hxN⟩) * tau hC := h
    rw [h', hA, map_one, one_mul]
  · rintro ⟨C, hC, rfl⟩
    have hN := tau_mem_N1 hK4 hC
    refine (Vol2.Ch11.SecS.C11P9A.mem_pCoreOf_N_iff hK4 1 hN).2 ?_
    rw [blkQ_apply]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blkIdx, sigma2, show spMat (tau hC) = fromBlocks 1 C 0 1 from coe_tau hC]

omit [Finite K] in
theorem sl_mul_sym2_alt (A : Matrix.SpecialLinearGroup (Fin 2) K) (b : K) :
    (A : Matrix (Fin 2) (Fin 2) K) * sym2 0 b 0 * (A : Matrix (Fin 2) (Fin 2) K)ᵀ = sym2 0 b 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := A.2
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sym2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply]
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
      b) * h2
  · linear_combination b * hdet + ((A : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (A : Matrix (Fin 2) (Fin 2) K) 1 0 * b) * h2
  · linear_combination b * hdet + ((A : Matrix (Fin 2) (Fin 2) K) 0 1 *
      (A : Matrix (Fin 2) (Fin 2) K) 1 0 * b) * h2
  · linear_combination ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * (A : Matrix (Fin 2) (Fin 2) K) 1 1 *
      b) * h2

variable (K) in
@[expose] noncomputable def cOne : Subgroup (StatedSp 2 K) :=
  Subgroup.closure {x | ∃ b : K, x = tau (sym2_transpose 0 b 0)}

theorem conj_eq_of_mem_cOne {c : StatedSp 2 K} (hc : c ∈ cOne K) {n : StatedSp 2 K}
    (hn : n ∈ perfectCore (Q2 K 1)) : n * c * n⁻¹ = c := by
  have hle : cOne K ≤ Subgroup.centralizer (perfectCore (Q2 K 1) : Set (StatedSp 2 K)) := by
    rw [cOne, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    have h := mul_tau_mul_inv_of_mem ⟨m, hm⟩ (sym2_transpose 0 b 0)
    rw [tau_congr _ (sym2_transpose 0 b 0) (sl_mul_sym2_alt _ b)] at h
    calc m * tau (sym2_transpose 0 b 0) =
        (m * tau (sym2_transpose 0 b 0) * m⁻¹) * m := by group
      _ = tau (sym2_transpose 0 b 0) * m := by rw [h]
  have h := Subgroup.mem_centralizer_iff.1 (hle hc) n hn
  rw [h, mul_inv_cancel_right]

theorem cOne_le (hK4 : ∃ s : Finset K, s.card = 4) : cOne K ≤ pCoreOf 2 (perfectCore (Q2 K 1)) := by
  rw [cOne, Subgroup.closure_le]
  rintro _ ⟨b, rfl⟩
  exact (mem_pCoreOf_N1_iff hK4).2 ⟨_, _, rfl⟩

omit [Finite K] in
theorem mul_mul_transpose_diag (g D : Matrix (Fin 2) (Fin 2) K) (hD : D 1 0 = D 0 1) (i : Fin 2) :
    (g * D * gᵀ) i i = g i 0 ^ 2 * D 0 0 + g i 1 ^ 2 * D 1 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, hD]
  linear_combination (g i 0 * g i 1 * D 0 1) * h2

omit [CharP K 2] in
theorem exists_sq_eq [CharP K 2] (a : K) : ∃ r : K, r ^ 2 = a := by
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨r, by rw [sq, hr]⟩

theorem le_closure_conj_sup_cOne (hK4 : ∃ s : Finset K, s.card = 4) {v : StatedSp 2 K}
    (hv : v ∈ pCoreOf 2 (perfectCore (Q2 K 1))) (hvC : v ∉ cOne K) :
    pCoreOf 2 (perfectCore (Q2 K 1)) ≤
      Subgroup.closure {x | ∃ n ∈ perfectCore (Q2 K 1), x = n * v * n⁻¹} ⊔ cOne K := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨D, hD, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 hv
  have hD10 : D 1 0 = D 0 1 := by simpa using congrFun (congrFun hD 0) 1
  have hDne : D 0 0 ≠ 0 ∨ D 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hvC
    rw [tau_congr hD (sym2_transpose 0 (D 0 1) 0) (by rw [eq_sym2 hD, h.1, h.2]; rfl)]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  intro x hx
  obtain ⟨E, hE, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 hx
  have hE10 : E 1 0 = E 0 1 := by simpa using congrFun (congrFun hE 0) 1
  by_cases hE0 : E 0 0 = 0 ∧ E 1 1 = 0
  · apply Subgroup.mem_sup_right
    rw [tau_congr hE (sym2_transpose 0 (E 0 1) 0) (by rw [eq_sym2 hE, hE0.1, hE0.2]; rfl)]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  obtain ⟨r0, hr0⟩ := exists_sq_eq (D 0 0)
  obtain ⟨r1, hr1⟩ := exists_sq_eq (D 1 1)
  obtain ⟨s0, hs0⟩ := exists_sq_eq (E 0 0)
  obtain ⟨s1, hs1⟩ := exists_sq_eq (E 1 1)
  have hu : (![r0, r1] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0 : r0 = 0 := by simpa using congrFun h 0
    have h1 : r1 = 0 := by simpa using congrFun h 1
    rcases hDne with h | h
    · exact h (by rw [← hr0, h0]; ring)
    · exact h (by rw [← hr1, h1]; ring)
  have hu' : (![s0, s1] : Fin 2 → K) ≠ 0 := by
    intro h
    have h0 : s0 = 0 := by simpa using congrFun h 0
    have h1 : s1 = 0 := by simpa using congrFun h 1
    exact hE0 ⟨by rw [← hs0, h0]; ring, by rw [← hs1, h1]; ring⟩
  obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hu hu'
  have hgi : ∀ i : Fin 2, (g : Matrix (Fin 2) (Fin 2) K) i 0 * r0 +
      (g : Matrix (Fin 2) (Fin 2) K) i 1 * r1 = ![s0, s1] i := fun i => by
    rw [← hg]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  set F := (g : Matrix (Fin 2) (Fin 2) K) * D * (g : Matrix (Fin 2) (Fin 2) K)ᵀ with hFdef
  have hFsym : Fᵀ = F := by
    rw [hFdef, transpose_mul, transpose_mul, transpose_transpose, hD, Matrix.mul_assoc]
  have hFii : ∀ i : Fin 2, F i i = ![s0, s1] i ^ 2 := fun i => by
    rw [hFdef, mul_mul_transpose_diag _ _ hD10, ← hr0, ← hr1, ← hgi i]
    linear_combination (-((g : Matrix (Fin 2) (Fin 2) K) i 0 * r0 *
      (g : Matrix (Fin 2) (Fin 2) K) i 1 * r1)) * h2
  have hmemF : tau hFsym ∈
      Subgroup.closure {x | ∃ n ∈ perfectCore (Q2 K 1), x = n * tau hD * n⁻¹} :=
    Subgroup.subset_closure ⟨spLevi 1 g, spLevi_mem_perfectCore hK4 1 g,
      (spLevi_one_mul_tau_mul_inv g hD).symm⟩
  have hsplit : tau hE = tau hFsym * tau (sym2_transpose 0 (E 0 1 + F 0 1) 0) := by
    rw [tau_mul_tau]
    apply tau_congr
    have hF10 : F 1 0 = F 0 1 := by simpa using congrFun (congrFun hFsym 0) 1
    have h00 := hFii 0
    have h11 := hFii 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sym2, h00, h11, hs0, hs1, hF10, hE10]
    · linear_combination (-F 0 1) * h2
    · linear_combination (-F 0 1) * h2
  rw [hsplit]
  exact Subgroup.mul_mem_sup hmemF (Subgroup.subset_closure ⟨_, rfl⟩)

theorem le_commutator_N1 (hK4 : ∃ s : Finset K, s.card = 4) :
    pCoreOf 2 (perfectCore (Q2 K 1)) ≤
      ⁅pCoreOf 2 (perfectCore (Q2 K 1)), perfectCore (Q2 K 1)⁆ := by
  intro x hx
  obtain ⟨E, hE, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 hx
  refine tau_mem_of_comm hK4 (fun A C hC => ?_) hE
  rw [← commutator_tau_spLevi A hC]
  have h := Subgroup.commutator_mem_commutator ((mem_pCoreOf_N1_iff hK4).2 ⟨C, hC, rfl⟩)
    (spLevi_mem_perfectCore hK4 1 A)
  rwa [commutatorElement_def] at h

theorem comm_of_mem_pCoreOf_N1 (hK4 : ∃ s : Finset K, s.card = 4) {a b : StatedSp 2 K}
    (ha : a ∈ pCoreOf 2 (perfectCore (Q2 K 1))) (hb : b ∈ pCoreOf 2 (perfectCore (Q2 K 1))) :
    a * b = b * a := by
  obtain ⟨C, hC, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 ha
  obtain ⟨D, hD, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 hb
  exact tau_comm hC hD

omit [Finite K] [CharP K 2] in
theorem torusHom_injective : Function.Injective (torusHom : (Fin 2 → Kˣ) →* StatedSp 2 K) := by
  rw [injective_iff_map_eq_one]
  intro t ht
  funext i
  have h := congrArg (fun x : StatedSp 2 K => spMat x (Sum.inl i) (Sum.inl i)) ht
  simp only [Vol2.Ch11.SecS.C11P9A.spMat_torusHom, spMat_one, diagonal_apply_eq,
    Sum.elim_inl, one_apply_eq] at h
  exact Units.ext h

omit [Finite K] [CharP K 2] in
theorem torusHom_mul_tau_mul_inv (t : Fin 2 → Kˣ) {D : Matrix (Fin 2) (Fin 2) K}
    (hD : Dᵀ = D) :
    torusHom t * tau hD * (torusHom t)⁻¹ =
      tau (C := diagonal (fun i => (t i : K)) * D * diagonal (fun i => (t i : K)))
        (by rw [transpose_mul, transpose_mul, diagonal_transpose, hD, Matrix.mul_assoc]) := by
  apply statedSp_ext
  show spMat (torusHom t * tau hD * (torusHom t)⁻¹) = spMat (tau _)
  rw [← map_inv, spMat_mul, spMat_mul, Vol2.Ch11.SecS.C11P9A.spMat_torusHom,
    Vol2.Ch11.SecS.C11P9A.spMat_torusHom, show spMat (tau hD) = fromBlocks 1 D 0 1 from coe_tau hD,
    show spMat (tau (C := diagonal (fun i => (t i : K)) * D * diagonal (fun i => (t i : K)))
      (by rw [transpose_mul, transpose_mul, diagonal_transpose, hD, Matrix.mul_assoc])) =
      fromBlocks 1 (diagonal (fun i => (t i : K)) * D * diagonal (fun i => (t i : K))) 0 1
      from coe_tau _]
  ext (i | i) (j | j) <;>
    simp [Matrix.mul_apply, diagonal_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, one_apply] <;> fin_cases i <;> fin_cases j <;> simp

omit [Finite K] [CharP K 2] in
theorem tau_zero : tau (transpose_zero (m := Fin 2) (n := Fin 2) (α := K)) = 1 := by
  apply statedSp_ext
  rw [coe_tau, fromBlocks_one]
  rfl

variable (K) in
@[expose] noncomputable def xOne : Subgroup (StatedSp 2 K) :=
  (Vol2.Ch11.SecS.C11P9A.tSd K).map torusHom

theorem radicalData_one (hK4 : ∃ s : Finset K, s.card = 4) :
    RadicalData (perfectCore (Q2 K 1)) (xOne K) (Nat.card K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun a ha b hb => comm_of_mem_pCoreOf_N1 hK4 ha hb,
    ⟨cOne K, cOne_le hK4, fun c hc n hn => conj_eq_of_mem_cOne hc hn,
      fun v hv hvC => le_closure_conj_sup_cOne hK4 hv hvC⟩,
    le_commutator_N1 hK4, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact Vol2.Ch11.SecS.C11P9A.mem_normalizer_N 1 (Vol2.Ch11.SecS.C11P9A.torusHom_mem_Q2 1 t)
  · rw [xOne, Subgroup.card_map_of_injective torusHom_injective,
      Vol2.Ch11.SecS.C11P9A.card_tSd, Nat.card_units]
  · rintro _ ⟨t, ht, rfl⟩ l hl
    have h := (Vol2.Ch11.SecS.C11P9A.torusHom_mem_sc1_iff hK4 t).2
      (Vol2.Ch11.SecS.C11P9A.mem_tSd.1 ht)
    exact h.2.2 l hl
  · rintro _ ⟨t, ht, rfl⟩ hx v hv hfix
    obtain ⟨D, hD, rfl⟩ := (mem_pCoreOf_N1_iff hK4).1 hv
    rw [torusHom_mul_tau_mul_inv] at hfix
    have heq := tau_injective _ _ hfix
    have ht01 : t 0 = t 1 := Vol2.Ch11.SecS.C11P9A.mem_tSd.1 ht
    have ht0 : (t 0 : K) ≠ 1 := by
      intro h1
      apply hx
      have ht1 : t = 1 := by
        funext i
        fin_cases i
        · exact Units.ext h1
        · show t 1 = 1
          rw [← ht01]
          exact Units.ext h1
      rw [ht1, map_one]
    have hsq : (t 0 : K) ^ 2 - 1 ≠ 0 := by
      intro h
      apply ht0
      have h3 : ((t 0 : K) + 1) ^ 2 = 0 := by linear_combination h + (t 0 : K) * h2 + h2
      have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      have h5 : (t 0 : K) = -1 := eq_neg_of_add_eq_zero_left h4
      rw [h5, CharTwo.neg_eq]
    have hD0 : D = 0 := by
      ext i j
      have hij := congrFun (congrFun heq i) j
      simp only [Matrix.mul_apply, diagonal_apply, Fin.sum_univ_two] at hij
      have hti : ∀ k : Fin 2, (t k : K) = t 0 := fun k => by
        fin_cases k
        · rfl
        · exact congrArg Units.val ht01.symm
      fin_cases i <;> fin_cases j <;> simp [hti] at hij ⊢ <;>
        exact (mul_eq_zero.1 (by linear_combination hij)).resolve_left hsq
    rw [tau_congr hD (transpose_zero (m := Fin 2) (n := Fin 2) (α := K)) hD0, tau_zero]

end Finite

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
