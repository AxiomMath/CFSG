module

public import CFSG.Quasithin.Vol2.Ch10SecKHK3B
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4I

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K]

@[expose] noncomputable def wZ (x y r : K) : StatedSp 2 K := tau (sym2_transpose x y 0) * lam r

theorem wZ_mul [CharP K 2] (x y r x' y' r' : K) :
    wZ x y r * wZ x' y' r' = wZ (x + x') (y + y') (r + r') := by
  have hcomm : lam r * tau (sym2_transpose x' y' 0) * (lam r)⁻¹ = tau (sym2_transpose x' y' 0) := by
    rw [lam_mul_tau_mul_inv]
    apply tau_congr
    rw [unitri_mul_sym2_mul_transpose]
    simp
  have e : wZ x y r * wZ x' y' r' =
      tau (sym2_transpose x y 0) * (lam r * tau (sym2_transpose x' y' 0) * (lam r)⁻¹) *
        (lam r * lam r') := by
    simp only [wZ]
    group
  rw [e, hcomm, tau_mul_tau, lam_mul, wZ]
  congr 1
  apply tau_congr
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2]

theorem wZ_congr {x y r x' y' r' : K} (hx : x = x') (hy : y = y') (hr : r = r') :
    wZ x y r = wZ x' y' r' := by
  subst hx hy hr
  rfl

theorem wZ_zero : wZ (0 : K) 0 0 = 1 := by
  rw [wZ, tau_congr _ (transpose_zero (m := Fin 2) (n := Fin 2) (α := K))
    (by ext i j; fin_cases i <;> fin_cases j <;> rfl), tau_zero, lam_zero, mul_one]

theorem wZ_mul_self [CharP K 2] (x y r : K) : wZ x y r * wZ x y r = 1 := by
  rw [wZ_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
    wZ_zero]

theorem wZ_comm [CharP K 2] (x y r x' y' r' : K) :
    wZ x y r * wZ x' y' r' = wZ x' y' r' * wZ x y r := by
  rw [wZ_mul, wZ_mul, add_comm x, add_comm y, add_comm r]

theorem wZ_mem_unipotent (x y r : K) : wZ x y r ∈ unipotent 2 K :=
  Subgroup.mul_mem _ (tau_mem_unipotent _) (lam_mem_unipotent r)

theorem wZ_mem_Q2 (j : Fin 2) (x y r : K) : wZ x y r ∈ Q2 K j :=
  borelSubgroup_le_Q2 j (unipotent_le_borelSubgroup (wZ_mem_unipotent x y r))

theorem spMat_wZ (x y r : K) :
    spMat (wZ x y r) = fromBlocks (unitri r) (sym2 x y 0 * (unitri (-r))ᵀ) 0 (unitri (-r))ᵀ := by
  show spMat (tau (sym2_transpose x y 0) * lam r) = _
  rw [spMat_mul, show spMat (tau (sym2_transpose x y 0)) = fromBlocks 1 (sym2 x y 0) 0 1 from
    coe_tau _, show spMat (lam r) = fromBlocks (unitri r) 0 0 (unitri (-r))ᵀ from coe_lam r,
    fromBlocks_multiply]
  simp

theorem spLevi_zero_mul_wZ_mul_inv [CharP K 2] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (x y r : K) :
    spLevi 0 g * wZ x y r * (spLevi 0 g)⁻¹ =
      wZ (x + r * y + ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * y +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r) * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 * y +
          (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r))
        ((g : Matrix (Fin 2) (Fin 2) K) 0 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r)
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hdet := g.2
  rw [Matrix.det_fin_two] at hdet
  apply statedSp_ext
  show spMat (spLevi 0 g * wZ x y r * (spLevi 0 g)⁻¹) = spMat (wZ _ _ _)
  rw [← map_inv, spMat_mul, spMat_mul, spMat_lam, spMat_lam, spMat_wZ, spMat_wZ,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairMat, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, unitri, sym2,
      Matrix.vecMul, dotProduct, CharTwo.neg_eq] <;>
    first
      | ring1
      | linear_combination hdet + ((g : Matrix (Fin 2) (Fin 2) K) 0 1 *
          (g : Matrix (Fin 2) (Fin 2) K) 1 0) * h2
      | linear_combination ((g : Matrix (Fin 2) (Fin 2) K) 0 0 *
          (g : Matrix (Fin 2) (Fin 2) K) 0 1) * h2
      | linear_combination ((g : Matrix (Fin 2) (Fin 2) K) 1 0 *
          (g : Matrix (Fin 2) (Fin 2) K) 1 1) * h2
      | linear_combination (-(((g : Matrix (Fin 2) (Fin 2) K) 1 0 * y +
          (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r) * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 * y +
            (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r))) * h2

section Finite

variable [Finite K] [CharP K 2]

theorem mem_pCoreOf_N0_iff (hK4 : ∃ s : Finset K, s.card = 4) {M : StatedSp 2 K} :
    M ∈ pCoreOf 2 (perfectCore (Q2 K 0)) ↔ ∃ x y r : K, M = wZ x y r := by
  rw [← Vol2.Ch11.SecS.C11P9A.pCoreOf_Q0_eq hK4, Vol2.Ch11.SecS.C11P9A.mem_pCoreOf_Q0_iff hK4]
  constructor
  · rintro ⟨hM, hχ, hB⟩
    obtain ⟨C, hC, a, rfl⟩ :=
      mem_unipotent_iff.1 (Vol2.Ch11.SecS.C11P9A.mem_unipotent_of_mem_Q0 hM hχ hB)
    have h11 : C 1 1 = 0 := by
      have h := congrFun (congrFun hB 0) 1
      rw [blkQ_apply] at h
      simp only [blkIdx, sigma2, Matrix.submatrix_apply] at h
      rw [show spMat (tau hC * lam a) = fromBlocks (unitri a) (C * (unitri (-a))ᵀ) 0
          (unitri (-a))ᵀ by
        rw [spMat_mul, show spMat (tau hC) = fromBlocks 1 C 0 1 from coe_tau hC,
          show spMat (lam a) = fromBlocks (unitri a) 0 0 (unitri (-a))ᵀ from coe_lam a,
          fromBlocks_multiply]
        simp] at h
      simpa [unitri, Matrix.mul_apply, Fin.sum_univ_two] using h
    refine ⟨C 0 0, C 0 1, a, ?_⟩
    rw [wZ]
    congr 1
    apply tau_congr
    rw [eq_sym2 hC, h11]
    rfl
  · rintro ⟨x, y, r, rfl⟩
    refine ⟨wZ_mem_Q2 0 x y r, ?_, ?_⟩
    · rw [spMat_wZ]
      simp [unitri]
    · rw [blkQ_apply, spMat_wZ]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [blkIdx, sigma2, unitri, sym2, Matrix.vecMul, dotProduct, Fin.sum_univ_two]

theorem exists_mul_spLevi_zero (hK4 : ∃ s : Finset K, s.card = 4)
    (n : ↥(perfectCore (Q2 K 0))) :
    ∃ v ∈ pCoreOf 2 (perfectCore (Q2 K 0)), (n : StatedSp 2 K) = v * spLevi 0 (blkN 0 n) := by
  set l := spLevi 0 (blkN 0 n) with hl
  have hlN : l ∈ perfectCore (Q2 K 0) := spLevi_mem_perfectCore hK4 0 _
  have hvN : (n : StatedSp 2 K) * l⁻¹ ∈ perfectCore (Q2 K 0) :=
    Subgroup.mul_mem _ n.2 (Subgroup.inv_mem _ hlN)
  refine ⟨(n : StatedSp 2 K) * l⁻¹, ?_, by rw [inv_mul_cancel_right]⟩
  refine (Vol2.Ch11.SecS.C11P9A.mem_pCoreOf_N_iff hK4 0 hvN).2 ?_
  have hnQ : (n : StatedSp 2 K) ∈ Q2 K 0 := perfectCore_le _ n.2
  have hlQ : l⁻¹ ∈ Q2 K 0 := perfectCore_le _ (Subgroup.inv_mem _ hlN)
  have e : (⟨(n : StatedSp 2 K) * l⁻¹, perfectCore_le _ hvN⟩ : ↥(Q2 K 0)) =
      ⟨(n : StatedSp 2 K), hnQ⟩ * ⟨l⁻¹, hlQ⟩ := rfl
  rw [e, map_mul, Vol2.Ch11.SecS.C11P9A.blkQ_spLevi_inv 0 _ hlQ, blkQ_apply,
    ← blkN_coe 0 n, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one]

variable (K) in
@[expose] noncomputable def cZero : Subgroup (StatedSp 2 K) :=
  Subgroup.closure {v | ∃ x : K, v = wZ x 0 0}

theorem conj_eq_of_mem_cZero (hK4 : ∃ s : Finset K, s.card = 4) {c : StatedSp 2 K}
    (hc : c ∈ cZero K) {n : StatedSp 2 K} (hn : n ∈ perfectCore (Q2 K 0)) : n * c * n⁻¹ = c := by
  have hle : cZero K ≤ Subgroup.centralizer (perfectCore (Q2 K 0) : Set (StatedSp 2 K)) := by
    rw [cZero, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro m hm
    obtain ⟨v, hv, hmv⟩ := exists_mul_spLevi_zero hK4 ⟨m, hm⟩
    obtain ⟨a, b, d, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hv
    have hmv' : m = wZ a b d * spLevi 0 (blkN 0 ⟨m, hm⟩) := hmv
    have h1 : m * wZ x 0 0 * m⁻¹ = wZ x 0 0 := by
      rw [hmv']
      have e : wZ a b d * spLevi 0 (blkN 0 ⟨m, hm⟩) * wZ x 0 0 *
          (wZ a b d * spLevi 0 (blkN 0 ⟨m, hm⟩))⁻¹ = wZ a b d *
            (spLevi 0 (blkN 0 ⟨m, hm⟩) * wZ x 0 0 * (spLevi 0 (blkN 0 ⟨m, hm⟩))⁻¹) *
              (wZ a b d)⁻¹ := by group
      rw [e, spLevi_zero_mul_wZ_mul_inv]
      simp only [mul_zero, add_zero]
      rw [wZ_comm, mul_inv_cancel_right]
    calc m * wZ x 0 0 = (m * wZ x 0 0 * m⁻¹) * m := by group
      _ = wZ x 0 0 * m := by rw [h1]
  have h := Subgroup.mem_centralizer_iff.1 (hle hc) n hn
  rw [h, mul_inv_cancel_right]

theorem cZero_le (hK4 : ∃ s : Finset K, s.card = 4) :
    cZero K ≤ pCoreOf 2 (perfectCore (Q2 K 0)) := by
  rw [cZero, Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  exact (mem_pCoreOf_N0_iff hK4).2 ⟨x, 0, 0, rfl⟩

theorem le_closure_conj_sup_cZero (hK4 : ∃ s : Finset K, s.card = 4) {v : StatedSp 2 K}
    (hv : v ∈ pCoreOf 2 (perfectCore (Q2 K 0))) (hvC : v ∉ cZero K) :
    pCoreOf 2 (perfectCore (Q2 K 0)) ≤
      Subgroup.closure {x | ∃ n ∈ perfectCore (Q2 K 0), x = n * v * n⁻¹} ⊔ cZero K := by
  obtain ⟨x, y, r, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hv
  have hu : (![y, r] : Fin 2 → K) ≠ 0 := by
    intro h
    have hy : y = 0 := by simpa using congrFun h 0
    have hr : r = 0 := by simpa using congrFun h 1
    subst hy hr
    exact hvC (Subgroup.subset_closure ⟨x, rfl⟩)
  intro w hw
  obtain ⟨X, Y, R, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hw
  by_cases hYR : Y = 0 ∧ R = 0
  · rw [hYR.1, hYR.2]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨X, rfl⟩)
  have hu' : (![Y, R] : Fin 2 → K) ≠ 0 := by
    intro h
    exact hYR ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩
  obtain ⟨g, hg⟩ := exists_sl2_mulVec_eq hu hu'
  have hg0 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 * y +
      (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r = Y := by
    have := congrFun hg 0
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hg1 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 * y +
      (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r = R := by
    have := congrFun hg 1
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hconj := spLevi_zero_mul_wZ_mul_inv g x y r
  rw [hg0, hg1] at hconj
  set x'' := x + r * y + R * Y
  have hmem : wZ x'' Y R ∈ Subgroup.closure
      {z | ∃ n ∈ perfectCore (Q2 K 0), z = n * wZ x y r * n⁻¹} :=
    Subgroup.subset_closure ⟨spLevi 0 g, spLevi_mem_perfectCore hK4 0 g, hconj.symm⟩
  have hsplit : wZ X Y R = wZ x'' Y R * wZ (X + x'') 0 0 := by
    rw [wZ_mul, add_zero, add_zero]
    congr 1
    rw [add_comm X, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
  rw [hsplit]
  exact Subgroup.mul_mem_sup hmem (Subgroup.subset_closure ⟨_, rfl⟩)

theorem comm_of_mem_pCoreOf_N0 (hK4 : ∃ s : Finset K, s.card = 4) {a b : StatedSp 2 K}
    (ha : a ∈ pCoreOf 2 (perfectCore (Q2 K 0))) (hb : b ∈ pCoreOf 2 (perfectCore (Q2 K 0))) :
    a * b = b * a := by
  obtain ⟨x, y, r, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 ha
  obtain ⟨x', y', r', rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hb
  exact wZ_comm x y r x' y' r'

omit [Finite K] in
theorem wZ_inv (x y r : K) : (wZ x y r)⁻¹ = wZ x y r :=
  inv_eq_of_mul_eq_one_right (wZ_mul_self x y r)

omit [Finite K] in
theorem commutator_wZ_spLevi (g : Matrix.SpecialLinearGroup (Fin 2) K) (x y r : K) :
    wZ x y r * spLevi 0 g * (wZ x y r)⁻¹ * (spLevi 0 g)⁻¹ =
      wZ (x + (x + r * y + ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * y +
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r) * ((g : Matrix (Fin 2) (Fin 2) K) 0 0 * y +
          (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r)))
        (y + ((g : Matrix (Fin 2) (Fin 2) K) 0 0 * y + (g : Matrix (Fin 2) (Fin 2) K) 0 1 * r))
        (r + ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * y +
          (g : Matrix (Fin 2) (Fin 2) K) 1 1 * r)) := by
  have e : wZ x y r * spLevi 0 g * (wZ x y r)⁻¹ * (spLevi 0 g)⁻¹ =
      wZ x y r * (spLevi 0 g * (wZ x y r)⁻¹ * (spLevi 0 g)⁻¹) := by group
  rw [e, wZ_inv, spLevi_zero_mul_wZ_mul_inv, wZ_mul]

theorem le_commutator_N0 (hK4 : ∃ s : Finset K, s.card = 4) :
    pCoreOf 2 (perfectCore (Q2 K 0)) ≤
      ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set H := ⁅pCoreOf 2 (perfectCore (Q2 K 0)), perfectCore (Q2 K 0)⁆ with hH
  have hcm : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (x y r : K),
      wZ x y r * spLevi 0 g * (wZ x y r)⁻¹ * (spLevi 0 g)⁻¹ ∈ H := fun g x y r => by
    have h := Subgroup.commutator_mem_commutator ((mem_pCoreOf_N0_iff hK4).2 ⟨x, y, r, rfl⟩)
      (spLevi_mem_perfectCore hK4 0 g)
    rwa [commutatorElement_def] at h
  obtain ⟨α, hα⟩ := exists_units_sq_ne_one hK4
  have hα1 : (1 : K) + α ≠ 0 := by
    intro h
    apply hα
    have h' : (α : K) = 1 := by linear_combination h - h2
    rw [h', one_pow]
  have hα0 : (α : K) ≠ 0 := α.ne_zero
  have hy : ∀ Y : K, wZ 0 Y 0 ∈ H := fun Y => by
    have h := hcm (dSL α) 0 (Y / (1 + α)) 0
    rw [commutator_wZ_spLevi] at h
    convert h using 2
    · simp [dSL]
    · simp [dSL]
      field_simp
    · simp [dSL]
  have hr : ∀ R : K, wZ 0 0 R ∈ H := fun R => by
    have h := hcm (dSL α⁻¹) 0 0 (R / (1 + α))
    rw [commutator_wZ_spLevi] at h
    convert h using 2
    · simp [dSL]
    · simp [dSL]
    · simp [dSL]
      field_simp
  have hx : ∀ X : K, wZ X 0 0 ∈ H := fun X => by
    obtain ⟨s, hs⟩ := exists_sq_eq X
    have h := hcm uniSL 0 0 s
    rw [commutator_wZ_spLevi] at h
    have e : wZ X 0 0 = wZ (0 + (0 + s * 0 + (0 * 0 + 1 * s) * (1 * 0 + 1 * s)))
        (0 + (1 * 0 + 1 * s)) (s + (0 * 0 + 1 * s)) * wZ 0 s 0 := by
      rw [wZ_mul]
      refine wZ_congr ?_ ?_ ?_
      · rw [← hs]; ring
      · linear_combination (-s) * h2
      · linear_combination (-s) * h2
    rw [e]
    refine H.mul_mem ?_ (hy s)
    convert h using 3 <;> simp [uniSL, unitri]
  intro w hw
  obtain ⟨X, Y, R, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hw
  have e : wZ X Y R = wZ X 0 0 * wZ 0 Y 0 * wZ 0 0 R := by
    rw [wZ_mul, wZ_mul]
    exact wZ_congr (by ring) (by ring) (by ring)
  rw [e]
  exact H.mul_mem (H.mul_mem (hx X) (hy Y)) (hr R)

omit [Finite K] [CharP K 2] in
theorem wZ_injective {x y r x' y' r' : K} (h : wZ x y r = wZ x' y' r') :
    x = x' ∧ y = y' ∧ r = r' := by
  have hm := congrArg spMat h
  rw [spMat_wZ, spMat_wZ] at hm
  have h1 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inl 1)
  have h2 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inr 1)
  have h3 := congrFun (congrFun hm (Sum.inl 0)) (Sum.inr 0)
  simp [unitri, sym2, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h1 h2 h3
  subst h1 h2
  exact ⟨by linear_combination h3, rfl, rfl⟩

omit [Finite K] [CharP K 2] in
theorem torusHom_mul_wZ_mul_inv (t : Fin 2 → Kˣ) (ht : t 1 = 1) (x y r : K) :
    torusHom t * wZ x y r * (torusHom t)⁻¹ =
      wZ ((t 0 : K) ^ 2 * x) ((t 0 : K) * y) ((t 0 : K) * r) := by
  have ht' : (t 1 : K) = 1 := by rw [ht, Units.val_one]
  have ht0 : (t 0 : K) ≠ 0 := (t 0).ne_zero
  apply statedSp_ext
  show spMat (torusHom t * wZ x y r * (torusHom t)⁻¹) = spMat (wZ _ _ _)
  rw [← map_inv, spMat_mul, spMat_mul, Vol2.Ch11.SecS.C11P9A.spMat_torusHom,
    Vol2.Ch11.SecS.C11P9A.spMat_torusHom, spMat_wZ, spMat_wZ]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, unitri, sym2, ht', diagonal_apply, Matrix.vecMul,
      dotProduct] <;> field_simp

variable (K) in
@[expose] noncomputable def xZero : Subgroup (StatedSp 2 K) :=
  (Vol2.Ch11.SecS.C11P9A.tSb K).map torusHom

theorem radicalData_zero (hK4 : ∃ s : Finset K, s.card = 4) :
    RadicalData (perfectCore (Q2 K 0)) (xZero K) (Nat.card K) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨fun a ha b hb => comm_of_mem_pCoreOf_N0 hK4 ha hb,
    ⟨cZero K, cZero_le hK4, fun c hc n hn => conj_eq_of_mem_cZero hK4 hc hn,
      fun v hv hvC => le_closure_conj_sup_cZero hK4 hv hvC⟩,
    le_commutator_N0 hK4, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨t, -, rfl⟩
    exact Vol2.Ch11.SecS.C11P9A.mem_normalizer_N 0 (Vol2.Ch11.SecS.C11P9A.torusHom_mem_Q2 0 t)
  · rw [xZero, Subgroup.card_map_of_injective torusHom_injective,
      Vol2.Ch11.SecS.C11P9A.card_tSb, Nat.card_units]
  · rintro _ ⟨t, ht, rfl⟩ l hl
    have h := (Vol2.Ch11.SecS.C11P9A.torusHom_mem_sc0_iff hK4 t).2
      (Vol2.Ch11.SecS.C11P9A.mem_tSb.1 ht)
    exact h.2.2 l hl
  · rintro _ ⟨t, ht, rfl⟩ hx v hv hfix
    obtain ⟨x, y, r, rfl⟩ := (mem_pCoreOf_N0_iff hK4).1 hv
    have ht1 : t 1 = 1 := Vol2.Ch11.SecS.C11P9A.mem_tSb.1 ht
    rw [torusHom_mul_wZ_mul_inv t ht1] at hfix
    obtain ⟨hxx, hyy, hrr⟩ := wZ_injective hfix
    have ht0 : (t 0 : K) ≠ 1 := by
      intro h1
      apply hx
      have htt : t = 1 := by
        funext i
        fin_cases i
        · exact Units.ext h1
        · exact ht1
      rw [htt, map_one]
    have hsq : (t 0 : K) ^ 2 - 1 ≠ 0 := by
      intro h
      apply ht0
      have h3 : ((t 0 : K) + 1) ^ 2 = 0 := by linear_combination h + (t 0 : K) * h2 + h2
      have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
      have h5 : (t 0 : K) = -1 := eq_neg_of_add_eq_zero_left h4
      rw [h5, CharTwo.neg_eq]
    have hs1 : (t 0 : K) - 1 ≠ 0 := sub_ne_zero.2 ht0
    have hx0 : x = 0 := (mul_eq_zero.1
      (by linear_combination hxx : ((t 0 : K) ^ 2 - 1) * x = 0)).resolve_left hsq
    have hy0 : y = 0 := (mul_eq_zero.1
      (by linear_combination hyy : ((t 0 : K) - 1) * y = 0)).resolve_left hs1
    have hr0 : r = 0 := (mul_eq_zero.1
      (by linear_combination hrr : ((t 0 : K) - 1) * r = 0)).resolve_left hs1
    rw [hx0, hy0, hr0, wZ_zero]

end Finite

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
