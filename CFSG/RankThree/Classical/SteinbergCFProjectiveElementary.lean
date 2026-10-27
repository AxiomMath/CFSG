module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.Classical

open Matrix Matrix.ProjGenLinGroup
open scoped MatrixGroups

variable {k : Type*} [Field k]

theorem traceless_mul_self {M : Matrix (Fin 2) (Fin 2) k} (hM : M.trace = 0) :
    M * M = (-M.det) • (1 : Matrix (Fin 2) (Fin 2) k) := by
  rw [Matrix.trace_fin_two] at hM
  have h11 : M 1 1 = -M 0 0 := by linear_combination hM
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two, h11] <;> ring

theorem traceless_mul_add_mul {M N : Matrix (Fin 2) (Fin 2) k} (hM : M.trace = 0)
    (hN : N.trace = 0) :
    M * N + N * M = (M * N).trace • (1 : Matrix (Fin 2) (Fin 2) k) := by
  rw [Matrix.trace_fin_two] at hM hN
  have h11 : M 1 1 = -M 0 0 := by linear_combination hM
  have h11' : N 1 1 = -N 0 0 := by linear_combination hN
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, h11, h11'] <;> ring

theorem mul_self_eq_trace_smul_sub (M : Matrix (Fin 2) (Fin 2) k) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) k) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem exists_eq_smul_one_add_smul (h2 : (2 : k) ≠ 0) {A G : Matrix (Fin 2) (Fin 2) k}
    (hA : A.trace = 0) (hdet : A.det ≠ 0) (hG : G * A = A * G) :
    ∃ α β : k, G = α • (1 : Matrix (Fin 2) (Fin 2) k) + β • A := by
  set G₀ := G - (G.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) k) with hG₀
  have htr : G₀.trace = 0 := by
    rw [hG₀, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
      smul_eq_mul]
    field_simp
    norm_num
  have hcomm : G₀ * A = A * G₀ := by
    rw [hG₀, sub_mul, mul_sub, hG, smul_mul, one_mul, mul_smul_comm, mul_one]
  set t := (A * G₀).trace
  have h1 : A * G₀ + G₀ * A = t • (1 : Matrix (Fin 2) (Fin 2) k) := traceless_mul_add_mul hA htr
  rw [← hcomm, ← two_smul k (G₀ * A)] at h1
  have h3 : (2 * -A.det) • G₀ = t • A := by
    have := congrArg (· * A) h1
    simp only [smul_mul, one_mul, mul_assoc, traceless_mul_self hA, mul_smul_comm,
      mul_one] at this
    rw [mul_smul]
    exact this
  have hne : (2 * -A.det) ≠ 0 := mul_ne_zero h2 (neg_ne_zero.2 hdet)
  refine ⟨G.trace / 2, t / (2 * -A.det), ?_⟩
  have hG₀' : G₀ = (t / (2 * -A.det)) • A := by
    rw [div_eq_inv_mul, mul_smul, ← h3, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [← hG₀', hG₀]
  abel

theorem eq_zero_of_anticomm (h2 : (2 : k) ≠ 0) {P Y : Matrix (Fin 2) (Fin 2) k} {α β : k}
    (hPY : P * Y = -(Y * P)) (hY : Y ≠ 0)
    (hG : (α • (1 : Matrix (Fin 2) (Fin 2) k) + β • P) * Y =
      -(Y * (α • (1 : Matrix (Fin 2) (Fin 2) k) + β • P))) : α = 0 := by
  rw [add_mul, mul_add, smul_mul, one_mul, smul_mul, mul_smul_comm, mul_smul_comm, mul_one, hPY,
    neg_add, smul_neg] at hG
  have h : (2 * α) • Y = 0 := by
    rw [mul_smul, two_smul]
    linear_combination (norm := module) hG
  rcases smul_eq_zero.1 h with h | h
  · exact (mul_eq_zero.1 h).resolve_left h2
  · exact absurd h hY

theorem eq_zero_of_comm (h2 : (2 : k) ≠ 0) {P Y : Matrix (Fin 2) (Fin 2) k} {α β : k}
    (hPY : P * Y = -(Y * P)) (hY : P * Y ≠ 0)
    (hG : (α • (1 : Matrix (Fin 2) (Fin 2) k) + β • P) * Y =
      Y * (α • (1 : Matrix (Fin 2) (Fin 2) k) + β • P)) : β = 0 := by
  rw [add_mul, mul_add, smul_mul, one_mul, smul_mul, mul_smul_comm, mul_smul_comm, mul_one] at hG
  have hYP : Y * P = -(P * Y) := by rw [hPY, neg_neg]
  rw [hYP] at hG
  have h : (2 * β) • (P * Y) = 0 := by
    rw [mul_smul, two_smul]
    linear_combination (norm := module) hG
  rcases smul_eq_zero.1 h with h | h
  · exact (mul_eq_zero.1 h).resolve_left h2
  · exact absurd h hY

theorem mk_eq_mk_iff_smul {g h : GL (Fin 2) k} :
    mk g = mk h ↔ ∃ c : k, (h : Matrix (Fin 2) (Fin 2) k) = c • (g : Matrix (Fin 2) (Fin 2) k) := by
  rw [mk_eq_mk_iff]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨u, ?_⟩
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
      mul_smul_comm, mul_one]
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      have := h.isUnit.ne_zero
      rw [hc, zero_smul] at this
      exact this rfl
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← smul_one_eq_diagonal,
      Units.val_mk0, mul_smul_comm, mul_one, hc]

theorem mk_eq_one_iff_smul {g : GL (Fin 2) k} :
    mk g = 1 ↔ ∃ c : k, (g : Matrix (Fin 2) (Fin 2) k) = c • (1 : Matrix (Fin 2) (Fin 2) k) := by
  rw [← mk_one, eq_comm, mk_eq_mk_iff_smul, Units.val_one]

theorem mk_eq_of_eq_smul {g h : GL (Fin 2) k} {β : k}
    (hβ : (h : Matrix (Fin 2) (Fin 2) k) = β • (g : Matrix (Fin 2) (Fin 2) k)) : mk h = mk g :=
  (mk_eq_mk_iff_smul.2 ⟨β, hβ⟩).symm

theorem det_ne_zero_of_GL (g : GL (Fin 2) k) : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
  rw [← GeneralLinearGroup.val_det_apply]
  exact Units.ne_zero _

theorem exists_mul_eq_smul_of_commute {g h : GL (Fin 2) k} (hc : mk g * mk h = mk h * mk g) :
    ∃ c : k, c * c = 1 ∧ (g : Matrix (Fin 2) (Fin 2) k) * (h : Matrix (Fin 2) (Fin 2) k) =
      c • ((h : Matrix (Fin 2) (Fin 2) k) * (g : Matrix (Fin 2) (Fin 2) k)) := by
  rw [← map_mul, ← map_mul, eq_comm, mk_eq_mk_iff_smul] at hc
  obtain ⟨c, hc⟩ := hc
  simp only [Units.val_mul] at hc
  refine ⟨c, ?_, hc⟩
  have hdet := congrArg Matrix.det hc
  rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, Matrix.det_mul, mul_comm (det _)] at hdet
  have hne := mul_ne_zero (det_ne_zero_of_GL h) (det_ne_zero_of_GL g)
  have : (c * c - 1) * ((h : Matrix (Fin 2) (Fin 2) k).det *
      (g : Matrix (Fin 2) (Fin 2) k).det) = 0 := by
    linear_combination -hdet
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hne)

theorem trace_eq_zero_of_mk_mul_self {g : GL (Fin 2) k} (hg : mk g * mk g = 1) (hne : mk g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  rw [← map_mul, mk_eq_one_iff_smul] at hg
  obtain ⟨c, hc⟩ := hg
  rw [Units.val_mul, mul_self_eq_trace_smul_sub] at hc
  by_contra htr
  apply hne
  rw [mk_eq_one_iff_smul]
  refine ⟨((g : Matrix (Fin 2) (Fin 2) k).trace)⁻¹ * (c + (g : Matrix (Fin 2) (Fin 2) k).det),
    ?_⟩
  have h1 : (g : Matrix (Fin 2) (Fin 2) k).trace • (g : Matrix (Fin 2) (Fin 2) k) =
      (c + (g : Matrix (Fin 2) (Fin 2) k).det) • (1 : Matrix (Fin 2) (Fin 2) k) := by
    rw [add_smul, ← hc, sub_add_cancel]
  rw [mul_smul, ← h1, smul_smul, inv_mul_cancel₀ htr, one_smul]

theorem exists_traceless_lift {x : PGL(2, k)} (hx : x * x = 1) (hne : x ≠ 1) :
    ∃ A : GL (Fin 2) k, mk A = x ∧ (A : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
  obtain ⟨A, rfl⟩ := mk_surjective x
  exact ⟨A, rfl, trace_eq_zero_of_mk_mul_self hx hne⟩

theorem mk_eq_of_commute_traceless (h2 : (2 : k) ≠ 0) {A B : GL (Fin 2) k}
    (hA : (A : Matrix (Fin 2) (Fin 2) k).trace = 0) (hB : (B : Matrix (Fin 2) (Fin 2) k).trace = 0)
    (hAB : (B : Matrix (Fin 2) (Fin 2) k) * A = A * B) : mk B = mk A := by
  obtain ⟨α, β, h⟩ := exists_eq_smul_one_add_smul h2 hA (det_ne_zero_of_GL A) hAB
  have hα : α = 0 := by
    have := congrArg Matrix.trace h
    rw [hB, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hA, Matrix.trace_one,
      Fintype.card_fin, smul_zero, add_zero, smul_eq_mul] at this
    exact (mul_eq_zero.1 this.symm).resolve_right (by exact_mod_cast h2)
  rw [hα, zero_smul, zero_add] at h
  exact mk_eq_of_eq_smul h

theorem mk_eq_or_anticomm (h2 : (2 : k) ≠ 0) {A B : GL (Fin 2) k}
    (hA : (A : Matrix (Fin 2) (Fin 2) k).trace = 0) (hB : (B : Matrix (Fin 2) (Fin 2) k).trace = 0)
    (hc : mk A * mk B = mk B * mk A) :
    mk B = mk A ∨ (B : Matrix (Fin 2) (Fin 2) k) * A = -((A : Matrix (Fin 2) (Fin 2) k) * B) := by
  obtain ⟨c, hc1, h⟩ := exists_mul_eq_smul_of_commute hc.symm
  rcases mul_self_eq_one_iff.1 hc1 with rfl | rfl
  · rw [one_smul] at h
    exact Or.inl (mk_eq_of_commute_traceless h2 hA hB h)
  · rw [neg_one_smul] at h
    exact Or.inr h

theorem trace_mul_eq_zero_of_anticomm (h2 : (2 : k) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) k}
    (hAB : B * A = -(A * B)) : (A * B).trace = 0 := by
  have h := Matrix.trace_mul_comm A B
  rw [hAB, Matrix.trace_neg] at h
  have : (2 : k) * (A * B).trace = 0 := by linear_combination h
  exact (mul_eq_zero.1 this).resolve_left h2

theorem mem_four_of_commute (h2 : (2 : k) ≠ 0) {A B : GL (Fin 2) k}
    (hA : (A : Matrix (Fin 2) (Fin 2) k).trace = 0) (hB : (B : Matrix (Fin 2) (Fin 2) k).trace = 0)
    (hAB : (B : Matrix (Fin 2) (Fin 2) k) * A = -((A : Matrix (Fin 2) (Fin 2) k) * B))
    {y : PGL(2, k)} (hyA : y * mk A = mk A * y) (hyB : y * mk B = mk B * y) :
    y = 1 ∨ y = mk A ∨ y = mk B ∨ y = mk A * mk B := by
  obtain ⟨G, rfl⟩ := mk_surjective y
  obtain ⟨c, hc, hGA⟩ := exists_mul_eq_smul_of_commute hyA
  obtain ⟨d, hd, hGB⟩ := exists_mul_eq_smul_of_commute hyB
  have hA0 : (A : Matrix (Fin 2) (Fin 2) k) ≠ 0 := Units.ne_zero A
  have hB0 : (B : Matrix (Fin 2) (Fin 2) k) ≠ 0 := Units.ne_zero B
  have hAB0 : (A : Matrix (Fin 2) (Fin 2) k) * B ≠ 0 := by
    rw [← Units.val_mul]
    exact Units.ne_zero _
  have hAB' : (A : Matrix (Fin 2) (Fin 2) k) * B = -((B : Matrix (Fin 2) (Fin 2) k) * A) := by
    rw [hAB, neg_neg]
  rcases mul_self_eq_one_iff.1 hc with rfl | rfl <;>
    rcases mul_self_eq_one_iff.1 hd with rfl | rfl
  ·
    rw [one_smul] at hGA hGB
    obtain ⟨α, β, hG⟩ := exists_eq_smul_one_add_smul h2 hA (det_ne_zero_of_GL A) hGA
    rw [hG] at hGB
    have hβ := eq_zero_of_comm h2 hAB' hAB0 hGB
    rw [hβ, zero_smul, add_zero] at hG
    exact Or.inl (mk_eq_one_iff_smul.2 ⟨α, hG⟩)
  ·
    rw [one_smul] at hGA
    rw [neg_one_smul] at hGB
    obtain ⟨α, β, hG⟩ := exists_eq_smul_one_add_smul h2 hA (det_ne_zero_of_GL A) hGA
    rw [hG] at hGB
    have hα := eq_zero_of_anticomm h2 hAB' hB0 hGB
    rw [hα, zero_smul, zero_add] at hG
    exact Or.inr (Or.inl (mk_eq_of_eq_smul hG))
  ·
    rw [neg_one_smul] at hGA
    rw [one_smul] at hGB
    obtain ⟨α, β, hG⟩ := exists_eq_smul_one_add_smul h2 hB (det_ne_zero_of_GL B) hGB
    rw [hG] at hGA
    have hα := eq_zero_of_anticomm h2 hAB hA0 hGA
    rw [hα, zero_smul, zero_add] at hG
    exact Or.inr (Or.inr (Or.inl (mk_eq_of_eq_smul hG)))
  ·
    rw [neg_one_smul] at hGA hGB
    set C : GL (Fin 2) k := A * B with hC
    have hCm : (C : Matrix (Fin 2) (Fin 2) k) = A * B := Units.val_mul A B
    have hCtr : (C : Matrix (Fin 2) (Fin 2) k).trace = 0 := by
      rw [hCm]
      exact trace_mul_eq_zero_of_anticomm h2 hAB
    have hGC : (G : Matrix (Fin 2) (Fin 2) k) * C = C * G := by
      rw [hCm, ← mul_assoc, hGA, neg_mul, mul_assoc, hGB, mul_neg, neg_neg, mul_assoc]
    have hCA : (C : Matrix (Fin 2) (Fin 2) k) * A = -((A : Matrix (Fin 2) (Fin 2) k) * C) := by
      rw [hCm, mul_assoc, hAB, mul_neg]
    obtain ⟨α, β, hG⟩ := exists_eq_smul_one_add_smul h2 hCtr (det_ne_zero_of_GL C) hGC
    rw [hG] at hGA
    have hα := eq_zero_of_anticomm h2 hCA hA0 hGA
    rw [hα, zero_smul, zero_add] at hG
    refine Or.inr (Or.inr (Or.inr ?_))
    rw [mk_eq_of_eq_smul hG, hC, map_mul]

theorem finite_and_card_le_of_forall_mem {G : Type*} [Group G] (R : Subgroup G) (s : Finset G)
    (h : ∀ x ∈ R, x ∈ s) : Finite R ∧ Nat.card R ≤ s.card := by
  have hsub : (R : Set G) ⊆ ↑s := fun x hx => h x hx
  refine ⟨(s.finite_toSet.subset hsub).to_subtype, ?_⟩
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard hsub s.finite_toSet

theorem card_four_le {G : Type*} [DecidableEq G] (a b c d : G) :
    ({a, b, c, d} : Finset G).card ≤ 4 :=
  (Finset.card_insert_le _ _).trans (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans
    (Nat.succ_le_succ ((Finset.card_insert_le _ _).trans (by simp)))))


theorem odd_projective_linear_elementary_two_subgroups_and_centralizers (k : Type*) [Field k]
    (hk : ringChar k ≠ 2) (R : Subgroup PGL(2, k)) [hR : CFSG.IsElementaryAbelian 2 R] :
    Finite R ∧ Nat.card R ≤ 4 ∧
      (Nat.card R = 4 → Subgroup.centralizer (R : Set PGL(2, k)) = R) := by
  classical
  have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hk
  have hsq : ∀ x ∈ R, x * x = 1 := fun x hx => by
    rw [← sq]
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : R) ⟨y, hy⟩)
  by_cases hR1 : ∀ x ∈ R, x = 1
  · obtain ⟨hfin, hcard⟩ := finite_and_card_le_of_forall_mem R {1} fun x hx => by
      simp [hR1 x hx]
    rw [Finset.card_singleton] at hcard
    exact ⟨hfin, hcard.trans (by norm_num), fun h => by omega⟩
  push Not at hR1
  obtain ⟨z, hzR, hz1⟩ := hR1
  obtain ⟨A, rfl, hA⟩ := exists_traceless_lift (hsq _ hzR) hz1
  by_cases hR2 : ∀ x ∈ R, x = 1 ∨ x = mk A
  · obtain ⟨hfin, hcard⟩ := finite_and_card_le_of_forall_mem R {1, mk A} fun x hx => by
      rcases hR2 x hx with rfl | rfl <;> simp
    have h2' : ({1, mk A} : Finset PGL(2, k)).card ≤ 2 := Finset.card_le_two
    exact ⟨hfin, by omega, fun h => by omega⟩
  push Not at hR2
  obtain ⟨r, hrR, hr1, hrz⟩ := hR2
  obtain ⟨B, rfl, hB⟩ := exists_traceless_lift (hsq _ hrR) hr1
  have hAB : (B : Matrix (Fin 2) (Fin 2) k) * A = -((A : Matrix (Fin 2) (Fin 2) k) * B) :=
    (mk_eq_or_anticomm h2 hA hB (hcomm _ hzR _ hrR)).resolve_left hrz
  have hfour : ∀ y : PGL(2, k), y * mk A = mk A * y → y * mk B = mk B * y →
      y ∈ ({1, mk A, mk B, mk A * mk B} : Finset PGL(2, k)) := fun y hyA hyB => by
    rcases mem_four_of_commute h2 hA hB hAB hyA hyB with rfl | rfl | rfl | rfl <;> simp
  obtain ⟨hfin, hcard⟩ := finite_and_card_le_of_forall_mem R {1, mk A, mk B, mk A * mk B}
    fun x hx => hfour x (hcomm x hx _ hzR) (hcomm x hx _ hrR)
  refine ⟨hfin, hcard.trans (card_four_le _ _ _ _), fun _ => le_antisymm ?_ ?_⟩
  · intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy
    have hy' := hfour y (hy _ hzR).symm (hy _ hrR).symm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
    rcases hy' with rfl | rfl | rfl | rfl
    exacts [R.one_mem, hzR, hrR, R.mul_mem hzR hrR]
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hcomm y hy x hx

end CFSG.RankThree.Classical
