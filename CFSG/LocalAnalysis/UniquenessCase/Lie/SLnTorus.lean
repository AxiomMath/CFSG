module

public import CFSG.LieType.SpecialLinear.BorelTwist.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {m : ℕ} {K : Type} [Field K]

@[expose] def uc22pwSLnDv (a : Kˣ) (i : Fin (m + 2)) : K :=
  if i = 0 then (a : K) else if i = Fin.last (m + 1) then ((a⁻¹ : Kˣ) : K) else 1

theorem uc22pwSLnDv_mul (a b : Kˣ) (i : Fin (m + 2)) :
    uc22pwSLnDv (a * b) i = uc22pwSLnDv a i * uc22pwSLnDv b i := by
  by_cases h0 : i = 0
  · subst h0
    simp [uc22pwSLnDv, Units.val_mul]
  by_cases hl : i = Fin.last (m + 1)
  · subst hl
    simp only [uc22pwSLnDv, h0, if_false, if_true, Units.val_mul, _root_.mul_inv_rev]
    rw [mul_comm]
  · simp [uc22pwSLnDv, h0, hl]

theorem prod_uc22pwSLnDv (a : Kˣ) : ∏ i, uc22pwSLnDv (m := m) a i = 1 := by
  rw [Fin.prod_univ_succ]
  have htail : (∏ j : Fin (m + 1), uc22pwSLnDv (m := m) a (Fin.succ j)) =
      ((a⁻¹ : Kˣ) : K) := by
    rw [Fin.prod_univ_castSucc]
    have h1 : (∏ j : Fin m,
        uc22pwSLnDv (m := m) a (Fin.succ (Fin.castSucc j))) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      have h0 : Fin.succ (Fin.castSucc j) ≠ (0 : Fin (m + 2)) := Fin.succ_ne_zero _
      have hl : Fin.succ (Fin.castSucc j) ≠ Fin.last (m + 1) := by
        rw [← Fin.succ_last m]
        exact (Fin.succ_lt_succ_iff.mpr (Fin.castSucc_lt_last j)).ne
      simp [uc22pwSLnDv, h0, hl]
    have hlast : Fin.succ (Fin.last m) = Fin.last (m + 1) := Fin.succ_last m
    rw [h1, one_mul, hlast, uc22pwSLnDv]
    have h0 : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := Fin.last_pos.ne'
    simp [h0]
  rw [htail, uc22pwSLnDv]
  simp

theorem uc22pwSLnDv_rev (a : Kˣ) (i : Fin (m + 2)) :
    uc22pwSLnDv a (Fin.rev i) = uc22pwSLnDv a⁻¹ i := by
  by_cases h0 : i = 0
  · subst h0
    rw [Fin.rev_zero]
    simp [uc22pwSLnDv, Fin.last_pos.ne']
  by_cases hl : i = Fin.last (m + 1)
  · subst hl
    rw [Fin.rev_last]
    simp [uc22pwSLnDv, h0, inv_inv]
  · have hr0 : Fin.rev i ≠ 0 := by
      intro h
      have := congrArg Fin.rev h
      rw [Fin.rev_rev, Fin.rev_zero] at this
      exact hl this
    have hrl : Fin.rev i ≠ Fin.last (m + 1) := by
      intro h
      have := congrArg Fin.rev h
      rw [Fin.rev_rev, Fin.rev_last] at this
      exact h0 this
    simp [uc22pwSLnDv, hr0, hrl, h0, hl]

theorem uc22pwSLnDv_map {φ : K ≃+* K} {i : ℕ} (hi : ∀ x : K, φ x = x ^ 2 ^ i) (a : Kˣ)
    (j : Fin (m + 2)) : φ (uc22pwSLnDv a j) = uc22pwSLnDv (a ^ 2 ^ i) j := by
  by_cases h0 : j = 0
  · subst h0
    simp [uc22pwSLnDv, hi]
  by_cases hl : j = Fin.last (m + 1)
  · subst hl
    simp [uc22pwSLnDv, h0, hi, inv_pow]
  · simp [uc22pwSLnDv, h0, hl, hi]

variable (m K) in
@[expose] def uc22pwSLnD : Kˣ →* SpecialLinearGroup (Fin (m + 2)) K where
  toFun a := ⟨diagonal (uc22pwSLnDv a), by rw [det_diagonal, prod_uc22pwSLnDv]⟩
  map_one' := Subtype.ext <| by
    change diagonal (uc22pwSLnDv 1) = 1
    rw [← diagonal_one]
    congr 1
    funext i
    simp [uc22pwSLnDv]
  map_mul' a b := Subtype.ext <| by
    change diagonal (uc22pwSLnDv (a * b)) = diagonal (uc22pwSLnDv a) * diagonal (uc22pwSLnDv b)
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    exact uc22pwSLnDv_mul a b i

theorem coe_uc22pwSLnD (a : Kˣ) :
    ((uc22pwSLnD m K a : SpecialLinearGroup (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) = diagonal (uc22pwSLnDv a) :=
  rfl

theorem uc22pwSLnD_injective : Function.Injective (uc22pwSLnD m K) := by
  intro a b h
  have h00 := congrArg (fun g : SpecialLinearGroup (Fin (m + 2)) K =>
      (g : Matrix (Fin (m + 2)) (Fin (m + 2)) K) 0 0) h
  simp [coe_uc22pwSLnD, uc22pwSLnDv] at h00
  exact Units.ext h00

theorem uc22pwSLnD_mem_upperTriangular (a : Kˣ) :
    uc22pwSLnD m K a ∈ upperTriangular (m + 2) K := by
  rw [mem_upperTriangular]
  intro i j hji
  rw [coe_uc22pwSLnD, Matrix.diagonal_apply_ne _ (ne_of_gt hji)]

theorem uc22pwSLnD_map {φ : K ≃+* K} {i : ℕ} (hi : ∀ x : K, φ x = x ^ 2 ^ i) (a : Kˣ) :
    ((uc22pwSLnD m K a : SpecialLinearGroup (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K).map φ = diagonal (uc22pwSLnDv (a ^ 2 ^ i)) := by
  rw [coe_uc22pwSLnD, Matrix.diagonal_map (map_zero φ)]
  congr 1
  funext j
  exact uc22pwSLnDv_map hi a j

theorem uc22pwSLnD_graph {φ : K ≃+* K} {i : ℕ} (hi : ∀ x : K, φ x = x ^ 2 ^ i) (a : Kˣ) :
    ((((uc22pwSLnD m K a)⁻¹ : SpecialLinearGroup (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K)ᵀ).map φ =
      permMatrix (m + 2) K Fin.revPerm * diagonal (uc22pwSLnDv (a ^ 2 ^ i)) *
        permMatrix (m + 2) K Fin.revPerm := by
  have hD : ((uc22pwSLnD m K a)⁻¹ : SpecialLinearGroup (Fin (m + 2)) K) =
      uc22pwSLnD m K a⁻¹ := ((uc22pwSLnD m K).map_inv a).symm
  rw [hD, coe_uc22pwSLnD, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero φ)]
  have hφ : (fun j : Fin (m + 2) => φ (uc22pwSLnDv (m := m) a⁻¹ j)) =
      uc22pwSLnDv (m := m) ((a⁻¹) ^ 2 ^ i) :=
    funext fun j => uc22pwSLnDv_map hi a⁻¹ j
  rw [hφ, inv_pow, CFSG.LieType.SpecialLinear.revGL_conj_diagonal]
  congr 1
  funext j
  exact (uc22pwSLnDv_rev (a ^ 2 ^ i) j).symm

variable (m K) in
@[expose] def uc22pwSLnJ [CharP K 2] : SpecialLinearGroup (Fin (m + 2)) K :=
  ⟨permMatrix (m + 2) K Fin.revPerm, by
    rw [det_permMatrix]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (m + 2)))) with
      h | h <;> simp [h, CharTwo.neg_eq]⟩

theorem coe_uc22pwSLnJ [CharP K 2] :
    ((uc22pwSLnJ m K : SpecialLinearGroup (Fin (m + 2)) K) :
      Matrix (Fin (m + 2)) (Fin (m + 2)) K) = permMatrix (m + 2) K Fin.revPerm :=
  rfl

theorem uc22pwSLnJ_mul_self [CharP K 2] : uc22pwSLnJ m K * uc22pwSLnJ m K = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one,
    coe_uc22pwSLnJ]
  exact CFSG.LieType.SpecialLinear.permMatrix_rev_mul_self K (m + 2)

theorem uc22pwSLnJ_conj [CharP K 2] (a : Kˣ) :
    uc22pwSLnJ m K * uc22pwSLnD m K a * (uc22pwSLnJ m K)⁻¹ = (uc22pwSLnD m K a)⁻¹ := by
  have hJ : (uc22pwSLnJ m K)⁻¹ = uc22pwSLnJ m K :=
    inv_eq_of_mul_eq_one_right (uc22pwSLnJ_mul_self (m := m) (K := K))
  have hD : (uc22pwSLnD m K a)⁻¹ = uc22pwSLnD m K a⁻¹ :=
    ((uc22pwSLnD m K).map_inv a).symm
  rw [hJ, hD]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    coe_uc22pwSLnJ, coe_uc22pwSLnD, coe_uc22pwSLnD]
  rw [CFSG.LieType.SpecialLinear.revGL_conj_diagonal]
  congr 1
  funext i
  exact uc22pwSLnDv_rev a i

theorem uc22pwSLnJ_not_mem_stabilizer [CharP K 2] {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ m + 1) :
    uc22pwSLnJ m K ∉ stabilizer (flagSpace (m + 2) K k) := by
  intro h
  rw [mem_stabilizer] at h
  have he : (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K) ∈
      flagSpace (m + 2) K k := by
    rw [mem_flagSpace]
    intro j hj
    have hj0 : j ≠ 0 := fun h0 => by
      rw [h0] at hj
      simp at hj
      omega
    exact Pi.single_eq_of_ne hj0 _
  have h1 : (uc22pwSLnJ m K : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ
      (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K) ∈
      flagSpace (m + 2) K k := by
    rw [← h]
    exact ⟨_, he, rfl⟩
  rw [mem_flagSpace] at h1
  have h2 := h1 (Fin.last (m + 1)) (by simpa using hk2)
  rw [coe_uc22pwSLnJ, permMatrix_mulVec_single, Fin.revPerm_apply, Fin.rev_zero,
    Pi.single_eq_same] at h2
  exact one_ne_zero h2

theorem uc22pwSLn_upper_sup_J [CharP K 2] :
    upperTriangular (m + 2) K ⊔ zpowers (uc22pwSLnJ m K) = ⊤ := by
  set A := upperTriangular (m + 2) K ⊔ Subgroup.zpowers (uc22pwSLnJ m K) with hA
  have hBA : upperTriangular (m + 2) K ≤ A := le_sup_left
  obtain ⟨hAeq, -⟩ := borel_overgroups A hBA
  have hcuts : borelOvergroupCuts A = ∅ := by
    by_contra hne
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.mpr hne
    have hwA : uc22pwSLnJ m K ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    rw [hAeq] at hwA
    have hw' := (mem_flagStabilizer.mp hwA) k hk
    obtain ⟨hk1, hkn, -⟩ := hk
    exact uc22pwSLnJ_not_mem_stabilizer hk1 (by omega) hw'
  rw [hcuts, flagStabilizer_empty] at hAeq
  exact hAeq

end CFSG.LocalAnalysis.UniquenessCase.UC22
