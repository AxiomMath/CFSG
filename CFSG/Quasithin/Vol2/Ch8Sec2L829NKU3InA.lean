module

public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Torus

public section

namespace CFSG.Quasithin.H13.L829NK.U3In

open CFSG.Open CFSG.SectionRank.ClassicalEven Matrix

theorem charP_two_of_natCard_eq {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Nat.card K = (2 ^ n) ^ 2) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  obtain ⟨k, hp, hk⟩ := FiniteField.card K (ringChar K)
  have h2 : ringChar K ^ (k : ℕ) = 2 ^ (2 * n) := by
    rw [← hk, ← Nat.card_eq_fintype_card, h, ← pow_mul, mul_comm]
  have hdvd : ringChar K ∣ 2 := by
    refine hp.dvd_of_dvd_pow (n := 2 * n) ?_
    rw [← h2]
    exact dvd_pow_self _ k.ne_zero
  have hr : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd
  have := ringChar.charP K
  rwa [hr] at this

section Witness

variable {K : Type} [Field K]

@[expose] def u3SwapMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

theorem u3SwapMat_mul_self : u3SwapMat * u3SwapMat = (1 : Matrix (Fin 3) (Fin 3) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3SwapMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

@[expose] def u3SwapU : GL (Fin 3) K :=
  Units.mk u3SwapMat u3SwapMat u3SwapMat_mul_self u3SwapMat_mul_self

theorem u3SwapU_val : ((u3SwapU : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u3SwapMat := rfl

theorem u3SwapU_sq : u3SwapU ^ 2 = (1 : GL (Fin 3) K) := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, u3SwapU_val, sq, u3SwapMat_mul_self]

theorem u3SwapMat_det [CharP K 2] : (u3SwapMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [u3SwapMat, CharTwo.neg_eq]

theorem u3SwapMat_unitary [CharP K 2] {q : ℕ} (hq : q ≠ 0) :
    ((u3SwapMat : Matrix (Fin 3) (Fin 3) K).map (fun x => x ^ q))ᵀ * u3SwapMat = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3SwapMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, zero_pow hq]

theorem u3SwapU_mem [CharP K 2] {q : ℕ} (hq : q ≠ 0) :
    (u3SwapU : GL (Fin 3) K) ∈ StatedSU 3 q K :=
  Subgroup.subset_closure ⟨u3SwapMat_det, u3SwapMat_unitary hq⟩

theorem u3_torus_g_mem [Finite K] {q : ℕ} (hq : q ≠ 0) (l : Kˣ) (hl : l ^ (q + 1) = 1) :
    torusDiag ![l, l⁻¹, 1] ∈ StatedSU 3 q K := by
  refine torusDiag_mem_SU hq ?_ ?_
  · simp [Fin.prod_univ_three]
  · funext i
    fin_cases i <;> simp [Pi.pow_apply, inv_pow, hl]

theorem u3SwapU_mul_conj_torus (l : Kˣ) :
    u3SwapU * ((torusDiag ![l, l⁻¹, 1])⁻¹ * u3SwapU * torusDiag ![l, l⁻¹, 1]) =
      torusDiag ![l ^ 2, (l⁻¹) ^ 2, 1] := by
  have hinv : (torusDiag ![l, l⁻¹, 1])⁻¹ = torusDiag ![l⁻¹, l, 1] := by
    rw [← map_inv]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [hinv]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3SwapU, u3SwapMat, coe_torusDiag, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.diagonal_apply, Units.val_mul, sq]

end Witness

section Proj

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem u3_exists_unit_order {q : ℕ} (hq : 16 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ l : Kˣ, orderOf l = q + 1 := by
  have hcard : Nat.card Kˣ = (q + 1) * (q - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨μ, hμ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hdvd : q - 1 ∣ orderOf μ := by
    rw [hμ, hcard]
    exact dvd_mul_left _ _
  refine ⟨μ ^ (q - 1), ?_⟩
  rw [orderOf_pow_of_dvd (by omega) hdvd, hμ, hcard, Nat.mul_div_cancel _ (by omega)]

theorem u3_exists_order_witness {q : ℕ} (hq : 16 ≤ q) (hK : Nat.card K = q ^ 2) :
    ∃ z g : StatedProj (StatedSU 3 q K), orderOf z = 2 ∧ 6 ≤ orderOf (z * (g⁻¹ * z * g)) := by
  obtain ⟨l, hl⟩ := u3_exists_unit_order hq hK
  have hq0 : q ≠ 0 := by omega
  have hlq : l ^ (q + 1) = 1 := by
    rw [← hl]
    exact pow_orderOf_eq_one l
  let zQ : StatedSU 3 q K := ⟨u3SwapU, u3SwapU_mem hq0⟩
  let gQ : StatedSU 3 q K := ⟨torusDiag ![l, l⁻¹, 1], u3_torus_g_mem hq0 l hlq⟩
  let wQ : StatedSU 3 q K := zQ * (gQ⁻¹ * zQ * gQ)
  have hwQ : (wQ : GL (Fin 3) K) = torusDiag ![l ^ 2, (l⁻¹) ^ 2, 1] :=
    u3SwapU_mul_conj_torus l
  let π : StatedSU 3 q K →* StatedProj (StatedSU 3 q K) :=
    QuotientGroup.mk' ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K))
  have hzsq : zQ ^ 2 = 1 := Subtype.ext u3SwapU_sq
  have hzne : π zQ ≠ 1 := by
    intro h
    have h' : zQ ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) :=
      (QuotientGroup.eq_one_iff zQ).1 h
    rw [Subgroup.mem_subgroupOf] at h'
    rw [StatedScalars] at h'
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h'
    have h01 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 1) hc
    simp [zQ, u3SwapU, u3SwapMat, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] at h01
  have hsq : π zQ ^ 2 = 1 := by
    rw [← map_pow, hzsq, map_one]
  have hz2 : orderOf (π zQ) = 2 := orderOf_eq_prime hsq hzne
  have hcomm : π zQ * ((π gQ)⁻¹ * π zQ * π gQ) = π wQ := by
    simp only [wQ, map_mul, map_inv]
  have hkey : ∀ k : ℕ, π wQ ^ k = 1 → l ^ (2 * k) = 1 := by
    intro k hk
    rw [← map_pow] at hk
    have hmem : wQ ^ k ∈ (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) :=
      (QuotientGroup.eq_one_iff (wQ ^ k)).1 hk
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, hwQ, ← map_pow, StatedScalars] at hmem
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 hmem
    rw [scalar_eq_torusDiag] at hc
    have hD := torusDiag_injective hc
    have hc1 : c = 1 := by
      have h2 := congrFun hD 2
      simpa using h2
    have h0 : c = (l ^ 2) ^ k := by
      have h0' := congrFun hD 0
      simpa [Pi.pow_apply] using h0'
    rw [pow_mul, ← h0, hc1]
  have hm6 : 6 ≤ orderOf (π wQ) := by
    by_contra hlt
    have hlt' : orderOf (π wQ) < 6 := not_le.1 hlt
    have hpos : 0 < orderOf (π wQ) := orderOf_pos _
    have h1 : l ^ (2 * orderOf (π wQ)) = 1 := hkey _ (pow_orderOf_eq_one _)
    have hdvd : orderOf l ∣ 2 * orderOf (π wQ) := orderOf_dvd_of_pow_eq_one h1
    rw [hl] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega
  exact ⟨π zQ, π gQ, hz2, by rw [hcomm]; exact hm6⟩

end Proj

end CFSG.Quasithin.H13.L829NK.U3In
