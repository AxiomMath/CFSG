module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsSU
public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.StandardType.SUTransvection

open Subgroup Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.StandardType.RCSTSU CFSG.StandardType.RootCentSU CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree (iotaHom mat_iotaHom iotaMat
  iotaMat_isBlkOn mid mem_range_mid mid_injective mid_ne_zero mid_ne_last submatrix_iotaMat
  rev_mid aform aform_apply map_aform)

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {k : ℕ}

@[expose] noncomputable def radCol (x : SU σ (k + 2)) : Fin k → F :=
  fun j => mat σ (k + 2) x (mid j) 0

omit [CharP F 2] in
theorem radCol_apply (x : SU σ (k + 2)) (j : Fin k) : radCol x j = mat σ (k + 2) x (mid j) 0 :=
  rfl

omit [CharP F 2] in
theorem radCol_one : radCol (1 : SU σ (k + 2)) = 0 := by
  funext j
  simp [radCol, Matrix.one_apply_ne (mid_ne_zero j)]

private theorem fin_succ_castSucc_mid (i : Fin k) :
    (Fin.succ (Fin.castSucc i) : Fin (k + 2)) = mid i := rfl

private theorem fin_succ_last_last :
    (Fin.succ (Fin.last k) : Fin (k + 2)) = Fin.last (k + 1) := rfl

private theorem row_zero_mem_suRad {x : SU σ (k + 2)} (hx : x ∈ suRad σ k) (b : Fin (k + 2)) :
    mat σ (k + 2) x 0 b = if b = 0 then 1 else 0 := by
  rw [row_zero_of_commute (commute_of_mem (mem_suRad.mp hx).1), (mem_suRad.mp hx).2.1]

private theorem col_last_mem_suRad {x : SU σ (k + 2)} (hx : x ∈ suRad σ k) (a : Fin (k + 2)) :
    mat σ (k + 2) x a (Fin.last (k + 1)) = if a = Fin.last (k + 1) then 1 else 0 := by
  have hA := commute_of_mem (mem_suRad.mp hx).1
  have h00 : mat σ (k + 2) x 0 0 = 1 := by
    rw [← corner_eq_of_commute hA, (mem_suRad.mp hx).2.1]
  rw [col_last_of_commute hA, h00]

private theorem mid_mid_mem_suRad {x : SU σ (k + 2)} (hx : x ∈ suRad σ k) (i j : Fin k) :
    mat σ (k + 2) x (mid i) (mid j) = if i = j then 1 else 0 := by
  have h2 := (mem_suRad.mp hx).2.2
  have h := congrFun (congrFun h2 i) j
  rw [Matrix.submatrix_apply] at h
  rw [h, Matrix.one_apply]

private theorem radCol_mul_apply {x y : SU σ (k + 2)} (hx : x ∈ suRad σ k)
    (hy : y ∈ suRad σ k) (j : Fin k) :
    mat σ (k + 2) (x * y) (mid j) 0 = radCol x j + radCol y j := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [fin_succ_castSucc_mid, fin_succ_last_last]
  rw [radCol_apply, radCol_apply]
  have hy0 : mat σ (k + 2) y 0 0 = 1 := by
    have h := row_zero_mem_suRad hy 0
    rwa [if_pos rfl] at h
  have hxl : mat σ (k + 2) x (mid j) (Fin.last (k + 1)) = 0 := by
    rw [col_last_mem_suRad hx, ite_eq_right (mid_ne_last j)]
  have hmid : ∀ i : Fin k, mat σ (k + 2) x (mid j) (mid i) = if j = i then 1 else 0 :=
    fun i => mid_mid_mem_suRad hx j i
  rw [hxl, hy0, zero_mul, add_zero, mul_one]
  have hsum : ∀ i : Fin k,
      mat σ (k + 2) x (mid j) (mid i) * mat σ (k + 2) y (mid i) 0 =
        if j = i then mat σ (k + 2) y (mid i) 0 else 0 := by
    intro i
    rw [hmid i]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_eq_single j]
  · simp
  · intro i _ hji
    rw [if_neg (Ne.symm hji)]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem radCol_mul {x y : SU σ (k + 2)} (hx : x ∈ suRad σ k) (hy : y ∈ suRad σ k) :
    radCol (x * y) = radCol x + radCol y := by
  funext j
  rw [radCol_apply, radCol_mul_apply hx hy, Pi.add_apply, radCol_apply, radCol_apply]

theorem radCol_inv {x : SU σ (k + 2)} (hx : x ∈ suRad σ k) : radCol x⁻¹ = -radCol x := by
  have h := radCol_mul hx (inv_mem hx)
  rw [mul_inv_cancel, radCol_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

private theorem mat_last_mid_apply (_hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (j : Fin k) :
    mat σ (k + 2) x (Fin.last (k + 1)) (mid j) = σ (radCol x (Fin.rev j)) := by
  have hxx := sum_mat_mul_mat x 0 (mid j)
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hxx
  simp only [fin_succ_castSucc_mid, fin_succ_last_last] at hxx
  have h00 : mat σ (k + 2) x 0 0 = 1 := by
    have h := row_zero_mem_suRad hx 0
    rwa [if_pos rfl] at h
  have hrow : mat σ (k + 2) x 0 (mid j) = 0 := by
    rw [row_zero_mem_suRad hx, if_neg (mid_ne_zero j)]
  have hsum : (∑ i : Fin k, σ (mat σ (k + 2) x (mid i) 0) *
      mat σ (k + 2) x (mid i).rev (mid j)) = σ (radCol x (Fin.rev j)) := by
    have hterm : ∀ i : Fin k, σ (mat σ (k + 2) x (mid i) 0) *
        mat σ (k + 2) x (mid i).rev (mid j) =
        if i = Fin.rev j then σ (radCol x (Fin.rev j)) else 0 := by
      intro i
      rw [rev_mid i, radCol_apply, mid_mid_mem_suRad hx (Fin.rev i) j]
      by_cases hi : i = Fin.rev j
      · subst hi
        rw [Fin.rev_rev, if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hi, if_neg]
        · exact mul_zero _
        · intro h2
          exact hi (by rw [← h2, Fin.rev_rev])
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_eq_single (Fin.rev j)]
    · simp
    · intro i _ hi
      rw [if_neg hi]
    · intro hi
      exact absurd (Finset.mem_univ (Fin.rev j)) hi
  rw [Fin.rev_zero, Fin.rev_last, if_neg (mid_ne_last j), h00, hrow, map_one,
    one_mul, mul_zero, add_zero, hsum] at hxx
  have h := congrArg (fun z => z + σ (radCol x (Fin.rev j))) hxx
  simpa [add_assoc, CharTwo.add_self_eq_zero] using h

theorem mat_last_mid_of_mem_suRad (hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (j : Fin k) :
    mat σ (k + 2) x (Fin.last (k + 1)) (mid j) = σ (radCol x (Fin.rev j)) :=
  mat_last_mid_apply hσ hx j

private theorem mat_mul_last_zero (hσ : ∀ c, σ (σ c) = c) {x y : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (hy : y ∈ suRad σ k) :
    mat σ (k + 2) (x * y) (Fin.last (k + 1)) 0 =
      mat σ (k + 2) x (Fin.last (k + 1)) 0 + mat σ (k + 2) y (Fin.last (k + 1)) 0 +
        aform σ (radCol x) (radCol y) := by
  rw [map_mul, Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [fin_succ_castSucc_mid, fin_succ_last_last]
  have hy0 : mat σ (k + 2) y 0 0 = 1 := by
    have h := row_zero_mem_suRad hy 0
    rwa [if_pos rfl] at h
  have hxl : mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) = 1 :=
    (mem_suRad.mp hx).2.1
  have hsum : (∑ i : Fin k, mat σ (k + 2) x (Fin.last (k + 1)) (mid i) *
      mat σ (k + 2) y (mid i) 0) = aform σ (radCol x) (radCol y) := by
    have h1 : ∀ i : Fin k, mat σ (k + 2) x (Fin.last (k + 1)) (mid i) *
        mat σ (k + 2) y (mid i) 0 = σ (radCol x (Fin.rev i)) * radCol y i := by
      intro i
      rw [mat_last_mid_of_mem_suRad hσ hx i, radCol_apply y i]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), aform_apply]
    refine Fintype.sum_equiv Fin.revPerm _ _ (fun a => ?_)
    rw [Fin.revPerm_apply, Fin.rev_rev]
  rw [hy0, hxl, mul_one, one_mul, hsum]
  ring

theorem aform_radCol_comm (hσ : ∀ c, σ (σ c) = c) {x y : SU σ (k + 2)} (hx : x ∈ suRad σ k)
    (hy : y ∈ suRad σ k) (h : x * y = y * x) :
    aform σ (radCol x) (radCol y) = aform σ (radCol y) (radCol x) := by
  have hxy := mat_mul_last_zero hσ hx hy
  have hyx := mat_mul_last_zero hσ hy hx
  rw [h] at hxy
  have h1 := hxy.symm.trans hyx
  rw [add_comm (mat σ (k + 2) x (Fin.last (k + 1)) 0)] at h1
  exact add_left_cancel h1

omit [CharP F 2] in
private theorem mat_conj_iotaHom_apply (x : SU σ (k + 2)) (B : SU σ k) (j : Fin k) :
    mat σ (k + 2) (iotaHom B * x * (iotaHom B)⁻¹) (mid j) 0 =
      (mat σ k B *ᵥ radCol x) j := by
  have hQ : mat σ (k + 2) ((iotaHom B)⁻¹) = iotaMat (mat σ k B⁻¹) := by
    rw [← map_inv, mat_iotaHom]
  have h0 : (0 : Fin (k + 2)) ∉ Set.range (mid (m := k)) := by
    rw [mem_range_mid]
    simp
  have hQ0 : ∀ b : Fin (k + 2),
      iotaMat (mat σ k B⁻¹) b 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) b 0 :=
    fun b => iotaMat_isBlkOn _ b 0 (Or.inr h0)
  have hinner : ∀ a : Fin (k + 2),
      (mat σ (k + 2) x * iotaMat (mat σ k B⁻¹)) a 0 = mat σ (k + 2) x a 0 := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [hQ0 0, Matrix.one_apply_eq, mul_one]
    · intro b _ hb
      rw [hQ0 b, Matrix.one_apply, if_neg hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ 0) h
  have hPm : ∀ j' : Fin k,
      iotaMat (mat σ k B) (mid j) (mid j') = mat σ k B j j' :=
    fun j' => CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.iotaMat_mid _ j j'
  have hP0 : ∀ a : Fin (k + 2), a ∉ Set.range (mid (m := k)) →
      iotaMat (mat σ k B) (mid j) a = 0 := by
    intro a ha
    rw [iotaMat_isBlkOn _ (mid j) a (Or.inr ha), Matrix.one_apply_ne (fun h => ha ⟨j, h⟩)]
  rw [map_mul, map_mul, mat_iotaHom, hQ, Matrix.mul_assoc, Matrix.mul_apply]
  rw [← Fintype.sum_of_injective mid mid_injective
    (fun j' => iotaMat (mat σ k B) (mid j) (mid j') *
      (mat σ (k + 2) x * iotaMat (mat σ k B⁻¹)) (mid j') 0)
    (fun a => iotaMat (mat σ k B) (mid j) a *
      (mat σ (k + 2) x * iotaMat (mat σ k B⁻¹)) a 0)
    (fun a ha => by rw [hP0 a ha, zero_mul]) (fun j' => rfl)]
  simp only [hPm, hinner]
  rfl

omit [CharP F 2] in
theorem radCol_conj_iotaHom (x : SU σ (k + 2)) (B : SU σ k) :
    radCol (iotaHom B * x * (iotaHom B)⁻¹) = mat σ k B *ᵥ radCol x := by
  funext j
  rw [radCol_apply]
  exact mat_conj_iotaHom_apply x B j

omit [CharP F 2] in
private theorem mat_mid_zero_of_radCol_eq_zero {x : SU σ (k + 2)} (h0 : radCol x = 0)
    (i : Fin k) : mat σ (k + 2) x (mid i) 0 = 0 := by
  rw [← radCol_apply]
  exact congrFun h0 i

private theorem mat_apply_mid_of_radCol_eq_zero {x : SU σ (k + 2)} (hx : x ∈ suRad σ k)
    (h0 : radCol x = 0) (i : Fin k) (b : Fin (k + 2)) :
    mat σ (k + 2) x (mid i) b =
      (1 + single (Fin.last (k + 1)) 0 (mat σ (k + 2) x (Fin.last (k + 1)) 0)) (mid i) b := by
  by_cases hb : b ∈ Set.range (mid (m := k))
  · obtain ⟨i', rfl⟩ := hb
    by_cases hii : i = i'
    · subst hii
      rw [mid_mid_mem_suRad hx i i, if_pos rfl]
      change (1 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) (mid i) +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) (mid i) (mid i)
      rw [Matrix.one_apply_eq, Matrix.single_apply_of_row_ne (mid_ne_last i).symm, add_zero]
    · rw [mid_mid_mem_suRad hx i i', if_neg hii]
      change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) (mid i') +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) (mid i) (mid i')
      rw [Matrix.one_apply_ne (mid_injective.ne hii),
        Matrix.single_apply_of_row_ne (mid_ne_last i).symm, add_zero]
  · rcases eq_zero_or_eq_last_of_not_mem hb with rfl | rfl
    · rw [mat_mid_zero_of_radCol_eq_zero h0 i]
      change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) 0 +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) (mid i) 0
      rw [Matrix.one_apply_ne (mid_ne_zero i),
        Matrix.single_apply_of_row_ne (mid_ne_last i).symm, zero_add]
    · rw [col_last_mem_suRad hx, if_neg (mid_ne_last i)]
      change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (mid i) (Fin.last (k + 1)) +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) (mid i) (Fin.last (k + 1))
      rw [Matrix.one_apply_ne (mid_ne_last i),
        Matrix.single_apply_of_row_ne (mid_ne_last i).symm, zero_add]

private theorem mat_apply_zero_of_radCol_eq_zero {x : SU σ (k + 2)} (hx : x ∈ suRad σ k)
    (b : Fin (k + 2)) :
    mat σ (k + 2) x 0 b =
      (1 + single (Fin.last (k + 1)) 0 (mat σ (k + 2) x (Fin.last (k + 1)) 0)) 0 b := by
  have hlast0 : (Fin.last (k + 1) : Fin (k + 2)) ≠ 0 := by simp
  by_cases hb : b ∈ Set.range (mid (m := k))
  · obtain ⟨j, rfl⟩ := hb
    rw [row_zero_mem_suRad hx, if_neg (mid_ne_zero j)]
    change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 (mid j) +
      single (Fin.last (k + 1)) (0 : Fin (k + 2))
        (mat σ (k + 2) x (Fin.last (k + 1)) 0) 0 (mid j)
    rw [Matrix.one_apply_ne (Ne.symm (mid_ne_zero j)),
      Matrix.single_apply_of_row_ne hlast0, zero_add]
  · rcases eq_zero_or_eq_last_of_not_mem hb with rfl | rfl
    · rw [row_zero_mem_suRad hx, if_pos rfl]
      change (1 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 0 +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) 0 0
      rw [Matrix.one_apply_eq, Matrix.single_apply_of_row_ne hlast0, add_zero]
    · rw [row_zero_mem_suRad hx, if_neg hlast0]
      change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 (Fin.last (k + 1)) +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) 0 (Fin.last (k + 1))
      rw [Matrix.one_apply_ne (Ne.symm hlast0),
        Matrix.single_apply_of_row_ne hlast0, zero_add]

private theorem mat_apply_last_of_radCol_eq_zero (hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (h0 : radCol x = 0) (b : Fin (k + 2)) :
    mat σ (k + 2) x (Fin.last (k + 1)) b =
      (1 + single (Fin.last (k + 1)) 0 (mat σ (k + 2) x (Fin.last (k + 1)) 0))
        (Fin.last (k + 1)) b := by
  have hlast0 : (Fin.last (k + 1) : Fin (k + 2)) ≠ 0 := by simp
  by_cases hb : b ∈ Set.range (mid (m := k))
  · obtain ⟨j, rfl⟩ := hb
    rw [mat_last_mid_of_mem_suRad hσ hx j, h0, Pi.zero_apply, map_zero]
    change (0 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (Fin.last (k + 1)) (mid j) +
      single (Fin.last (k + 1)) (0 : Fin (k + 2))
        (mat σ (k + 2) x (Fin.last (k + 1)) 0) (Fin.last (k + 1)) (mid j)
    rw [Matrix.one_apply_ne (Ne.symm (mid_ne_last j)), Matrix.single_apply,
      if_neg (by rintro ⟨-, h⟩; exact (mid_ne_zero j).symm h), zero_add]
  · rcases eq_zero_or_eq_last_of_not_mem hb with rfl | rfl
    · change (mat σ (k + 2) x (Fin.last (k + 1)) 0 : F) =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) (Fin.last (k + 1)) 0 +
          single (Fin.last (k + 1)) (0 : Fin (k + 2))
            (mat σ (k + 2) x (Fin.last (k + 1)) 0) (Fin.last (k + 1)) 0
      rw [Matrix.one_apply_ne hlast0, Matrix.single_apply_same, zero_add]
    · rw [(mem_suRad.mp hx).2.1]
      change (1 : F) = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F)
          (Fin.last (k + 1)) (Fin.last (k + 1)) +
        single (Fin.last (k + 1)) (0 : Fin (k + 2))
          (mat σ (k + 2) x (Fin.last (k + 1)) 0) (Fin.last (k + 1)) (Fin.last (k + 1))
      rw [Matrix.one_apply_eq, Matrix.single_apply,
        if_neg (by rintro ⟨-, h⟩; exact hlast0.symm h), add_zero]

theorem mat_of_radCol_eq_zero (hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)} (hx : x ∈ suRad σ k)
    (h0 : radCol x = 0) :
    mat σ (k + 2) x = 1 + single (Fin.last (k + 1)) 0 (mat σ (k + 2) x (Fin.last (k + 1)) 0) := by
  ext a b
  by_cases ha : a ∈ Set.range (mid (m := k))
  · obtain ⟨i, rfl⟩ := ha
    exact mat_apply_mid_of_radCol_eq_zero hx h0 i b
  · rcases eq_zero_or_eq_last_of_not_mem ha with rfl | rfl
    · exact mat_apply_zero_of_radCol_eq_zero hx b
    · exact mat_apply_last_of_radCol_eq_zero hσ hx h0 b

omit [CharP F 2] in
private theorem single_commute_iotaMat (c : F) (B : SU σ k) :
    single (Fin.last (k + 1)) 0 c * iotaMat (mat σ k B) =
      iotaMat (mat σ k B) * single (Fin.last (k + 1)) 0 c := by
  have h0 : (0 : Fin (k + 2)) ∉ Set.range (mid (m := k)) := by
    rw [mem_range_mid]
    simp
  have hl : (Fin.last (k + 1)) ∉ Set.range (mid (m := k)) := by
    rw [mem_range_mid]
    simp
  have hrow : ∀ b : Fin (k + 2), iotaMat (mat σ k B) 0 b =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b :=
    fun b => iotaMat_isBlkOn _ 0 b (Or.inl h0)
  have hcol : ∀ a : Fin (k + 2), iotaMat (mat σ k B) a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) :=
    fun a => iotaMat_isBlkOn _ a _ (Or.inr hl)
  ext a b
  by_cases ha : a = Fin.last (k + 1)
  · subst ha
    by_cases hb : b = 0
    · subst hb
      rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_same, hrow 0,
        hcol (Fin.last (k + 1)), Matrix.one_apply_eq, Matrix.one_apply_eq]
      ring
    · rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ hb,
        hrow b, Matrix.one_apply, if_neg (Ne.symm hb), mul_zero]
  · by_cases hb : b = 0
    · subst hb
      rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, Matrix.mul_single_apply_same, hcol a,
        Matrix.one_apply, if_neg ha, zero_mul]
    · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha,
        Matrix.mul_single_apply_of_ne _ _ _ _ _ hb]

theorem commute_iotaHom_of_radCol_eq_zero (hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (h0 : radCol x = 0) (B : SU σ k) : x * iotaHom B = iotaHom B * x := by
  apply mat_injective
  rw [map_mul, map_mul, mat_of_radCol_eq_zero hσ hx h0, mat_iotaHom, Matrix.add_mul,
    Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  rw [single_commute_iotaMat (mat σ (k + 2) x (Fin.last (k + 1)) 0) B]

theorem sq_eq_one_of_radCol_eq_zero (hσ : ∀ c, σ (σ c) = c) {x : SU σ (k + 2)}
    (hx : x ∈ suRad σ k) (h0 : radCol x = 0) : x ^ 2 = 1 := by
  apply mat_injective
  rw [pow_two, map_mul, mat_of_radCol_eq_zero hσ hx h0, map_one]
  have hlast0 : (Fin.last (k + 1) : Fin (k + 2)) ≠ 0 := by simp
  have hS : single (Fin.last (k + 1)) (0 : Fin (k + 2))
        (mat σ (k + 2) x (Fin.last (k + 1)) 0) *
      single (Fin.last (k + 1)) (0 : Fin (k + 2))
        (mat σ (k + 2) x (Fin.last (k + 1)) 0) = 0 := by
    rw [Matrix.single_mul_single_of_ne (c := mat σ (k + 2) x (Fin.last (k + 1)) 0)
      (i := Fin.last (k + 1)) (j := (0 : Fin (k + 2))) (k := Fin.last (k + 1))
      (Ne.symm hlast0)]
  have h2 : ∀ Y : Matrix (Fin (k + 2)) (Fin (k + 2)) F, Y + Y = 0 := fun Y => by
    ext a b
    simp [CharTwo.add_self_eq_zero]
  rw [one_add_mul_self (h2 _), hS, add_zero]

theorem exists_mat_eq_submatrix_mid {x : SU σ (k + 2)}
    (hx : x ∈ centralizer ({ggInvSU σ (k + 2) 1} : Set (SU σ (k + 2))))
    (h1 : mat σ (k + 2) x (Fin.last (k + 1)) (Fin.last (k + 1)) = 1) :
    ∃ B : SU σ k, mat σ k B = (mat σ (k + 2) x).submatrix mid mid := by
  have hA := commute_of_mem hx
  have h00 : mat σ (k + 2) x 0 0 = 1 := by rw [← corner_eq_of_commute hA]; exact h1
  have hcol : ∀ a, mat σ (k + 2) x a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) := by
    intro a
    rw [col_last_of_commute hA, h00]
    by_cases ha : a = Fin.last (k + 1)
    · rw [ite_eq_left ha, ha, Matrix.one_apply_eq]
    · rw [ite_eq_right ha, Matrix.one_apply_ne ha]
  have hrow : ∀ b, mat σ (k + 2) x 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b := by
    intro b
    rw [row_zero_of_commute hA, h1]
    by_cases hb : b = 0
    · rw [ite_eq_left hb, hb, Matrix.one_apply_eq]
    · rw [ite_eq_right hb, Matrix.one_apply_ne (Ne.symm hb)]
  have hdet : ((mat σ (k + 2) x).submatrix mid mid).det = 1 := by
    rw [← det_eq_det_submatrix_mid hrow hcol]
    exact x.2.1
  have hBu : IsUnit ((mat σ (k + 2) x).submatrix mid mid).det := by
    rw [hdet]
    exact isUnit_one
  exact ⟨⟨⟨(mat σ (k + 2) x).submatrix mid mid, ((mat σ (k + 2) x).submatrix mid mid)⁻¹,
    Matrix.mul_nonsing_inv _ hBu, Matrix.nonsing_inv_mul _ hBu⟩, hdet,
    isometry_submatrix_mid x hrow⟩, rfl⟩

omit [CharP F 2] in
private theorem conjTr_antidiag (n : ℕ) :
    conjTr σ (antidiag n : Matrix (Fin n) (Fin n) F) = antidiag n := by
  ext i j
  simp only [conjTr, transpose_apply, Matrix.map_apply, antidiag, of_apply]
  by_cases h : i = Fin.rev j
  · have h' : j = Fin.rev i := by rw [h, Fin.rev_rev]
    rw [if_pos h, if_pos h', map_one]
  · have h' : j ≠ Fin.rev i := fun hh => h (by rw [hh, Fin.rev_rev])
    rw [if_neg h, if_neg h', map_zero]

private theorem det_antidiag_eq_one (n : ℕ) :
    (antidiag n : Matrix (Fin n) (Fin n) F).det = 1 := by
  have h : (antidiag n : Matrix (Fin n) (Fin n) F).det *
      (antidiag n : Matrix (Fin n) (Fin n) F).det = 1 := by
    rw [← Matrix.det_mul, antidiag_mul_self, Matrix.det_one]
  have h2 : (antidiag n : Matrix (Fin n) (Fin n) F).det ^ 2 = (1 : F) ^ 2 := by
    rw [pow_two, h, one_pow]
  exact CharTwo.sq_inj.1 h2

private theorem exists_antidiag_mem_SU (n : ℕ) :
    ∃ J : SU σ n, mat σ n J = antidiag n := by
  refine ⟨⟨⟨antidiag n, antidiag n, antidiag_mul_self n, antidiag_mul_self n⟩, ?_⟩, rfl⟩
  refine mem_SU.mpr ⟨det_antidiag_eq_one n, ?_⟩
  rw [conjTr_antidiag]
  change (antidiag n : Matrix (Fin n) (Fin n) F) * antidiag n * antidiag n = antidiag n
  rw [Matrix.mul_assoc, antidiag_mul_self, Matrix.mul_one]

omit [CharP F 2] in
private theorem antidiag_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ((antidiag n : Matrix (Fin n) (Fin n) F) * A) i j = A (Fin.rev i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev i)]
  · simp [antidiag]
  · intro b _ hb
    simp [antidiag, hb]
  · simp

omit [CharP F 2] in
private theorem mul_antidiag_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    (A * (antidiag n : Matrix (Fin n) (Fin n) F)) i j = A i (Fin.rev j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.rev j)]
  · simp [antidiag]
  · intro b _ hb
    have h : j ≠ Fin.rev b := fun h => hb (by rw [h, Fin.rev_rev])
    simp [antidiag, h]
  · simp

omit [CharP F 2] in
private theorem eMat_rev_zero_rev {y : Fin (k + 2) → F} (hy : y (Fin.last (k + 1)) = 0)
    (c : F) (b : Fin (k + 2)) :
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat σ y c (Fin.rev 0) (Fin.rev b) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b := by
  rw [Fin.rev_zero, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat_apply, hy,
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.e0_last]
  simp only [zero_mul, add_zero]
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases hb : b = 0
  · subst hb
    simp
  · have h : Fin.last (k + 1) ≠ Fin.rev b := fun hh =>
      hb (by rw [← Fin.rev_rev b, ← hh, Fin.rev_last])
    rw [if_neg h, if_neg (Ne.symm hb)]

omit [CharP F 2] in
private theorem eMat_rev_last {y : Fin (k + 2) → F} (hy : y (Fin.last (k + 1)) = 0)
    (c : F) (a : Fin (k + 2)) :
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat σ y c (Fin.rev a)
        (Fin.rev (Fin.last (k + 1))) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1)) := by
  rw [Fin.rev_last, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat_apply,
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eL_zero, mul_zero, Fin.rev_zero, hy,
    map_zero, sub_zero, mul_zero, add_zero]
  rw [Matrix.one_apply, Matrix.one_apply]
  by_cases ha : a = Fin.last (k + 1)
  · subst ha
    simp
  · have h : Fin.rev a ≠ 0 := fun hh =>
      ha (by rw [← Fin.rev_rev a, hh, Fin.rev_zero])
    rw [if_neg h, if_neg ha, mul_zero, add_zero]

omit [CharP F 2] in
private theorem commute_ggInvUMatrix_of_row_col {A : Matrix (Fin (k + 2)) (Fin (k + 2)) F}
    (hrow : ∀ b, A 0 b = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) 0 b)
    (hcol : ∀ a, A a (Fin.last (k + 1)) =
      (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) F) a (Fin.last (k + 1))) :
    A * ggInvUMatrix (k + 2) 1 F = ggInvUMatrix (k + 2) 1 F * A := by
  rw [RootCentSU.ggInvUMatrix_one_eq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
    Matrix.one_mul]
  congr 1
  ext a b
  by_cases hb : b = 0
  · subst hb
    rw [mul_single_apply_same, mul_one]
    by_cases ha : a = Fin.last (k + 1)
    · subst ha
      rw [single_mul_apply_same, one_mul, hcol, hrow, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [single_mul_apply_of_ne _ _ _ _ _ ha, hcol, Matrix.one_apply_ne ha]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hb]
    by_cases ha : a = Fin.last (k + 1)
    · subst ha
      rw [single_mul_apply_same, one_mul, hrow, Matrix.one_apply_ne (Ne.symm hb)]
    · rw [single_mul_apply_of_ne _ _ _ _ _ ha]

theorem exists_mem_suRad_radCol_eq (hσ : IsUnitaryInvolution σ) (θ : Fin k → F) :
    ∃ x ∈ suRad σ k, radCol x = θ := by
  have hσ' : ∀ c, σ (σ c) = c := hσ.invol
  let y : Fin (k + 2) → F :=
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.midExt (θ ∘ Fin.rev)
  have hy : y (Fin.last (k + 1)) = 0 :=
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.midExt_last _
  have hy0 : y 0 = 0 :=
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.midExt_zero_apply _
  obtain ⟨c, hc⟩ := hσ.trace_surj (aform σ y y) (map_aform σ hσ' y y)
  have hc' : c + σ c + aform σ y y = 0 := by
    rw [hc, CharTwo.add_self_eq_zero]
  let E : SU σ (k + 2) :=
    CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eSU σ hσ' hy (c := c) hc'
  obtain ⟨J, hJ⟩ := exists_antidiag_mem_SU (σ := σ) (n := k + 2)
  let M : SU σ (k + 2) := J * E * J
  have hME : mat σ (k + 2) M =
      antidiag (k + 2) * CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat σ y c *
        antidiag (k + 2) := by
    simp only [M, E, map_mul, hJ, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.mat_eSU]
  have hentry : ∀ i j, mat σ (k + 2) M i j =
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat σ y c (Fin.rev i) (Fin.rev j) := by
    intro i j
    rw [hME, mul_antidiag_apply, antidiag_mul_apply]
  refine ⟨M, ?_, ?_⟩
  · refine mem_suRad.mpr ⟨?_, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      apply mat_injective
      simp only [map_mul, mat_ggInvSU_one]
      exact commute_ggInvUMatrix_of_row_col
        (fun b => by rw [hentry]; exact eMat_rev_zero_rev hy c b)
        (fun a => by rw [hentry]; exact eMat_rev_last hy c a)
    · rw [hentry, Fin.rev_last]
      simp [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat_apply, hy]
    · ext i j
      rw [Matrix.submatrix_apply, hentry, rev_mid, rev_mid]
      simp [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat_apply,
        mid_ne_zero, mid_ne_last, Matrix.one_apply, mid_injective.eq_iff,
        Fin.rev_injective.eq_iff]
  · funext j
    rw [radCol_apply, hentry, rev_mid, Fin.rev_zero,
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.eMat_apply_last σ hy0]
    simp [y, CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.midExt_mid,
      mid_ne_zero, mid_ne_last, Function.comp_apply, Fin.rev_rev]

theorem exists_mem_suRad_not_commute (hσ : IsUnitaryInvolution σ) (hk : 1 ≤ k) :
    ∃ x ∈ suRad σ k, ∃ y ∈ suRad σ k, x * y ≠ y * x := by
  obtain ⟨μ, hμ⟩ := hσ.exists_ne
  let i0 : Fin k := ⟨0, by omega⟩
  have h1 : aform σ (Pi.single i0 1) (μ • Pi.single (Fin.rev i0) 1) = μ := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_smul_right,
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_single]
    simp [i0, antidiag]
  have h2 : aform σ (μ • Pi.single (Fin.rev i0) 1) (Pi.single i0 1) = σ μ := by
    rw [CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_smul_left,
      CFSG.LieType.Steinberg.CentralExt.SUOddFieldThree.aform_single]
    simp [i0, antidiag, Fin.rev_rev]
  obtain ⟨x, hx, hxθ⟩ := exists_mem_suRad_radCol_eq hσ (Pi.single i0 1)
  obtain ⟨y, hy, hyθ⟩ := exists_mem_suRad_radCol_eq hσ (μ • Pi.single (Fin.rev i0) 1)
  refine ⟨x, hx, y, hy, fun hxy => ?_⟩
  have hcomm := aform_radCol_comm hσ.invol hx hy hxy
  rw [hxθ, hyθ, h1, h2] at hcomm
  exact hμ hcomm.symm

end CFSG.StandardType.SUTransvection
