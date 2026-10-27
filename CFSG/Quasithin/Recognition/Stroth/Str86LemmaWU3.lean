module

public import CFSG.Quasithin.Recognition.Stroth.Str86U3Model

import CFSG.Quasithin.Recognition.Stroth.Str86U3Model3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H Matrix
open scoped Matrix

private theorem one_le_k_of_natCard_eq_sq {K : Type} [Field K] [Finite K] {k : ℕ}
    (hK : Nat.card K = (2 ^ k) ^ 2) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exfalso
    have h2 : 1 < Nat.card K := Finite.one_lt_card (α := K)
    simp only [pow_zero, one_pow, one_mul] at hK
    omega
  · exact hk

private theorem exists_units_orderOf_eq_bar_inv {K : Type} [Field K] [Finite K] [CharP K 2]
    {k n : ℕ} (hK : Nat.card K = (2 ^ k) ^ 2) (hnq : n ∣ 2 ^ k + 1) :
    ∃ μ : Kˣ, orderOf μ = n ∧
      CFSG.Quasithin.H.SU3.bar k (μ : K) = (μ : K)⁻¹ := by
  have hKu : Nat.card Kˣ = (2 ^ k + 1) * (2 ^ k - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  have hdvdK : n ∣ Nat.card Kˣ := by
    rw [hKu]
    exact dvd_mul_of_dvd_left hnq _
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hdvdg : n ∣ orderOf g := hg ▸ hdvdK
  let μ : Kˣ := g ^ (orderOf g / n)
  have hμ : orderOf μ = n := orderOf_pow_orderOf_div (orderOf_pos g).ne' hdvdg
  have hμq : μ ^ (2 ^ k + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hμ]; exact hnq)
  have hμqK : (μ : K) ^ (2 ^ k + 1) = 1 := by
    simpa using congrArg (fun u : Kˣ => (u : K)) hμq
  have hbar : CFSG.Quasithin.H.SU3.bar k (μ : K) = (μ : K)⁻¹ := by
    rw [CFSG.Quasithin.H.SU3.bar_apply]
    have h : (μ : K) ^ (2 ^ k) * (μ : K) = 1 := by
      rw [← pow_succ]
      exact hμqK
    exact eq_inv_of_mul_eq_one_left h
  exact ⟨μ, hμ, hbar⟩

private theorem torJ_pow_coe_diagonal {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (μ : Kˣ) (d : ℕ)
    (hbar : CFSG.Quasithin.H.SU3.bar k (μ : K) = (μ : K)⁻¹) :
    ((CFSG.Quasithin.H.SU3.torJ k (μ ^ d) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![((μ ^ d : Kˣ) : K),
        ((μ ^ d : Kˣ) : K)⁻¹ * ((μ ^ d : Kˣ) : K)⁻¹, ((μ ^ d : Kˣ) : K)] := by
  have hbar' : CFSG.Quasithin.H.SU3.bar k ((μ ^ d : Kˣ) : K) =
      ((μ ^ d : Kˣ) : K)⁻¹ := by
    change CFSG.Quasithin.H.SU3.bar k ((μ : K) ^ d) = ((μ : K) ^ d)⁻¹
    calc
      CFSG.Quasithin.H.SU3.bar k ((μ : K) ^ d) =
          (CFSG.Quasithin.H.SU3.bar k (μ : K)) ^ d := map_pow _ _ _
      _ = ((μ : K)⁻¹) ^ d := by rw [hbar]
      _ = ((μ : K) ^ d)⁻¹ := inv_pow _ _
  rw [CFSG.Quasithin.H.SU3.coe_torJ, CFSG.Quasithin.H.SU3.torJMat]
  change Matrix.diagonal ![((μ ^ d : Kˣ) : K),
      CFSG.Quasithin.H.SU3.bar k ((μ ^ d : Kˣ) : K) * ((μ ^ d : Kˣ) : K)⁻¹,
      (CFSG.Quasithin.H.SU3.bar k ((μ ^ d : Kˣ) : K))⁻¹] =
    Matrix.diagonal ![((μ ^ d : Kˣ) : K),
      ((μ ^ d : Kˣ) : K)⁻¹ * ((μ ^ d : Kˣ) : K)⁻¹, ((μ ^ d : Kˣ) : K)]
  rw [hbar']
  congr 1
  funext i
  fin_cases i <;> simp

private theorem diagonal_fixed_eq_zero {K : Type} [Field K] {α : K} (hα1 : α ≠ 1)
    (hα2 : α * α ≠ 1) {v : Fin 3 → K}
    (hv : Matrix.diagonal ![α, α⁻¹ * α⁻¹, α] *ᵥ v = v) : v = 0 := by
  have hα2inv : α⁻¹ * α⁻¹ ≠ 1 := by
    intro h
    apply hα2
    have h' : (α⁻¹ * α⁻¹)⁻¹ = 1 := by rw [h, inv_one]
    simpa only [_root_.mul_inv_rev, inv_inv] using h'
  have hv0 : v 0 = 0 := by
    have h : α * v 0 = v 0 := by
      have := congrFun hv 0
      simpa [Matrix.mulVec_diagonal] using this
    have h' : (α - 1) * v 0 = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hα1)
  have hv1 : v 1 = 0 := by
    have h : (α⁻¹ * α⁻¹) * v 1 = v 1 := by
      have := congrFun hv 1
      simpa [Matrix.mulVec_diagonal] using this
    have h' : (α⁻¹ * α⁻¹ - 1) * v 1 = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hα2inv)
  have hv2 : v 2 = 0 := by
    have h : α * v 2 = v 2 := by
      have := congrFun hv 2
      simpa [Matrix.mulVec_diagonal] using this
    have h' : (α - 1) * v 2 = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hα1)
  funext i
  fin_cases i <;> simp [hv0, hv1, hv2]

private def su3BlockMat (K : Type) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 0, 1, 0; 1, 0, 1]

private theorem det_su3BlockMat {K : Type} [Field K] [CharP K 2] :
    (su3BlockMat K).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [su3BlockMat, CFSG.Quasithin.H.SU3.neg_one_eq_one]

private noncomputable def su3BlockY (K : Type) [Field K] [CharP K 2] : GL (Fin 3) K :=
  CFSG.Quasithin.H.SU3.glOfDetOne (su3BlockMat K) (det_su3BlockMat (K := K))

private theorem coe_su3BlockY {K : Type} [Field K] [CharP K 2] :
    ((su3BlockY K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = su3BlockMat K :=
  CFSG.Quasithin.H.SU3.coe_glOfDetOne (su3BlockMat K) (det_su3BlockMat (K := K))

private theorem su3BlockY_mem_su3Anti {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hK : Nat.card K = (2 ^ k) ^ 2) (hk : 1 ≤ k) : su3BlockY K ∈ su3Anti K k := by
  rw [mem_su3Anti_iff (F := K) hK]
  refine ⟨?_, ?_⟩
  · rw [coe_su3BlockY]
    exact det_su3BlockMat
  · rw [coe_su3BlockY]
    have hq0 : 2 ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    have h01 : ∀ i j : Fin 3, su3BlockMat K i j = 0 ∨ su3BlockMat K i j = 1 := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [su3BlockMat]
    have hmap : (su3BlockMat K).map (· ^ (2 ^ k)) = su3BlockMat K :=
      CFSG.Quasithin.H.SU3.map_pow_of_zero_one hq0 _ h01
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [su3BlockMat, CFSG.Quasithin.H.SU3.antiJ, Matrix.mul_apply, Fin.sum_univ_three,
        CharTwo.add_self_eq_zero]

private theorem su3BlockY_pow_three {K : Type} [Field K] [CharP K 2] :
    su3BlockY K ^ 3 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_su3BlockY, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3BlockMat, Matrix.mul_apply, Fin.sum_univ_three, pow_succ, pow_two,
      CharTwo.add_self_eq_zero]

private theorem commute_su3BlockY_torJ {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (μ : Kˣ)
    (hbar : CFSG.Quasithin.H.SU3.bar k (μ : K) = (μ : K)⁻¹) :
    Commute (su3BlockY K) (CFSG.Quasithin.H.SU3.torJ k μ) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_su3BlockY, CFSG.Quasithin.H.SU3.coe_torJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [su3BlockMat, CFSG.Quasithin.H.SU3.torJMat, hbar, Matrix.mul_apply, Matrix.diagonal,
      Fin.sum_univ_three, CharTwo.add_self_eq_zero]

private theorem su3BlockY_not_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {k : ℕ} (hk : 1 ≤ k) (hK : Nat.card K = (2 ^ k) ^ 2) :
    su3BlockY K ∉ Subgroup.normalizer
      (CFSG.Quasithin.H.SU3.ujSub k K : Set (GL (Fin 3) K)) := by
  intro hyN
  have hyL := su3BlockY_mem_su3Anti hK hk
  have hconj : ∀ b ∈ CFSG.Quasithin.H.SU3.ujSub k K,
      su3BlockY K * b * (su3BlockY K)⁻¹ ∈ CFSG.Quasithin.H.SU3.ujSub k K :=
    fun b hb => (Subgroup.mem_normalizer_iff.mp hyN b).mp hb
  obtain ⟨β, u, hu, hyu⟩ := exists_torJ_mul_of_mem_normalizer hk hK hyL hconj
  have h20 : ((su3BlockY K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 := by
    rw [hyu, Units.val_mul]
    obtain ⟨hlow, -⟩ := CFSG.Quasithin.H.Tri.uni3_entries
      (CFSG.Quasithin.H.SU3.ujSub_le_uni3 hu)
    simp [Matrix.mul_apply, Fin.sum_univ_three, CFSG.Quasithin.H.SU3.coe_torJ,
      CFSG.Quasithin.H.SU3.torJMat, Matrix.diagonal, hlow 1 0 (by decide),
      hlow 2 0 (by decide), hlow 2 1 (by decide)]
  have hy20 : ((su3BlockY K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 1 := by
    rw [coe_su3BlockY]
    simp [su3BlockMat]
  rw [hy20] at h20
  exact one_ne_zero h20

theorem exists_su3Anti_torus_and_block {K : Type} [Field K] [Finite K] [CharP K 2] {k : ℕ}
    (hK : Nat.card K = (2 ^ k) ^ 2) {n d : ℕ} (hn : Odd n)
    (hnq : n ∣ 2 ^ k + 1) (hd : ¬ n ∣ d) :
    ∃ w y : GL (Fin 3) K, w ∈ su3Anti K k ∧
      w ∈ Subgroup.normalizer (CFSG.Quasithin.H.SU3.ujSub k K : Set (GL (Fin 3) K)) ∧
      w ^ n = 1 ∧
      (∀ v : Fin 3 → K,
        ((w ^ d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0) ∧
      y ∈ su3Anti K k ∧ y ^ 3 = 1 ∧ Commute y w ∧
      y ∉ Subgroup.normalizer (CFSG.Quasithin.H.SU3.ujSub k K : Set (GL (Fin 3) K)) := by
  have hk : 1 ≤ k := one_le_k_of_natCard_eq_sq hK
  obtain ⟨μ, hμ, hbar⟩ := exists_units_orderOf_eq_bar_inv hK hnq
  let w : GL (Fin 3) K := CFSG.Quasithin.H.SU3.torJ k μ
  have hwL : w ∈ su3Anti K k := by
    dsimp [w]
    exact CFSG.Quasithin.H.SU3.torJ_mem_witt hK μ
  have hwN : w ∈ Subgroup.normalizer
      (CFSG.Quasithin.H.SU3.ujSub k K : Set (GL (Fin 3) K)) := by
    dsimp [w]
    exact torJ_mem_normalizer_ujSub hK μ
  have hwn : w ^ n = 1 := by
    dsimp [w]
    rw [← map_pow, ← hμ, pow_orderOf_eq_one, map_one]
  let α : K := ((μ ^ d : Kˣ) : K)
  have hα1 : α ≠ 1 := by
    intro h
    apply hd
    have hdvd : n ∣ d := by
      rw [← hμ]
      refine orderOf_dvd_iff_pow_eq_one.mpr ?_
      exact Units.ext (by simpa [α] using h)
    exact hdvd
  have hα2 : α * α ≠ 1 := by
    intro hαα
    have h : ((μ : K) ^ d) ^ 2 = 1 := by
      simpa [α, pow_two] using hαα
    have h2 : (μ : K) ^ (2 * d) = 1 := by
      rw [← pow_mul, mul_comm d 2] at h
      exact h
    have hμ2 : μ ^ (2 * d) = 1 := Units.ext (by simpa using h2)
    have hdvd2 : n ∣ 2 * d := by
      rw [← hμ]
      exact orderOf_dvd_iff_pow_eq_one.mpr hμ2
    exact hd ((hn.coprime_two_right).dvd_of_dvd_mul_left hdvd2)
  have hwd : ((w ^ d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![α, α⁻¹ * α⁻¹, α] := by
    have hpow : w ^ d = CFSG.Quasithin.H.SU3.torJ k (μ ^ d) := by
      dsimp [w]
      exact (map_pow (CFSG.Quasithin.H.SU3.torJ k) μ d).symm
    rw [hpow]
    have h := torJ_pow_coe_diagonal (k := k) μ d hbar
    simpa [α] using h
  have hfixall : ∀ v : Fin 3 → K,
      ((w ^ d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v → v = 0 := by
    intro v hv
    rw [hwd] at hv
    exact diagonal_fixed_eq_zero hα1 hα2 hv
  exact ⟨w, su3BlockY K, hwL, hwN, hwn, hfixall,
    su3BlockY_mem_su3Anti hK hk, su3BlockY_pow_three,
    commute_su3BlockY_torJ μ hbar, su3BlockY_not_mem_normalizer hk hK⟩

end CFSG.Quasithin.Stroth

end
