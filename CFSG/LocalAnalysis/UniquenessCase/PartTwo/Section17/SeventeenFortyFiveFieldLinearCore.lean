module

public import CFSG.RankThree.PartOne.CTP.SeitzMaxSLRoot
public import CFSG.RankThree.PartOne.SLB4B.ModelL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL proj proj_surjective
  proj_eq_one_iff mem_scalars)
open CFSG.RankThree.PartOne (linearSubfieldInclusion mem_range_linearSubfieldInclusion)
open CFSG.RankThree.PartOne.SLB4B (blockMat blockSL coe_blockSL blockMat_mul blockMat_one
  blockMat_inl_inl blockMat_inr_inr)

theorem exists_pow_five_not_mem_of_card {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hK : Nat.card K = Nat.card k ^ 5) (h5 : ¬ 5 ∣ Nat.card K - 1) :
    ∃ c : K, c ≠ 0 ∧ c ^ 5 ∉ k := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype K := Fintype.ofFinite K
  have hU : Nat.card Kˣ = Nat.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
  have hcop : Nat.Coprime (Nat.card Kˣ) 5 := by
    rw [hU]
    exact Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h5)
  have hinj : Function.Injective
      (fun u : Kˣ => (⟨((u ^ 5 : Kˣ) : K), by simpa using hcon _ u.ne_zero⟩ : k)) := by
    intro u v huv
    have h := congrArg Subtype.val huv
    exact (powCoprime hcop).injective (Units.ext h)
  have hle := Nat.card_le_card_of_injective _ hinj
  have hk2 : 1 < Nat.card k := Finite.one_lt_card
  rw [hU, hK] at hle
  have h4 : 2 ^ 4 ≤ Nat.card k ^ 4 := Nat.pow_le_pow_left hk2 4
  have h5' : Nat.card k ^ 5 = Nat.card k * Nat.card k ^ 4 := by ring
  have h6 : Nat.card k ^ 5 ≤ Nat.card k + 1 := by omega
  nlinarith

def phi5Companion (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, -1; 1, 0, 0, -1; 0, 1, 0, -1; 0, 0, 1, -1]

theorem det_phi5Companion (K : Type) [Field K] : (phi5Companion K).det = 1 := by
  have h32 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  simp [phi5Companion, Matrix.det_succ_row_zero, Fin.sum_univ_succ, h32] <;> norm_num

theorem phi5Companion_pow_five (K : Type) [Field K] : phi5Companion K ^ 5 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi5Companion, pow_succ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem phi5Companion_mem {K : Type} [Field K] (k : Subfield K) (i j : Fin 4) :
    phi5Companion K i j ∈ k := by
  fin_cases i <;> fin_cases j <;> simp [phi5Companion, neg_mem_iff]

@[expose] def phi5SL (K : Type) [Field K] : SpecialLinearGroup (Fin 4) K :=
  ⟨phi5Companion K, det_phi5Companion K⟩

theorem coe_phi5SL (K : Type) [Field K] :
    (phi5SL K : Matrix (Fin 4) (Fin 4) K) = phi5Companion K := rfl

private theorem blockMat_mem {K : Type} [Field K] (k : Subfield K) {m : ℕ}
    {A : Matrix (Fin 4) (Fin 4) K} (hA : ∀ i j, A i j ∈ k) (a b : Fin (4 + m)) :
    blockMat (m := m) A a b ∈ k := by
  induction a using Fin.addCases with
  | left i => induction b using Fin.addCases with
    | left j => rw [blockMat_inl_inl]; exact hA i j
    | right j => simp [blockMat]
  | right i => induction b using Fin.addCases with
    | left j => simp [blockMat]
    | right j =>
      rw [blockMat_inr_inr, Matrix.one_apply]
      split_ifs <;> simp

private theorem blockMat_pow {K : Type} [Field K] {m : ℕ} (A : Matrix (Fin 4) (Fin 4) K) (r : ℕ) :
    blockMat (m := m) (A ^ r) = blockMat (m := m) A ^ r := by
  induction r with
  | zero => rw [pow_zero, pow_zero, blockMat_one]
  | succ r ih => rw [pow_succ, blockMat_mul, ih, pow_succ]

theorem orderOf_proj_blockSL_phi5 {K : Type} [Field K] (m : ℕ) :
    orderOf (proj (4 + m) K (blockSL (m := m) (phi5SL K))) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply orderOf_eq_prime
  · have hd : (blockSL (m := m) (phi5SL K)) ^ 5 = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, coe_blockSL, ← blockMat_pow, coe_phi5SL,
        phi5Companion_pow_five, blockMat_one, Matrix.SpecialLinearGroup.coe_one]
    rw [← map_pow, hd, map_one]
  · intro h
    obtain ⟨c, -, hc⟩ := mem_scalars.mp (proj_eq_one_iff.mp h)
    have h0 := congrFun (congrFun hc (Fin.castAdd m 0)) (Fin.castAdd m 0)
    rw [coe_blockSL, blockMat_inl_inl, coe_phi5SL] at h0
    simp [phi5Companion] at h0 <;> first | exact c.ne_zero h0 | exact c.ne_zero h0.symm

@[expose] def torusFive {K : Type} [Field K] (c : K) (m : ℕ) : Fin (4 + (m + 1)) → K :=
  Fin.addCases (motive := fun _ => K) (fun _ => c)
    (Fin.cons (α := fun _ => K) (c ^ 4)⁻¹ fun _ => 1)

theorem torusFive_castAdd {K : Type} [Field K] (c : K) (m : ℕ) (i : Fin 4) :
    torusFive c m (Fin.castAdd (m + 1) i) = c := by
  simp [torusFive]

theorem torusFive_natAdd_zero {K : Type} [Field K] (c : K) (m : ℕ) :
    torusFive c m (Fin.natAdd 4 0) = (c ^ 4)⁻¹ := by
  simp [torusFive]

theorem torusFive_natAdd_succ {K : Type} [Field K] (c : K) (m : ℕ) (j : Fin m) :
    torusFive c m (Fin.natAdd 4 j.succ) = 1 := by
  simp [torusFive]

theorem prod_torusFive {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ) :
    ∏ i, torusFive c m i = 1 := by
  rw [Fin.prod_univ_add]
  simp [torusFive, Fin.prod_univ_succ, hc]

@[expose] def torusFiveSL {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ) :
    SpecialLinearGroup (Fin (4 + (m + 1))) K :=
  ⟨Matrix.diagonal (torusFive c m), by rw [Matrix.det_diagonal, prod_torusFive hc]⟩

theorem coe_torusFiveSL {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ) :
    (torusFiveSL hc m : Matrix (Fin (4 + (m + 1))) (Fin (4 + (m + 1))) K) =
      Matrix.diagonal (torusFive c m) := rfl

theorem diagonal_torusFive_commute_blockMat {K : Type} [Field K] (c : K) (m : ℕ)
    (A : Matrix (Fin 4) (Fin 4) K) :
    Matrix.diagonal (torusFive c m) * blockMat (m := m + 1) A =
      blockMat (m := m + 1) A * Matrix.diagonal (torusFive c m) := by
  ext a b
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  induction a using Fin.addCases with
  | left i => induction b using Fin.addCases with
    | left j => rw [blockMat_inl_inl, torusFive_castAdd, torusFive_castAdd, mul_comm]
    | right j => simp [blockMat]
  | right i => induction b using Fin.addCases with
    | left j => simp [blockMat]
    | right j =>
      rw [blockMat_inr_inr, Matrix.one_apply]
      split_ifs with hij
      · subst hij
        rw [mul_one, one_mul]
      · simp

theorem commute_torusFiveSL_blockSL {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ) :
    Commute (torusFiveSL hc m) (blockSL (m := m + 1) (phi5SL K)) := by
  show _ * _ = _ * _
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusFiveSL,
    coe_blockSL, coe_phi5SL]
  exact diagonal_torusFive_commute_blockMat c m (phi5Companion K)

private theorem diagonal_mul_one_add_single {K : Type} [Field K] {n : ℕ} (w : Fin n → K)
    {i j : Fin n} (hw : w j ≠ 0) (a : K) :
    Matrix.diagonal w * (1 + Matrix.single i j a) =
      (1 + Matrix.single i j (w i * a * (w j)⁻¹)) * Matrix.diagonal w := by
  rw [mul_add, add_mul, mul_one, one_mul]
  congr 1
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [mul_assoc (w i * a), inv_mul_cancel₀ hw, mul_one]
  · simp

theorem torusFiveSL_mul_transvection {K : Type} [Field K] {c : K} (hc : c ≠ 0) (m : ℕ)
    (hij : (Fin.castAdd (m + 1) 0 : Fin (4 + (m + 1))) ≠ Fin.natAdd 4 0) (a : K) :
    torusFiveSL hc m * SpecialLinearGroup.transvection hij a =
      SpecialLinearGroup.transvection hij (c ^ 5 * a) * torusFiveSL hc m := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_torusFiveSL,
    SpecialLinearGroup.transvection_coe, SpecialLinearGroup.transvection_coe,
    diagonal_mul_one_add_single _
      (by rw [torusFive_natAdd_zero]; exact inv_ne_zero (pow_ne_zero 4 hc)),
    torusFive_castAdd, torusFive_natAdd_zero, inv_inv]
  have : c * a * c ^ 4 = c ^ 5 * a := by ring
  rw [this]

theorem projectiveSL_eq_top_of_subfield_le {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 5 ≤ n) (k : Subfield K) (hK : Nat.card K = Nat.card k ^ 5)
    (h5 : ¬ 5 ∣ Nat.card K - 1) (M : Subgroup (projectiveSL n K))
    (hk : (linearSubfieldInclusion n k).range ≤ M)
    (hcent : ∀ x ∈ M, orderOf x = 5 → ∀ g : projectiveSL n K, Commute g x → g ∈ M) :
    M = ⊤ := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 + (m + 1) := ⟨n - 5, by omega⟩
  have hdk : proj (4 + (m + 1)) K (blockSL (m := m + 1) (phi5SL K)) ∈
      (linearSubfieldInclusion (4 + (m + 1)) k).range :=
    mem_range_linearSubfieldInclusion.mpr ⟨blockSL (m := m + 1) (phi5SL K),
      fun a b => blockMat_mem k (phi5Companion_mem k) a b, rfl⟩
  obtain ⟨c, hc0, hc5⟩ := exists_pow_five_not_mem_of_card k hK h5
  have htM : proj (4 + (m + 1)) K (torusFiveSL hc0 m) ∈ M :=
    hcent _ (hk hdk) (orderOf_proj_blockSL_phi5 (m + 1)) _
      ((commute_torusFiveSL_blockSL hc0 m).map _)
  have hslH : CFSG.RankThree.PartOne.CTP.slSub (4 + (m + 1)) k ≤
      M.comap (proj (4 + (m + 1)) K) := by
    intro g hg
    rw [Subgroup.mem_comap]
    apply hk
    rw [CFSG.RankThree.PartOne.CTP.range_linearSubfieldInclusion_eq_map]
    exact ⟨g, hg, rfl⟩
  have h04 : (Fin.castAdd (m + 1) 0 : Fin (4 + (m + 1))) ≠ Fin.natAdd 4 0 := by
    simp [Fin.ext_iff]
  have hx : SpecialLinearGroup.transvection h04 (c ^ 5) ∈ M.comap (proj (4 + (m + 1)) K) := by
    have hconj : torusFiveSL hc0 m * SpecialLinearGroup.transvection h04 1 *
        (torusFiveSL hc0 m)⁻¹ = SpecialLinearGroup.transvection h04 (c ^ 5) :=
      mul_inv_eq_of_eq_mul (by rw [torusFiveSL_mul_transvection, mul_one])
    rw [← hconj]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htM
      (hslH (CFSG.RankThree.PartOne.CTP.transvection_mem_slSub h04 k.one_mem)))
      (Subgroup.inv_mem _ htM)
  have hH := CFSG.RankThree.PartOne.CTP.eq_top_of_root_not_mem hslH (by omega)
    (by norm_num : Nat.Prime 5) hK hc5 h04 hx
  rw [eq_top_iff]
  intro y _
  obtain ⟨g, rfl⟩ := proj_surjective (4 + (m + 1)) K y
  have hg : g ∈ M.comap (proj (4 + (m + 1)) K) := hH ▸ Subgroup.mem_top g
  exact hg

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
