module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.LocalAnalysis.ComponentInitial
  Matrix

private theorem exists_orderOf_eq_four_of_lmodel {π : Bool} {p f : ℕ} {K : Type} [Field K]
    {T : Type} [Group T] (M : KS1424.LModel π p f K T) (g : GL (Fin 3) K)
    (hg : g ∈ Sec4.slPi π 3 (p ^ f) K) (h4 : g ^ 4 = 1)
    (h2 : ∀ c : K, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ scalar (Fin 3) c) :
    ∃ t : T, orderOf t = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set F : ↥(Sec4.slPi π 3 (p ^ f) K) := ⟨g, hg⟩ with hF
  have hF4 : F ^ 4 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, hF]
    simpa using congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) h4
  have hnot : ¬ (M.μ F) ^ 2 ^ 1 = 1 := by
    intro h
    rw [pow_one, ← map_pow] at h
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp ((M.ker_iff (F ^ 2)).mp h)
    refine h2 (u : K) ?_
    have hF2 : (((F ^ 2 : ↥(Sec4.slPi π 3 (p ^ f) K)) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Subgroup.coe_pow, hF]
    rw [← hF2, ← hu]
    exact Matrix.GeneralLinearGroup.coe_scalar u
  have hfin : (M.μ F) ^ 2 ^ (1 + 1) = 1 := by
    rw [← map_pow]
    show M.μ (F ^ (2 ^ 2)) = 1
    rw [show 2 ^ 2 = 4 by norm_num, hF4, map_one]
  exact ⟨M.μ F, by simpa using orderOf_eq_prime_pow hnot hfin⟩

private theorem exists_orderOf_eq_four_of_projSL {S : Type} [Group S] {r f : ℕ} [Fact r.Prime]
    (φ : S ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField r f)) :
    ∃ s : S, orderOf s = 4 := by
  let K := GaloisField r f
  let A : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 1; 0, 0, 1]
  have hdet : A.det = 1 := by simp [A, det_fin_three]
  let g : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
  have hgA : (g : Matrix (Fin 3) (Fin 3) K) = A := Matrix.GeneralLinearGroup.val_mkOfDetNeZero A _
  have hg2 : ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(-1 : K), 0, 1; 0, -1, 1; 0, 0, 1] := by
    rw [Units.val_pow_eq_pow_val, hgA, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_three]
  have h4 : g ^ 4 = 1 := by
    apply Units.ext
    rw [show g ^ 4 = (g ^ 2) ^ 2 by group, Units.val_pow_eq_pow_val, hg2, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> ring
  have h2 : ∀ c : K, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ scalar (Fin 3) c := by
    intro c h
    have h02 := congrFun (congrFun h 0) 2
    rw [hg2] at h02
    simp [scalar_apply, show (0 : Fin 3) ≠ 2 by decide] at h02
  have hg : g ∈ Sec4.slPi true 3 (r ^ f) K := by
    rw [Sec4.mem_slPi_true, hgA, hdet]
  exact exists_orderOf_eq_four_of_lmodel
    (KS1424.LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage (r ^ f) K))))
    g hg h4 h2

private theorem exists_orderOf_eq_four_of_projSU_odd {S : Type} [Group S] {r f : ℕ}
    [Fact r.Prime] (hr : r ≠ 2) (hf : 1 ≤ f)
    (φ : S ≃* CFSG.Assembly.RankThreeEven.projSU 3 r f) : ∃ s : S, orderOf s = 4 := by
  let K := GaloisField r (2 * f)
  have hUF : UnitaryFieldData r f K := ⟨Fact.out, hf, GaloisField.card r (2 * f) (by omega)⟩
  haveI : CharP K r := hUF.charP
  have hneg : (-1 : K) ≠ 1 := by
    haveI : Fact (2 < r) := ⟨by have := (Fact.out : r.Prime).two_le; omega⟩
    exact CharP.neg_one_ne_one K r
  let A : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]
  have hdet : A.det = 1 := by simp [A, det_fin_three]
  let g : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
  have hgA : (g : Matrix (Fin 3) (Fin 3) K) = A := Matrix.GeneralLinearGroup.val_mkOfDetNeZero A _
  have hg2 : ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![(-1 : K), 0, 0; 0, -1, 0; 0, 0, 1] := by
    rw [Units.val_pow_eq_pow_val, hgA, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_three]
  have h4 : g ^ 4 = 1 := by
    apply Units.ext
    rw [show g ^ 4 = (g ^ 2) ^ 2 by group, Units.val_pow_eq_pow_val, hg2, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three] <;> ring
  have h2 : ∀ c : K, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ scalar (Fin 3) c := by
    intro c h
    have h00 := congrFun (congrFun h 0) 0
    have h22 := congrFun (congrFun h 2) 2
    rw [hg2] at h00 h22
    simp [scalar_apply] at h00 h22
    exact hneg (h00.trans h22.symm)
  have hmap : A.map hUF.bar = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.map_apply]
  have hunit : ((g : Matrix (Fin 3) (Fin 3) K).map hUF.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hgA, hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, mul_apply, Fin.sum_univ_three, one_apply] <;> ring
  have hg : g ∈ Sec4.slPi false 3 (r ^ f) K := by
    rw [Sec4.mem_slPi_false hUF]
    exact ⟨by rw [hgA, hdet], hunit⟩
  exact exists_orderOf_eq_four_of_lmodel
    (KS1424.LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage r f))))
    g hg h4 h2

private theorem det_charTwo {K : Type} [Field K] (h2 : (2 : K) = 0) (s : K) :
    (!![s, s + 1, 1; s + 1, s, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [det_fin_three]
  simp [vecHead, vecTail]
  linear_combination (-s) * h2

private theorem sq_charTwo {K : Type} [Field K] (h2 : (2 : K) = 0) (s : K) :
    (!![s, s + 1, 1; s + 1, s, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) K) *
      !![s, s + 1, 1; s + 1, s, 1; 1, 1, 1] = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
  · linear_combination (s ^ 2 + s + 1) * h2
  · linear_combination (s ^ 2 + s) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s ^ 2 + s) * h2
  · linear_combination (s ^ 2 + s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination h2

private theorem unitary_charTwo {K : Type} [Field K] (h2 : (2 : K) = 0) (s : K) :
    (!![s + 1, s, 1; s, s + 1, 1; 1, 1, 1] : Matrix (Fin 3) (Fin 3) K)ᵀ *
      !![s, s + 1, 1; s + 1, s, 1; 1, 1, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, one_apply]
  · linear_combination (s ^ 2 + s) * h2
  · linear_combination (s ^ 2 + s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s ^ 2 + s + 1) * h2
  · linear_combination (s ^ 2 + s) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination (s + 1) * h2
  · linear_combination h2

private theorem exists_orderOf_eq_four_of_projSU_two {S : Type} [Group S] {f : ℕ} [Fact (2 : ℕ).Prime]
    (hf : 1 ≤ f) (φ : S ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 f) :
    ∃ s : S, orderOf s = 4 := by
  let K := GaloisField 2 (2 * f)
  have hUF : UnitaryFieldData 2 f K := ⟨Nat.prime_two, hf, GaloisField.card 2 (2 * f) (by omega)⟩
  haveI : CharP K 2 := hUF.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  obtain ⟨s, hs⟩ := hUF.traceLin_surjective (1 : hUF.fixedField)
  have htrace : s + hUF.bar s = 1 := by
    simpa [UnitaryFieldData.coe_traceLin, UnitaryFieldData.trace] using congrArg Subtype.val hs
  have hbs : hUF.bar s = s + 1 := by linear_combination htrace - s * h2
  have hbs1 : hUF.bar (s + 1) = s := by
    rw [map_add, hbs, map_one]
    linear_combination h2
  let A : Matrix (Fin 3) (Fin 3) K := !![s, s + 1, 1; s + 1, s, 1; 1, 1, 1]
  have hdet : A.det = 1 := det_charTwo h2 s
  let g : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero A (by rw [hdet]; exact one_ne_zero)
  have hgA : (g : Matrix (Fin 3) (Fin 3) K) = A := Matrix.GeneralLinearGroup.val_mkOfDetNeZero A _
  have hg2 : ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] := by
    rw [Units.val_pow_eq_pow_val, hgA, pow_two]
    exact sq_charTwo h2 s
  have h4 : g ^ 4 = 1 := by
    apply Units.ext
    rw [show g ^ 4 = (g ^ 2) ^ 2 by group, Units.val_pow_eq_pow_val, hg2, pow_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three]
  have h2ns : ∀ c : K, ((g ^ 2 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
      scalar (Fin 3) c := by
    intro c h
    have h01 := congrFun (congrFun h 0) 1
    rw [hg2] at h01
    simp [scalar_apply, show (0 : Fin 3) ≠ 1 by decide] at h01
  have hmap : A.map hUF.bar = !![s + 1, s, 1; s, s + 1, 1; 1, 1, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, Matrix.map_apply, hbs, hbs1]
  have hunit : ((g : Matrix (Fin 3) (Fin 3) K).map hUF.bar)ᵀ * (g : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [hgA, hmap]
    exact unitary_charTwo h2 s
  have hg : g ∈ Sec4.slPi false 3 (2 ^ f) K := by
    rw [Sec4.mem_slPi_false hUF]
    exact ⟨by rw [hgA, hdet], hunit⟩
  exact exists_orderOf_eq_four_of_lmodel
    (KS1424.LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage 2 f))))
    g hg h4 h2ns

theorem exists_orderOf_eq_four_of_isLThreeEpsAt {S : Type} [Group S] {r f : ℕ} [Fact r.Prime]
    (h : IsLThreeEpsAt S r f) : ∃ s : S, orderOf s = 4 := by
  rcases h with h | ⟨hq, ⟨φ⟩⟩
  · obtain ⟨φ⟩ := h
    exact exists_orderOf_eq_four_of_projSL φ
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at hq
      · exact hf
    by_cases hr : r = 2
    · subst hr
      exact exists_orderOf_eq_four_of_projSU_two hf φ
    · exact exists_orderOf_eq_four_of_projSU_odd hr hf φ

end CFSG.RankThree.PartTwo.Sec15
