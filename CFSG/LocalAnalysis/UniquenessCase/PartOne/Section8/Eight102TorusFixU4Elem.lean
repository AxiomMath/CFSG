module

public import CFSG.ClassicalGroups.UnitaryFlag.Triangular
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def torusFixElem (h : UnitaryFieldData 2 n K) (μ : Kˣ) : hypSU h 2 0 :=
  mkHypSU h (diagonal (torusEntries h ![μ, μ⁻¹] (1 : Fin 0 → Kˣ)))
    (diagonal_torusEntries_isometry h _ (fun k => k.elim0)) (by
      rw [det_diagonal_torusEntries]
      have hc0 : (μ : K) ≠ 0 := μ.ne_zero
      simp only [torusRatio, Fin.prod_univ_two, Fin.prod_univ_zero, mul_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_inv_eq_inv_val, map_inv₀,
        div_eq_mul_inv]
      field_simp)

theorem coe_torusFixElem (h : UnitaryFieldData 2 n K) (μ : Kˣ) :
    (((torusFixElem h μ : hypSU h 2 0) : GL (HypIndex 2 0) K) :
      Matrix (HypIndex 2 0) (HypIndex 2 0) K) =
      diagonal (torusEntries h ![μ, μ⁻¹] (1 : Fin 0 → Kˣ)) :=
  rfl

theorem orderOf_torusFixElem (h : UnitaryFieldData 2 n K) (μ : Kˣ) :
    orderOf (torusFixElem h μ) = orderOf μ := by
  have hone : torusFixElem h 1 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_torusFixElem, Subgroup.coe_one, Units.val_one, ← diagonal_one]
    congr 1
    funext x
    rcases x with i | k | i
    · fin_cases i <;> simp [torusEntries]
    · exact k.elim0
    · fin_cases i <;> simp [torusEntries]
  have hmul : ∀ μ ν : Kˣ, torusFixElem h (μ * ν) =
      torusFixElem h μ * torusFixElem h ν := by
    intro μ ν
    have hentries : torusEntries h ![μ * ν, (μ * ν)⁻¹] (1 : Fin 0 → Kˣ) =
        torusEntries h ![μ, μ⁻¹] (1 : Fin 0 → Kˣ) *
          torusEntries h ![ν, ν⁻¹] (1 : Fin 0 → Kˣ) := by
      funext x
      rcases x with i | k | i
      · fin_cases i
        · rfl
        · simp [torusEntries, mul_comm]
      · exact k.elim0
      · fin_cases i
        · simp [torusEntries, map_mul, _root_.mul_inv_rev, mul_comm]
        · simp [torusEntries, map_mul, _root_.mul_inv_rev, mul_comm]
    apply Subtype.ext
    apply Units.ext
    rw [coe_torusFixElem, Subgroup.coe_mul, Units.val_mul, coe_torusFixElem, coe_torusFixElem,
      diagonal_mul_diagonal, hentries]
    rfl
  let f : Kˣ →* hypSU h 2 0 :=
    { toFun := torusFixElem h
      map_one' := hone
      map_mul' := hmul }
  have hf : Function.Injective f := by
    intro μ ν hμν
    have h0 := congrArg (fun g : hypSU h 2 0 =>
      (((g : GL (HypIndex 2 0) K) : Matrix (HypIndex 2 0) (HypIndex 2 0) K) (.inl 0) (.inl 0)))
      hμν
    exact Units.ext (by simpa [f, coe_torusFixElem, torusEntries] using h0)
  exact orderOf_injective f hf μ

theorem torusFixElem_mul_comm_of_mem_torusPow (h : UnitaryFieldData 2 n K) (μ : Kˣ) {m : ℕ}
    {s : hypSU h 2 0} (hs : s ∈ Syl3.torusPow h 2 0 m) :
    torusFixElem h μ * s = s * torusFixElem h μ := by
  obtain ⟨a, -, hmat⟩ := Syl3.mem_torusPow.mp hs
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_mul, Units.val_mul, coe_torusFixElem, hmat,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext x
  exact mul_comm _ _

theorem exists_prime_dvd_two_pow_add_one_and_two_pow_sub_one (hn : n ≠ 0) :
    ∃ q m b : ℕ, q.Prime ∧ q ∣ 2 ^ n + 1 ∧ ¬ 3 ∣ m ∧ 2 * n = 3 ^ b * m ∧ q ∣ 2 ^ m - 1 := by
  set n₁ := ordCompl[3] n with hn₁
  set b := n.factorization 3 with hb
  have hnot3 : ¬ 3 ∣ n₁ := Nat.not_dvd_ordCompl Nat.prime_three hn
  have hpow : 2 ^ n₁ + 1 ≠ 1 := by
    have : 0 < 2 ^ n₁ := pow_pos (by norm_num) n₁
    omega
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hpow
  have hdecomp : n = 3 ^ b * n₁ := by
    have h3b : 3 ^ b = ordProj[3] n := by rw [hb]
    rw [h3b, hn₁]
    exact (Nat.ordProj_mul_ordCompl_eq_self n 3).symm
  refine ⟨q, 2 * n₁, b, hq, ?_, ?_, ?_, ?_⟩
  · have hodd : Odd (3 ^ b) := Odd.pow (show Odd (3 : ℕ) by norm_num)
    have hdvd : 2 ^ n₁ + 1 ∣ (2 ^ n₁) ^ 3 ^ b + 1 ^ 3 ^ b :=
      hodd.nat_add_dvd_pow_add_pow (2 ^ n₁) 1
    have hpow2 : (2 ^ n₁) ^ 3 ^ b = 2 ^ n := by
      rw [← pow_mul, mul_comm, hdecomp]
    rw [hpow2, one_pow] at hdvd
    exact dvd_trans hqdvd hdvd
  · intro h3
    rcases (Nat.prime_three.dvd_mul).mp h3 with h | h
    · norm_num at h
    · exact hnot3 h
  · rw [hdecomp]
    ring
  · have hfac : 2 ^ (2 * n₁) - 1 = (2 ^ n₁ + 1) * (2 ^ n₁ - 1) := by
      rw [← sq_tsub_sq (2 ^ n₁) 1, one_pow, mul_comm 2 n₁, pow_mul]
    rw [hfac]
    exact dvd_mul_of_dvd_left hqdvd _

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
