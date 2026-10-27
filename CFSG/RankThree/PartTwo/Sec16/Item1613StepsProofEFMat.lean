module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.Assembly.GL83LieDefs
import CFSG.RankThree.PartTwo.Sec4.LThreePiRank

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1615EF

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix

variable {K : Type} [Field K]

theorem diagE_conj_cycThree {τ : K} (hτ : τ ^ 3 = 1) (ε : Kˣ) (hε : (ε : K) = τ) :
    diagE ε * cycThree * (diagE ε)⁻¹ = diagTau hτ * cycThree := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ
    exact zero_ne_one hτ
  have hτ2 : τ⁻¹ = τ ^ 2 :=
    (eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hτ)).symm
  apply Units.ext
  have hinv : (((diagE ε)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![τ⁻¹, 1, 1] := by
    rw [diagE]
    change Matrix.diagonal ![((ε⁻¹ : Kˣ) : K), ((1⁻¹ : Kˣ) : K), ((1⁻¹ : Kˣ) : K)] = _
    rw [Units.val_inv_eq_inv_val, hε]
    simp
  rw [Units.val_mul, Units.val_mul, Units.val_mul, hinv, coe_diagE, coe_cycThree, coe_diagTau,
    hε]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply, hτ2]

theorem diagE_comm_diagTau {τ : K} (hτ : τ ^ 3 = 1) (ε : Kˣ) :
    diagE ε * diagTau hτ = diagTau hτ * diagE ε := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagE, coe_diagTau_eq_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm]

theorem diagTau_eq_diagUnits {τ : K} (hτ : τ ^ 3 = 1) (ε : Kˣ) (hε : (ε : K) = τ) :
    diagTau hτ = diagUnits ε (ε ^ 2) 1 := by
  apply Units.ext
  rw [coe_diagTau_eq_diagonal, coe_diagUnits]
  congr 1
  funext i
  fin_cases i <;> simp [hε]

theorem diagTau_pow_mul_diagE_pow {τ : K} (hτ : τ ^ 3 = 1) (ε : Kˣ) (hε : (ε : K) = τ)
    (j k : ℕ) :
    diagTau hτ ^ j * diagE ε ^ k = diagUnits (ε ^ (j + k)) (ε ^ (2 * j)) 1 := by
  have hpow : ∀ (a b c : Kˣ) (n : ℕ), diagUnits a b c ^ n = diagUnits (a ^ n) (b ^ n) (c ^ n) := by
    intro a b c n
    induction n with
    | zero =>
      apply Units.ext
      rw [pow_zero, pow_zero, pow_zero, pow_zero, Units.val_one, coe_diagUnits]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp
    | succ n ih => rw [pow_succ, ih, diagUnits_mul, pow_succ, pow_succ, pow_succ]
  rw [diagTau_eq_diagUnits hτ ε hε, diagE, hpow, hpow, diagUnits_mul]
  simp only [one_pow, mul_one, ← pow_add, ← pow_mul]

theorem exists_eq_diagTau_pow_mul_diagE_pow {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) (ε : Kˣ)
    (hε : (ε : K) = τ) {u v : Kˣ} (hu : (u : K) ^ 3 = 1) (hv : (v : K) ^ 3 = 1) :
    ∃ j k : ℕ, diagUnits u v 1 = diagTau hτ ^ j * diagE ε ^ k := by
  have hε3 : ε ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hε, hτ, Units.val_one])
  have key : ∀ w : Kˣ, (w : K) ^ 3 = 1 → w = 1 ∨ w = ε ∨ w = ε ^ 2 := by
    intro w hw
    rcases cube_root_cases hτ hτ1 hw with h | h | h
    · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
    · exact Or.inr (Or.inl (Units.ext (by rw [h, hε])))
    · exact Or.inr (Or.inr (Units.ext (by rw [h, Units.val_pow_eq_pow_val, hε])))
  have e4 : ε ^ 4 = ε := by rw [show 4 = 3 + 1 by norm_num, pow_add, hε3, one_mul, pow_one]
  have e5 : ε ^ 5 = ε ^ 2 := by rw [show 5 = 3 + 2 by norm_num, pow_add, hε3, one_mul]
  have e6 : ε ^ 6 = 1 := by rw [show 6 = 3 * 2 by norm_num, pow_mul, hε3, one_pow]
  have e3 : ε ^ 3 = 1 := hε3
  have e2 : ε ^ 2 = ε ^ 2 := rfl
  simp only [diagTau_pow_mul_diagE_pow hτ ε hε]
  rcases key v hv with hv' | hv' | hv' <;> rcases key u hu with hu' | hu' | hu' <;>
    rw [hu', hv']
  · exact ⟨0, 0, by simp⟩
  · exact ⟨0, 1, by simp⟩
  · exact ⟨0, 2, by simp⟩
  · exact ⟨2, 1, by norm_num [e3, e4]⟩
  · exact ⟨2, 2, by norm_num [e3, e4]⟩
  · exact ⟨2, 0, by norm_num [e3, e4]⟩
  · exact ⟨1, 2, by norm_num [e3, e4]⟩
  · exact ⟨1, 0, by norm_num [e3, e4]⟩
  · exact ⟨1, 1, by norm_num [e3, e4]⟩

theorem diagUnits_eq_scalar_mul (a b c : Kˣ) :
    diagUnits a b c = GeneralLinearGroup.scalar (Fin 3) c * diagUnits (a * c⁻¹) (b * c⁻¹) 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_scalar_eq_smul, Matrix.smul_mul, Matrix.one_mul, coe_diagUnits,
    coe_diagUnits, ← Matrix.diagonal_smul]
  congr 1
  funext i
  fin_cases i <;> simp [mul_comm (c : K)]

theorem diagTau_mem_stdTypeC {τ : K} (hτ : τ ^ 3 = 1) (ε : Kˣ) (hε : (ε : K) = τ) :
    diagTau hτ ∈ stdTypeC K := by
  have hε3 : ε ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hε, hτ, Units.val_one])
  refine ⟨(ε, ε ^ 2, 1), ⟨?_, ?_, ?_⟩, (diagTau_eq_diagUnits hτ ε hε).symm⟩
  · exact (mem_rootsOfUnity 3 ε).mpr hε3
  · exact (mem_rootsOfUnity 3 _).mpr (by rw [← pow_mul, mul_comm, pow_mul, hε3, one_pow])
  · exact one_mem _

theorem diagE_mem_stdTypeC {ε : Kˣ} (hε3 : ε ^ 3 = 1) : diagE ε ∈ stdTypeC K :=
  ⟨(ε, 1, 1), ⟨(mem_rootsOfUnity 3 ε).mpr hε3, one_mem _, one_mem _⟩, rfl⟩

theorem isTypeC_map_conj {π : Bool} {q : ℕ} {D : Subgroup (GL (Fin 3) K)}
    (hD : IsTypeC π q K D) {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 q K) :
    IsTypeC π q K (D.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hDH, hD3, hDcard, b, hb, hDb⟩ := hD
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact mul_mem (mul_mem hg (hDH ha)) (inv_mem hg)
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨κ, hκ⟩ := hD3 a ha
    refine ⟨κ, ?_⟩
    change GeneralLinearGroup.scalar (Fin 3) κ = (g * a * g⁻¹) ^ 3
    rw [show g * a * g⁻¹ = MulAut.conj g a from rfl, ← map_pow, ← hκ, MulAut.conj_apply,
      (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar κ g).eq, mul_inv_cancel_right]
  · set mk := QuotientGroup.mk' (StatedScalars (Fin 3) K) with hmk
    have hcomm : (D.map (MulAut.conj g).toMonoidHom).map mk =
        (D.map mk).map (MulAut.conj (mk g)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hcomm, Subgroup.card_map_of_injective (MulAut.conj (mk g)).injective]
    exact hDcard
  · refine ⟨fun i => (g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i, ?_, ?_⟩
    · have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
        intro v w hvw
        have := congrArg (Matrix.toLin' ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hvw
        simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using this
      exact hb.map' (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K))
        (LinearMap.ker_eq_bot.mpr hinj)
    · rintro _ ⟨a, ha, rfl⟩ i
      obtain ⟨c, hc⟩ := hDb a ha i
      refine ⟨c, ?_⟩
      change ((g * a * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i) = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ b i)
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, show g * a * g⁻¹ * g = g * a by group,
        Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul]

end CFSG.RankThree.PartTwo.Sec16.Proof1615EF
