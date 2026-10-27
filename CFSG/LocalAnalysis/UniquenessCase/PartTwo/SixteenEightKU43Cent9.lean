module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Leaves
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Matrix CFSG.Blueprint

section Linear

variable {K : Type*} [Field K] [CharP K 3]

theorem pow_four_eq_zero_of_pow {N : Matrix (Fin 4) (Fin 4) K} {k : ℕ} (h : N ^ k = 0) :
    N ^ 4 = 0 := by
  set f := Matrix.toLinAlgEquiv' N with hf
  have hfk : f ^ k = 0 := by rw [hf, ← map_pow, h, map_zero]
  have hker : LinearMap.ker (f ^ 4) = ⊤ := by
    rcases Nat.lt_or_ge k 4 with hk | hk
    · have : f ^ 4 = 0 := by
        have h4 : f ^ 4 = f ^ k * f ^ (4 - k) := by rw [← pow_add]; congr 1; omega
        rw [h4, hfk, zero_mul]
      rw [this, LinearMap.ker_zero]
    · have h1 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := f) (m := k)
        (by rw [Module.finrank_fin_fun]; exact hk)
      rw [Module.finrank_fin_fun, hfk, LinearMap.ker_zero] at h1
      exact h1.symm
  have hf4 : f ^ 4 = 0 := LinearMap.ker_eq_top.mp hker
  apply Matrix.toLinAlgEquiv'.injective
  rw [map_pow, ← hf, hf4, map_zero]

theorem pow_nine_eq_scalar_of_commute {N Y : Matrix (Fin 4) (Fin 4) K} (hN4 : N ^ 4 = 0)
    (hN3 : N ^ 3 ≠ 0) (hc : Y * N = N * Y) : ∃ c : K, Y ^ 9 = Matrix.scalar (Fin 4) (c ^ 9) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin 4 → K, N ^ 3 *ᵥ v ≠ 0 := by
    by_contra h
    push Not at h
    apply hN3
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    rw [Matrix.toLin'_apply, h w, map_zero, LinearMap.zero_apply]
  have hNk : ∀ j : ℕ, 4 ≤ j → N ^ j *ᵥ v = 0 := fun j hj => by
    rw [show j = 4 + (j - 4) by omega, pow_add, hN4, zero_mul, zero_mulVec]
  let b : Fin 4 → (Fin 4 → K) := fun k => N ^ (k : ℕ) *ᵥ v
  have hmv : ∀ (i j : ℕ), N ^ i *ᵥ (N ^ j *ᵥ v) = N ^ (i + j) *ᵥ v := fun i j => by
    rw [mulVec_mulVec, pow_add]
  have hli : LinearIndependent K b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    simp only [Fin.sum_univ_four, b] at hg
    have happ : ∀ i : ℕ, g 0 • (N ^ (i + 0) *ᵥ v) + g 1 • (N ^ (i + 1) *ᵥ v) +
        g 2 • (N ^ (i + 2) *ᵥ v) + g 3 • (N ^ (i + 3) *ᵥ v) = 0 := fun i => by
      have := congrArg (fun w => N ^ i *ᵥ w) hg
      have h3v : ((3 : Fin 4) : ℕ) = 3 := rfl
      simpa only [mulVec_add, mulVec_smul, hmv, mulVec_zero, Fin.val_zero, Fin.val_one,
        Fin.val_two, h3v, Fin.isValue] using this
    have h3 := happ 3
    have h2 := happ 2
    have h1 := happ 1
    have h0 := happ 0
    simp only [show 3 + 1 = 4 by rfl, show 3 + 2 = 5 by rfl, show 3 + 3 = 6 by rfl,
      hNk 4 le_rfl, hNk 5 (by norm_num), hNk 6 (by norm_num), smul_zero, add_zero] at h3
    have g0 : g 0 = 0 := (smul_eq_zero.mp h3).resolve_right hv
    simp only [g0, zero_smul, zero_add, show 2 + 1 = 3 by rfl, show 2 + 2 = 4 by rfl,
      show 2 + 3 = 5 by rfl, hNk 4 le_rfl, hNk 5 (by norm_num), smul_zero, add_zero] at h2
    have g1 : g 1 = 0 := (smul_eq_zero.mp h2).resolve_right hv
    simp only [g0, g1, zero_smul, zero_add, show 1 + 2 = 3 by rfl, show 1 + 3 = 4 by rfl,
      hNk 4 le_rfl, smul_zero, add_zero] at h1
    have g2 : g 2 = 0 := (smul_eq_zero.mp h1).resolve_right hv
    simp only [g0, g1, g2, zero_smul, zero_add, show 0 + 3 = 3 by rfl] at h0
    have g3 : g 3 = 0 := (smul_eq_zero.mp h0).resolve_right hv
    intro i
    fin_cases i <;> assumption
  have hspan : Submodule.span K (Set.range b) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  obtain ⟨c, hcY⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (hspan ▸ Submodule.mem_top : Y *ᵥ v ∈ Submodule.span K (Set.range b))
  set P : Matrix (Fin 4) (Fin 4) K :=
    c 0 • 1 + c 1 • N + c 2 • N ^ 2 + c 3 • N ^ 3 with hP
  have hPN : P * N = N * P := by
    simp only [hP, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      ← pow_succ, ← pow_succ']
  have hYk : ∀ k : ℕ, Y * N ^ k = N ^ k * Y := fun k =>
    ((Commute.pow_right (show Commute Y N from hc) k)).eq
  have hPk : ∀ k : ℕ, P * N ^ k = N ^ k * P := fun k =>
    ((Commute.pow_right (show Commute P N from hPN) k)).eq
  have hPv : P *ᵥ v = Y *ᵥ v := by
    rw [← hcY]
    simp only [hP, Fin.sum_univ_four, b, add_mulVec, smul_mulVec, one_mulVec, pow_one,
      Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, Fin.isValue]
    rfl
  have hYP : Y = P := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan (fun k => ?_)
    simp only [Matrix.toLin'_apply, b]
    calc Y *ᵥ (N ^ (k : ℕ) *ᵥ v) = N ^ (k : ℕ) *ᵥ (Y *ᵥ v) := by
          rw [mulVec_mulVec, hYk, ← mulVec_mulVec]
      _ = N ^ (k : ℕ) *ᵥ (P *ᵥ v) := by rw [hPv]
      _ = P *ᵥ (N ^ (k : ℕ) *ᵥ v) := by rw [mulVec_mulVec, ← hPk, ← mulVec_mulVec]
  set M : Matrix (Fin 4) (Fin 4) K := c 1 • N + c 2 • N ^ 2 + c 3 • N ^ 3 with hM
  have hYM : Y = Matrix.scalar (Fin 4) (c 0) + M := by
    rw [hYP, hP, hM, Matrix.scalar_apply, ← smul_one_eq_diagonal]; abel
  set Q : Matrix (Fin 4) (Fin 4) K := c 1 • 1 + c 2 • N + c 3 • N ^ 2 with hQ
  have hMQ : M = N * Q := by
    rw [hM, hQ]
    simp only [mul_add, mul_smul_comm, mul_one]
    rw [show N * N = N ^ 2 by rw [sq], show N * N ^ 2 = N ^ 3 by rw [pow_succ' N 2]]
  have hQN : Commute N Q := by
    show N * Q = Q * N
    simp only [hQ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      ← pow_succ, ← pow_succ']
  have hM4 : M ^ 4 = 0 := by rw [hMQ, hQN.mul_pow, hN4, zero_mul]
  have hM9 : M ^ (3 ^ 2) = 0 := by
    rw [show 3 ^ 2 = 4 + 5 by norm_num, pow_add, hM4, zero_mul]
  refine ⟨c 0, ?_⟩
  have hcomm : Commute (Matrix.scalar (Fin 4) (c 0)) M :=
    Matrix.scalar_commute _ (fun _ => Commute.all _ _) M
  rw [hYM, show (9 : ℕ) = 3 ^ 2 by norm_num, add_pow_char_pow_of_commute (p := 3) (n := _) hcomm,
    hM9, add_zero, ← map_pow]

end Linear

section U43

open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.A318P (projSU_of_statedClassicalModel_gen)
open CFSG.RankThree.PartTwo.Sec4.Item426 (pow_mul_four_eq_one)

theorem pow_nine_of_mem_centralizer_projSU (g : projSU 4 3 1) (hg : orderOf g = 9)
    (y : projSU 4 3 1) (hy : y ∈ Subgroup.centralizer ({g} : Set (projSU 4 3 1))) :
    y ^ 9 = 1 := by
  set K := GaloisField 3 (2 * 1) with hKdef
  have hU : UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩
  have : CharP K 3 := hU.charP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hlift : ∀ z : projSU 4 3 1, ∃ Z : GL (Fin 4) K, Z ∈ unitarySU 3 1 K 4 ∧
      ProjGenLinGroup.mk Z = (z : ProjGenLinGroup (Fin 4) K) := fun z =>
    Subgroup.mem_map.mp
      ((SetLike.ext_iff.mp (CFSG.RankThree.PartTwo.Sec4.projSU_eq_map_statedSU 4 3 1) _).mp z.2)
  obtain ⟨X, hX, hXg⟩ := hlift g
  obtain ⟨Y, hY, hYy⟩ := hlift y
  have hXdet := ((mem_unitarySU_iff hU).mp hX).1
  have hg9 : (g : ProjGenLinGroup (Fin 4) K) ^ 9 = 1 := by
    have h := pow_orderOf_eq_one g
    rw [hg] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hX36 : X ^ (9 * 4) = 1 := pow_mul_four_eq_one hXdet (by rw [hXg, hg9])
  set B := X ^ 28 with hB
  have hB9 : B ^ 9 = 1 := by
    rw [hB, ← pow_mul, show 28 * 9 = (9 * 4) * 7 by norm_num, pow_mul, hX36, one_pow]
  have hBg : ProjGenLinGroup.mk B = (g : ProjGenLinGroup (Fin 4) K) := by
    rw [hB, map_pow, hXg, show 28 = 9 * 3 + 1 by norm_num, pow_succ, pow_mul, hg9, one_pow,
      one_mul]
  have hBdet : Matrix.GeneralLinearGroup.det B = 1 := by
    rw [hB, map_pow]
    have : Matrix.GeneralLinearGroup.det X = 1 := Units.ext (by simpa using hXdet)
    rw [this, one_pow]
  have hyg : y * g = g * y := (Subgroup.mem_centralizer_iff.mp hy g (Set.mem_singleton g)).symm
  have hcomm : Y * B = B * Y := by
    have hmk : ProjGenLinGroup.mk (B * Y) = ProjGenLinGroup.mk (Y * B) := by
      rw [map_mul, map_mul, hBg, hYy]
      exact_mod_cast hyg.symm
    obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hmk
    set s := Matrix.GeneralLinearGroup.scalar (Fin 4) u with hs
    have hsc : ∀ h : GL (Fin 4) K, h * s = s * h := fun h => by
      have : s ∈ Subgroup.center (GL (Fin 4) K) := by
        rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
        exact ⟨u, rfl⟩
      exact (Subgroup.mem_center_iff.mp this h)
    have hC : Y⁻¹ * B * Y * s = B := by
      calc Y⁻¹ * B * Y * s = Y⁻¹ * (B * Y * s) := by group
        _ = B := by rw [hu]; group
    have hu9 : u ^ 9 = 1 := by
      have h1 : (Y⁻¹ * B * Y * s) ^ 9 = (Y⁻¹ * B * Y) ^ 9 * s ^ 9 :=
        Commute.mul_pow (hsc _) 9
      have h2 : (Y⁻¹ * B * Y) ^ 9 = 1 := by
        rw [show Y⁻¹ * B * Y = MulAut.conj Y⁻¹ B by simp, ← map_pow, hB9, map_one]
      rw [hC, hB9, h2, one_mul] at h1
      have h4 : Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ 9) = 1 := by
        rw [map_pow, ← hs, ← h1]
      have h3 := congrArg (fun h : GL (Fin 4) K => (h : Matrix (Fin 4) (Fin 4) K) 0 0) h4
      exact Units.ext (by simpa [Matrix.diagonal_pow] using h3)
    have hu4 : u ^ 4 = 1 := by
      have h1 := congrArg Matrix.GeneralLinearGroup.det hC
      rw [map_mul, map_mul, map_mul, hBdet, hs, Matrix.GeneralLinearGroup.det_scalar,
        Fintype.card_fin, map_inv] at h1
      have h2 : Matrix.GeneralLinearGroup.det Y⁻¹ * Matrix.GeneralLinearGroup.det Y = 1 := by
        rw [← map_mul, inv_mul_cancel, map_one]
      calc u ^ 4 = (Matrix.GeneralLinearGroup.det Y)⁻¹ * 1 *
            Matrix.GeneralLinearGroup.det Y * u ^ 4 := by group
        _ = 1 := h1
    have hu1 : u = 1 := by
      calc u = u ^ 9 * ((u ^ 4) ^ 2)⁻¹ := by group
        _ = 1 := by rw [hu9, hu4, one_pow, inv_one, one_mul]
    rw [← hu, hs, hu1, map_one]
    exact mul_one _
  set Nm : Matrix (Fin 4) (Fin 4) K := (B : Matrix (Fin 4) (Fin 4) K) - 1 with hNm
  have hc1 : Commute (B : Matrix (Fin 4) (Fin 4) K) 1 := Commute.one_right _
  have hBm9 : (B : Matrix (Fin 4) (Fin 4) K) ^ 9 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hB9, Units.val_one]
  have hN9 : Nm ^ (3 ^ 2) = 0 := by
    rw [hNm, sub_pow_char_pow_of_commute (p := 3) (n := _) hc1, one_pow,
      show 3 ^ 2 = 9 by norm_num, hBm9, sub_self]
  have hN4 : Nm ^ 4 = 0 := pow_four_eq_zero_of_pow hN9
  have hN3 : Nm ^ 3 ≠ 0 := by
    intro h3
    have h3' : Nm ^ (3 ^ 1) = 0 := by simpa using h3
    rw [hNm, sub_pow_char_pow_of_commute (p := 3) (n := _) hc1, one_pow, pow_one,
      sub_eq_zero] at h3'
    have hB3 : B ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h3', Units.val_one])
    have hg3 : g ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hBg, ← map_pow, hB3, map_one, OneMemClass.coe_one]
    have := orderOf_dvd_of_pow_eq_one hg3
    rw [hg] at this
    norm_num at this
  have hYN : (Y : Matrix (Fin 4) (Fin 4) K) * Nm = Nm * Y := by
    have hm : (Y : Matrix (Fin 4) (Fin 4) K) * B = B * Y := by
      rw [← Units.val_mul, ← Units.val_mul, hcomm]
    rw [hNm, Matrix.mul_sub, Matrix.sub_mul, hm, Matrix.mul_one, Matrix.one_mul]
  obtain ⟨c, hc⟩ := pow_nine_eq_scalar_of_commute hN4 hN3 hYN
  have hc0 : c ^ 9 ≠ 0 := by
    intro h0
    have hdet := congrArg Matrix.det hc
    rw [h0, map_zero, Matrix.det_zero, ← Units.val_pow_eq_pow_val] at hdet
    exact (Matrix.GeneralLinearGroup.det (Y ^ 9)).ne_zero (by simpa using hdet)
  have hY9 : Y ^ 9 = Matrix.GeneralLinearGroup.scalar (Fin 4) (Units.mk0 _ hc0) := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hc]
    rfl
  apply Subtype.ext
  rw [Subgroup.coe_pow, ← hYy, ← map_pow, hY9, OneMemClass.coe_one, ProjGenLinGroup.mk_eq_one,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨_, rfl⟩

theorem u43Cent9 : U43Cent9Statement := by
  unfold U43Cent9Statement
  intro S _ _ hS g hg
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := projSU_of_statedClassicalModel_gen (hS.statedClassicalModel (by decide))
  intro y
  refine ⟨2, ?_⟩
  have hy : e (y : S) ∈ Subgroup.centralizer ({e g} : Set (projSU 4 3 1)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp y.2
    rw [← map_mul, ← map_mul, this]
  have h9 := pow_nine_of_mem_centralizer_projSU (e g) (by rw [MulEquiv.orderOf_eq]; exact hg) _ hy
  apply Subtype.ext
  rw [Subgroup.coe_pow, OneMemClass.coe_one, show 3 ^ 2 = 9 by norm_num]
  apply e.injective
  rw [map_pow, h9, map_one]

end U43

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

