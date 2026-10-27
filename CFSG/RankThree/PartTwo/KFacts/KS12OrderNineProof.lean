module

public import CFSG.RankThree.PartTwo.KFacts.KS12OrderNine
public import CFSG.RankThree.PartTwo.Sec4.LThreePiFrob
import CFSG.RankThree.PartTwo.KFacts.KS12ClassExp
import CFSG.RankThree.PartTwo.KFacts.K72SLPiElems
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldFour

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Matrix
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace KS12OrderNine

variable {π : Bool} {p f : ℕ} {K : Type} [Field K]

@[expose] def swapNegTwo : GL (Fin 3) K :=
  ⟨!![-1, 0, 0; 0, 0, -1; 0, -1, 0], !![-1, 0, 0; 0, 0, -1; 0, -1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]⟩

theorem coe_swapNegTwo :
    ((swapNegTwo : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = !![-1, 0, 0; 0, 0, -1; 0, -1, 0] :=
  rfl

theorem swapNegTwo_mul_self : (swapNegTwo : GL (Fin 3) K) * swapNegTwo = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_swapNegTwo, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem swapNegTwo_ne_one : (swapNegTwo : GL (Fin 3) K) ≠ 1 := by
  intro h
  have h11 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) h
  simp [coe_swapNegTwo] at h11

theorem swapNegTwo_mem_slPi (hπ : π = false → UnitaryFieldData p f K) :
    swapNegTwo ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((swapNegTwo : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_swapNegTwo, Matrix.det_fin_three]
    simp
  cases π
  · have h := hπ rfl
    rw [mem_slPi_false h]
    refine ⟨hdet, ?_⟩
    rw [coe_swapNegTwo]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]
  · rw [mem_slPi_true]
    exact hdet

theorem swapNegTwo_commute_diagE (e : Kˣ) : swapNegTwo * diagE e = diagE e * swapNegTwo := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_swapNegTwo, coe_diagE]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

theorem diagTau_commute_diagE {τ : K} (hτ : τ ^ 3 = 1) (e : Kˣ) :
    diagTau hτ * diagE e = diagE e * diagTau hτ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagTau_eq_diagonal hτ, coe_diagE,
    diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem diagTau_not_mem_scalars {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1) :
    diagTau hτ ∉ StatedScalars (Fin 3) K :=
  CFSG.RankThree.PartTwo.Sec4.diagTau_not_mem_statedScalars hτ hτ1

theorem exists_commute_of_orderOf_eq_nine (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {v : GL (Fin 3) K} (hv : v ∈ slPi π 3 (p ^ f) K) (hv9 : orderOf v = 9)
    (hv3 : v ^ 3 ∈ StatedScalars (Fin 3) K) :
    (∃ w ∈ slPi π 3 (p ^ f) K, orderOf w = 3 ∧ w ∉ StatedScalars (Fin 3) K ∧ w * v = v * w) ∧
      ∃ t ∈ slPi π 3 (p ^ f) K, orderOf t = 2 ∧ t * v = v * t := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hdet : (v : Matrix (Fin 3) (Fin 3) K).det = 1 := ((mem_slPi_iff hπ).mp hv).2
  have hvH : v ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hv
  obtain ⟨κ, hκ⟩ := hv3
  have hv3ne : v ^ 3 ≠ 1 := by
    intro h
    have h1 := orderOf_dvd_of_pow_eq_one h
    rw [hv9] at h1
    norm_num at h1
  have hκ1 : κ ≠ 1 := by
    rintro rfl
    exact hv3ne (by rw [← hκ, map_one])
  have hvm : (v : Matrix (Fin 3) (Fin 3) K) ^ 3 = (κ : K) • 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hκ, coe_scalar_eq_smul]
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ ^ 3 = κ := by
    by_contra hcon
    push Not at hcon
    have h1 := det_eq_of_cube hcon hvm
    rw [hdet] at h1
    exact hκ1 (Units.ext h1.symm)
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hμ
    exact κ.ne_zero hμ.symm
  have hvμ : v ^ 3 = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 μ hμ0 ^ 3) := by
    rw [← hκ]
    congr 1
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμ]
  have hvs : v ∉ StatedScalars (Fin 3) K := by
    rintro ⟨s, rfl⟩
    apply hv3ne
    have hs3 : (s : K) ^ 3 = 1 := by rw [← det_scalar_three]; exact hdet
    have hs3' : s ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hs3, Units.val_one])
    rw [← map_pow, hs3', map_one]
  obtain ⟨y, ⟨z, hzZ, rfl⟩, g, hg, hD⟩ := exists_diag_normal_form hK hq hτ hτ1 hvH hvs hvμ
  rw [zPi_eq hπ hq' hτ hτ1] at hzZ
  obtain ⟨-, ζ, rfl⟩ := Subgroup.mem_inf.mp hzZ
  have hzc : ∀ h : GL (Fin 3) K, h * GeneralLinearGroup.scalar (Fin 3) ζ =
      GeneralLinearGroup.scalar (Fin 3) ζ * h := fun h => commute_of_mem_statedScalars ⟨ζ, rfl⟩ h
  have hcomm : ∀ x : GL (Fin 3) K, x * (v * GeneralLinearGroup.scalar (Fin 3) ζ) =
      v * GeneralLinearGroup.scalar (Fin 3) ζ * x → x * v = v * x := by
    intro x hx
    have h1 : x * v * GeneralLinearGroup.scalar (Fin 3) ζ =
        v * x * GeneralLinearGroup.scalar (Fin 3) ζ := by
      rw [mul_assoc, hx, mul_assoc, ← hzc x, mul_assoc]
    exact mul_right_cancel h1
  rcases hD with hD | ⟨e, -, hD⟩
  ·
    exfalso
    have hy : v * GeneralLinearGroup.scalar (Fin 3) ζ = g * diagTau hτ * g⁻¹ := by
      rw [← hD]
      group
    have hdetD : ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 :=
      ((mem_slPi_iff hπ).mp (diagTau_mem_slPi hπ hq' hτ)).2
    have hζ3 : (ζ : K) ^ 3 = 1 := by
      have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K).det) hy
      simp only [Units.val_mul, det_mul, hdet, one_mul] at h1
      rw [det_scalar_three] at h1
      rw [h1, mul_right_comm, hdetD, mul_one, ← det_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, det_one]
    have hζ3' : ζ ^ 3 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hζ3, Units.val_one])
    have hy3 : (v * GeneralLinearGroup.scalar (Fin 3) ζ) ^ 3 = 1 := by
      rw [hy, conj_pow, diagTau_pow_three, mul_one, mul_inv_cancel]
    apply hv3ne
    rwa [Commute.mul_pow (hzc v) 3, ← map_pow, hζ3', map_one, mul_one] at hy3
  ·
    have hy : v * GeneralLinearGroup.scalar (Fin 3) ζ = g * diagE e * g⁻¹ := by
      rw [← hD]
      group
    have hconj : ∀ x : GL (Fin 3) K, x * diagE e = diagE e * x →
        (g * x * g⁻¹) * v = v * (g * x * g⁻¹) := by
      intro x hx
      refine hcomm _ ?_
      rw [hy]
      calc g * x * g⁻¹ * (g * diagE e * g⁻¹) = g * (x * diagE e) * g⁻¹ := by group
        _ = g * (diagE e * x) * g⁻¹ := by rw [hx]
        _ = g * diagE e * g⁻¹ * (g * x * g⁻¹) := by group
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨⟨g * diagTau hτ * g⁻¹, conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hq' hτ), ?_, ?_,
      hconj _ (diagTau_commute_diagE hτ e)⟩, g * swapNegTwo * g⁻¹,
      conj_mem_slPi hπ hg (swapNegTwo_mem_slPi hπ), ?_, hconj _ (swapNegTwo_commute_diagE e)⟩
    · refine orderOf_eq_prime (by rw [conj_pow, diagTau_pow_three, mul_one, mul_inv_cancel]) ?_
      intro h1
      apply diagTau_not_mem_scalars hτ hτ1
      have : diagTau hτ = 1 := by
        calc diagTau hτ = g⁻¹ * (g * diagTau hτ * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      rw [this]
      exact Subgroup.one_mem _
    · rintro ⟨s, hs⟩
      apply diagTau_not_mem_scalars hτ hτ1
      refine ⟨s, ?_⟩
      have hsc := commute_of_mem_statedScalars ⟨s, rfl⟩ g⁻¹
      calc GeneralLinearGroup.scalar (Fin 3) s
          = g⁻¹ * GeneralLinearGroup.scalar (Fin 3) s * g := by rw [hsc]; group
        _ = diagTau hτ := by rw [hs]; group
    · refine orderOf_eq_prime ?_ ?_
      · rw [conj_pow, sq, swapNegTwo_mul_self, mul_one, mul_inv_cancel]
      · intro h1
        apply swapNegTwo_ne_one (K := K)
        calc swapNegTwo = g⁻¹ * (g * swapNegTwo * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group

end KS12OrderNine

open KS12OrderNine

theorem orderNine_of_isSLThreePi {X : Type} [Group X] (hX : Sec4.IsSLThreePi X) (v : X)
    (hv9 : orderOf v = 9) (hv3 : v ^ 3 ∈ Subgroup.center X) :
    (∃ w : X, orderOf w = 3 ∧ w ∉ Subgroup.center X ∧ w * v = v * w) ∧
      ∃ t : X, orderOf t = 2 ∧ t * v = v * t := by
  obtain ⟨q, K, _, _, hcase⟩ := hX
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hp⟩
  have hnc : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨π, f, hK, hq, ⟨e⟩⟩ : ∃ (π : Bool) (f : ℕ), PiField π (ringChar K) f K ∧
      ModThree π (ringChar K ^ f) ∧ Nonempty (X ≃* slPi π 3 (ringChar K ^ f) K) := by
    rcases hcase with ⟨hK, hq, ⟨e⟩⟩ | ⟨hK, hq, ⟨e⟩⟩
    · refine ⟨true, n, ⟨hp, n.2, hnc⟩, ?_, ⟨e⟩⟩
      change ringChar K ^ (n : ℕ) % 3 = 1
      rw [← hnc, hK]
      exact hq
    · have hqd : q ∣ ringChar K ^ (n : ℕ) := ⟨q, by rw [← hnc, hK, sq]⟩
      obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hqd
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · rw [h0, pow_zero] at hm
          rw [hm] at hq
          norm_num at hq
        · exact h0
      refine ⟨false, m, ⟨hp, hm1, by rw [hK, hm]; rfl⟩, ?_, ⟨hm ▸ e⟩⟩
      change ringChar K ^ m % 3 = 2
      rw [← hm]
      exact hq
  have hπ : π = false → UnitaryFieldData (ringChar K) f K := fun h => by
    subst h; exact hK.unitary
  have hq' : π = false → ModThree false (ringChar K ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  set S := slPi π 3 (ringChar K ^ f) K
  have hscal : ∀ s : S, s ∈ Subgroup.center S → (s : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K :=
    fun s hs => mem_statedScalars_of_commute hπ hq' hτ hτ1 fun x hx =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hs ⟨x, hx⟩)).symm
  have hv'9 : orderOf ((e v : S) : GL (Fin 3) K) = 9 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hv9]
  have hv'3 : ((e v : S) : GL (Fin 3) K) ^ 3 ∈ StatedScalars (Fin 3) K := by
    have hc := mem_center_of_mulEquiv e hv3
    rw [map_pow] at hc
    have h1 := hscal _ hc
    rwa [Subgroup.coe_pow] at h1
  obtain ⟨⟨w, hwS, hw3, hws, hwv⟩, t, htS, ht2, htv⟩ :=
    exists_commute_of_orderOf_eq_nine hK hq (e v).2 hv'9 hv'3
  have hback : ∀ (x : GL (Fin 3) K) (hx : x ∈ S), x * (e v : S) = (e v : S) * x →
      e.symm ⟨x, hx⟩ * v = v * e.symm ⟨x, hx⟩ := by
    intro x hx hxv
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext hxv
  refine ⟨⟨e.symm ⟨w, hwS⟩, ?_, ?_, hback w hwS hwv⟩, e.symm ⟨t, htS⟩, ?_, hback t htS htv⟩
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hw3]
  · intro hwZ
    apply hws
    have h1 := mem_center_of_mulEquiv e hwZ
    rw [MulEquiv.apply_symm_apply] at h1
    exact hscal _ h1
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, ht2]

theorem ks12OrderNine :
    KS12OrderNine := by
  intro X _ _ _ hX v hv9 hv3
  rcases hX with hSL | hTC
  · exact orderNine_of_isSLThreePi hSL v hv9 hv3
  · exact absurd hv9 (orderOf_ne_nine_of_isTripleCover hTC v)

end CFSG.RankThree.PartTwo.KFacts
