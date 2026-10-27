module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofReeConj
import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.SEITZQ1
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem exists_involution_unitarySU {f : ℕ} {K' : Type} [Field K'] (h : UnitaryFieldData 2 f K') :
    ∃ t : unitarySU 2 f K' 3, t ≠ 1 ∧ t ^ 2 = 1 := by
  have : CharP K' 2 := h.charP
  set P : Matrix (Fin 3) (Fin 3) K' := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hP
  have hdet : P.det = 1 := by
    rw [hP, Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.head_fin_const]
    ring_nf
    exact CharTwo.neg_eq 1
  have hPP : P * P = 1 := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hbar : P.map h.bar = P := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hPT : Pᵀ = P := by
    rw [hP]
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  set A : GL (Fin 3) K' := GeneralLinearGroup.mkOfDetNeZero P (by rw [hdet]; exact one_ne_zero)
    with hA
  have hAP : (A : Matrix (Fin 3) (Fin 3) K') = P := rfl
  have hAu : A ∈ unitarySU 2 f K' 3 := by
    refine (mem_unitarySU_iff h).2 ⟨by rw [hAP, hdet], ?_⟩
    rw [hAP, hbar, hPT, hPP]
  refine ⟨⟨A, hAu⟩, fun h1 => ?_, ?_⟩
  · have h2 : P = 1 := by
      rw [← hAP]
      exact congrArg (fun g : unitarySU 2 f K' 3 => ((g : GL (Fin 3) K') :
        Matrix (Fin 3) (Fin 3) K')) h1
    have h3 := congrFun (congrFun h2 0) 0
    rw [hP] at h3
    simp at h3
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, sq, Subgroup.coe_one, Units.val_one]
    exact hPP


theorem exists_orderThree_commute_involution (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ y t : ReeTag.F4.reeGamma K a, orderOf y = 3 ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ t * y = y * t := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := L) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' := GaloisField 2 (2 * (2 * a + 1))
  have hK' : Nat.card K' = 2 ^ (2 * (2 * a + 1)) := GaloisField.card 2 _ (by omega)
  have h : UnitaryFieldData 2 (2 * a + 1) K' := ⟨Nat.prime_two, by omega, hK'⟩
  have : CharP K' 2 := h.charP
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) K' := Algebra.IsAlgebraic.of_finite (ZMod 2) K'
  let ι : K' →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K') (M := L)).toRingHom
  obtain ⟨ω', hω', hbar⟩ := q1_exists_omega h (odd_two_mul_add_one a)
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  obtain ⟨Ψ, hΨ⟩ := q1_exists_hom D hK hω (q1SUToSL h ι) (q1SUToSL_fixed h ι D.Frq hFr)
  have hj : Function.Injective (q1SUToSL h ι) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι = 1 := by
      rw [← coe_q1SUToSL h ι, hu]
      rfl
    have hm' : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 :=
      Matrix.map_injective ι.injective (hm.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
    exact Subtype.ext (Units.ext hm')
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hΨ u).symm
    rw [hu, map_one, mul_inv_eq_one, mul_eq_left] at h1
    have h2 : q1SUToSL h ι u = 1 :=
      ReeF4Cent2Proof.q1Psi0_injective D.isFrob (by rw [h1, map_one])
    exact hj (by rw [h2, map_one])
  obtain ⟨x₀, hx₀⟩ := ReeF4Cent2Proof.exists_scalar_unitarySU h hω' hbar
  have hx₀c : ∀ u : unitarySU 2 (2 * a + 1) K' 3, u * x₀ = x₀ * u := by
    intro u
    apply Subtype.ext
    apply Units.ext
    change ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') * ((x₀ : GL (Fin 3) K') :
      Matrix (Fin 3) (Fin 3) K') = ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') *
        ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K')
    rw [hx₀]
    exact (Matrix.scalar_commute ω' (fun _ => Commute.all _ _) _).symm
  have hω3 : ω' ^ 3 = 1 := by linear_combination (ω' - 1) * hω'
  have hx₀3 : x₀ ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hx₀, ← map_pow, hω3, map_one,
      Subgroup.coe_one, Units.val_one]
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    have h2 : Matrix.scalar (Fin 3) ω' = 1 := by
      rw [← hx₀, h1]
      rfl
    have h3 : ω' = 1 := by simpa using congrFun (congrFun h2 0) 0
    rw [h3] at hω'
    have h4 : (2 : K') = 0 := CharTwo.two_eq_zero
    have h5 : (1 : K') = 0 := by linear_combination hω' - h4
    exact one_ne_zero h5
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf (Ψ x₀) = 3 := by
    rw [orderOf_injective Ψ hΨinj x₀]
    exact orderOf_eq_prime hx₀3 hx₀1
  obtain ⟨t₀, ht₀1, ht₀2⟩ := exists_involution_unitarySU h
  refine ⟨Ψ x₀, Ψ t₀, hord, fun h1 => ht₀1 (hΨinj (h1.trans (map_one Ψ).symm)), ?_, ?_⟩
  · rw [← map_pow, ht₀2, map_one]
  · rw [← map_mul, hx₀c, map_mul]

theorem exists_involution_commute_of_pow_three (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) (u : ReeTag.F4.reeGamma K a)
    (hu : u ^ 3 = 1) : ∃ v : ReeTag.F4.reeGamma K a, v ≠ 1 ∧ v ^ 2 = 1 ∧ v * u = u * v := by
  obtain ⟨y, t, hy, ht1, ht2, hty⟩ := exists_orderThree_commute_involution a K hK
  by_cases hu1 : u = 1
  · exact ⟨t, ht1, ht2, by rw [hu1, mul_one, one_mul]⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, rfl⟩ := reeGamma_orderThree_conj a K hK y u hy (orderOf_eq_prime hu hu1)
  refine ⟨g * t * g⁻¹, fun h1 => ht1 (conj_eq_one_iff.mp h1), ?_, ?_⟩
  · rw [conj_pow, ht2, mul_one, mul_inv_cancel]
  · calc g * t * g⁻¹ * (g * y * g⁻¹) = g * (t * y) * g⁻¹ := by group
      _ = g * (y * t) * g⁻¹ := by rw [hty]
      _ = g * y * g⁻¹ * (g * t * g⁻¹) := by group

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3Ree
