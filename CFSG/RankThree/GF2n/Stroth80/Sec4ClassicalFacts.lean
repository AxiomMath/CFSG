module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Classical
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SteinbergCDEvenClassicalOrderFour
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalHighWitt

public section

namespace CFSG.RankThree.GF2n.Stroth80

section Sylow

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank

theorem omegaMinusFourSylowStatement_holds : OmegaMinusFourSylowStatement := by
  intro K _ _ _ hq4 b c hirr P
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hqm : Nat.card K = 2 ^ (m : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hm
  have hm0 : (m : ℕ) ≠ 0 := by
    rintro h0
    rw [h0, pow_zero] at hqm
    omega
  have hq2 : 2 ∣ Nat.card K := by
    rw [hqm]
    exact dvd_pow_self 2 hm0
  have hqpos : 0 < Nat.card K := by omega
  have hN0 : Nat.card K ^ 2 ≠ 0 := pow_ne_zero 2 (by omega)
  have hsq : 2 ∣ Nat.card K ^ 2 := dvd_pow hq2 two_ne_zero
  have hsq2 : 2 ∣ (Nat.card K ^ 2) ^ 2 := dvd_pow hsq two_ne_zero
  have hbig : 256 ≤ (Nat.card K ^ 2) ^ 2 := by
    have h1 : 4 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hq4 2
    have h2 : (4 ^ 2) ^ 2 ≤ (Nat.card K ^ 2) ^ 2 := Nat.pow_le_pow_left h1 2
    have h3 : (4 ^ 2) ^ 2 = 256 := by norm_num
    rw [h3] at h2
    exact h2
  have hodd : ¬ 2 ∣ (Nat.card K ^ 2) ^ 2 - 1 := by omega
  have hne : (Nat.card K ^ 2) ^ 2 - 1 ≠ 0 := by omega
  haveI : Finite ↥(StatedOmega (StatedQuadMinus 2 K b c)) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
        CFSG.SeitzReduction.F4Pilot.ordSL_two]
      exact Nat.mul_ne_zero hN0 hne)
  have key : Nat.factorization (Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1)) 2 = m * 2 := by
    rw [Nat.factorization_mul hN0 hne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hodd, add_zero, hqm, ← pow_mul,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  rw [Sylow.card_eq_multiplicity P,
    CFSG.SeitzReduction.F4Pilot.natCard_statedOmega_quadMinus_two hirr,
    CFSG.SeitzReduction.F4Pilot.ordSL_two, key, hqm, ← pow_mul]

end Sylow

section ClassicalOrderFour

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank

private theorem sp_orderOf_four (K : Type) [Field K] [CharP K 2] (m : ℕ) (hm : 2 ≤ m) :
    ∃ g : ↥(StatedSp m K), orderOf g = 4 := by
  obtain ⟨g, hg, -⟩ := CFSG.LocalAnalysis.SteinbergCD.exists_orderOf_eq_four_statedSp
    (k := K) CharTwo.two_eq_zero hm
  exact ⟨g, hg⟩

private theorem omegaPlus_orderOf_four (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ)
    (hm : 3 ≤ m) : ∃ g : ↥(StatedOmega (StatedQuadPlus m K)), orderOf g = 4 := by
  have hn : 0 < m := by omega
  have hV : Module.finrank K (Fin m ⊕ Fin m → K) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  have hdim := CFSG.RankThree.Classical.finrank_tailSpace_add
    (CFSG.ClassicalGroups.Orthogonal.plusFamily_orth (K := K) (n := m) hn) m le_rfl
  obtain ⟨g, hg, hg4⟩ := CFSG.LocalAnalysis.SteinbergCD.exists_orderOf_eq_four_orthogonal
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus m K)
    (CFSG.ClassicalGroups.Orthogonal.plusFamily_orth (K := K) (n := m) hn) hm
    (fun x hx _ => CFSG.ClassicalGroups.Orthogonal.eq_zero_of_mem_tailSpace_plusFamily hn hx)
    (Or.inl (by omega))
  have hE := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadPlus (K := K) hm
  rw [hE] at hg
  refine ⟨(CFSG.ClassicalGroups.Orthogonal.statedOmegaPlusEquiv hm).symm ⟨g, hg⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact hg4

private theorem omegaMinus_orderOf_four (K : Type) [Field K] [Finite K] [CharP K 2] (m : ℕ)
    (hm : 4 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ g : ↥(StatedOmega (StatedQuadMinus m K b c)), orderOf g = 4 := by
  have hn : 0 < m - 1 := by omega
  have hV : Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) = 2 * m :=
    CFSG.SeitzReduction.F4Pilot.finrank_minusSpace (K := K) (n := m) (by omega)
  have hdim := CFSG.RankThree.Classical.finrank_tailSpace_add
    (CFSG.ClassicalGroups.Orthogonal.minusFamily_orth (K := K) (b := b) (c := c) hn) (m - 1)
      le_rfl
  obtain ⟨g, hg, hg4⟩ := CFSG.LocalAnalysis.SteinbergCD.exists_orderOf_eq_four_orthogonal
    (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    (CFSG.ClassicalGroups.Orthogonal.minusFamily_orth (K := K) (b := b) (c := c) hn) (by omega)
    (fun x hx hQx =>
      CFSG.ClassicalGroups.Orthogonal.eq_zero_of_mem_tailSpace_minusFamily hirr hn hx hQx)
    (Or.inr (by omega))
  have hE := CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
    (by omega : 2 ≤ m) hirr
  rw [hE] at hg
  refine ⟨(CFSG.ClassicalGroups.Orthogonal.statedOmegaMinusEquiv (by omega : 2 ≤ m) hirr).symm
    ⟨g, hg⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact hg4

end ClassicalOrderFour

section OmegaMinusSix

open CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadMinus)

private abbrev oE₁ (K : Type) [Field K] : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl (0 : Fin 2)) 1

private abbrev oE₂ (K : Type) [Field K] : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inl (1 : Fin 2)) 1

private abbrev oF₁ (K : Type) [Field K] : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inl (0 : Fin 2))) 1

private abbrev oF₂ (K : Type) [Field K] : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inl (1 : Fin 2))) 1

private abbrev oU (K : Type) [Field K] : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1

private theorem omega_q_e₁ (K : Type) [Field K] (b c : K) :
    quadMinus 3 K b c (oE₁ K) = 0 := by
  rw [quadMinus_apply]
  simp [oE₁, Pi.single_apply]

private theorem omega_q_e₂ (K : Type) [Field K] (b c : K) :
    quadMinus 3 K b c (oE₂ K) = 0 := by
  rw [quadMinus_apply]
  simp [oE₂, Pi.single_apply]

private theorem omega_q_f₁ (K : Type) [Field K] (b c : K) :
    quadMinus 3 K b c (oF₁ K) = 0 := by
  rw [quadMinus_apply]
  simp [oF₁, Pi.single_apply]

private theorem omega_q_f₂ (K : Type) [Field K] (b c : K) :
    quadMinus 3 K b c (oF₂ K) = 0 := by
  rw [quadMinus_apply]
  simp [oF₂, Pi.single_apply]

private theorem omega_q_W (K : Type) [Field K] [CharP K 2] (b c : K) :
    quadMinus 3 K b c (oE₁ K + oF₁ K + oU K) = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [quadMinus_apply]
  simp [oE₁, oF₁, oU, Pi.single_apply]
  linear_combination h2

private theorem omega_polar_f₂ (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus 3 K b c) z (oF₂ K) = z (Sum.inl (1 : Fin 2)) :=
  polar_quadMinus_single_inr_inl 3 K b c z 1

private theorem omega_polar_f₁ (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus 3 K b c) z (oF₁ K) = z (Sum.inl (0 : Fin 2)) :=
  polar_quadMinus_single_inr_inl 3 K b c z 0

private theorem omega_polar_e₁ (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus 3 K b c) z (oE₁ K) = z (Sum.inr (Sum.inl (0 : Fin 2))) :=
  polar_quadMinus_single_inl 3 K b c z 0

private theorem omega_polar_e₂ (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus 3 K b c) z (oE₂ K) = z (Sum.inr (Sum.inl (1 : Fin 2))) :=
  polar_quadMinus_single_inl 3 K b c z 1

private theorem omega_polar_U (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    polar (quadMinus 3 K b c) z (oU K) =
      2 * z (Sum.inr (Sum.inr (0 : Fin 2))) + b * z (Sum.inr (Sum.inr (1 : Fin 2))) :=
  polar_quadMinus_single_inr_inr_zero 3 K b c z

private theorem omega_polar_f₂_f₁ (K : Type) [Field K] (b c : K) :
    polar (quadMinus 3 K b c) (oF₂ K) (oF₁ K) = 0 := by
  rw [omega_polar_f₁]
  simp [oF₂, Pi.single_apply]

private theorem omega_polar_f₂_e₁ (K : Type) [Field K] (b c : K) :
    polar (quadMinus 3 K b c) (oF₂ K) (oE₁ K) = 0 := by
  rw [omega_polar_e₁]
  simp [oF₂, Pi.single_apply]

private theorem omega_polar_e₂_W (K : Type) [Field K] (b c : K) :
    polar (quadMinus 3 K b c) (oE₂ K) (oE₁ K + oF₁ K + oU K) = 0 := by
  rw [polar_add_right, polar_add_right, omega_polar_e₁, omega_polar_f₁, omega_polar_U]
  simp [oE₂, Pi.single_apply]

private theorem omega_eichler_1 (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    eichler (quadMinus 3 K b c) (oF₂ K) (oF₁ K) z =
      z + z (Sum.inl (1 : Fin 2)) • oF₁ K - z (Sum.inl (0 : Fin 2)) • oF₂ K := by
  rw [eichler_apply (omega_q_f₂ K b c) (omega_polar_f₂_f₁ K b c), omega_polar_f₂,
    omega_polar_f₁, omega_q_f₁, zero_mul, add_zero]

private theorem omega_eichler_2 (K : Type) [Field K] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    eichler (quadMinus 3 K b c) (oF₂ K) (oE₁ K) z =
      z + z (Sum.inl (1 : Fin 2)) • oE₁ K - z (Sum.inr (Sum.inl (0 : Fin 2))) • oF₂ K := by
  rw [eichler_apply (omega_q_f₂ K b c) (omega_polar_f₂_e₁ K b c), omega_polar_f₂,
    omega_polar_e₁, omega_q_e₁, zero_mul, add_zero]

private theorem omega_eichler_3 (K : Type) [Field K] [CharP K 2] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    eichler (quadMinus 3 K b c) (oE₂ K) (oE₁ K + oF₁ K + oU K) z =
      z + z (Sum.inr (Sum.inl (1 : Fin 2))) • (oE₁ K + oF₁ K + oU K) -
        (z (Sum.inr (Sum.inl (0 : Fin 2))) + z (Sum.inl (0 : Fin 2)) +
          (2 * z (Sum.inr (Sum.inr (0 : Fin 2))) + b * z (Sum.inr (Sum.inr (1 : Fin 2))))) •
          oE₂ K := by
  rw [eichler_apply (omega_q_e₂ K b c) (omega_polar_e₂_W K b c), omega_polar_e₂, polar_add_right,
    polar_add_right, omega_polar_e₁, omega_polar_f₁, omega_polar_U, omega_q_W K b c, zero_mul,
    add_zero]

private def omegaTmap (K : Type) [Field K] (b : K)
    (y : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K :=
  Sum.elim
    (fun j : Fin (3 - 1) => if j.val = 0 then
        y (Sum.inl (1 : Fin 2)) + y (Sum.inr (Sum.inl (0 : Fin 2))) +
          y (Sum.inr (Sum.inl (1 : Fin 2))) + b * y (Sum.inr (Sum.inr (1 : Fin 2)))
      else
        y (Sum.inl (0 : Fin 2)) + y (Sum.inl (1 : Fin 2)) +
          y (Sum.inr (Sum.inl (0 : Fin 2))) + b * y (Sum.inr (Sum.inr (1 : Fin 2))))
    (Sum.elim
      (fun j : Fin (3 - 1) => if j.val = 0 then
          y (Sum.inl (0 : Fin 2)) + y (Sum.inl (1 : Fin 2)) +
            y (Sum.inr (Sum.inl (1 : Fin 2))) + b * y (Sum.inr (Sum.inr (1 : Fin 2)))
        else
          y (Sum.inl (1 : Fin 2)) + y (Sum.inr (Sum.inl (1 : Fin 2))) +
            b * y (Sum.inr (Sum.inr (1 : Fin 2))))
      (fun j : Fin 2 => if j.val = 0 then
          y (Sum.inr (Sum.inr (0 : Fin 2))) + y (Sum.inr (Sum.inl (1 : Fin 2)))
        else y (Sum.inr (Sum.inr (1 : Fin 2)))))

private noncomputable def omegaG (K : Type) [Field K] (b c : K) :
    (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :=
  eichler (quadMinus 3 K b c) (oF₂ K) (oF₁ K) * eichler (quadMinus 3 K b c) (oF₂ K) (oE₁ K) *
    eichler (quadMinus 3 K b c) (oE₂ K) (oE₁ K + oF₁ K + oU K)

private theorem omegaG_apply (K : Type) [Field K] [CharP K 2] (b c : K)
    (z : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    omegaG K b c z = omegaTmap K b z := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  simp only [omegaG, LinearEquiv.mul_apply, omega_eichler_1, omega_eichler_2, omega_eichler_3]
  funext i
  rcases i with j | j | j <;> fin_cases j <;>
    simp [omegaTmap, oE₁, oE₂, oF₁, oF₂, oU, Pi.single_apply, CharTwo.sub_eq_add] <;>
    ring_nf <;> simp [h2, CharTwo.neg_eq, show (3 : K) = 1 by linear_combination h2]

private theorem omegaTmap_four (K : Type) [Field K] [CharP K 2] (b : K)
    (x : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → K) :
    omegaTmap K b (omegaTmap K b (omegaTmap K b (omegaTmap K b x))) = x := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext i
  rcases i with j | j | j <;> fin_cases j
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp
    linear_combination
      (17 * x (Sum.inr (Sum.inr 1)) * b + 7 * x (Sum.inr (Sum.inl 1)) +
        6 * x (Sum.inr (Sum.inl 0)) + 11 * x (Sum.inl 1) + 6 * x (Sum.inl 0)) * h2
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp
    linear_combination
      (19 * x (Sum.inr (Sum.inr 1)) * b + 8 * x (Sum.inr (Sum.inl 1)) +
        7 * x (Sum.inr (Sum.inl 0)) + 12 * x (Sum.inl 1) + 7 * x (Sum.inl 0)) * h2
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp
    linear_combination
      (17 * x (Sum.inr (Sum.inr 1)) * b + 7 * x (Sum.inr (Sum.inl 1)) +
        6 * x (Sum.inr (Sum.inl 0)) + 11 * x (Sum.inl 1) + 6 * x (Sum.inl 0)) * h2
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp
    linear_combination
      (11 * x (Sum.inr (Sum.inr 1)) * b + 4 * x (Sum.inr (Sum.inl 1)) +
        4 * x (Sum.inr (Sum.inl 0)) + 7 * x (Sum.inl 1) + 4 * x (Sum.inl 0)) * h2
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp
    linear_combination
      (6 * x (Sum.inr (Sum.inr 1)) * b + 3 * x (Sum.inr (Sum.inl 1)) +
        2 * x (Sum.inr (Sum.inl 0)) + 4 * x (Sum.inl 1) + 2 * x (Sum.inl 0)) * h2
  · simp only [omegaTmap, Sum.elim_inl, Sum.elim_inr, Fin.isValue]
    simp

private theorem omegaG_pow_four (K : Type) [Field K] [CharP K 2] (b c : K) :
    omegaG K b c ^ 4 = 1 := by
  apply LinearEquiv.ext
  intro x
  have h4 : omegaG K b c ^ 4 = omegaG K b c * (omegaG K b c * (omegaG K b c * omegaG K b c)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  simp only [h4, LinearEquiv.mul_apply, omegaG_apply, omegaTmap_four]
  rfl

private theorem omegaG_sq_ne_one (K : Type) [Field K] [CharP K 2] (b c : K) :
    omegaG K b c ^ 2 ≠ 1 := by
  intro h
  have h1 : (omegaG K b c ^ 2) (oE₁ K) = oE₁ K := by
    rw [h]
    rfl
  have h3 := congrFun h1 (Sum.inr (Sum.inl (0 : Fin 2)))
  simp only [pow_two, LinearEquiv.mul_apply, omegaG_apply] at h3
  simp [omegaTmap, oE₁, Pi.single_apply] at h3

private theorem omegaG_orderOf (K : Type) [Field K] [CharP K 2] (b c : K) :
    orderOf (omegaG K b c) = 4 := by
  have hnot : ¬ omegaG K b c ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact omegaG_sq_ne_one K b c
  have hfin : omegaG K b c ^ 2 ^ (1 + 1) = 1 := by
    norm_num
    exact omegaG_pow_four K b c
  have h := orderOf_eq_prime_pow hnot hfin
  norm_num at h
  exact h

private theorem omegaG_mem (K : Type) [Field K] (b c : K) :
    omegaG K b c ∈ elementaryGroup (quadMinus 3 K b c) :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (eichler_mem_elementaryGroup _ _ _)
    (eichler_mem_elementaryGroup _ _ _)) (eichler_mem_elementaryGroup _ _ _)

private theorem omegaMinusSix_exists_orderOf_four (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ g : ↥(StatedOmega (StatedQuadMinus 3 K b c)), orderOf g = 4 := by
  refine ⟨(statedOmegaMinusEquiv (m := 3) (by norm_num) hirr).symm
    ⟨omegaG K b c, omegaG_mem K b c⟩, ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact omegaG_orderOf K b c

end OmegaMinusSix

section MainStatements

theorem classicalOrderFourStatement_holds : ClassicalOrderFourStatement := by
  intro K _ _ _ _
  refine ⟨fun m hm => sp_orderOf_four K m hm, fun m hm => omegaPlus_orderOf_four K m hm, ?_⟩
  intro m b c hm hirr
  rcases Nat.lt_or_ge m 4 with h4 | h4
  · obtain rfl : m = 3 := by omega
    exact omegaMinusSix_exists_orderOf_four K b c hirr
  · exact omegaMinus_orderOf_four K m h4 hirr

end MainStatements

end CFSG.RankThree.GF2n.Stroth80
