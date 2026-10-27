module

public import CFSG.Monster.B.Cbar.AxisCentral
public import CFSG.Monster.B.Cbar.FourGroupSpin
public import CFSG.Monster.Generated.OddCocode

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.Generated.OddCocode

variable {δ : Cocode}

theorem hCocode_Xlift_rPlus_even (hδ : pair ΩC δ = 0) (i j : Fin 24) :
    hCocode δ (0, Xlift (rPlus i j), 0) = ((0 : symMat), Xlift (rPlus i j), (0 : SpaceW)) := by
  rw [hCocode_Xlift, pair_coordOf_rPlus, hδ, sgn_zero, one_smul]

theorem hCocode_pair_even (hδ : pair ΩC δ = 0) (p : LtPair) (k : Fin 3) :
    hCocode δ (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact hCocode_pair_zero δ p
  · rw [tbasis_pair_one', map_sub, hCocode_Xlift_rMinus, hCocode_Xlift_rPlus_even hδ]
  · rw [tbasis_pair_two', map_add, hCocode_Xlift_rMinus, hCocode_Xlift_rPlus_even hδ]

theorem hCocode_odd_even (hδ : pair ΩC δ = 0) (c : C₀) (i : Fin 24) (k : Fin 3) :
    hCocode δ (tbasis (.inr (.inr (.inl (c, i, k))))) =
      sgn (pair (c : C) δ) • tbasis (.inr (.inr (.inl (c, i, k)))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · have h1 : sgn (pair (coordOf (rOdd c i)).1 δ) = sgn (pair (c : C) δ) := by
      rw [coordOf_rOdd]
      exact congrArg sgn (by rw [aOdd, pair_add_left, pair_smul_left, hδ, mul_zero, add_zero])
    rw [tbasis_odd_zero, hCocode_Xlift, h1]
  · rw [tbasis_odd_one, mk_zero_zero_smul, map_smul, hCocode_tensor_E, hδ, add_zero, smul_comm]
  · rw [tbasis_odd_two, mk_zero_zero_smul, map_smul, hCocode_tensor_E, hδ, add_zero, smul_comm]

theorem hCocode_oct_even (hδ : pair ΩC δ = 0) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    hCocode δ (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      sgn (pair (d : C) δ) • tbasis (.inr (.inr (.inr ⟨d, v⟩))) := by
  rw [tbasis_oct, hCocode_Xlift]
  have h : (coordOf (rOctQ d v)).1 = aOct (d : C) (octRep d v) := by
    rw [rOctQ, coordOf_rOct]
  rw [h, aOct, pair_add_left, pair_smul_left, hδ, mul_zero, add_zero]

theorem hCocode_tauB_tbasis_even (hδ : pair ΩC δ = 0) (x : TIdx) :
    hCocode δ (tauB (tbasis x)) = tauB (hCocode δ (tbasis x)) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · rw [tauB_diag, hCocode_diag, tauB_diag]
  · rw [tauB_pair, hCocode_pair_even hδ, hCocode_pair_even hδ, tauB_pair]
  · rw [tauB_odd, hCocode_odd_even hδ, hCocode_odd_even hδ, map_smul, tauB_odd]
  · rw [tauB_oct, hCocode_oct_even hδ, map_smul, tauB_oct, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_smul, hCocode_oct_even hδ, smul_comm]

theorem hCocode_mul_tauB_even (hδ : pair ΩC δ = 0) : hCocode δ * tauB = tauB * hCocode δ :=
  tbasis.ext' fun x => hCocode_tauB_tbasis_even hδ x

theorem tStar_eq_hCocode : tStar = hCocode (deltaPair 0 1) := rfl

theorem tauB_mul_tStar : tauB * tStar = tStar * tauB := by
  rw [tStar_eq_hCocode]
  exact (hCocode_mul_tauB_even (pair_ΩC_deltaPair 0 1)).symm

theorem tauB_aStar : tauB aStar = aStar := by
  have h := (commute_iff_of_eq_tAxis aStar_mem_axisOrbit tAxis_aStar.symm tauB_mem_Gmat).1
    tauB_mul_tStar
  exact h

theorem closure_le_centralizer_tStar :
    Subgroup.closure (insert tauB ((Gvis ⊓ Subgroup.centralizer {tStar} :
      Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Set (SpaceB ≃ₗ[ℚ] SpaceB))) ≤
      Gmat ⊓ Subgroup.centralizer {tStar} := by
  rw [Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact ⟨tauB_mem_Gmat, Subgroup.mem_centralizer_singleton_iff.2 tauB_mul_tStar⟩
  · exact ⟨Hmat_le_Gmat hg.1, hg.2⟩

theorem even_cocode_centralizes_triality :
    (∀ δ : Cocode, pair ΩC δ = 0 → rhoEquiv (DQ δ) * tauB = tauB * rhoEquiv (DQ δ)) ∧
    tStar = rhoEquiv (DQ (deltaPair 0 1)) ∧ tauB * tStar = tStar * tauB ∧ tauB aStar = aStar ∧
    Subgroup.closure (insert tauB ((Gvis ⊓ Subgroup.centralizer {tStar} :
      Subgroup (SpaceB ≃ₗ[ℚ] SpaceB)) : Set (SpaceB ≃ₗ[ℚ] SpaceB))) ≤
      Gmat ⊓ Subgroup.centralizer {tStar} :=
  ⟨fun _ hδ => hCocode_mul_tauB_even hδ, rfl, tauB_mul_tStar, tauB_aStar,
    closure_le_centralizer_tStar⟩

end CFSG.Monster.B
