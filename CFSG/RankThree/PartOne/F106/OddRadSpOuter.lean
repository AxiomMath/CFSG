module

public import CFSG.RankThree.PartOne.F106.OddRadAt
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
import CFSG.RankThree.PartOne.KC.SymplecticSubfieldRadical
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.GroupTheory.PerfectResidualNodes

public section

namespace CFSG.RankThree.PartOne.F106.OddRadSp

open CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.KCSpComm
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldAut spLinearAutGroup
  spSemilinearAutGroup)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

variable {K : Type} [Field K] [Finite K] {f r : ℕ}

theorem oddRadConcl_fieldAut_sp (hr : 2 ≤ r) {p : ℕ}
    (hp : Odd p) {σ : K ≃+* K} (hσ : σ ^ p = 1) :
    OddRadConcl (StatedProj (StatedSp r K)) (fieldAut r K σ) := by
  have : NeZero r := ⟨by omega⟩
  unfold OddRadConcl
  have hfix : (((fieldAut r K σ : MulAut (StatedProj (StatedSp r K))) :
      StatedProj (StatedSp r K) →* StatedProj (StatedSp r K)).eqLocus (MonoidHom.id _)) =
      spFixedGroup (fieldAut r K σ) := Subgroup.ext fun _ => Iff.rfl
  rw [hfix]
  have hrad := solvableRadical_fixedGroup hr hp hσ
  have hsub : (perfectResidual ↥(spFixedGroup (fieldAut r K σ))).IsSubnormal :=
    Subgroup.Normal.isSubnormal inferInstance
  have h1 := (CFSG.RankThree.solvable_radical_subnormal_intersection hsub).1
  rw [hrad, inf_bot_eq] at h1
  have h2 : solvableRadical ↥(perfectResidual ↥(spFixedGroup (fieldAut r K σ))) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h1
  rw [h2, Subgroup.card_bot]
  exact odd_one

theorem oddRadConcl_outer_sp (hr : 2 ≤ r) (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (β : MulAut (StatedProj (StatedSp r K))) (hβ : orderOf β = 5)
    (hβI : β ∉ inner (StatedProj (StatedSp r K))) :
    OddRadConcl (StatedProj (StatedSp r K)) β := by
  obtain ⟨-, -, -, -, -, -, -, hidx, hrel, hdesc⟩ :=
    CFSG.RankThree.Classical.SteinbergBY.symplectic_prime_semilinear_field_descent Nat.prime_two
      hf hr hK
  have hβ5 : β ^ 5 = 1 := by
    have := pow_orderOf_eq_one β
    rwa [hβ] at this
  have hE : β ∈ spSemilinearAutGroup r K := by
    have hidx' : (spSemilinearAutGroup r K).index ≤ 2 := Nat.le_of_dvd (by norm_num) hidx
    refine CFSG.RankThree.PartOne.OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (N := 5)
      (by decide) ?_
    rw [hβ5]
    exact Subgroup.one_mem _
  have hD : β ∉ spLinearAutGroup r K := by
    intro hD
    have hcop : Nat.gcd 2 (2 ^ f - 1) = 1 := by
      have h1 : (2 : ℕ) ^ f % 2 = 0 := by
        obtain ⟨g, hg⟩ := Nat.exists_eq_add_of_le hf
        rw [hg, pow_add]
        simp
      have h2 : 1 ≤ (2 : ℕ) ^ f := Nat.one_le_two_pow
      exact Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega)
    rw [hcop, Nat.dvd_one] at hrel
    exact hβI (Subgroup.relIndex_eq_one.mp hrel hD)
  obtain ⟨-, σ, hσord, -, h, -, hβh⟩ := hdesc 5 (by norm_num) β hE hD hβ
  have hσ5 : σ ^ 5 = 1 := by
    have := pow_orderOf_eq_one σ
    rwa [hσord] at this
  have key : OddRadConcl (StatedProj (StatedSp r K)) (fieldAut r K σ) :=
    oddRadConcl_fieldAut_sp hr (by decide) hσ5
  rw [← oddRadConcl_congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) β]
  have : MulAut.congr (h⁻¹ : MulAut (StatedProj (StatedSp r K))) β = fieldAut r K σ := by
    rw [hβh]
    refine MulEquiv.ext fun x => ?_
    simp [MulAut.congr_apply]
  rw [this]
  exact key

end CFSG.RankThree.PartOne.F106.OddRadSp
