module

public import CFSG.LocalAnalysis.StandardType.GGL45FixA2Rank
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.ProjRank
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCoprimeCentral
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotEndFieldBasic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank
open CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne.OutStructure
open CFSG.HardMathSupport.Timmesfeld.LinearRank

private theorem gfr7_aut_index_facts {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8) :
    (semilinearAutGroup 3 K).index ∣ 2 ∧
      (conjAut 3 K).range.relIndex (semilinearAutGroup 3 K) ∣ 3 := by
  have hK' : Nat.card K = 2 ^ 3 := by rw [hK]; norm_num
  set E := semilinearAutGroup 3 K with hE
  set D := (conjAut 3 K).range with hD
  set Φ := (fieldAut 3 K).range with hΦ
  have hDn : D.Normal := CFSG.SeitzReduction.LinearPilot.conjAut_range_normal
    (by norm_num : 3 ≤ 3)
  have hEidx : E.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    refine ⟨dualAut 3 K, fun b => ?_⟩
    have hb : b ∈ standardAutGroup 3 K := by
      rw [(automorphism_generation (K := K) (n := 3) (by norm_num)).1]
      exact mem_top b
    rcases mem_or_mul_dualAut_mem hb with h | h
    · exact Or.inr h
    · exact Or.inl h
  have hEsup : E = Φ ⊔ D := by
    rw [hE, semilinearAutGroup, Subgroup.closure_union, linearAutGroup_eq_range,
      Subgroup.closure_eq, ← MonoidHom.coe_range, Subgroup.closure_eq, sup_comm]
  have hEDidx : D.relIndex E ∣ 3 := by
    rw [hEsup, Subgroup.relIndex_sup_right]
    refine (Subgroup.relIndex_dvd_card D Φ).trans ?_
    refine (Subgroup.card_range_dvd (fieldAut 3 K)).trans ?_
    rw [(card_ringAut_and_isCyclic Nat.prime_two K hK').1]
  exact ⟨hEidx, hEDidx⟩

private theorem gfr7_card_le_49_of_mulAut_projectiveSL {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) (B : Subgroup (MulAut (projectiveSL 3 K))) (hB : IsElemAbelian 7 B) :
    Nat.card B ≤ 7 ^ 2 := by
  obtain ⟨hEidx, hEDidx⟩ := gfr7_aut_index_facts (K := K) hK
  set E := semilinearAutGroup 3 K with hE
  set D := (conjAut 3 K).range with hD
  have hEidx' : E.index ≤ 2 := Nat.le_of_dvd (by norm_num) hEidx
  have hBE : B ≤ E := by
    intro α hα
    refine mem_of_pow_mem_of_index_le_two E hEidx' (N := 7) (by norm_num) ?_
    rw [hB.2 α hα]
    exact E.one_mem
  have hBD : B ≤ D := by
    have hne : D.relIndex E ≠ 0 := by
      rintro h0
      rw [h0] at hEDidx
      omega
    have hle : D.relIndex B ≤ D.relIndex E := Subgroup.relIndex_le_of_le_right hBE hne
    have hle3 : D.relIndex B ≤ 3 := hle.trans (Nat.le_of_dvd (by norm_num) hEDidx)
    have hdvd : D.relIndex B ∣ Nat.card B := Subgroup.relIndex_dvd_card D B
    haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have hP : IsPGroup 7 B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g g.2)⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
    rw [hj] at hdvd
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_seven).1 hdvd
    have hi0 : i = 0 := by
      by_contra hne0
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 hne0
      have h7 : 7 ^ 1 ≤ 7 ^ i := Nat.pow_le_pow_right (by norm_num) hi1
      rw [hi] at hle3
      simp only [pow_one] at h7
      omega
    rw [hi0] at hi
    exact Subgroup.relIndex_eq_one.mp (by simpa using hi)
  have hpK : 7 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
  let ρ : ↥(⊤ : Subgroup (GL (Fin 3) K)) →* MulAut (projectiveSL 3 K) :=
    (conjAut 3 K).comp (⊤ : Subgroup (GL (Fin 3) K)).subtype
  have hker : ∀ A : ↥(⊤ : Subgroup (GL (Fin 3) K)), ρ A = 1 ↔
      (A : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    intro A
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.mem_center_iff]
    exact conjAut_eq_one_iff le_rfl _
  have hBρ : B ≤ ρ.range := by
    intro α hα
    obtain ⟨A, rfl⟩ := hBD hα
    exact ⟨⟨A, trivial⟩, rfl⟩
  have h49 := card_le_of_scalar_kernel Nat.prime_seven (by norm_num) hpK (by norm_num)
    (⊤ : Subgroup (GL (Fin 3) K)) ρ hker B hBρ hB
  simpa using h49

theorem gffa2_rank_linear_seven {K : Type} [Field K] [Finite K] (hK : Nat.card K = 8)
    (A : Subgroup (MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))))
    (hA : IsElemAbelian 7 A) : Nat.card A ≤ 7 ^ 2 := by
  have h49 := gfr7_card_le_49_of_mulAut_projectiveSL (K := K) hK
    (A.map (MulAut.congr (TypeA.recipeEquiv 3 K)).toMonoidHom)
    (CFSG.SectionRank.isElemAbelian_map hA
      (MulAut.congr (TypeA.recipeEquiv 3 K)).toMonoidHom)
  rwa [Subgroup.card_map_of_injective (MulAut.congr (TypeA.recipeEquiv 3 K)).injective] at h49

end CFSG.StandardType

end
