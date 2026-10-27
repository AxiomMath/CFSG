module

public import Certificates.Data.CoverCenterThreeJ3
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
import CFSG.Certificates.Kernel.CoverCKSound
import Certificates.Kernel.CoverCenter.J3
import Certificates.Kernel.CoverCenter.J3Cov
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CertificateChecks.KernelCover.J3

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.CosetTable
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.KC.CoverCK
  CertificateChecks.KernelLC.J3Ops CFSG.Sporadic.SmallF2
open scoped commutatorElement

theorem mod_eq_of_toVec_eq {d v w : ℕ} (h : (spec2 d).toVec v = (spec2 d).toVec w) :
    v % 2 ^ d = w % 2 ^ d := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hj : j < d
  · have := congrFun h ⟨j, hj⟩
    change toVecD d v ⟨j, hj⟩ = toVecD d w ⟨j, hj⟩ at this
    simp only [toVecD_apply] at this
    simp only [hj, decide_true, Bool.true_and]
    cases hv : v.testBit j <;> cases hw : w.testBit j <;> simp_all
  · simp [hj]

theorem witness : ∃ g : Fin 6 → NativeSporadic.J3,
    (∀ i, j3CoverE i ≠ 0 → g i ^ j3CoverE i = 1) ∧
    (∀ i, j3CoverE i = 0 → g i = ⁅evalW g (j3CoverCWf i).1, evalW g (j3CoverCWf i).2⁆) ∧
    (∀ w ∈ j3CoverRels, evalW g w = 1) ∧
    Nat.card (Subgroup.closure ({g 0, g 1} : Set NativeSporadic.J3)) = 1944 := by
  have hsA : j3CoverData.seedA = String.ofList SA.chars :=
    (rfl : j3CoverData.seedA = CFSG.Sporadic.J3.Native.seedA).trans SA.eq
  have hsB : j3CoverData.seedB = String.ofList SB.chars :=
    (rfl : j3CoverData.seedB = CFSG.Sporadic.J3.Native.seedB).trans SB.eq
  obtain ⟨g, fg, -, he, hc, hrels⟩ :=
    (spec2 80).cover_of_check j3CoverData (coverCheck_of_K2 SA.bind SB.bind hsA hsB cover_K)
  refine ⟨g, he, hc, hrels, le_antisymm ?_ ?_⟩
  · have hws : ∀ w ∈ CFSG.KBRoute.J3Cov.nWords, evalW g w = 1 := by
      intro w hw
      simp only [CFSG.KBRoute.J3Cov.nWords, List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | rfl
      · exact hrels w hw
      · have hpow : evalW g (List.replicate 8 ((0 : Fin 6), true)) = g 0 ^ 8 := by
          simp [evalW, List.replicate_succ, pow_succ, mul_assoc]
        rw [hpow]
        exact he 0 (by decide)
    have hle : Subgroup.closure ({g 0, g 1} : Set _) ≤ Subgroup.closure (Set.range g) := by
      apply Subgroup.closure_mono
      rintro _ (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    exact (Subgroup.card_le_of_le hle).trans
      ((card_closure_le_of_rels g _ hws J3Cov.n_card.1).trans J3Cov.n_card.2)
  · have horb := orbitOK_of_K2 SA.bind SB.bind hsA hsB orbit_K
    have hsize : ((ops2 80).coverGens j3CoverData).size = 6 := by
      simp [Ops.coverGens, j3CoverData]
    set gens := ((ops2 80).coverGens j3CoverData).extract 0 2 with hgens
    have hgs : gens.size = 2 := by simp [gens, hsize]
    have hget : ∀ j < 2, gens[j]! = ((ops2 80).coverGens j3CoverData)[j]! := by
      intro j hj
      rw [getElem!_pos gens j (by omega),
        getElem!_pos ((ops2 80).coverGens j3CoverData) j (by omega)]
      simp [gens]
    let g' : ℕ → (NativeSporadic.seedMonoid 2 80 1 j3CoverData.seedA j3CoverData.seedB)ˣ :=
      fun l => if h : l < 6 then g ⟨l, h⟩ else 1
    have hg' : ∀ (j : ℕ) (hj : j < 6), g' j = g ⟨j, hj⟩ := fun j hj => dite_eq_left hj
    have fg' : ∀ j < gens.size, (spec2 80).WF gens[j]! ∧
        LocalWitness.valHom _ (g' j) = (spec2 80).toMat gens[j]! := by
      intro j hj
      rw [hgs] at hj
      rw [hg' j (by omega), hget j hj]
      exact fg ⟨j, by omega⟩
    have hle := (spec2 80).le_card_closure_of_orbitOK gens g' fg'
      (fun v w _ _ hvw => mod_eq_of_toVec_eq hvw) horb
    have hlen : CFSG.KD.CoverMasks.J3.c0.length = 1944 := by decide +kernel
    rw [hlen] at hle
    have hset : g' '' Set.Iio gens.size = {g 0, g 1} := by
      rw [hgs]
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hj2 : j = 0 ∨ j = 1 := by
          simp only [Set.mem_Iio] at hj
          omega
        rcases hj2 with rfl | rfl
        · exact Or.inl (hg' 0 (by norm_num))
        · exact Or.inr (hg' 1 (by norm_num))
      · rintro (rfl | rfl)
        · exact ⟨0, by simp, hg' 0 (by norm_num)⟩
        · exact ⟨1, by simp, hg' 1 (by norm_num)⟩
    rw [hset] at hle
    exact hle

end CertificateChecks.KernelCover.J3

end
