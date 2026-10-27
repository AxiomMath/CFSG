module

public import Certificates.Data.CoverCenterThreeMcL
public import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestNative
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF3
import CFSG.Certificates.Kernel.CoverCKSound
import Certificates.Kernel.CoverCenter.McL
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.KD.CoverMcL

open Subgroup CFSG.SectionRank CFSG.SectionRank.Native CFSG.Blueprint CFSG.CosetTable
  CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRest CFSG.KC.CoverCK
open scoped commutatorElement

theorem f3Key_eq_of_toVec_eq {d : ℕ} {v w : CFSG.F3.Native.V}
    (h : (spec3 d).toVec v = (spec3 d).toVec w) : f3Key d v = f3Key d w := by
  have hget : ∀ j < d, v.get j = w.get j := by
    intro j hj
    have := congrFun h ⟨j, hj⟩
    change v.val j = w.val j at this
    unfold CFSG.F3.Native.V.val at this
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (V.get_lt v j),
      Nat.mod_eq_of_lt (V.get_lt w j)] at this
    exact this
  unfold f3Key
  have key : ∀ l : List ℕ, (∀ j ∈ l, v.get j = w.get j) →
      l.foldr (fun j acc => v.get j + 3 * acc) 0 = l.foldr (fun j acc => w.get j + 3 * acc) 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.foldr_cons, List.foldr_cons, hl a List.mem_cons_self,
        ih fun j hj => hl j (List.mem_cons_of_mem _ hj)]
  exact key _ fun j hj => hget j (List.mem_range.mp hj)

theorem witness : ∃ g : Fin 7 → NativeSporadic.McL,
    (∀ i, mclCoverE i ≠ 0 → g i ^ mclCoverE i = 1) ∧
    (∀ i, mclCoverE i = 0 → g i = ⁅evalW g (mclCoverCWf i).1, evalW g (mclCoverCWf i).2⁆) ∧
    (∀ w ∈ mclCoverRels, evalW g w = 1) ∧
    58320 ≤ Nat.card (Subgroup.closure (Set.range g)) := by
  have hsA : mclCoverData.seedA = String.ofList LA :=
    (rfl : mclCoverData.seedA = NativeSporadic.McLSeed1).trans LA_eq
  have hsB : mclCoverData.seedB = String.ofList LB :=
    (rfl : mclCoverData.seedB = NativeSporadic.McLSeed2).trans LB_eq
  obtain ⟨g, fg, -, he, hc, hrels⟩ := (spec3 21).cover_of_check mclCoverData
    (coverCheck_of_KL (d := 21) lay_ok rfl rfl decA decB hsA hsB cover_K)
  refine ⟨g, he, hc, hrels, ?_⟩
  have hsize : ((ops3 21).coverGens mclCoverData).size = 7 := by
    simp [Ops.coverGens, mclCoverData]
  have horb := orbitOK_of_KL (d := 21) lay_ok rfl rfl decA decB hsA hsB orbit_K
  rw [Array.extract_eq_self_of_le (by rw [hsize])] at horb
  let g' : ℕ → (NativeSporadic.seedMonoid 3 21 1 mclCoverData.seedA mclCoverData.seedB)ˣ :=
    fun l => if h : l < 7 then g ⟨l, h⟩ else 1
  have hg' : ∀ (j : ℕ) (hj : j < 7), g' j = g ⟨j, hj⟩ := fun j hj => dite_eq_left hj
  have fg' : ∀ j < ((ops3 21).coverGens mclCoverData).size,
      (spec3 21).WF ((ops3 21).coverGens mclCoverData)[j]! ∧
        LocalWitness.valHom _ (g' j) =
          (spec3 21).toMat ((ops3 21).coverGens mclCoverData)[j]! := by
    intro j hj
    rw [hsize] at hj
    rw [hg' j hj]
    exact fg ⟨j, hj⟩
  have hle := (spec3 21).le_card_closure_of_orbitOK _ g' fg'
    (fun v w _ _ hvw => f3Key_eq_of_toVec_eq hvw) horb
  have hlen : CFSG.KD.CoverMasks.mcl.length = 58320 := by decide +kernel
  rw [hlen] at hle
  have hset : g' '' Set.Iio ((ops3 21).coverGens mclCoverData).size = Set.range g := by
    rw [hsize]
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, hj⟩, (hg' j hj).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.val, Set.mem_Iio.mpr i.2, hg' i.val i.2⟩
  rw [hset] at hle
  exact hle

end CFSG.KD.CoverMcL

end
