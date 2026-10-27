module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeUC.Basic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_mem_pCoreOf_of_prime_order {K : Subgroup G} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    {a : G} (haK : a ∈ K) (har : orderOf a = r) : a ∉ CFSG.Open.pCoreOf 2 K := by
  intro hmem
  have hpc : (⟨a, haK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
    (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨a, haK⟩).1 hmem
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨⟨a, haK⟩, hpc⟩
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, har] at hk
  have hodd : Odd r := hr.odd_of_ne_two hr2
  rcases k with _ | k
  · rw [pow_zero] at hk
    exact hr.ne_one hk
  · exact (Nat.not_even_iff_odd.mpr hodd) ⟨2 ^ k, by rw [hk, pow_succ]; ring⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
