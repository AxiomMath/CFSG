module

public import CFSG.Monster.GMS.Leech.Pairs
public import CFSG.Monster.GMS.Leech.Involutions

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

include L

theorem leechData
    [Finite G] (hP : Co1PairFacts) (hI : Co1InvolutionFacts) : LeechData z := by
  refine ⟨L.typeSet 0, L.typeSet 1, L.typeSet 2, ?_, L.typeSet_subset 0, L.typeSet_subset 1,
    L.typeSet_subset 2, L.disjoint_typeSet (by decide), L.disjoint_typeSet (by decide),
    L.disjoint_typeSet (by decide), ?_, ?_, fun q hq => L.mul_self_of_mem_typeSet_one hq,
    fun g hg q hq => L.conj_mem_typeSet hg hq, fun g hg q hq => L.conj_mem_typeSet hg hq,
    fun g hg q hq => L.conj_mem_typeSet hg hq,
    fun q hq q' hq' => L.exists_conj_of_mem_typeSet hq hq',
    fun q hq q' hq' => L.exists_conj_of_mem_typeSet hq hq',
    fun q hq q' hq' => L.exists_conj_of_mem_typeSet hq hq', ?_, ?_, ?_,
    L.leechData_pair_one hP, L.leechData_pair_two hP, L.leechData_pair_three hP,
    L.leechData_involution_one hI, L.leechData_involution_two hI⟩
  · intro q hq h1 hz
    obtain ⟨i, hi⟩ := L.exists_mem_typeSet hq h1 hz
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  · exact fun q hq => ⟨L.ne_one_of_mem_typeSet hq, L.ne_z_of_mem_typeSet hq,
      L.mul_self_of_mem_typeSet_zero hq, L.mul_z_mem_typeSet hq⟩
  · exact fun q hq => ⟨L.ne_one_of_mem_typeSet hq, L.ne_z_of_mem_typeSet hq,
      L.mul_self_of_mem_typeSet_two hq, L.mul_z_mem_typeSet hq⟩
  · rw [L.ncard_typeSet, Leech.ncard_co1Orbit_zero]
  · rw [L.ncard_typeSet, Leech.ncard_co1Orbit_one]
  · rw [L.ncard_typeSet, Leech.ncard_co1Orbit_two]

end LeechSystem

theorem leechStatement_of
    (h13 : Co1ModuleUniqueness) (hP : Co1PairFacts)
    (hI : Co1InvolutionFacts) : LeechStatement := by
  intro G _ _ z hz
  obtain ⟨L⟩ := exists_leechSystem h13 hz
  exact L.leechData hP hI

theorem leechPairStatement_of
    (h13 : Co1ModuleUniqueness) (hP : Co1PairFacts) :
    LeechPairStatement := by
  intro G _ _ z hz
  obtain ⟨L⟩ := exists_leechSystem h13 hz
  exact L.leechPairData hP

theorem leechCosetStatement_of
    (h13 : Co1ModuleUniqueness) (hI : Co1InvolutionFacts) :
    LeechCosetStatement := by
  intro G _ _ z hz
  obtain ⟨L⟩ := exists_leechSystem h13 hz
  exact L.leechCosetData hI

theorem leechInvolutionStatement_of
    (h13 : Co1ModuleUniqueness) (hI : Co1InvolutionFacts) :
    LeechInvolutionStatement := by
  intro G _ _ z hz
  obtain ⟨L⟩ := exists_leechSystem h13 hz
  exact L.leechInvolutionData hI

end CFSG.Monster.GMS
