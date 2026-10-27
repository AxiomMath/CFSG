module

public import CFSG.Monster.GMS.S365Basic
public import CFSG.Monster.GMS.Leech.Data
public import CFSG.Monster.GMS.NotConj
import CFSG.Monster.GMS.Griess13.ChecksUniqueness
import CFSG.Monster.GMS.Leech.Pairs
import CFSG.Sporadic.Co1.Module.Pairs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace LeechSystem

variable {G : Type*} [Group G] {z : G} (L : LeechSystem z)

theorem leechOrbits
    [Finite G] (hP : Co1PairFacts) :
    LeechOrbits z (L.typeSet 0) (L.typeSet 1) (L.typeSet 2) := by
  refine ⟨?_, L.typeSet_subset 0, L.typeSet_subset 2, ?_, ?_,
    fun q hq => L.mul_self_of_mem_typeSet_one hq, fun g hg q hq => L.conj_mem_typeSet hg hq,
    fun g hg q hq => L.conj_mem_typeSet hg hq,
    fun q hq q' hq' => L.exists_conj_of_mem_typeSet hq hq',
    fun q hq q' hq' => L.exists_conj_of_mem_typeSet hq hq', ?_, L.leechData_pair_one hP,
    L.leechData_pair_two hP, L.leechData_pair_three hP⟩
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
  · rw [L.ncard_typeSet, Leech.ncard_co1Orbit_two]

end LeechSystem

namespace S365

section Classes

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ w : G}

theorem exists_leechSystem_of_isConj
    (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w) :
    Nonempty (LeechSystem w) :=
  exists_leechSystem co1ModuleUniqueness (hG.2.of_isConj hw)

theorem isConj_of_mem_typeSet_zero
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) (L : LeechSystem w) {q : G} (hq : q ∈ L.typeSet 0) : IsConj a q := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  exact h.isConj_of_mem_two hw (L.leechOrbits co1PairFacts) hq

theorem isConj_of_mem_typeSet_two
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) (L : LeechSystem w) {q : G} (hq : q ∈ L.typeSet 2) : IsConj z₀ q := by
  obtain ⟨b, z, u, h⟩ := exists_twoClasses I.sls I.tableV I.leech hG
  exact h.isConj_of_mem_four hw (L.leechOrbits co1PairFacts) hq

theorem mem_typeSet_zero_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) (L : LeechSystem w) {q : G} (hq : q ∈ leechQ w) (hqa : IsConj a q) :
    q ∈ L.typeSet 0 := by
  have hq2 : q * q = 1 := mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hqa).symm.trans hG.1.1)
  have hq1 : q ≠ 1 := ne_one_of_orderOf ((orderOf_eq_of_isConj hqa).symm.trans hG.1.1)
  have hqw : q ≠ w := fun h => hG.not_isConj ((h ▸ hqa).trans hw.symm)
  rcases L.mem_typeSet_zero_or_two hq hq1 hqw hq2 with h | h
  · exact h
  · exact absurd (isConj_of_mem_typeSet_two I hG hw L h)
      (fun hb => hG.not_isConj (hqa.trans hb.symm))

theorem isLeechCentralLift_of_isConj
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀)
    (hw : IsConj z₀ w) {y : G} (hyC : y ∈ Subgroup.centralizer ({w} : Set G))
    (hya : IsConj a y) (hyQ : y ∉ leechQ w) : IsLeechCentralLift w y := by
  have hcomm : y * w = w * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
  have hy2 : orderOf y = 2 := (orderOf_eq_of_isConj hya).symm.trans hG.1.1
  refine ⟨hyC, hy2, hyQ, ?_, ?_⟩
  · have := card_centralizer_inf_of_not_mem_leechQ I.sls I.tableV I.leech hG hw hyC hyQ hya
    rw [this]
    rfl
  · intro g hg hgy
    have h1 : IsConj a (y * w) := by
      rw [← hgy]
      exact hya.trans (isConj_conj_self g y)
    have h2 : IsConj z₀ (w * y) := (isConj_mul_iff I hG hw hya hcomm).2 hyQ
    rw [← hcomm] at h2
    exact hG.not_isConj (h1.trans h2.symm)

end Classes

end S365

end CFSG.Monster.GMS
