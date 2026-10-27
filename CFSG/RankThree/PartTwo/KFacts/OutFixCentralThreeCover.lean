module

public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeTools
public import CFSG.RankThree.PartTwo.Sec4.Statements
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSU
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_mem_center_of_mulEquiv {Y : Type*} [Group Y] (e : X ≃* Y) {z : X}
    (hz : z ∈ Subgroup.center X) : e z ∈ Subgroup.center Y := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.mem_map_of_mem _ hz

omit [Finite X] in
theorem fixCommInner_of_isSLThreeEpsAt {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e) (hq : 2 < p ^ e)
    (hX : IsSLThreeEpsAt X (p ^ e)) {z : X} (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) :
    FixCommInner X z := by
  obtain ⟨K, _, _, ⟨-, ⟨f⟩⟩ | ⟨hK, ⟨f⟩⟩⟩ := hX
  · set g : X ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
      f.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
    exact FixCommInner.of_mulEquiv g (fixCommInner_specialLinear
      (map_mem_center_of_mulEquiv g hz) (by rw [MulEquiv.orderOf_eq, hz3]))
  · have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p e K :=
      ⟨hp, he, by rw [hK, ← pow_mul, mul_comm]⟩
    exact FixCommInner.of_mulEquiv f (fixCommInner_unitarySU h hq
      (map_mem_center_of_mulEquiv f hz) (by rw [MulEquiv.orderOf_eq, hz3]))

theorem isoLThreePi_of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) {p e' : ℕ}
    [Fact p.Prime] (h : IsoLThreePi T p e') : IsoLThreePi S p e' := by
  rcases h with ⟨h1, ⟨f⟩⟩ | ⟨h2, ⟨f⟩⟩
  · exact Or.inl ⟨h1, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨h2, ⟨e.trans f⟩⟩

omit [Finite X] in
theorem two_lt_of_isoLThreePi (hq : IsQuasisimple X) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hpi : IsoLThreePi (X ⧸ Subgroup.center X) p e) : 2 < p ^ e := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpe : p ≤ p ^ e := Nat.le_self_pow (by omega) p
  rcases hpi with ⟨h1, -⟩ | ⟨h2, ⟨f⟩⟩
  · by_contra hle
    have h2' : p ^ e = 2 := by omega
    rw [h2'] at h1
    norm_num at h1
  · by_contra hle
    have h2' : p ^ e = 2 := by omega
    have hp : p = 2 := by omega
    subst hp
    have he1 : e = 1 := by
      by_contra hne
      have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst he1
    exact Sec4.Census.false_of_isQuasisimple_projSU_three_two hq f

section Cover


theorem fixCommInner_of_isoLThreePi_of_isPGroup (hq : IsQuasisimple X)
    (hZ3 : IsPGroup 3 (Subgroup.center X)) {z : X} (hz : z ∈ Subgroup.center X)
    (hz3 : orderOf z = 3) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hb : p = 2 ∨ e ≤ 2)
    (hpi : IsoLThreePi (X ⧸ Subgroup.center X) p e) : FixCommInner X z := by
  have hZ : Subgroup.center X ≠ ⊥ := by
    intro hbot
    have hz1 : z = 1 := by
      have := hz
      rwa [hbot, Subgroup.mem_bot] at this
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  exact fixCommInner_of_isSLThreeEpsAt Fact.out he (two_lt_of_isoLThreePi hq he hpi)
    (Sec4.Census.coverSLThree46 X hq hZ3 hZ p e he hb hpi) hz hz3

theorem fixCommInner_of_isoLThreePi (hq : IsQuasisimple X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hb : p = 2 ∨ e ≤ 2) (hpi : IsoLThreePi (X ⧸ Subgroup.center X) p e) :
    FixCommInner X z := by
  obtain ⟨hq', ⟨ε⟩, hz'⟩ := quotient_centerThreePrime_facts hq hz
  refine FixCommInner.of_centerThreePrime hq ?_
  exact fixCommInner_of_isoLThreePi_of_isPGroup hq' (isPGroup_center_quotient_centerThreePrime hq)
    hz' (orderOf_mk_centerThreePrime hz3) he hb (isoLThreePi_of_mulEquiv ε hpi)

end Cover

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
