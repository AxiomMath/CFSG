module

public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.Goldschmidt.Steps.G310Basic
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] def Item1411_3Strong (A : Subgroup G) (LB : Subgroup G → Subgroup G) : Prop :=
  ¬ TransOn A LB (xA A) ⊤ →
    ∃ Y : Subgroup G, Y = delta A LB Y ∧ Y ∈ scriptY A ∧ CFSG.Open.pCoreOf 2 Y ≠ ⊥ ∧
      inSubgroup perfectResidual Y ≠ ⊥ ∧ oPrimeResidualOf 3 Y ≠ ⊥ ∧
      ¬ TransOn A LB (xA A) Y

omit [Finite G] in
theorem item1411_3_of_strong {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    (h : Item1411_3Strong A LB) : Item1411_3 A LB := by
  intro hX
  obtain ⟨Y, hYΔ, hY, hO2, hres, -, hT⟩ := h hX
  exact ⟨Y, hYΔ, hY, hO2, hres, hT⟩

theorem not_three_dvd_of_oPrimeResidualOf_eq_bot {Y : Subgroup G}
    (hO : oPrimeResidualOf 3 Y = ⊥) : ¬ 3 ∣ Nat.card Y := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) 3 h3
  have hmem : (y : G) ∈ oPrimeResidualOf 3 Y := by
    rw [oPrimeResidualOf_eq_closure]
    refine Subgroup.subset_closure ⟨y.2, 1, ?_⟩
    rw [pow_one, ← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one, Subgroup.coe_one]
  rw [hO, Subgroup.mem_bot] at hmem
  have hy1 : y = 1 := Subtype.ext hmem
  rw [hy1, orderOf_one] at hy
  omega

theorem transOn_of_not_three_dvd {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hA : IsE27 A)
    (h146 : Item146 A LB) (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) {Y : Subgroup G}
    (hYΔ : Y = delta A LB Y) (hY : Y ∈ scriptY A) (hY3 : ¬ 3 ∣ Nat.card Y) :
    TransOn A LB (xA A) Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hYinv : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three Y).mpr hY3, hY.2⟩
  have hYQ : Y ∈ scriptQ A LB := by
    have := delta_mem_scriptQ hA h146 hYinv
    rwa [← hYΔ] at this
  have hAC : A ≤ Subgroup.centralizer (A : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hA.1.1
  have hsyl : ∀ S ∈ scriptQPiStar A LB Y (piOf 2), CFSG.Open.fusionIsSylowIn 2 S Y ∧
      A ≤ Subgroup.normalizer (S : Set G) := by
    intro S hS
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.prop.1.1.1.2.2
    obtain ⟨S', hS', hSS', hAS'⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      Nat.prime_three Nat.prime_two hA3 hY3 hY.2 hS.prop.1.2 hS2 hAS
    have hS'mem : S' ∈ scriptQPi A LB Y (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hYQ hS'.1 hAS', hS'.1⟩,
        (isPiSubgroup_piOf_iff Nat.prime_two S').mpr hS'.2.1⟩
    have := hS.eq_of_le hS'mem hSS'
    exact ⟨this ▸ hS', hAS⟩
  intro S hS T hT
  obtain ⟨hSs, hAS⟩ := hsyl S hS
  obtain ⟨hTs, hAT⟩ := hsyl T hT
  obtain ⟨x, hx, hxT⟩ := CFSG.Goldschmidt.G310.exists_conj_of_invariant_sylows Nat.prime_three
    Nat.prime_two hA3 hY3 hY.2 hSs hTs hAS hAT
  have hCYA : Y ⊓ Subgroup.centralizer (A : Set G) ≤ xA A := by
    refine le_pPrimeCoreOf_centralizer hbot (mem_scriptQ_of_le hYQ inf_le_left ?_) inf_le_right
    exact le_normalizer_inf hY.2 (hAC.trans Subgroup.le_normalizer)
  exact ⟨x, ⟨hCYA hx, (Subgroup.mem_inf.mp hx).1⟩, hxT⟩

theorem rank3II_14_11_3_strong_of {A : Subgroup G} {LB : Subgroup G → Subgroup G} (hA : IsE27 A)
    (h146 : Item146 A LB) (hbot : ∃ B, IsHyperplane A B ∧ LB B = ⊥) (h3 : Item1411_3 A LB) :
    Item1411_3Strong A LB := by
  intro hX
  obtain ⟨Y, hYΔ, hY, hO2, hres, hT⟩ := h3 hX
  refine ⟨Y, hYΔ, hY, hO2, hres, fun hO => hT ?_, hT⟩
  exact transOn_of_not_three_dvd hA h146 hbot hYΔ hY (not_three_dvd_of_oPrimeResidualOf_eq_bot hO)

theorem transOn_of_transOn_top {A : Subgroup G} {LB : Subgroup G → Subgroup G} {Y : Subgroup G}
    (hXY : xA A ≤ Y) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (htr : TransOn A LB (xA A) ⊤) : TransOn A LB (xA A) Y := by
  have hext : ∀ S ∈ scriptQPiStar A LB Y (piOf 2),
      ∃ S' ∈ scriptQPiStar A LB ⊤ (piOf 2), S = S' ⊓ Y := by
    intro S hS
    obtain ⟨S', hSS', hS'⟩ := Finite.exists_le_maximal
      (p := (· ∈ scriptQPi A LB ⊤ (piOf 2))) (a := S) ⟨⟨hS.prop.1.1, le_top⟩, hS.prop.2⟩
    have hmem : S' ⊓ Y ∈ scriptQPi A LB Y (piOf 2) :=
      ⟨⟨mem_scriptQ_of_le hS'.prop.1.1 inf_le_left (le_normalizer_inf hS'.prop.1.1.1.2.2 hAY),
          inf_le_right⟩,
        fun q hq => hS'.prop.2 q (hq.trans (Subgroup.card_dvd_of_le inf_le_left))⟩
    exact ⟨S', hS', hS.eq_of_le hmem (le_inf hSS' hS.prop.1.2)⟩
  intro S hS T hT
  obtain ⟨S', hS', rfl⟩ := hext S hS
  obtain ⟨T', hT', rfl⟩ := hext T hT
  obtain ⟨x, hx, hxT⟩ := htr S' hS' T' hT'
  have hxX : x ∈ xA A := (Subgroup.mem_inf.mp hx).1
  have hxY : x ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer (hXY hxX)
  refine ⟨x, ⟨hxX, hXY hxX⟩, ?_⟩
  rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj x).injective, ← hxT,
    Late.map_conj_eq_of_mem_normalizer hxY]

end CFSG.RankThree.PartTwo.Sec14
