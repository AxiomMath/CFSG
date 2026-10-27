module

public import CFSG.GroupTheory.PCore.SolvableRadical
public import CFSG.OddTranspositions.PartThree.EightOne.Quotient
public import CFSG.Timmesfeld.Bridge.Asc72ElemCompQuot
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.OddTranspositions.PartThree.ElevenThree

private theorem isSolvable_comap_center_pCore {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] :
    Group.IsSolvable
      ((Subgroup.center (X ⧸ CFSG.pCore p X)).comap
        (QuotientGroup.mk' (CFSG.pCore p X))) := by
  let N := CFSG.pCore p X
  let P := (Subgroup.center (X ⧸ N)).comap (QuotientGroup.mk' N)
  change Group.IsSolvable P
  have hN_le_P : N ≤ P := by
    intro n hn
    rw [Subgroup.mem_comap]
    have h1 : (QuotientGroup.mk' N) n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [h1]
    exact one_mem _
  let f : N →* P := Subgroup.inclusion hN_le_P
  let g : P →* Subgroup.center (X ⧸ N) :=
    ((QuotientGroup.mk' N).comp P.subtype).codRestrict _ (by
      intro p
      exact p.2)
  have hker : g.ker ≤ f.range := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (x : X) ∈ N := by
      have hval : (QuotientGroup.mk' N) (x : X) = 1 := by
        have h1 : ((QuotientGroup.mk' N).comp P.subtype) x = 1 :=
          congrArg Subtype.val hx
        simpa using h1
      exact (QuotientGroup.eq_one_iff (x : X)).mp hval
    exact ⟨⟨x, hx'⟩, rfl⟩
  have hN_solvable : Group.IsSolvable N := by
    have hN_p : IsPGroup p N := CFSG.pCore_isPGroup
    haveI : Group.IsNilpotent N := IsPGroup.isNilpotent hN_p
    exact inferInstance
  have hZ_solvable : Group.IsSolvable (Subgroup.center (X ⧸ N)) := by
    refine Group.isSolvable_of_comm ?_
    intro a b
    exact Subtype.ext ((Subgroup.mem_center_iff.mp a.2 b.val).symm)
  exact Group.isSolvable_of_ker_le_range f g hker

private theorem center_quotient_pCore_eq_bot_of_isPGroup {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (h : IsPGroup p (CFSG.solvableRadical X)) :
    Subgroup.center (X ⧸ CFSG.pCore p X) = ⊥ := by
  let N := CFSG.pCore p X
  let M := CFSG.solvableRadical X
  have hM_le_N : M ≤ N := by
    have hM_normal : M.Normal := inferInstance
    exact le_sSup ⟨hM_normal, h⟩
  let P := (Subgroup.center (X ⧸ N)).comap (QuotientGroup.mk' N)
  have hP_normal : P.Normal := inferInstance
  have hP_solvable : Group.IsSolvable P := isSolvable_comap_center_pCore
  have hP_le_M : P ≤ M := le_sSup ⟨hP_normal, hP_solvable⟩
  have hP_le_N : P ≤ N := hP_le_M.trans hM_le_N
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  obtain ⟨p, hp⟩ := QuotientGroup.mk'_surjective N z
  have hpP : p ∈ P := by
    rw [Subgroup.mem_comap]
    rwa [hp]
  have hpN : p ∈ N := hP_le_N hpP
  rw [← hp]
  exact (QuotientGroup.eq_one_iff p).mpr hpN

theorem map_solvableRadical_eq_center_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (h : IsPGroup p (CFSG.solvableRadical X)) :
    (CFSG.solvableRadical X).map (QuotientGroup.mk' (CFSG.pCore p X)) =
      Subgroup.center (X ⧸ CFSG.pCore p X) := by
  let N := CFSG.pCore p X
  let M := CFSG.solvableRadical X
  have hM_le_N : M ≤ N := by
    have hM_normal : M.Normal := inferInstance
    exact le_sSup ⟨hM_normal, h⟩
  have hL : M.map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hM_le_N
  have hR : Subgroup.center (X ⧸ N) = ⊥ := center_quotient_pCore_eq_bot_of_isPGroup h
  rw [hL, hR]

theorem map_solvableRadical_eq_center_of_oddCore_le_center {X : Type} [Group X] [Finite X]
    (h : CFSG.oddCore (X ⧸ CFSG.pCore 2 X) ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X)) :
    (CFSG.solvableRadical X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := CFSG.pCore 2 X
  have hN : N ≤ CFSG.solvableRadical X := CFSG.pCore_le_solvableRadical 2 X
  have hO2 : CFSG.pCore 2 (X ⧸ N) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hRad : CFSG.solvableRadical (X ⧸ N) ≤ Subgroup.center (X ⧸ N) :=
    CFSG.Timmesfeld.Bridge.Asc72.otg2_solvableRadical_le_center (by rw [hO2]; exact bot_le) h
  have hZ : Subgroup.center (X ⧸ N) ≤ CFSG.solvableRadical (X ⧸ N) := by
    have hcenter_normal : (Subgroup.center (X ⧸ N)).Normal := inferInstance
    have hcenter_solvable : Group.IsSolvable (Subgroup.center (X ⧸ N)) := by
      refine Group.isSolvable_of_comm ?_
      intro a b
      exact Subtype.ext ((Subgroup.mem_center_iff.mp a.2 b.val).symm)
    exact CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      hcenter_normal hcenter_solvable
  have hmap : (CFSG.solvableRadical X).map (QuotientGroup.mk' N) = CFSG.solvableRadical (X ⧸ N) :=
    CFSG.OddTranspositions.PartThree.EightOne.map_solvableRadical_eq hN
  rw [hmap]
  exact le_antisymm hRad hZ

theorem oddCore_le_center_of_map_solvableRadical_eq_center {X : Type} [Group X] [Finite X]
    (h : (CFSG.solvableRadical X).map (QuotientGroup.mk' (CFSG.pCore 2 X)) =
      Subgroup.center (X ⧸ CFSG.pCore 2 X)) :
    CFSG.oddCore (X ⧸ CFSG.pCore 2 X) ≤ Subgroup.center (X ⧸ CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := CFSG.pCore 2 X
  have hO_solvable : Group.IsSolvable (CFSG.oddCore (X ⧸ N)) := by
    have hodd : Odd (Nat.card (CFSG.oddCore (X ⧸ N))) :=
      CFSG.OddTranspositions.PartThree.EightOne.odd_card_oddCore
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hO_le_Rad : CFSG.oddCore (X ⧸ N) ≤ CFSG.solvableRadical (X ⧸ N) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical
      (CFSG.oddCore_normal (X ⧸ N)) hO_solvable
  have hRad_eq : CFSG.solvableRadical (X ⧸ N) = Subgroup.center (X ⧸ N) := by
    have hN : N ≤ CFSG.solvableRadical X := CFSG.pCore_le_solvableRadical 2 X
    have hmap : (CFSG.solvableRadical X).map (QuotientGroup.mk' N) = CFSG.solvableRadical (X ⧸ N) :=
      CFSG.OddTranspositions.PartThree.EightOne.map_solvableRadical_eq hN
    rw [← hmap]
    exact h
  rw [hRad_eq] at hO_le_Rad
  exact hO_le_Rad

end CFSG.OddTranspositions.PartThree.ElevenThree
