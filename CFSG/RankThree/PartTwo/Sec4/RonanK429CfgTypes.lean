module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hy : e x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx z]
  rw [h, Subgroup.mem_bot] at hy
  exact e.injective (by rw [hy, map_one])

theorem center_eq_bot_of_isSimpleGroup_of_isPerfect {X : Type*} [Group X] [IsSimpleGroup X]
    [Group.IsPerfect X] : Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative X := ⟨⟨fun a b => by
      have ha : a ∈ Subgroup.center X := h ▸ Subgroup.mem_top a
      exact (Subgroup.mem_center_iff.mp ha b).symm⟩⟩
    exact Group.IsPerfect.not_isMulCommutative X hc

theorem center_eq_bot_of_isoLThreePi {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (h : IsoLThreePi X p e) : Subgroup.center X = ⊥ := by
  rcases h with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · exact center_eq_bot_of_mulEquiv φ (Sec13.isPerfect_center_projSL p e he hq).2
  · by_cases hq2 : 2 < p ^ e
    · exact center_eq_bot_of_mulEquiv φ (Sec13.isPerfect_center_projSU p e he hq hq2).2
    · exfalso
      have h2 : p ^ e = 2 := by omega
      obtain ⟨rfl, rfl⟩ := (Nat.prime_two.pow_eq_iff).mp h2
      have hs := Sec13.isSolvable_projSU_two
      have hsolv : IsSolvable X :=
        solvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
      exact Group.IsPerfect.not_isSolvable X hsolv

theorem center_eq_bot_of_isType429
    {X : Type} [Group X] [Finite X] [Group.IsPerfect X]
    [Nontrivial X] (h : IsType429 X) : Subgroup.center X = ⊥ := by
  rcases h with ⟨p, e, hp, he, h⟩ | h | h | h | h
  · exact center_eq_bot_of_isoLThreePi he h
  · obtain ⟨φ⟩ := h
    exact center_eq_bot_of_mulEquiv φ Sec13.isPerfect_center_alt7.2
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup Blueprint.NativeSporadic.M12 :=
      CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    haveI : IsSimpleGroup X := φ.isSimpleGroup
    exact center_eq_bot_of_isSimpleGroup_of_isPerfect
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup Blueprint.NativeSporadic.M22 :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    haveI : IsSimpleGroup X := φ.isSimpleGroup
    exact center_eq_bot_of_isSimpleGroup_of_isPerfect
  · obtain ⟨φ⟩ := h
    haveI : IsSimpleGroup Blueprint.NativeSporadic.J2 := CFSG.Sporadic.J2.isSimpleGroup_J2
    haveI : IsSimpleGroup X := φ.isSimpleGroup
    exact center_eq_bot_of_isSimpleGroup_of_isPerfect

end CFSG.RankThree.PartTwo.Sec4.RonanK429
