module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_centralizer_B_eq {G : Type} [Group G] [Finite G] {B L : Subgroup G} {x : G}
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup 3 S → IsCyclic S) :
    B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x := by
  let S : Subgroup G := B ⊓ Subgroup.centralizer (L : Set G)
  have hSB : S ≤ B := inf_le_left
  have hSle : S ≤ Subgroup.centralizer (L : Set G) := inf_le_right
  have hSpg : IsPGroup 3 S := by
    intro g
    refine ⟨1, ?_⟩
    rw [pow_one]
    apply Subtype.ext
    simpa using hB.2 ((g : S) : G) (hSB g.2)
  have hScyc : IsCyclic S := hcyc S hSle hSpg
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hScyc
  have hg3 : g ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hB.2 ((g : S) : G) (hSB g.2)
  have hgord : orderOf g ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hg3
  have hgordle : orderOf g ≤ 3 := Nat.le_of_dvd (by norm_num) hgord
  have hScard : Nat.card S ≤ 3 := by
    rw [← orderOf_eq_card_of_zpowers_eq_top hg]
    exact hgordle
  have hx3 : x ^ 3 = 1 := hB.2 x hxB
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hxord]
  have hle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr ⟨hxB, hxL⟩
  have hfin : Subgroup.zpowers x = S :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hxcard]; exact hScard)
  change S = Subgroup.zpowers x
  exact hfin.symm

end CFSG.StandardType
