module

public import CFSG.Quasithin.Background.RonanE628RBorel

public section

namespace CFSG.Quasithin.RonanE628.MathAS4

open CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem not_uniqueSmallModel_of_normal_elemAbelian
    (T : Sylow 2 G) {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hVT : V ≤ (T : Subgroup G))
    (hN : (T : Subgroup G) ≤ Subgroup.normalizer (V : Set G)) (hV2 : 2 < Nat.card V) :
    ¬ CFSG.QuasithinUnique.UniqueSmallModel G := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ConjCrit ↥(T : Subgroup G) → False := by
    intro hc
    obtain ⟨z, hz⟩ := hc
    have hsub : (V : Set G) ⊆ ({1, (z : G)} : Set G) := fun v hv =>
      mem_pair_of_conjCrit hV hVT hN hz hv
    have hcard : Nat.card V ≤ 2 := by
      rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
      exact (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
    omega
  rintro (⟨p, hp, hp7, hpF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩)
  · haveI : Finite PSL(2, ZMod p) := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_psl2 hp hp7 hpF
    exact key (conjCrit_sylow_of_mulEquiv e Q hQ T)
  · haveI : Finite PSL(3, ZMod 3) := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_psl33
    exact key (conjCrit_sylow_of_mulEquiv e Q hQ T)
  · haveI : Finite ↥M11 := Finite.of_equiv G e.toEquiv
    obtain ⟨Q, hQ⟩ := conjCrit_m11
    exact key (conjCrit_sylow_of_mulEquiv e Q hQ T)

end CFSG.Quasithin.RonanE628.MathAS4
