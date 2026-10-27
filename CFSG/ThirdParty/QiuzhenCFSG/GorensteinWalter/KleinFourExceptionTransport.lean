module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourAlternatingEndpoint
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourCentralizerTransport
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise

universe u

public theorem isCyclic_subgroupOf
    {G : Type*} [Group G] {M A : Subgroup G}
    (hAM : A ≤ M) (hAcyc : IsCyclic A) :
    IsCyclic (A.subgroupOf M) := by
  let : IsCyclic A := hAcyc
  exact (Subgroup.subgroupOfEquivOfLe hAM).isCyclic.mpr
    (inferInstance : IsCyclic A)

public theorem subgroupOf_ne_bot
    {G : Type*} [Group G] [Finite G] {M A : Subgroup G}
    (hAM : A ≤ M) (hAne : A ≠ ⊥) :
    A.subgroupOf M ≠ ⊥ := by
  intro hbot
  have hcard : Nat.card (A.subgroupOf M) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  have hgt : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
  have hone : Nat.card (A.subgroupOf M) = 1 := by rw [hbot]; simp
  rw [hcard] at hone
  omega

public theorem subgroupOf_odd_card
    {G : Type*} [Group G] [Finite G] {M A : Subgroup G}
    (hAM : A ≤ M) (hAodd : Odd (Nat.card A)) :
    Odd (Nat.card (A.subgroupOf M)) := by
  have hcard : Nat.card (A.subgroupOf M) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
  rw [hcard]
  exact hAodd

public theorem isKleinFour_subgroupOf
    {G : Type*} [Group G] {M V : Subgroup G}
    (hVM : V ≤ M) (hVK : IsKleinFour V) :
    IsKleinFour (V.subgroupOf M) := by
  let eV : V.subgroupOf M ≃* V := Subgroup.subgroupOfEquivOfLe hVM
  refine ⟨?_, ?_⟩
  · have hc := Nat.card_congr eV.toEquiv
    rw [hVK.card_four] at hc
    exact hc
  · have hexp : Monoid.exponent (V.subgroupOf M) = Monoid.exponent V :=
      Monoid.exponent_eq_of_mulEquiv eV
    exact hexp.trans hVK.exponent_two

public theorem centralizer_subgroupOf_le
    {G : Type*} [Group G] {M A V : Subgroup G}
    (hAM : A ≤ M) (hVM : V ≤ M)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    V.subgroupOf M ≤
      Subgroup.centralizer ((A.subgroupOf M : Subgroup M) : Set M) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hxV : (x : G) ∈ V := by
    simpa using (Subgroup.mem_subgroupOf.mp hx)
  have haA : (a : G) ∈ A := by
    simpa using (Subgroup.mem_subgroupOf.mp ha)
  have hcomm : (a : G) * (x : G) = (x : G) * (a : G) :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hxV)) (a : G) haA
  exact Subtype.ext hcomm

public theorem no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_alternatingGroup_four
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 4))
    (A V : Subgroup G)
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  let A' : Subgroup (alternatingGroup (Fin 4)) := A.map e.toMonoidHom
  let V' : Subgroup (alternatingGroup (Fin 4)) := V.map e.toMonoidHom
  let eA : A ≃* A' := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  have hA'cyc : IsCyclic A' := by
    let : IsCyclic A := hAcyc
    exact eA.isCyclic.mp (inferInstance : IsCyclic A)
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    have hgt : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
    have hone : Nat.card A' = 1 := by rw [hbot]; simp
    rw [← hcard] at hone
    omega
  have hA'odd : Odd (Nat.card A') := by
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    rw [hcard] at hAodd
    exact hAodd
  have hV'K : IsKleinFour V' := isKleinFour_map_mulEquiv_cross V hVK e
  have hV'leC : V' ≤ Subgroup.centralizer (A' : Set (alternatingGroup (Fin 4))) := by
    simpa [A', V'] using centralizer_map_le_of_mulEquiv e A V hVleC
  exact no_kleinFour_centralizes_odd_cyclic_alternatingGroup_four
    A' V' hA'cyc hA'ne hA'odd hV'K hV'leC

public theorem no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_alternatingGroup_five
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* alternatingGroup (Fin 5))
    (A V : Subgroup G)
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  let A' : Subgroup (alternatingGroup (Fin 5)) := A.map e.toMonoidHom
  let V' : Subgroup (alternatingGroup (Fin 5)) := V.map e.toMonoidHom
  let eA : A ≃* A' := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  have hA'cyc : IsCyclic A' := by
    let : IsCyclic A := hAcyc
    exact eA.isCyclic.mp (inferInstance : IsCyclic A)
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    have hgt : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
    have hone : Nat.card A' = 1 := by rw [hbot]; simp
    rw [← hcard] at hone
    omega
  have hA'odd : Odd (Nat.card A') := by
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    rw [hcard] at hAodd
    exact hAodd
  have hV'K : IsKleinFour V' := isKleinFour_map_mulEquiv_cross V hVK e
  have hV'leC : V' ≤ Subgroup.centralizer (A' : Set (alternatingGroup (Fin 5))) := by
    simpa [A', V'] using centralizer_map_le_of_mulEquiv e A V hVleC
  exact no_kleinFour_centralizes_odd_cyclic_alternatingGroup_five
    A' V' hA'cyc hA'ne hA'odd hV'K hV'leC

public theorem no_kleinFour_centralizes_odd_cyclic_of_mulEquiv_perm_four
    {G : Type u} [Group G] [Finite G]
    (e : G ≃* Equiv.Perm (Fin 4))
    (A V : Subgroup G)
    (hAcyc : IsCyclic A) (hAne : A ≠ ⊥)
    (hAodd : Odd (Nat.card A))
    (hVK : IsKleinFour V)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  let A' : Subgroup (Equiv.Perm (Fin 4)) := A.map e.toMonoidHom
  let V' : Subgroup (Equiv.Perm (Fin 4)) := V.map e.toMonoidHom
  let eA : A ≃* A' := Subgroup.equivMapOfInjective A e.toMonoidHom e.injective
  have hA'cyc : IsCyclic A' := by
    let : IsCyclic A := hAcyc
    exact eA.isCyclic.mp (inferInstance : IsCyclic A)
  have hA'ne : A' ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    have hgt : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
    have hone : Nat.card A' = 1 := by rw [hbot]; simp
    rw [← hcard] at hone
    omega
  have hA'odd : Odd (Nat.card A') := by
    have hcard : Nat.card A = Nat.card A' := Nat.card_congr eA.toEquiv
    rw [hcard] at hAodd
    exact hAodd
  have hV'K : IsKleinFour V' := isKleinFour_map_mulEquiv_cross V hVK e
  have hV'leC : V' ≤ Subgroup.centralizer (A' : Set (Equiv.Perm (Fin 4))) := by
    simpa [A', V'] using centralizer_map_le_of_mulEquiv e A V hVleC
  exact no_kleinFour_centralizes_odd_cyclic_perm_four
    A' V' hA'cyc hA'ne hA'odd hV'K hV'leC

end CFSG.GorensteinWalter
