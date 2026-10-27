module

public import CFSG.OddTranspositions.SevenOne
public import CFSG.GroupTheory.ConjugacyClassCommuting
public import CFSG.OddTranspositions.F25Carrier
public import CFSG.OddTranspositions.SevenThreeTransitive

public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld.Bridge Asc72 CFSG.Timmesfeld.Connectivity CFSG.GroupTheory
open CFSG.OddTranspositions.QZ

variable {Y : Type} [Group Y] [Finite Y] {Θ : Set Y}

omit [Finite Y] in
theorem localSecond_of_forall_secondKind
    (hsec : ∀ x y t : Y, IsTriangle Θ x y t → orderOf (x * t * y) = 4) : LocalSecond Θ :=
  fun _ _ x y t _ _ _ h => hsec x y t h

theorem not_meetsSq_of_secondKind (hS : Setup Y Θ)
    (hrad : ∀ N : Subgroup Y, N.Normal → Group.IsSolvable N → N = ⊥)
    (hsec : ∀ x y t : Y, IsTriangle Θ x y t → orderOf (x * t * y) = 4) :
    ¬ ∃ u ∈ Θ, ∃ v ∈ Θ, u ≠ v ∧ Commute u v ∧ u * v ∈ Θ := by
  rintro ⟨u, hu, v, hv, huv, hc, huvD⟩
  obtain ⟨e, he, hue⟩ : ∃ e ∈ Θ, ¬ Commute u e := by
    by_contra h
    push Not at h
    have hle : Subgroup.closure Θ ≤ Subgroup.centralizer ({u} : Set Y) := by
      rw [Subgroup.closure_le]
      intro e he
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h e he).symm.eq
    have hcent : u ∈ Subgroup.center Y := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ Subgroup.centralizer ({u} : Set Y) := hle (by rw [hS.gen]; trivial)
      exact (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hZ : Subgroup.center Y = ⊥ :=
      hrad _ inferInstance (Group.isSolvable_of_comm fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
    rw [hZ, Subgroup.mem_bot] at hcent
    exact hS.oddT.ne_one hu hcent
  obtain ⟨h1, h2⟩ := centralizer_eq_of_mul_mem hS hu hv huv hc huvD
  have hve : ¬ Commute v e := by
    intro hve
    have hmem : e ∈ Θ ∩ Subgroup.centralizer ({v} : Set Y) :=
      ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr hve.symm.eq⟩
    rw [← h1] at hmem
    exact hue (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
  have huve : ¬ Commute (u * v) e := by
    intro huve
    have hmem : e ∈ Θ ∩ Subgroup.centralizer ({u * v} : Set Y) :=
      ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr huve.symm.eq⟩
    rw [h2] at hmem
    exact hue (Subgroup.mem_centralizer_singleton_iff.mp hmem.2).symm
  have h4 : orderOf (u * v * e) = 4 := hsec u e v ⟨hu, hv, he, huv, hc, hue, hve⟩
  have hodd : Odd (orderOf (u * v * e)) := hS.oddT.odd_of_not_commute huvD he huve
  rw [h4] at hodd
  exact absurd hodd (by decide)

end CFSG.OddTranspositions

end
