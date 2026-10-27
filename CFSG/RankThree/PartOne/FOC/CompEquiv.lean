module

public import CFSG.RankThree.PartOne.FOC.Assemble
public import CFSG.RankThree.PartOne.FOC.Equiv
import CFSG.RankThree.PartOne.S11c.Sec66TFamily
import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL
import CFSG.RankThree.PartOne.S11d.LieGoodConclusion

public section

namespace CFSG.RankThree.PartOne.FOC

open Subgroup CFSG
open CFSG.RankThree.PartOne.Sec66T (fixSub innerAut fixSub_congr mem_innerAut_congr)

section Transport

variable {T T' : Type} [Group T] [Finite T] [Group T'] [Finite T']

theorem InnerComp.of_mulEquiv (e : T ≃* T') {p : ℕ} (hp : p.Prime) (h : InnerComp p T') :
    InnerComp p T := by
  intro hLR b y hbp hyp hby E hE
  have hLR' := Sec66T.localRankLeTwo_of_mulEquiv e hp hLR
  have hcent : (Subgroup.centralizer ({b} : Set T)).map e.toMonoidHom =
      Subgroup.centralizer ({e b} : Set T') := by
    ext g
    rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      apply e.symm.injective
      rw [map_mul, map_mul, e.symm_apply_apply]
      exact hg
    · intro hg
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg
  have hE' : IsComponentOf (Subgroup.centralizer ({e b} : Set T')) (E.map e.toMonoidHom) := by
    rw [← hcent]
    exact isComponentOf_map_mulEquiv e hE
  have hmem := h hLR' (e b) (e y) (by rw [← map_pow, hbp, map_one])
    (by rw [← map_pow, hyp, map_one]) (by rw [← map_mul, ← map_mul, hby]) _ hE'
  obtain ⟨a, ha, c, hc, hac⟩ := PlaneInner.exists_mul_of_mem_sup_centralizer hmem
  have ha' : e.symm a ∈ E := Subgroup.mem_map_equiv.mp ha
  have hc' : e.symm c ∈ Subgroup.centralizer (E : Set T) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact Subgroup.mem_centralizer_iff.mp hc (e k) ⟨k, hk, rfl⟩
  have hy : y = e.symm a * e.symm c := by
    apply e.injective
    rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
    exact hac
  rw [hy]
  exact Subgroup.mul_mem_sup ha' hc'

theorem OuterComp.of_mulEquiv (e : T ≃* T') {p : ℕ} (hp : p.Prime) (h : OuterComp p T') :
    OuterComp p T := by
  intro hLR β hβp hβout hLRA y hβy hyp E hE
  have hE' := isComponentOf_map_mulEquiv e hE
  rw [← fixSub_congr e β] at hE'
  have hmem := h (Sec66T.localRankLeTwo_of_mulEquiv e hp hLR) (MulAut.congr e β)
    (by rw [← map_pow, hβp, map_one])
    (fun hmem => hβout ((mem_innerAut_congr e β).mp hmem)) (localRankAut_of_equiv e hp hLRA) (e y)
    (by
      show e (β (e.symm (e y))) = e y
      rw [e.symm_apply_apply, hβy])
    (by rw [← map_pow, hyp, map_one]) _ hE'
  have h2 := Subgroup.mem_map_equiv.mp hmem
  simpa using h2

end Transport

section Abstract

variable {P : Type} [Group P] [Finite P]

theorem outerComp_of_descent {p : ℕ} (hp : p.Prime) (E D : Subgroup (MulAut P))
    (hE : ∀ β : MulAut P, β ^ p = 1 → β ∈ E)
    (hD : ∀ β ∈ D, β ^ p = 1 → β ∈ innerAut P)
    (hdesc : ∀ a ∈ E, a ∉ D → orderOf a = p → ∃ (P' : Type) (_ : Group P') (Θ : P ≃* P')
      (a' : MulAut P'), MulAut.congr Θ a = a' ∧
        ∀ y ∈ fixSub a', y ^ p = 1 → ∀ F : Subgroup P', IsComponentOf (fixSub a') F → y ∈ F) :
    OuterComp p P := by
  have : Fact p.Prime := ⟨hp⟩
  intro _ β hβp hβout _ y hβy hyp F hF
  have hβ1 : β ≠ 1 := fun h1 => hβout (h1 ▸ (innerAut P).one_mem)
  have hord : orderOf β = p := orderOf_eq_prime hβp hβ1
  have hβE : β ∈ E := hE β hβp
  have hβD : β ∉ D := fun hD' => hβout (hD β hD' hβp)
  obtain ⟨P', _, Θ, a', hΘ, hcl⟩ := hdesc β hβE hβD hord
  have hF' := isComponentOf_map_mulEquiv Θ hF
  have hfix : fixSub a' = (fixSub β).map Θ.toMonoidHom := by
    rw [← hΘ]
    exact fixSub_congr Θ β
  rw [← hfix] at hF'
  have hy' : Θ y ∈ fixSub a' := by
    rw [hfix]
    exact ⟨y, hβy, rfl⟩
  have := hcl (Θ y) hy' (by rw [← map_pow, hyp, map_one]) _ hF'
  have h2 := Subgroup.mem_map_equiv.mp this
  simpa using h2

end Abstract

end CFSG.RankThree.PartOne.FOC
