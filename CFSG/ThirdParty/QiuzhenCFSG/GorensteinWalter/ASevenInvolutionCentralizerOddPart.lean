module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic
import all Mathlib.GroupTheory.Perm.Cycle.Factors

namespace CFSG
end CFSG
open CFSG

/-!
# Odd part of an involution centralizer in `A₇`

Every involution of `A₇` is conjugate to the double transposition
`a7t = (0 1)(2 3)`.  Its centralizer in `A₇` has order `24`, so an odd-order
subgroup `P` centralizing any involution has order dividing both `24` and an
odd number; hence `|P| ∣ 3` and in particular `|P| ≤ 3`.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

private abbrev A7 := alternatingGroup (Fin 7)

private theorem a7t_involution : IsInvolution a7t := by
  unfold IsInvolution
  constructor <;> decide

private theorem a7t_perm_cycleType :
    (a7t : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  decide

private theorem a7t_perm_centralizer_card :
    Nat.card (Subgroup.centralizer
      ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, a7t_perm_cycleType]
  norm_num

/-- The centralizer of the concrete double transposition in `A₇` has order
`24`. -/
private theorem a7t_centralizer_card :
    Nat.card (Subgroup.centralizer ({a7t} : Set A7)) = 24 := by
  let C : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
  let A : Subgroup (Equiv.Perm (Fin 7)) := alternatingGroup (Fin 7)
  have hAindex : A.index = 2 := alternatingGroup.index_eq_two
  have hcC : (Equiv.swap (4 : Fin 7) 5) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
    subst y
    decide
  have hcA : (Equiv.swap (4 : Fin 7) 5) ∉ A := by
    intro h
    change Equiv.Perm.sign (Equiv.swap (4 : Fin 7) 5) = 1 at h
    norm_num [Equiv.Perm.sign_swap] at h
    all_goals exact (by decide : (4 : Fin 7) ≠ 5) h
  let D : Subgroup (Equiv.Perm (Fin 7)) := Lattice.inf C A
  have hrel : D.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨Equiv.swap (4 : Fin 7) 5, hcC, ?_⟩
    intro b hbC
    have hbcC : b * Equiv.swap (4 : Fin 7) 5 ∈ C := C.mul_mem hbC hcC
    by_cases hbA : b ∈ A
    · right
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbC, hbA⟩
      · intro hbc
        have hbcA : b * Equiv.swap (4 : Fin 7) 5 ∈ A :=
          (Subgroup.mem_inf.mp hbc).2
        have hiff : b * Equiv.swap (4 : Fin 7) 5 ∈ A ↔
            (b ∈ A ↔ Equiv.swap (4 : Fin 7) 5 ∈ A) :=
          Subgroup.mul_mem_iff_of_index_two hAindex
        have hbnot : ¬ b ∈ A := by
          intro hbA'
          exact hcA ((hiff.mp hbcA).1 hbA')
        exact hbnot hbA
    · left
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbcC, by
          exact (Subgroup.mul_mem_iff_of_index_two hAindex).2
            (iff_of_false hbA hcA)⟩
      · intro hbD
        exact hbA ((Subgroup.mem_inf.mp hbD).2)
  have hrel' : (D.subgroupOf C).index = 2 := by
    exact hrel
  have hperm : Nat.card C = 48 := a7t_perm_centralizer_card
  have hDleC : D ≤ C := inf_le_left
  have hcardSub : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleC).toEquiv
  have hcardC : Nat.card D * 2 = Nat.card C := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [hcardSub, hrel'] at h
    exact h
  have hcard24 : Nat.card D = 24 := by omega
  have hmap : (Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype = D := by
    ext p
    constructor
    · rintro ⟨x, hxC, rfl⟩
      constructor
      · change (x : Equiv.Perm (Fin 7)) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyP : y = (a7t : Equiv.Perm (Fin 7)) := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) a7t (by simp)
        exact congrArg Subtype.val hcomm
      · exact x.2
    · rintro ⟨hpC, hpA⟩
      refine ⟨⟨p, hpA⟩, ?_, rfl⟩
      have hx : (⟨p, hpA⟩ : A7) ∈ Subgroup.centralizer ({a7t} : Set A7) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyA : y = a7t := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpC)
          (a7t : Equiv.Perm (Fin 7)) (by simp)
        exact Subtype.ext hcomm
      exact hx
  have hcardMap : Nat.card (Subgroup.centralizer ({a7t} : Set A7)) =
      Nat.card ((Subgroup.centralizer ({a7t} : Set A7)).map A7.subtype) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({a7t} : Set A7)) A7.subtype
        A7.subtype_injective).toEquiv
  rw [hcardMap, hmap, hcard24]

private lemma centralizer_conj_mem
    {G : Type*} [Group G] (g t x : G)
    (hx : x ∈ Subgroup.centralizer ({t} : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc
    (g * x * g⁻¹) * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
    _ = g * (t * x) * g⁻¹ := by rw [hx]
    _ = (g * t * g⁻¹) * (g * x * g⁻¹) := by group

private lemma odd_dvd_24_dvd_three {n : ℕ} (hn : Odd n) (h : n ∣ 24) :
    n ∣ 3 := by
  have hnpos : 0 < n := Nat.pos_of_dvd_of_pos h (by norm_num)
  have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num : 0 < 24) h
  interval_cases n
  all_goals try norm_num at hn
  all_goals try norm_num at h
  all_goals try norm_num

/-- An odd-order subgroup of `A₇` centralizing an involution has order at most
`3`. -/
public theorem aSeven_odd_subgroup_centralizing_involution_card_le_three
    {P : Subgroup (alternatingGroup (Fin 7))}
    (hPodd : Odd (Nat.card P))
    {t : alternatingGroup (Fin 7)} (ht : IsInvolution t)
    (hcent : P ≤ Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) :
    Nat.card P ≤ 3 := by
  classical
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate t a7t ht a7t_involution
  let e : A7 ≃* A7 := MulAut.conj g
  let P0 : Subgroup A7 := P.map e.toMonoidHom
  have hP0cent : P0 ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hconj : e x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set A7) := by
      simpa [e, MulAut.conj_apply] using centralizer_conj_mem g t x (hcent hx)
    simpa [hgt] using hconj
  have hdvd24 : Nat.card P0 ∣ 24 := by
    rw [← a7t_centralizer_card]
    exact Subgroup.card_dvd_of_le hP0cent
  have hcardEq : Nat.card P0 = Nat.card P :=
    Subgroup.card_map_of_injective e.injective
  have hP0odd : Odd (Nat.card P0) := by
    rwa [hcardEq]
  have hP0dvd3 : Nat.card P0 ∣ 3 := odd_dvd_24_dvd_three hP0odd hdvd24
  have hP0le : Nat.card P0 ≤ 3 :=
    Nat.le_of_dvd (by norm_num : 0 < 3) hP0dvd3
  exact hcardEq.symm ▸ hP0le

end CFSG.GorensteinWalter
