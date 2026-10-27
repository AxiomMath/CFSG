module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCentralized
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic
import all Mathlib.GroupTheory.Perm.Cycle.Factors

namespace CFSG
end CFSG
open CFSG

/-!
# The finite `A₇` endpoint `|P₀| = 3`

Every Klein four subgroup `V ≤ A₇` contains an involution `t`.  A `3`-subgroup
`P` centralizing `V` therefore centralizes `t`.  All involutions of `A₇` are
conjugate to the double transposition `a7t = (0 1)(2 3)`, whose centralizer in
`A₇` has order `24`; since `|P|` is a power of `3` dividing `24`, it is at most
`3`.  This avoids a separate classification of the two Klein-four conjugacy
types.
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
  have hrel' : (D.subgroupOf C).index = 2 := hrel
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

private lemma card_le_three_of_three_power_dvd_24 {n : ℕ}
    (h : 3 ^ n ∣ 24) : 3 ^ n ≤ 3 := by
  by_cases hn : n ≤ 1
  · exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hn
  · exfalso
    have h2 : 2 ≤ n := by omega
    have h9 : 9 ∣ 24 := (pow_dvd_pow 3 h2).trans h
    norm_num at h9

/-- If a `3`-subgroup of `A₇` centralizes a Klein four subgroup, then its
cardinality is at most `3`. -/
public theorem aSeven_three_subgroup_centralizing_kleinFour_card_le_three
    {V P : Subgroup (alternatingGroup (Fin 7))}
    (hV : IsKleinFour V)
    (hP : IsPGroup 3 P)
    (hcent : P ≤ Subgroup.centralizer (V : Set (alternatingGroup (Fin 7)))) :
    Nat.card P ≤ 3 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fintype V := Fintype.ofFinite V
  have hlt : 1 < Fintype.card V := by
    rw [← Nat.card_eq_fintype_card, hV.card_four]
    norm_num
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : V)
  let t : A7 := w
  have htmem : t ∈ V := w.property
  have htInv : IsInvolution t := by
    unfold IsInvolution
    constructor
    · intro ht
      apply hwne
      apply Subtype.ext
      simpa [t] using ht
    · have hsq := IsKleinFour.mul_self w
      simpa [t, pow_two] using congrArg Subtype.val hsq
  have hPcentT : P ≤ Subgroup.centralizer ({t} : Set A7) := by
    intro p hp
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hcent hp) t htmem).symm
  obtain ⟨g, hgt⟩ := aSeven_involutions_conjugate t a7t htInv a7t_involution
  let e : A7 ≃* A7 := MulAut.conj g
  let P0 : Subgroup A7 := P.map e.toMonoidHom
  have hP0p : IsPGroup 3 P0 := IsPGroup.map hP e.toMonoidHom
  have hP0cent : P0 ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hx, rfl⟩
    have hconj : e x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set A7) := by
      simpa [e, MulAut.conj_apply] using centralizer_conj_mem g t x (hPcentT hx)
    simpa [hgt] using hconj
  have hdvd24 : Nat.card P0 ∣ 24 := by
    rw [← a7t_centralizer_card]
    exact Subgroup.card_dvd_of_le hP0cent
  obtain ⟨n, hP0card⟩ := hP0p.exists_card_eq
  have hn : n ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ n := by omega
    have hP0card' : Fintype.card P0 = 3 ^ n := by
      simpa [Nat.card_eq_fintype_card] using hP0card
    have hdvd : 3 ^ n ∣ 24 := by simpa [hP0card'] using hdvd24
    have h9 : 9 ∣ 24 := (pow_dvd_pow 3 h2).trans hdvd
    norm_num at h9
  have hP0le : Nat.card P0 ≤ 3 := by
    rw [hP0card]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hn
  have hcardEq : Nat.card P0 = Nat.card P :=
    Subgroup.card_map_of_injective e.injective
  exact hcardEq.symm ▸ hP0le

end CFSG.GorensteinWalter
