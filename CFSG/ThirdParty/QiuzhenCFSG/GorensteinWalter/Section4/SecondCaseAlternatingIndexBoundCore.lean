module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenInvariantOddPSubgroupCertificateDefs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.A7SylowCentralizer
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the `A₇` component has index at most seven

This module owns the A₇-specific Section 4 route
`secondCase_alternating_index_bound`.  The source pp. 224--226 derives the
structure of `K`, `B`, `F`, `V`, the index-three inclusion
`U∩M ≤ U`, and the per-coset involution bound
`|J ∩ M·y| ≤ 21`, then combines the counts

`|J∩M| = 105`,  `|J| = 35·|G:M|`

to obtain `|G:M| ≤ 7`.  The finite `A₇` facts used there are proved
privately in this file.
-/

noncomputable section

open Matrix
open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

private abbrev A7 := alternatingGroup (Fin 7)

/-- The order of `A₇` is `2520`. -/
private theorem card_alternatingGroupSeven :
    Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card]
  decide

/-- The distinguished double transposition has cycle type `{2,2}`. -/
private theorem a7t_perm_cycleType :
    (a7t : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  show (Equiv.swap (0 : Fin 7) 1 * Equiv.swap 2 3).cycleType = {2, 2}
  exact Equiv.Perm.cycleType_swap_mul_swap_of_nodup (by decide)

/-- The centralizer of a double transposition in `S₇` has order `48`. -/
private theorem a7t_perm_centralizer_card :
    Nat.card (Subgroup.centralizer
      ({(a7t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, a7t_perm_cycleType]
  norm_num

/-- The centralizer of a double transposition in `A₇` has order `24`. -/
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

/-! ## The A₇ reflected cyclic torus -/

/-- An involution of `A₇` that commutes with `a7t` and inverts the
three-cycle `a7a`. -/
private def a7s : A7 :=
  ⟨Equiv.swap (0 : Fin 7) 1 * Equiv.swap (4 : Fin 7) 5, by
    simp [Equiv.Perm.sign_mul]⟩

/-- `a7s` is an involution. -/
private theorem a7s_involution : IsInvolution a7s := by
  constructor <;> decide

/-- `a7s` inverts the generator `a7a`. -/
private theorem a7s_inverts_a7a :
    a7s * a7a * a7s⁻¹ = a7a⁻¹ := by
  decide

/-- `a7s` inverts every integer power of `a7a`. -/
private theorem a7s_inverts_zpow (n : ℤ) :
    a7s * (a7a ^ n) * a7s⁻¹ = (a7a ^ n)⁻¹ := by
  calc
    a7s * (a7a ^ n) * a7s⁻¹ = (MulAut.conj a7s) (a7a ^ n) := by
      simp [MulAut.conj_apply]
    _ = (MulAut.conj a7s) a7a ^ n := map_zpow (MulAut.conj a7s) a7a n
    _ = (a7a⁻¹) ^ n := by
      rw [show (MulAut.conj a7s) a7a = a7a⁻¹ by
        simpa [MulAut.conj_apply] using a7s_inverts_a7a]
    _ = (a7a ^ n)⁻¹ := by
      rw [inv_zpow]

/-- The cyclic subgroup generated by `a7a` is a reflected torus in the
centralizer of `a7t`. -/
private theorem a7_reflected_cyclicTorus :
    ∃ T : Subgroup A7, ∃ s : A7,
      IsCyclic T ∧ T ≠ ⊥ ∧ Nat.card T = 3 ∧
        s ∉ T ∧ IsInvolution s ∧
          (∀ x : A7, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
            T ≤ Subgroup.centralizer ({a7t} : Set A7) := by
  let T : Subgroup A7 := Subgroup.zpowers a7a
  refine ⟨T, a7s, ?_⟩
  have hTcyc : IsCyclic T := by
    let : IsCyclic (↥T) := Subgroup.isCyclic_zpowers a7a
    exact inferInstance
  have hTne : T ≠ ⊥ := by
    intro hbot
    have ha : a7a ∈ T := Subgroup.mem_zpowers a7a
    have ha1 : a7a = 1 := Subgroup.mem_bot.mp (by simpa [hbot] using ha)
    exact (by decide : a7a ≠ 1) ha1
  have hTcard : Nat.card T = 3 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime <;> decide
  have hs_not_T : a7s ∉ T := by
    intro hsT
    have hord_s : orderOf a7s = 2 := by
      apply orderOf_eq_prime
      · exact a7s_involution.2
      · exact a7s_involution.1
    have hdvd : orderOf a7s ∣ Nat.card T :=
      Subgroup.orderOf_dvd_natCard T hsT
    rw [hord_s, hTcard] at hdvd
    norm_num at hdvd
  have hinvT : ∀ x : A7, x ∈ T → a7s * x * a7s⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, hn⟩
    rw [← hn]
    exact a7s_inverts_zpow n
  have hTcent : T ≤ Subgroup.centralizer ({a7t} : Set A7) := by
    change Subgroup.zpowers a7a ≤ Subgroup.centralizer ({a7t} : Set A7)
    exact (Subgroup.zpowers_le).2 (by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hyT : y = a7t := by simpa using hy
      subst y
      decide)
  exact ⟨hTcyc, hTne, hTcard, hs_not_T, a7s_involution, hinvT, hTcent⟩

/-! ## The coset-fiber count for the index bound -/

/-- If the base coset contains `105` involutions, every other coset contains
at most `21`, and the total number of involutions is `35·|Ω|`, then
`|Ω| ≤ 7`.  This is the aggregate of the Section 4 count. -/
public theorem secondCase_index_le_seven_of_involution_fibers
    {G : Type u} [Group G] [Finite G]
    {Ω : Type u} [Fintype Ω]
    (π : G → Ω) (ω0 : Ω)
    (hbase : Nat.card {x : G // IsInvolution x ∧ π x = ω0} = 105)
    (hbound : ∀ ω : Ω, ω ≠ ω0 →
      Nat.card {x : G // IsInvolution x ∧ π x = ω} ≤ 21)
    (htotal : Nat.card {x : G // IsInvolution x} = 35 * Nat.card Ω) :
    Nat.card Ω ≤ 7 := by
  classical
  let fiber : Ω → Type u := fun ω => {x : G // IsInvolution x ∧ π x = ω}
  have htotalSum : Nat.card {x : G // IsInvolution x} = ∑ ω : Ω, Nat.card (fiber ω) := by
    let e : {x : G // IsInvolution x} ≃ Σ ω : Ω, fiber ω :=
      { toFun := fun x => ⟨π x.1, ⟨x.1, x.2, rfl⟩⟩
        invFun := fun p => ⟨p.2.1, p.2.2.1⟩
        left_inv := by intro x; rfl
        right_inv := by
          rintro ⟨ω, ⟨x, hx, hω⟩⟩
          subst ω
          rfl }
    exact Nat.card_congr e |>.trans Nat.card_sigma
  let s : Finset Ω := Finset.univ.erase ω0
  have hnonbase :
      (∑ ω ∈ s, Nat.card (fiber ω)) ≤ 21 * (Nat.card Ω - 1) := by
    have hs_card : s.card = Fintype.card Ω - 1 :=
      Finset.card_erase_of_mem (Finset.mem_univ ω0)
    have hs_le : s.card ≤ Nat.card Ω - 1 := by
      rw [hs_card]
      simp [Nat.card_eq_fintype_card]
    calc
      (∑ ω ∈ s, Nat.card (fiber ω)) ≤ ∑ ω ∈ s, 21 := by
        apply Finset.sum_le_sum
        intro ω _hω
        exact hbound ω (Finset.mem_erase.mp _hω).1
      _ = 21 * s.card := by
        rw [Finset.sum_const]
        simp [nsmul_eq_mul, mul_comm]
      _ ≤ 21 * (Nat.card Ω - 1) :=
        Nat.mul_le_mul_left 21 hs_le
  have hbaseSum :
      Nat.card (fiber ω0) + (∑ ω ∈ s, Nat.card (fiber ω)) =
        ∑ ω : Ω, Nat.card (fiber ω) := by
    have hErase := Finset.sum_erase_add Finset.univ
      (fun ω : Ω => Nat.card (fiber ω)) (Finset.mem_univ ω0)
    calc
      Nat.card (fiber ω0) +
          (∑ ω ∈ s, Nat.card (fiber ω)) =
          (∑ ω ∈ s, Nat.card (fiber ω)) + Nat.card (fiber ω0) := by
        rw [add_comm]
      _ = ∑ ω : Ω, Nat.card (fiber ω) := by
        exact hErase
  have htotal' : Nat.card {x : G // IsInvolution x} =
      Nat.card (fiber ω0) +
        (∑ ω ∈ s, Nat.card (fiber ω)) := by
    rw [htotalSum, hbaseSum]
  have hle : 35 * Nat.card Ω ≤ 105 + 21 * (Nat.card Ω - 1) := by
    calc
      35 * Nat.card Ω = Nat.card {x : G // IsInvolution x} := htotal.symm
      _ = Nat.card (fiber ω0) +
          (∑ ω ∈ s, Nat.card (fiber ω)) := htotal'
      _ ≤ 105 + 21 * (Nat.card Ω - 1) := by
        exact Nat.add_le_add (le_of_eq (by simpa [fiber] using hbase)) hnonbase
  omega

/-- The index of a finite subgroup is the cardinality of its coset space. -/
private theorem index_eq_card_quotient
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) :
    H.index = Nat.card (G ⧸ H) :=
  @Subgroup.index_eq_card G _ H

/-! ## The Section 4 count data -/

/-- The three counts that the A₇ branch produces before the final estimate:
the total involution count, the base-coset count, and the per-coset bound
for cosets represented by an involution outside `M`. -/
public structure SecondCaseA7CountData
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) where
  involutions_card : Nat.card {x : G // IsInvolution x} = 35 * M.index
  base_involutions_card :
    Nat.card {x : G // IsInvolution x ∧ x ∈ M} = 105
  coset_involutions_bound :
    ∀ y : G, IsInvolution y → y ∉ M →
      Nat.card {x : G // IsInvolution x ∧
        x ∈ (M : Set G) * ({y} : Set G)} ≤ 21

/-- The fiber of the involution map `x ↦ x⁻¹ mod M` over the base coset is
exactly the involutions lying in `M`. -/
private theorem base_fiber_card_eq
    {G : Type u} [Group G] [Finite G] (M : Subgroup G) :
    Nat.card {x : G // IsInvolution x ∧
        QuotientGroup.mk (s := M) (x⁻¹ : G) =
          QuotientGroup.mk (s := M) (1 : G)} =
      Nat.card {x : G // IsInvolution x ∧ x ∈ M} := by
  apply Nat.card_congr
  refine ⟨fun x => ⟨x.1, x.2.1, ?_⟩, fun x => ⟨x.1, x.2.1, ?_⟩, ?_, ?_⟩
  · have hx : QuotientGroup.mk (s := M) (x.1⁻¹ : G) =
        QuotientGroup.mk (s := M) (1 : G) := x.2.2
    have hm : (x.1⁻¹)⁻¹ * (1 : G) ∈ M := (QuotientGroup.eq (s := M)).mp hx
    simpa using hm
  · have hx : x.1 ∈ M := x.2.2
    exact (QuotientGroup.eq (s := M)).mpr (by simpa using hx)
  · intro x
    rfl
  · intro x
    rfl

/-- For an involution `y ∉ M`, the fiber over `y⁻¹ mod M` consists exactly
of the involutions in the coset `M·y`. -/
private theorem nonbase_fiber_card_eq
    {G : Type u} [Group G] [Finite G] (M : Subgroup G)
    {y : G} (hy : IsInvolution y) (hyM : y ∉ M) :
    Nat.card {x : G // IsInvolution x ∧
        QuotientGroup.mk (s := M) (x⁻¹ : G) =
          QuotientGroup.mk (s := M) (y⁻¹ : G)} =
      Nat.card {x : G // IsInvolution x ∧
        x ∈ (M : Set G) * ({y} : Set G)} := by
  apply Nat.card_congr
  refine ⟨fun x => ⟨x.1, x.2.1, ?_⟩, fun x => ⟨x.1, x.2.1, ?_⟩, ?_, ?_⟩
  · have hx : QuotientGroup.mk (s := M) (x.1⁻¹ : G) =
        QuotientGroup.mk (s := M) (y⁻¹ : G) := x.2.2
    have hm : x.1 * y⁻¹ ∈ M := by
      simpa using (QuotientGroup.eq (s := M)).mp hx
    exact Set.mem_mul.mpr ⟨x.1 * y⁻¹, hm, y, by simp, by group⟩
  · rcases x.2.2 with ⟨m, hmM, z, hz, hxz⟩
    have hzy : z = y := by simpa using hz
    subst z
    have hxy : x.1 = m * y := hxz.symm
    rw [hxy]
    apply (QuotientGroup.eq (s := M)).mpr
    simpa [mul_assoc] using hmM
  · intro x
    rfl
  · intro x
    rfl

/-- The Section 4 counts imply `|G:M| ≤ 7`. -/
public theorem index_le_seven_of_countData
    {G : Type u} [Group G] [Finite G]
    (M : Subgroup G) (d : SecondCaseA7CountData M) :
    M.index ≤ 7 := by
  classical
  let Ω := G ⧸ M
  let π : G → Ω := fun x => QuotientGroup.mk (s := M) (x⁻¹ : G)
  let ω0 : Ω := π 1
  let : Fintype Ω := Fintype.ofFinite Ω
  have hbase : Nat.card {x : G // IsInvolution x ∧ π x = ω0} = 105 := by
    have h := base_fiber_card_eq (G := G) M
    -- unfold π/ω0 in h and replace by d.base_involutions_card
    simpa [π, ω0] using h.trans d.base_involutions_card
  have hbound : ∀ ω : Ω, ω ≠ ω0 →
      Nat.card {x : G // IsInvolution x ∧ π x = ω} ≤ 21 := by
    intro ω hω
    by_cases hnonempty : ∃ x : G, IsInvolution x ∧ π x = ω
    · rcases hnonempty with ⟨y, hy, hyω⟩
      have hyM : y ∉ M := by
        intro hyM
        apply hω
        rw [← hyω]
        apply (QuotientGroup.eq (s := M)).mpr
        simpa using hyM
      have hcard := nonbase_fiber_card_eq (G := G) M hy hyM
      have hcard' : Nat.card {x : G // IsInvolution x ∧ π x = ω} =
          Nat.card {x : G // IsInvolution x ∧
            x ∈ (M : Set G) * ({y} : Set G)} := by
        simpa [π, hyω] using hcard
      rw [hcard']
      exact d.coset_involutions_bound y hy hyM
    · have hcard0 : Nat.card {x : G // IsInvolution x ∧ π x = ω} = 0 := by
        have : IsEmpty {x : G // IsInvolution x ∧ π x = ω} :=
          ⟨fun x => hnonempty ⟨x.1, x.2.1, x.2.2⟩⟩
        exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
      rw [hcard0]
      norm_num
  have htotal : Nat.card {x : G // IsInvolution x} = 35 * Nat.card Ω := by
    have hindex : M.index = Nat.card Ω := index_eq_card_quotient M
    rw [← hindex]
    exact d.involutions_card
  have hle := secondCase_index_le_seven_of_involution_fibers
    (G := G) (Ω := Ω) π ω0 hbase hbound htotal
  rw [← index_eq_card_quotient (G := G) M] at hle
  exact hle

end CFSG.GorensteinWalter
