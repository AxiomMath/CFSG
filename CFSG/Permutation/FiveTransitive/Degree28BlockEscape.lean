module

public import CFSG.Permutation.FiveTransitive.Degree28DiagonalEscape
public import CFSG.Permutation.FiveTransitive.PrimeCyclicFixedAction
public import CFSG.Permutation.FiveTransitive.LargePrimeNormalizer
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.GroupTheory.SpecificGroups.ZGroup

public section

namespace CFSG

namespace FiveTransitive.Degree28BlockEscape

open Equiv
open scoped Pointwise

private theorem cycle_factor_support_card_eq_three
    {X : Type*} [Fintype X] [DecidableEq X]
    {r : Equiv.Perm X} (hr : orderOf r = 3)
    (c : r.cycleFactorsFinset) :
    c.1.support.card = 3 := by
  have hp : Nat.Prime (orderOf r) := by
    rw [hr]
    norm_num
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order hp
  have hmem : c.1.support.card ∈ r.cycleType := by
    rw [Equiv.Perm.cycleType_def]
    exact Multiset.mem_map.mpr
      ⟨c.1, c.2, rfl⟩
  rw [hn, hr] at hmem
  rw [Multiset.mem_replicate] at hmem
  exact hmem.2

@[expose] def fixedPart
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X))) :
    Equiv.Perm (Function.fixedPoints r) :=
  (u.1 : Equiv.Perm X).subtypePerm fun _ =>
    Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer u.2

@[simp] theorem fixedPart_apply
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (x : Function.fixedPoints r) :
    ((fixedPart r u x : Function.fixedPoints r) : X) = u.1 x :=
  rfl

abbrev cyclePart
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X))) :
    Equiv.Perm r.cycleFactorsFinset :=
  Equiv.Perm.OnCycleFactors.toPermHom r u

private abbrev FixedCycleFactors
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X))) :=
  Function.fixedPoints (cyclePart r u)

private theorem cycleFactorsFinset_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) :
    Fintype.card r.cycleFactorsFinset = r.cycleType.card := by
  rw [Fintype.card_coe, Equiv.Perm.cycleType_def,
    Multiset.card_map]
  rfl

private theorem fixedCycleFactors_card_eq_four
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hrCycles : r.cycleType.card = 7)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    Fintype.card (FixedCycleFactors r u) = 4 := by
  rw [Equiv.Perm.card_fixedPoints, huCycles.cycleType,
    cycleFactorsFinset_card, hrCycles]
  norm_num

@[expose] noncomputable def cycleBasis
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) : r.Basis :=
  Classical.choice (Equiv.Perm.Basis.nonempty r)

private theorem centralizer_maps_fixed_cycle_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (c : FixedCycleFactors r u) {x : X}
    (hx : x ∈ c.1.1.support) :
    u.1 x ∈ c.1.1.support := by
  have hconj :
      u.1 * c.1.1 * u.1⁻¹ = c.1.1 := by
    calc
      u.1 * c.1.1 * u.1⁻¹ =
          ((cyclePart r u c.1 : r.cycleFactorsFinset) :
            Equiv.Perm X) :=
        (Equiv.Perm.OnCycleFactors.coe_toPermHom r u c.1).symm
      _ = c.1.1 := congrArg Subtype.val c.2
  have hux : u.1 x ∈ (u.1 * c.1.1 * u.1⁻¹).support := by
    rw [Equiv.Perm.support_conj]
    simp [hx]
  rwa [hconj] at hux

private theorem exists_shift_fixing_cycle_basis
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (c : FixedCycleFactors r u) :
    ∃ k : Fin 3,
      (u.1 * r ^ (k : ℕ)) (cycleBasis r c.1) =
        cycleBasis r c.1 := by
  let x : X := cycleBasis r c.1
  have hx : x ∈ c.1.1.support :=
    (cycleBasis r).mem_support_self c.1
  have hux : u.1 x ∈ c.1.1.support :=
    centralizer_maps_fixed_cycle_support r u c hx
  obtain ⟨n, hnlt, hn⟩ :=
    (Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.1.2).exists_pow_eq
      hux hx
  have hnltThree : n < 3 := by
    simpa [cycle_factor_support_card_eq_three hr c.1] using hnlt
  refine ⟨⟨n, hnltThree⟩, ?_⟩
  change (u.1 * r ^ n) x = x
  have hcomm : Commute u.1 r :=
    Subgroup.mem_centralizer_singleton_iff.mp u.2
  rw [(hcomm.pow_right n).eq]
  exact hn

private noncomputable def fixedCycleShift
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (c : FixedCycleFactors r u) : Fin 3 :=
  Classical.choose (exists_shift_fixing_cycle_basis r u hr c)

private theorem fixedCycleShift_spec
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (c : FixedCycleFactors r u) :
    (u.1 * r ^ (fixedCycleShift r u hr c : ℕ))
        (cycleBasis r c.1) = cycleBasis r c.1 :=
  Classical.choose_spec (exists_shift_fixing_cycle_basis r u hr c)

private theorem exists_shift_fixing_two_cycle_bases
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (hrCycles : r.cycleType.card = 7)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    ∃ k : Fin 3,
      2 ≤ (Finset.univ.filter fun c : FixedCycleFactors r u =>
        fixedCycleShift r u hr c = k).card := by
  obtain ⟨k, hk⟩ :=
    Fintype.exists_lt_card_fiber_of_mul_lt_card
      (fixedCycleShift r u hr) (n := 1) (by
        rw [fixedCycleFactors_card_eq_four r u hrCycles huCycles]
        norm_num)
  refine ⟨k, ?_⟩
  omega

private theorem shifted_centralizer_fixes_fixed_cycle
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (k : Fin 3)
    (c : FixedCycleFactors r u)
    (hbase :
      (u.1 * r ^ (k : ℕ)) (cycleBasis r c.1) =
        cycleBasis r c.1) :
    ∀ x ∈ c.1.1.support,
      (u.1 * r ^ (k : ℕ)) x = x := by
  intro x hx
  let a : X := cycleBasis r c.1
  have ha : a ∈ c.1.1.support :=
    (cycleBasis r).mem_support_self c.1
  obtain ⟨n, _, hn⟩ :=
    (Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset c.1.2).exists_pow_eq
      ha hx
  have hur : Commute u.1 r :=
    Subgroup.mem_centralizer_singleton_iff.mp u.2
  have hshiftComm : Commute (u.1 * r ^ (k : ℕ)) r :=
    hur.mul_left ((Commute.refl r).pow_left (k : ℕ))
  calc
    (u.1 * r ^ (k : ℕ)) x =
        (u.1 * r ^ (k : ℕ)) ((r ^ n) a) := by rw [hn]
    _ = (r ^ n) ((u.1 * r ^ (k : ℕ)) a) := by
      change ((u.1 * r ^ (k : ℕ)) * r ^ n) a =
        (r ^ n * (u.1 * r ^ (k : ℕ))) a
      rw [(hshiftComm.pow_right n).eq]
    _ = (r ^ n) a := by rw [hbase]
    _ = x := hn

private theorem centralizer_pow_nine_eq_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (huFixed : (fixedPart r u).IsThreeCycle)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    u.1 ^ 9 = 1 := by
  classical
  have hr3 : r ^ 3 = 1 := by
    simpa [hr] using pow_orderOf_eq_one r
  have huFixed3 : (fixedPart r u) ^ 3 = 1 := by
    simpa [huFixed.orderOf] using pow_orderOf_eq_one (fixedPart r u)
  have huCycles3 : (cyclePart r u) ^ 3 = 1 := by
    simpa [huCycles.orderOf] using pow_orderOf_eq_one (cyclePart r u)
  have hu3Ker :
      u ^ 3 ∈ (Equiv.Perm.OnCycleFactors.toPermHom r).ker := by
    rw [MonoidHom.mem_ker]
    simpa only [map_pow] using huCycles3
  apply Equiv.ext
  intro x
  by_cases hx : r x = x
  · let y : Function.fixedPoints r := ⟨x, hx⟩
    let huPreserves : ∀ z : X,
        u.1 z ∈ Function.fixedPoints r ↔ z ∈ Function.fixedPoints r :=
      fun _ => Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer u.2
    have huRestricted3 : (u.1.subtypePerm huPreserves) ^ 3 = 1 := by
      simpa only [fixedPart] using huFixed3
    rw [Equiv.Perm.subtypePerm_pow] at huRestricted3
    have happ := congrArg
      (fun e : Equiv.Perm (Function.fixedPoints r) => e y)
      huRestricted3
    have happVal := congrArg Subtype.val happ
    have hu3x : (u.1 ^ 3) x = x := by
      simpa using happVal
    have hpow := Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hu3x 3
    simpa [← pow_mul] using hpow
  · have hxr : x ∈ r.support := Equiv.Perm.mem_support.mpr hx
    let c : r.cycleFactorsFinset :=
      ⟨r.cycleOf x,
        Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hxr⟩
    have hxc : x ∈ c.1.support := by
      exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
        r c.1 c.2 x).mp rfl
    have hu3Comm : Commute ((u ^ 3 :
        Subgroup.centralizer ({r} : Set (Equiv.Perm X))) :
          Equiv.Perm X) c.1 :=
      (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff r (u ^ 3)).mp
        hu3Ker c.1 c.2
    obtain ⟨hu3Preserves, hu3Rotation⟩ :=
      (Equiv.Perm.commute_iff_of_mem_cycleFactorsFinset c.2).mp hu3Comm
    let hrPreserves : ∀ z : X, r z ∈ c.1.support ↔ z ∈ c.1.support :=
      fun z => Equiv.Perm.mem_cycleFactorsFinset_support c.2 z
    let rCycle : Equiv.Perm c.1.support :=
      r.subtypePerm hrPreserves
    have hrCycle3 : rCycle ^ 3 = 1 := by
      rw [Equiv.Perm.subtypePerm_pow]
      apply Equiv.ext
      intro z
      apply Subtype.ext
      change (r ^ 3) z.1 = z.1
      rw [hr3]
      rfl
    let v : Equiv.Perm X :=
      ((u ^ 3 : Subgroup.centralizer
        ({r} : Set (Equiv.Perm X))) : Equiv.Perm X)
    change v.subtypePerm hu3Preserves ∈ Subgroup.zpowers rCycle at hu3Rotation
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu3Rotation
    have hu3Restricted3 :
        ((v.subtypePerm hu3Preserves) ^ 3) = 1 := by
      rw [← hm]
      calc
        (rCycle ^ m) ^ 3 =
            (rCycle ^ m) ^ (3 : ℤ) :=
          (zpow_natCast (rCycle ^ m) 3).symm
        _ = rCycle ^ (m * 3) := (zpow_mul rCycle m 3).symm
        _ = rCycle ^ (3 * m) := by rw [mul_comm]
        _ = (rCycle ^ (3 : ℤ)) ^ m := zpow_mul rCycle 3 m
        _ = 1 := by simp [zpow_natCast, hrCycle3]
    have happ := congrArg
      (fun e : Equiv.Perm c.1.support => e ⟨x, hxc⟩)
      hu3Restricted3
    have happVal := congrArg Subtype.val happ
    rw [Equiv.Perm.subtypePerm_apply_pow_of_mem hu3Preserves hxc] at happVal
    simpa [v, ← pow_mul] using happVal

private theorem shifted_centralizer_pow_nine_eq_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (huFixed : (fixedPart r u).IsThreeCycle)
    (huCycles : (cyclePart r u).IsThreeCycle)
    (k : Fin 3) :
    (u.1 * r ^ (k : ℕ)) ^ 9 = 1 := by
  have hur : Commute u.1 r :=
    Subgroup.mem_centralizer_singleton_iff.mp u.2
  have hr9 : r ^ 9 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (by rw [hr]; norm_num)
  rw [(hur.pow_right (k : ℕ)).mul_pow]
  rw [centralizer_pow_nine_eq_one r u hr huFixed huCycles]
  have hrk9 : (r ^ (k : ℕ)) ^ 9 = 1 := by
    rw [pow_right_comm]
    simp [hr9]
  simp [hrk9]

private theorem shifted_centralizer_ne_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (huFixed : (fixedPart r u).IsThreeCycle)
    (k : ℕ) :
    u.1 * r ^ k ≠ 1 := by
  intro hshift
  apply huFixed.ne_one
  apply Equiv.ext
  intro y
  apply Subtype.ext
  change u.1 y.1 = y.1
  have happ := congrArg (fun e : Equiv.Perm X => e y.1) hshift
  have hrky : (r ^ k) y.1 = y.1 :=
    Equiv.Perm.pow_apply_eq_self_of_apply_eq_self y.2 k
  simpa only [Equiv.Perm.mul_apply, hrky, Equiv.Perm.one_apply] using happ

private theorem exists_shift_with_support_le_eighteen
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (hrFixed : Fintype.card (Function.fixedPoints r) = 7)
    (hrCycles : r.cycleType.card = 7)
    (huFixed : (fixedPart r u).IsThreeCycle)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    ∃ k : Fin 3,
      (u.1 * r ^ (k : ℕ)).support.card ≤ 18 := by
  classical
  obtain ⟨k, hk⟩ :=
    exists_shift_fixing_two_cycle_bases
      r u hr hrCycles huCycles
  let S : Finset (FixedCycleFactors r u) :=
    Finset.univ.filter fun c => fixedCycleShift r u hr c = k
  let fixedEmbedding :
      Function.fixedPoints (fixedPart r u) ↪ X :=
    (Function.Embedding.subtype _).trans (Function.Embedding.subtype _)
  let A : Finset X := Finset.univ.map fixedEmbedding
  let T : Finset X :=
    S.biUnion fun c => c.1.1.support
  let h : Equiv.Perm X := u.1 * r ^ (k : ℕ)
  have hScard : 2 ≤ S.card := by
    simpa only [S] using hk
  have hAcard : A.card = 4 := by
    calc
      A.card = Fintype.card
          (Function.fixedPoints (fixedPart r u)) := by
        simp [A, fixedEmbedding]
      _ = Fintype.card (Function.fixedPoints r) - 3 := by
        rw [Equiv.Perm.card_fixedPoints, huFixed.cycleType]
        norm_num
      _ = 4 := by omega
  have hTcard : T.card = 3 * S.card := by
    change (S.biUnion fun c => c.1.1.support).card = 3 * S.card
    rw [Finset.card_biUnion]
    · simp_rw [cycle_factor_support_card_eq_three hr]
      simp [Nat.mul_comm]
    · intro c hc d hd hcd
      apply Finset.disjoint_left.mpr
      intro x hxc hxd
      have hfactorNe : c.1.1 ≠ d.1.1 := by
        intro heq
        apply hcd
        apply Subtype.ext
        exact Subtype.ext heq
      have hdisjoint :=
        r.cycleFactorsFinset_pairwise_disjoint
          c.1.2 d.1.2 hfactorNe
      exact Finset.disjoint_left.mp
        (Equiv.Perm.Disjoint.disjoint_support hdisjoint) hxc hxd
  have hAT : Disjoint A T := by
    rw [Finset.disjoint_left]
    intro x hxA hxT
    change x ∈ Finset.univ.map fixedEmbedding at hxA
    rw [Finset.mem_map] at hxA
    obtain ⟨y, -, rfl⟩ := hxA
    change (y.1 : X) ∈ S.biUnion (fun c => c.1.1.support) at hxT
    rw [Finset.mem_biUnion] at hxT
    obtain ⟨c, -, hyc⟩ := hxT
    have hyrSupport : (y.1 : X) ∈ r.support :=
      Equiv.Perm.mem_cycleFactorsFinset_support_le c.1.2 hyc
    exact Equiv.Perm.mem_support.mp hyrSupport y.1.2
  have hAfix : ∀ x ∈ A, h x = x := by
    intro x hx
    change x ∈ Finset.univ.map fixedEmbedding at hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, -, rfl⟩ := hx
    have hry : r (y.1 : X) = y.1 := y.1.2
    have hrky : (r ^ (k : ℕ)) (y.1 : X) = y.1 :=
      Equiv.Perm.pow_apply_eq_self_of_apply_eq_self hry _
    have huy : u.1 (y.1 : X) = y.1 := by
      exact congrArg Subtype.val y.2
    change (u.1 * r ^ (k : ℕ)) (y.1 : X) = y.1
    rw [Equiv.Perm.mul_apply, hrky, huy]
  have hTfix : ∀ x ∈ T, h x = x := by
    intro x hx
    change x ∈ S.biUnion (fun c => c.1.1.support) at hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨c, hcS, hxc⟩ := hx
    have hcShift : fixedCycleShift r u hr c = k := by
      simpa [S] using hcS
    have hbase := fixedCycleShift_spec r u hr c
    rw [hcShift] at hbase
    exact shifted_centralizer_fixes_fixed_cycle
      r u k c hbase x hxc
  have hUnionCard : 10 ≤ (A ∪ T).card := by
    rw [Finset.card_union_of_disjoint hAT, hAcard, hTcard]
    omega
  have hUnionSupport : Disjoint (A ∪ T) h.support := by
    rw [Finset.disjoint_left]
    intro x hxU hxsupport
    have hxfix : h x = x := by
      rcases Finset.mem_union.mp hxU with hxA | hxT
      · exact hAfix x hxA
      · exact hTfix x hxT
    exact Equiv.Perm.mem_support.mp hxsupport hxfix
  have htotal : (A ∪ T).card + h.support.card ≤ Fintype.card X := by
    rw [← Finset.card_union_of_disjoint hUnionSupport]
    exact Finset.card_le_univ _
  refine ⟨k, ?_⟩
  change h.support.card ≤ 18
  rw [hX] at htotal
  omega

private theorem exists_shift_with_support_le_eighteen_pow_nine_ne_one
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hr : orderOf r = 3)
    (hrFixed : Fintype.card (Function.fixedPoints r) = 7)
    (hrCycles : r.cycleType.card = 7)
    (huFixed : (fixedPart r u).IsThreeCycle)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    ∃ k : Fin 3,
      (u.1 * r ^ (k : ℕ)).support.card ≤ 18 ∧
      (u.1 * r ^ (k : ℕ)) ^ 9 = 1 ∧
      u.1 * r ^ (k : ℕ) ≠ 1 := by
  obtain ⟨k, hk⟩ :=
    exists_shift_with_support_le_eighteen
      hX r u hr hrFixed hrCycles huFixed huCycles
  exact ⟨k, hk,
    shifted_centralizer_pow_nine_eq_one
      r u hr huFixed huCycles k,
    shifted_centralizer_ne_one r u huFixed k⟩

theorem five_stabilizer_card_eq
    (X : Type*) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s t : Set X) (hs : s.ncard = 5) (ht : t.ncard = 5) :
    Nat.card (fixingSubgroup P s) =
      Nat.card (fixingSubgroup P t) := by
  classical
  letI : Fintype s := Fintype.ofFinite s
  letI : Fintype t := Fintype.ofFinite t
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hs]
  have htCard : Fintype.card t = 5 := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, ht]
  let es : s ≃ Fin 5 := Fintype.equivFinOfCardEq hsCard
  let et : t ≃ Fin 5 := Fintype.equivFinOfCardEq htCard
  let a : Fin 5 ↪ X :=
    { toFun := fun i => (es.symm i).1
      inj' := fun i j hij => es.symm.injective (Subtype.ext hij) }
  let b : Fin 5 ↪ X :=
    { toFun := fun i => (et.symm i).1
      inj' := fun i j hij => et.symm.injective (Subtype.ext hij) }
  have haRange : Set.range a = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ := es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  have hbRange : Set.range b = t := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (et.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ := et.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q, hq⟩ := h5 a b a.injective b.injective
  have hqRange : q • s = t := by
    rw [← haRange, ← hbRange, Set.smul_set_range]
    congr 1
    funext i
    exact hq i
  exact Nat.card_congr
    (SubMulAction.fixingSubgroupEquivFixingSubgroup hqRange).toEquiv

private theorem exists_order_three_support_le_eighteen_mem_of_global_lift
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (r : Equiv.Perm X)
    (u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hrP : r ∈ P) (huP : u.1 ∈ P)
    (hr : orderOf r = 3)
    (hrFixed : Fintype.card (Function.fixedPoints r) = 7)
    (hrCycles : r.cycleType.card = 7)
    (huFixed : (fixedPart r u).IsThreeCycle)
    (huCycles : (cyclePart r u).IsThreeCycle) :
    ∃ g : Equiv.Perm X,
      g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  classical
  obtain ⟨k, hsupport, hpow, hne⟩ :=
    exists_shift_with_support_le_eighteen_pow_nine_ne_one
      hX r u hr hrFixed hrCycles huFixed huCycles
  let g : Equiv.Perm X := u.1 * r ^ (k : ℕ)
  have hgP : g ∈ P :=
    P.mul_mem huP (P.pow_mem hrP (k : ℕ))
  have hsupportG : g.support.card ≤ 18 := by
    simpa only [g] using hsupport
  have hcomplCard : g.supportᶜ.card = 28 - g.support.card := by
    rw [Finset.card_compl, hX]
  have hfiveCompl : 5 ≤ g.supportᶜ.card := by
    rw [hcomplCard]
    omega
  obtain ⟨tFin, htSub, htCard⟩ :=
    Finset.exists_subset_card_eq hfiveCompl
  let t : Set X := (tFin : Set X)
  have ht : t.ncard = 5 := by
    simpa only [t, Set.ncard_coe_finset] using htCard
  let gP : P := ⟨g, hgP⟩
  have hgFix : ∀ x ∈ t, gP • x = x := by
    intro x hxt
    change x ∈ tFin at hxt
    have hxCompl : x ∈ g.supportᶜ := htSub hxt
    rw [Finset.mem_compl] at hxCompl
    change g x = x
    simpa only [Equiv.Perm.mem_support, not_not] using hxCompl
  let gT : fixingSubgroup P t :=
    ⟨gP, (mem_fixingSubgroup_iff P).mpr hgFix⟩
  have hgTPow : gT ^ 9 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact hpow
  have hgTNe : gT ≠ 1 := by
    intro hgOne
    apply hne
    have hcoe := congrArg
      (fun z : fixingSubgroup P t =>
        (((z : fixingSubgroup P t) : P) : Equiv.Perm X)) hgOne
    exact hcoe
  have hnineS : ¬9 ∣ Nat.card (fixingSubgroup P s) := by
    intro hnine
    obtain ⟨a, ha⟩ := hnine
    have hindexCard := S.index_mul_card
    rw [hScard] at hindexCard
    apply S.not_dvd_index
    refine ⟨a, ?_⟩
    omega
  have hnineT : ¬9 ∣ Nat.card (fixingSubgroup P t) := by
    rw [← five_stabilizer_card_eq X P h5 s t hs ht]
    exact hnineS
  have hgTOrder : orderOf gT = 3 := by
    have hordNine : orderOf gT ∣ 3 ^ 2 := by
      norm_num
      exact orderOf_dvd_of_pow_eq_one hgTPow
    obtain ⟨j, hj, hord⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hordNine
    interval_cases j
    · norm_num at hord
      exact (hgTNe hord).elim
    · simpa using hord
    · exfalso
      apply hnineT
      simpa [hord] using (orderOf_dvd_natCard gT)
  have hgOrder : orderOf g = 3 := by
    calc
      orderOf g = orderOf gP :=
        by simpa only [gP] using Subgroup.orderOf_coe gP
      _ = orderOf gT := by
        simpa only [gT] using Subgroup.orderOf_coe gT
      _ = 3 := hgTOrder
  exact ⟨g, hgP, hgOrder, hsupportG⟩

private theorem exists_order_three_support_le_eighteen_of_subdirect_centralizer
    {X : Type*} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (r : Equiv.Perm X) (hrP : r ∈ P)
    (hr : orderOf r = 3)
    (hrFixed : Fintype.card (Function.fixedPoints r) = 7)
    (hrCycles : r.cycleType.card = 7)
    (L : Type*) [Group L] [Finite L]
    (incl : L →*
      Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hinclP : ∀ l : L, (incl l).1 ∈ P)
    (fixedMap : L →* alternatingGroup (Function.fixedPoints r))
    (cycleMap : L →* alternatingGroup r.cycleFactorsFinset)
    (hfixedSurj : Function.Surjective fixedMap)
    (hcycleSurj : Function.Surjective cycleMap)
    (hfixedCompat : ∀ l : L,
      ((fixedMap l : alternatingGroup (Function.fixedPoints r)) :
          Equiv.Perm (Function.fixedPoints r)) =
        fixedPart r (incl l))
    (hcycleCompat : ∀ l : L,
      ((cycleMap l : alternatingGroup r.cycleFactorsFinset) :
          Equiv.Perm r.cycleFactorsFinset) =
        cyclePart r (incl l)) :
    ∃ g : Equiv.Perm X,
      g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  have hcycleCard : Fintype.card r.cycleFactorsFinset = 7 := by
    rw [cycleFactorsFinset_card, hrCycles]
  obtain ⟨l, hlFixed, hlCycles⟩ :=
    Degree28DiagonalEscape.exists_lift_threeCycle_both_of_surjective_alternating
      hrFixed hcycleCard L fixedMap cycleMap hfixedSurj hcycleSurj
  let u : Subgroup.centralizer ({r} : Set (Equiv.Perm X)) := incl l
  have huFixed : (fixedPart r u).IsThreeCycle := by
    rw [← hfixedCompat l]
    exact hlFixed
  have huCycles : (cyclePart r u).IsThreeCycle := by
    rw [← hcycleCompat l]
    exact hlCycles
  exact
    exists_order_three_support_le_eighteen_mem_of_global_lift
      hX P h5 s hs S hScard r u hrP (hinclP l)
        hr hrFixed hrCycles huFixed huCycles

private theorem exists_order_three_support_le_eighteen_of_solvable_aux_actions
    {X : Type} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (r : Equiv.Perm X) (hrP : r ∈ P)
    (hr : orderOf r = 3)
    (hrFixed : Fintype.card (Function.fixedPoints r) = 7)
    (hrCycles : r.cycleType.card = 7)
    (N B : Type) [Group N] [Finite N]
    [Group B] [Finite B] [Group.IsSolvable B]
    (fixedRaw : N →* Equiv.Perm (Function.fixedPoints r))
    (cycleRaw : N →* Equiv.Perm r.cycleFactorsFinset)
    (auxBase : N →* B)
    (centerIncl : auxBase.ker →*
      Subgroup.centralizer ({r} : Set (Equiv.Perm X)))
    (hcenterP : ∀ z : auxBase.ker, (centerIncl z).1 ∈ P)
    (hfixedCompat : ∀ z : auxBase.ker,
      fixedRaw z.1 = fixedPart r (centerIncl z))
    (hcycleCompat : ∀ z : auxBase.ker,
      cycleRaw z.1 = cyclePart r (centerIncl z))
    (hAltFixed :
      alternatingGroup (Function.fixedPoints r) ≤ fixedRaw.range)
    (hAltCycles :
      alternatingGroup r.cycleFactorsFinset ≤ cycleRaw.range) :
    ∃ g : Equiv.Perm X,
      g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  classical
  let fixedSign : N →* ℤˣ := Equiv.Perm.sign.comp fixedRaw
  let cycleSign : N →* ℤˣ := Equiv.Perm.sign.comp cycleRaw
  let aux : N →* (B × ℤˣ) × ℤˣ :=
    (auxBase.prod fixedSign).prod cycleSign
  let K : Subgroup N := aux.ker
  let toBase : K →* auxBase.ker :=
    { toFun := fun z => ⟨z.1, by
        rw [MonoidHom.mem_ker]
        have hz := MonoidHom.mem_ker.mp z.2
        have hzBase := congrArg
          (fun w : (B × ℤˣ) × ℤˣ => w.1.1) hz
        simpa [aux] using hzBase⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let fixedKBase : K →* Equiv.Perm (Function.fixedPoints r) :=
    fixedRaw.comp K.subtype
  have hfixedEven : ∀ z : K, fixedKBase z ∈
      alternatingGroup (Function.fixedPoints r) := by
    intro z
    rw [Equiv.Perm.mem_alternatingGroup]
    have hz := MonoidHom.mem_ker.mp z.2
    have hzSign := congrArg
      (fun w : (B × ℤˣ) × ℤˣ => w.1.2) hz
    simpa [aux, fixedSign, fixedKBase] using hzSign
  let fixedK : K →* alternatingGroup (Function.fixedPoints r) :=
    fixedKBase.codRestrict
      (alternatingGroup (Function.fixedPoints r)) hfixedEven
  let cycleKBase : K →* Equiv.Perm r.cycleFactorsFinset :=
    cycleRaw.comp K.subtype
  have hcycleEven : ∀ z : K, cycleKBase z ∈
      alternatingGroup r.cycleFactorsFinset := by
    intro z
    rw [Equiv.Perm.mem_alternatingGroup]
    have hz := MonoidHom.mem_ker.mp z.2
    have hzSign := congrArg
      (fun w : (B × ℤˣ) × ℤˣ => w.2) hz
    simpa [aux, cycleSign, cycleKBase] using hzSign
  let cycleK : K →* alternatingGroup r.cycleFactorsFinset :=
    cycleKBase.codRestrict
      (alternatingGroup r.cycleFactorsFinset) hcycleEven
  letI : IsSimpleGroup
      (alternatingGroup (Function.fixedPoints r)) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, hrFixed]
      norm_num)
  have hcycleCard : Fintype.card r.cycleFactorsFinset = 7 := by
    rw [cycleFactorsFinset_card, hrCycles]
  letI : IsSimpleGroup (alternatingGroup r.cycleFactorsFinset) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card, hcycleCard]
      norm_num)
  letI : Group.IsPerfect
      (alternatingGroup (Function.fixedPoints r)) := by
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top (by
      rw [Nat.card_eq_fintype_card, hrFixed]
      norm_num)
  letI : Group.IsPerfect
      (alternatingGroup r.cycleFactorsFinset) := by
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top (by
      rw [Nat.card_eq_fintype_card, hcycleCard]
      norm_num)
  have hfixedNonsolvable :
      ¬Group.IsSolvable
        (alternatingGroup (Function.fixedPoints r)) :=
    Group.IsPerfect.not_isSolvable _
  have hcycleNonsolvable :
      ¬Group.IsSolvable
        (alternatingGroup r.cycleFactorsFinset) :=
    Group.IsPerfect.not_isSolvable _
  have hfixedSurj : Function.Surjective fixedK := by
    intro q
    obtain ⟨n, hnFixed, hnAux⟩ :=
      FiveTransitive.SolvableOrbitGoursat.exists_lift_with_solvable_aux_eq_one
        N (Equiv.Perm (Function.fixedPoints r))
          ((B × ℤˣ) × ℤˣ) fixedRaw aux
          (alternatingGroup (Function.fixedPoints r))
          hAltFixed hfixedNonsolvable q.1 q.2
    let z : K := ⟨n, MonoidHom.mem_ker.mpr hnAux⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hnFixed
  have hcycleSurj : Function.Surjective cycleK := by
    intro q
    obtain ⟨n, hnCycle, hnAux⟩ :=
      FiveTransitive.SolvableOrbitGoursat.exists_lift_with_solvable_aux_eq_one
        N (Equiv.Perm r.cycleFactorsFinset)
          ((B × ℤˣ) × ℤˣ) cycleRaw aux
          (alternatingGroup r.cycleFactorsFinset)
          hAltCycles hcycleNonsolvable q.1 q.2
    let z : K := ⟨n, MonoidHom.mem_ker.mpr hnAux⟩
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hnCycle
  let inclK : K →*
      Subgroup.centralizer ({r} : Set (Equiv.Perm X)) :=
    centerIncl.comp toBase
  exact exists_order_three_support_le_eighteen_of_subdirect_centralizer
    hX P h5 s hs S hScard r hrP hr hrFixed hrCycles
    K inclK (fun z => hcenterP (toBase z))
    fixedK cycleK hfixedSurj hcycleSurj
    (fun z => by
      change fixedRaw z.1 = fixedPart r (centerIncl (toBase z))
      exact hfixedCompat (toBase z))
    (fun z => by
      change cycleRaw z.1 = cyclePart r (centerIncl (toBase z))
      exact hcycleCompat (toBase z))

abbrev cyclicConjugation
    {X : Type*} (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      MulAut (FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r) :=
  (FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r).normalizerMonoidHom

@[expose] def cyclicConjugationKernelToCentralizer
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    (cyclicConjugation P r).ker →*
      Subgroup.centralizer
        ({((r : P) : Equiv.Perm X)} : Set (Equiv.Perm X)) where
  toFun z := ⟨(((z.1 :
      FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r) : P) :
        Equiv.Perm X), by
    rw [Subgroup.mem_centralizer_singleton_iff]
    let R := FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r
    let N := FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r
    have hzCentral : (z.1 : N) ∈
        (Subgroup.centralizer (R : Set P)).subgroupOf N := by
      rw [← R.normalizerMonoidHom_ker]
      exact z.2
    have hcommP : Commute ((z.1 : N) : P) r :=
      (hzCentral r (Subgroup.mem_zpowers r)).symm
    exact congrArg Subtype.val hcommP.eq⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

@[expose] def cyclicFixedEquivGeneratorFixed
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r ≃
      Function.fixedPoints ((r : P) : Equiv.Perm X) :=
  Set.equivOfEq
    (FiveTransitive.PrimeCyclicFixedAction.fixedPoints_eq_fixedPoints_generator
      X P r)

private noncomputable def cyclicNormalizerFixedHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      Equiv.Perm (Function.fixedPoints ((r : P) : Equiv.Perm X)) :=
  (cyclicFixedEquivGeneratorFixed P r).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom
      (FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
      (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r))

private theorem cyclicNormalizerFixedHom_ker_compat
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P)
    (z : (cyclicConjugation P r).ker) :
    cyclicNormalizerFixedHom P r z.1 =
      fixedPart ((r : P) : Equiv.Perm X)
        (cyclicConjugationKernelToCentralizer P r z) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

private theorem alternatingGroup_le_cyclicNormalizerFixedHom_range
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (r : P)
    (hRSP :
      FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r =
        FiveTransitive.Degree24.sylowImage X P s S)
    (hfixed : Fintype.card
      (Function.fixedPoints ((r : P) : Equiv.Perm X)) = 7) :
    alternatingGroup
        (Function.fixedPoints ((r : P) : Equiv.Perm X)) ≤
      (cyclicNormalizerFixedHom P r).range := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let R : Subgroup P :=
    FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r
  let N : Subgroup P :=
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r
  let F :=
    MulAction.fixedPoints (R.subgroupOf N) X
  let Y := Function.fixedPoints ((r : P) : Equiv.Perm X)
  let e : F ≃ Y :=
    Set.equivOfEq
      (FiveTransitive.PrimeCyclicFixedAction.fixedPoints_eq_fixedPoints_generator
        X P r)
  let J : Subgroup (Equiv.Perm Y) :=
    (cyclicNormalizerFixedHom P r).range
  have hNfive :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : N, ∀ i, q • a i = b i := by
    let SP : Subgroup P :=
      FiveTransitive.Degree24.sylowImage X P s S
    have htransport
        (R' : Subgroup P) (hR' : R' = SP) :
        ∀ a b : Fin 5 →
            MulAction.fixedPoints
              (R'.subgroupOf
                (Subgroup.normalizer (R' : Set P))) X,
          Function.Injective a → Function.Injective b →
          ∃ q : Subgroup.normalizer (R' : Set P),
            ∀ i, q • a i = b i := by
      subst R'
      simpa only [SP,
        FiveTransitive.Degree24.sylowFixedPoints,
        FiveTransitive.Degree24.sylowInNormalizer,
        FiveTransitive.Degree24.sylowNormalizer] using
        (FiveTransitive.LargePrimeNormalizer.sylowNormalizer_transitive_on_fixedPoints
          X P hdegree h5 (k := 5) (by norm_num) s hs S)
    simpa only [F, N, R] using htransport R (by
      simpa only [SP, R] using hRSP)
  have hJfive :
      ∀ a b : Fin 5 → Y, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    let aF : Fin 5 → F := fun i => e.symm (a i)
    let bF : Fin 5 → F := fun i => e.symm (b i)
    have haF : Function.Injective aF := e.symm.injective.comp ha
    have hbF : Function.Injective bF := e.symm.injective.comp hb
    obtain ⟨q, hq⟩ := hNfive aF bF haF hbF
    let qJ : J :=
      ⟨cyclicNormalizerFixedHom P r q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    apply Subtype.ext
    have hqi := congrArg Subtype.val (hq i)
    change
      (((q : N) : P) : Equiv.Perm X) (a i).1 = (b i).1
    change
      (((q : N) : P) : Equiv.Perm X) (a i).1 = (b i).1 at hqi
    exact hqi
  have hJpre : MulAction.IsMultiplyPretransitive J Y 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ := hJfive a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact congrArg Subtype.val (hq i)
  have hdegreeFive : Nat.card Y - 2 = 5 := by
    rw [Nat.card_eq_fintype_card]
    have hYcard : Fintype.card Y = 7 := by
      simpa only [Y] using hfixed
    rw [hYcard]
  have hJdegree :
      MulAction.IsMultiplyPretransitive J Y (Nat.card Y - 2) := by
    rwa [hdegreeFive]
  exact IsMultiplyPretransitive.alternatingGroup_le Y J hJdegree

@[expose] def supportRestriction
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) : Equiv.Perm r.support :=
  r.subtypePerm fun _ => Equiv.Perm.apply_mem_support

abbrev supportOrbitQuotient
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) :=
  MulAction.orbitRel.Quotient
    (Subgroup.zpowers (supportRestriction r)) r.support

@[expose] noncomputable def cycleFactorsEquivSupportOrbitQuotient
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) :
    r.cycleFactorsFinset ≃ supportOrbitQuotient r := by
  classical
  let a : r.Basis := cycleBasis r
  let rp : Equiv.Perm r.support := supportRestriction r
  have haSupport (c : r.cycleFactorsFinset) : a c ∈ r.support :=
    Equiv.Perm.mem_cycleFactorsFinset_support_le
      c.2 (a.mem_support_self c)
  let f : r.cycleFactorsFinset → supportOrbitQuotient r :=
    fun c => Quotient.mk''
      (⟨a c, haSupport c⟩ : r.support)
  apply Equiv.ofBijective f
  constructor
  · intro c d hcd
    have hrel :
        MulAction.orbitRel (Subgroup.zpowers rp) r.support
          (⟨a c, haSupport c⟩ : r.support)
          (⟨a d, haSupport d⟩ : r.support) :=
      Quotient.exact hcd
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨z, hz⟩ := hrel
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp z.prop
    apply Subtype.ext
    rw [← Equiv.Perm.Basis.cycleOf_eq a c,
      ← Equiv.Perm.Basis.cycleOf_eq a d]
    have hzVal := congrArg Subtype.val hz
    change
      ((z : Equiv.Perm r.support)
        (⟨a d, haSupport d⟩ : r.support)).1 = a c at hzVal
    rw [← hzVal]
    change r.cycleOf
        (((z : Equiv.Perm r.support)
          (⟨a d, haSupport d⟩ : r.support)).1) =
      r.cycleOf (a d)
    rw [← hm]
    have hpowVal :=
      Equiv.Perm.subtypePerm_apply_zpow_of_mem
        (g := r) (s := r.support)
        (fun _ => Equiv.Perm.apply_mem_support)
        (x := a d) (i := m) (haSupport d)
    change r.cycleOf
        (((rp ^ m) (⟨a d, haSupport d⟩ : r.support)).1) =
      r.cycleOf (a d)
    rw [show
      ((rp ^ m) (⟨a d, haSupport d⟩ : r.support)).1 =
        (r ^ m) (a d) by simpa only [rp, supportRestriction] using hpowVal]
    rw [Equiv.Perm.cycleOf_self_apply_zpow]
  · intro q
    induction q using Quotient.inductionOn'
    rename_i x
    have hfactor : r.cycleOf x.1 ∈ r.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr x.2
    let c : r.cycleFactorsFinset := ⟨r.cycleOf x.1, hfactor⟩
    refine ⟨c, ?_⟩
    apply Quotient.sound
    change
      (⟨a c, haSupport c⟩ : r.support) ∈
        MulAction.orbit (Subgroup.zpowers rp) x
    rw [MulAction.mem_orbit_iff]
    obtain ⟨m, hm⟩ := Equiv.Perm.Basis.sameCycle a hfactor
    let z : Subgroup.zpowers rp :=
      ⟨rp ^ m, Subgroup.zpow_mem_zpowers rp m⟩
    refine ⟨z⁻¹, ?_⟩
    have hpowVal :=
      Equiv.Perm.subtypePerm_apply_zpow_of_mem
        (g := r) (s := r.support)
        (fun _ => Equiv.Perm.apply_mem_support)
        (x := a c) (i := m) (haSupport c)
    have hmSupport :
        (rp ^ m) (⟨a c, haSupport c⟩ : r.support) = x := by
      apply Subtype.ext
      rw [show
        ((rp ^ m) (⟨a c, haSupport c⟩ : r.support)).1 =
          (r ^ m) (a c) by
            simpa only [rp, supportRestriction] using hpowVal]
      exact hm
    change (rp ^ m)⁻¹ x =
      (⟨a c, haSupport c⟩ : r.support)
    rw [← hmSupport]
    simp

@[simp] theorem cycleFactorsEquivSupportOrbitQuotient_apply
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) (c : r.cycleFactorsFinset) :
    cycleFactorsEquivSupportOrbitQuotient r c =
      Quotient.mk''
        (⟨cycleBasis r c,
          Equiv.Perm.mem_cycleFactorsFinset_support_le
            c.2 ((cycleBasis r).mem_support_self c)⟩ : r.support) := by
  rfl

theorem cyclicComplement_eq_support
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    (FiveTransitive.PrimeCyclicFixedAction.cyclicComplement X P r : Set X) =
      (((r : P) : Equiv.Perm X).support : Set X) := by
  ext x
  change
    x ∉ FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r ↔
      x ∈ ((r : P) : Equiv.Perm X).support
  rw [show
    x ∈ FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r ↔
      x ∈ Function.fixedPoints ((r : P) : Equiv.Perm X) from
    Set.ext_iff.mp
      (FiveTransitive.PrimeCyclicFixedAction.fixedPoints_eq_fixedPoints_generator
        X P r) x]
  simp only [Function.mem_fixedPoints_iff, Equiv.Perm.mem_support]

@[expose] def cyclicComplementEquivSupport
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicComplement X P r ≃
      ((r : P) : Equiv.Perm X).support :=
  Set.equivOfEq (cyclicComplement_eq_support P r)

@[expose] noncomputable def cyclicNormalizerSupportHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      Equiv.Perm (((r : P) : Equiv.Perm X).support) :=
  (cyclicComplementEquivSupport P r).permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom
      (FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
      (FiveTransitive.PrimeCyclicFixedAction.cyclicComplement X P r))

@[simp] theorem cyclicNormalizerSupportHom_apply_val
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P)
    (z : FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
    (x : ((r : P) : Equiv.Perm X).support) :
    ((cyclicNormalizerSupportHom P r z x :
        ((r : P) : Equiv.Perm X).support) : X) =
      (((z : FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r) : P) :
        Equiv.Perm X) x := by
  rfl

private theorem cyclicNormalizerSupportHom_generator
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    cyclicNormalizerSupportHom P r
        (FiveTransitive.PrimeCyclicFixedAction.generatorInNormalizer P r) =
      supportRestriction ((r : P) : Equiv.Perm X) := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

theorem cyclicNormalizerSupportHom_range_le_normalizer
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    (cyclicNormalizerSupportHom P r).range ≤
      Subgroup.normalizer
        (Subgroup.zpowers
            (supportRestriction ((r : P) : Equiv.Perm X)) :
          Set (Equiv.Perm (((r : P) : Equiv.Perm X).support))) := by
  let N := FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r
  let SN : Subgroup N :=
    FiveTransitive.PrimeCyclicFixedAction.cyclicInNormalizer P r
  let rN : N :=
    FiveTransitive.PrimeCyclicFixedAction.generatorInNormalizer P r
  let τ : N →* Equiv.Perm (((r : P) : Equiv.Perm X).support) :=
    cyclicNormalizerSupportHom P r
  let g : Equiv.Perm (((r : P) : Equiv.Perm X).support) :=
    supportRestriction ((r : P) : Equiv.Perm X)
  have hSN : SN = Subgroup.zpowers rN := by
    simpa only [N, SN, rN] using
      FiveTransitive.PrimeCyclicFixedAction.cyclicInNormalizer_eq_zpowers_generator
        P r
  have hτr : τ rN = g := by
    simpa only [τ, rN, g] using
      cyclicNormalizerSupportHom_generator P r
  have hmap : SN.map τ = Subgroup.zpowers g := by
    calc
      SN.map τ = (Subgroup.zpowers rN).map τ := by rw [hSN]
      _ = Subgroup.zpowers (τ rN) := MonoidHom.map_zpowers τ rN
      _ = Subgroup.zpowers g := by rw [hτr]
  apply Subgroup.le_normalizer_iff.mpr
  intro q hq z hz
  obtain ⟨n, rfl⟩ := hq
  rw [← hmap] at hz ⊢
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hz
  refine Subgroup.mem_map.mpr ⟨n * s * n⁻¹, ?_, ?_⟩
  · exact (inferInstance : SN.Normal).conj_mem s hs n
  · change τ (n * s * n⁻¹) = τ n * τ s * (τ n)⁻¹
    simp

@[expose] noncomputable def cyclicNormalizerSupportNormalizerHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      Subgroup.normalizer
        (Subgroup.zpowers
            (supportRestriction ((r : P) : Equiv.Perm X)) :
          Set (Equiv.Perm (((r : P) : Equiv.Perm X).support))) :=
  (cyclicNormalizerSupportHom P r).codRestrict _ fun z =>
    cyclicNormalizerSupportHom_range_le_normalizer P r
      ⟨z, rfl⟩

@[expose] noncomputable def cyclicNormalizerSupportOrbitHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      Equiv.Perm
        (supportOrbitQuotient ((r : P) : Equiv.Perm X)) :=
  (FiveTransitive.CyclicNormalizerOrbitAction.normalizerOrbitHom
      (Subgroup.zpowers
        (supportRestriction ((r : P) : Equiv.Perm X)))).comp
    (cyclicNormalizerSupportNormalizerHom P r)

private noncomputable def cyclicNormalizerSupportRangeOrbitHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    (cyclicNormalizerSupportHom P r).range →*
      Equiv.Perm
        (supportOrbitQuotient ((r : P) : Equiv.Perm X)) :=
  FiveTransitive.CyclicNormalizerOrbitAction.orbitHomOfLeNormalizer
    (Subgroup.zpowers
      (supportRestriction ((r : P) : Equiv.Perm X)))
    (cyclicNormalizerSupportHom P r).range
    (cyclicNormalizerSupportHom_range_le_normalizer P r)

private theorem supportRestriction_fixedPointFree
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) :
    ∀ x : r.support, supportRestriction r x ≠ x := by
  intro x hx
  exact Equiv.Perm.mem_support.mp x.2 (congrArg Subtype.val hx)

private theorem orderOf_supportRestriction
    {X : Type*} [Fintype X] [DecidableEq X]
    (r : Equiv.Perm X) {p : ℕ}
    (hp : p.Prime) (hr : orderOf r = p) :
    orderOf (supportRestriction r) = p := by
  have hrPow : r ^ p = 1 := by
    rw [← hr]
    exact pow_orderOf_eq_one r
  have hrpPow : (supportRestriction r) ^ p = 1 := by
    unfold supportRestriction
    rw [Equiv.Perm.subtypePerm_pow]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change (r ^ p) x.1 = x.1
    rw [hrPow]
    rfl
  have hrNe : r ≠ 1 := by
    intro hrOne
    rw [hrOne, orderOf_one] at hr
    exact hp.ne_one hr.symm
  have hsupp : r.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    apply hrNe
    apply Equiv.ext
    intro x
    by_contra hx
    have hmem : x ∈ r.support := Equiv.Perm.mem_support.mpr hx
    rw [hempty] at hmem
    simpa using hmem
  obtain ⟨x, hx⟩ := hsupp
  let y : r.support := ⟨x, hx⟩
  have hrpNe : supportRestriction r ≠ 1 := by
    intro hOne
    apply supportRestriction_fixedPointFree r y
    exact congrFun (congrArg DFunLike.coe hOne) y
  letI : Fact p.Prime := ⟨hp⟩
  exact orderOf_eq_prime hrpPow hrpNe

private theorem cyclicNormalizerSupportRangeOrbitHom_ker_isSolvable
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) {p : ℕ}
    (hp : p.Prime)
    (hr : orderOf ((r : P) : Equiv.Perm X) = p) :
    Group.IsSolvable
      (cyclicNormalizerSupportRangeOrbitHom P r).ker := by
  classical
  let rawR : Equiv.Perm X := ((r : P) : Equiv.Perm X)
  let rp : Equiv.Perm rawR.support := supportRestriction rawR
  have hrpOrder : orderOf rp = p := by
    exact orderOf_supportRestriction rawR hp hr
  have hrpSupport : rp.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact supportRestriction_fixedPointFree rawR x
  have hrpSum : rp.cycleType.sum = Fintype.card rawR.support := by
    rw [rp.sum_cycleType, hrpSupport, Finset.card_univ]
  unfold cyclicNormalizerSupportRangeOrbitHom
  exact
    FiveTransitive.CyclicNormalizerOrbitAction.orbitHomOfLeNormalizer_ker_isSolvable
      (cyclicNormalizerSupportHom P r).range
      (cyclicNormalizerSupportHom_range_le_normalizer P r)
      hp hrpOrder hrpSum

private theorem cyclicNormalizerSupportRangeOrbitHom_comp
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    (cyclicNormalizerSupportRangeOrbitHom P r).comp
        (cyclicNormalizerSupportHom P r).rangeRestrict =
      cyclicNormalizerSupportOrbitHom P r := by
  apply MonoidHom.ext
  intro z
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn'
  rfl

@[expose] noncomputable def cyclicNormalizerCycleHom
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r →*
      Equiv.Perm (((r : P) : Equiv.Perm X).cycleFactorsFinset) :=
  (cycleFactorsEquivSupportOrbitQuotient
      ((r : P) : Equiv.Perm X)).symm.permCongrHom.toMonoidHom.comp
    (cyclicNormalizerSupportOrbitHom P r)

private theorem range_card_lt_alternating_of_card_eq_seven
    {L Y : Type*} [Group L] [Fintype Y] [DecidableEq Y]
    (f : L →* Equiv.Perm Y)
    (hY : Fintype.card Y = 7)
    (hnot : ¬alternatingGroup Y ≤ f.range) :
    Nat.card f.range < Nat.card (alternatingGroup Y) := by
  letI : Nontrivial Y :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  by_contra hlt
  have hle : Nat.card (alternatingGroup Y) ≤ Nat.card f.range :=
    Nat.le_of_not_gt hlt
  have hAltCard : Nat.card (alternatingGroup Y) = 2520 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, hY]
    norm_num
  have hPermCard : Nat.card (Equiv.Perm Y) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hY]
    norm_num
  have hindexProduct := f.range.index_mul_card
  have hindexLe : f.range.index ≤ 2 := by
    by_contra hi
    have hthree : 3 ≤ f.range.index := by omega
    have hmul := Nat.mul_le_mul_right (Nat.card f.range) hthree
    rw [hindexProduct, hPermCard] at hmul
    rw [hAltCard] at hle
    omega
  exact hnot
    (Equiv.Perm.alternatingGroup_le_of_index_le_two hindexLe)

private theorem supportOrbit_range_card_eq_cycle_range_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P) :
    Nat.card (cyclicNormalizerSupportOrbitHom P r).range =
      Nat.card (cyclicNormalizerCycleHom P r).range := by
  let e := cycleFactorsEquivSupportOrbitQuotient
    ((r : P) : Equiv.Perm X)
  let φ := e.symm.permCongrHom.toMonoidHom
  let ψ := cyclicNormalizerSupportOrbitHom P r
  calc
    Nat.card ψ.range = Nat.card (ψ.range.map φ) :=
      Nat.card_congr
        (ψ.range.equivMapOfInjective φ
          e.symm.permCongrHom.injective).toEquiv
    _ = Nat.card (φ.comp ψ).range := by
      rw [MonoidHom.map_range]
    _ = Nat.card (cyclicNormalizerCycleHom P r).range := by
      rfl

private theorem alternatingGroup_le_of_canonical_cycle_range_small
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (r : P)
    (hr : orderOf ((r : P) : Equiv.Perm X) = 3)
    (hfixed : Fintype.card
      (Function.fixedPoints ((r : P) : Equiv.Perm X)) = 7)
    (hAltFixed :
      alternatingGroup
          (Function.fixedPoints ((r : P) : Equiv.Perm X)) ≤
        (cyclicNormalizerFixedHom P r).range)
    (hsmall :
      Nat.card (cyclicNormalizerCycleHom P r).range <
        Nat.card
          (alternatingGroup
            (Function.fixedPoints ((r : P) : Equiv.Perm X)))) :
    alternatingGroup X ≤ P := by
  classical
  let rawR : Equiv.Perm X := ((r : P) : Equiv.Perm X)
  let N := FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r
  let Y := Function.fixedPoints rawR
  let U := rawR.support
  let fixedRaw : N →* Equiv.Perm Y :=
    cyclicNormalizerFixedHom P r
  let supportRaw : N →* Equiv.Perm U :=
    cyclicNormalizerSupportHom P r
  let B : Subgroup (Equiv.Perm U) := supportRaw.range
  let orbitMap : B →*
      Equiv.Perm (supportOrbitQuotient rawR) :=
    cyclicNormalizerSupportRangeOrbitHom P r
  letI : Group.IsSolvable orbitMap.ker := by
    simpa only [orbitMap, rawR] using
      (cyclicNormalizerSupportRangeOrbitHom_ker_isSolvable
        P r (by norm_num) hr)
  have hAltFixed' : alternatingGroup Y ≤ fixedRaw.range := by
    simpa only [Y, rawR, fixedRaw] using hAltFixed
  have hsmall' :
      Nat.card (orbitMap.comp supportRaw.rangeRestrict).range <
        Nat.card (alternatingGroup Y) := by
    have hcomp :
        orbitMap.comp supportRaw.rangeRestrict =
          cyclicNormalizerSupportOrbitHom P r := by
      simpa only [orbitMap, supportRaw, B, rawR] using
        cyclicNormalizerSupportRangeOrbitHom_comp P r
    rw [hcomp, supportOrbit_range_card_eq_cycle_range_card]
    simpa only [Y, rawR] using hsmall
  have hYfive : 5 ≤ Fintype.card Y := by
    have hYcard : Fintype.card Y = 7 := by
      simpa only [Y, rawR] using hfixed
    omega
  letI : IsSimpleGroup (alternatingGroup Y) :=
    alternatingGroup.isSimpleGroup (by
      rw [Nat.card_eq_fintype_card]
      exact hYfive)
  letI : Group.IsPerfect (alternatingGroup Y) := by
    rw [Group.isPerfect_def]
    exact commutator_alternatingGroup_eq_top (by
      rw [Nat.card_eq_fintype_card]
      exact hYfive)
  have hAltNonsolvable : ¬Group.IsSolvable (alternatingGroup Y) :=
    Group.IsPerfect.not_isSolvable _
  have hthreeCard : 3 ≤ Fintype.card Y := by
    have hYcard : Fintype.card Y = 7 := by
      simpa only [Y, rawR] using hfixed
    omega
  let e : Fin 3 ↪ Y :=
    Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (by
        rw [Fintype.card_fin]
        exact hthreeCard))
  have heZeroOne : e 0 ≠ e 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (e.injective h)
  have heZeroTwo : e 0 ≠ e 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (e.injective h)
  have heOneTwo : e 1 ≠ e 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (e.injective h)
  let q : Equiv.Perm Y :=
    Equiv.swap (e 0) (e 1) * Equiv.swap (e 0) (e 2)
  have hqThree : q.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same
      heZeroOne heZeroTwo heOneTwo
  have hqAlt : q ∈ alternatingGroup Y :=
    hqThree.mem_alternatingGroup
  obtain ⟨n, hnFixed, hnSupportRange⟩ :=
    FiveTransitive.SolvableOrbitGoursat.exists_lift_with_solvable_kernel_small_range
      N (Equiv.Perm Y) B
        (Equiv.Perm (supportOrbitQuotient rawR))
        fixedRaw supportRaw.rangeRestrict orbitMap
        (alternatingGroup Y) hAltFixed' hAltNonsolvable
        hsmall' q hqAlt
  have hnSupport : supportRaw n = 1 :=
    congrArg Subtype.val hnSupportRange
  let nP : P := n
  let nPerm : Equiv.Perm X := nP
  have hnSupportSubset : (nPerm.support : Set X) ⊆ Y := by
    intro x hx
    by_contra hxY
    have hxU : x ∈ rawR.support := by
      exact Equiv.Perm.mem_support.mpr hxY
    let y : U := ⟨x, hxU⟩
    have happ := congrFun (congrArg DFunLike.coe hnSupport) y
    have hfix : nPerm x = x := congrArg Subtype.val happ
    exact Equiv.Perm.mem_support.mp hx hfix
  let valEmbedding : Y ↪ X := Function.Embedding.subtype _
  have hsupportMap :
      Finset.map valEmbedding q.support = nPerm.support := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      apply Equiv.Perm.mem_support.mp hy
      have happ := congrFun (congrArg DFunLike.coe hnFixed) y
      apply Subtype.ext
      exact congrArg Subtype.val
        (happ.symm.trans (Subtype.ext hfix))
    · intro hx
      have hxY : x ∈ Y := hnSupportSubset hx
      let y : Y := ⟨x, hxY⟩
      rw [Finset.mem_map]
      refine ⟨y, ?_, rfl⟩
      apply Equiv.Perm.mem_support.mpr
      intro hfix
      apply Equiv.Perm.mem_support.mp hx
      have happ := congrFun (congrArg DFunLike.coe hnFixed) y
      exact congrArg Subtype.val (happ.trans hfix)
  have hnSupportCard : nPerm.support.card = 3 := by
    calc
      nPerm.support.card =
          (Finset.map valEmbedding q.support).card := by
            rw [hsupportMap]
      _ = q.support.card := Finset.card_map valEmbedding
      _ = 3 := hqThree.card_support
  have hnNe : nPerm ≠ 1 := by
    intro hnOne
    rw [hnOne, Equiv.Perm.support_one] at hnSupportCard
    norm_num at hnSupportCard
  apply
    FiveTransitive.Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
      X P h5 hdegree nP.prop hnNe
  change nPerm.support.card ≤ 5
  omega

@[simp] theorem cyclicNormalizerSupportOrbitHom_apply_mk
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P)
    (z : FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
    (x : ((r : P) : Equiv.Perm X).support) :
    cyclicNormalizerSupportOrbitHom P r z (Quotient.mk'' x) =
      Quotient.mk'' (cyclicNormalizerSupportHom P r z x) := by
  rfl

private theorem cycleFactorsEquivSupportOrbitQuotient_cycleHom_apply
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P)
    (z : FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
    (c : ((r : P) : Equiv.Perm X).cycleFactorsFinset) :
    cycleFactorsEquivSupportOrbitQuotient ((r : P) : Equiv.Perm X)
        (cyclicNormalizerCycleHom P r z c) =
      cyclicNormalizerSupportOrbitHom P r z
        (cycleFactorsEquivSupportOrbitQuotient
          ((r : P) : Equiv.Perm X) c) := by
  change
    cycleFactorsEquivSupportOrbitQuotient ((r : P) : Equiv.Perm X)
        ((cycleFactorsEquivSupportOrbitQuotient
          ((r : P) : Equiv.Perm X)).symm
            (cyclicNormalizerSupportOrbitHom P r z
              (cycleFactorsEquivSupportOrbitQuotient
                ((r : P) : Equiv.Perm X) c))) = _
  exact (cycleFactorsEquivSupportOrbitQuotient
    ((r : P) : Equiv.Perm X)).apply_symm_apply _

private theorem cyclicNormalizerCycleHom_ker_compat
    {X : Type*} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (r : P)
    (z : (cyclicConjugation P r).ker) :
    cyclicNormalizerCycleHom P r z.1 =
      cyclePart ((r : P) : Equiv.Perm X)
        (cyclicConjugationKernelToCentralizer P r z) := by
  classical
  let rawR : Equiv.Perm X := ((r : P) : Equiv.Perm X)
  let u : Subgroup.centralizer ({rawR} : Set (Equiv.Perm X)) :=
    cyclicConjugationKernelToCentralizer P r z
  let a : rawR.Basis := cycleBasis rawR
  apply Equiv.ext
  intro c
  apply (cycleFactorsEquivSupportOrbitQuotient rawR).injective
  have hcycleAction :=
    cycleFactorsEquivSupportOrbitQuotient_cycleHom_apply P r z.1 c
  change
    cycleFactorsEquivSupportOrbitQuotient rawR
        (cyclicNormalizerCycleHom P r z.1 c) =
      cyclicNormalizerSupportOrbitHom P r z.1
        (cycleFactorsEquivSupportOrbitQuotient rawR c) at hcycleAction
  rw [hcycleAction]
  let d : rawR.cycleFactorsFinset := cyclePart rawR u c
  have hcSupport : a c ∈ rawR.support :=
    Equiv.Perm.mem_cycleFactorsFinset_support_le
      c.2 (a.mem_support_self c)
  have hdSupport : a d ∈ rawR.support :=
    Equiv.Perm.mem_cycleFactorsFinset_support_le
      d.2 (a.mem_support_self d)
  have hzaCycle : u.1 (a c) ∈ d.1.support := by
    have hconj : d.1 = u.1 * c.1 * u.1⁻¹ := by
      simpa only [d, cyclePart, rawR, u] using
        (Equiv.Perm.OnCycleFactors.coe_toPermHom rawR u c)
    rw [hconj, Equiv.Perm.support_conj]
    simp [a.mem_support_self c]
  have hzaSupport : u.1 (a c) ∈ rawR.support :=
    Equiv.Perm.mem_cycleFactorsFinset_support_le d.2 hzaCycle
  have hsame : rawR.SameCycle (a d) (u.1 (a c)) := by
    apply
      (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        hdSupport hzaSupport).2
    calc
      rawR.cycleOf (a d) = d.1 :=
        (Equiv.Perm.cycle_is_cycleOf (a.mem_support_self d) d.2).symm
      _ = rawR.cycleOf (u.1 (a c)) :=
        Equiv.Perm.cycle_is_cycleOf hzaCycle d.2
  obtain ⟨m, hm⟩ := hsame
  rw [cycleFactorsEquivSupportOrbitQuotient_apply,
    cycleFactorsEquivSupportOrbitQuotient_apply,
    cyclicNormalizerSupportOrbitHom_apply_mk]
  apply Quotient.sound
  change
    cyclicNormalizerSupportHom P r z.1
        (⟨a c, hcSupport⟩ : rawR.support) ∈
      MulAction.orbit
        (Subgroup.zpowers (supportRestriction rawR))
        (⟨a d, hdSupport⟩ : rawR.support)
  rw [MulAction.mem_orbit_iff]
  let rp : Equiv.Perm rawR.support := supportRestriction rawR
  let w : Subgroup.zpowers rp :=
    ⟨rp ^ m, Subgroup.zpow_mem_zpowers rp m⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  have hpowVal :=
    Equiv.Perm.subtypePerm_apply_zpow_of_mem
      (g := rawR) (s := rawR.support)
      (fun _ => Equiv.Perm.apply_mem_support)
      (x := a d) (i := m) hdSupport
  change
    ((rp ^ m) (⟨a d, hdSupport⟩ : rawR.support)).1 =
      (cyclicNormalizerSupportHom P r z.1
        (⟨a c, hcSupport⟩ : rawR.support)).1
  rw [show
    ((rp ^ m) (⟨a d, hdSupport⟩ : rawR.support)).1 =
      (rawR ^ m) (a d) by
        simpa only [rp, supportRestriction] using hpowVal]
  rw [hm]
  rfl

private theorem exists_order_three_support_le_eighteen_of_cyclic_normalizer_actions
    {X : Type} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (rP : P)
    (hr : orderOf ((rP : P) : Equiv.Perm X) = 3)
    (hrFixed : Fintype.card
      (Function.fixedPoints ((rP : P) : Equiv.Perm X)) = 7)
    (hrCycles : ((rP : P) : Equiv.Perm X).cycleType.card = 7)
    (fixedRaw :
      FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P rP →*
        Equiv.Perm
          (Function.fixedPoints ((rP : P) : Equiv.Perm X)))
    (cycleRaw :
      FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P rP →*
        Equiv.Perm
          (((rP : P) : Equiv.Perm X).cycleFactorsFinset))
    (hfixedCompat : ∀ z : (cyclicConjugation P rP).ker,
      fixedRaw z.1 =
        fixedPart ((rP : P) : Equiv.Perm X)
          (cyclicConjugationKernelToCentralizer P rP z))
    (hcycleCompat : ∀ z : (cyclicConjugation P rP).ker,
      cycleRaw z.1 =
        cyclePart ((rP : P) : Equiv.Perm X)
          (cyclicConjugationKernelToCentralizer P rP z))
    (hAltFixed :
      alternatingGroup
          (Function.fixedPoints ((rP : P) : Equiv.Perm X)) ≤
        fixedRaw.range)
    (hAltCycles :
      alternatingGroup
          (((rP : P) : Equiv.Perm X).cycleFactorsFinset) ≤
        cycleRaw.range) :
    ∃ g : Equiv.Perm X,
      g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  let R := FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P rP
  let N := FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P rP
  letI : Group.IsSolvable (MulAut R) := by
    exact Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv R).toMonoidHom)
      (IsCyclic.mulAutMulEquiv R).injective
  apply exists_order_three_support_le_eighteen_of_solvable_aux_actions
      hX P h5 s hs S hScard
      ((rP : P) : Equiv.Perm X) rP.prop
      hr hrFixed hrCycles N (MulAut R)
      fixedRaw cycleRaw (cyclicConjugation P rP)
      (cyclicConjugationKernelToCentralizer P rP)
  · intro z
    exact ((z.1 : N) : P).prop
  · exact hfixedCompat
  · exact hcycleCompat
  · exact hAltFixed
  · exact hAltCycles

private theorem exists_order_three_support_le_eighteen_of_canonical_actions
    {X : Type} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (rP : P)
    (hr : orderOf ((rP : P) : Equiv.Perm X) = 3)
    (hrFixed : Fintype.card
      (Function.fixedPoints ((rP : P) : Equiv.Perm X)) = 7)
    (hrCycles : ((rP : P) : Equiv.Perm X).cycleType.card = 7)
    (hAltFixed :
      alternatingGroup
          (Function.fixedPoints ((rP : P) : Equiv.Perm X)) ≤
        (cyclicNormalizerFixedHom P rP).range)
    (hAltCycles :
      alternatingGroup
          (((rP : P) : Equiv.Perm X).cycleFactorsFinset) ≤
        (cyclicNormalizerCycleHom P rP).range) :
    ∃ g : Equiv.Perm X,
      g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  exact
    exists_order_three_support_le_eighteen_of_cyclic_normalizer_actions
      hX P h5 s hs S hScard rP hr hrFixed hrCycles
      (cyclicNormalizerFixedHom P rP)
      (cyclicNormalizerCycleHom P rP)
      (cyclicNormalizerFixedHom_ker_compat P rP)
      (cyclicNormalizerCycleHom_ker_compat P rP)
      hAltFixed hAltCycles

theorem alternating_or_exists_order_three_support_le_eighteen
    {X : Type} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (rP : P)
    (hRSP :
      FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P rP =
        FiveTransitive.Degree24.sylowImage X P s S)
    (hr : orderOf ((rP : P) : Equiv.Perm X) = 3)
    (hrFixed : Fintype.card
      (Function.fixedPoints ((rP : P) : Equiv.Perm X)) = 7)
    (hrCycles : ((rP : P) : Equiv.Perm X).cycleType.card = 7) :
    alternatingGroup X ≤ P ∨
      ∃ g : Equiv.Perm X,
        g ∈ P ∧ orderOf g = 3 ∧ g.support.card ≤ 18 := by
  have hdegree : 5 ≤ Fintype.card X := by omega
  have hAltFixed :
      alternatingGroup
          (Function.fixedPoints ((rP : P) : Equiv.Perm X)) ≤
        (cyclicNormalizerFixedHom P rP).range :=
    alternatingGroup_le_cyclicNormalizerFixedHom_range
      P hdegree h5 s hs S rP hRSP hrFixed
  have hcycleCard :
      Fintype.card (((rP : P) : Equiv.Perm X).cycleFactorsFinset) = 7 := by
    rw [cycleFactorsFinset_card, hrCycles]
  by_cases hAltCycles :
      alternatingGroup
          (((rP : P) : Equiv.Perm X).cycleFactorsFinset) ≤
        (cyclicNormalizerCycleHom P rP).range
  · exact Or.inr
      (exists_order_three_support_le_eighteen_of_canonical_actions
        hX P h5 s hs S hScard rP hr hrFixed hrCycles
        hAltFixed hAltCycles)
  · left
    have hcycleSmall :=
      range_card_lt_alternating_of_card_eq_seven
        (cyclicNormalizerCycleHom P rP) hcycleCard hAltCycles
    letI : Nontrivial
        (((rP : P) : Equiv.Perm X).cycleFactorsFinset) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    letI : Nontrivial
        (Function.fixedPoints ((rP : P) : Equiv.Perm X)) :=
      Fintype.one_lt_card_iff_nontrivial.mp (by omega)
    have hAltCardEq :
        Nat.card
            (alternatingGroup
              (((rP : P) : Equiv.Perm X).cycleFactorsFinset)) =
          Nat.card
            (alternatingGroup
              (Function.fixedPoints ((rP : P) : Equiv.Perm X))) := by
      simp only [Nat.card_eq_fintype_card, card_alternatingGroup,
        hcycleCard, hrFixed]
    rw [hAltCardEq] at hcycleSmall
    exact alternatingGroup_le_of_canonical_cycle_range_small
      P hdegree h5 rP hr hrFixed hAltFixed hcycleSmall

end FiveTransitive.Degree28BlockEscape

end CFSG
