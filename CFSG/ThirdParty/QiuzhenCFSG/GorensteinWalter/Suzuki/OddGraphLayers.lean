module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.UConjugatesGraph
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenWitness
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSevenXCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinB4Divisible
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCosetFiberCard
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseCountConstructor
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.OddGraphNeighbors
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Odd-graph coset layers

The 35 right cosets of `Ĥ` are partitioned into the base coset and the
non-base coset-involution layers of sizes `0`, `2`, and `4`.  This module
owns the first-case layer cardinalities and the `Ĥ`-orbit statements used
by the odd-graph reconstruction.
-/

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

@[expose] public def firstCaseCosetLayer
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (n : ℕ) : Type u :=
  {q : G ⧸ c.Hhat // q ≠ cosetInvolution_base c.Hhat ∧
    Nat.card (cosetInvolution_fiber c.Hhat q) = n}

public theorem firstCaseCosetLayer_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c) :
    Nat.card (firstCaseCosetLayer c 0) = 4 ∧
      Nat.card (firstCaseCosetLayer c 2) = 18 ∧
      Nat.card (firstCaseCosetLayer c 4) = 12 := by
  have hb0 : d.b0 = 4 := by
    obtain ⟨m, hm⟩ := d.h4dvd
    have h8 := d.h8
    have h9 := d.h9
    rw [d.hK] at h8 h9
    have hb4le : d.b4 ≤ 18 := by omega
    have hm1 : m = 1 := by
      have hb4m : d.b4 = 12 * m := hm
      have hmle : m ≤ 1 := by omega
      have hmne : m ≠ 0 := by
        intro hm0
        apply d.h4ne
        omega
      omega
    have hb4 : d.b4 = 12 := by omega
    have hb2 : d.b2 = 18 := by omega
    obtain ⟨k, hk⟩ := d.h1dvd
    have hk0 : k = 0 := by
      have hb1k : d.b1 = 8 * k := hk
      omega
    omega
  have hb4 : d.b4 = 12 := by
    obtain ⟨m, hm⟩ := d.h4dvd
    have h8 := d.h8
    rw [d.hK] at h8
    have hb4le : d.b4 ≤ 18 := by omega
    have hm1 : m = 1 := by
      have hb4m : d.b4 = 12 * m := hm
      have hmle : m ≤ 1 := by omega
      have hmne : m ≠ 0 := by
        intro hm0
        apply d.h4ne
        omega
      omega
    omega
  have hb2 : d.b2 = 18 := by
    have h8 := d.h8
    rw [d.hK, hb4] at h8
    omega
  have hb1 : d.b1 = 0 := by
    obtain ⟨k, hk⟩ := d.h1dvd
    have h9 := d.h9
    rw [d.hK, hb0, hb2, hb4] at h9
    omega
  have hb3 : d.b3 = 0 := d.h3zero
  have hbn (n : ℕ) (hn0 : 0 < n) (hn : n ≤ 4) :
      cosetInvolution_b c.Hhat n = firstCaseBn d.b0 d.b1 d.b2 d.b3 d.b4 n := by
    have hJgeneric := firstCase_J_n_card c n
    have hJdata := d.h1_Jn n hn
    rw [hJgeneric] at hJdata
    exact Nat.eq_of_mul_eq_mul_left hn0 hJdata
  constructor
  · have hactual1 : cosetInvolution_b c.Hhat 1 = 0 := by
      rw [hbn 1 (by omega) (by omega)]
      simpa [firstCaseBn] using hb1
    have hactual2 : cosetInvolution_b c.Hhat 2 = 18 := by
      rw [hbn 2 (by omega) (by omega)]
      simpa [firstCaseBn] using hb2
    have hactual3 : cosetInvolution_b c.Hhat 3 = 0 := by
      rw [hbn 3 (by omega) (by omega)]
      simpa [firstCaseBn] using hb3
    have hactual4 : cosetInvolution_b c.Hhat 4 = 12 := by
      rw [hbn 4 (by omega) (by omega)]
      simpa [firstCaseBn] using hb4
    have hklein : IsKleinFour (pCore 2 c.Hhat) :=
      firstCase_twoCore_isKleinFour hmin c hfirst
    have h7strong : ∀ (n : ℕ) (y : G) (X : Subgroup G),
        4 ≤ n → y ∈ firstCaseJ c n → X ≠ ⊥ → X ≤ c.Hhat →
        Nat.Coprime 2 (Nat.card X) →
        (∀ x : G, x ∈ X → x ∈ invertedElements c.Hhat y) →
        Even (Nat.card (Subgroup.centralizer (X : Set G))) →
        Even (Nat.card ((Subgroup.normalizer (X : Set G) ⊓ c.Hhat : Subgroup G))) →
        Nat.card c.U = Nat.card X ∧ Nat.card X = 3 ∧ n = 4 ∧
          (let D := c.Hhat ⊓ conjugateSubgroup c.Hhat y
           let N := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
           (N.subgroupOf D).index = 6) := by
      intro n y X hn hyJ hXne hXle hXodd hXinv hC hN
      have hd := d.h7 n y X hn hyJ hXne hXle hXodd hXinv hC hN
      have hy : IsInvolution y := by simpa [firstCaseJ] using hyJ |>.1
      have hyH : y ∉ c.Hhat := by simpa [firstCaseJ] using hyJ |>.2.1
      have hX3 := firstCase_klein_restrictionSeven_X_card_three
        hmin c hfirst hklein hy hyH hd.2.2.2 hXne hXle hXodd hXinv
      refine ⟨?_, hX3, hd.2.2.1, hd.2.2.2⟩
      rw [hd.1, d.hK, hX3]
    have hvanish : ∀ n : ℕ, 5 ≤ n → cosetInvolution_b c.Hhat n = 0 :=
      firstCase_klein_high_fiber_vanish_of_n_eq_four
        hmin c hfirst hklein h7strong
    have htotal : Nat.card {x : G // IsInvolution x} = 105 := by
      rw [d.h2_total, d.hK, hb1, hb2, hb3, hb4]
    have hidx : c.Hhat.index = 35 :=
      (firstCase_index_card_of_countData c d).1
    have hsum := cosetInvolution_index_eq_one_add_sum_b c.Hhat
    rw [hidx, htotal] at hsum
    have htail :
        (∑ n ∈ Finset.range 101, cosetInvolution_b c.Hhat (5 + n)) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      exact hvanish (5 + n) (by omega)
    have hsumSplit :
        (∑ n ∈ Finset.range 106, cosetInvolution_b c.Hhat n) =
          (∑ n ∈ Finset.range 5, cosetInvolution_b c.Hhat n) := by
      calc
        (∑ n ∈ Finset.range 106, cosetInvolution_b c.Hhat n) =
            (∑ n ∈ Finset.range 5, cosetInvolution_b c.Hhat n) +
              ∑ n ∈ Finset.range 101, cosetInvolution_b c.Hhat (5 + n) := by
                simpa using (Finset.sum_range_add
                  (f := fun n => cosetInvolution_b c.Hhat n) 5 101)
        _ = (∑ n ∈ Finset.range 5, cosetInvolution_b c.Hhat n) := by
          rw [htail, add_zero]
    rw [hsumSplit] at hsum
    have hactual0 : cosetInvolution_b c.Hhat 0 = 4 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hsum
      rw [hactual1, hactual2, hactual3, hactual4] at hsum
      omega
    rw [show Nat.card (firstCaseCosetLayer c 0) =
          cosetInvolution_b c.Hhat 0 by
        rw [cosetInvolution_b_card]
        rfl,
      hactual0]
  constructor
  · rw [show Nat.card (firstCaseCosetLayer c 2) =
        cosetInvolution_b c.Hhat 2 by
      rw [cosetInvolution_b_card]
      rfl,
      hbn 2 (by omega) (by omega)]
    simpa [firstCaseBn] using hb2
  · rw [show Nat.card (firstCaseCosetLayer c 4) =
        cosetInvolution_b c.Hhat 4 by
      rw [cosetInvolution_b_card]
      rfl,
      hbn 4 (by omega) (by omega)]
    simpa [firstCaseBn] using hb4

public def quotient_subgroup_stabilizer_equiv_inter_conjugate
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (g : G) :
    MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H) ≃*
      ↥(H ⊓ conjugateSubgroup H g : Subgroup G) := by
  let f : MulAction.stabilizer H (QuotientGroup.mk g : G ⧸ H) →*
      ↥(H ⊓ conjugateSubgroup H g : Subgroup G) :=
    { toFun := fun h => ⟨(h : G), ⟨h.1.2, by
          apply Subgroup.mem_map.mpr
          refine ⟨g⁻¹ * (h : G) * g, ?_, ?_⟩
          · have hfix := MulAction.mem_stabilizer_iff.mp h.2
            change QuotientGroup.mk ((h.1 : H) * g) = QuotientGroup.mk g at hfix
            have hm := (QuotientGroup.eq (s := H)).mp hfix
            have hminv := H.inv_mem hm
            have heq : ((((h : G) * g)⁻¹ * g)⁻¹) =
                g⁻¹ * (h : G) * g := by group
            rwa [heq] at hminv
          · simp [MulAut.conj_apply, mul_assoc]⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply MulEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(H ⊓ conjugateSubgroup H g : Subgroup G) => (z : G)) hab
  · intro x
    let h : H := ⟨(x : G), x.2.1⟩
    have hfix : h • (QuotientGroup.mk g : G ⧸ H) = QuotientGroup.mk g := by
      change QuotientGroup.mk ((x : G) * g) = QuotientGroup.mk g
      apply (QuotientGroup.eq (s := H)).mpr
      rcases Subgroup.mem_map.mp x.2.2 with ⟨y, hy, hyx⟩
      have hyx' : g * y * g⁻¹ = (x : G) := by
        simpa [conjugateSubgroup, MulAut.conj_apply] using hyx
      have heq : ((x : G) * g)⁻¹ * g = y⁻¹ := by
        rw [← hyx']
        group
      rw [heq]
      exact H.inv_mem hy
    refine ⟨⟨h, hfix⟩, ?_⟩
    apply Subtype.ext
    rfl

public theorem firstCase_hhat_card_72
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (d : FirstCaseCountData c) :
    Nat.card c.Hhat = 72 := by
  have hidx : c.Hhat.index = 35 :=
    (firstCase_index_card_of_countData c d).1
  have hG : Nat.card G = 2520 := by
    simpa using (firstCase_index_card_of_countData c d).2
  have hm := c.Hhat.index_mul_card
  rw [hidx, hG] at hm
  omega

/-- The full orbit of the base conjugate `U` is the whole conjugacy class. -/
private def orbitBaseEquiv {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) :
    (MulAction.orbit G (UConjugates.base c)) ≃ UConjugates c :=
  { toFun := fun x => x.1
    invFun := fun V => ⟨V, by
      rcases V.2 with ⟨g, hV⟩
      refine ⟨g, ?_⟩
      change g • UConjugates.base c = V
      rw [UConjugates.smul_def]
      apply Subtype.ext
      change conjugateSubgroup c.U g = V.1
      exact hV.symm⟩
    left_inv := by intro x; rfl
    right_inv := by intro V; rfl }

/-- The canonical identification of the right coset space `G / Ĥ` with the
35 conjugates of `U`, sending `gĤ` to `g • U`. -/
public def cosetLineEquiv {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) :
    G ⧸ c.Hhat ≃ UConjugates c :=
  let e1 : (MulAction.orbit G (UConjugates.base c)) ≃
      G ⧸ MulAction.stabilizer G (UConjugates.base c) :=
    MulAction.orbitEquivQuotientStabilizer G (UConjugates.base c)
  let eqStab : MulAction.stabilizer G (UConjugates.base c) = c.Hhat :=
    commutingGraph.stabilizer_base_eq_hhat hmin c hfirst
  let e2 : G ⧸ MulAction.stabilizer G (UConjugates.base c) ≃ G ⧸ c.Hhat :=
    Subgroup.quotientEquivOfEq eqStab
  ((e2.symm.trans e1.symm).trans (orbitBaseEquiv c))

/-- `cosetLineEquiv` sends the class of `g` to the conjugate `g • U`. -/
public theorem cosetLineEquiv_mk {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c) (g : G) :
    cosetLineEquiv hmin c hfirst (QuotientGroup.mk g) = g • UConjugates.base c := by
  rfl

/-- `cosetLineEquiv` is `Ĥ`-equivariant for the left actions on the coset
space and on the conjugacy class. -/
public theorem cosetLineEquiv_smul {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (h : c.Hhat) (q : G ⧸ c.Hhat) :
    cosetLineEquiv hmin c hfirst ((h : G) • q) =
      (h : G) • cosetLineEquiv hmin c hfirst q := by
  refine Quotient.inductionOn q ?_
  intro g
  change cosetLineEquiv hmin c hfirst (QuotientGroup.mk ((h : G) * g)) =
      (h : G) • g • UConjugates.base c
  rw [cosetLineEquiv_mk]
  rw [mul_smul]

private def firstCaseCosetLayer.smul
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {n : ℕ}
    (h : c.Hhat) (q : firstCaseCosetLayer c n) :
    firstCaseCosetLayer c n :=
  ⟨(h : G) • q.1,
    smul_base_ne c.Hhat h.2 q.2.1,
    (fiber_card_smul c.Hhat h.2 q.1).trans q.2.2⟩

private theorem firstCaseCosetLayer_orbit_subset
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} {n : ℕ}
    (q : firstCaseCosetLayer c n) :
    MulAction.orbit c.Hhat q.1 ⊆
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = n} := by
  intro x hx
  rcases hx with ⟨h, rfl⟩
  exact (firstCaseCosetLayer.smul h q).2

private theorem firstCaseCosetLayer_four_orbit_card_private
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (q : firstCaseCosetLayer c 4) :
    Nat.card (MulAction.orbit c.Hhat (q.1)) = 12 := by
  classical
  have hqpos : 0 < Nat.card (cosetInvolution_fiber c.Hhat (q.1)) := by
    rw [q.2.2]
    norm_num
  obtain ⟨y, hy⟩ := (Nat.card_pos_iff.mp hqpos).1
  have hyI : IsInvolution (y : G) := hy.1
  have hyproj : cosetInvolution_proj c.Hhat (y : G) = q.1 := hy.2
  have hyH : (y : G) ∉ c.Hhat := by
    intro hyH
    apply q.2.1
    rw [← hyproj]
    unfold cosetInvolution_proj cosetInvolution_base
    apply (QuotientGroup.eq (s := c.Hhat)).mpr
    simpa using hyH
  have hyJ : (y : G) ∈ firstCaseJ c 4 := by
    refine ⟨hyI, hyH, ?_⟩
    rw [firstCase_coset_fiber_card_eq c hyI, hyproj, q.2.2]
  have hklein : IsKleinFour (pCore 2 c.Hhat) :=
    firstCase_twoCore_isKleinFour hmin c hfirst
  obtain ⟨w, hwJ, hwproj, X, hXne, hXle, hXodd, hXinv, hC, hN⟩ :=
    firstCase_klein_restrictionSeven_witness_of_mem_J_four
      hmin c hfirst hklein hyJ
  have hwI : IsInvolution w := by simpa [firstCaseJ] using hwJ |>.1
  have hidx := (d.h7 4 w X (by norm_num) hwJ hXne hXle hXodd hXinv hC hN).2.2.2
  let D : Subgroup G := c.Hhat ⊓ conjugateSubgroup c.Hhat w
  let N : Subgroup G := D ⊓ (twoCoreOf c.Hhat ⊔ c.U)
  have hNbot : N = ⊥ := by
    simpa [D, N] using firstCase_klein_restrictionSeven_N_eq_bot
      hmin c hfirst hklein hwJ (by norm_num : 4 ≤ 4)
        hXne hXle hXodd hXinv hC hN
  have hidx' : (N.subgroupOf D).index = 6 := by simpa [D, N] using hidx
  have hNsub : N.subgroupOf D = ⊥ := by
    ext z
    constructor
    · intro hz
      have hzN : (z : G) ∈ N := (Subgroup.mem_subgroupOf.mp hz)
      rw [hNbot] at hzN
      simpa using hzN
    · intro hz
      have hz1 : z = 1 := by simpa using hz
      subst z
      simp
  have hDcard : Nat.card D = 6 := by
    rw [hNsub, Subgroup.index_bot] at hidx'
    simpa using hidx'
  have hwinv : w⁻¹ = w :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hwI.2)
  have hqmk : q.1 = (QuotientGroup.mk w : G ⧸ c.Hhat) := by
    rw [← hyproj, ← hwproj]
    simp [cosetInvolution_proj, hwinv]
  have hstabcard : Nat.card (MulAction.stabilizer c.Hhat (q.1)) = 6 := by
    rw [hqmk]
    calc
      Nat.card (MulAction.stabilizer c.Hhat
          (QuotientGroup.mk w : G ⧸ c.Hhat)) = Nat.card D := by
        exact Nat.card_congr
          (quotient_subgroup_stabilizer_equiv_inter_conjugate c.Hhat w).toEquiv
      _ = 6 := hDcard
  let : Fintype ↥c.Hhat := Fintype.ofFinite _
  let : Fintype (MulAction.orbit c.Hhat (q.1)) := Fintype.ofFinite _
  let : Fintype (MulAction.stabilizer c.Hhat (q.1)) := Fintype.ofFinite _
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    c.Hhat (q.1)
  have horbit' : Nat.card (MulAction.orbit c.Hhat (q.1)) *
      Nat.card (MulAction.stabilizer c.Hhat (q.1)) = Nat.card c.Hhat := by
    simpa [Nat.card_eq_fintype_card] using horbit
  rw [hstabcard, firstCase_hhat_card_72 c d] at horbit'
  omega

/-- Public form of the fibre-four orbit statement: a non-base coset with
four involutions has an `Ĥ`-orbit of size twelve. -/
public theorem firstCaseCosetLayer_four_orbit_card
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (q : G ⧸ c.Hhat)
    (hq : q ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat q) = 4) :
    Nat.card (MulAction.orbit c.Hhat q) = 12 :=
  firstCaseCosetLayer_four_orbit_card_private hmin c hfirst d ⟨q, hq⟩

/-- The fibre-four layer is a single `Ĥ`-orbit.  The orbit inclusion follows
from invariance of the fibre cardinal, and equality follows from the two
cardinality computations. -/
public theorem firstCaseCosetLayer_four_orbit_eq
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (hfirst : FirstCase c)
    (d : FirstCaseCountData c)
    (q : G ⧸ c.Hhat)
    (hq : q ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat q) = 4) :
    MulAction.orbit c.Hhat q =
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = 4} := by
  classical
  have hsubset : MulAction.orbit c.Hhat q ⊆
      {x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
        Nat.card (cosetInvolution_fiber c.Hhat x) = 4} := by
    exact firstCaseCosetLayer_orbit_subset ⟨q, hq⟩
  have horbit : (MulAction.orbit c.Hhat q).ncard = 12 := by
    change Nat.card {x : G ⧸ c.Hhat // x ∈ MulAction.orbit c.Hhat q} = 12
    exact firstCaseCosetLayer_four_orbit_card hmin c hfirst d q hq
  have hlayer : ({x : G ⧸ c.Hhat | x ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat x) = 4} : Set (G ⧸ c.Hhat)).ncard = 12 := by
    change Nat.card {x : G ⧸ c.Hhat // x ≠ cosetInvolution_base c.Hhat ∧
      Nat.card (cosetInvolution_fiber c.Hhat x) = 4} = 12
    simpa [firstCaseCosetLayer] using
      (firstCaseCosetLayer_card hmin c hfirst d).2.2
  exact Set.eq_of_subset_of_ncard_le hsubset (by rw [hlayer, horbit])

end CFSG.GorensteinWalter
