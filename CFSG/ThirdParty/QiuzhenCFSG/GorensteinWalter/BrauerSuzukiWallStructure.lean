module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallIndexK
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallTISubset
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallHall
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_2_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.ConjugateAction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStability
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_8_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.NormalComplement
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.theorem_1_13
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.theorem_10_1_b
import Mathlib.GroupTheory.GroupAction.SubMulAction
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Tactic.Group

namespace CFSG
end CFSG
open CFSG

/-!
# Structural completion of the Brauer--Suzuki--Wall theorem

This module formalizes Bender's structural completion after the order
calculation in `refs/bender-bsw.tex`, paragraphs 3.1--3.8.
-/

namespace CFSG.GorensteinWalter

open BenderSuzuki.External
open scoped Pointwise

universe u

/-- The ambient involutions, as a finite set for Bender's pair count. -/
public def bswInvolutions (G : Type u) [Group G] : Set G :=
  {x : G | IsInvolution x}

public theorem bswInvolutions_eq_orbit
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    bswInvolutions G = MulAction.orbit (ConjAct G) h.t := by
  ext x
  constructor
  · intro hx
    rw [ConjAct.mem_orbit_conjAct, isConj_iff]
    rcases h.involutions_conjugate x hx with ⟨g, hg⟩
    exact ⟨g, hg⟩
  · intro hx
    rw [ConjAct.mem_orbit_conjAct, isConj_iff] at hx
    rcases hx with ⟨g, hg⟩
    constructor
    · intro hone
      apply h.t_involution.1
      rw [← hg]
      simp [hone]
    · calc
        x ^ 2 = g⁻¹ * (h.t ^ 2) * g := by
          have hc := congrArg (fun z : G => g⁻¹ * z * g) hg
          have hx' : x = g⁻¹ * h.t * g := by
            simpa [mul_assoc] using hc
          rw [hx', pow_two, pow_two]
          group
        _ = 1 := by rw [h.t_involution.2]; simp

public theorem bswInvolutions_ncard_mul_card_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    (bswInvolutions G).ncard * Nat.card h.H = Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  rw [bswInvolutions_eq_orbit h]
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    (ConjAct G) h.t
  have horbit' :
      Nat.card ↑(MulAction.orbit (ConjAct G) h.t) *
          Nat.card (MulAction.stabilizer (ConjAct G) h.t) = Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using horbit
  have hstab : Nat.card (MulAction.stabilizer (ConjAct G) h.t) = Nat.card h.H := by
    rw [← Subgroup.nat_card_centralizer_nat_card_stabilizer h.t,
      ← h.H_eq_centralizer]
  rw [← Nat.card_coe_set_eq, ← hstab]
  exact horbit'

public theorem bswInvolutions_ncard_eq_index_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    (bswInvolutions G).ncard = h.H.index := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := h.H))
  calc
    Nat.card h.H * (bswInvolutions G).ncard = Nat.card G := by
      simpa [mul_comm] using bswInvolutions_ncard_mul_card_H h
    _ = Nat.card h.H * h.H.index := h.H.card_mul_index.symm

/-- The fiber over `x` of the product map on ordered pairs of involutions. -/
public def bswPairFiber
    (G : Type u) [Group G] (x : G) : Type u :=
  {p : (bswInvolutions G) × (bswInvolutions G) |
    (p.1 : G) * (p.2 : G) = x}

/-- Bender's function `i(x)`: the number of ordered pairs of involutions
whose product is `x`. -/
public noncomputable def bswPairCount
    (G : Type u) [Group G] (x : G) : ℕ :=
  Nat.card (bswPairFiber G x)

/-- The raw subtype presentation of Bender's pair count.  This is the stable
public bridge for consumers that formulate the fiber directly. -/
public theorem bswPairCount_eq_card_pair_subtype
    {G : Type u} [Group G] (x : G) :
    bswPairCount G x =
      Nat.card
        {p : (bswInvolutions G) × (bswInvolutions G) |
          (p.1 : G) * (p.2 : G) = x} := by
  rfl

/-- Summing Bender's pair-count function over the group counts every ordered
pair of involutions exactly once. -/
public theorem sum_bswPairCount
    {G : Type u} [Group G] [Fintype G] :
    ∑ x : G, bswPairCount G x = (bswInvolutions G).ncard ^ 2 := by
  classical
  let f : (bswInvolutions G) × (bswInvolutions G) → G :=
    fun p => (p.1 : G) * (p.2 : G)
  change (∑ x : G, Nat.card {p | f p = x}) =
    (bswInvolutions G).ncard ^ 2
  calc
    (∑ x : G, Nat.card {p | f p = x}) =
        Nat.card (Σ x : G, {p | f p = x}) := Nat.card_sigma.symm
    _ = Nat.card ((bswInvolutions G) × (bswInvolutions G)) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv f)
    _ = (bswInvolutions G).ncard ^ 2 := by
      rw [Nat.card_prod, Nat.card_coe_set_eq, pow_two]

/-- The fiber of the product map over the identity is equivalent to the set
of involutions, by projecting to either coordinate. -/
private noncomputable def bswPairFiberOneEquiv
    {G : Type u} [Group G] :
    bswPairFiber G 1 ≃ bswInvolutions G := by
  let f : bswPairFiber G 1 → bswInvolutions G := fun p => p.1.1
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply Prod.ext
    · exact hpq
    · apply Subtype.ext
      have hp : (p.1.1 : G) * (p.1.2 : G) = 1 := p.2
      have hq : (q.1.1 : G) * (q.1.2 : G) = 1 := q.2
      have hu : (p.1.1 : G) = (q.1.1 : G) :=
        congrArg Subtype.val hpq
      rw [← hu] at hq
      exact mul_left_cancel (hp.trans hq.symm)
  · intro x
    refine ⟨⟨(x, x), ?_⟩, rfl⟩
    simpa [pow_two] using x.2.2

/-- The identity is assigned one pair for every involution. -/
public theorem bswPairCount_one
    {G : Type u} [Group G] [Finite G] :
    bswPairCount G 1 = (bswInvolutions G).ncard := by
  calc
    bswPairCount G 1 = Nat.card (bswInvolutions G) :=
      Nat.card_congr bswPairFiberOneEquiv
    _ = (bswInvolutions G).ncard :=
      Nat.card_coe_set_eq (bswInvolutions G)

/-- In the fiber of the product map, the first involution conjugates the
product to its inverse. -/
private theorem bswPair_first_inverts_product
    {G : Type u} [Group G] {u v x : G}
    (hu : IsInvolution u) (hv : IsInvolution v) (hx : u * v = x) :
    u * x * u⁻¹ = x⁻¹ := by
  have huu : u * u = 1 := by simpa [pow_two] using hu.2
  have hvv : v * v = 1 := by simpa [pow_two] using hv.2
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  rw [← hx, hui, mul_inv_rev, hui, hvi]
  calc
    u * (u * v) * u = (u * u) * v * u := by group
    _ = v * u := by rw [huu]; simp

/-- The cyclic subgroup generated by an involution consists only of the
identity and that involution. -/
private theorem eq_one_or_eq_of_mem_zpowers_involution
    {G : Type u} [Group G] [Finite G]
    {a x : G} (ha : IsInvolution a)
    (hx : x ∈ Subgroup.zpowers a) :
    x = 1 ∨ x = a := by
  let Z : Subgroup G := Subgroup.zpowers a
  have haOrder : orderOf a = 2 :=
    orderOf_eq_prime ha.2 ha.1
  have hZcard : Nat.card Z = 2 := by
    simp [Z, Nat.card_zpowers, haOrder]
  have haZ : a ∈ Z := Subgroup.mem_zpowers a
  have haZne : (⟨a, haZ⟩ : Z) ≠ 1 := by
    intro heq
    exact ha.1 (congrArg Subtype.val heq)
  have hZeq : ∀ z : Z, z = 1 ∨ z = ⟨a, haZ⟩ := by
    intro z
    by_cases hz : z = 1
    · exact Or.inl hz
    · rcases (Nat.card_eq_two_iff' (1 : Z)).mp hZcard with
        ⟨z0, _hz0ne, hz0uniq⟩
      exact Or.inr
        ((hz0uniq z hz).trans (hz0uniq ⟨a, haZ⟩ haZne).symm)
  rcases hZeq ⟨x, hx⟩ with hx1 | hxa
  · exact Or.inl (congrArg Subtype.val hx1)
  · exact Or.inr (congrArg Subtype.val hxa)

/-- The distinguished involution normalizes `K`, acting by inversion. -/
private theorem BrauerSuzukiWallHypotheses.s_mem_normalizer_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    h.s ∈ Subgroup.normalizer (h.K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [h.s_inverts_K x hx]
    exact h.K.inv_mem hx
  · intro hsx
    have hss : h.s * h.s = 1 := by
      simpa [pow_two] using h.s_involution.2
    have hsinv : h.s⁻¹ = h.s := inv_eq_of_mul_eq_one_right hss
    have hinv := h.s_inverts_K (h.s * x * h.s⁻¹) hsx
    have hdouble : h.s * (h.s * x * h.s⁻¹) * h.s⁻¹ = x := by
      rw [hsinv]
      calc
        h.s * (h.s * x * h.s) * h.s =
            (h.s * h.s) * x * (h.s * h.s) := by group
        _ = x := by rw [hss]; simp
    rw [hdouble.symm.trans hinv]
    exact h.K.inv_mem hsx

/-- Every element of the nontrivial coset `H \ K` has the normal form
`k * s`. -/
private theorem BrauerSuzukiWallHypotheses.exists_eq_mul_s_of_mem_H_not_mem_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {y : G} (hyH : y ∈ h.H) (hyK : y ∉ h.K) :
    ∃ k : G, k ∈ h.K ∧ y = k * h.s := by
  let Z : Subgroup G := Subgroup.zpowers h.s
  have hZNorm : Z ≤ Subgroup.normalizer (h.K : Set G) :=
    Subgroup.zpowers_le.mpr h.s_mem_normalizer_K
  have hyprod : y ∈ (h.K : Set G) * (Z : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left h.K Z hZNorm]
    rw [← h.H_eq_join]
    exact hyH
  rcases hyprod with ⟨k, hk, z, hz, hkz⟩
  rcases eq_one_or_eq_of_mem_zpowers_involution h.s_involution hz with hz1 | hzs
  · exfalso
    apply hyK
    have hyk : y = k := by simpa [hz1] using hkz.symm
    simpa [hyk] using hk
  · exact ⟨k, hk, by simpa [hzs] using hkz.symm⟩

/-- The nontrivial coset `H \ K` consists of involutions. -/
private theorem BrauerSuzukiWallHypotheses.isInvolution_of_mem_H_not_mem_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {y : G} (hyH : y ∈ h.H) (hyK : y ∉ h.K) :
    IsInvolution y := by
  obtain ⟨k, hk, rfl⟩ := h.exists_eq_mul_s_of_mem_H_not_mem_K hyH hyK
  have hsk := h.s_inverts_K k hk
  have hss : h.s * h.s = 1 := by
    simpa [pow_two] using h.s_involution.2
  constructor
  · intro hks
    apply h.s_not_mem_K
    have hs_eq : h.s = k⁻¹ := eq_inv_of_mul_eq_one_right hks
    rw [hs_eq]
    exact h.K.inv_mem hk
  · rw [pow_two]
    calc
      (k * h.s) * (k * h.s) =
          k * (h.s * k * h.s⁻¹) * (h.s * h.s) := by group
      _ = 1 := by rw [hsk, hss]; simp

/-- Every element of `H \ K` inverts `K`. -/
private theorem BrauerSuzukiWallHypotheses.conjugates_eq_inv_of_mem_H_not_mem_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {y x : G} (hyH : y ∈ h.H) (hyK : y ∉ h.K) (hxK : x ∈ h.K) :
    y * x * y⁻¹ = x⁻¹ := by
  obtain ⟨k, hk, rfl⟩ := h.exists_eq_mul_s_of_mem_H_not_mem_K hyH hyK
  have hkx : Commute k x := by
    rw [commute_iff_eq]
    let : IsMulCommutative h.K := h.K_commutative
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := h.K)).comm ⟨k, hk⟩ ⟨x, hxK⟩)
  calc
    (k * h.s) * x * (k * h.s)⁻¹ =
        k * (h.s * x * h.s⁻¹) * k⁻¹ := by group
    _ = k * x⁻¹ * k⁻¹ := by rw [h.s_inverts_K x hxK]
    _ = x⁻¹ := hkx.inv_right.mul_inv_cancel

/-- The distinguished element `t` is the unique involution of `K`. -/
private theorem BrauerSuzukiWallHypotheses.eq_t_of_mem_K_of_isInvolution
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {x : G} (hxK : x ∈ h.K) (hxI : IsInvolution x) :
    x = h.t := by
  have hxx : x * x = 1 := by simpa [pow_two] using hxI.2
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hsfix : h.s * x * h.s⁻¹ = x := by
    rw [h.s_inverts_K x hxK, hxi]
  have hxcent : x ∈ Subgroup.centralizer ({h.s} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzs : z = h.s := by simpa using hz
    rw [hzs]
    have hcomm := congrArg (fun q : G => q * h.s) hsfix
    simpa [mul_assoc] using hcomm
  have hxZ : x ∈ Subgroup.zpowers h.t := by
    have hxInf : x ∈ h.K ⊓ Subgroup.centralizer ({h.s} : Set G) :=
      ⟨hxK, hxcent⟩
    rw [h.fixed_subgroup_eq] at hxInf
    exact hxInf
  rcases eq_one_or_eq_of_mem_zpowers_involution h.t_involution hxZ with hx1 | hxt
  · exact False.elim (hxI.1 hx1)
  · exact hxt

/-- The distinguished involution makes `|K|` even. -/
private theorem BrauerSuzukiWallHypotheses.card_K_even
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) : Even (Nat.card h.K) := by
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  have htKne : tK ≠ 1 := by
    intro htKone
    exact h.t_involution.1 (congrArg Subtype.val htKone)
  have htKsq : tK ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htKorder : orderOf tK = 2 :=
    orderOf_eq_prime htKsq htKne
  rw [even_iff_two_dvd, ← htKorder]
  exact orderOf_dvd_natCard tK

/-- The involutions of `H` are the distinguished involution `t` together
with the `|K|` elements of the nontrivial coset `Ks`. -/
private noncomputable def bsw_H_involutions_equiv_option_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Option h.K ≃ {y : G // y ∈ h.H ∧ IsInvolution y} := by
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact (show Subgroup.zpowers h.s ≤ h.K ⊔ Subgroup.zpowers h.s from
      le_sup_right) (Subgroup.mem_zpowers h.s)
  have hmulNotK (k : h.K) : (k : G) * h.s ∉ h.K := by
    intro hksK
    apply h.s_not_mem_K
    have hmem := h.K.mul_mem (h.K.inv_mem k.property) hksK
    simpa [mul_assoc] using hmem
  let toFun : Option h.K → {y : G // y ∈ h.H ∧ IsInvolution y}
    | none => ⟨h.t, hKleH h.t_mem_K, h.t_involution⟩
    | some k =>
        ⟨(k : G) * h.s,
          h.H.mul_mem (hKleH k.property) hsH,
          h.isInvolution_of_mem_H_not_mem_K
            (h.H.mul_mem (hKleH k.property) hsH) (hmulNotK k)⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro a b hab
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some k =>
            exfalso
            have heq := congrArg Subtype.val hab
            change h.t = (k : G) * h.s at heq
            apply hmulNotK k
            rw [← heq]
            exact h.t_mem_K
    | some k =>
        cases b with
        | none =>
            exfalso
            have heq := congrArg Subtype.val hab
            change (k : G) * h.s = h.t at heq
            apply hmulNotK k
            rw [heq]
            exact h.t_mem_K
        | some l =>
            apply congrArg some
            apply Subtype.ext
            have heq := congrArg Subtype.val hab
            exact mul_right_cancel heq
  · intro y
    by_cases hyK : (y : G) ∈ h.K
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      exact (h.eq_t_of_mem_K_of_isInvolution hyK y.property.2).symm
    · obtain ⟨k, hkK, hy⟩ :=
        h.exists_eq_mul_s_of_mem_H_not_mem_K y.property.1 hyK
      refine ⟨some ⟨k, hkK⟩, ?_⟩
      apply Subtype.ext
      exact hy.symm

/-- The distinguished centralizer `H` contains exactly `|K| + 1`
involutions. -/
private theorem bsw_H_involutions_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Nat.card {y : G // y ∈ h.H ∧ IsInvolution y} =
      Nat.card h.K + 1 := by
  calc
    Nat.card {y : G // y ∈ h.H ∧ IsInvolution y} =
        Nat.card (Option h.K) :=
      (Nat.card_congr (bsw_H_involutions_equiv_option_K h)).symm
    _ = Nat.card h.K + 1 := by simp

/-- For a nonidentity product in `K`, the first involution in the product
fiber lies in the nontrivial coset `H \ K`. -/
private theorem bswPair_first_mem_H_not_mem_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {x : G} (hxK : x ∈ h.K) (hxne : x ≠ 1)
    (p : bswPairFiber G x) :
    (p.1.1 : G) ∈ h.H ∧ (p.1.1 : G) ∉ h.K := by
  let u : G := p.1.1
  let v : G := p.1.2
  have huI : IsInvolution u := p.1.1.2
  have hvI : IsInvolution v := p.1.2.2
  have huv : u * v = x := p.2
  have huinv : u * x * u⁻¹ = x⁻¹ :=
    bswPair_first_inverts_product huI hvI huv
  have hsinv : h.s * x * h.s⁻¹ = x⁻¹ := h.s_inverts_K x hxK
  have husconj : (u * h.s) * x * (u * h.s)⁻¹ = x := by
    calc
      (u * h.s) * x * (u * h.s)⁻¹ =
          u * (h.s * x * h.s⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hsinv]
      _ = x := by
        have hinv := congrArg Inv.inv huinv
        simpa [mul_inv_rev, mul_assoc] using hinv
  have husC : u * h.s ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm := congrArg (fun z : G => z * (u * h.s)) husconj
    simpa [mul_assoc] using hcomm
  have husH : u * h.s ∈ h.H :=
    h.isTISubsetRelative.2.2.2 x hxK hxne husC
  have hsH : h.s ∈ h.H := by
    rw [h.H_eq_join]
    exact (show Subgroup.zpowers h.s ≤ h.K ⊔ Subgroup.zpowers h.s from
      le_sup_right) (Subgroup.mem_zpowers h.s)
  have hss : h.s * h.s = 1 := by
    simpa [pow_two] using h.s_involution.2
  have huH : u ∈ h.H := by
    have hm := h.H.mul_mem husH hsH
    simpa [mul_assoc, hss] using hm
  refine ⟨huH, ?_⟩
  intro huK
  have huu : u * u = 1 := by simpa [pow_two] using huI.2
  have hv_eq : v = u * x := by
    calc
      v = 1 * v := by simp
      _ = (u * u) * v := by rw [huu]
      _ = u * (u * v) := by group
      _ = u * x := by rw [huv]
  have hvK : v ∈ h.K := by
    rw [hv_eq]
    exact h.K.mul_mem huK hxK
  have hut : u = h.t := h.eq_t_of_mem_K_of_isInvolution huK huI
  have hvt : v = h.t := h.eq_t_of_mem_K_of_isInvolution hvK hvI
  apply hxne
  calc
    x = u * v := huv.symm
    _ = h.t * h.t := by rw [hut, hvt]
    _ = 1 := by simpa [pow_two] using h.t_involution.2

/-- Projection to the first coordinate identifies the product fiber over a
nonidentity element of `K` with the nontrivial coset `H \ K`. -/
private noncomputable def bswPairFiberEquivHDiffK
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {x : G} (hxK : x ∈ h.K) (hxne : x ≠ 1) :
    bswPairFiber G x ≃ ↥((h.H : Set G) \ (h.K : Set G)) := by
  let f : bswPairFiber G x → ↥((h.H : Set G) \ (h.K : Set G)) := fun p =>
    ⟨p.1.1, bswPair_first_mem_H_not_mem_K h hxK hxne p⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q hpq
    have hpqG := congrArg Subtype.val hpq
    change (p.1.1 : G) = (q.1.1 : G) at hpqG
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hpqG
    · apply Subtype.ext
      have hp : (p.1.1 : G) * (p.1.2 : G) = x := p.2
      have hq : (q.1.1 : G) * (q.1.2 : G) = x := q.2
      rw [← hpqG] at hq
      exact mul_left_cancel (hp.trans hq.symm)
  · intro y
    have hyH : (y : G) ∈ h.H := y.2.1
    have hyK : (y : G) ∉ h.K := y.2.2
    have hyI : IsInvolution (y : G) :=
      h.isInvolution_of_mem_H_not_mem_K hyH hyK
    let v : G := (y : G) * x
    have hvI : IsInvolution v := by
      have hyy : (y : G) * (y : G) = 1 := by
        simpa [pow_two] using hyI.2
      have hyinv : (y : G) * x * (y : G)⁻¹ = x⁻¹ :=
        h.conjugates_eq_inv_of_mem_H_not_mem_K hyH hyK hxK
      constructor
      · intro hv1
        apply hyK
        have hy_eq : (y : G) = x⁻¹ :=
          eq_inv_of_mul_eq_one_left hv1
        rw [hy_eq]
        exact h.K.inv_mem hxK
      · rw [pow_two]
        calc
          v * v = ((y : G) * x * (y : G)⁻¹) *
              ((y : G) * (y : G)) * x := by
                dsimp [v]
                group
          _ = 1 := by rw [hyinv, hyy]; simp
    refine ⟨⟨(⟨(y : G), hyI⟩, ⟨v, hvI⟩), ?_⟩, ?_⟩
    · change (y : G) * v = x
      dsimp [v]
      have hyy : (y : G) * (y : G) = 1 := by
        simpa [pow_two] using hyI.2
      calc
        (y : G) * ((y : G) * x) =
            ((y : G) * (y : G)) * x := by group
        _ = x := by rw [hyy]; simp
    · rfl

/-- Bender's exact local count: every nonidentity element of `K` is the
product of exactly `|K|` ordered pairs of involutions. -/
public theorem bswPairCount_eq_card_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {x : G} (hxK : x ∈ h.K) (hxne : x ≠ 1) :
    bswPairCount G x = Nat.card h.K := by
  have hKleH : (h.K : Set G) ⊆ (h.H : Set G) := by
    intro k hk
    rw [h.H_eq_join]
    exact (show h.K ≤ h.K ⊔ Subgroup.zpowers h.s from le_sup_left) hk
  have hHset : (h.H : Set G).ncard = Nat.card h.H := by
    simpa using (Nat.card_coe_set_eq (h.H : Set G)).symm
  have hKset : (h.K : Set G).ncard = Nat.card h.K := by
    simpa using (Nat.card_coe_set_eq (h.K : Set G)).symm
  calc
    bswPairCount G x =
        Nat.card ↥((h.H : Set G) \ (h.K : Set G)) :=
      Nat.card_congr (bswPairFiberEquivHDiffK h hxK hxne)
    _ = ((h.H : Set G) \ (h.K : Set G)).ncard :=
      Nat.card_coe_set_eq _
    _ = (h.H : Set G).ncard - (h.K : Set G).ncard :=
      Set.ncard_sdiff hKleH
    _ = Nat.card h.H - Nat.card h.K := by rw [hHset, hKset]
    _ = Nat.card h.K := by rw [h.card_H]; omega

/-- The punctured subgroup `K^#`. -/
private def bswKPunctured
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) : Set G :=
  {x | x ∈ h.K ∧ x ≠ 1}

/-- The union of all conjugates of `K^#`. -/
private def bswKConjugates
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) : Set G :=
  {z | ∃ x : G, x ∈ h.K ∧ x ≠ 1 ∧
      ∃ g : G, z = g * x * g⁻¹}

/-- Because distinct conjugates of `K` meet trivially and
`N_G(K) = H`, the conjugate union of `K^#` is parametrized by a right coset
of `H` and an element of `K^#`. -/
private noncomputable def bswKConjugatesEquiv
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    (Quotient (QuotientGroup.rightRel h.H) × ↥(bswKPunctured h)) ≃
      ↥(bswKConjugates h) := by
  let Ω := Quotient (QuotientGroup.rightRel h.H)
  let X0 := ↥(bswKPunctured h)
  let C0 := ↥(bswKConjugates h)
  let f : Ω × X0 → C0 := fun qx =>
    let a : G := Quotient.out qx.1
    ⟨a⁻¹ * qx.2.1 * a,
      ⟨qx.2.1, qx.2.2.1, qx.2.2.2, a⁻¹, by simp [mul_assoc]⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro qx1 qx2 hEq
    rcases qx1 with ⟨q1, x1⟩
    rcases qx2 with ⟨q2, x2⟩
    let a1 : G := Quotient.out q1
    let a2 : G := Quotient.out q2
    have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
      congrArg Subtype.val hEq
    by_cases hq : q1 = q2
    · have ha : a2 = a1 := by
        simpa [a1, a2] using congrArg Quotient.out hq.symm
      have hx : x1 = x2 := by
        apply Subtype.ext
        rw [ha] at hval
        have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
        simpa [a1, mul_assoc] using hconj
      cases hq
      cases hx
      rfl
    · have hgNotH : a1 * a2⁻¹ ∉ h.H := by
        intro hgH
        apply hq
        have hginv : a2 * a1⁻¹ ∈ h.H := by
          simpa using h.H.inv_mem hgH
        calc
          q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
          _ = Quotient.mk'' a2 :=
            Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
          _ = q2 := Quotient.out_eq' q2
      have hconjEq :
          x1.1 = (a1 * a2⁻¹) * x2.1 * (a1 * a2⁻¹)⁻¹ := by
        have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
        simpa [a1, a2, mul_assoc] using hconj
      have hx1Conj : x1.1 ∈ h.K.conjBy (a1 * a2⁻¹) := by
        refine Subgroup.mem_map.mpr ⟨x2.1, x2.2.1, ?_⟩
        change (a1 * a2⁻¹) * x2.1 * (a1 * a2⁻¹)⁻¹ = x1.1
        exact hconjEq.symm
      have hx1one : x1.1 = 1 :=
        Subgroup.disjoint_def.mp
          (h.conjugate_disjoint (a1 * a2⁻¹) hgNotH)
          x1.2.1 hx1Conj
      exact False.elim (x1.2.2 hx1one)
  · intro z
    rcases z.2 with ⟨x, hxK, hxne, y, hzy⟩
    let q : Ω := Quotient.mk'' y⁻¹
    let a : G := Quotient.out q
    have hyaH : y⁻¹ * a⁻¹ ∈ h.H := by
      have hqa : (Quotient.mk'' a : Ω) = Quotient.mk'' y⁻¹ := by
        simp [q, a]
      exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
    let n : G := y⁻¹ * a⁻¹
    have hnInvNorm : n⁻¹ ∈ Subgroup.normalizer (h.K : Set G) := by
      rw [h.isTISubsetRelative.2.1]
      exact h.H.inv_mem hyaH
    have hx'K : n⁻¹ * x * n ∈ h.K := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp hnInvNorm x).mp hxK
    have hx'ne : n⁻¹ * x * n ≠ 1 := by
      intro hone
      apply hxne
      have hconj := congrArg (fun z : G => n * z * n⁻¹) hone
      simpa [mul_assoc] using hconj
    refine ⟨(q, ⟨n⁻¹ * x * n, hx'K, hx'ne⟩), ?_⟩
    apply Subtype.ext
    calc
      ((f (q, ⟨n⁻¹ * x * n, hx'K, hx'ne⟩)).1) =
          y * x * y⁻¹ := by
        simp [f, q, a, n, mul_assoc]
      _ = z := hzy.symm

/-- The punctured conjugate union has the expected TI cardinality. -/
private theorem bswKConjugates_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Nat.card ↥(bswKConjugates h) =
      h.H.index * (Nat.card h.K - 1) := by
  let Ω := Quotient (QuotientGroup.rightRel h.H)
  have hcardOmega : Nat.card Ω = h.H.index := by
    calc
      Nat.card Ω = Nat.card (G ⧸ h.H) := by
        exact Nat.card_congr
          (QuotientGroup.quotientRightRelEquivQuotientLeftRel h.H)
      _ = h.H.index := h.H.index_eq_card.symm
  have honeK : ({1} : Set G) ⊆ (h.K : Set G) := by simp
  have hKset : (h.K : Set G).ncard = Nat.card h.K := by
    simpa using (Nat.card_coe_set_eq (h.K : Set G)).symm
  have hcardX :
      Nat.card ↥(bswKPunctured h) = Nat.card h.K - 1 := by
    calc
      Nat.card ↥(bswKPunctured h) =
          ((h.K : Set G) \ {1}).ncard := by
        rw [Nat.card_coe_set_eq]
        rfl
      _ = (h.K : Set G).ncard - ({1} : Set G).ncard :=
        Set.ncard_sdiff honeK
      _ = Nat.card h.K - 1 := by rw [hKset]; simp
  calc
    Nat.card ↥(bswKConjugates h) =
        Nat.card (Ω × ↥(bswKPunctured h)) :=
      Nat.card_congr (bswKConjugatesEquiv h).symm
    _ = Nat.card Ω * Nat.card ↥(bswKPunctured h) := Nat.card_prod _ _
    _ = h.H.index * (Nat.card h.K - 1) := by rw [hcardOmega, hcardX]

/-- The punctured set of an arbitrary subgroup. -/
private def bswSubgroupPunctured
    {G : Type u} [Group G] (P : Subgroup G) : Set G :=
  {x | x ∈ P ∧ x ≠ 1}

/-- The union of all conjugates of the punctured subgroup. -/
private def bswSubgroupConjugates
    {G : Type u} [Group G] (P : Subgroup G) : Set G :=
  {z | ∃ x : G, x ∈ P ∧ x ≠ 1 ∧
      ∃ g : G, z = g * x * g⁻¹}

/-- A nontrivial relative-TI subgroup has its punctured conjugate union
parametrized by normalizer right cosets and its own nonidentity elements. -/
private noncomputable def bswSubgroupConjugatesEquiv
    {G : Type u} [Group G] [Finite G]
    (P N : Subgroup G) (hPne : P ≠ ⊥)
    (hTI : Suzuki.VI.IsTISubsetRelative N (P : Set G)) :
    (Quotient (QuotientGroup.rightRel N) ×
        ↥(bswSubgroupPunctured P)) ≃
      ↥(bswSubgroupConjugates P) := by
  let Omega := Quotient (QuotientGroup.rightRel N)
  let X0 := ↥(bswSubgroupPunctured P)
  let C0 := ↥(bswSubgroupConjugates P)
  let f : Omega × X0 → C0 := fun qx =>
    let a : G := Quotient.out qx.1
    ⟨a⁻¹ * qx.2.1 * a,
      ⟨qx.2.1, qx.2.2.1, qx.2.2.2, a⁻¹, by simp [mul_assoc]⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro qx1 qx2 hEq
    rcases qx1 with ⟨q1, x1⟩
    rcases qx2 with ⟨q2, x2⟩
    let a1 : G := Quotient.out q1
    let a2 : G := Quotient.out q2
    have hval : a1⁻¹ * x1.1 * a1 = a2⁻¹ * x2.1 * a2 :=
      congrArg Subtype.val hEq
    by_cases hq : q1 = q2
    · have ha : a2 = a1 := by
        simpa [a1, a2] using congrArg Quotient.out hq.symm
      have hx : x1 = x2 := by
        apply Subtype.ext
        rw [ha] at hval
        have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
        simpa [a1, mul_assoc] using hconj
      cases hq
      cases hx
      rfl
    · have hgNotN : a1 * a2⁻¹ ∉ N := by
        intro hgN
        apply hq
        have hginv : a2 * a1⁻¹ ∈ N := by
          simpa using N.inv_mem hgN
        calc
          q1 = Quotient.mk'' a1 := (Quotient.out_eq' q1).symm
          _ = Quotient.mk'' a2 :=
            Quotient.sound' (QuotientGroup.rightRel_apply.mpr hginv)
          _ = q2 := Quotient.out_eq' q2
      have hconjEq :
          x1.1 = (a1 * a2⁻¹) * x2.1 * (a1 * a2⁻¹)⁻¹ := by
        have hconj := congrArg (fun z : G => a1 * z * a1⁻¹) hval
        simpa [a1, a2, mul_assoc] using hconj
      have hx1Image : x1.1 ∈
          (fun z : G => (a1 * a2⁻¹) * z * (a1 * a2⁻¹)⁻¹) ''
            (P : Set G) := by
        exact ⟨x2.1, x2.2.1, hconjEq.symm⟩
      obtain ⟨p, hpne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
      have hPnontrivial : ∃ z : G, z ∈ (P : Set G) ∧ z ≠ 1 :=
        ⟨p, p.property, by simpa using hpne⟩
      have hintersection :=
        (Suzuki.VI.suzuki_ch6_proposition_2_8
          N (P : Set G) hTI.1 (le_of_eq hTI.2.1.symm)
          hPnontrivial).1 hTI (a1 * a2⁻¹) hgNotN
      have hx1one := hintersection ⟨hx1Image, x1.2.1⟩
      exact False.elim (x1.2.2 (by simpa using hx1one))
  · intro z
    rcases z.2 with ⟨x, hxP, hxne, y, hzy⟩
    let q : Omega := Quotient.mk'' y⁻¹
    let a : G := Quotient.out q
    have hyaN : y⁻¹ * a⁻¹ ∈ N := by
      have hqa : (Quotient.mk'' a : Omega) = Quotient.mk'' y⁻¹ := by
        simp [q, a]
      exact QuotientGroup.rightRel_apply.mp (Quotient.exact' hqa)
    let n : G := y⁻¹ * a⁻¹
    have hnInvNorm : n⁻¹ ∈ Subgroup.normalizer (P : Set G) := by
      rw [hTI.2.1]
      exact N.inv_mem hyaN
    have hx'P : n⁻¹ * x * n ∈ P := by
      simpa using
        (Subgroup.mem_normalizer_iff.mp hnInvNorm x).mp hxP
    have hx'ne : n⁻¹ * x * n ≠ 1 := by
      intro hone
      apply hxne
      have hconj := congrArg (fun z : G => n * z * n⁻¹) hone
      simpa [mul_assoc] using hconj
    refine ⟨(q, ⟨n⁻¹ * x * n, hx'P, hx'ne⟩), ?_⟩
    apply Subtype.ext
    calc
      ((f (q, ⟨n⁻¹ * x * n, hx'P, hx'ne⟩)).1) =
          y * x * y⁻¹ := by
        simp [f, q, a, n, mul_assoc]
      _ = z := hzy.symm

/-- Cardinality of the punctured conjugate union of a relative-TI
subgroup. -/
private theorem bswSubgroupConjugates_card
    {G : Type u} [Group G] [Finite G]
    (P N : Subgroup G) (hPne : P ≠ ⊥)
    (hTI : Suzuki.VI.IsTISubsetRelative N (P : Set G)) :
    Nat.card ↥(bswSubgroupConjugates P) =
      N.index * (Nat.card P - 1) := by
  let Omega := Quotient (QuotientGroup.rightRel N)
  have hcardOmega : Nat.card Omega = N.index := by
    calc
      Nat.card Omega = Nat.card (G ⧸ N) := by
        exact Nat.card_congr
          (QuotientGroup.quotientRightRelEquivQuotientLeftRel N)
      _ = N.index := N.index_eq_card.symm
  have honeP : ({1} : Set G) ⊆ (P : Set G) := by simp
  have hPset : (P : Set G).ncard = Nat.card P := by
    simpa using (Nat.card_coe_set_eq (P : Set G)).symm
  have hcardX :
      Nat.card ↥(bswSubgroupPunctured P) = Nat.card P - 1 := by
    calc
      Nat.card ↥(bswSubgroupPunctured P) =
          ((P : Set G) \ {1}).ncard := by
        rw [Nat.card_coe_set_eq]
        rfl
      _ = (P : Set G).ncard - ({1} : Set G).ncard :=
        Set.ncard_sdiff honeP
      _ = Nat.card P - 1 := by rw [hPset]; simp
  calc
    Nat.card ↥(bswSubgroupConjugates P) =
        Nat.card (Omega × ↥(bswSubgroupPunctured P)) :=
      Nat.card_congr (bswSubgroupConjugatesEquiv P N hPne hTI).symm
    _ = Nat.card Omega * Nat.card ↥(bswSubgroupPunctured P) :=
      Nat.card_prod _ _
    _ = N.index * (Nat.card P - 1) := by rw [hcardOmega, hcardX]

/-- The identity is not in the punctured conjugate union of a subgroup. -/
private theorem one_not_mem_bswSubgroupConjugates
    {G : Type u} [Group G] (P : Subgroup G) :
    (1 : G) ∉ bswSubgroupConjugates P := by
  rintro ⟨x, _hxP, hxne, g, hone⟩
  apply hxne
  calc
    x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * 1 * g := by rw [← hone]
    _ = 1 := by simp

/-- The punctured conjugate union of a subgroup is invariant under
conjugation. -/
private theorem mem_bswSubgroupConjugates_conj_iff
    {G : Type u} [Group G] (P : Subgroup G) (g x : G) :
    g * x * g⁻¹ ∈ bswSubgroupConjugates P ↔
      x ∈ bswSubgroupConjugates P := by
  constructor
  · rintro ⟨a, haP, hane, z, heq⟩
    refine ⟨a, haP, hane, g⁻¹ * z, ?_⟩
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (z * a * z⁻¹) * g := by rw [heq]
      _ = (g⁻¹ * z) * a * (g⁻¹ * z)⁻¹ := by group
  · rintro ⟨a, haP, hane, z, heq⟩
    refine ⟨a, haP, hane, g * z, ?_⟩
    rw [heq]
    group

/-- The punctured conjugate union of a subgroup is invariant under
inversion. -/
private theorem mem_bswSubgroupConjugates_inv_iff
    {G : Type u} [Group G] (P : Subgroup G) (x : G) :
    x⁻¹ ∈ bswSubgroupConjugates P ↔
      x ∈ bswSubgroupConjugates P := by
  constructor
  · rintro ⟨a, haP, hane, g, heq⟩
    refine ⟨a⁻¹, P.inv_mem haP, ?_, g, ?_⟩
    · simpa using hane
    · calc
        x = (x⁻¹)⁻¹ := by simp
        _ = (g * a * g⁻¹)⁻¹ := by rw [heq]
        _ = g * a⁻¹ * g⁻¹ := by group
  · rintro ⟨a, haP, hane, g, heq⟩
    refine ⟨a⁻¹, P.inv_mem haP, ?_, g, ?_⟩
    · simpa using hane
    · calc
        x⁻¹ = (g * a * g⁻¹)⁻¹ := by rw [heq]
        _ = g * a⁻¹ * g⁻¹ := by group

/-- If every nonidentity element of `P` has centralizer `P`, then the
punctured conjugate union of `P` contains every nonidentity element
centralizing one of its members. -/
private theorem mem_bswSubgroupConjugates_of_commute_of_mem
    {G : Type u} [Group G] (P : Subgroup G)
    (hCent : ∀ a : G, a ∈ P → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = P)
    {a c : G} (ha : a ∈ bswSubgroupConjugates P)
    (hcne : c ≠ 1) (hcomm : Commute c a) :
    c ∈ bswSubgroupConjugates P := by
  rcases ha with ⟨p, hpP, hpne, g, rfl⟩
  let c0 : G := g⁻¹ * c * g
  have hc0comm : Commute c0 p := by
    have hconj := hcomm.conj g⁻¹
    simpa [c0, mul_assoc] using hconj
  have hc0cent : c0 ∈ Subgroup.centralizer ({p} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc0comm
  have hc0P : c0 ∈ P := by
    rw [hCent p hpP hpne] at hc0cent
    exact hc0cent
  have hc0ne : c0 ≠ 1 := by
    intro hc0one
    apply hcne
    have hconj := congrArg (fun z : G => g * z * g⁻¹) hc0one
    simpa [c0, mul_assoc] using hconj
  refine ⟨c0, hc0P, hc0ne, g, ?_⟩
  dsimp [c0]
  group

/-- Punctured conjugate unions of subgroups of coprime orders are
disjoint. -/
private theorem bswSubgroupConjugates_disjoint_of_coprime_cards
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hcop : Nat.Coprime (Nat.card A) (Nat.card B)) :
    Disjoint (bswSubgroupConjugates A) (bswSubgroupConjugates B) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  rcases hzA with ⟨a, haA, hane, g, hza⟩
  rcases hzB with ⟨b, hbB, hbne, w, hzb⟩
  have hordA : orderOf z ∣ Nat.card A := by
    have hconj : orderOf (g * a * g⁻¹) = orderOf a := by
      simpa [MulAut.conj_apply] using (MulAut.conj g).orderOf_eq a
    rw [hza, hconj]
    exact Subgroup.orderOf_dvd_natCard A haA
  have hordB : orderOf z ∣ Nat.card B := by
    have hconj : orderOf (w * b * w⁻¹) = orderOf b := by
      simpa [MulAut.conj_apply] using (MulAut.conj w).orderOf_eq b
    rw [hzb, hconj]
    exact Subgroup.orderOf_dvd_natCard B hbB
  have hord : orderOf z = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hordA hordB
  have hzone : z = 1 := orderOf_eq_one_iff.mp hord
  apply hane
  have hconj := congrArg (fun q : G => g⁻¹ * q * g) hzone
  rw [hza] at hconj
  simpa [mul_assoc] using hconj

/-- An element of prime order whose prime divides the order of a Hall
subgroup is conjugate into that subgroup. -/
private theorem exists_conjugate_mem_of_prime_order_of_coprime_card_index
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hHall : Nat.Coprime (Nat.card H) H.index)
    {p : ℕ} (hpPrime : p.Prime) (hpH : p ∣ Nat.card H)
    {a : G} (haOrder : orderOf a = p) :
    ∃ y : G, y * a * y⁻¹ ∈ H := by
  classical
  let : Fact p.Prime := ⟨hpPrime⟩
  let PH : Sylow p H := default
  let Psub : Subgroup G := (PH : Subgroup H).map H.subtype
  have hPsubP : IsPGroup p Psub := by
    simpa [Psub] using
      (IsPGroup.map (p := p) (H := (PH : Subgroup H))
        PH.isPGroup' H.subtype)
  have hpNotHindex : ¬ p ∣ H.index := by
    exact hpPrime.coprime_iff_not_dvd.mp
      (Nat.Coprime.of_dvd_left hpH hHall)
  have hpNotPHindex : ¬ p ∣ (PH : Subgroup H).index :=
    PH.not_dvd_index
  have hpNotPsubIndex : ¬ p ∣ Psub.index := by
    have hidx : Psub.index =
        (PH : Subgroup H).index * H.index := by
      simpa [Psub] using
        (Subgroup.index_map_subtype (K := (PH : Subgroup H)))
    rw [hidx]
    exact hpPrime.not_dvd_mul hpNotPHindex hpNotHindex
  let S : Sylow p G :=
    IsPGroup.toSylow (p := p) hPsubP hpNotPsubIndex
  have hSleH : (S : Subgroup G) ≤ H := by
    intro x hx
    change x ∈ Psub at hx
    rcases Subgroup.mem_map.mp hx with ⟨z, _hz, rfl⟩
    exact z.2
  let A : Subgroup G := Subgroup.zpowers a
  have hAP : IsPGroup p A := by
    exact IsPGroup.of_card
      (((Nat.card_zpowers a).trans haOrder).trans (pow_one p).symm)
  obtain ⟨Q, hAQ⟩ := IsPGroup.exists_le_sylow (G := G) (p := p) hAP
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G Q S
  refine ⟨y, ?_⟩
  have haQ : a ∈ (Q : Subgroup G) := hAQ (Subgroup.mem_zpowers a)
  have hayS : y * a * y⁻¹ ∈ (S : Subgroup G) := by
    have hmem : (MulAut.conj y) a ∈
        ((y • Q : Sylow p G) : Subgroup G) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul
        a (MulAut.conj y) (Q : Subgroup G) haQ
    simpa [MulAut.conj_apply, hy] using hmem
  exact hSleH hayS

/-- The elements outside the identity and the two punctured conjugate
unions in Bender 3.5. -/
private def bswResidualSet
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G) : Set G :=
  ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F)ᶜ

/-- Conjugation preserves involutions. -/
private theorem bswInvolution_conj
    {G : Type u} [Group G] {x : G}
    (hx : IsInvolution x) (g : G) :
    IsInvolution (g * x * g⁻¹) := by
  constructor
  · intro hone
    apply hx.1
    have hconj := congrArg (fun z : G => g⁻¹ * z * g) hone
    simpa [mul_assoc] using hconj
  · calc
      (g * x * g⁻¹) ^ 2 = g * (x ^ 2) * g⁻¹ := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hx.2]; simp

/-- Simultaneous conjugation of both factors identifies the product fibers
over conjugate elements. -/
private noncomputable def bswPairFiberConjEquiv
    {G : Type u} [Group G] (g x : G) :
    bswPairFiber G x ≃ bswPairFiber G (g * x * g⁻¹) where
  toFun p := by
    refine ⟨(⟨g * p.1.1 * g⁻¹, bswInvolution_conj p.1.1.2 g⟩,
      ⟨g * p.1.2 * g⁻¹, bswInvolution_conj p.1.2.2 g⟩), ?_⟩
    calc
      (g * (p.1.1 : G) * g⁻¹) * (g * (p.1.2 : G) * g⁻¹) =
          g * ((p.1.1 : G) * (p.1.2 : G)) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [p.2]
  invFun p := by
    refine ⟨(⟨g⁻¹ * p.1.1 * (g⁻¹)⁻¹,
        bswInvolution_conj p.1.1.2 g⁻¹⟩,
      ⟨g⁻¹ * p.1.2 * (g⁻¹)⁻¹,
        bswInvolution_conj p.1.2.2 g⁻¹⟩), ?_⟩
    calc
      (g⁻¹ * (p.1.1 : G) * (g⁻¹)⁻¹) *
          (g⁻¹ * (p.1.2 : G) * (g⁻¹)⁻¹) =
          g⁻¹ * ((p.1.1 : G) * (p.1.2 : G)) * (g⁻¹)⁻¹ := by group
      _ = x := by rw [p.2]; group
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_assoc]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> simp [mul_assoc]

/-- Bender's pair count is constant on conjugacy classes. -/
private theorem bswPairCount_conj
    {G : Type u} [Group G] [Finite G] (g x : G) :
    bswPairCount G (g * x * g⁻¹) = bswPairCount G x := by
  exact Nat.card_congr (bswPairFiberConjEquiv g x).symm

/-- Every element in the punctured conjugate union of `K` has pair count
`|K|`. -/
private theorem bswPairCount_eq_card_K_of_mem_conjugates
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    {z : G} (hz : z ∈ bswKConjugates h) :
    bswPairCount G z = Nat.card h.K := by
  rcases hz with ⟨x, hxK, hxne, g, rfl⟩
  rw [bswPairCount_conj]
  exact bswPairCount_eq_card_K h hxK hxne

/-- The identity is not in the union of the conjugates of `K^#`. -/
private theorem one_not_mem_bswKConjugates
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    (1 : G) ∉ bswKConjugates h := by
  rintro ⟨x, _hxK, hxne, g, hone⟩
  apply hxne
  calc
    x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * 1 * g := by rw [← hone]
    _ = 1 := by simp

/-- A finite nonempty family of natural numbers contains a value at least
its average, in division-free form. -/
private theorem exists_card_mul_ge_sum
    {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℕ) :
    ∃ x ∈ s, ∑ y ∈ s, f y ≤ s.card * f x := by
  apply Finset.exists_le_of_sum_le hs
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  exact le_rfl

/-- Bender's pair-count averaging step, before substituting either order
case.  The selected element lies outside the identity and every conjugate of
`K^#`; the displayed inequality is exactly the division-free average. -/
private theorem exists_bswPairCount_average_outside
    {G : Type u} [Group G] [Fintype G]
    (h : BrauerSuzukiWallHypotheses G) (hk : 4 < Nat.card h.K) :
    ∃ x : G,
      x ∉ bswKConjugates h ∧ x ≠ 1 ∧
        h.H.index ^ 2 ≤
          (Nat.card G - (h.H.index * (Nat.card h.K - 1) + 1)) *
              bswPairCount G x +
            h.H.index +
            h.H.index * (Nat.card h.K - 1) * Nat.card h.K := by
  classical
  let C : Finset G := (bswKConjugates h).toFinset
  let S : Finset G := insert 1 C
  let T : Finset G := Finset.univ \ S
  have honeC : (1 : G) ∉ C := by
    simp [C, one_not_mem_bswKConjugates h]
  have hCcard : C.card = h.H.index * (Nat.card h.K - 1) := by
    calc
      C.card = (bswKConjugates h).ncard := by
        simpa [C] using (Set.ncard_eq_toFinset_card' (bswKConjugates h)).symm
      _ = Nat.card ↥(bswKConjugates h) :=
        (Nat.card_coe_set_eq (bswKConjugates h)).symm
      _ = h.H.index * (Nat.card h.K - 1) := bswKConjugates_card h
  have hScard : S.card = h.H.index * (Nat.card h.K - 1) + 1 := by
    rw [show S = insert 1 C from rfl, Finset.card_insert_of_notMem honeC,
      hCcard]
  have hsumC :
      (∑ x ∈ C, bswPairCount G x) =
        (h.H.index * (Nat.card h.K - 1)) * Nat.card h.K := by
    calc
      (∑ x ∈ C, bswPairCount G x) =
          ∑ _x ∈ C, Nat.card h.K := by
        apply Finset.sum_congr rfl
        intro x hxC
        exact bswPairCount_eq_card_K_of_mem_conjugates h (by
          simpa [C] using hxC)
      _ = C.card * Nat.card h.K := by simp
      _ = (h.H.index * (Nat.card h.K - 1)) * Nat.card h.K := by rw [hCcard]
  have hsumS :
      (∑ x ∈ S, bswPairCount G x) =
        h.H.index +
          (h.H.index * (Nat.card h.K - 1)) * Nat.card h.K := by
    rw [show S = insert 1 C from rfl, Finset.sum_insert honeC,
      bswPairCount_one, bswInvolutions_ncard_eq_index_H h, hsumC]
  have hsumAll :
      (∑ x ∈ (Finset.univ : Finset G), bswPairCount G x) =
        h.H.index ^ 2 := by
    simpa [bswInvolutions_ncard_eq_index_H h] using
      (sum_bswPairCount (G := G))
  have hST : S ⊆ (Finset.univ : Finset G) := by simp
  have hsplit :
      (∑ x ∈ T, bswPairCount G x) +
          (∑ x ∈ S, bswPairCount G x) =
        ∑ x ∈ (Finset.univ : Finset G), bswPairCount G x := by
    simpa [T] using
      (Finset.sum_sdiff (f := fun x : G => bswPairCount G x) hST)
  rw [hsumS, hsumAll] at hsplit
  have hGcard : Nat.card G = 2 * Nat.card h.K * h.H.index := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = 2 * Nat.card h.K * h.H.index := by rw [h.card_H]
  have hIpos : 0 < h.H.index :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := h.H))
  have hKpos : 0 < Nat.card h.K := by omega
  have hmulLt :
      h.H.index * (Nat.card h.K - 1) <
        h.H.index * Nat.card h.K :=
    Nat.mul_lt_mul_of_pos_left (by omega) hIpos
  have hregionLe :
      h.H.index * (Nat.card h.K - 1) + 1 ≤
        h.H.index * Nat.card h.K := by omega
  have hIkpos : 0 < h.H.index * Nat.card h.K :=
    Nat.mul_pos hIpos hKpos
  have hSlt : S.card < Fintype.card G := by
    calc
      S.card = h.H.index * (Nat.card h.K - 1) + 1 := hScard
      _ ≤ h.H.index * Nat.card h.K := hregionLe
      _ < 2 * Nat.card h.K * h.H.index := by nlinarith
      _ = Nat.card G := hGcard.symm
      _ = Fintype.card G := Nat.card_eq_fintype_card
  have hTcard :
      T.card = Nat.card G - (h.H.index * (Nat.card h.K - 1) + 1) := by
    calc
      T.card = (Finset.univ : Finset G).card - S.card := by
        simpa [T] using Finset.card_sdiff_of_subset hST
      _ = Nat.card G - (h.H.index * (Nat.card h.K - 1) + 1) := by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hScard]
  have hTnonempty : T.Nonempty := by
    apply Finset.card_pos.mp
    rw [hTcard]
    rw [← Nat.card_eq_fintype_card] at hSlt
    omega
  obtain ⟨x, hxT, havg⟩ :=
    exists_card_mul_ge_sum T hTnonempty (fun y => bswPairCount G y)
  have hxS : x ∉ S := (Finset.mem_sdiff.mp hxT).2
  have hxone : x ≠ 1 := by
    intro hx
    apply hxS
    simp [S, hx]
  have hxC : x ∉ bswKConjugates h := by
    intro hx
    apply hxS
    simp [S, C, hx]
  refine ⟨x, hxC, hxone, ?_⟩
  rw [← hTcard]
  omega

/-- The two group-order alternatives give the corresponding values of
`|G:H|` by cancellation of `|H| = 2|K|`. -/
private theorem bswIndex_H_order_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (horder :
      let k := Nat.card h.K
      Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
        Nat.card G = (2 * k - 1) * (k - 1) * (2 * k)) :
    h.H.index = (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∨
      h.H.index = (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) := by
  dsimp only at horder
  have hkpos : 0 < 2 * Nat.card h.K := by
    have : 0 < Nat.card h.K := Nat.card_pos
    omega
  rcases horder with hplus | hminus
  · left
    apply Nat.eq_of_mul_eq_mul_left hkpos
    calc
      (2 * Nat.card h.K) * h.H.index = Nat.card G := by
        rw [← h.card_H]
        exact h.H.card_mul_index
      _ = (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) *
          (2 * Nat.card h.K) := hplus
      _ = (2 * Nat.card h.K) *
          ((2 * Nat.card h.K + 1) * (Nat.card h.K + 1)) := by ring
  · right
    apply Nat.eq_of_mul_eq_mul_left hkpos
    calc
      (2 * Nat.card h.K) * h.H.index = Nat.card G := by
        rw [← h.card_H]
        exact h.H.card_mul_index
      _ = (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) *
          (2 * Nat.card h.K) := hminus
      _ = (2 * Nat.card h.K) *
          ((2 * Nat.card h.K - 1) * (Nat.card h.K - 1)) := by ring

/-- Substituting the two possible indices into the averaging inequality
gives the integral lower bounds used in Bender 3.1(iv). -/
private theorem exists_bswPairCount_order_bound
    {G : Type u} [Group G] [Fintype G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K)
    (horder :
      let k := Nat.card h.K
      Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
        Nat.card G = (2 * k - 1) * (k - 1) * (2 * k)) :
    ∃ x : G,
      x ∉ bswKConjugates h ∧ x ≠ 1 ∧
        ((h.H.index =
              (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
            Nat.card h.K + 3 ≤ bswPairCount G x) ∨
          (h.H.index =
              (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
            Nat.card h.K - 2 ≤ bswPairCount G x)) := by
  obtain ⟨x, hxC, hxne, havg⟩ :=
    exists_bswPairCount_average_outside h hk
  let k := Nat.card h.K
  let I := h.H.index
  let D := Nat.card G - (I * (k - 1) + 1)
  have hGcard : Nat.card G = 2 * k * I := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = 2 * k * I := by rw [h.card_H]
  have hDle : D ≤ I * (k + 1) := by
    dsimp [D]
    rw [Nat.sub_le_iff_le_add, hGcard]
    have hkdec : k - 1 + 1 = k := by
      dsimp [k]
      omega
    nlinarith
  have havg' : I ^ 2 ≤ D * bswPairCount G x + I + I * (k - 1) * k := by
    simpa [I, k, D, mul_assoc] using havg
  rcases bswIndex_H_order_cases h horder with hplus | hminus
  · refine ⟨x, hxC, hxne, Or.inl ⟨hplus, ?_⟩⟩
    change k + 3 ≤ bswPairCount G x
    by_contra hnot
    have hi : bswPairCount G x ≤ k + 2 := by omega
    have hDi : D * bswPairCount G x ≤ (I * (k + 1)) * (k + 2) :=
      Nat.mul_le_mul hDle hi
    have hkdec : k - 1 + 1 = k := by
      dsimp [k]
      omega
    have hI : I = (2 * k + 1) * (k + 1) := by simpa [I, k] using hplus
    nlinarith
  · refine ⟨x, hxC, hxne, Or.inr ⟨hminus, ?_⟩⟩
    change k - 2 ≤ bswPairCount G x
    by_contra hnot
    have hi : bswPairCount G x ≤ k - 3 := by
      dsimp [k] at hnot ⊢
      omega
    have hk1 : 1 ≤ k := by
      dsimp [k]
      omega
    have hk3 : 3 ≤ k := by
      dsimp [k]
      omega
    have h2k1 : 1 ≤ 2 * k := by omega
    have hI : I = (2 * k - 1) * (k - 1) := by simpa [I, k] using hminus
    have hI' : (I : ℤ) = (2 * (k : ℤ) - 1) * ((k : ℤ) - 1) := by
      calc
        (I : ℤ) = (((2 * k - 1) * (k - 1) : ℕ) : ℤ) := by omega
        _ = (2 * (k : ℤ) - 1) * ((k : ℤ) - 1) := by
          push_cast [Nat.cast_sub h2k1, Nat.cast_sub hk1]
          rfl
    have hDi : D * bswPairCount G x ≤ (I * (k + 1)) * (k - 3) :=
      Nat.mul_le_mul hDle hi
    have hDi' : (D : ℤ) * (bswPairCount G x : ℤ) ≤
        (I : ℤ) * ((k : ℤ) + 1) * ((k : ℤ) - 3) := by
      calc
        (D : ℤ) * (bswPairCount G x : ℤ) =
            ((D * bswPairCount G x : ℕ) : ℤ) := by push_cast; rfl
        _ ≤ (((I * (k + 1)) * (k - 3) : ℕ) : ℤ) := by
          exact_mod_cast hDi
        _ = (I : ℤ) * ((k : ℤ) + 1) * ((k : ℤ) - 3) := by
          push_cast [Nat.cast_sub hk3]
          rfl
    have havgInt : (I : ℤ) ^ 2 ≤
        (D : ℤ) * (bswPairCount G x : ℤ) + I +
          I * ((k : ℤ) - 1) * k := by
      calc
        (I : ℤ) ^ 2 = ((I ^ 2 : ℕ) : ℤ) := by push_cast; rfl
        _ ≤ ((D * bswPairCount G x + I + I * (k - 1) * k : ℕ) : ℤ) := by
          exact_mod_cast havg'
        _ = (D : ℤ) * (bswPairCount G x : ℤ) + I +
            I * ((k : ℤ) - 1) * k := by
          push_cast [Nat.cast_sub hk1]
          rfl
    nlinarith

/-- The punctured conjugate union is invariant under conjugation. -/
private theorem mem_bswKConjugates_conj_iff
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (g x : G) :
    g * x * g⁻¹ ∈ bswKConjugates h ↔ x ∈ bswKConjugates h := by
  constructor
  · rintro ⟨a, haK, hane, z, heq⟩
    refine ⟨a, haK, hane, g⁻¹ * z, ?_⟩
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (z * a * z⁻¹) * g := by rw [heq]
      _ = (g⁻¹ * z) * a * (g⁻¹ * z)⁻¹ := by group
  · rintro ⟨a, haK, hane, z, heq⟩
    refine ⟨a, haK, hane, g * z, ?_⟩
    rw [heq]
    group

/-- Every involution lies in the punctured conjugate union of `K`, since all
involutions are conjugate to the distinguished element `t ∈ K`. -/
private theorem mem_bswKConjugates_of_isInvolution
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G} (hxI : IsInvolution x) :
    x ∈ bswKConjugates h := by
  obtain ⟨g, hg⟩ := h.involutions_conjugate x hxI
  refine ⟨h.t, h.t_mem_K, h.t_involution.1, g⁻¹, ?_⟩
  calc
    x = g⁻¹ * (g * x * g⁻¹) * g := by group
    _ = g⁻¹ * h.t * g := by rw [hg]
    _ = g⁻¹ * h.t * (g⁻¹)⁻¹ := by simp

/-- Every nonidentity element of `H` lies in the punctured conjugate union of
`K`, which is the equality `H^G = K^G` used at the start of Bender's
completion argument. -/
private theorem mem_bswKConjugates_of_mem_H_of_ne_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxH : x ∈ h.H) (hxne : x ≠ 1) :
    x ∈ bswKConjugates h := by
  by_cases hxK : x ∈ h.K
  · exact ⟨x, hxK, hxne, 1, by simp⟩
  · have hxI : IsInvolution x :=
      h.isInvolution_of_mem_H_not_mem_K hxH hxK
    exact mem_bswKConjugates_of_isInvolution h hxI

/-- The TI property forces every element centralizing a nonidentity element
of `K` into `H = N_G(K)`. -/
private theorem mem_H_of_commute_mem_K_of_ne_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {a c : G}
    (haK : a ∈ h.K) (hane : a ≠ 1) (hc : Commute c a) :
    c ∈ h.H := by
  by_contra hcH
  have hdisj : Disjoint h.K (h.K.conjBy c) := h.conjugate_disjoint c hcH
  have haConj : a ∈ h.K.conjBy c := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨a, haK, ?_⟩
    change c * a * c⁻¹ = a
    rw [hc.eq]
    simp
  exact hane (Subgroup.disjoint_def.mp hdisj haK haConj)

/-- The punctured conjugate union of `K` contains the nonidentity centralizer
of each of its elements. -/
private theorem mem_bswKConjugates_of_commute_of_mem_bswKConjugates
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {a c : G}
    (ha : a ∈ bswKConjugates h) (hcne : c ≠ 1)
    (hcomm : Commute c a) :
    c ∈ bswKConjugates h := by
  rcases ha with ⟨k, hkK, hkne, g, rfl⟩
  let c0 : G := g⁻¹ * c * g
  have hc0comm : Commute c0 k := by
    have hconj := hcomm.conj g⁻¹
    simpa [c0, mul_assoc] using hconj
  have hc0H : c0 ∈ h.H :=
    mem_H_of_commute_mem_K_of_ne_one h hkK hkne hc0comm
  have hc0ne : c0 ≠ 1 := by
    intro hc0one
    apply hcne
    have hconj := congrArg (fun z : G => g * z * g⁻¹) hc0one
    simpa [c0, mul_assoc] using hconj
  have hc0C : c0 ∈ bswKConjugates h :=
    mem_bswKConjugates_of_mem_H_of_ne_one h hc0H hc0ne
  have hcC := (mem_bswKConjugates_conj_iff h g c0).mpr hc0C
  simpa [c0, mul_assoc] using hcC

/-- If `a` lies outside the conjugate union of `K` and is inverted by `t`,
then conjugation by `t` is a fixed-point-free involution of `C_G(a)`.
Consequently the centralizer is abelian, has odd order, and is inverted by
`t`.  This expands the first fixed-point-free argument in Bender 3.1. -/
private theorem centralizer_data_of_not_mem_bswKConjugates_of_inverted_by_t
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {a : G}
    (haC : a ∉ bswKConjugates h) (hane : a ≠ 1)
    (htinv : h.t * a * h.t⁻¹ = a⁻¹) :
    IsMulCommutative (Subgroup.centralizer ({a} : Set G)) ∧
      Odd (Nat.card (Subgroup.centralizer ({a} : Set G))) ∧
      ∀ y : G, y ∈ Subgroup.centralizer ({a} : Set G) →
        h.t * y * h.t⁻¹ = y⁻¹ := by
  let F : Subgroup G := Subgroup.centralizer ({a} : Set G)
  have htt : h.t * h.t = 1 := by
    simpa [pow_two] using h.t_involution.2
  have htInvSelf : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right htt
  have htNormalizesF : h.t ∈ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hpreserve : ∀ z : G, z ∈ F → h.t * z * h.t⁻¹ ∈ F := by
      intro z hzF
      have hycomm : Commute z a := by
        change z * a = a * z
        exact Subgroup.mem_centralizer_singleton_iff.mp hzF
      have hconj :
          Commute (h.t * z * h.t⁻¹) (h.t * a * h.t⁻¹) :=
        hycomm.conj h.t
      rw [htinv] at hconj
      have hcomm : Commute (h.t * z * h.t⁻¹) a := by
        simpa using hconj
      simpa [F] using
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    constructor
    · exact hpreserve y
    · intro hyF
      have htwice := hpreserve (h.t * y * h.t⁻¹) hyF
      have hdouble :
          h.t * (h.t * y * h.t⁻¹) * h.t⁻¹ = y := by
        rw [htInvSelf]
        calc
          h.t * (h.t * y * h.t) * h.t =
              (h.t * h.t) * y * (h.t * h.t) := by group
          _ = y := by rw [htt]; simp
      rw [hdouble] at htwice
      exact htwice
  let tN : Subgroup.normalizer (F : Set G) := ⟨h.t, htNormalizesF⟩
  let phi : MulAut F := F.normalizerMonoidHom tN
  have hphiInvolutive : Function.Involutive phi := by
    intro y
    apply Subtype.ext
    simp only [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [htInvSelf]
    calc
      h.t * (h.t * (y : G) * h.t) * h.t =
          (h.t * h.t) * (y : G) * (h.t * h.t) := by group
      _ = (y : G) := by rw [htt]; simp
  have hphiFixedPointFree : MonoidHom.FixedPointFree phi := by
    intro y hyfix
    apply Subtype.ext
    have hyconj : h.t * (y : G) * h.t⁻¹ = (y : G) := by
      simpa [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hyfix
    have hyH : (y : G) ∈ h.H := by
      rw [h.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hmul := congrArg (fun z : G => z * h.t) hyconj
      have hty : h.t * (y : G) = (y : G) * h.t := by
        simpa [mul_assoc] using hmul
      exact hty.symm
    by_contra hyne
    have hyC : (y : G) ∈ bswKConjugates h :=
      mem_bswKConjugates_of_mem_H_of_ne_one h hyH hyne
    have hycomm : Commute (y : G) a := by
      change (y : G) * a = a * (y : G)
      exact Subgroup.mem_centralizer_singleton_iff.mp y.property
    exact haC
      (mem_bswKConjugates_of_commute_of_mem_bswKConjugates
        h hyC hane hycomm.symm)
  have hFcomm : IsMulCommutative F := by
    refine IsMulCommutative.mk <| Std.Commutative.mk ?_
    intro y z
    exact (hphiFixedPointFree.commute_all_of_involutive
      hphiInvolutive y z).eq
  have hFodd : Odd (Nat.card F) :=
    hphiFixedPointFree.odd_card_of_involutive hphiInvolutive
  have hFinv : ∀ y : G, y ∈ F → h.t * y * h.t⁻¹ = y⁻¹ := by
    intro y hyF
    have hy := congrFun
      (hphiFixedPointFree.coe_eq_inv_of_involutive hphiInvolutive)
      (⟨y, hyF⟩ : F)
    simpa [phi, tN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hy
  exact ⟨hFcomm, hFodd, hFinv⟩

/-- Bender 3.1(i), in the form needed downstream: the selected centralizer is
abelian and odd, `t` inverts it, and every nonidentity element has exactly
that centralizer. -/
private theorem selected_centralizer_structure
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (htx : h.t * x * h.t⁻¹ = x⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    IsMulCommutative F ∧ Odd (Nat.card F) ∧
      (∀ a : G, a ∈ F → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = F ∧
          h.t * a * h.t⁻¹ = a⁻¹) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  obtain ⟨hFcomm, hFodd, hFinv⟩ :=
    centralizer_data_of_not_mem_bswKConjugates_of_inverted_by_t
      h hxC hxne htx
  refine ⟨hFcomm, hFodd, ?_⟩
  intro a haF hane
  have hacommx : Commute a x := by
    change a * x = x * a
    exact Subgroup.mem_centralizer_singleton_iff.mp haF
  have haC : a ∉ bswKConjugates h := by
    intro haC
    exact hxC
      (mem_bswKConjugates_of_commute_of_mem_bswKConjugates
        h haC hxne hacommx.symm)
  have htainv : h.t * a * h.t⁻¹ = a⁻¹ := hFinv a haF
  obtain ⟨hCacomm, _hCaodd, _hCainv⟩ :=
    centralizer_data_of_not_mem_bswKConjugates_of_inverted_by_t
      h haC hane htainv
  refine ⟨le_antisymm ?_ ?_, htainv⟩
  · intro y hyCa
    have hxCa : x ∈ Subgroup.centralizer ({a} : Set G) := by
      exact Subgroup.mem_centralizer_singleton_iff.mpr hacommx.symm
    let : IsMulCommutative (Subgroup.centralizer ({a} : Set G)) := hCacomm
    have hyx : Commute y x := by
      change y * x = x * y
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm
          (M := Subgroup.centralizer ({a} : Set G))).comm
            ⟨y, hyCa⟩ ⟨x, hxCa⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hyx
  · intro y hyF
    let : IsMulCommutative F := hFcomm
    have hya : Commute y a := by
      change y * a = a * y
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := F)).comm
          ⟨y, hyF⟩ ⟨a, haF⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mpr hya

/-- An involution that inverts a subgroup normalizes it. -/
private theorem mem_normalizer_of_involution_inverts_subgroup
    {G : Type u} [Group G] (F : Subgroup G) {u : G}
    (huI : IsInvolution u)
    (huinv : ∀ y : G, y ∈ F → u * y * u⁻¹ = y⁻¹) :
    u ∈ Subgroup.normalizer (F : Set G) := by
  have huu : u * u = 1 := by simpa [pow_two] using huI.2
  have huInvSelf : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hpreserve : ∀ z : G, z ∈ F → u * z * u⁻¹ ∈ F := by
    intro z hzF
    rw [huinv z hzF]
    exact F.inv_mem hzF
  constructor
  · exact hpreserve y
  · intro hyF
    have htwice := hpreserve (u * y * u⁻¹) hyF
    have hdouble : u * (u * y * u⁻¹) * u⁻¹ = y := by
      rw [huInvSelf]
      calc
        u * (u * y * u) * u = (u * u) * y * (u * u) := by group
        _ = y := by rw [huu]; simp
    rw [hdouble] at htwice
    exact htwice

/-- Every involution in the normalizer of the selected centralizer acts on it
fixed-point-freely, hence by inversion. -/
private theorem involution_in_normalizer_inverts_selected_centralizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (huI : IsInvolution u)
    (huN : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      u * y * u⁻¹ = y⁻¹ := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let uN : Subgroup.normalizer (F : Set G) := ⟨u, huN⟩
  let phi : MulAut F := F.normalizerMonoidHom uN
  have huu : u * u = 1 := by simpa [pow_two] using huI.2
  have huInvSelf : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hphiInvolutive : Function.Involutive phi := by
    intro y
    apply Subtype.ext
    simp only [phi, uN, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rw [huInvSelf]
    calc
      u * (u * (y : G) * u) * u =
          (u * u) * (y : G) * (u * u) := by group
      _ = (y : G) := by rw [huu]; simp
  have hphiFixedPointFree : MonoidHom.FixedPointFree phi := by
    intro y hyfix
    apply Subtype.ext
    have hyconj : u * (y : G) * u⁻¹ = (y : G) := by
      simpa [phi, uN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hyfix
    have hycommu : Commute (y : G) u := by
      have hmul := congrArg (fun z : G => z * u) hyconj
      have huy : u * (y : G) = (y : G) * u := by
        simpa [mul_assoc] using hmul
      exact huy.symm
    by_contra hyne
    have huC : u ∈ bswKConjugates h :=
      mem_bswKConjugates_of_isInvolution h huI
    have hyC : (y : G) ∈ bswKConjugates h :=
      mem_bswKConjugates_of_commute_of_mem_bswKConjugates
        h huC hyne hycommu
    have hycommx : Commute (y : G) x := by
      change (y : G) * x = x * (y : G)
      exact Subgroup.mem_centralizer_singleton_iff.mp y.property
    exact hxC
      (mem_bswKConjugates_of_commute_of_mem_bswKConjugates
        h hyC hxne hycommx.symm)
  intro y hyF
  have hy := congrFun
    (hphiFixedPointFree.coe_eq_inv_of_involutive hphiInvolutive)
    (⟨y, hyF⟩ : F)
  simpa [phi, uN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
    congrArg Subtype.val hy

/-- The product of two involutions in the normalizer of the selected
centralizer belongs to that centralizer. -/
private theorem mul_mem_selected_centralizer_of_involutions_mem_normalizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u v : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (huI : IsInvolution u) (hvI : IsInvolution v)
    (huN : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hvN : v ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    u * v ∈ Subgroup.centralizer ({x} : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hxF : x ∈ F := by
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have huinv :=
    involution_in_normalizer_inverts_selected_centralizer
      h hxC hxne huI huN
  have hvinv :=
    involution_in_normalizer_inverts_selected_centralizer
      h hxC hxne hvI hvN
  have huinvx : u * x * u⁻¹ = x⁻¹ := huinv x hxF
  have hvinvx : v * x * v⁻¹ = x⁻¹ := hvinv x hxF
  have huinvxInv : u * x⁻¹ * u⁻¹ = x := by
    have hconj := congrArg (fun z : G => z⁻¹) huinvx
    simpa [mul_inv_rev, mul_assoc] using hconj
  have hprodConj : (u * v) * x * (u * v)⁻¹ = x := by
    calc
      (u * v) * x * (u * v)⁻¹ =
          u * (v * x * v⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hvinvx]
      _ = x := huinvxInv
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc
    (u * v) * x = ((u * v) * x * (u * v)⁻¹) * (u * v) := by group
    _ = x * (u * v) := by rw [hprodConj]

/-- Once `t` inverts both `x` and its centralizer, ordered involution pairs
with product `x` form a torsor for `C_G(x)`.  The forward map sends a pair
with first entry `u` to `tu`. -/
private noncomputable def bswPairFiberEquivCentralizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (htx : h.t * x * h.t⁻¹ = x⁻¹)
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    bswPairFiber G x ≃ Subgroup.centralizer ({x} : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have htt : h.t * h.t = 1 := by
    simpa [pow_two] using h.t_involution.2
  have htInvSelf : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right htt
  have htxInv : h.t * x⁻¹ * h.t⁻¹ = x := by
    have hconj := congrArg (fun z : G => z⁻¹) htx
    simpa [mul_inv_rev, mul_assoc] using hconj
  have htC : h.t ∈ bswKConjugates h :=
    ⟨h.t, h.t_mem_K, h.t_involution.1, 1, by simp⟩
  have htNotF : h.t ∉ F := by
    intro htF
    have htcommx : Commute h.t x := by
      change h.t * x = x * h.t
      exact Subgroup.mem_centralizer_singleton_iff.mp htF
    exact hxC
      (mem_bswKConjugates_of_commute_of_mem_bswKConjugates
        h htC hxne htcommx.symm)
  let toFun : bswPairFiber G x → F := fun p =>
    ⟨h.t * (p.1.1 : G), by
      have huinv :
          (p.1.1 : G) * x * (p.1.1 : G)⁻¹ = x⁻¹ :=
        bswPair_first_inverts_product p.1.1.2 p.1.2.2 p.2
      have hprodConj :
          (h.t * (p.1.1 : G)) * x *
              (h.t * (p.1.1 : G))⁻¹ = x := by
        calc
          (h.t * (p.1.1 : G)) * x *
                (h.t * (p.1.1 : G))⁻¹ =
              h.t * ((p.1.1 : G) * x * (p.1.1 : G)⁻¹) * h.t⁻¹ := by
                group
          _ = h.t * x⁻¹ * h.t⁻¹ := by rw [huinv]
          _ = x := htxInv
      dsimp [F]
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (h.t * (p.1.1 : G)) * x =
        x * (h.t * (p.1.1 : G))
      calc
        (h.t * (p.1.1 : G)) * x =
            ((h.t * (p.1.1 : G)) * x *
              (h.t * (p.1.1 : G))⁻¹) *
                (h.t * (p.1.1 : G)) := by group
        _ = x * (h.t * (p.1.1 : G)) := by rw [hprodConj]⟩
  let fromFun : F → bswPairFiber G x := fun f => by
    let u0 : G := h.t * (f : G)
    have hu0ne : u0 ≠ 1 := by
      intro hu0one
      apply htNotF
      have hf : (f : G) = h.t⁻¹ :=
        eq_inv_of_mul_eq_one_right hu0one
      rw [htInvSelf] at hf
      rw [← hf]
      exact f.property
    have hu0sq : u0 ^ 2 = 1 := by
      rw [pow_two]
      calc
        u0 * u0 =
            (h.t * (f : G) * h.t⁻¹) * (f : G) := by
              dsimp [u0]
              rw [htInvSelf]
              group
        _ = (f : G)⁻¹ * (f : G) := by rw [hFinv (f : G) f.property]
        _ = 1 := by simp
    have hu0I : IsInvolution u0 := ⟨hu0ne, hu0sq⟩
    have hu0u0 : u0 * u0 = 1 := by simpa [pow_two] using hu0sq
    have hu0InvSelf : u0⁻¹ = u0 := inv_eq_of_mul_eq_one_right hu0u0
    have hfcommx : Commute (f : G) x := by
      change (f : G) * x = x * (f : G)
      exact Subgroup.mem_centralizer_singleton_iff.mp f.property
    have hffix : (f : G) * x * (f : G)⁻¹ = x := by
      rw [hfcommx.eq]
      simp
    have hu0invx : u0 * x * u0⁻¹ = x⁻¹ := by
      calc
        u0 * x * u0⁻¹ =
            h.t * ((f : G) * x * (f : G)⁻¹) * h.t⁻¹ := by
              dsimp [u0]
              group
        _ = h.t * x * h.t⁻¹ := by rw [hffix]
        _ = x⁻¹ := htx
    let v0 : G := u0 * x
    have hv0sq : v0 ^ 2 = 1 := by
      rw [pow_two]
      calc
        v0 * v0 = (u0 * x * u0⁻¹) * x := by
          dsimp [v0]
          rw [hu0InvSelf]
          group
        _ = x⁻¹ * x := by rw [hu0invx]
        _ = 1 := by simp
    have hv0ne : v0 ≠ 1 := by
      intro hv0one
      have hxEq : x = u0⁻¹ := eq_inv_of_mul_eq_one_right hv0one
      rw [hu0InvSelf] at hxEq
      have hxI : IsInvolution x := by simpa [hxEq] using hu0I
      exact hxC (mem_bswKConjugates_of_isInvolution h hxI)
    have hv0I : IsInvolution v0 := ⟨hv0ne, hv0sq⟩
    refine ⟨(⟨u0, hu0I⟩, ⟨v0, hv0I⟩), ?_⟩
    change u0 * v0 = x
    dsimp [v0]
    calc
      u0 * (u0 * x) = (u0 * u0) * x := by group
      _ = x := by rw [hu0u0]; simp
  exact
    { toFun := toFun
      invFun := fromFun
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          change h.t * (h.t * (p.1.1 : G)) = (p.1.1 : G)
          rw [← mul_assoc, htt, one_mul]
        · apply Subtype.ext
          change (h.t * (h.t * (p.1.1 : G))) * x = (p.1.2 : G)
          rw [← mul_assoc, htt, one_mul]
          have huu : (p.1.1 : G) * (p.1.1 : G) = 1 := by
            simpa [pow_two] using p.1.1.2.2
          calc
            (p.1.1 : G) * x =
                (p.1.1 : G) *
                  ((p.1.1 : G) * (p.1.2 : G)) := by rw [p.2]
            _ = ((p.1.1 : G) * (p.1.1 : G)) * (p.1.2 : G) := by group
            _ = (p.1.2 : G) := by rw [huu]; simp
      right_inv := by
        intro f
        apply Subtype.ext
        change h.t * (h.t * (f : G)) = (f : G)
        rw [← mul_assoc, htt, one_mul] }

/-- For the selected element of Bender 3.1, the pair count is exactly the
order of its centralizer. -/
private theorem bswPairCount_eq_card_centralizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (htx : h.t * x * h.t⁻¹ = x⁻¹)
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    bswPairCount G x = Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  exact Nat.card_congr
    (bswPairFiberEquivCentralizer h hxC hxne htx hFinv)

/-- After conjugating the first involution in a selected pair to `t`, the
high-count element may be chosen to be inverted by `t`, as in Bender's line
237. -/
private theorem exists_bswPairCount_order_bound_inverted_by_t
    {G : Type u} [Group G] [Fintype G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K)
    (horder :
      let k := Nat.card h.K
      Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
        Nat.card G = (2 * k - 1) * (k - 1) * (2 * k)) :
    ∃ x : G,
      x ∉ bswKConjugates h ∧ x ≠ 1 ∧
        h.t * x * h.t⁻¹ = x⁻¹ ∧
        ((h.H.index =
              (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
            Nat.card h.K + 3 ≤ bswPairCount G x) ∨
          (h.H.index =
              (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
            Nat.card h.K - 2 ≤ bswPairCount G x)) := by
  obtain ⟨x, hxC, hxne, hbound⟩ :=
    exists_bswPairCount_order_bound h hk horder
  have hcountpos : 0 < bswPairCount G x := by
    rcases hbound with hplus | hminus
    · omega
    · omega
  have hfiberPos : 0 < Nat.card (bswPairFiber G x) := by
    simpa [bswPairCount] using hcountpos
  obtain ⟨p⟩ := (Nat.card_pos_iff.mp hfiberPos).1
  obtain ⟨g, hgu⟩ := h.involutions_conjugate (p.1.1 : G) p.1.1.2
  let y : G := g * x * g⁻¹
  have hyC : y ∉ bswKConjugates h := by
    intro hy
    exact hxC ((mem_bswKConjugates_conj_iff h g x).mp hy)
  have hyne : y ≠ 1 := by
    intro hy
    apply hxne
    have hconj := congrArg (fun z : G => g⁻¹ * z * g) hy
    simpa [y, mul_assoc] using hconj
  have huinv :
      (p.1.1 : G) * x * (p.1.1 : G)⁻¹ = x⁻¹ :=
    bswPair_first_inverts_product p.1.1.2 p.1.2.2 p.2
  have hyt : h.t * y * h.t⁻¹ = y⁻¹ := by
    have hc := congrArg (fun z : G => g * z * g⁻¹) huinv
    rw [← hgu]
    simpa [y, mul_inv_rev, mul_assoc] using hc
  have hycount : bswPairCount G y = bswPairCount G x := by
    dsimp [y]
    exact bswPairCount_conj g x
  refine ⟨y, hyC, hyne, hyt, ?_⟩
  rcases hbound with hplus | hminus
  · exact Or.inl ⟨hplus.1, by simpa [hycount] using hplus.2⟩
  · exact Or.inr ⟨hminus.1, by simpa [hycount] using hminus.2⟩

/-- The selected element and its centralizer satisfy Bender 3.1(i) and (iv).
The minus-branch bound improves from `k - 2` to `k - 1` because `|K|` is
even while the fixed-point-free centralizer has odd order. -/
private theorem exists_selected_centralizer_order_bound
    {G : Type u} [Group G] [Fintype G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K)
    (horder :
      let k := Nat.card h.K
      Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
        Nat.card G = (2 * k - 1) * (k - 1) * (2 * k)) :
    ∃ x : G, ∃ F : Subgroup G,
      F = Subgroup.centralizer ({x} : Set G) ∧
      x ∉ bswKConjugates h ∧ x ≠ 1 ∧
      h.t * x * h.t⁻¹ = x⁻¹ ∧
      IsMulCommutative F ∧ Odd (Nat.card F) ∧
      (∀ y : G, y ∈ F → h.t * y * h.t⁻¹ = y⁻¹) ∧
      (∀ a : G, a ∈ F → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = F) ∧
      ((h.H.index =
            (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
          Nat.card h.K + 3 ≤ Nat.card F) ∨
        (h.H.index =
            (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
          Nat.card h.K - 1 ≤ Nat.card F)) := by
  obtain ⟨x, hxC, hxne, htx, hbound⟩ :=
    exists_bswPairCount_order_bound_inverted_by_t h hk horder
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  obtain ⟨hFcomm, hFodd, hFCent⟩ :=
    selected_centralizer_structure h hxC hxne htx
  have hFinv : ∀ y : G, y ∈ F → h.t * y * h.t⁻¹ = y⁻¹ := by
    intro y hyF
    by_cases hyone : y = 1
    · subst y
      simp
    · exact (hFCent y hyF hyone).2
  have hcount : bswPairCount G x = Nat.card F :=
    bswPairCount_eq_card_centralizer h hxC hxne htx hFinv
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  have htKne : tK ≠ 1 := by
    intro htKone
    exact h.t_involution.1 (congrArg Subtype.val htKone)
  have htKsq : tK ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htKorder : orderOf tK = 2 :=
    orderOf_eq_prime htKsq htKne
  have hKeven : Even (Nat.card h.K) := by
    rw [even_iff_two_dvd, ← htKorder]
    exact orderOf_dvd_natCard tK
  refine ⟨x, F, rfl, hxC, hxne, htx, hFcomm, hFodd, hFinv, ?_, ?_⟩
  · intro a haF hane
    exact (hFCent a haF hane).1
  · rcases hbound with hplus | hminus
    · left
      refine ⟨hplus.1, ?_⟩
      rw [← hcount]
      exact hplus.2
    · right
      refine ⟨hminus.1, ?_⟩
      have hlower : Nat.card h.K - 2 ≤ Nat.card F := by
        rw [← hcount]
        exact hminus.2
      rcases hKeven with ⟨m, hm⟩
      rcases hFodd with ⟨n, hn⟩
      rw [hm, hn] at hlower ⊢
      omega

/-- Bender 3.1(ii): if `F = C_G(x)` is the selected centralizer and
`M = N_G(F)`, then `M` is generated by `F` and `K ∩ M`. -/
private theorem selected_centralizer_normalizer_eq_sup_inf_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    M = F ⊔ (h.K ⊓ M) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have hFleM : F ≤ M := by
    exact Subgroup.le_normalizer
  have htM : h.t ∈ M := by
    exact mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have htt : h.t * h.t = 1 := by
    simpa [pow_two] using h.t_involution.2
  have htInvSelf : h.t⁻¹ = h.t := inv_eq_of_mul_eq_one_right htt
  apply le_antisymm
  · intro m hmM
    let v : G := m * h.t * m⁻¹
    have hvI : IsInvolution v := by
      constructor
      · intro hvone
        apply h.t_involution.1
        have hc := congrArg (fun z : G => m⁻¹ * z * m) hvone
        simpa [v, mul_assoc] using hc
      · calc
          v ^ 2 = m * (h.t ^ 2) * m⁻¹ := by
            dsimp [v]
            simp [pow_two, mul_assoc]
          _ = 1 := by rw [h.t_involution.2]; simp
    have hvM : v ∈ M := by
      exact M.mul_mem (M.mul_mem hmM htM) (M.inv_mem hmM)
    have htvF : h.t * v ∈ F := by
      exact mul_mem_selected_centralizer_of_involutions_mem_normalizer
        h hxC hxne h.t_involution hvI htM hvM
    have htvOdd : Odd (orderOf (h.t * v)) :=
      Odd.of_dvd_nat hFodd (Subgroup.orderOf_dvd_natCard F htvF)
    obtain ⟨g, hgZ, hgconj⟩ :=
      BenderSuzuki.PFchapter1section1.exists_zpowers_conjugator_of_odd_product
        h.t_involution hvI htvOdd
    have hgF : g ∈ F :=
      (Subgroup.zpowers_le.mpr htvF) hgZ
    have hgconj' : g⁻¹ * h.t * g = v := by
      simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using hgconj
    let q : G := g * m
    have hqM : q ∈ M := M.mul_mem (hFleM hgF) hmM
    have hqH : q ∈ h.H := by
      rw [h.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
      have hqconj : q⁻¹ * h.t * q = h.t := by
        calc
          q⁻¹ * h.t * q = m⁻¹ * (g⁻¹ * h.t * g) * m := by
            dsimp [q]
            group
          _ = m⁻¹ * v * m := by rw [hgconj']
          _ = h.t := by
            dsimp [v]
            group
      have hmul := congrArg (fun z : G => q * z) hqconj
      have htq : h.t * q = q * h.t := by
        simpa [mul_assoc] using hmul
      exact htq.symm
    let S : Subgroup G := F ⊔ (h.K ⊓ M)
    by_cases hqK : q ∈ h.K
    · have hgInvS : g⁻¹ ∈ S :=
        Subgroup.mem_sup_left (F.inv_mem hgF)
      have hqS : q ∈ S :=
        Subgroup.mem_sup_right ⟨hqK, hqM⟩
      have hmq : m = g⁻¹ * q := by
        dsimp [q]
        group
      rw [hmq]
      exact S.mul_mem hgInvS hqS
    · have hqI : IsInvolution q :=
        h.isInvolution_of_mem_H_not_mem_K hqH hqK
      have htqF : h.t * q ∈ F :=
        mul_mem_selected_centralizer_of_involutions_mem_normalizer
          h hxC hxne h.t_involution hqI htM hqM
      let r : G := h.t * q
      have hrF : r ∈ F := htqF
      have htr : h.t * r = r⁻¹ * h.t := by
        calc
          h.t * r = (h.t * r * h.t⁻¹) * h.t := by
            rw [htInvSelf]
            simp [mul_assoc, htt]
          _ = r⁻¹ * h.t := by rw [hFinv r hrF]
      have hfS : g⁻¹ * r⁻¹ ∈ S :=
        Subgroup.mem_sup_left
          (F.mul_mem (F.inv_mem hgF) (F.inv_mem hrF))
      have htS : h.t ∈ S :=
        Subgroup.mem_sup_right ⟨h.t_mem_K, htM⟩
      have httr : h.t * r = q := by
        dsimp [r]
        calc
          h.t * (h.t * q) = (h.t * h.t) * q := by group
          _ = q := by rw [htt]; simp
      have hmdecomp : m = (g⁻¹ * r⁻¹) * h.t := by
        calc
          m = g⁻¹ * q := by
            dsimp [q]
            group
          _ = g⁻¹ * (h.t * r) := by rw [httr]
          _ = (g⁻¹ * r⁻¹) * h.t := by rw [htr]; group
      rw [hmdecomp]
      exact S.mul_mem hfS htS
  · exact sup_le hFleM inf_le_right

/-- Bender 3.1(iii), first in its reusable relative-TI form: a nontrivial
centralizer whose nonidentity elements all have that same centralizer is a TI
subset relative to its normalizer. -/
private theorem selected_centralizer_isTISubsetRelative
    {G : Type u} [Group G] [Finite G] {x : G}
    (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFCent : ∀ a : G,
      a ∈ Subgroup.centralizer ({x} : Set G) → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) =
          Subgroup.centralizer ({x} : Set G)) :
    Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have hxF : x ∈ F := by
    change x ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hFleM : F ≤ M := Subgroup.le_normalizer
  have hFnontrivial : ∃ a : G, a ∈ (F : Set G) ∧ a ≠ 1 :=
    ⟨x, hxF, hxne⟩
  apply
    (Suzuki.VI.suzuki_ch6_proposition_2_8
      M (F : Set G) hFleM le_rfl hFnontrivial).2
  intro g hgM z hz
  rcases hz.1 with ⟨a, haF, haz⟩
  have hzF : z ∈ F := hz.2
  by_cases hz1 : z = 1
  · simp [hz1]
  · have hconj_le : F.conjBy g ≤
        Subgroup.centralizer ({z} : Set G) := by
      intro y hy
      rw [Subgroup.conjBy, Subgroup.mem_map] at hy
      rcases hy with ⟨y₀, hy₀F, hy₀y⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      rw [← haz, ← hy₀y]
      have hcomm : y₀ * a = a * y₀ := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm
            (M := Subgroup.centralizer ({x} : Set G))).comm
              ⟨y₀, hy₀F⟩ ⟨a, haF⟩)
      calc
        (g * y₀ * g⁻¹) * (g * a * g⁻¹) =
            g * (y₀ * a) * g⁻¹ := by group
        _ = g * (a * y₀) * g⁻¹ := by rw [hcomm]
        _ = (g * a * g⁻¹) * (g * y₀ * g⁻¹) := by group
    have hconj_le_F : F.conjBy g ≤ F := by
      intro y hy
      have hyCentral := hconj_le hy
      rw [hFCent z hzF hz1] at hyCentral
      exact hyCentral
    have hcardConj : Nat.card (F.conjBy g) = Nat.card F := by
      simpa [Subgroup.conjBy] using
        (Subgroup.card_map_of_injective
          (K := F) (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective)
    have hconjEq : F.conjBy g = F :=
      Subgroup.eq_of_le_of_card_ge hconj_le_F
        (le_of_eq hcardConj.symm)
    have hgNorm : g ∈ M := by
      change g ∈ Subgroup.normalizer (F : Set G)
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      simpa [Subgroup.conjBy] using hconjEq
    exact (hgM hgNorm).elim

/-- The omitted Hall step in Bender 3.1(iii): if every nonidentity element of
a nontrivial centralizer has that same centralizer, its order is coprime to
its ambient index. -/
private theorem selected_centralizer_isHall
    {G : Type u} [Group G] [Finite G] {x : G}
    (hFCent : ∀ a : G,
      a ∈ Subgroup.centralizer ({x} : Set G) → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) =
          Subgroup.centralizer ({x} : Set G)) :
    Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  by_contra hcop
  rcases Nat.Prime.not_coprime_iff_dvd.mp hcop with
    ⟨p, hp, hpF, hpIndex⟩
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let P : Sylow p F := default
  let PG : Subgroup G := (P : Subgroup F).map F.subtype
  have hPGp : IsPGroup p PG := P.isPGroup'.map F.subtype
  have hpPGIndex : p ∣ PG.index := by
    change p ∣ ((P : Subgroup F).map F.subtype).index
    rw [Subgroup.index_map_subtype]
    exact dvd_mul_of_dvd_right hpIndex _
  obtain ⟨Q, hPGQ⟩ := IsPGroup.exists_le_sylow hPGp
  have hPGneQ : PG ≠ (Q : Subgroup G) := by
    intro hEq
    apply Q.not_dvd_index
    rwa [← hEq]
  have hPGltQ : PG < (Q : Subgroup G) :=
    lt_of_le_of_ne hPGQ hPGneQ
  obtain ⟨Y, hPGY, _hYQ, hYNorm, hYp⟩ :=
    section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
      Q.isPGroup' hPGltQ
  have hPne : (P : Subgroup F) ≠ ⊥ := by
    intro hPbot
    apply P.not_dvd_index
    simpa [hPbot, Subgroup.index_bot] using hpF
  have hPGne : PG ≠ ⊥ := by
    intro hPGbot
    apply hPne
    exact
      (Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup F)) F.subtype_injective).mp
        hPGbot
  let PY : Subgroup Y := PG.subgroupOf Y
  have hPYnormal : PY.Normal := by
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer hPGY.le).mpr
        hYNorm
  let : PY.Normal := hPYnormal
  have hPYne : PY ≠ ⊥ := by
    intro hPYbot
    exact hPGne
      ((Subgroup.subgroupOf_eq_bot.mp hPYbot).eq_bot_of_le hPGY.le)
  let : Fact (IsPGroup p Y) := ⟨hYp⟩
  obtain ⟨a, haPY, haCenter, hane, _hap⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := Y) (p := p) PY hPYne
  have haPG : (a : G) ∈ PG := haPY
  have hPGleF : PG ≤ F := Subgroup.map_subtype_le (P : Subgroup F)
  have haF : (a : G) ∈ F := hPGleF haPG
  have haneG : (a : G) ≠ 1 := by
    intro haone
    exact hane (Subtype.ext haone)
  have hYleF : Y ≤ F := by
    intro y hyY
    have hcommY :=
      (Subgroup.mem_center_iff.mp haCenter) ⟨y, hyY⟩
    have hcommG : Commute y (a : G) := by
      change y * (a : G) = (a : G) * y
      simpa using congrArg Subtype.val hcommY
    have hyCentral : y ∈
        Subgroup.centralizer ({(a : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hcommG
    rw [hFCent (a : G) haF haneG] at hyCentral
    exact hyCentral
  let YF : Subgroup F := Y.subgroupOf F
  have hYFp : IsPGroup p YF :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYleF).symm
  have hPleYF : (P : Subgroup F) ≤ YF := by
    intro aF haP
    change (aF : G) ∈ Y
    exact hPGY.le (Subgroup.mem_map_of_mem F.subtype haP)
  have hYFeqP : YF = (P : Subgroup F) :=
    P.is_maximal' hYFp hPleYF
  apply hPGY.not_ge
  intro y hyY
  have hyF : y ∈ F := hYleF hyY
  let yF : F := ⟨y, hyF⟩
  have hyYF : yF ∈ YF := hyY
  have hyP : yF ∈ (P : Subgroup F) := by
    rw [← hYFeqP]
    exact hyYF
  exact Subgroup.mem_map_of_mem F.subtype hyP

/-- Bender 3.1(iii) in the form used by the coset count: outside the
normalizer of the selected centralizer, that centralizer meets the conjugate
normalizer trivially. -/
private theorem selected_centralizer_disjoint_conj_normalizer
    {G : Type u} [Group G] [Finite G] {x : G}
    (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (g : G)
    (hgM : g ∉ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    Disjoint
      (Subgroup.centralizer ({x} : Set G))
      ((Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G)).conjBy g) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let Fg : Subgroup G := F.conjBy g
  let Mg : Subgroup G := M.conjBy g
  have hMgEq : Mg = Subgroup.normalizer (Fg : Set G) := by
    dsimp [Mg, M, Fg]
    simpa [Subgroup.conjBy] using
      (Subgroup.map_equiv_normalizer_eq F (MulAut.conj g))
  have hFgLeMg : Fg ≤ Mg := by
    rw [hMgEq]
    exact Subgroup.le_normalizer
  have hFgIndex : Fg.index = F.index := by
    dsimp [Fg]
    change (F.map (MulAut.conj g).toMonoidHom).index = F.index
    exact Subgroup.index_map_equiv (H := F) (MulAut.conj g)
  rw [Subgroup.disjoint_def]
  intro z hzF hzMg
  by_cases hz1 : z = 1
  · exact hz1
  · let N : Subgroup Mg := Fg.subgroupOf Mg
    have hNnormal : N.Normal := by
      exact
        (Subgroup.normal_subgroupOf_iff_le_normalizer hFgLeMg).mpr
          (le_of_eq hMgEq)
    let : N.Normal := hNnormal
    let zMg : Mg := ⟨z, hzMg⟩
    let q : Mg →* (Mg ⧸ N) := QuotientGroup.mk' N
    have horderF : orderOf (q zMg) ∣ Nat.card F := by
      apply (orderOf_map_dvd q zMg).trans
      simpa [zMg] using Subgroup.orderOf_dvd_natCard F hzF
    have horderQuotient :
        orderOf (q zMg) ∣ Nat.card (Mg ⧸ N) :=
      orderOf_dvd_natCard (q zMg)
    have hNindexDvd : N.index ∣ F.index := by
      have hrelDvd : Fg.relIndex Mg ∣ Fg.index :=
        Subgroup.relIndex_dvd_index_of_le hFgLeMg
      rw [hFgIndex] at hrelDvd
      change (Fg.subgroupOf Mg).index ∣ F.index at hrelDvd
      change (Fg.subgroupOf Mg).index ∣ F.index
      exact hrelDvd
    have horderIndex : orderOf (q zMg) ∣ F.index := by
      have horderNindex : orderOf (q zMg) ∣ N.index := by
        simpa [Subgroup.index_eq_card] using horderQuotient
      exact horderNindex.trans hNindexDvd
    have horderOne : orderOf (q zMg) = 1 :=
      Nat.eq_one_of_dvd_coprimes hFHall horderF horderIndex
    have hqOne : q zMg = 1 := orderOf_eq_one_iff.mp horderOne
    have hzN : zMg ∈ N := by
      apply (QuotientGroup.eq_one_iff zMg).mp
      simpa [q] using hqOne
    have hzFg : z ∈ Fg := hzN
    have hzImage : z ∈
        (fun y : G => g * y * g⁻¹) '' (F : Set G) := by
      change z ∈ F.conjBy g at hzFg
      rw [Subgroup.conjBy, Subgroup.mem_map] at hzFg
      rcases hzFg with ⟨y, hyF, hyz⟩
      refine ⟨y, hyF, ?_⟩
      simpa [MulAut.conj_apply] using hyz
    have hxF : x ∈ F := by
      change x ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hFnontrivial : ∃ a : G, a ∈ (F : Set G) ∧ a ≠ 1 :=
      ⟨x, hxF, hxne⟩
    have hintersection :=
      (Suzuki.VI.suzuki_ch6_proposition_2_8
        M (F : Set G) Subgroup.le_normalizer le_rfl hFnontrivial).1
        hFTI g hgM
    have hzSingleton := hintersection ⟨hzImage, hzF⟩
    simpa using hzSingleton

/-- The selected centralizer meets the distinguished involution centralizer
trivially.  This is the local form of `F ∩ H^G = 1` used throughout the
coset count. -/
private theorem selected_centralizer_disjoint_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1) :
    Disjoint (Subgroup.centralizer ({x} : Set G)) h.H := by
  rw [Subgroup.disjoint_def]
  intro a haF haH
  by_cases ha1 : a = 1
  · exact ha1
  have haC : a ∈ bswKConjugates h :=
    mem_bswKConjugates_of_mem_H_of_ne_one h haH ha1
  have hax : Commute a x :=
    Subgroup.mem_centralizer_singleton_iff.mp haF
  exact False.elim <| hxC <|
    mem_bswKConjugates_of_commute_of_mem_bswKConjugates
      h haC hxne hax.symm

/-- The selected normalizer has order `|F| |K ∩ M|`. -/
private theorem selected_centralizer_normalizer_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card M = Nat.card F * Nat.card (h.K ⊓ M : Subgroup G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  have hMdecomp : M = F ⊔ A :=
    selected_centralizer_normalizer_eq_sup_inf_K
      h hxC hxne hFodd hFinv
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hAleH : A ≤ h.H := inf_le_left.trans hKleH
  have hFA : Disjoint F A :=
    (selected_centralizer_disjoint_H h hxC hxne).mono_right hAleH
  have hAnorm : A ≤ Subgroup.normalizer (F : Set G) := inf_le_right
  let toM : F × A → M := fun z =>
    ⟨(z.1 : G) * (z.2 : G), by
      rw [hMdecomp]
      exact Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have htoInjective : Function.Injective toM := by
    intro a b hab
    apply Subgroup.mul_injective_of_disjoint hFA
    exact congrArg Subtype.val hab
  have htoSurjective : Function.Surjective toM := by
    intro m
    have hmProd : (m : G) ∈ (F : Set G) * (A : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left F A hAnorm,
        ← hMdecomp]
      exact m.property
    rcases hmProd with ⟨f, hfF, a, haA, hfa⟩
    exact ⟨(⟨f, hfF⟩, ⟨a, haA⟩), Subtype.ext hfa⟩
  calc
    Nat.card M = Nat.card (F × A) :=
      Nat.card_congr (Equiv.ofBijective toM ⟨htoInjective, htoSurjective⟩).symm
    _ = Nat.card F * Nat.card A := Nat.card_prod F A

/-- Multiplication by the distinguished involution identifies the selected
centralizer with the involutions in its normalizer. -/
private noncomputable def selected_centralizer_equiv_involutions_normalizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    F ≃ {u : G // u ∈ M ∧ IsInvolution u} := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have hFleM : F ≤ M := Subgroup.le_normalizer
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have hFH : Disjoint F h.H :=
    selected_centralizer_disjoint_H h hxC hxne
  have htF : h.t ∉ F := by
    intro htF
    exact h.t_involution.1
      (Subgroup.disjoint_def.mp hFH htF (by
        rw [h.H_eq_centralizer]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Commute.refl h.t)))
  have htt : h.t * h.t = 1 := by
    simpa [pow_two] using h.t_involution.2
  have htInvSelf : h.t⁻¹ = h.t :=
    inv_eq_of_mul_eq_one_right htt
  let e : F → {u : G // u ∈ M ∧ IsInvolution u} := fun a =>
    ⟨h.t * (a : G),
      ⟨M.mul_mem htM (hFleM a.property), by
        constructor
        · intro hta
          apply htF
          have htEq : h.t = (a : G)⁻¹ :=
            eq_inv_of_mul_eq_one_left hta
          rw [htEq]
          exact F.inv_mem a.property
        · rw [pow_two]
          calc
            (h.t * (a : G)) * (h.t * (a : G)) =
                (h.t * (a : G) * h.t⁻¹) * (a : G) := by
              rw [htInvSelf]
              group
            _ = (a : G)⁻¹ * (a : G) := by
              rw [hFinv (a : G) a.property]
            _ = 1 := inv_mul_cancel _⟩⟩
  refine Equiv.ofBijective e ⟨?_, ?_⟩
  · intro a b hab
    apply Subtype.ext
    have habG := congrArg Subtype.val hab
    change h.t * (a : G) = h.t * (b : G) at habG
    exact mul_left_cancel habG
  · intro u
    have htuF : h.t * (u : G) ∈ F :=
      mul_mem_selected_centralizer_of_involutions_mem_normalizer
        h hxC hxne h.t_involution u.property.2 htM u.property.1
    refine ⟨⟨h.t * (u : G), htuF⟩, ?_⟩
    apply Subtype.ext
    change h.t * (h.t * (u : G)) = (u : G)
    rw [← mul_assoc, htt, one_mul]

/-- The selected normalizer contains exactly `|F|` involutions. -/
private theorem selected_centralizer_involutions_normalizer_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card {u : G // u ∈ M ∧ IsInvolution u} = Nat.card F := by
  exact Nat.card_congr
    (selected_centralizer_equiv_involutions_normalizer
      h hxC hxne hFinv).symm

/-- Every involution in the selected normalizer is conjugate to `t` by an
element of the selected centralizer. -/
private theorem selected_centralizer_involutions_conjugate_by_centralizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    ∃ g : G, g ∈ Subgroup.centralizer ({x} : Set G) ∧
      g⁻¹ * h.t * g = u := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have htuF : h.t * u ∈ F :=
    mul_mem_selected_centralizer_of_involutions_mem_normalizer
      h hxC hxne h.t_involution huI htM huM
  have htuOdd : Odd (orderOf (h.t * u)) :=
    Odd.of_dvd_nat hFodd (Subgroup.orderOf_dvd_natCard F htuF)
  obtain ⟨g, hgZ, hgconj⟩ :=
    BenderSuzuki.PFchapter1section1.exists_zpowers_conjugator_of_odd_product
      h.t_involution huI htuOdd
  have hgF : g ∈ F := (Subgroup.zpowers_le.mpr htuF) hgZ
  refine ⟨g, hgF, ?_⟩
  simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using hgconj

/-- Any two involutions in the selected normalizer are conjugate by an
element of the selected centralizer. -/
private theorem selected_centralizer_involutions_conjugate
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x a b : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (haM : a ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (haI : IsInvolution a)
    (hbM : b ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hbI : IsInvolution b) :
    ∃ g : G, g ∈ Subgroup.centralizer ({x} : Set G) ∧
      g⁻¹ * a * g = b := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  obtain ⟨ga, hgaF, hga⟩ :=
    selected_centralizer_involutions_conjugate_by_centralizer
      h hxC hxne hFodd hFinv haM haI
  obtain ⟨gb, hgbF, hgb⟩ :=
    selected_centralizer_involutions_conjugate_by_centralizer
      h hxC hxne hFodd hFinv hbM hbI
  refine ⟨ga⁻¹ * gb, F.mul_mem (F.inv_mem hgaF) hgbF, ?_⟩
  calc
    (ga⁻¹ * gb)⁻¹ * a * (ga⁻¹ * gb) =
        gb⁻¹ * (ga * a * ga⁻¹) * gb := by group
    _ = gb⁻¹ * h.t * gb := by
      have hga' : ga * a * ga⁻¹ = h.t := by
        calc
          ga * a * ga⁻¹ = ga * (ga⁻¹ * h.t * ga) * ga⁻¹ := by
            rw [← hga]
          _ = h.t := by group
      rw [hga']
    _ = b := hgb

/-- Inside the selected normalizer, the centralizer of `t` is exactly
`K ∩ M`. -/
private theorem selected_centralizer_inf_centralizer_t_eq_inf_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    M ⊓ Subgroup.centralizer ({h.t} : Set G) = h.K ⊓ M := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have htH : h.t ∈ h.H := hKleH h.t_mem_K
  have hFH : Disjoint F h.H :=
    selected_centralizer_disjoint_H h hxC hxne
  have htt : h.t * h.t = 1 := by
    simpa [pow_two] using h.t_involution.2
  have htInvSelf : h.t⁻¹ = h.t :=
    inv_eq_of_mul_eq_one_right htt
  ext z
  constructor
  · rintro ⟨hzM, hzC⟩
    have hzH : z ∈ h.H := by
      rw [h.H_eq_centralizer]
      exact hzC
    refine ⟨?_, hzM⟩
    by_contra hzK
    have hzI : IsInvolution z :=
      h.isInvolution_of_mem_H_not_mem_K hzH hzK
    have htzF : h.t * z ∈ F :=
      mul_mem_selected_centralizer_of_involutions_mem_normalizer
        h hxC hxne h.t_involution hzI htM hzM
    have htzH : h.t * z ∈ h.H := h.H.mul_mem htH hzH
    have htz1 : h.t * z = 1 :=
      Subgroup.disjoint_def.mp hFH htzF htzH
    have hzt : z = h.t := by
      calc
        z = h.t⁻¹ := eq_inv_of_mul_eq_one_right htz1
        _ = h.t := htInvSelf
    exact hzK (hzt ▸ h.t_mem_K)
  · rintro ⟨hzK, hzM⟩
    refine ⟨hzM, ?_⟩
    rw [← h.H_eq_centralizer]
    exact hKleH hzK

/-- Conjugation inside `M` transports its internal centralizers. -/
private def infCentralizerEquivOfRightConjugateElemEq
    {G : Type u} [Group G] (M : Subgroup G) {a b g : G}
    (hgM : g ∈ M)
    (hab : BenderSuzuki.PFAppendixIII.rightConjugateElem a g = b) :
    (M ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) ≃
      (M ⊓ Subgroup.centralizer ({b} : Set G) : Subgroup G) := by
  let Ca : Subgroup G := M ⊓ Subgroup.centralizer ({a} : Set G)
  let Cb : Subgroup G := M ⊓ Subgroup.centralizer ({b} : Set G)
  have hba :
      BenderSuzuki.PFAppendixIII.rightConjugateElem b g⁻¹ = a := by
    rw [← hab,
      BenderSuzuki.PFchapter1section1.rightConjugateElem_comp]
    simp [BenderSuzuki.PFAppendixIII.rightConjugateElem]
  have hforward {z : G} (hzM : z ∈ M)
      (hza : z ∈ Subgroup.centralizer ({a} : Set G)) :
      BenderSuzuki.PFAppendixIII.rightConjugateElem z g ∈ Cb := by
    refine ⟨?_, ?_⟩
    · simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using
        M.mul_mem (M.mul_mem (M.inv_mem hgM) hzM) hgM
    · change BenderSuzuki.PFAppendixIII.rightConjugateElem z g ∈
        Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hab]
      have hcomm : z * a = a * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hza
      calc
        BenderSuzuki.PFAppendixIII.rightConjugateElem z g *
              BenderSuzuki.PFAppendixIII.rightConjugateElem a g =
            BenderSuzuki.PFAppendixIII.rightConjugateElem (z * a) g := by
          simp [BenderSuzuki.PFAppendixIII.rightConjugateElem, mul_assoc]
        _ = BenderSuzuki.PFAppendixIII.rightConjugateElem (a * z) g := by
          rw [hcomm]
        _ = BenderSuzuki.PFAppendixIII.rightConjugateElem a g *
              BenderSuzuki.PFAppendixIII.rightConjugateElem z g := by
          simp [BenderSuzuki.PFAppendixIII.rightConjugateElem, mul_assoc]
  have hbackward {z : G} (hzM : z ∈ M)
      (hzb : z ∈ Subgroup.centralizer ({b} : Set G)) :
      BenderSuzuki.PFAppendixIII.rightConjugateElem z g⁻¹ ∈ Ca := by
    refine ⟨?_, ?_⟩
    · simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using
        M.mul_mem (M.mul_mem hgM hzM) (M.inv_mem hgM)
    · change BenderSuzuki.PFAppendixIII.rightConjugateElem z g⁻¹ ∈
        Subgroup.centralizer ({a} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff, ← hba]
      have hcomm : z * b = b * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hzb
      calc
        BenderSuzuki.PFAppendixIII.rightConjugateElem z g⁻¹ *
              BenderSuzuki.PFAppendixIII.rightConjugateElem b g⁻¹ =
            BenderSuzuki.PFAppendixIII.rightConjugateElem (z * b) g⁻¹ := by
          simp [BenderSuzuki.PFAppendixIII.rightConjugateElem, mul_assoc]
        _ = BenderSuzuki.PFAppendixIII.rightConjugateElem (b * z) g⁻¹ := by
          rw [hcomm]
        _ = BenderSuzuki.PFAppendixIII.rightConjugateElem b g⁻¹ *
              BenderSuzuki.PFAppendixIII.rightConjugateElem z g⁻¹ := by
          simp [BenderSuzuki.PFAppendixIII.rightConjugateElem, mul_assoc]
  let forward : Ca → Cb := fun z =>
    ⟨BenderSuzuki.PFAppendixIII.rightConjugateElem (z : G) g,
      hforward z.property.1 z.property.2⟩
  let backward : Cb → Ca := fun z =>
    ⟨BenderSuzuki.PFAppendixIII.rightConjugateElem (z : G) g⁻¹,
      hbackward z.property.1 z.property.2⟩
  exact
    { toFun := forward
      invFun := backward
      left_inv := by
        intro z
        apply Subtype.ext
        change BenderSuzuki.PFAppendixIII.rightConjugateElem
            (BenderSuzuki.PFAppendixIII.rightConjugateElem (z : G) g) g⁻¹ =
          (z : G)
        rw [BenderSuzuki.PFchapter1section1.rightConjugateElem_comp]
        simp [BenderSuzuki.PFAppendixIII.rightConjugateElem]
      right_inv := by
        intro z
        apply Subtype.ext
        change BenderSuzuki.PFAppendixIII.rightConjugateElem
            (BenderSuzuki.PFAppendixIII.rightConjugateElem (z : G) g⁻¹) g =
          (z : G)
        rw [BenderSuzuki.PFchapter1section1.rightConjugateElem_comp]
        simp [BenderSuzuki.PFAppendixIII.rightConjugateElem] }

/-- Every involution of the selected normalizer has internal centralizer of
order `|K ∩ M|`. -/
private theorem selected_centralizer_inf_centralizer_involution_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card (M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
      Nat.card (h.K ⊓ M : Subgroup G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  obtain ⟨g, hgF, htu⟩ :=
    selected_centralizer_involutions_conjugate_by_centralizer
      h hxC hxne hFodd hFinv huM huI
  have hgM : g ∈ M := Subgroup.le_normalizer hgF
  calc
    Nat.card (M ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) =
        Nat.card (M ⊓ Subgroup.centralizer ({h.t} : Set G) : Subgroup G) :=
      (Nat.card_congr
        (infCentralizerEquivOfRightConjugateElemEq M hgM (by
          simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using htu))).symm
    _ = Nat.card (h.K ⊓ M : Subgroup G) := by
      rw [selected_centralizer_inf_centralizer_t_eq_inf_K
        h hxC hxne hFinv]

/-- All involution centralizers have the order of the distinguished
centralizer `H`. -/
private theorem centralizer_involution_card_eq_card_H
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {u : G}
    (huI : IsInvolution u) :
    Nat.card (Subgroup.centralizer ({u} : Set G)) = Nat.card h.H := by
  obtain ⟨g, hgu⟩ := h.involutions_conjugate u huI
  have hright :
      BenderSuzuki.PFAppendixIII.rightConjugateElem u g⁻¹ = h.t := by
    simpa [BenderSuzuki.PFAppendixIII.rightConjugateElem] using hgu
  have he := infCentralizerEquivOfRightConjugateElemEq
    (⊤ : Subgroup G) (by simp : g⁻¹ ∈ (⊤ : Subgroup G)) hright
  calc
    Nat.card (Subgroup.centralizer ({u} : Set G)) =
        Nat.card ((⊤ : Subgroup G) ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G) := by simp
    _ = Nat.card ((⊤ : Subgroup G) ⊓
        Subgroup.centralizer ({h.t} : Set G) : Subgroup G) :=
      Nat.card_congr he
    _ = Nat.card h.H := by simpa [h.H_eq_centralizer]

/-- Conjugating an involution to `t` identifies the involutions in its
centralizer with the involutions in `H = C_G(t)`. -/
private noncomputable def centralizer_involutions_equiv_H_involutions
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {u : G}
    (huI : IsInvolution u) :
    {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution y} ≃
      {y : G // y ∈ h.H ∧ IsInvolution y} := by
  let g := Classical.choose (h.involutions_conjugate u huI)
  have hgu : g * u * g⁻¹ = h.t :=
    Classical.choose_spec (h.involutions_conjugate u huI)
  have hback : g⁻¹ * h.t * g = u := by
    have hc := congrArg (fun z : G => g⁻¹ * z * g) hgu
    simpa [mul_assoc] using hc.symm
  have conj_involution (a c : G) (ha : IsInvolution a) :
      IsInvolution (c * a * c⁻¹) := by
    constructor
    · intro hone
      apply ha.1
      have hc := congrArg (fun z : G => c⁻¹ * z * c) hone
      simpa [mul_assoc] using hc
    · calc
        (c * a * c⁻¹) ^ 2 = c * (a ^ 2) * c⁻¹ := by
          simp [pow_two, mul_assoc]
        _ = 1 := by rw [ha.2]; simp
  let toFun :
      {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution y} →
        {y : G // y ∈ h.H ∧ IsInvolution y} := fun y =>
    ⟨g * (y : G) * g⁻¹, by
      rw [h.H_eq_centralizer,
        Subgroup.mem_centralizer_singleton_iff]
      have hc := Subgroup.mem_centralizer_singleton_iff.mp y.property.1
      calc
        g * (y : G) * g⁻¹ * h.t =
            g * (y : G) * g⁻¹ * (g * u * g⁻¹) := by rw [hgu]
        _ = g * ((y : G) * u) * g⁻¹ := by simp [mul_assoc]
        _ = g * (u * (y : G)) * g⁻¹ := by rw [hc]
        _ = (g * u * g⁻¹) * (g * (y : G) * g⁻¹) := by simp [mul_assoc]
        _ = h.t * (g * (y : G) * g⁻¹) := by rw [hgu],
      conj_involution (y : G) g y.property.2⟩
  let invFun : {y : G // y ∈ h.H ∧ IsInvolution y} →
      {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution y} :=
    fun y =>
      ⟨g⁻¹ * (y : G) * g, by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hyC : (y : G) ∈ Subgroup.centralizer ({h.t} : Set G) := by
          rw [← h.H_eq_centralizer]
          exact y.property.1
        have hc := Subgroup.mem_centralizer_singleton_iff.mp hyC
        calc
          g⁻¹ * (y : G) * g * u =
              g⁻¹ * (y : G) * g * (g⁻¹ * h.t * g) := by rw [hback]
          _ = g⁻¹ * ((y : G) * h.t) * g := by simp [mul_assoc]
          _ = g⁻¹ * (h.t * (y : G)) * g := by rw [hc]
          _ = (g⁻¹ * h.t * g) * (g⁻¹ * (y : G) * g) := by
            simp [mul_assoc]
          _ = u * (g⁻¹ * (y : G) * g) := by rw [hback],
        by
          simpa using conj_involution (y : G) g⁻¹ y.property.2⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro y
        apply Subtype.ext
        simp [toFun, invFun, mul_assoc]
      right_inv := by
        intro y
        apply Subtype.ext
        simp [toFun, invFun, mul_assoc] }

/-- Every involution centralizer contains exactly `|K| + 1`
involutions. -/
private theorem centralizer_involutions_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {u : G}
    (huI : IsInvolution u) :
    Nat.card
        {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution y} =
      Nat.card h.K + 1 := by
  calc
    Nat.card
        {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧ IsInvolution y} =
        Nat.card {y : G // y ∈ h.H ∧ IsInvolution y} :=
      Nat.card_congr (centralizer_involutions_equiv_H_involutions h huI)
    _ = Nat.card h.K + 1 := bsw_H_involutions_card h

/-- An involution `u` in the selected normalizer is the only involution in
its internal centralizer.  Indeed, a second commuting involution would give
an involution in the odd-order selected centralizer `F`. -/
private theorem selected_centralizer_internal_involution_eq
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u a : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u)
    (haM : a ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (haC : a ∈ Subgroup.centralizer ({u} : Set G))
    (haI : IsInvolution a) :
    a = u := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have huaF : u * a ∈ F :=
    mul_mem_selected_centralizer_of_involutions_mem_normalizer
      h hxC hxne huI haI huM haM
  have hau : a * u = u * a :=
    Subgroup.mem_centralizer_singleton_iff.mp haC
  have huu : u * u = 1 := by
    simpa [pow_two] using huI.2
  have haa : a * a = 1 := by
    simpa [pow_two] using haI.2
  have huaSq : (u * a) ^ 2 = 1 := by
    calc
      (u * a) ^ 2 = u * a * (u * a) := by rw [pow_two]
      _ = u * (a * u) * a := by simp [mul_assoc]
      _ = u * (u * a) * a := by rw [hau]
      _ = (u * u) * (a * a) := by simp [mul_assoc]
      _ = 1 := by rw [huu, haa]; simp
  have huaOne : u * a = 1 := by
    by_contra huaNe
    exact
      (BenderSuzuki.PFchapter1section1.not_isInvolution_of_mem_odd_subgroup
        F hFodd huaF) ⟨huaNe, huaSq⟩
  calc
    a = u⁻¹ := eq_inv_of_mul_eq_one_right huaOne
    _ = u := inv_eq_of_mul_eq_one_right huu

/-- The internal centralizer `M ∩ C_G(u)` contains exactly one involution. -/
private theorem selected_centralizer_internal_involutions_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card
        {a : {y : G // y ∈ Subgroup.centralizer ({u} : Set G) ∧
            IsInvolution y} //
          (a : G) ∈ M} = 1 := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  apply Nat.card_eq_one_iff_unique.mpr
  constructor
  · constructor
    intro a b
    have ha : (a : G) = u :=
      selected_centralizer_internal_involution_eq
        h hxC hxne hFodd huM huI a.property
          a.val.property.1 a.val.property.2
    have hb : (b : G) = u :=
      selected_centralizer_internal_involution_eq
        h hxC hxne hFodd huM huI b.property
          b.val.property.1 b.val.property.2
    apply Subtype.ext
    apply Subtype.ext
    exact ha.trans hb.symm
  · refine ⟨⟨⟨u, ?_, huI⟩, huM⟩⟩
    rw [Subgroup.mem_centralizer_singleton_iff]

/-- Removing the unique internal involution from `C_G(u)` leaves exactly
`|K|` involutions outside the selected normalizer. -/
private theorem selected_centralizer_external_involutions_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card
        {y : {a : G // a ∈ Subgroup.centralizer ({u} : Set G) ∧
            IsInvolution a} //
          (y : G) ∉ M} = Nat.card h.K := by
  classical
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let I := {a : G // a ∈ Subgroup.centralizer ({u} : Set G) ∧
    IsInvolution a}
  have hinternal : Nat.card {y : I // (y : G) ∈ M} = 1 :=
    selected_centralizer_internal_involutions_card
      h hxC hxne hFodd huM huI
  have htotal : Nat.card I = Nat.card h.K + 1 :=
    centralizer_involutions_card h huI
  have hpartition :
      Nat.card {y : I // (y : G) ∈ M} +
          Nat.card {y : I // (y : G) ∉ M} = Nat.card I := by
    calc
      Nat.card {y : I // (y : G) ∈ M} +
            Nat.card {y : I // (y : G) ∉ M} =
          Nat.card ({y : I // (y : G) ∈ M} ⊕
            {y : I // (y : G) ∉ M}) := Nat.card_sum.symm
      _ = Nat.card I :=
        Nat.card_congr (Equiv.sumCompl (fun y : I => (y : G) ∈ M))
  change Nat.card {y : I // (y : G) ∉ M} = Nat.card h.K
  omega

/-- A coset fixed by an involution of the selected normalizer has a
representative centralizing that involution.  This is the representative
change implicit in the first sentence of Bender 3.2. -/
private theorem selected_centralizer_fixed_coset_centralizing_rep
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u)
    (omega : G ⧸ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (homega : u • omega = omega) :
    ∃ g : G,
      (g : G ⧸ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G)) = omega ∧
      g ∈ Subgroup.centralizer ({u} : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let g : G := omega.out
  have huinv : u⁻¹ = u := by
    exact inv_eq_of_mul_eq_one_right (by simpa [pow_two] using huI.2)
  have homegaOut : u • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M) := by
    simpa only [g, M, F, QuotientGroup.out_eq'] using homega
  have hconjM : g⁻¹ * u * g ∈ M := by
    change ((((u * g : G)) : G ⧸ M) = (g : G ⧸ M)) at homegaOut
    rw [QuotientGroup.eq] at homegaOut
    simpa [huinv, mul_assoc] using homegaOut
  have hconjI : IsInvolution (g⁻¹ * u * g) := by
    simpa [GorensteinWalter.IsInvolution,
      BenderSuzuki.PFAppendixIII.IsInvolution,
      BenderSuzuki.PFAppendixIII.rightConjugateElem] using
      (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
        (x := u) (g := g) huI)
  obtain ⟨m, hmF, hmconj⟩ :=
    selected_centralizer_involutions_conjugate
      h hxC hxne hFodd hFinv hconjM hconjI huM huI
  have hmM : m ∈ M := Subgroup.le_normalizer hmF
  let e : G := g * m
  refine ⟨e, ?_, ?_⟩
  · calc
      (e : G ⧸ M) = (g : G ⧸ M) := by
        rw [QuotientGroup.eq]
        dsimp [e]
        simpa [mul_assoc] using M.inv_mem hmM
      _ = omega := by
        exact QuotientGroup.out_eq' omega
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := congrArg (fun z : G => e * z) hmconj
    simpa [e, g, mul_assoc] using hc.symm

/-- Fixed cosets of the selected normalizer for an involution `u` are the
cosets of its internal centralizer inside its ambient centralizer. -/
private noncomputable def
    selected_centralizer_fixed_cosets_equiv_centralizer_quotient
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    let C := Subgroup.centralizer ({u} : Set G)
    let CM := (M ⊓ C).subgroupOf C
    C ⧸ CM ≃ {omega : G ⧸ M // u • omega = omega} := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  let CM : Subgroup C := (M ⊓ C).subgroupOf C
  have huinv : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using huI.2)
  let toRep : C → {omega : G ⧸ M // u • omega = omega} := fun c =>
    ⟨((c : G) : G ⧸ M), by
      change (((u * (c : G) : G) : G ⧸ M) = ((c : G) : G ⧸ M))
      rw [QuotientGroup.eq]
      have hcomm : (c : G) * u = u * (c : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp c.property
      have hcommInv : (c : G)⁻¹ * u * (c : G) = u := by
        calc
          (c : G)⁻¹ * u * (c : G) =
              (c : G)⁻¹ * (u * (c : G)) := by group
          _ = (c : G)⁻¹ * ((c : G) * u) := by rw [hcomm.symm]
          _ = u := by simp
      simpa [huinv, mul_assoc, hcommInv] using M.inv_mem huM⟩
  let toFun : C ⧸ CM → {omega : G ⧸ M // u • omega = omega} := fun q =>
    Quotient.liftOn' q toRep (by
      intro a b hab
      apply Subtype.ext
      change (((a : G) : G ⧸ M) = ((b : G) : G ⧸ M))
      rw [QuotientGroup.eq]
      exact (QuotientGroup.leftRel_apply.mp hab).1)
  let centralRep : {omega : G ⧸ M // u • omega = omega} → G :=
    fun omega => Classical.choose
      (selected_centralizer_fixed_coset_centralizing_rep
        h hxC hxne hFodd hFinv huM huI omega.1 omega.2)
  have centralRep_spec
      (omega : {omega : G ⧸ M // u • omega = omega}) :
      ((centralRep omega : G) : G ⧸ M) = omega.1 ∧
        centralRep omega ∈ C := by
    exact Classical.choose_spec
      (selected_centralizer_fixed_coset_centralizing_rep
        h hxC hxne hFodd hFinv huM huI omega.1 omega.2)
  let invFun : {omega : G ⧸ M // u • omega = omega} → C ⧸ CM :=
    fun omega =>
      ((⟨centralRep omega, (centralRep_spec omega).2⟩ : C) : C ⧸ CM)
  refine
    { toFun := toFun
      invFun := invFun
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    refine Quotient.inductionOn' q ?_
    intro c
    apply QuotientGroup.eq.mpr
    change ((⟨centralRep (toRep c),
      (centralRep_spec (toRep c)).2⟩ : C)⁻¹ * c) ∈ CM
    change (centralRep (toRep c))⁻¹ * (c : G) ∈ M ⊓ C
    refine ⟨?_, ?_⟩
    · apply QuotientGroup.eq.mp
      exact (centralRep_spec (toRep c)).1
    · exact C.mul_mem
        (C.inv_mem (centralRep_spec (toRep c)).2) c.property
  · intro omega
    apply Subtype.ext
    change ((centralRep omega : G) : G ⧸ M) = omega.1
    exact (centralRep_spec omega).1

/-- The fixed-coset count in multiplication form: the number of fixed
`M`-cosets times the order of the internal centralizer is the order of the
ambient centralizer. -/
private theorem selected_centralizer_fixed_cosets_card_mul_internal_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    let C := Subgroup.centralizer ({u} : Set G)
    Nat.card {omega : G ⧸ M // u • omega = omega} *
        Nat.card (M ⊓ C : Subgroup G) = Nat.card C := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  let CM : Subgroup C := (M ⊓ C).subgroupOf C
  have hquotCard : Nat.card (C ⧸ CM) =
      Nat.card {omega : G ⧸ M // u • omega = omega} :=
    Nat.card_congr
      (selected_centralizer_fixed_cosets_equiv_centralizer_quotient
        h hxC hxne hFodd hFinv huM huI)
  have hCMcard : Nat.card CM = Nat.card (M ⊓ C : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  calc
    Nat.card {omega : G ⧸ M // u • omega = omega} *
          Nat.card (M ⊓ C : Subgroup G) =
        Nat.card (C ⧸ CM) * Nat.card CM := by
      rw [hquotCard, hCMcard]
    _ = Nat.card C :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup CM).symm

/-- Every involution in the selected normalizer fixes `r` cosets with
`r |K ∩ M| = 2|K|`. -/
private theorem selected_centralizer_fixed_cosets_card_mul_inf_K_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card {omega : G ⧸ M // u • omega = omega} *
        Nat.card (h.K ⊓ M : Subgroup G) = 2 * Nat.card h.K := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let C : Subgroup G := Subgroup.centralizer ({u} : Set G)
  calc
    Nat.card {omega : G ⧸ M // u • omega = omega} *
          Nat.card (h.K ⊓ M : Subgroup G) =
        Nat.card {omega : G ⧸ M // u • omega = omega} *
          Nat.card (M ⊓ C : Subgroup G) := by
      rw [selected_centralizer_inf_centralizer_involution_card
        h hxC hxne hFodd hFinv huM huI]
    _ = Nat.card C :=
      selected_centralizer_fixed_cosets_card_mul_internal_card
        h hxC hxne hFodd hFinv huM huI
    _ = Nat.card h.H := centralizer_involution_card_eq_card_H h huI
    _ = 2 * Nat.card h.K := h.card_H

/-- A non-base coset of the selected normalizer is fixed by at most one of
its involutions.  The product of two such involutions lies in both `F` and
the conjugate normalizer attached to the coset, so Bender 3.1(iii) makes it
trivial. -/
private theorem selected_centralizer_fixed_coset_unique_involution
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x u v : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u)
    (hvM : v ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hvI : IsInvolution v)
    (omega : G ⧸ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (homegaNe : omega ≠
      ((1 : G) : G ⧸ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G)))
    (huFix : u • omega = omega) (hvFix : v • omega = omega) :
    u = v := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let g : G := omega.out
  have hgM : g ∉ M := by
    intro hgM
    apply homegaNe
    calc
      omega = (g : G ⧸ M) := (QuotientGroup.out_eq' omega).symm
      _ = ((1 : G) : G ⧸ M) := by
        rw [QuotientGroup.eq]
        simpa using M.inv_mem hgM
  have fixed_conj_mem (a : G) (haI : IsInvolution a)
      (haFix : a • omega = omega) : a ∈ M.conjBy g := by
    have hainv : a⁻¹ = a :=
      inv_eq_of_mul_eq_one_right (by simpa [pow_two] using haI.2)
    have haFixOut : a • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M) := by
      simpa only [g, M, F, QuotientGroup.out_eq'] using haFix
    have hconjM : g⁻¹ * a * g ∈ M := by
      change ((((a * g : G)) : G ⧸ M) = (g : G ⧸ M)) at haFixOut
      rw [QuotientGroup.eq] at haFixOut
      simpa [hainv, mul_assoc] using haFixOut
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * a * g, hconjM, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have huMg : u ∈ M.conjBy g := fixed_conj_mem u huI huFix
  have hvMg : v ∈ M.conjBy g := fixed_conj_mem v hvI hvFix
  have huvF : u * v ∈ F :=
    mul_mem_selected_centralizer_of_involutions_mem_normalizer
      h hxC hxne huI hvI huM hvM
  have huvMg : u * v ∈ M.conjBy g :=
    (M.conjBy g).mul_mem huMg hvMg
  have huvOne : u * v = 1 :=
    Subgroup.disjoint_def.mp
      (selected_centralizer_disjoint_conj_normalizer
        hxne hFHall hFTI g hgM) huvF huvMg
  calc
    u = v⁻¹ := eq_inv_of_mul_eq_one_left huvOne
    _ = v := inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using hvI.2)

/-- If an outside involution lies in a coset fixed by an involution of the
selected normalizer, then the two involutions commute.  Conjugating the
fixer by the outside involution gives a second fixer in `M`, so uniqueness
on the non-base coset applies. -/
private theorem selected_centralizer_occupied_involution_centralizes_fixer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x y u : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hyI : IsInvolution y)
    (hyM : y ∉ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huM : u ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (huI : IsInvolution u)
    (huFix : u •
        ((y : G) : G ⧸ Subgroup.normalizer
          (Subgroup.centralizer ({x} : Set G) : Set G)) =
      ((y : G) : G ⧸ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))) :
    y ∈ Subgroup.centralizer ({u} : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let omega : G ⧸ M := ((y : G) : G ⧸ M)
  let v : G := y * u * y
  have hyy : y * y = 1 := by
    simpa [pow_two] using hyI.2
  have huu : u * u = 1 := by
    simpa [pow_two] using huI.2
  have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have huInv : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hvM : v ∈ M := by
    change ((((u * y : G)) : G ⧸ M) = (y : G ⧸ M)) at huFix
    rw [QuotientGroup.eq] at huFix
    simpa [v, mul_inv_rev, hyInv, huInv, mul_assoc] using huFix
  have hvI : IsInvolution v := by
    simpa [v, hyInv, GorensteinWalter.IsInvolution,
      BenderSuzuki.PFAppendixIII.IsInvolution,
      BenderSuzuki.PFAppendixIII.rightConjugateElem] using
      (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
        (x := u) (g := y) huI)
  have homegaNe : omega ≠ ((1 : G) : G ⧸ M) := by
    intro heq
    apply hyM
    rw [QuotientGroup.eq] at heq
    have hyInvM : y⁻¹ ∈ M := by simpa using heq
    simpa using M.inv_mem hyInvM
  have hvFix : v • omega = omega := by
    change ((((v * y : G)) : G ⧸ M) = (y : G ⧸ M))
    rw [QuotientGroup.eq]
    simpa [v, mul_inv_rev, hyInv, huInv, hyy, huu, mul_assoc] using huM
  have huv : u = v :=
    selected_centralizer_fixed_coset_unique_involution
      h hxC hxne hFHall hFTI huM huI hvM hvI omega homegaNe huFix hvFix
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc
    y * u = y * v := by rw [huv]
    _ = y * (y * u * y) := rfl
    _ = (y * y) * u * y := by group
    _ = u * y := by rw [hyy]; simp

/-- The involutions contained in the normalizer of a selected centralizer. -/
private abbrev selected_centralizer_normalizer_involutions
    {G : Type u} [Group G] (F : Subgroup G) :=
  {u : G // u ∈ Subgroup.normalizer (F : Set G) ∧ IsInvolution u}

/-- Commuting pairs consisting of an involution of the selected normalizer
and an involution outside it. -/
private abbrev selected_centralizer_external_commuting_involution_pairs
    {G : Type u} [Group G] (F : Subgroup G) :=
  {p : selected_centralizer_normalizer_involutions F × G //
    p.2 ∈ Subgroup.centralizer ({(p.1 : G)} : Set G) ∧
      IsInvolution p.2 ∧
      p.2 ∉ Subgroup.normalizer (F : Set G)}

/-- The involutions lying in occupied non-base cosets of the selected
normalizer. -/
private abbrev selected_centralizer_occupied_nonbase_involutions
    {G : Type u} [Group G] (F : Subgroup G) :=
  {y : G //
    IsInvolution y ∧
      y ∉ Subgroup.normalizer (F : Set G) ∧
      ∃ u : selected_centralizer_normalizer_involutions F,
        (u : G) •
            ((y : G) : G ⧸ Subgroup.normalizer (F : Set G)) =
          ((y : G) : G ⧸ Subgroup.normalizer (F : Set G))}

/-- The involutions lying in unoccupied non-base cosets of the selected
normalizer. -/
private abbrev selected_centralizer_unoccupied_nonbase_involutions
    {G : Type u} [Group G] (F : Subgroup G) :=
  {y : G //
    IsInvolution y ∧
      ((y : G) : G ⧸ Subgroup.normalizer (F : Set G)) ≠
        ((1 : G) : G ⧸ Subgroup.normalizer (F : Set G)) ∧
      ∀ u : selected_centralizer_normalizer_involutions F,
        (u : G) •
            ((y : G) : G ⧸ Subgroup.normalizer (F : Set G)) ≠
          ((y : G) : G ⧸ Subgroup.normalizer (F : Set G))}

/-- Incidences between an involution in the selected normalizer and one of
its fixed non-base cosets. -/
private abbrev selected_centralizer_nonbase_fixed_incidences
    {G : Type u} [Group G] (F : Subgroup G) :=
  {p : selected_centralizer_normalizer_involutions F ×
      (G ⧸ Subgroup.normalizer (F : Set G)) //
    (p.1 : G) • p.2 = p.2 ∧
      p.2 ≠ ((1 : G) : G ⧸ Subgroup.normalizer (F : Set G))}

/-- The non-base cosets fixed by at least one involution of the selected
normalizer. -/
private abbrev selected_centralizer_occupied_nonbase_cosets
    {G : Type u} [Group G] (F : Subgroup G) :=
  {omega : G ⧸ Subgroup.normalizer (F : Set G) //
    omega ≠ ((1 : G) : G ⧸ Subgroup.normalizer (F : Set G)) ∧
      ∃ u : selected_centralizer_normalizer_involutions F,
        (u : G) • omega = omega}

/-- The complementary non-base cosets, fixed by no involution of the
selected normalizer. -/
private abbrev selected_centralizer_unoccupied_nonbase_cosets
    {G : Type u} [Group G] (F : Subgroup G) :=
  {omega : G ⧸ Subgroup.normalizer (F : Set G) //
    omega ≠ ((1 : G) : G ⧸ Subgroup.normalizer (F : Set G)) ∧
      ∀ u : selected_centralizer_normalizer_involutions F,
        (u : G) • omega ≠ omega}

/-- The involutions contained in a specified coset of the selected
normalizer. -/
private abbrev selected_centralizer_coset_involutions
    {G : Type u} [Group G] (F : Subgroup G)
    (omega : G ⧸ Subgroup.normalizer (F : Set G)) :=
  {y : G //
    IsInvolution y ∧
      ((y : G) : G ⧸ Subgroup.normalizer (F : Set G)) = omega}

/-- Ambient involutions split into those in the selected normalizer, those
in occupied non-base cosets, and those in unoccupied non-base cosets. -/
private noncomputable def selected_centralizer_involutions_equiv_partition
    {G : Type u} [Group G] (F : Subgroup G) :
    {y : G // IsInvolution y} ≃
      selected_centralizer_normalizer_involutions F ⊕
        (selected_centralizer_occupied_nonbase_involutions F ⊕
          selected_centralizer_unoccupied_nonbase_involutions F) := by
  classical
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Occupied := selected_centralizer_occupied_nonbase_involutions F
  let Unoccupied := selected_centralizer_unoccupied_nonbase_involutions F
  have coset_ne_base_of_not_mem (y : G) (hyM : y ∉ M) :
      ((y : G) : G ⧸ M) ≠ ((1 : G) : G ⧸ M) := by
    intro heq
    apply hyM
    rw [QuotientGroup.eq] at heq
    have hyInvM : y⁻¹ ∈ M := by simpa using heq
    simpa using M.inv_mem hyInvM
  have not_mem_of_coset_ne_base (y : G)
      (hy : ((y : G) : G ⧸ M) ≠ ((1 : G) : G ⧸ M)) : y ∉ M := by
    intro hyM
    apply hy
    rw [QuotientGroup.eq]
    simpa using M.inv_mem hyM
  let toFun : {y : G // IsInvolution y} →
      U ⊕ (Occupied ⊕ Unoccupied) := fun y =>
    if hyM : (y : G) ∈ M then
      Sum.inl ⟨(y : G), hyM, y.property⟩
    else if hfix : ∃ u : U,
        (u : G) • ((y : G) : G ⧸ M) = ((y : G) : G ⧸ M) then
      Sum.inr (Sum.inl ⟨(y : G), y.property, hyM, hfix⟩)
    else
      Sum.inr (Sum.inr
        ⟨(y : G), y.property, coset_ne_base_of_not_mem (y : G) hyM,
          by
            intro u huFix
            exact hfix ⟨u, huFix⟩⟩)
  let invFun : U ⊕ (Occupied ⊕ Unoccupied) →
      {y : G // IsInvolution y}
    | Sum.inl y => ⟨(y : G), y.property.2⟩
    | Sum.inr (Sum.inl y) => ⟨(y : G), y.property.1⟩
    | Sum.inr (Sum.inr y) => ⟨(y : G), y.property.1⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro y
        apply Subtype.ext
        dsimp only [toFun]
        split
        · rfl
        · split <;> rfl
      right_inv := by
        intro q
        rcases q with u | q
        · change toFun ⟨(u : G), u.property.2⟩ = Sum.inl u
          dsimp only [toFun]
          rw [dif_pos u.property.1]
        · rcases q with y | y
          · change toFun ⟨(y : G), y.property.1⟩ = Sum.inr (Sum.inl y)
            dsimp only [toFun]
            rw [dif_neg y.property.2.1, dif_pos y.property.2.2]
          · have hyM : (y : G) ∉ M :=
              not_mem_of_coset_ne_base (y : G) y.property.2.1
            have hfix : ¬ ∃ u : U,
                (u : G) • ((y : G) : G ⧸ M) = ((y : G) : G ⧸ M) := by
              rintro ⟨u, huFix⟩
              exact y.property.2.2 u huFix
            change toFun ⟨(y : G), y.property.1⟩ = Sum.inr (Sum.inr y)
            dsimp only [toFun]
            rw [dif_neg hyM, dif_neg hfix] }

/-- Commuting pairs `(u,y)`, with `u` in the selected normalizer and `y`
outside it, are exactly the involutions lying in occupied non-base cosets. -/
private noncomputable def
    selected_centralizer_external_commuting_pairs_equiv_occupied_involutions
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    selected_centralizer_external_commuting_involution_pairs F ≃
      selected_centralizer_occupied_nonbase_involutions F := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Pair := selected_centralizer_external_commuting_involution_pairs F
  let Occupied := selected_centralizer_occupied_nonbase_involutions F
  have fixed_of_centralizing (u : U) (y : G)
      (hyC : y ∈ Subgroup.centralizer ({(u : G)} : Set G)) :
      (u : G) • ((y : G) : G ⧸ M) = ((y : G) : G ⧸ M) := by
    change (((((u : G) * y : G)) : G ⧸ M) = (y : G ⧸ M))
    rw [QuotientGroup.eq]
    have hyu : Commute y (u : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hcalc : ((u : G) * y)⁻¹ * y = (u : G)⁻¹ := by
      calc
        ((u : G) * y)⁻¹ * y = y⁻¹ * (u : G)⁻¹ * y := by
          rw [mul_inv_rev]
        _ = y⁻¹ * ((u : G)⁻¹ * y) := by rw [mul_assoc]
        _ = y⁻¹ * (y * (u : G)⁻¹) := by
          rw [hyu.inv_right.eq.symm]
        _ = (u : G)⁻¹ := by simp
    rw [hcalc]
    exact M.inv_mem u.property.1
  have coset_ne_base_of_not_mem (y : G) (hyM : y ∉ M) :
      ((y : G) : G ⧸ M) ≠ ((1 : G) : G ⧸ M) := by
    intro heq
    apply hyM
    rw [QuotientGroup.eq] at heq
    have hyInvM : y⁻¹ ∈ M := by simpa using heq
    simpa using M.inv_mem hyInvM
  let toFun : Pair → Occupied := fun p =>
    ⟨p.1.2, p.2.2.1, p.2.2.2,
      ⟨p.1.1, fixed_of_centralizing p.1.1 p.1.2 p.2.1⟩⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro p q hpq
    have hy : p.1.2 = q.1.2 := congrArg Subtype.val hpq
    have hpFix := fixed_of_centralizing p.1.1 p.1.2 p.2.1
    have hqFix := fixed_of_centralizing q.1.1 q.1.2 q.2.1
    have hyCoset :
        ((p.1.2 : G) : G ⧸ M) = ((q.1.2 : G) : G ⧸ M) :=
      congrArg (fun z : G => ((z : G) : G ⧸ M)) hy
    have hqFix' :
        (q.1.1 : G) • ((p.1.2 : G) : G ⧸ M) =
          ((p.1.2 : G) : G ⧸ M) := by
      calc
        (q.1.1 : G) • ((p.1.2 : G) : G ⧸ M) =
            (q.1.1 : G) • ((q.1.2 : G) : G ⧸ M) := by rw [hyCoset]
        _ = ((q.1.2 : G) : G ⧸ M) := hqFix
        _ = ((p.1.2 : G) : G ⧸ M) := hyCoset.symm
    have hu : (p.1.1 : G) = (q.1.1 : G) :=
      selected_centralizer_fixed_coset_unique_involution
        h hxC hxne hFHall hFTI
          p.1.1.property.1 p.1.1.property.2
          q.1.1.property.1 q.1.1.property.2
          ((p.1.2 : G) : G ⧸ M)
          (coset_ne_base_of_not_mem p.1.2 p.2.2.2) hpFix hqFix'
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hu
    · exact hy
  · intro y
    obtain ⟨u, huFix⟩ := y.property.2.2
    have hyC : (y : G) ∈ Subgroup.centralizer ({(u : G)} : Set G) :=
      selected_centralizer_occupied_involution_centralizes_fixer
        h hxC hxne hFHall hFTI y.property.1 y.property.2.1
          u.property.1 u.property.2 huFix
    refine ⟨⟨(u, (y : G)), hyC, y.property.1, y.property.2.1⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- There are `|F||K|` commuting pairs consisting of an involution in the
selected normalizer and an involution outside it. -/
private theorem selected_centralizer_external_commuting_pairs_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    Nat.card (selected_centralizer_external_commuting_involution_pairs F) =
      Nat.card F * Nat.card h.K := by
  classical
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Pair := selected_centralizer_external_commuting_involution_pairs F
  let External (u : U) :=
    {y : {a : G // a ∈ Subgroup.centralizer ({(u : G)} : Set G) ∧
        IsInvolution a} //
      (y : G) ∉ M}
  let ePair : Pair ≃ Σ u : U, External u :=
    { toFun := fun p =>
        ⟨p.1.1, ⟨⟨p.1.2, p.2.1, p.2.2.1⟩, p.2.2.2⟩⟩
      invFun := fun p =>
        ⟨(p.1, (p.2 : G)),
          p.2.val.property.1, p.2.val.property.2, p.2.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  have hExternal (u : U) : Nat.card (External u) = Nat.card h.K :=
    selected_centralizer_external_involutions_card
      h hxC hxne hFodd u.property.1 u.property.2
  let : Fintype U := Fintype.ofFinite U
  calc
    Nat.card Pair = Nat.card (Σ u : U, External u) := Nat.card_congr ePair
    _ = ∑ u : U, Nat.card (External u) := Nat.card_sigma
    _ = ∑ _u : U, Nat.card h.K := by
      apply Finset.sum_congr rfl
      intro u _hu
      exact hExternal u
    _ = Nat.card U * Nat.card h.K := by
      simp [Nat.card_eq_fintype_card]
    _ = Nat.card F * Nat.card h.K := by
      rw [selected_centralizer_involutions_normalizer_card
        h hxC hxne hFinv]

/-- The occupied non-base cosets contain exactly `|F||K|` involutions. -/
private theorem selected_centralizer_occupied_nonbase_involutions_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    Nat.card (selected_centralizer_occupied_nonbase_involutions F) =
      Nat.card F * Nat.card h.K := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  calc
    Nat.card (selected_centralizer_occupied_nonbase_involutions F) =
        Nat.card (selected_centralizer_external_commuting_involution_pairs F) :=
      (Nat.card_congr
        (selected_centralizer_external_commuting_pairs_equiv_occupied_involutions
          h hxC hxne hFHall hFTI)).symm
    _ = Nat.card F * Nat.card h.K :=
      selected_centralizer_external_commuting_pairs_card
        h hxC hxne hFodd hFinv

/-- A cyclic subgroup of the selected normalizer that misses `F` is
conjugate by an element of `F` into `K ∩ M`.  This is the precise
Schur--Zassenhaus step behind Bender's assertion about involutions that
invert a nonidentity element of `M`. -/
private theorem selected_centralizer_zpowers_conjugate_into_inf_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x m : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hmM : m ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hFJ : Disjoint
      (Subgroup.centralizer ({x} : Set G)) (Subgroup.zpowers m)) :
    ∃ f : G,
      f ∈ Subgroup.centralizer ({x} : Set G) ∧
        f * m * f⁻¹ ∈ h.K ⊓
          Subgroup.normalizer
            (Subgroup.centralizer ({x} : Set G) : Set G) := by
  classical
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  let J : Subgroup G := Subgroup.zpowers m
  let P : Subgroup G := F ⊔ J
  let A0 : Subgroup G := A ⊓ P
  have hFleM : F ≤ M := Subgroup.le_normalizer
  have hAleM : A ≤ M := inf_le_right
  have hJleM : J ≤ M := Subgroup.zpowers_le.mpr hmM
  have hFleP : F ≤ P := le_sup_left
  have hJleP : J ≤ P := le_sup_right
  have hPleM : P ≤ M := sup_le hFleM hJleM
  have hMdecomp : M = F ⊔ A :=
    selected_centralizer_normalizer_eq_sup_inf_K
      h hxC hxne hFodd hFinv
  have hMset : (M : Set G) = (F : Set G) * (A : Set G) := by
    calc
      (M : Set G) = ((F ⊔ A : Subgroup G) : Set G) :=
        congrArg (fun S : Subgroup G => (S : Set G)) hMdecomp
      _ = (F : Set G) * (A : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left F A hAleM
  have hPdecomp : P = F ⊔ A0 := by
    apply le_antisymm
    · intro p hpP
      have hpM : p ∈ M := hPleM hpP
      have hpProd : p ∈ (F : Set G) * (A : Set G) := by
        rw [← hMset]
        exact hpM
      rcases hpProd with ⟨f, hfF, a, haA, hfa⟩
      have haP : a ∈ P := by
        have haEq : a = f⁻¹ * p := by
          calc
            a = 1 * a := by simp
            _ = (f⁻¹ * f) * a := by simp
            _ = f⁻¹ * (f * a) := by group
            _ = f⁻¹ * p := congrArg (fun z : G => f⁻¹ * z) hfa
        rw [haEq]
        exact P.mul_mem (P.inv_mem (hFleP hfF)) hpP
      rw [← hfa]
      exact (F ⊔ A0).mul_mem
        (Subgroup.mem_sup_left hfF)
        (Subgroup.mem_sup_right ⟨haA, haP⟩)
    · exact sup_le hFleP inf_le_right
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hAleH : A ≤ h.H := inf_le_left.trans hKleH
  have hFdisjA : Disjoint F A :=
    (selected_centralizer_disjoint_H h hxC hxne).mono_right hAleH
  have hFdisjA0 : Disjoint F A0 := hFdisjA.mono_right inf_le_left
  have complement_of (B : Subgroup G) (hBleP : B ≤ P)
      (hFdisjB : Disjoint F B) (hPdecompB : P = F ⊔ B) :
      (F.subgroupOf P).IsComplement' (B.subgroupOf P) := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro z hzF hzB
      apply Subtype.ext
      exact Subgroup.disjoint_def.mp hFdisjB
        (by simpa [Subgroup.mem_subgroupOf] using hzF)
        (by simpa [Subgroup.mem_subgroupOf] using hzB)
    · rw [Set.eq_univ_iff_forall]
      intro p
      have hBnorm : B ≤ Subgroup.normalizer (F : Set G) :=
        hBleP.trans hPleM
      have hpProd : (p : G) ∈ (F : Set G) * (B : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left F B hBnorm,
          ← hPdecompB]
        exact p.property
      rcases hpProd with ⟨f, hfF, b, hbB, hfb⟩
      refine ⟨⟨f, hFleP hfF⟩, ?_, ⟨b, hBleP hbB⟩, ?_, ?_⟩
      · simpa [Subgroup.mem_subgroupOf] using hfF
      · simpa [Subgroup.mem_subgroupOf] using hbB
      · apply Subtype.ext
        exact hfb
  let Fp : Subgroup P := F.subgroupOf P
  let Jp : Subgroup P := J.subgroupOf P
  let A0p : Subgroup P := A0.subgroupOf P
  have hFpNormal : Fp.Normal := by
    exact
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFleP).mpr hPleM
  let : Fp.Normal := hFpNormal
  let : IsMulCommutative Fp := by
    refine IsMulCommutative.mk ⟨?_⟩
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := F)).comm
        ⟨(a : G), a.property⟩ ⟨(b : G), b.property⟩)
  have hFpCard : Nat.card Fp = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFleP).toEquiv
  have hFpIndexDvd : Fp.index ∣ F.index := by
    simpa [Fp, Subgroup.relIndex] using
      Subgroup.relIndex_dvd_index_of_le hFleP
  have hFpCoprime : Nat.Coprime (Nat.card Fp) Fp.index := by
    rw [hFpCard]
    exact hFHall.of_dvd_right hFpIndexDvd
  have hJcomp : Fp.IsComplement' Jp :=
    complement_of J hJleP hFJ rfl
  have hA0comp : Fp.IsComplement' A0p :=
    complement_of A0 inf_le_right hFdisjA0 hPdecomp
  obtain ⟨f, hfconj⟩ :=
    Subgroup.exists_conj_eq_of_isComplement'
      hFpCoprime hJcomp hA0comp
  let mP : P := ⟨m, hJleP (Subgroup.mem_zpowers m)⟩
  have hmJp : mP ∈ Jp := Subgroup.mem_zpowers m
  have hmMap :
      (MulAut.conj (f : P)) mP ∈
        Jp.map (MulAut.conj (f : P)).toMonoidHom :=
    Subgroup.mem_map_of_mem
      (MulAut.conj (f : P)).toMonoidHom hmJp
  rw [← hfconj] at hmMap
  let fG : G := (f : P)
  refine ⟨fG, ?_, ?_⟩
  · exact f.property
  · have hmA0 : fG * m * fG⁻¹ ∈ A0 := by
      change (((MulAut.conj (f : P)) mP : P) : G) ∈ A0 at hmMap
      simpa [fG, mP, MulAut.conj_apply] using hmMap
    exact hmA0.1

/-- An involution outside the selected normalizer that inverts a nonidentity
element of the normalizer commutes with an involution in the normalizer.
After the cyclic subgroup is conjugated into `K ∩ M`, the standard
involution-pair description for a nonidentity element of `K` puts the
conjugated outside involution in `H = C_G(t)`. -/
private theorem
    selected_centralizer_inverting_involution_commutes_with_normalizer_involution
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x y m : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hyI : IsInvolution y)
    (hyM : y ∉ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hmM : m ∈ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hmne : m ≠ 1)
    (hyinv : y * m * y⁻¹ = m⁻¹) :
    ∃ u : G,
      u ∈ Subgroup.normalizer
          (Subgroup.centralizer ({x} : Set G) : Set G) ∧
        IsInvolution u ∧
        y ∈ Subgroup.centralizer ({u} : Set G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have hyy : y * y = 1 := by
    simpa [pow_two] using hyI.2
  have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hmMg : m ∈ M.conjBy y := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨m⁻¹, M.inv_mem hmM, ?_⟩
    have hc := congrArg (fun z : G => z⁻¹) hyinv
    simpa [MulAut.conj_apply, mul_inv_rev, mul_assoc] using hc
  have hJleMg : Subgroup.zpowers m ≤ M.conjBy y :=
    Subgroup.zpowers_le.mpr hmMg
  have hFJ : Disjoint F (Subgroup.zpowers m) :=
    (selected_centralizer_disjoint_conj_normalizer
      hxne hFHall hFTI y hyM).mono_right hJleMg
  obtain ⟨f, hfF, hfmA⟩ :=
    selected_centralizer_zpowers_conjugate_into_inf_K
      h hxC hxne hFcomm hFodd hFinv hFHall hmM hFJ
  let a : G := f * m * f⁻¹
  let w : G := f * y * f⁻¹
  have hfM : f ∈ M := Subgroup.le_normalizer hfF
  have haK : a ∈ h.K := hfmA.1
  have haM : a ∈ M := hfmA.2
  have hane : a ≠ 1 := by
    intro haone
    apply hmne
    have hc := congrArg (fun z : G => f⁻¹ * z * f) haone
    simpa [a, mul_assoc] using hc
  have hwI : IsInvolution w := by
    simpa [w, GorensteinWalter.IsInvolution,
      BenderSuzuki.PFAppendixIII.IsInvolution,
      BenderSuzuki.PFAppendixIII.rightConjugateElem] using
      (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
        (x := y) (g := f⁻¹) hyI)
  have hwM : w ∉ M := by
    intro hwM
    apply hyM
    have hyEq : y = f⁻¹ * w * f := by
      dsimp [w]
      group
    rw [hyEq]
    exact M.mul_mem (M.mul_mem (M.inv_mem hfM) hwM) hfM
  have hwinv : w * a * w⁻¹ = a⁻¹ := by
    have hc := congrArg (fun z : G => f * z * f⁻¹) hyinv
    simpa [w, a, mul_inv_rev, mul_assoc] using hc
  have hww : w * w = 1 := by
    simpa [pow_two] using hwI.2
  have hwInv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  let v : G := w * a
  have hvSq : v ^ 2 = 1 := by
    calc
      v ^ 2 = (w * a) * (w * a) := by rw [pow_two]
      _ = (w * a * w⁻¹) * a := by simp [hwInv, mul_assoc]
      _ = a⁻¹ * a := by rw [hwinv]
      _ = 1 := by simp
  have hvne : v ≠ 1 := by
    intro hvone
    apply hwM
    have hwa : w = a⁻¹ :=
      eq_inv_of_mul_eq_one_left (by simpa [v] using hvone)
    rw [hwa]
    exact M.inv_mem haM
  have hvI : IsInvolution v := ⟨hvne, hvSq⟩
  let p : bswPairFiber G a :=
    ⟨(⟨w, hwI⟩, ⟨v, hvI⟩), by
      change w * v = a
      dsimp [v]
      calc
        w * (w * a) = (w * w) * a := by group
        _ = a := by rw [hww]; simp⟩
  have hwH : w ∈ h.H :=
    (bswPair_first_mem_H_not_mem_K h haK hane p).1
  have hwt : Commute w h.t := by
    rw [h.H_eq_centralizer,
      Subgroup.mem_centralizer_singleton_iff] at hwH
    exact hwH
  let u : G := f⁻¹ * h.t * f
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have huM : u ∈ M :=
    M.mul_mem (M.mul_mem (M.inv_mem hfM) htM) hfM
  have huI : IsInvolution u := by
    simpa [u, GorensteinWalter.IsInvolution,
      BenderSuzuki.PFAppendixIII.IsInvolution,
      BenderSuzuki.PFAppendixIII.rightConjugateElem] using
      (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
        (x := h.t) (g := f) h.t_involution)
  refine ⟨u, huM, huI, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hc := congrArg (fun z : G => f⁻¹ * z * f) hwt.eq
  simpa [w, u, mul_assoc] using hc

/-- Every unoccupied non-base coset contains at most one involution. -/
private theorem selected_centralizer_unoccupied_coset_involutions_subsingleton
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (omega : selected_centralizer_unoccupied_nonbase_cosets
      (Subgroup.centralizer ({x} : Set G))) :
    Subsingleton
      (selected_centralizer_coset_involutions
        (Subgroup.centralizer ({x} : Set G)) omega.1) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let U := selected_centralizer_normalizer_involutions F
  constructor
  intro y z
  by_contra hyz
  have hyy : (y : G) * (y : G) = 1 := by
    simpa [pow_two] using y.property.1.2
  have hzz : (z : G) * (z : G) = 1 := by
    simpa [pow_two] using z.property.1.2
  have hyInv : (y : G)⁻¹ = (y : G) :=
    inv_eq_of_mul_eq_one_right hyy
  have hzInv : (z : G)⁻¹ = (z : G) :=
    inv_eq_of_mul_eq_one_right hzz
  let m : G := (y : G) * (z : G)
  have hyzCoset :
      (((y : G) : G ⧸ M)) = (((z : G) : G ⧸ M)) :=
    y.property.2.trans z.property.2.symm
  have hmM : m ∈ M := by
    rw [QuotientGroup.eq] at hyzCoset
    simpa [m, hyInv] using hyzCoset
  have hmne : m ≠ 1 := by
    intro hmone
    apply hyz
    apply Subtype.ext
    calc
      (y : G) = (z : G)⁻¹ :=
        eq_inv_of_mul_eq_one_left (by simpa [m] using hmone)
      _ = (z : G) := hzInv
  have hyM : (y : G) ∉ M := by
    intro hyM
    apply omega.property.1
    calc
      omega.1 = (((y : G) : G ⧸ M)) := y.property.2.symm
      _ = ((1 : G) : G ⧸ M) := by
        rw [QuotientGroup.eq]
        simpa using M.inv_mem hyM
  have hyinv : (y : G) * m * (y : G)⁻¹ = m⁻¹ := by
    calc
      (y : G) * m * (y : G)⁻¹ =
          ((y : G) * (y : G)) * (z : G) * (y : G) := by
        dsimp [m]
        rw [hyInv]
        group
      _ = (z : G) * (y : G) := by rw [hyy]; simp
      _ = m⁻¹ := by simp [m, mul_inv_rev, hyInv, hzInv]
  obtain ⟨u, huM, huI, hyC⟩ :=
    selected_centralizer_inverting_involution_commutes_with_normalizer_involution
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI
        y.property.1 hyM hmM hmne hyinv
  let uM : U := ⟨u, huM, huI⟩
  have hyu : Commute (y : G) u :=
    Subgroup.mem_centralizer_singleton_iff.mp hyC
  have huFixY :
      u • (((y : G) : G ⧸ M)) = (((y : G) : G ⧸ M)) := by
    change (((u * (y : G) : G)) : G ⧸ M) =
      (((y : G) : G ⧸ M))
    rw [QuotientGroup.eq]
    have hcalc : (u * (y : G))⁻¹ * (y : G) = u⁻¹ := by
      calc
        (u * (y : G))⁻¹ * (y : G) =
            (y : G)⁻¹ * u⁻¹ * (y : G) := by rw [mul_inv_rev]
        _ = (y : G)⁻¹ * (u⁻¹ * (y : G)) := by rw [mul_assoc]
        _ = (y : G)⁻¹ * ((y : G) * u⁻¹) := by
          rw [hyu.inv_right.eq.symm]
        _ = u⁻¹ := by simp
    rw [hcalc]
    exact M.inv_mem huM
  have huFixOmega : u • omega.1 = omega.1 := by
    calc
      u • omega.1 = u • (((y : G) : G ⧸ M)) := by rw [y.property.2]
      _ = (((y : G) : G ⧸ M)) := huFixY
      _ = omega.1 := y.property.2
  exact omega.property.2 uM huFixOmega

/-- The number of involutions in unoccupied non-base cosets is at most the
number of those cosets. -/
private theorem selected_centralizer_unoccupied_involutions_card_le_cosets
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    Nat.card (selected_centralizer_unoccupied_nonbase_involutions F) ≤
      Nat.card (selected_centralizer_unoccupied_nonbase_cosets F) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let InvExtra := selected_centralizer_unoccupied_nonbase_involutions F
  let Extra := selected_centralizer_unoccupied_nonbase_cosets F
  let toFun : InvExtra → Extra := fun y =>
    ⟨((y : G) : G ⧸ M), y.property.2.1, y.property.2.2⟩
  apply Nat.card_le_card_of_injective toFun
  intro y z hyz
  have hcoset :
      (((y : G) : G ⧸ M)) = (((z : G) : G ⧸ M)) :=
    congrArg Subtype.val hyz
  let omega : Extra := toFun y
  let y' : selected_centralizer_coset_involutions F omega.1 :=
    ⟨(y : G), y.property.1, rfl⟩
  let z' : selected_centralizer_coset_involutions F omega.1 :=
    ⟨(z : G), z.property.1, hcoset.symm⟩
  let : Subsingleton (selected_centralizer_coset_involutions F omega.1) :=
    selected_centralizer_unoccupied_coset_involutions_subsingleton
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI omega
  apply Subtype.ext
  exact congrArg
    (fun q : selected_centralizer_coset_involutions F omega.1 => (q : G))
    (Subsingleton.elim y' z')

/-- Division-free form of the second half of Bender 3.2.  If `j` is the
number of involutions in unoccupied non-base cosets and `e` is the number of
such cosets, then `j ≤ e` and
`|G:H| = |F|(|K|+1) + j`. -/
private theorem selected_centralizer_involution_count_bound
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    let e := Nat.card (selected_centralizer_unoccupied_nonbase_cosets F)
    ∃ j : ℕ,
      j ≤ e ∧
        h.H.index = Nat.card F * (Nat.card h.K + 1) + j := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Occupied := selected_centralizer_occupied_nonbase_involutions F
  let Unoccupied := selected_centralizer_unoccupied_nonbase_involutions F
  let Extra := selected_centralizer_unoccupied_nonbase_cosets F
  have htotal : Nat.card {y : G // IsInvolution y} = h.H.index := by
    calc
      Nat.card {y : G // IsInvolution y} =
          Nat.card (bswInvolutions G) := by rfl
      _ = (bswInvolutions G).ncard := Nat.card_coe_set_eq _
      _ = h.H.index := bswInvolutions_ncard_eq_index_H h
  have hpartition :
      Nat.card {y : G // IsInvolution y} =
        Nat.card U + (Nat.card Occupied + Nat.card Unoccupied) := by
    calc
      Nat.card {y : G // IsInvolution y} =
          Nat.card (U ⊕ (Occupied ⊕ Unoccupied)) :=
        Nat.card_congr (selected_centralizer_involutions_equiv_partition F)
      _ = Nat.card U + (Nat.card Occupied + Nat.card Unoccupied) := by
        rw [Nat.card_sum, Nat.card_sum]
  have hU : Nat.card U = Nat.card F :=
    selected_centralizer_involutions_normalizer_card
      h hxC hxne hFinv
  have hOccupied : Nat.card Occupied = Nat.card F * Nat.card h.K :=
    selected_centralizer_occupied_nonbase_involutions_card
      h hxC hxne hFodd hFinv hFHall hFTI
  have hUnoccupied : Nat.card Unoccupied ≤ Nat.card Extra :=
    selected_centralizer_unoccupied_involutions_card_le_cosets
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI
  refine ⟨Nat.card Unoccupied, hUnoccupied, ?_⟩
  calc
    h.H.index = Nat.card {y : G // IsInvolution y} := htotal.symm
    _ = Nat.card U + (Nat.card Occupied + Nat.card Unoccupied) := hpartition
    _ = Nat.card F * (Nat.card h.K + 1) + Nat.card Unoccupied := by
      rw [hU, hOccupied, Nat.mul_add, Nat.mul_one]
      omega

/-- The selected centralizer acts freely on every non-base coset of its
normalizer. -/
private theorem selected_centralizer_nonbase_coset_smul_injective
    {G : Type u} [Group G] [Finite G] {x : G}
    (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (omega : G ⧸ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (homegaNe : omega ≠
      ((1 : G) : G ⧸ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))) :
    Function.Injective (fun a : Subgroup.centralizer ({x} : Set G) =>
      (a : G) • omega) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let g : G := omega.out
  have hgM : g ∉ M := by
    intro hgM
    apply homegaNe
    calc
      omega = (g : G ⧸ M) := (QuotientGroup.out_eq' omega).symm
      _ = ((1 : G) : G ⧸ M) := by
        rw [QuotientGroup.eq]
        simpa using M.inv_mem hgM
  intro a b hab
  let c : G := (b : G)⁻¹ * (a : G)
  have hcF : c ∈ F := F.mul_mem (F.inv_mem b.property) a.property
  have hab' : (a : G) • omega = (b : G) • omega := hab
  have hcFix : c • omega = omega := by
    calc
      c • omega = (b : G)⁻¹ • ((a : G) • omega) := by
        simp [c, mul_smul]
      _ = (b : G)⁻¹ • ((b : G) • omega) := by rw [hab']
      _ = omega := inv_smul_smul (b : G) omega
  have hcFixOut : c • ((g : G) : G ⧸ M) = ((g : G) : G ⧸ M) := by
    simpa only [g, M, F, QuotientGroup.out_eq'] using hcFix
  have hconjInvM : g⁻¹ * c⁻¹ * g ∈ M := by
    change ((((c * g : G)) : G ⧸ M) = (g : G ⧸ M)) at hcFixOut
    rw [QuotientGroup.eq] at hcFixOut
    simpa [mul_assoc] using hcFixOut
  have hconjM : g⁻¹ * c * g ∈ M := by
    have hinv := M.inv_mem hconjInvM
    simpa [mul_inv_rev, mul_assoc] using hinv
  have hcMg : c ∈ M.conjBy g := by
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * c * g, hconjM, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  have hcOne : c = 1 :=
    Subgroup.disjoint_def.mp
      (selected_centralizer_disjoint_conj_normalizer
        hxne hFHall hFTI g hgM) hcF hcMg
  apply Subtype.ext
  have hc := congrArg (fun z : G => (b : G) * z) hcOne
  simpa [c, mul_assoc] using hc

/-- If an unoccupied coset exists, its free `F`-orbit embeds `F` into the
set of unoccupied cosets. -/
private theorem selected_centralizer_card_le_unoccupied_of_nonempty
    {G : Type u} [Group G] [Finite G] {x : G}
    (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hNonempty : Nonempty
      (selected_centralizer_unoccupied_nonbase_cosets
        (Subgroup.centralizer ({x} : Set G)))) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) ≤
      Nat.card (selected_centralizer_unoccupied_nonbase_cosets
        (Subgroup.centralizer ({x} : Set G))) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let Omega := G ⧸ M
  let base : Omega := ((1 : G) : G ⧸ M)
  let U := selected_centralizer_normalizer_involutions F
  let Extra := selected_centralizer_unoccupied_nonbase_cosets F
  let omega : Extra := Classical.choice hNonempty
  have base_fix (m : G) (hmM : m ∈ M) : m • base = base := by
    dsimp [base, Omega]
    change ((((m * 1 : G)) : G ⧸ M) = ((1 : G) : G ⧸ M))
    rw [QuotientGroup.eq]
    simpa using M.inv_mem hmM
  let orbitMap : F → Extra := fun a =>
    ⟨(a : G) • omega.1, by
      constructor
      · intro haBase
        apply omega.2.1
        calc
          omega.1 = (a : G)⁻¹ • ((a : G) • omega.1) :=
            (inv_smul_smul (a : G) omega.1).symm
          _ = (a : G)⁻¹ • base := by rw [haBase]
          _ = base := base_fix (a : G)⁻¹
            (M.inv_mem (Subgroup.le_normalizer a.property))
      · intro u huFix
        let v : G := (a : G)⁻¹ * (u : G) * (a : G)
        have hvM : v ∈ M :=
          M.mul_mem
            (M.mul_mem
              (M.inv_mem (Subgroup.le_normalizer a.property))
              u.property.1)
            (Subgroup.le_normalizer a.property)
        have hvI : IsInvolution v := by
          simpa [v, GorensteinWalter.IsInvolution,
            BenderSuzuki.PFAppendixIII.IsInvolution,
            BenderSuzuki.PFAppendixIII.rightConjugateElem] using
            (BenderSuzuki.PFAppendixIII.isInvolution_rightConjugateElem
              (x := (u : G)) (g := (a : G)) u.property.2)
        have hvFix : v • omega.1 = omega.1 := by
          calc
            v • omega.1 = (a : G)⁻¹ •
                ((u : G) • ((a : G) • omega.1)) := by
              simp [v, mul_smul, mul_assoc]
            _ = (a : G)⁻¹ • ((a : G) • omega.1) := by rw [huFix]
            _ = omega.1 := inv_smul_smul (a : G) omega.1
        exact omega.2.2 ⟨v, hvM, hvI⟩ hvFix⟩
  apply Nat.card_le_card_of_injective orbitMap
  intro a b hab
  apply selected_centralizer_nonbase_coset_smul_injective
    hxne hFHall hFTI omega.1 omega.2.1
  exact congrArg Subtype.val hab

/-- The normalizer cosets split into the base coset, the occupied non-base
cosets, and the unoccupied non-base cosets. -/
private theorem selected_centralizer_cosets_card_partition
    {G : Type u} [Group G] [Finite G] (F : Subgroup G) :
    Nat.card (G ⧸ Subgroup.normalizer (F : Set G)) =
      1 + Nat.card (selected_centralizer_occupied_nonbase_cosets F) +
        Nat.card (selected_centralizer_unoccupied_nonbase_cosets F) := by
  classical
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let Omega := G ⧸ M
  let base : Omega := ((1 : G) : G ⧸ M)
  let U := selected_centralizer_normalizer_involutions F
  let Nonbase := {omega : Omega // omega ≠ base}
  let OccupiedPred : Nonbase → Prop := fun omega =>
    ∃ u : U, (u : G) • omega.1 = omega.1
  let Occupied := {omega : Nonbase // OccupiedPred omega}
  let Unoccupied := {omega : Nonbase // ¬ OccupiedPred omega}
  let eOccupied : Occupied ≃
      selected_centralizer_occupied_nonbase_cosets F :=
    { toFun := fun omega =>
        ⟨omega.1.1, omega.1.2, omega.2⟩
      invFun := fun omega =>
        ⟨⟨omega.1, omega.2.1⟩, omega.2.2⟩
      left_inv := by intro omega; rfl
      right_inv := by intro omega; rfl }
  let eUnoccupied : Unoccupied ≃
      selected_centralizer_unoccupied_nonbase_cosets F :=
    { toFun := fun omega =>
        ⟨omega.1.1, omega.1.2, by
          intro u huFix
          exact omega.2 ⟨u, huFix⟩⟩
      invFun := fun omega =>
        ⟨⟨omega.1, omega.2.1⟩, by
          rintro ⟨u, huFix⟩
          exact omega.2.2 u huFix⟩
      left_inv := by intro omega; rfl
      right_inv := by intro omega; rfl }
  have hbaseCard : Nat.card {omega : Omega // omega = base} = 1 := by
    simp
  have hfirst : Nat.card Omega =
      Nat.card {omega : Omega // omega = base} + Nat.card Nonbase := by
    calc
      Nat.card Omega = Nat.card
          ({omega : Omega // omega = base} ⊕
            {omega : Omega // ¬ omega = base}) :=
        (Nat.card_congr (Equiv.sumCompl (fun omega : Omega => omega = base))).symm
      _ = Nat.card {omega : Omega // omega = base} +
          Nat.card {omega : Omega // ¬ omega = base} := Nat.card_sum
      _ = Nat.card {omega : Omega // omega = base} + Nat.card Nonbase := by
        rfl
  have hsecond : Nat.card Nonbase = Nat.card Occupied + Nat.card Unoccupied := by
    calc
      Nat.card Nonbase = Nat.card (Occupied ⊕ Unoccupied) :=
        (Nat.card_congr
          (Equiv.sumCompl (fun omega : Nonbase => OccupiedPred omega))).symm
      _ = Nat.card Occupied + Nat.card Unoccupied := Nat.card_sum
  calc
    Nat.card (G ⧸ Subgroup.normalizer (F : Set G)) = Nat.card Omega := rfl
    _ = Nat.card {omega : Omega // omega = base} + Nat.card Nonbase := hfirst
    _ = 1 + (Nat.card Occupied + Nat.card Unoccupied) := by
      rw [hbaseCard, hsecond]
    _ = 1 + Nat.card (selected_centralizer_occupied_nonbase_cosets F) +
        Nat.card (selected_centralizer_unoccupied_nonbase_cosets F) := by
      rw [Nat.card_congr eOccupied, Nat.card_congr eUnoccupied]
      omega

/-- On non-base cosets, projecting an involution/fixed-coset incidence to
the coset is an equivalence, because the fixing involution is unique. -/
private noncomputable def
    selected_centralizer_nonbase_fixed_incidences_equiv_occupied
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    selected_centralizer_nonbase_fixed_incidences F ≃
      selected_centralizer_occupied_nonbase_cosets F := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Omega := G ⧸ Subgroup.normalizer (F : Set G)
  let toFun : selected_centralizer_nonbase_fixed_incidences F →
      selected_centralizer_occupied_nonbase_cosets F := fun p =>
    ⟨p.1.2, p.2.2, ⟨p.1.1, p.2.1⟩⟩
  apply Equiv.ofBijective toFun
  constructor
  · intro p q hpq
    have homega : p.1.2 = q.1.2 := congrArg Subtype.val hpq
    have hu : (p.1.1 : G) = (q.1.1 : G) := by
      apply selected_centralizer_fixed_coset_unique_involution
        h hxC hxne hFHall hFTI
          p.1.1.property.1 p.1.1.property.2
          q.1.1.property.1 q.1.1.property.2 p.1.2 p.2.2 p.2.1
      simpa [homega] using q.2.1
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hu
    · exact homega
  · intro omega
    obtain ⟨u, huFix⟩ := omega.2.2
    refine ⟨⟨(u, omega.1), huFix, omega.2.1⟩, ?_⟩
    rfl

/-- The occupied non-base cosets have cardinality `|F| (r - 1)`, where
`r |K ∩ M| = 2|K|` is the common fixed-coset count of an involution in
`M`. -/
private theorem selected_centralizer_occupied_nonbase_cosets_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    ∃ r : ℕ,
      r * Nat.card (h.K ⊓ M : Subgroup G) = 2 * Nat.card h.K ∧
      Nat.card (selected_centralizer_occupied_nonbase_cosets F) =
        Nat.card F * (r - 1) := by
  classical
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let U := selected_centralizer_normalizer_involutions F
  let Omega := G ⧸ M
  let base : Omega := ((1 : G) : G ⧸ M)
  let Fixed (u : U) := {omega : Omega // (u : G) • omega = omega}
  let NonbaseFixed (u : U) :=
    {omega : Fixed u // omega.1 ≠ base}
  let Inc := selected_centralizer_nonbase_fixed_incidences F
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  let r : ℕ := Nat.card {omega : Omega // h.t • omega = omega}
  have hrMul : r * Nat.card (h.K ⊓ M : Subgroup G) =
      2 * Nat.card h.K := by
    exact selected_centralizer_fixed_cosets_card_mul_inf_K_card
      h hxC hxne hFodd hFinv htM h.t_involution
  refine ⟨r, hrMul, ?_⟩
  have hfixedCard (u : U) : Nat.card (Fixed u) = r := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α := (h.K ⊓ M : Subgroup G)))
    calc
      Nat.card (Fixed u) * Nat.card (h.K ⊓ M : Subgroup G) =
          2 * Nat.card h.K :=
        selected_centralizer_fixed_cosets_card_mul_inf_K_card
          h hxC hxne hFodd hFinv u.property.1 u.property.2
      _ = r * Nat.card (h.K ⊓ M : Subgroup G) := hrMul.symm
  have hbaseFix (u : U) : (u : G) • base = base := by
    dsimp [base, Omega]
    change ((((u : G) * 1 : G) : G ⧸ M) = ((1 : G) : G ⧸ M))
    rw [QuotientGroup.eq]
    simpa using M.inv_mem u.property.1
  have houtCard (u : U) : Nat.card (NonbaseFixed u) = r - 1 := by
    let baseFixed : Fixed u := ⟨base, hbaseFix u⟩
    have hcomp : Nat.card {omega : Fixed u // omega ≠ baseFixed} =
        Nat.card (Fixed u) - 1 := by
      let : Fintype (Fixed u) := Fintype.ofFinite (Fixed u)
      simpa [Nat.card_eq_fintype_card] using
        (Fintype.card_subtype_compl
          (fun omega : Fixed u => omega = baseFixed))
    let e : {omega : Fixed u // omega ≠ baseFixed} ≃ NonbaseFixed u :=
      Equiv.subtypeEquiv (Equiv.refl (Fixed u)) (by
        intro omega
        simp only [Equiv.refl_apply, ne_eq]
        constructor
        · intro hne hval
          apply hne
          exact Subtype.ext hval
        · intro hne heq
          exact hne (congrArg Subtype.val heq))
    calc
      Nat.card (NonbaseFixed u) =
          Nat.card {omega : Fixed u // omega ≠ baseFixed} :=
        (Nat.card_congr e).symm
      _ = Nat.card (Fixed u) - 1 := hcomp
      _ = r - 1 := by rw [hfixedCard u]
  let eInc : Inc ≃ Σ u : U, NonbaseFixed u :=
    { toFun := fun p =>
        ⟨p.1.1, ⟨⟨p.1.2, p.2.1⟩, p.2.2⟩⟩
      invFun := fun p =>
        ⟨(p.1, p.2.1.1), p.2.1.2, p.2.2⟩
      left_inv := by
        intro p
        rfl
      right_inv := by
        intro p
        rfl }
  let : Fintype U := Fintype.ofFinite U
  have hIncCard : Nat.card Inc = Nat.card U * (r - 1) := by
    calc
      Nat.card Inc = Nat.card (Σ u : U, NonbaseFixed u) :=
        Nat.card_congr eInc
      _ = ∑ u : U, Nat.card (NonbaseFixed u) := Nat.card_sigma
      _ = ∑ _u : U, (r - 1) := by
        apply Finset.sum_congr rfl
        intro u _hu
        exact houtCard u
      _ = Nat.card U * (r - 1) := by
        simp [Nat.card_eq_fintype_card]
  calc
    Nat.card (selected_centralizer_occupied_nonbase_cosets F) =
        Nat.card Inc :=
      (Nat.card_congr
        (selected_centralizer_nonbase_fixed_incidences_equiv_occupied
          h hxC hxne hFHall hFTI)).symm
    _ = Nat.card U * (r - 1) := hIncCard
    _ = Nat.card F * (r - 1) := by
      rw [selected_centralizer_involutions_normalizer_card
        h hxC hxne hFinv]

/-- Division-free form of the first half of Bender 3.2.  If `e` is the
number of unoccupied non-base cosets, then
`|G:M| = 1 + |F|(r-1) + e`, with `r |K∩M| = 2|K|`; either `e = 0` or
`|F| ≤ e`. -/
private theorem selected_centralizer_coset_count_dichotomy
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    let e := Nat.card (selected_centralizer_unoccupied_nonbase_cosets F)
    ∃ r : ℕ,
      0 < r ∧
      r * Nat.card (h.K ⊓ M : Subgroup G) = 2 * Nat.card h.K ∧
      M.index = 1 + Nat.card F * (r - 1) + e ∧
      (e = 0 ∨ Nat.card F ≤ e) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let Extra := selected_centralizer_unoccupied_nonbase_cosets F
  obtain ⟨r, hrMul, hOccupied⟩ :=
    selected_centralizer_occupied_nonbase_cosets_card
      h hxC hxne hFodd hFinv hFHall hFTI
  let e : ℕ := Nat.card Extra
  have hrPos : 0 < r := by
    by_contra hr
    have hr0 : r = 0 := by omega
    rw [hr0] at hrMul
    have hkPos : 0 < Nat.card h.K := Nat.card_pos
    omega
  have hindex : M.index = 1 + Nat.card F * (r - 1) + e := by
    rw [Subgroup.index_eq_card]
    calc
      Nat.card (G ⧸ M) =
          1 + Nat.card (selected_centralizer_occupied_nonbase_cosets F) +
            Nat.card Extra := selected_centralizer_cosets_card_partition F
      _ = 1 + Nat.card F * (r - 1) + e := by
        rw [hOccupied]
  refine ⟨r, hrPos, hrMul, hindex, ?_⟩
  by_cases he : e = 0
  · exact Or.inl he
  · right
    apply selected_centralizer_card_le_unoccupied_of_nonempty
      hxne hFHall hFTI
    exact (Nat.card_pos_iff.mp (Nat.pos_of_ne_zero he)).1

/-- A finite group acting fixed-point-freely on the nonidentity elements of
another finite group has order dividing the number of those elements. -/
private theorem natCard_dvd_card_sub_one_of_fixedPointFree_action
    {A N : Type*} [Group A] [Finite A] [Group N] [Finite N]
    [MulDistribMulAction A N]
    (hfree : ∀ a : A, a ≠ 1 → ∀ x : N, a • x = x → x = 1) :
    Nat.card A ∣ Nat.card N - 1 := by
  classical
  let X := {x : N // x ≠ 1}
  let : MulAction A X :=
    { smul := fun a x => ⟨a • (x : N), by
        intro h
        apply x.2
        have h' := congrArg (fun y : N => a⁻¹ • y) h
        simpa using h'⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change (1 : A) • (x : N) = (x : N)
        simp
      mul_smul := by
        intro a b x
        apply Subtype.ext
        change (a * b) • (x : N) = a • (b • (x : N))
        rw [mul_smul] }
  have hstab : ∀ x : X, MulAction.stabilizer A x = ⊥ := by
    intro x
    rw [eq_bot_iff]
    intro a ha
    have hax : a • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro haeq
      apply ha1
      simpa [haeq]
    exact x.2 (hfree a hane (x : N) (congrArg Subtype.val hax))
  let Omega := Quotient (MulAction.orbitRel A X)
  have hcard :=
    Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hXcard : Nat.card X = Nat.card N - 1 := by
    let : Fintype N := Fintype.ofFinite N
    let : Fintype X := Fintype.ofFinite X
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {x : N // x ≠ 1} = Fintype.card N - 1
    simp
  refine ⟨Nat.card Omega, ?_⟩
  rw [← hXcard]
  simpa [Nat.card_prod, mul_comm, Omega, X] using hcard

/-- The complement `K ∩ N_G(F)` acts fixed-point-freely on `F`, so its
order divides `|F|-1`, as used in Bender 3.4. -/
private theorem selected_centralizer_inf_K_card_dvd_card_sub_one
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFCent : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer ({x} : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card (h.K ⊓ M : Subgroup G) ∣ Nat.card F - 1 := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  have hAnorm : A ≤ Subgroup.normalizer (F : Set G) := inf_le_right
  let : MulDistribMulAction A F :=
    MulDistribMulAction.compHom F (Subgroup.inclusion hAnorm)
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hAH : A ≤ h.H := inf_le_left.trans hKleH
  have hFH : Disjoint F h.H :=
    selected_centralizer_disjoint_H h hxC hxne
  apply natCard_dvd_card_sub_one_of_fixedPointFree_action
  intro a hane z hfix
  by_contra hzne
  let ag : G := a
  have hconj : ag * (z : G) * ag⁻¹ = (z : G) := by
    have hfix' := congrArg Subtype.val hfix
    change (a : G) * (z : G) * (a : G)⁻¹ = (z : G) at hfix'
    simpa [ag] using hfix'
  have hacent :
      ag ∈ Subgroup.centralizer ({(z : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have haF : ag ∈ F := by
    have hcentEq := hFCent (z : G) z.property (by simpa using hzne)
    change ag ∈ Subgroup.centralizer ({x} : Set G)
    rw [← hcentEq]
    exact hacent
  have haH : ag ∈ h.H := by simpa [ag] using hAH a.property
  have habot : ag ∈ (⊥ : Subgroup G) :=
    hFH.le_bot ⟨haF, haH⟩
  apply hane
  apply Subtype.ext
  simpa [ag] using habot

/-- The distinguished involution belongs to `K ∩ N_G(F)`, so that
intersection has order at least two. -/
private theorem selected_centralizer_two_le_card_inf_K
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hFinv : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) →
        h.t * z * h.t⁻¹ = z⁻¹) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    2 ≤ Nat.card (h.K ⊓ M : Subgroup G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  let tA : A := ⟨h.t, h.t_mem_K, htM⟩
  have htAne : tA ≠ 1 := by
    intro htAone
    exact h.t_involution.1 (congrArg Subtype.val htAone)
  have htAsq : tA ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htAorder : orderOf tA = 2 :=
    orderOf_eq_prime htAsq htAne
  have hdvd : 2 ∣ Nat.card A := by
    rw [← htAorder]
    exact orderOf_dvd_natCard tA
  exact Nat.le_of_dvd Nat.card_pos hdvd

/-- The complete division-free counting data of Bender 3.2. -/
private theorem selected_centralizer_bender_3_2_count_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    let e := Nat.card (selected_centralizer_unoccupied_nonbase_cosets F)
    ∃ r j : ℕ,
      0 < r ∧
      r * Nat.card (h.K ⊓ M : Subgroup G) = 2 * Nat.card h.K ∧
      M.index = 1 + Nat.card F * (r - 1) + e ∧
      (e = 0 ∨ Nat.card F ≤ e) ∧
      j ≤ e ∧
      h.H.index = Nat.card F * (Nat.card h.K + 1) + j := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let e := Nat.card (selected_centralizer_unoccupied_nonbase_cosets F)
  obtain ⟨r, hrPos, hrMul, hMindex, he⟩ :=
    selected_centralizer_coset_count_dichotomy
      h hxC hxne hFodd hFinv hFHall hFTI
  obtain ⟨j, hjle, hHindex⟩ :=
    selected_centralizer_involution_count_bound
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI
  exact ⟨r, j, hrPos, hrMul, hMindex, he, hjle, hHindex⟩

/-- An even `k` makes `k+1` coprime to `2k`. -/
private theorem bender_coprime_succ_two_mul
    (k : ℕ) (hk : 4 < k) (hkeven : Even k) :
    Nat.Coprime (k + 1) (2 * k) := by
  obtain ⟨c, hc⟩ := hkeven
  have hodd : Odd (k + 1) := ⟨c, by omega⟩
  have hcop2 : Nat.Coprime 2 (k + 1) :=
    Nat.coprime_two_left.mpr hodd
  have hcopPred : Nat.Coprime (k - 1) (k + 1) := by
    apply (Nat.coprime_self_sub_left (by omega : k - 1 ≤ k + 1)).mp
    rw [show k + 1 - (k - 1) = 2 by omega]
    exact hcop2
  have hcop : Nat.Coprime (2 * k) (k + 1) := by
    apply (Nat.coprime_sub_self_left (by omega : k + 1 ≤ 2 * k)).mp
    rw [show 2 * k - (k + 1) = k - 1 by omega]
    exact hcopPred
  exact hcop.symm

/-- In the minus order case, `k+1` cannot divide the involution index. -/
private theorem bender_minus_index_not_dvd_succ
    (k : ℕ) (hk : 4 < k) (hkeven : Even k) :
    ¬ k + 1 ∣ (2 * k - 1) * (k - 1) := by
  intro hdvdR
  have hid : (2 * k - 1) * (k - 1) =
      (2 * k - 5) * (k + 1) + 6 := by
    obtain ⟨a, rfl⟩ : ∃ a, k = a + 5 := ⟨k - 5, by omega⟩
    have h1 : 2 * (a + 5) - 1 = 2 * a + 9 := by omega
    have h2 : a + 5 - 1 = a + 4 := by omega
    have h3 : 2 * (a + 5) - 5 = 2 * a + 5 := by omega
    rw [h1, h2, h3]
    ring
  rw [hid] at hdvdR
  have hterm : k + 1 ∣ (2 * k - 5) * (k + 1) :=
    Nat.dvd_mul_left (k + 1) (2 * k - 5)
  have hdvd6 : k + 1 ∣ 6 :=
    (Nat.dvd_add_iff_right hterm).mpr hdvdR
  have hle : k + 1 ≤ 6 := Nat.le_of_dvd (by omega) hdvd6
  obtain ⟨c, hc⟩ := hkeven
  omega

/-- Division-free form of the strict inequality in the second half of
Bender 3.4.  If `|M|>|H|`, the two count inequalities force `f<k+2`. -/
private theorem bender_positive_e_high_card_lt
    (k f n r e j I L : ℕ)
    (hk : 4 < k) (hrPos : 0 < r) (hn2 : 2 ≤ n)
    (hrn : r * n = 2 * k)
    (hM : L = 1 + f * (r - 1) + e)
    (hI : I = f * (k + 1) + j)
    (hglobal : L * (f * n) = (2 * k) * I)
    (he : f ≤ e) (hj : j ≤ e)
    (hhigh : 2 * k < n * f) :
    f < k + 2 := by
  have hfPos : 0 < f := by nlinarith
  have hrf : r < f := by
    rw [← hrn] at hhigh
    nlinarith
  have hcancel : L * f = r * I := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n)
    calc
      (L * f) * n = L * (f * n) := by ring
      _ = (2 * k) * I := hglobal
      _ = (r * I) * n := by rw [← hrn]; ring
  have hrone : r - 1 + 1 = r := by omega
  have hfr : f * (r - 1) + f = f * r := by
    calc
      f * (r - 1) + f = f * (r - 1) + f * 1 := by simp
      _ = f * ((r - 1) + 1) := by rw [Nat.mul_add]
      _ = f * r := by rw [hrone]
  have hmain : f * (f - r) < I - L := by
    have hIL : L < I := by
      have hIPos : 0 < I := by rw [hI]; positivity
      have : L * f < I * f := by
        calc
          L * f = r * I := hcancel
          _ < f * I := Nat.mul_lt_mul_of_pos_right hrf hIPos
          _ = I * f := by ring
      exact Nat.lt_of_mul_lt_mul_right this
    have heq : r * (I - L) = L * (f - r) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib]
      rw [← hcancel, mul_comm r L]
    have hL : f * r < L := by
      rw [hM]
      omega
    have hprod : r * (f * (f - r)) < r * (I - L) := by
      rw [heq]
      calc
        r * (f * (f - r)) = (f * r) * (f - r) := by ring
        _ < L * (f - r) :=
          (Nat.mul_lt_mul_right (by omega : 0 < f - r)).mpr hL
    exact Nat.lt_of_mul_lt_mul_left hprod
  have hupper : I - L < f * (k + 2 - r) := by
    have hrle : r ≤ k + 2 := by
      nlinarith [hrn]
    rw [hI, hM]
    have hform :
        f * (k + 2 - r) + f * (r - 1) = f * (k + 1) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  have hmul : f * (f - r) < f * (k + 2 - r) :=
    lt_trans hmain hupper
  have hsub : f - r < k + 2 - r :=
    Nat.lt_of_mul_lt_mul_left hmul
  omega

/-- Arithmetic core of Bender 3.4.  In the branch with additional cosets,
the selected centralizer has order `k-1` and the internal complement has
order two. -/
private theorem bender_3_4_cards
    (k f n r e j I L : ℕ)
    (hk : 4 < k) (hkeven : Even k) (hfodd : Odd f)
    (hn2 : 2 ≤ n) (hrPos : 0 < r)
    (hrn : r * n = 2 * k)
    (hM : L = 1 + f * (r - 1) + e)
    (hI : I = f * (k + 1) + j)
    (hglobal : L * (f * n) = (2 * k) * I)
    (he : f ≤ e) (hj : j ≤ e)
    (hcases :
      (I = (2 * k + 1) * (k + 1) ∧ k + 3 ≤ f) ∨
        (I = (2 * k - 1) * (k - 1) ∧ k - 1 ≤ f))
    (hnDvdK : n ∣ k) (hnDvdFsub : n ∣ f - 1) :
    f = k - 1 ∧ n = 2 := by
  have hfPos : 0 < f := by
    obtain ⟨a, ha⟩ := hfodd
    omega
  have hcancel : L * f = r * I := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n)
    calc
      (L * f) * n = L * (f * n) := by ring
      _ = (2 * k) * I := hglobal
      _ = (r * I) * n := by rw [← hrn]; ring
  by_cases hlow : n * f ≤ 2 * k
  · have hfle : f ≤ k := by nlinarith
    have hf : f = k - 1 := by
      rcases hcases with hplus | hminus
      · omega
      · obtain ⟨a, ha⟩ := hkeven
        obtain ⟨b, hb⟩ := hfodd
        omega
    refine ⟨hf, ?_⟩
    rw [hf] at hlow
    let a := k - 1
    have hka : k = a + 1 := by dsimp [a]; omega
    rw [hka] at hlow
    rw [show a + 1 - 1 = a by omega] at hlow
    have ha : 3 < a := by dsimp [a]; omega
    nlinarith
  · have hhigh : 2 * k < n * f := by omega
    have hflt : f < k + 2 :=
      bender_positive_e_high_card_lt k f n r e j I L hk hrPos hn2
        hrn hM hI hglobal he hj hhigh
    rcases hcases with hplus | hminus
    · omega
    · have hfCases : f = k - 1 ∨ f = k + 1 := by
        obtain ⟨a, ha⟩ := hkeven
        obtain ⟨b, hb⟩ := hfodd
        omega
      rcases hfCases with hf | hf
      · refine ⟨hf, ?_⟩
        have hnDvdPredTwo : n ∣ k - 2 := by
          rw [hf] at hnDvdFsub
          rwa [show k - 1 - 1 = k - 2 by omega] at hnDvdFsub
        have hnDvdTwo : n ∣ 2 := by
          have hsub : n ∣ k - (k - 2) :=
            Nat.dvd_sub hnDvdK hnDvdPredTwo
          rwa [show k - (k - 2) = 2 by omega] at hsub
        have hnle : n ≤ 2 := Nat.le_of_dvd (by omega) hnDvdTwo
        omega
      · exfalso
        have hcop : Nat.Coprime f r := by
          rw [hf]
          exact (bender_coprime_succ_two_mul k hk hkeven).of_dvd_right
            ⟨n, hrn.symm⟩
        have hfDvdRI : f ∣ r * I := by
          refine ⟨L, ?_⟩
          simpa [mul_comm] using hcancel.symm
        have hfDvdI : f ∣ I := hcop.dvd_of_dvd_mul_left hfDvdRI
        rw [hf, hminus.1] at hfDvdI
        exact bender_minus_index_not_dvd_succ k hk hkeven hfDvdI

/-- Arithmetic core of Bender 3.3: when no additional cosets occur, the
selected centralizer has order `2k+1`. -/
private theorem bender_3_3_card_F
    (k f I : ℕ) (hk : 4 < k) (hkeven : Even k)
    (hcases :
      (I = (2 * k + 1) * (k + 1) ∧ k + 3 ≤ f) ∨
        (I = (2 * k - 1) * (k - 1) ∧ k - 1 ≤ f))
    (hI : I = f * (k + 1)) :
    f = 2 * k + 1 := by
  rcases hcases with hplus | hminus
  · apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < k + 1)
    calc
      f * (k + 1) = I := hI.symm
      _ = (2 * k + 1) * (k + 1) := hplus.1
  · exfalso
    have heq : f * (k + 1) = (2 * k - 1) * (k - 1) :=
      hI.symm.trans hminus.1
    have hdvdR : k + 1 ∣ (2 * k - 1) * (k - 1) := by
      refine ⟨f, ?_⟩
      calc
        (2 * k - 1) * (k - 1) = f * (k + 1) := heq.symm
        _ = (k + 1) * f := by rw [Nat.mul_comm]
    exact bender_minus_index_not_dvd_succ k hk hkeven hdvdR

/-- The remaining arithmetic core of Bender 3.3: the internal complement
has the full order `k`. -/
private theorem bender_3_3_internal_card
    (k f n r : ℕ) (hk : 0 < k) (hrPos : 0 < r)
    (hf : f = 2 * k + 1)
    (hr : r * n = 2 * k)
    (heq : (1 + f * (r - 1)) * n = 2 * k * (k + 1)) :
    n = k := by
  let s := r - 1
  have hrs : r = s + 1 := by
    dsimp [s]
    omega
  have hsn : s * n + n = 2 * k := by
    rw [hrs] at hr
    nlinarith
  have hmain : n + f * (s * n) = 2 * k * (k + 1) := by
    rw [hrs] at heq
    have hsimp : s + 1 - 1 = s := by omega
    rw [hsimp] at heq
    nlinarith
  rw [hf] at hmain
  nlinarith

/-- Group-theoretic form of Bender 3.4.  If an additional coset occurs,
then `|F|=k-1`, `|K ∩ N_G(F)|=2`, the selected normalizer has order
`2(k-1)`, and the ambient order is the minus case. -/
private theorem selected_centralizer_bender_3_4_card_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) →
        h.t * z * h.t⁻¹ = z⁻¹)
    (hFCent : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer ({x} : Set G))
    (hbound :
      (h.H.index =
            (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
          Nat.card h.K + 3 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))) ∨
        (h.H.index =
            (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
          Nat.card h.K - 1 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (hePos : 0 < Nat.card
      (selected_centralizer_unoccupied_nonbase_cosets
        (Subgroup.centralizer ({x} : Set G)))) :
    let F := Subgroup.centralizer ({x} : Set G)
    let M := Subgroup.normalizer (F : Set G)
    Nat.card F = Nat.card h.K - 1 ∧
      Nat.card (h.K ⊓ M : Subgroup G) = 2 ∧
      Nat.card M = 2 * (Nat.card h.K - 1) ∧
      h.H.index =
        (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  let k : ℕ := Nat.card h.K
  let f : ℕ := Nat.card F
  let n : ℕ := Nat.card A
  let e : ℕ := Nat.card
    (selected_centralizer_unoccupied_nonbase_cosets F)
  obtain ⟨r, j, hrPos, hrMul, hMindex, heCases, hjle, hHindex⟩ :=
    selected_centralizer_bender_3_2_count_data
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI
  have heLower : f ≤ e := by
    rcases heCases with he0 | hle
    · exfalso
      exact (Nat.ne_of_gt hePos) (by simpa [e, F] using he0)
    · simpa [f, e, F] using hle
  have hMcard : Nat.card M = f * n := by
    simpa [M, F, A, f, n] using
      selected_centralizer_normalizer_card h hxC hxne hFodd hFinv
  have hglobal : M.index * (f * n) = (2 * k) * h.H.index := by
    calc
      M.index * (f * n) = M.index * Nat.card M := by rw [hMcard]
      _ = Nat.card G := by simpa [mul_comm] using M.card_mul_index
      _ = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * h.H.index := by rw [h.card_H]
  have hn2 : 2 ≤ n := by
    simpa [n, A, M, F] using
      selected_centralizer_two_le_card_inf_K h hFinv
  have hnDvdK : n ∣ k := by
    simpa [n, k, A] using
      (Subgroup.card_dvd_of_le (H := A) (K := h.K) inf_le_left)
  have hnDvdFsub : n ∣ f - 1 := by
    simpa [n, f, A, M, F] using
      selected_centralizer_inf_K_card_dvd_card_sub_one
        h hxC hxne hFCent
  have hMindex' : M.index = 1 + f * (r - 1) + e := by
    simpa [M, F, f, e] using hMindex
  have hHindex' : h.H.index = f * (k + 1) + j := by
    simpa [F, f, k] using hHindex
  obtain ⟨hf, hn⟩ :=
    bender_3_4_cards k f n r e j h.H.index M.index
      (by simpa [k] using hk) (by simpa [k] using h.card_K_even)
      (by simpa [f, F] using hFodd) hn2 hrPos
      (by simpa [n, k, A, M, F] using hrMul)
      hMindex' hHindex' hglobal heLower hjle
      (by simpa [k, f, F] using hbound) hnDvdK hnDvdFsub
  have hMcardFinal : Nat.card M = 2 * (k - 1) := by
    rw [hMcard, hf, hn]
    ring
  have hminus :
      h.H.index = (2 * k - 1) * (k - 1) := by
    rcases hbound with hplus | hminus
    · have : k + 3 ≤ f := by simpa [k, f, F] using hplus.2
      omega
    · simpa [k] using hminus.1
  exact ⟨by simpa [f, k, F] using hf,
    by simpa [n, A, M, F] using hn,
    by simpa [M, k] using hMcardFinal,
    by simpa [k] using hminus⟩

/-- The subtraction-free numerical identity behind the residual-set count
in Bender 3.5. -/
private theorem bender_3_5_card_identity
    (k : ℕ) (hk : 4 < k) :
    (2 * k - 1) * (k - 1) * (2 * k) =
      4 * k * (k - 1) +
        (1 + (2 * k - 1) * (k - 1) * (k - 1) +
          ((2 * k - 1) * k) * (k - 2)) := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 5 := ⟨k - 5, by omega⟩
  have hq : 2 * (a + 5) - 1 = 2 * a + 9 := by omega
  have hk1 : a + 5 - 1 = a + 4 := by omega
  have hk2 : a + 5 - 2 = a + 3 := by omega
  rw [hq, hk1, hk2]
  ring

/-- Under the Bender 3.4 cardinal data, the elements outside the identity,
the conjugates of `K^#`, and the conjugates of `F^#` number
`4k(k-1)`. -/
private theorem bender_3_5_residual_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1)) :
    Nat.card ↥(bswResidualSet h F) =
      4 * Nat.card h.K * (Nat.card h.K - 1) := by
  let k : ℕ := Nat.card h.K
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  have hk' : 4 < k := by simpa [k] using hk
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hFcard
    omega
  have hcopKpred : Nat.Coprime k (k - 1) := by
    apply (Nat.coprime_self_sub_right (by omega : 1 ≤ k)).mpr
    exact Nat.coprime_one_right k
  have hcopKF : Nat.Coprime (Nat.card h.K) (Nat.card F) := by
    rw [hFcard]
    exact hcopKpred
  have hKFdisj :
      Disjoint (bswKConjugates h) (bswSubgroupConjugates F) := by
    change Disjoint
      (bswSubgroupConjugates h.K) (bswSubgroupConjugates F)
    exact bswSubgroupConjugates_disjoint_of_coprime_cards
      h.K F hcopKF
  have hMindex : M.index = (2 * k - 1) * k := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < 2 * (k - 1))
    calc
      M.index * (2 * (k - 1)) = M.index * Nat.card M := by
        rw [show Nat.card M = 2 * (k - 1) by
          simpa [M, k] using hMcard]
      _ = Nat.card G := M.index_mul_card
      _ = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
        rw [h.card_H]
        simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
      _ = ((2 * k - 1) * k) * (2 * (k - 1)) := by ring
  have hKconjCard :
      (bswKConjugates h).ncard =
        (2 * k - 1) * (k - 1) * (k - 1) := by
    calc
      (bswKConjugates h).ncard =
          Nat.card ↥(bswKConjugates h) :=
        (Nat.card_coe_set_eq (bswKConjugates h)).symm
      _ = h.H.index * (Nat.card h.K - 1) :=
        bswKConjugates_card h
      _ = (2 * k - 1) * (k - 1) * (k - 1) := by
        rw [hHindex]
  have hFconjCard :
      (bswSubgroupConjugates F).ncard =
        ((2 * k - 1) * k) * (k - 2) := by
    calc
      (bswSubgroupConjugates F).ncard =
          Nat.card ↥(bswSubgroupConjugates F) :=
        (Nat.card_coe_set_eq (bswSubgroupConjugates F)).symm
      _ = M.index * (Nat.card F - 1) :=
        bswSubgroupConjugates_card F M hFne (by simpa [M] using hFTI)
      _ = ((2 * k - 1) * k) * (k - 2) := by
        rw [hMindex, hFcard]
        rw [show Nat.card h.K - 1 - 1 = k - 2 by
          dsimp [k]
          omega]
  let U : Set G :=
    {1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F
  have hOneK : Disjoint ({1} : Set G) (bswKConjugates h) := by
    rw [Set.disjoint_left]
    intro z hz1 hzK
    have hzone : z = 1 := by simpa using hz1
    subst z
    exact one_not_mem_bswKConjugates h hzK
  have hUnionF :
      Disjoint (({1} : Set G) ∪ bswKConjugates h)
        (bswSubgroupConjugates F) := by
    rw [Set.disjoint_left]
    intro z hzU hzF
    rcases hzU with hz1 | hzK
    · have hzone : z = 1 := by simpa using hz1
      subst z
      exact one_not_mem_bswSubgroupConjugates F hzF
    · exact Set.disjoint_left.mp hKFdisj hzK hzF
  have hUcard : U.ncard =
      1 + (2 * k - 1) * (k - 1) * (k - 1) +
        ((2 * k - 1) * k) * (k - 2) := by
    calc
      U.ncard =
          (({1} : Set G) ∪ bswKConjugates h).ncard +
            (bswSubgroupConjugates F).ncard := by
        exact Set.ncard_union_eq hUnionF
      _ = (({1} : Set G).ncard + (bswKConjugates h).ncard) +
            (bswSubgroupConjugates F).ncard := by
        rw [Set.ncard_union_eq hOneK]
      _ = 1 + (2 * k - 1) * (k - 1) * (k - 1) +
            ((2 * k - 1) * k) * (k - 2) := by
        rw [hKconjCard, hFconjCard]
        simp
  have hGcard :
      Nat.card G = (2 * k - 1) * (k - 1) * (2 * k) := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
        rw [h.card_H]
        simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
      _ = (2 * k - 1) * (k - 1) * (2 * k) := by ring
  have hdecomp :
      Nat.card G = 4 * k * (k - 1) + U.ncard := by
    rw [hGcard, hUcard]
    exact bender_3_5_card_identity k (by simpa [k] using hk)
  have hcompl : Uᶜ.ncard = 4 * k * (k - 1) :=
    Set.ncard_compl_of_ncard_eq_add U hdecomp
  calc
    Nat.card ↥(bswResidualSet h F) = (bswResidualSet h F).ncard :=
      Nat.card_coe_set_eq _
    _ = Uᶜ.ncard := by rfl
    _ = 4 * Nat.card h.K * (Nat.card h.K - 1) := by
      simpa [k] using hcompl

/-- Every residual element has centralizer order dividing `2k-1`.  A
prime shared with `2k(k-1)` would give a prime-order centralizer element
conjugate into the Hall subgroup `H` or `F`, forcing the residual element
into the same punctured conjugate union. -/
private theorem bender_3_5_residual_centralizer_card_dvd
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y : G} (hy : y ∈ bswResidualSet h F) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) ∣
      2 * Nat.card h.K - 1 := by
  let k : ℕ := Nat.card h.K
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hyForbidden :
      y ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hy
  have hyne : y ≠ 1 := by
    intro hyone
    apply hyForbidden
    simp [hyone]
  have hyK : y ∉ bswKConjugates h := by
    intro hyKmem
    apply hyForbidden
    simp [hyKmem]
  have hyF : y ∉ bswSubgroupConjugates F := by
    intro hyFmem
    apply hyForbidden
    simp [hyFmem]
  have hcopC :
      Nat.Coprime (Nat.card C) (2 * k * (k - 1)) := by
    by_contra hnot
    rcases Nat.Prime.not_coprime_iff_dvd.mp hnot with
      ⟨p, hpPrime, hpC, hpRest⟩
    let : Fact p.Prime := ⟨hpPrime⟩
    obtain ⟨aC, haCorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := C) p hpC
    let a : G := aC
    have haOrder : orderOf a = p := by
      simpa [a, Subgroup.orderOf_coe] using haCorder
    have hane : a ≠ 1 := by
      intro haone
      rw [haone, orderOf_one] at haOrder
      exact hpPrime.ne_one haOrder.symm
    have hcomm : Commute a y := by
      change a * y = y * a
      exact Subgroup.mem_centralizer_singleton_iff.mp aC.property
    rcases hpPrime.dvd_mul.mp hpRest with hpTwoK | hpPred
    · have hpH : p ∣ Nat.card h.H := by
        rw [h.card_H]
        simpa [k] using hpTwoK
      obtain ⟨g, hgaH⟩ :=
        exists_conjugate_mem_of_prime_order_of_coprime_card_index
          h.H h.hall_H hpPrime hpH haOrder
      have hgaNe : g * a * g⁻¹ ≠ 1 := by
        intro hgaOne
        apply hane
        have hconj := congrArg (fun z : G => g⁻¹ * z * g) hgaOne
        simpa [mul_assoc] using hconj
      have hgaK : g * a * g⁻¹ ∈ bswKConjugates h :=
        mem_bswKConjugates_of_mem_H_of_ne_one h hgaH hgaNe
      have haK : a ∈ bswKConjugates h :=
        (mem_bswKConjugates_conj_iff h g a).mp hgaK
      exact hyK
        (mem_bswKConjugates_of_commute_of_mem_bswKConjugates
          h haK hyne hcomm.symm)
    · have hpF : p ∣ Nat.card F := by
        rw [hFcard]
        simpa [k] using hpPred
      obtain ⟨g, hgaF⟩ :=
        exists_conjugate_mem_of_prime_order_of_coprime_card_index
          F hFHall hpPrime hpF haOrder
      have hgaNe : g * a * g⁻¹ ≠ 1 := by
        intro hgaOne
        apply hane
        have hconj := congrArg (fun z : G => g⁻¹ * z * g) hgaOne
        simpa [mul_assoc] using hconj
      have hgaUnion :
          g * a * g⁻¹ ∈ bswSubgroupConjugates F :=
        ⟨g * a * g⁻¹, hgaF, hgaNe, 1, by simp⟩
      have haUnion : a ∈ bswSubgroupConjugates F :=
        (mem_bswSubgroupConjugates_conj_iff F g a).mp hgaUnion
      exact hyF
        (mem_bswSubgroupConjugates_of_commute_of_mem
          F hFCent haUnion hyne hcomm.symm)
  have hGcard :
      Nat.card G = (2 * k - 1) * (2 * k * (k - 1)) := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
        rw [h.card_H]
        simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
      _ = (2 * k - 1) * (2 * k * (k - 1)) := by ring
  have hCdvd : Nat.card C ∣
      (2 * k - 1) * (2 * k * (k - 1)) := by
    have hCdvdG := Subgroup.card_subgroup_dvd_card C
    rwa [hGcard] at hCdvdG
  have hmain : Nat.card C ∣ 2 * k - 1 :=
    hcopC.dvd_of_dvd_mul_right hCdvd
  simpa [C, k] using hmain

/-- The residual set is stable under ambient conjugation. -/
private def bswResidualSubMulAction
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G) :
    SubMulAction (ConjAct G) G where
  carrier := bswResidualSet h F
  smul_mem' := by
    intro g x hx
    let a : G := ConjAct.ofConjAct g
    change a * x * a⁻¹ ∈ bswResidualSet h F
    rw [bswResidualSet, Set.mem_compl_iff] at hx ⊢
    intro hbad
    apply hx
    simp only [Set.mem_union, Set.mem_singleton_iff] at hbad ⊢
    rcases hbad with (hone | hK) | hF
    · left
      left
      have hconj := congrArg (fun z : G => a⁻¹ * z * a) hone
      simpa [mul_assoc] using hconj
    · left
      right
      exact (mem_bswKConjugates_conj_iff h a x).mp hK
    · right
      exact (mem_bswSubgroupConjugates_conj_iff F a x).mp hF

/-- The residual set is stable under inversion. -/
private theorem mem_bswResidualSet_inv_iff
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G) (x : G) :
    x⁻¹ ∈ bswResidualSet h F ↔ x ∈ bswResidualSet h F := by
  simp only [bswResidualSet, Set.mem_compl_iff, Set.mem_union,
    Set.mem_singleton_iff, inv_eq_one]
  rw [show x⁻¹ ∈ bswKConjugates h ↔ x ∈ bswKConjugates h by
      change x⁻¹ ∈ bswSubgroupConjugates h.K ↔
        x ∈ bswSubgroupConjugates h.K
      exact mem_bswSubgroupConjugates_inv_iff h.K x,
    mem_bswSubgroupConjugates_inv_iff F x]

/-- Equality of residual orbit-quotient classes gives ordinary ambient
conjugacy of their underlying elements. -/
private theorem isConj_of_bswResidual_orbitQuotient_eq
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G)
    (a b : bswResidualSubMulAction h F)
    (hab :
      (Quotient.mk'' a : Quotient
        (MulAction.orbitRel (ConjAct G) (bswResidualSubMulAction h F))) =
      Quotient.mk'' b) :
    IsConj (a : G) (b : G) := by
  have hrel :
      MulAction.orbitRel (ConjAct G) (bswResidualSubMulAction h F) a b :=
    Quotient.exact' hab
  have haOrbit : a ∈ MulAction.orbit (ConjAct G) b :=
    MulAction.orbitRel_apply.mp hrel
  rw [← ConjAct.mem_orbit_conjAct]
  rcases MulAction.mem_orbit_iff.mp haOrbit with ⟨g, hg⟩
  refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
  simpa using congrArg Subtype.val hg

/-- An element conjugate to its inverse and having odd centralizer order is
inverted by an actual involution.  The conjugator gives a nontrivial
involution modulo the centralizer; the odd-kernel lifting theorem supplies
an involution in that quotient coset. -/
private theorem exists_involution_conjugator_of_isConj_inv_of_odd_centralizer
    {G : Type u} [Group G] [Finite G] {y : G}
    (hCodd : Odd (Nat.card (Subgroup.centralizer ({y} : Set G))))
    (hyconj : IsConj y y⁻¹) (hyneinv : y ≠ y⁻¹) :
    ∃ u : G, IsInvolution u ∧ u * y * u⁻¹ = y⁻¹ := by
  obtain ⟨g, hgy⟩ := isConj_iff.mp hyconj
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hconj_mem : ∀ (a c : G), a * y * a⁻¹ = y⁻¹ → c ∈ C →
      a * c * a⁻¹ ∈ C := by
    intro a c hay hc
    have hcy : Commute c y :=
      Subgroup.mem_centralizer_singleton_iff.mp hc
    have hayinv : a * y⁻¹ * a⁻¹ = y := by
      calc
        a * y⁻¹ * a⁻¹ = (a * y * a⁻¹)⁻¹ := by group
        _ = (y⁻¹)⁻¹ := by rw [hay]
        _ = y := by simp
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      (a * c * a⁻¹) * y =
          (a * c * a⁻¹) * (a * y⁻¹ * a⁻¹) := by rw [hayinv]
      _ = a * (c * y⁻¹) * a⁻¹ := by group
      _ = a * (y⁻¹ * c) * a⁻¹ := by rw [hcy.inv_right.eq]
      _ = (a * y⁻¹ * a⁻¹) * (a * c * a⁻¹) := by group
      _ = y * (a * c * a⁻¹) := by rw [hayinv]
  have hginv : g⁻¹ * y * (g⁻¹)⁻¹ = y⁻¹ := by
    have hback : g⁻¹ * y⁻¹ * g = y := by
      calc
        g⁻¹ * y⁻¹ * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [hgy]
        _ = y := by group
    have hinv := congrArg Inv.inv hback
    simpa [mul_assoc] using hinv
  let M : Subgroup G := Subgroup.normalizer (C : Set G)
  have hgM : g ∈ M := by
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconj_mem g c hgy
    · intro hgc
      have hback := hconj_mem g⁻¹ (g * c * g⁻¹) hginv hgc
      simpa [mul_assoc] using hback
  have hCleM : C ≤ M := Subgroup.le_normalizer
  let N : Subgroup M := C.subgroupOf M
  have hNnormal : N.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCleM).mpr le_rfl
  let : N.Normal := hNnormal
  have hNodd : Odd (Nat.card N) := by
    have hcard : Nat.card N = Nat.card C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM)
    rw [hcard]
    exact hCodd
  let gM : M := ⟨g, hgM⟩
  let q := QuotientGroup.mk' N
  have hg2C : g * g ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hggconj : (g * g) * y * (g * g)⁻¹ = y := by
      calc
        (g * g) * y * (g * g)⁻¹ =
            g * (g * y * g⁻¹) * g⁻¹ := by group
        _ = g * y⁻¹ * g⁻¹ := by rw [hgy]
        _ = (g * y * g⁻¹)⁻¹ := by group
        _ = (y⁻¹)⁻¹ := by rw [hgy]
        _ = y := by simp
    have hmul := congrArg (fun z : G => z * (g * g)) hggconj
    simpa [mul_assoc] using hmul
  have hqgNe : q gM ≠ 1 := by
    intro hqg
    have hgN : gM ∈ N :=
      (QuotientGroup.eq_one_iff (N := N) gM).mp hqg
    have hgC : g ∈ C := hgN
    have hgcomm : Commute g y :=
      Subgroup.mem_centralizer_singleton_iff.mp hgC
    have hfix : g * y * g⁻¹ = y := by
      rw [hgcomm.eq]
      simp
    exact hyneinv (hfix.symm.trans hgy)
  have hqgSq : (q gM) ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    apply (QuotientGroup.eq_one_iff (N := N) (gM * gM)).2
    exact hg2C
  have hqgInv : BenderSuzuki.PFAppendixIII.IsInvolution (q gM) :=
    ⟨hqgNe, hqgSq⟩
  obtain ⟨uM, huM, hqu⟩ :=
    BenderSuzuki.exists_involution_lift_of_odd_kernel N hNodd hqgInv
  let u : G := (uM : G)
  have hu : IsInvolution u := by
    constructor
    · intro huone
      exact huM.1 (Subtype.ext huone)
    · exact congrArg Subtype.val huM.2
  have hquotOne : q (uM * gM⁻¹) = 1 := by
    rw [map_mul, map_inv, hqu]
    simp
  have hcN : uM * gM⁻¹ ∈ N :=
    (QuotientGroup.eq_one_iff (N := N) (uM * gM⁻¹)).mp hquotOne
  have hcC : u * g⁻¹ ∈ C := hcN
  have hccomm : Commute (u * g⁻¹) y :=
    Subgroup.mem_centralizer_singleton_iff.mp hcC
  refine ⟨u, hu, ?_⟩
  calc
    u * y * u⁻¹ =
        (u * g⁻¹) * (g * y * g⁻¹) * (u * g⁻¹)⁻¹ := by group
    _ = (u * g⁻¹) * y⁻¹ * (u * g⁻¹)⁻¹ := by rw [hgy]
    _ = y⁻¹ := by
      rw [hccomm.inv_right.eq]
      group

/-- Restricting conjugation to the residual subtype does not change the
stabilizer cardinality, hence its stabilizer still has the cardinality of
the ambient element centralizer. -/
private theorem bswResidual_stabilizer_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G)
    (y : bswResidualSubMulAction h F) :
    Nat.card (MulAction.stabilizer (ConjAct G) y) =
      Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) := by
  have hstab :
      MulAction.stabilizer (ConjAct G) y =
        MulAction.stabilizer (ConjAct G) (y : G) := by
    ext g
    simp only [MulAction.mem_stabilizer_iff]
    constructor
    · intro hg
      simpa using congrArg Subtype.val hg
    · intro hg
      apply Subtype.ext
      simpa using hg
  calc
    Nat.card (MulAction.stabilizer (ConjAct G) y) =
        Nat.card (MulAction.stabilizer (ConjAct G) (y : G)) := by
      rw [hstab]
    _ = Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) :=
      (Subgroup.nat_card_centralizer_nat_card_stabilizer (y : G)).symm

/-- Orbit--stabilizer for the residual subtype, with the stabilizer written
as the ambient element centralizer. -/
private theorem bswResidual_orbit_card_mul_centralizer_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G)
    (y : bswResidualSubMulAction h F) :
    Nat.card (MulAction.orbit (ConjAct G) y) *
        Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) =
      Nat.card G := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have horbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) y
  have horbit' :
      Nat.card (MulAction.orbit (ConjAct G) y) *
          Nat.card (MulAction.stabilizer (ConjAct G) y) =
        Nat.card G := by
    simpa only [Nat.card_eq_fintype_card, ConjAct.card] using horbit
  rwa [bswResidual_stabilizer_card h F y] at horbit'

/-- If finitely many odd positive multipliers sum to two, there are exactly
two of them and both are one. -/
private theorem odd_multipliers_sum_two
    {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hmOdd : ∀ i, Odd (m i)) (hsum : ∑ i, m i = 2) :
    Fintype.card ι = 2 ∧ ∀ i, m i = 1 := by
  have hmLe (i : ι) : m i ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum
      (fun j _hj => Nat.zero_le (m j)) (Finset.mem_univ i)
  have hmOne (i : ι) : m i = 1 := by
    rcases hmOdd i with ⟨a, ha⟩
    have := hmLe i
    omega
  constructor
  · calc
      Fintype.card ι = ∑ _i : ι, 1 := by simp
      _ = ∑ i : ι, m i := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (hmOne i).symm
      _ = 2 := hsum
  · exact hmOne

/-- Bender 3.5(i),(iii), up to the later proof that inversion exchanges the
two classes: the residual subtype has exactly two conjugacy orbits, every
such orbit has size `2k(k-1)`, and every residual centralizer has order
`2k-1`. -/
private theorem bender_3_5_residual_orbit_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1)) :
    let Y := bswResidualSubMulAction h F
    let Omega := Quotient (MulAction.orbitRel (ConjAct G) Y)
    Nat.card Omega = 2 ∧
      ∀ y : Y,
        Nat.card (MulAction.orbit (ConjAct G) y) =
            2 * Nat.card h.K * (Nat.card h.K - 1) ∧
          Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) =
            2 * Nat.card h.K - 1 := by
  classical
  let k : ℕ := Nat.card h.K
  let q : ℕ := 2 * k - 1
  let B : ℕ := 2 * k * (k - 1)
  let Y := bswResidualSubMulAction h F
  let Omega := Quotient (MulAction.orbitRel (ConjAct G) Y)
  let : Fintype G := Fintype.ofFinite G
  let : Fintype Y := Fintype.ofFinite Y
  let : Fintype Omega := Fintype.ofFinite Omega
  have hk' : 4 < k := by simpa [k] using hk
  have hBpos : 0 < B := by
    dsimp [B]
    exact Nat.mul_pos (by omega) (by omega)
  have hqOdd : Odd q := by
    refine ⟨k - 1, ?_⟩
    dsimp [q]
    omega
  have hGcard : Nat.card G = q * B := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
        rw [h.card_H]
        simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
      _ = q * B := by
        dsimp [q, B]
        ring
  have hCdvd (omega : Omega) :
      Nat.card
          (Subgroup.centralizer ({((Quotient.out omega : Y) : G)} : Set G)) ∣
        q := by
    simpa [q, k, Y] using
      bender_3_5_residual_centralizer_card_dvd
        h hk F hFcard hFCent hFHall hHindex
        (Quotient.out omega).property
  let m : Omega → ℕ := fun omega => (hCdvd omega).choose
  have hqFactor (omega : Omega) :
      q = Nat.card
          (Subgroup.centralizer ({((Quotient.out omega : Y) : G)} : Set G)) *
        m omega :=
    (hCdvd omega).choose_spec
  have hmOdd (omega : Omega) : Odd (m omega) := by
    apply hqOdd.of_dvd_nat
    refine ⟨Nat.card
      (Subgroup.centralizer ({((Quotient.out omega : Y) : G)} : Set G)), ?_⟩
    simpa [Nat.mul_comm] using hqFactor omega
  have hOrbit (omega : Omega) :
      Nat.card (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) =
        B * m omega := by
    apply Nat.eq_of_mul_eq_mul_right
      (Nat.card_pos (α :=
        Subgroup.centralizer ({((Quotient.out omega : Y) : G)} : Set G)))
    calc
      Nat.card (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) *
          Nat.card
            (Subgroup.centralizer
              ({((Quotient.out omega : Y) : G)} : Set G)) =
        Nat.card G :=
          bswResidual_orbit_card_mul_centralizer_card
            h F (Quotient.out omega : Y)
      _ = q * B := hGcard
      _ = (B * m omega) *
          Nat.card
            (Subgroup.centralizer
              ({((Quotient.out omega : Y) : G)} : Set G)) := by
        rw [hqFactor omega]
        ring
  have hResidualCard : Nat.card Y = 2 * B := by
    let eY : Y ≃ ↥(bswResidualSet h F) :=
      { toFun := fun y => ⟨y.1, y.2⟩
        invFun := fun y => ⟨y.1, y.2⟩
        left_inv := by intro y; rfl
        right_inv := by intro y; rfl }
    calc
      Nat.card Y = Nat.card ↥(bswResidualSet h F) := Nat.card_congr eY
      _ = 4 * k * (k - 1) := by
        simpa [k] using
          bender_3_5_residual_card h hk F hFcard hMcard hFTI hHindex
      _ = 2 * B := by
        dsimp [B]
        ring
  have hsumOrbit :
      Nat.card Y =
        ∑ omega : Omega,
          Nat.card
            (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) := by
    calc
      Nat.card Y = Nat.card
          (Sigma fun omega : Omega =>
            MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbits (ConjAct G) Y)
      _ = ∑ omega : Omega,
          Nat.card
            (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) :=
        Nat.card_sigma
  have hsumBM : ∑ omega : Omega, B * m omega = 2 * B := by
    calc
      ∑ omega : Omega, B * m omega =
          ∑ omega : Omega,
            Nat.card
              (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) := by
        apply Finset.sum_congr rfl
        intro omega _homega
        exact (hOrbit omega).symm
      _ = Nat.card Y := hsumOrbit.symm
      _ = 2 * B := hResidualCard
  have hsumM : ∑ omega : Omega, m omega = 2 := by
    apply Nat.eq_of_mul_eq_mul_left hBpos
    calc
      B * ∑ omega : Omega, m omega =
          ∑ omega : Omega, B * m omega := by rw [Finset.mul_sum]
      _ = 2 * B := hsumBM
      _ = B * 2 := by ring
  obtain ⟨hOmegaCard, hmOne⟩ :=
    odd_multipliers_sum_two m hmOdd hsumM
  have hRepOrbit (omega : Omega) :
      Nat.card (MulAction.orbit (ConjAct G) (Quotient.out omega : Y)) = B := by
    rw [hOrbit omega, hmOne omega, Nat.mul_one]
  have hAnyOrbit (y : Y) :
      Nat.card (MulAction.orbit (ConjAct G) y) = B := by
    let omega : Omega := Quotient.mk'' y
    have hquot :
        (Quotient.mk'' (Quotient.out omega) : Omega) = Quotient.mk'' y := by
      simpa [omega] using Quotient.out_eq' omega
    have hrel :
        MulAction.orbitRel (ConjAct G) Y (Quotient.out omega) y :=
      Quotient.exact' hquot
    have houtMem :
        Quotient.out omega ∈ MulAction.orbit (ConjAct G) y := by
      simpa [MulAction.orbitRel_apply] using hrel
    have horbitEq :
        MulAction.orbit (ConjAct G) (Quotient.out omega) =
          MulAction.orbit (ConjAct G) y :=
      MulAction.orbit_eq_iff.mpr houtMem
    rw [← horbitEq]
    exact hRepOrbit omega
  have hAnyCentralizer (y : Y) :
      Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) = q := by
    apply Nat.eq_of_mul_eq_mul_left hBpos
    calc
      B * Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) =
          Nat.card (MulAction.orbit (ConjAct G) y) *
            Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) := by
        rw [hAnyOrbit y]
      _ = Nat.card G :=
        bswResidual_orbit_card_mul_centralizer_card h F y
      _ = q * B := hGcard
      _ = B * q := by ring
  refine ⟨?_, ?_⟩
  · simpa [Nat.card_eq_fintype_card] using hOmegaCard
  · intro y
    exact ⟨by simpa [B, k] using hAnyOrbit y,
      by simpa [q, k] using hAnyCentralizer y⟩

/-- Elementwise form of the residual-centralizer order conclusion from
Bender 3.5. -/
private theorem bender_3_5_residual_centralizer_card
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y : G} (hy : y ∈ bswResidualSet h F) :
    Nat.card (Subgroup.centralizer ({y} : Set G)) =
      2 * Nat.card h.K - 1 := by
  let Y := bswResidualSubMulAction h F
  have hdata := bender_3_5_residual_orbit_data
    h hk F hFcard hFCent hFHall hMcard hFTI hHindex
  exact (hdata.2 (⟨y, hy⟩ : Y)).2

/-- The two outcomes of the selected-centralizer coset dichotomy, stated
only as the centralizer cardinality needed in Bender 3.5(ii). -/
private theorem selected_centralizer_card_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFCent : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer ({x} : Set G))
    (hbound :
      (h.H.index =
            (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
          Nat.card h.K + 3 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))) ∨
        (h.H.index =
            (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
          Nat.card h.K - 1 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    Nat.card (Subgroup.centralizer ({x} : Set G)) =
        2 * Nat.card h.K + 1 ∨
      Nat.card (Subgroup.centralizer ({x} : Set G)) =
        Nat.card h.K - 1 := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let k : ℕ := Nat.card h.K
  let f : ℕ := Nat.card F
  let e : ℕ := Nat.card
    (selected_centralizer_unoccupied_nonbase_cosets F)
  by_cases he : e = 0
  · left
    obtain ⟨_r, j, _hrPos, _hrMul, _hMindex, _heCases, hjle, hHcount⟩ :=
      selected_centralizer_bender_3_2_count_data
        h hxC hxne hFcomm hFodd hFinv hFHall hFTI
    have hj0 : j = 0 := by
      have : j ≤ e := by simpa [e, F] using hjle
      omega
    have hindex : h.H.index = f * (k + 1) := by
      simpa [f, k, hj0] using hHcount
    have hf : f = 2 * k + 1 :=
      bender_3_3_card_F k f h.H.index
        (by simpa [k] using hk) (by simpa [k] using h.card_K_even)
        (by simpa [f, k, F] using hbound) hindex
    simpa [f, k, F] using hf
  · right
    have hePos : 0 < Nat.card
        (selected_centralizer_unoccupied_nonbase_cosets F) := by
      simpa [e] using Nat.pos_of_ne_zero he
    exact (selected_centralizer_bender_3_4_card_data
      h hk hxC hxne hFcomm hFodd hFinv hFCent hbound
        hFHall hFTI hePos).1

/-- Bender 3.5(ii): a residual element is not conjugate to its inverse. -/
private theorem bender_3_5_residual_not_isConj_inv
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y : G} (hy : y ∈ bswResidualSet h F) :
    ¬ IsConj y y⁻¹ := by
  let k : ℕ := Nat.card h.K
  have hyForbidden :
      y ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hy
  have hyne : y ≠ 1 := by
    intro hyone
    apply hyForbidden
    simp [hyone]
  have hyK : y ∉ bswKConjugates h := by
    intro hyKmem
    apply hyForbidden
    simp [hyKmem]
  have hyneinv : y ≠ y⁻¹ := by
    intro hyinv
    have hyI : IsInvolution y := by
      constructor
      · exact hyne
      · have hmul := congrArg (fun z : G => z * y) hyinv
        simpa [pow_two] using hmul
    exact hyK (mem_bswKConjugates_of_isInvolution h hyI)
  have hyCcard :
      Nat.card (Subgroup.centralizer ({y} : Set G)) = 2 * k - 1 := by
    simpa [k] using bender_3_5_residual_centralizer_card
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  have hyCodd : Odd
      (Nat.card (Subgroup.centralizer ({y} : Set G))) := by
    rw [hyCcard]
    refine ⟨k - 1, ?_⟩
    have hk' : 4 < k := by simpa [k] using hk
    omega
  intro hyconj
  obtain ⟨u, huI, huy⟩ :=
    exists_involution_conjugator_of_isConj_inv_of_odd_centralizer
      hyCodd hyconj hyneinv
  obtain ⟨g, hgu⟩ := h.involutions_conjugate u huI
  let x : G := g * y * g⁻¹
  have hxResidual : x ∈ bswResidualSet h F := by
    have hx := (bswResidualSubMulAction h F).smul_mem
      (ConjAct.toConjAct g) hy
    change x ∈ bswResidualSubMulAction h F
    simpa [x, ConjAct.toConjAct_smul] using hx
  have hxForbidden :
      x ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hxResidual
  have hxne : x ≠ 1 := by
    intro hxone
    apply hxForbidden
    simp [hxone]
  have hxK : x ∉ bswKConjugates h := by
    intro hxKmem
    apply hxForbidden
    simp [hxKmem]
  have htx : h.t * x * h.t⁻¹ = x⁻¹ := by
    calc
      h.t * x * h.t⁻¹ =
          (g * u * g⁻¹) * (g * y * g⁻¹) * (g * u * g⁻¹)⁻¹ := by
        rw [hgu]
      _ = g * (u * y * u⁻¹) * g⁻¹ := by group
      _ = g * y⁻¹ * g⁻¹ := by rw [huy]
      _ = x⁻¹ := by
        dsimp [x]
        group
  obtain ⟨hXcomm, hXodd, hXdata⟩ :=
    selected_centralizer_structure h hxK hxne htx
  have hXCent : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer ({x} : Set G) := by
    intro z hz hzne
    exact (hXdata z hz hzne).1
  have hXinv : ∀ z : G,
      z ∈ Subgroup.centralizer ({x} : Set G) →
        h.t * z * h.t⁻¹ = z⁻¹ := by
    intro z hz
    by_cases hzone : z = 1
    · subst z
      simp
    · exact (hXdata z hz hzone).2
  have hXHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index :=
    selected_centralizer_isHall hXCent
  have hXTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G) :=
    selected_centralizer_isTISubsetRelative hxne hXcomm hXCent
  have hxCcard :
      Nat.card (Subgroup.centralizer ({x} : Set G)) = 2 * k - 1 := by
    simpa [k] using bender_3_5_residual_centralizer_card
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hxResidual
  have hbound :
      (h.H.index =
            (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
          Nat.card h.K + 3 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))) ∨
        (h.H.index =
            (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
          Nat.card h.K - 1 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))) := by
    right
    refine ⟨hHindex, ?_⟩
    rw [hxCcard]
    dsimp [k]
    omega
  rcases selected_centralizer_card_cases
      h hk hxK hxne hXcomm hXodd hXinv hXCent hbound hXHall hXTI with
    hplus | hminus
  · rw [hxCcard] at hplus
    have hk' : 4 < k := by simpa [k] using hk
    omega
  · rw [hxCcard] at hminus
    have hk' : 4 < k := by simpa [k] using hk
    omega

/-- Conjugate elements have the same order. -/
private theorem orderOf_eq_of_isConj
    {G : Type u} [Group G] {a b : G} (hab : IsConj a b) :
    orderOf a = orderOf b := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  symm
  calc
    orderOf b = orderOf ((MulAut.conj g) a) := by
      simpa [MulAut.conj_apply] using congrArg orderOf hg.symm
    _ = orderOf a := (MulAut.conj g).orderOf_eq a

/-- A nonidentity element centralizing a residual element is itself
residual. -/
private theorem mem_bswResidualSet_of_mem_centralizer
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    {y a : G} (hy : y ∈ bswResidualSet h F)
    (haC : a ∈ Subgroup.centralizer ({y} : Set G)) (hane : a ≠ 1) :
    a ∈ bswResidualSet h F := by
  have hyForbidden :
      y ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hy
  have hyne : y ≠ 1 := by
    intro hyone
    apply hyForbidden
    simp [hyone]
  have hcomm : Commute a y :=
    Subgroup.mem_centralizer_singleton_iff.mp haC
  rw [bswResidualSet, Set.mem_compl_iff]
  intro hbad
  simp only [Set.mem_union, Set.mem_singleton_iff] at hbad
  rcases hbad with (haone | haK) | haF
  · exact hane haone
  · apply hyForbidden
    simp only [Set.mem_union, Set.mem_singleton_iff]
    left
    right
    exact mem_bswKConjugates_of_commute_of_mem_bswKConjugates
      h haK hyne hcomm.symm
  · apply hyForbidden
    simp only [Set.mem_union, Set.mem_singleton_iff]
    right
    exact mem_bswSubgroupConjugates_of_commute_of_mem
      F hFCent haF hyne hcomm.symm

/-- Once inversion exchanges the two residual classes, every residual
element is conjugate to `y` or to `y⁻¹`. -/
private theorem bender_3_5_residual_isConj_or_inv
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ z : G, z ∈ F → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y a : G} (hy : y ∈ bswResidualSet h F)
    (ha : a ∈ bswResidualSet h F) :
    IsConj a y ∨ IsConj a y⁻¹ := by
  let Y := bswResidualSubMulAction h F
  let Omega := Quotient (MulAction.orbitRel (ConjAct G) Y)
  let yY : Y := ⟨y, hy⟩
  have hyInv : y⁻¹ ∈ bswResidualSet h F :=
    (mem_bswResidualSet_inv_iff h F y).mpr hy
  let yiY : Y := ⟨y⁻¹, hyInv⟩
  let aY : Y := ⟨a, ha⟩
  let cy : Omega := Quotient.mk'' yY
  let cyi : Omega := Quotient.mk'' yiY
  let ca : Omega := Quotient.mk'' aY
  have hOmega : Nat.card Omega = 2 :=
    (bender_3_5_residual_orbit_data
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex).1
  have hcyNe : cy ≠ cyi := by
    intro heq
    apply bender_3_5_residual_not_isConj_inv
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
    exact isConj_of_bswResidual_orbitQuotient_eq h F yY yiY heq
  have hall : ∀ c : Omega, c = cy ∨ c = cyi := by
    intro c
    by_cases hc : c = cy
    · exact Or.inl hc
    · rcases (Nat.card_eq_two_iff' cy).mp hOmega with
        ⟨other, _hother, huniq⟩
      exact Or.inr
        ((huniq c hc).trans (huniq cyi (Ne.symm hcyNe)).symm)
  rcases hall ca with hca | hca
  · left
    exact isConj_of_bswResidual_orbitQuotient_eq h F aY yY hca
  · right
    exact isConj_of_bswResidual_orbitQuotient_eq h F aY yiY hca

/-- Bender 3.5(iii): the centralizer of a residual element is a `p`-group
for some prime `p`. -/
private theorem bender_3_5_residual_centralizer_isPGroup
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ z : G, z ∈ F → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y : G} (hy : y ∈ bswResidualSet h F) :
    ∃ p : ℕ, Nat.Prime p ∧
      IsPGroup p (Subgroup.centralizer ({y} : Set G)) := by
  let k : ℕ := Nat.card h.K
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  have hCcard : Nat.card C = 2 * k - 1 := by
    simpa [C, k] using bender_3_5_residual_centralizer_card
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  have hCneOne : Nat.card C ≠ 1 := by
    rw [hCcard]
    have hk' : 4 < k := by simpa [k] using hk
    omega
  obtain ⟨p, hpPrime, hpC⟩ := Nat.exists_prime_and_dvd hCneOne
  let : Fact p.Prime := ⟨hpPrime⟩
  obtain ⟨aC, haCorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) p hpC
  have haCne : aC ≠ 1 := by
    intro haone
    rw [haone, orderOf_one] at haCorder
    exact hpPrime.ne_one haCorder.symm
  have hane : (aC : G) ≠ 1 := by
    intro haone
    exact haCne (Subtype.ext haone)
  have haResidual : (aC : G) ∈ bswResidualSet h F :=
    mem_bswResidualSet_of_mem_centralizer
      h F hFCent hy aC.property hane
  have haOrderG : orderOf (aC : G) = p := by
    simpa [Subgroup.orderOf_coe] using haCorder
  have hyOrder : orderOf y = p := by
    rcases bender_3_5_residual_isConj_or_inv
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex
          hy haResidual with haConj | haConj
    · exact (orderOf_eq_of_isConj haConj).symm.trans haOrderG
    · have hord := orderOf_eq_of_isConj haConj
      rw [orderOf_inv] at hord
      exact hord.symm.trans haOrderG
  refine ⟨p, hpPrime, ?_⟩
  apply (IsPGroup.iff_orderOf (p := p) (G := C)).2
  intro c
  by_cases hcone : c = 1
  · subst c
    exact ⟨0, by simp⟩
  have hcne : (c : G) ≠ 1 := by
    intro hconeG
    exact hcone (Subtype.ext hconeG)
  have hcResidual : (c : G) ∈ bswResidualSet h F :=
    mem_bswResidualSet_of_mem_centralizer
      h F hFCent hy c.property hcne
  have hcOrderG : orderOf (c : G) = p := by
    rcases bender_3_5_residual_isConj_or_inv
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex
          hy hcResidual with hcConj | hcConj
    · exact (orderOf_eq_of_isConj hcConj).trans hyOrder
    · have hord := orderOf_eq_of_isConj hcConj
      rw [orderOf_inv] at hord
      exact hord.trans hyOrder
  refine ⟨1, ?_⟩
  have hcOrder : orderOf c = p := by
    simpa [Subgroup.orderOf_coe] using hcOrderG
  simpa [pow_one] using hcOrder

/-- The order of an element in a punctured conjugate union divides the
order of the defining subgroup. -/
private theorem orderOf_dvd_card_of_mem_bswSubgroupConjugates
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) {x : G}
    (hx : x ∈ bswSubgroupConjugates P) :
    orderOf x ∣ Nat.card P := by
  rcases hx with ⟨a, haP, _hane, g, rfl⟩
  have hconj : IsConj a (g * a * g⁻¹) :=
    isConj_iff.mpr ⟨g, rfl⟩
  rw [← orderOf_eq_of_isConj hconj]
  simpa [Subgroup.orderOf_coe] using
    orderOf_dvd_natCard (⟨a, haP⟩ : P)

/-- The prime attached to a residual centralizer divides `2k-1`, is odd,
and is coprime to the orders of the two already occupied families. -/
private theorem bender_3_6_residual_prime_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ z : G, z ∈ F → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {y : G} (hy : y ∈ bswResidualSet h F) :
    ∃ p : ℕ, Nat.Prime p ∧
      IsPGroup p (Subgroup.centralizer ({y} : Set G)) ∧
      p ∣ 2 * Nat.card h.K - 1 ∧ Odd p ∧
      Nat.Coprime p (2 * Nat.card h.K * (Nat.card h.K - 1)) := by
  let k : ℕ := Nat.card h.K
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  obtain ⟨p, hpPrime, hpC⟩ :=
    bender_3_5_residual_centralizer_isPGroup
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  let : Fact p.Prime := ⟨hpPrime⟩
  have hCcard : Nat.card C = 2 * k - 1 := by
    simpa [C, k] using bender_3_5_residual_centralizer_card
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  have hCneOne : Nat.card C ≠ 1 := by
    rw [hCcard]
    have hk' : 4 < k := by simpa [k] using hk
    omega
  have hpq : p ∣ 2 * k - 1 := by
    rw [← hCcard]
    exact hpC.card_eq_or_dvd.resolve_left hCneOne
  have hqOdd : Odd (2 * k - 1) := by
    refine ⟨k - 1, ?_⟩
    have hk' : 4 < k := by simpa [k] using hk
    omega
  have hpOdd : Odd p := hpPrime.odd_of_ne_two
    (hqOdd.ne_two_of_dvd_nat hpq)
  have hpCop : Nat.Coprime p (2 * k * (k - 1)) := by
    apply hpPrime.coprime_iff_not_dvd.mpr
    intro hpRest
    rcases hpPrime.dvd_mul.mp hpRest with hpTwoK | hpPred
    · have hpOne : p ∣ 1 := by
        have hsub := Nat.dvd_sub hpTwoK hpq
        convert hsub using 1 <;> omega
      exact hpPrime.not_dvd_one hpOne
    · have hpTwoPred : p ∣ 2 * (k - 1) :=
        dvd_mul_of_dvd_right hpPred 2
      have hpOne : p ∣ 1 := by
        have hsub := Nat.dvd_sub hpq hpTwoPred
        convert hsub using 1 <;> omega
      exact hpPrime.not_dvd_one hpOne
  exact ⟨p, hpPrime, hpC, by simpa [k] using hpq, hpOdd,
    by simpa [k] using hpCop⟩

/-- Every nonidentity element of a subgroup at the residual prime lies in
the residual set. -/
private theorem mem_bswResidualSet_of_mem_residualPrimeSubgroup
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    (X : Subgroup G) (hXp : IsPGroup p X)
    {x : G} (hxX : x ∈ X) (hxne : x ≠ 1) :
    x ∈ bswResidualSet h F := by
  let : Fact p.Prime := ⟨hpPrime⟩
  let xX : X := ⟨x, hxX⟩
  have hxXne : xX ≠ 1 := by
    intro hone
    exact hxne (congrArg Subtype.val hone)
  have hpOrder : p ∣ orderOf x := by
    simpa [xX, Subgroup.orderOf_coe] using hXp.dvd_orderOf hxXne
  rw [bswResidualSet, Set.mem_compl_iff]
  intro hbad
  simp only [Set.mem_union, Set.mem_singleton_iff] at hbad
  rcases hbad with (hxone | hxK) | hxF
  · exact hxne hxone
  · have hpK : p ∣ Nat.card h.K :=
      hpOrder.trans
        (orderOf_dvd_card_of_mem_bswSubgroupConjugates h.K hxK)
    have hpRest : p ∣ 2 * Nat.card h.K * (Nat.card h.K - 1) := by
      rcases hpK with ⟨a, ha⟩
      refine ⟨2 * a * (Nat.card h.K - 1), ?_⟩
      rw [ha]
      ring
    exact hpPrime.ne_one
      (Nat.eq_one_of_dvd_coprimes hpCop dvd_rfl hpRest)
  · have hpF : p ∣ Nat.card F :=
      hpOrder.trans
        (orderOf_dvd_card_of_mem_bswSubgroupConjugates F hxF)
    have hpPred : p ∣ Nat.card h.K - 1 := by
      rwa [hFcard] at hpF
    have hpRest : p ∣ 2 * Nat.card h.K * (Nat.card h.K - 1) := by
      rcases hpPred with ⟨a, ha⟩
      refine ⟨2 * Nat.card h.K * a, ?_⟩
      rw [ha]
      ring
    exact hpPrime.ne_one
      (Nat.eq_one_of_dvd_coprimes hpCop dvd_rfl hpRest)

/-- An involution normalizing but not centralizing a subgroup inverts a
nonidentity element of that subgroup. -/
private theorem exists_nontrivial_inverted_of_involution_normalizes_not_centralizes
    {H : Type u} [Group H]
    {W : Subgroup H} {z : H}
    (hz : IsInvolution z)
    (hzNorm : z ∈ Subgroup.normalizer (W : Set H))
    (hnot : ¬ W ≤ Subgroup.centralizer ({z} : Set H)) :
    ∃ x : H, x ∈ W ∧ x ≠ 1 ∧ z * x * z⁻¹ = x⁻¹ := by
  rcases SetLike.not_le_iff_exists.mp hnot with ⟨w, hwW, hwNot⟩
  have hzwW : z * w * z⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp hzNorm w).mp hwW
  let x : H := w⁻¹ * (z * w * z⁻¹)
  have hxW : x ∈ W := W.mul_mem (W.inv_mem hwW) hzwW
  have hxne : x ≠ 1 := by
    intro hx
    apply hwNot
    rw [Subgroup.mem_centralizer_singleton_iff]
    have heq : w = z * w * z⁻¹ := eq_of_inv_mul_eq_one hx
    calc
      w * z = (z * w * z⁻¹) * z :=
        congrArg (fun q : H => q * z) heq
      _ = z * w := by simp [mul_assoc]
  have hz2 : z * z = 1 := by
    simpa [pow_two] using hz.2
  have hzinvself : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzinv : z * x * z⁻¹ = x⁻¹ := by
    rw [hzinvself]
    dsimp only [x]
    simp only [hzinvself]
    calc
      z * (w⁻¹ * (z * w * z)) * z =
          z * w⁻¹ * z * w := by simp [mul_assoc, hz2]
      _ = (z * w * z)⁻¹ * w := by
        simp [hzinvself, mul_assoc]
      _ = (w⁻¹ * (z * w * z))⁻¹ := by simp
  exact ⟨x, hxW, hxne, hzinv⟩

/-- Conjugating a subgroup does not change its finite cardinality. -/
private theorem bsw_natCard_conjBy
    {G : Type u} [Group G] (D : Subgroup G) (g : G) :
    Nat.card (D.conjBy g) = Nat.card D := by
  simpa [Subgroup.conjBy] using
    (Subgroup.card_map_of_injective
      (K := D) (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective)

/-- An odd-order subgroup of a finite group lies in every subgroup of
index two. -/
private theorem odd_subgroup_le_of_index_eq_two
    {H : Type u} [Group H] [Finite H]
    (D B : Subgroup H) (hindex : D.index = 2)
    (hBodd : Odd (Nat.card B)) : B ≤ D := by
  have hDnormal : D.Normal := Subgroup.normal_of_index_eq_two hindex
  let : D.Normal := hDnormal
  let q : H →* H ⧸ D := QuotientGroup.mk' D
  intro b hb
  apply (QuotientGroup.eq_one_iff (N := D) (x := b)).mp
  apply orderOf_eq_one_iff.mp
  have hordB : orderOf (q b) ∣ Nat.card B := by
    exact (orderOf_map_dvd q b).trans <| by
      simpa using orderOf_dvd_natCard (⟨b, hb⟩ : B)
  have hordTwo : orderOf (q b) ∣ 2 := by
    rw [← hindex, D.index_eq_card]
    exact orderOf_dvd_natCard (q b)
  exact Nat.eq_one_of_dvd_coprimes
    hBodd.coprime_two_right hordB hordTwo

/-- Relative form of the index-two odd-subgroup argument, with the index
encoded by the cardinality of an overgroup. -/
private theorem odd_subgroup_le_of_card_eq_two_mul
    {H : Type u} [Group H] [Finite H]
    (D E B : Subgroup H) (hDE : D ≤ E) (hBE : B ≤ E)
    (hEcard : Nat.card E = 2 * Nat.card D)
    (hBodd : Odd (Nat.card B)) : B ≤ D := by
  let D0 : Subgroup E := D.subgroupOf E
  let B0 : Subgroup E := B.subgroupOf E
  have hD0card : Nat.card D0 = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDE)
  have hB0card : Nat.card B0 = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBE)
  have hD0index : D0.index = 2 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D))
    calc
      D0.index * Nat.card D = D0.index * Nat.card D0 := by
        rw [hD0card]
      _ = Nat.card E := D0.index_mul_card
      _ = 2 * Nat.card D := hEcard
  have hB0odd : Odd (Nat.card B0) := by
    rwa [hB0card]
  have hB0D0 : B0 ≤ D0 :=
    odd_subgroup_le_of_index_eq_two D0 B0 hD0index hB0odd
  intro b hbB
  let bE : E := ⟨b, hBE hbB⟩
  have hbB0 : bE ∈ B0 := hbB
  exact hB0D0 hbB0

/-- Relative TI controls the normalizer of every nontrivial subgroup of
the TI subgroup. -/
private theorem normalizer_le_of_relativeTI
    {H : Type u} [Group H]
    (N D : Subgroup H)
    (hTI : Suzuki.VI.IsTISubsetRelative N (D : Set H))
    (X : Subgroup H) (hX : X ≠ ⊥) (hXD : X ≤ D) :
    Subgroup.normalizer (X : Set H) ≤ N := by
  intro g hg
  obtain ⟨x, hx_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
  have hxX : (x : H) ∈ X := x.property
  have hxD : (x : H) ∈ D := hXD hxX
  have hxgX : g * (x : H) * g⁻¹ ∈ X :=
    (Subgroup.mem_normalizer_iff.mp hg (x : H)).mp hxX
  have hxgD : g * (x : H) * g⁻¹ ∈ D := hXD hxgX
  have hx_ne_H : (x : H) ≠ 1 := by
    intro hx
    exact hx_ne (Subtype.ext hx)
  obtain ⟨n, hn⟩ := hTI.2.2.1 hxD hxgD ⟨g, rfl⟩
  have hc : (n : H)⁻¹ * g ∈
      Subgroup.centralizer ({(x : H)} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      (n : H)⁻¹ * g * (x : H) =
          (n : H)⁻¹ * (g * (x : H) * g⁻¹) * g := by group
      _ = (n : H)⁻¹ * ((n : H) * (x : H) * (n : H)⁻¹) * g := by
        rw [hn]
      _ = (x : H) * ((n : H)⁻¹ * g) := by group
  have hcN : (n : H)⁻¹ * g ∈ N :=
    hTI.2.2.2 (x : H) hxD hx_ne_H hc
  have hmul := N.mul_mem n.property hcN
  simpa using hmul

/-- Conjugated form of relative-TI normalizer control. -/
private theorem normalizer_le_conjBy_of_relativeTI
    {H : Type u} [Group H]
    (N D : Subgroup H)
    (hTI : Suzuki.VI.IsTISubsetRelative N (D : Set H))
    (g : H) (X : Subgroup H) (hX : X ≠ ⊥)
    (hXDg : X ≤ D.conjBy g) :
    Subgroup.normalizer (X : Set H) ≤ N.conjBy g := by
  let X0 : Subgroup H := X.conjBy g⁻¹
  have hX0ne : X0 ≠ ⊥ := by
    intro hbot
    apply hX
    have hmap := congrArg (fun Y : Subgroup H => Y.conjBy g) hbot
    calc
      X = X0.conjBy g := by
        simpa [X0] using (Subgroup.conjBy_inv' X g).symm
      _ = (⊥ : Subgroup H).conjBy g := hmap
      _ = ⊥ := by simp [Subgroup.conjBy]
  have hX0D : X0 ≤ D := by
    have hmap : X.conjBy g⁻¹ ≤ (D.conjBy g).conjBy g⁻¹ :=
      Subgroup.map_mono hXDg
    simpa [X0, Subgroup.conjBy_inv] using hmap
  have hnorm0 : Subgroup.normalizer (X0 : Set H) ≤ N :=
    normalizer_le_of_relativeTI N D hTI X0 hX0ne hX0D
  have hmapnorm :
      (Subgroup.normalizer (X0 : Set H)).conjBy g ≤ N.conjBy g :=
    Subgroup.map_mono hnorm0
  have hnormconj :
      (Subgroup.normalizer (X0 : Set H)).conjBy g =
        Subgroup.normalizer (X0.conjBy g : Set H) := by
    simpa [Subgroup.conjBy] using
      (Subgroup.map_equiv_normalizer_eq X0 (MulAut.conj g))
  have hXrecover : X0.conjBy g = X := by
    simpa [X0] using Subgroup.conjBy_inv' X g
  rw [hnormconj, hXrecover] at hmapnorm
  exact hmapnorm

/-- Centralizer containment transports across conjugation. -/
private theorem centralizer_le_conjBy_of_eq_conj
    {G : Type u} [Group G]
    (D : Subgroup G) {a z : G}
    (hcent : Subgroup.centralizer ({a} : Set G) ≤ D)
    (g : G) (hz : z = g * a * g⁻¹) :
    Subgroup.centralizer ({z} : Set G) ≤ D.conjBy g := by
  intro c hc
  let c0 : G := g⁻¹ * c * g
  have hccomm : Commute c z :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hc0comm : Commute c0 a := by
    have hconj := hccomm.conj g⁻¹
    rw [hz] at hconj
    simpa [c0, mul_assoc] using hconj
  have hc0D : c0 ∈ D := hcent
    (Subgroup.mem_centralizer_singleton_iff.mpr hc0comm)
  rw [Subgroup.conjBy, Subgroup.mem_map]
  refine ⟨c0, hc0D, ?_⟩
  simp [c0, MulAut.conj_apply, mul_assoc]

/-- An odd-order nonidentity element of `K` has centralizer contained in
`K`: TI first puts the centralizer in `H`, while every element of `H \ K`
inverts `K`. -/
private theorem centralizer_le_K_of_mem_K_of_ne_one_of_odd_order
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {a : G}
    (haK : a ∈ h.K) (hane : a ≠ 1) (haOdd : Odd (orderOf a)) :
    Subgroup.centralizer ({a} : Set G) ≤ h.K := by
  intro c hc
  have hcomm : Commute c a :=
    Subgroup.mem_centralizer_singleton_iff.mp hc
  have hcH : c ∈ h.H :=
    mem_H_of_commute_mem_K_of_ne_one h haK hane hcomm
  by_contra hcK
  have hinv : c * a * c⁻¹ = a⁻¹ :=
    h.conjugates_eq_inv_of_mem_H_not_mem_K hcH hcK haK
  have hfix : c * a * c⁻¹ = a := by
    rw [hcomm.eq]
    simp
  have haInv : a = a⁻¹ := hfix.symm.trans hinv
  have haSq : a ^ 2 = 1 := by
    have hmul := congrArg (fun z : G => z * a) haInv
    simpa [pow_two] using hmul
  have haOrder : orderOf a = 2 := orderOf_eq_prime haSq hane
  apply haOdd.not_two_dvd_nat
  rw [haOrder]

/-- Once one residual centralizer is known to be a `p`-group, all residual
centralizers are `p`-groups because they have the same order `2k-1`. -/
private theorem bender_3_6_residual_centralizer_isPGroup_fixedPrime
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p) {y : G}
    (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G)))
    {z : G} (hz : z ∈ bswResidualSet h F) :
    IsPGroup p (Subgroup.centralizer ({z} : Set G)) := by
  let : Fact p.Prime := ⟨hpPrime⟩
  obtain ⟨n, hn⟩ := hyP.exists_card_eq
  apply IsPGroup.of_card (n := n)
  calc
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
        2 * Nat.card h.K - 1 :=
      bender_3_5_residual_centralizer_card
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex hz
    _ = Nat.card (Subgroup.centralizer ({y} : Set G)) :=
      (bender_3_5_residual_centralizer_card
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy).symm
    _ = p ^ n := hn

/-- Commutativity pulls back along an injective homomorphism when the image
of the subgroup lies in a commutative subgroup. -/
private theorem isMulCommutative_of_map_le_commutative
    {H G : Type u} [Group H] [Group G]
    (S : Subgroup H) (f : H →* G) (hf : Function.Injective f)
    (D : Subgroup G) (hDcomm : IsMulCommutative D)
    (hmap : S.map f ≤ D) : IsMulCommutative S := by
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  apply hf
  change f ((a : H) * (b : H)) = f ((b : H) * (a : H))
  rw [map_mul, map_mul]
  have haD : f (a : H) ∈ D := hmap ⟨a, a.property, rfl⟩
  have hbD : f (b : H) ∈ D := hmap ⟨b, b.property, rfl⟩
  exact congrArg Subtype.val
    (hDcomm.is_comm.comm (⟨f (a : H), haD⟩ : D)
      (⟨f (b : H), hbD⟩ : D))

/-- Burnside transfer, packaged in the form used by Bender 3.6: if all
Sylow normalizers away from `p` are commutative, then the Sylow `p`-subgroup
is normal and the quotient by it is commutative. -/
private theorem sylow_normal_and_quotient_commutative_of_commutative_sylow_normalizers
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (P : Sylow p H)
    (hlocal : ∀ (q : Nat.Primes), q.val ∣ Nat.card H → q.val ≠ p →
      ∃ R : Sylow q.val H,
        IsMulCommutative
          (Subgroup.normalizer ((R : Subgroup H) : Set H))) :
    (P : Subgroup H).Normal ∧ commutator H ≤ (P : Subgroup H) := by
  classical
  let I : Type := {q : Nat.Primes // q.val ∣ Nat.card H ∧ q.val ≠ p}
  let C : Subgroup H := ⨅ q : I, pPrimeCore q.val H
  have hP_le_C : (P : Subgroup H) ≤ C := by
    intro x hx
    rw [Subgroup.mem_iInf]
    intro q
    have : Fact q.val.val.Prime := ⟨q.val.property⟩
    have hq_not_dvd_P : ¬ q.val.val ∣ Nat.card (P : Subgroup H) := by
      intro hq_dvd
      rcases P.isPGroup'.exists_card_eq with ⟨n, hcardP⟩
      have hq_dvd_pow : q.val.val ∣ p ^ n := by
        simpa [hcardP] using hq_dvd
      have hq_eq_p : q.val.val = p :=
        Nat.prime_eq_prime_of_dvd_pow
          q.val.property (Fact.out : p.Prime) hq_dvd_pow
      exact q.property.2 hq_eq_p
    obtain ⟨R, hRcomm⟩ := hlocal q.val q.property.1 q.property.2
    have hRcenter : (R : Subgroup H) ≤
        centerIn (G := H)
          (Subgroup.normalizer ((R : Subgroup H) : Set H)) := by
      intro r hr
      refine ⟨Subgroup.le_normalizer hr, ?_⟩
      change r ∈ Subgroup.centralizer
        (Subgroup.normalizer ((R : Subgroup H) : Set H) : Set H)
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      let : IsMulCommutative
          (Subgroup.normalizer ((R : Subgroup H) : Set H)) := hRcomm
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm
          (M := Subgroup.normalizer ((R : Subgroup H) : Set H))).comm
            ⟨n, hn⟩ ⟨r, Subgroup.le_normalizer hr⟩)
    have hcomp : HasNormalPComplement q.val H :=
      hasNormalPComplement_of_sylow_le_center_normalizer
        q.val R hRcenter
    exact section10_subgroup_le_pPrimeCore_of_hasNormalPComplement_of_not_dvd
      (H := H) (p := q.val.val) (B := (P : Subgroup H))
      hcomp hq_not_dvd_P hx
  have hCnormal : C.Normal := by
    simpa [C, I] using
      Subgroup.normal_iInf_normal (fun q : I =>
        (inferInstance : (pPrimeCore q.val.val H).Normal))
  have hCp : IsPGroup p C := by
    refine (IsPGroup.iff_card (p := p) (G := C)).2 ?_
    have hcard_pos : Nat.card C ≠ 0 := Nat.card_pos.ne'
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hcard_pos ?_⟩
    intro q hqprime hq_dvd
    by_cases hqp : q = p
    · exact hqp
    · exfalso
      let q' : Nat.Primes := ⟨q, hqprime⟩
      have hqH : q'.val ∣ Nat.card H :=
        hq_dvd.trans (Subgroup.card_subgroup_dvd_card C)
      let iq : I := ⟨q', hqH, by simpa [q'] using hqp⟩
      have hC_le_core : C ≤ pPrimeCore q H := by
        change C ≤ (fun q : I => pPrimeCore q.val.val H) iq
        exact iInf_le _ iq
      have hq_core : q ∣ Nat.card (pPrimeCore q H) :=
        hq_dvd.trans (Subgroup.card_dvd_of_le hC_le_core)
      have : Fact q.Prime := ⟨hqprime⟩
      exact ((hqprime.coprime_iff_not_dvd).1
        (pPrimeCore_coprime_card (G := H) (p := q))) hq_core
  have hC_eq_P : C = (P : Subgroup H) :=
    P.is_maximal' hCp hP_le_C
  have hPnormal : (P : Subgroup H).Normal := by
    rw [← hC_eq_P]
    exact hCnormal
  refine ⟨hPnormal, ?_⟩
  rw [← hC_eq_P]
  intro x hx
  rw [Subgroup.mem_iInf]
  intro q
  have : Fact q.val.val.Prime := ⟨q.val.property⟩
  obtain ⟨R, hRcomm⟩ := hlocal q.val q.property.1 q.property.2
  have hRcenter : (R : Subgroup H) ≤
      centerIn (G := H)
        (Subgroup.normalizer ((R : Subgroup H) : Set H)) := by
    intro r hr
    refine ⟨Subgroup.le_normalizer hr, ?_⟩
    change r ∈ Subgroup.centralizer
      (Subgroup.normalizer ((R : Subgroup H) : Set H) : Set H)
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    let : IsMulCommutative
        (Subgroup.normalizer ((R : Subgroup H) : Set H)) := hRcomm
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm
        (M := Subgroup.normalizer ((R : Subgroup H) : Set H))).comm
          ⟨n, hn⟩ ⟨r, Subgroup.le_normalizer hr⟩)
  have hcomp : HasNormalPComplement q.val H :=
    hasNormalPComplement_of_sylow_le_center_normalizer q.val R hRcenter
  have hRcomm' : IsMulCommutative R := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    let : IsMulCommutative
        (Subgroup.normalizer ((R : Subgroup H) : Set H)) := hRcomm
    exact congrArg
      (fun z : Subgroup.normalizer ((R : Subgroup H) : Set H) => (z : H))
      (hRcomm.is_comm.comm
        ⟨a, Subgroup.le_normalizer a.property⟩
        ⟨b, Subgroup.le_normalizer b.property⟩)
  let e : (H ⧸ pPrimeCore q.val.val H) ≃* (R : Subgroup H) :=
    quotientPPrimeCoreEquivSylowOfHasNormalPComplement hcomp R
  have hquotcomm : IsMulCommutative
      (H ⧸ pPrimeCore q.val.val H) := by
    rw [isMulCommutative_iff]
    intro a b
    apply e.injective
    simp only [map_mul]
    exact hRcomm'.is_comm.comm (e a) (e b)
  exact
    (Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquotcomm) hx

/-- Frattini's argument in the form needed after transfer in Bender 3.6. -/
private theorem sup_normalizer_eq_top_of_commutator_le
    {H : Type u} [Group H] [Finite H]
    {p r : ℕ} [Fact r.Prime]
    (P : Sylow p H) (R : Sylow r H)
    (hcomm : commutator H ≤ (P : Subgroup H)) :
    (P : Subgroup H) ⊔
      Subgroup.normalizer ((R : Subgroup H) : Set H) = ⊤ := by
  let C : Subgroup H := (P : Subgroup H) ⊔ (R : Subgroup H)
  have hCnormal : C.Normal :=
    Subgroup.Normal.of_commutator_le H (hcomm.trans le_sup_left)
  let : C.Normal := hCnormal
  let RC : Sylow r C := R.subtype le_sup_right
  have hfrattini :
      Subgroup.normalizer
          (((RC : Subgroup C).map C.subtype : Subgroup H) : Set H) ⊔ C = ⊤ :=
    Sylow.normalizer_sup_eq_top RC
  have hRCmap : (RC : Subgroup C).map C.subtype = (R : Subgroup H) := by
    simpa [RC, C] using
      (Subgroup.map_subgroupOf_eq_of_le
        (H := (R : Subgroup H)) (K := C) le_sup_right)
  rw [hRCmap] at hfrattini
  rw [← hfrattini]
  change (P : Subgroup H) ⊔
      Subgroup.normalizer ((R : Subgroup H) : Set H) =
    Subgroup.normalizer ((R : Subgroup H) : Set H) ⊔
      ((P : Subgroup H) ⊔ (R : Subgroup H))
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_right) le_sup_left
  · exact sup_le le_sup_right
      (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right))

/-- Bender 3.6, first step: the normalizer of a nontrivial subgroup at the
residual prime has odd order. -/
private theorem bender_3_6_normalizer_card_odd
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFCent : ∀ z : G, z ∈ F → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXp : IsPGroup p X) :
    Odd (Nat.card (Subgroup.normalizer (X : Set G))) := by
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  rw [← Nat.not_even_iff_odd]
  intro hNeven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨uN, huOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := N) 2 hNeven.two_dvd
  let u : G := uN
  have huOrderG : orderOf u = 2 := by
    simpa [u, Subgroup.orderOf_coe] using huOrder
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at huOrderG
    omega
  have huSq : u ^ 2 = 1 := by
    rw [← huOrderG]
    exact pow_orderOf_eq_one u
  have huI : IsInvolution u := ⟨huNe, huSq⟩
  have huNorm : u ∈ Subgroup.normalizer (X : Set G) := uN.property
  by_cases hcent : X ≤ Subgroup.centralizer ({u} : Set G)
  · obtain ⟨xX, hxXne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
    let x : G := xX
    have hxne : x ≠ 1 := by
      intro hxOne
      exact hxXne (Subtype.ext hxOne)
    have hxResidual : x ∈ bswResidualSet h F :=
      mem_bswResidualSet_of_mem_residualPrimeSubgroup
        h F hFcard hpPrime hpCop X hXp xX.property hxne
    have hxu : Commute x u :=
      Subgroup.mem_centralizer_singleton_iff.mp (hcent xX.property)
    have huC : u ∈ Subgroup.centralizer ({x} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxu.symm
    let uC : Subgroup.centralizer ({x} : Set G) := ⟨u, huC⟩
    have huCOrder : orderOf uC = 2 := by
      simpa [uC, Subgroup.orderOf_coe] using huOrderG
    have htwoDvd : 2 ∣
        Nat.card (Subgroup.centralizer ({x} : Set G)) := by
      rw [← huCOrder]
      exact orderOf_dvd_natCard uC
    have hCcard :
        Nat.card (Subgroup.centralizer ({x} : Set G)) =
          2 * Nat.card h.K - 1 :=
      bender_3_5_residual_centralizer_card
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex hxResidual
    have hqOdd : Odd (2 * Nat.card h.K - 1) := by
      refine ⟨Nat.card h.K - 1, ?_⟩
      omega
    exact hqOdd.not_two_dvd_nat (by rwa [hCcard] at htwoDvd)
  · obtain ⟨x, hxX, hxne, hux⟩ :=
      exists_nontrivial_inverted_of_involution_normalizes_not_centralizes
        huI huNorm hcent
    have hxResidual : x ∈ bswResidualSet h F :=
      mem_bswResidualSet_of_mem_residualPrimeSubgroup
        h F hFcard hpPrime hpCop X hXp hxX hxne
    apply bender_3_5_residual_not_isConj_inv
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hxResidual
    exact isConj_iff.mpr ⟨u, hux⟩

/-- Bender 3.6, local transfer input: for a prime `r ≠ p`, the normalizer
inside `N_G(X)` of a Sylow `r`-subgroup is commutative. -/
private theorem bender_3_6_sylow_normalizer_commutative
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFcomm : IsMulCommutative F)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p) {y : G}
    (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G)))
    (X : Subgroup G)
    (hNodd : Odd (Nat.card (Subgroup.normalizer (X : Set G))))
    {r : ℕ} (hrPrime : Nat.Prime r) (hrne : r ≠ p)
    (hrN : r ∣ Nat.card (Subgroup.normalizer (X : Set G)))
    (R : Sylow r (Subgroup.normalizer (X : Set G))) :
    IsMulCommutative
        (Subgroup.normalizer
          ((R : Subgroup (Subgroup.normalizer (X : Set G))) :
            Set (Subgroup.normalizer (X : Set G)))) ∧
      ((∃ g : G,
          (Subgroup.normalizer
              ((R : Subgroup (Subgroup.normalizer (X : Set G))) :
                Set (Subgroup.normalizer (X : Set G)))).map
              (Subgroup.normalizer (X : Set G)).subtype ≤ h.K.conjBy g) ∨
        ∃ g : G,
          (Subgroup.normalizer
              ((R : Subgroup (Subgroup.normalizer (X : Set G))) :
                Set (Subgroup.normalizer (X : Set G)))).map
              (Subgroup.normalizer (X : Set G)).subtype ≤ F.conjBy g) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let R0 : Subgroup N := (R : Subgroup N)
  let : Fact p.Prime := ⟨hpPrime⟩
  let : Fact r.Prime := ⟨hrPrime⟩
  have hRne : R0 ≠ ⊥ := by
    simpa [R0, N] using R.ne_bot_of_dvd_card hrN
  let : Nontrivial R0 :=
    (Subgroup.nontrivial_iff_ne_bot R0).mpr hRne
  have hcenterNontrivial : Nontrivial (Subgroup.center R0) :=
    R.isPGroup'.center_nontrivial
  have hcenterNe : Subgroup.center R0 ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (Subgroup.center R0)).mp
      hcenterNontrivial
  obtain ⟨zC, hzCne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hcenterNe
  let zR : R0 := zC
  let zN : N := zR
  let z : G := zN
  have hzRne : zR ≠ 1 := by
    intro hzOne
    exact hzCne (Subtype.ext hzOne)
  have hzNne : zN ≠ 1 := by
    intro hzOne
    exact hzRne (Subtype.ext hzOne)
  have hzne : z ≠ 1 := by
    intro hzOne
    exact hzNne (Subtype.ext hzOne)
  have hzOrderOdd : Odd (orderOf z) := by
    have hzNOrderOdd : Odd (orderOf zN) :=
      hNodd.of_dvd_nat (orderOf_dvd_natCard zN)
    simpa [z, zN, Subgroup.orderOf_coe] using hzNOrderOdd
  let RG : Subgroup G := R0.map N.subtype
  have hzRG : z ∈ RG := by
    exact ⟨zN, zR.property, rfl⟩
  have hRGne : RG ≠ ⊥ := by
    intro hbot
    have hzOne : z = 1 := by
      have : z ∈ (⊥ : Subgroup G) := by simpa [hbot] using hzRG
      simpa using this
    exact hzne hzOne
  have hRGcent : RG ≤ Subgroup.centralizer ({z} : Set G) := by
    intro a ha
    rcases ha with ⟨aN, haR, rfl⟩
    let aR : R0 := ⟨aN, haR⟩
    have hcommR : aR * zR = zR * aR :=
      Subgroup.mem_center_iff.mp zC.property aR
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg (fun w : R0 => (((w : N) : G))) hcommR
  have hzNotResidual : z ∉ bswResidualSet h F := by
    intro hzResidual
    have hzP : IsPGroup p (Subgroup.centralizer ({z} : Set G)) :=
      bender_3_6_residual_centralizer_isPGroup_fixedPrime
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex
          hpPrime hy hyP hzResidual
    let zZ : Subgroup.centralizer ({z} : Set G) :=
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl z)⟩
    have hzZne : zZ ≠ 1 := by
      intro hzOne
      exact hzne (congrArg Subtype.val hzOne)
    have hpOrder : p ∣ orderOf z := by
      simpa [zZ, Subgroup.orderOf_coe] using hzP.dvd_orderOf hzZne
    obtain ⟨n, hn⟩ :=
      (IsPGroup.iff_orderOf (p := r) (G := R0)).mp R.isPGroup' zR
    have hzOrder : orderOf z = r ^ n := by
      simpa [z, zN, zR, Subgroup.orderOf_coe] using hn
    have hpPow : p ∣ r ^ n := by rwa [hzOrder] at hpOrder
    exact hrne (Nat.prime_eq_prime_of_dvd_pow hpPrime hrPrime hpPow).symm
  have hoccupied :
      z ∈ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    by_contra hnot
    apply hzNotResidual
    rw [bswResidualSet, Set.mem_compl_iff]
    exact hnot
  have finish :
      ∀ (D E : Subgroup G),
        IsMulCommutative D →
        D ≤ E →
        Nat.card E = 2 * Nat.card D →
        Suzuki.VI.IsTISubsetRelative E (D : Set G) →
        ∀ g : G, RG ≤ D.conjBy g →
          IsMulCommutative (Subgroup.normalizer (R0 : Set N)) ∧
            (Subgroup.normalizer (R0 : Set N)).map N.subtype ≤
              D.conjBy g := by
    intro D E hDcomm hDE hEcard hDTI g hRGleDg
    let L : Subgroup N := Subgroup.normalizer (R0 : Set N)
    let LG : Subgroup G := L.map N.subtype
    have hLGleNorm : LG ≤ Subgroup.normalizer (RG : Set G) := by
      simpa [L, LG, RG] using R0.le_normalizer_map N.subtype
    have hNormLe : Subgroup.normalizer (RG : Set G) ≤ E.conjBy g :=
      normalizer_le_conjBy_of_relativeTI
        E D hDTI g RG hRGne hRGleDg
    have hLGleEg : LG ≤ E.conjBy g := hLGleNorm.trans hNormLe
    have hLodd : Odd (Nat.card L) :=
      hNodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)
    have hLGcard : Nat.card LG = Nat.card L := by
      simpa [LG] using
        (Subgroup.card_map_of_injective
          (K := L) (f := N.subtype) Subtype.coe_injective)
    have hLGodd : Odd (Nat.card LG) := by rwa [hLGcard]
    have hDgEg : D.conjBy g ≤ E.conjBy g :=
      Subgroup.map_mono hDE
    have hEgcard :
        Nat.card (E.conjBy g) = 2 * Nat.card (D.conjBy g) := by
      rw [bsw_natCard_conjBy, bsw_natCard_conjBy, hEcard]
    have hLGleDg : LG ≤ D.conjBy g :=
      odd_subgroup_le_of_card_eq_two_mul
        (D.conjBy g) (E.conjBy g) LG
          hDgEg hLGleEg hEgcard hLGodd
    have hDgcomm : IsMulCommutative (D.conjBy g) := by
      let : IsMulCommutative D := hDcomm
      change IsMulCommutative
        (D.map (MulAut.conj g).toMonoidHom)
      infer_instance
    exact ⟨isMulCommutative_of_map_le_commutative
      L N.subtype Subtype.coe_injective (D.conjBy g) hDgcomm hLGleDg,
      hLGleDg⟩
  simp only [Set.mem_union, Set.mem_singleton_iff] at hoccupied
  rcases hoccupied with (hzOne | hzK) | hzF
  · exact (hzne hzOne).elim
  · rcases hzK with ⟨a, haK, hane, g, hz⟩
    have hconj : IsConj a z := isConj_iff.mpr ⟨g, hz.symm⟩
    have haOdd : Odd (orderOf a) := by
      rw [orderOf_eq_of_isConj hconj]
      exact hzOrderOdd
    have hcenta : Subgroup.centralizer ({a} : Set G) ≤ h.K :=
      centralizer_le_K_of_mem_K_of_ne_one_of_odd_order
        h haK hane haOdd
    have hcentz : Subgroup.centralizer ({z} : Set G) ≤ h.K.conjBy g :=
      centralizer_le_conjBy_of_eq_conj h.K hcenta g hz
    have hKleH : h.K ≤ h.H := by
      rw [h.H_eq_join]
      exact le_sup_left
    obtain ⟨hcomm, hplace⟩ :=
      finish h.K h.H h.K_commutative hKleH h.card_H
        h.isTISubsetRelative g (hRGcent.trans hcentz)
    exact ⟨hcomm, Or.inl ⟨g, hplace⟩⟩
  · rcases hzF with ⟨a, haF, hane, g, hz⟩
    have hcenta : Subgroup.centralizer ({a} : Set G) ≤ F := by
      rw [hFCent a haF hane]
    have hcentz : Subgroup.centralizer ({z} : Set G) ≤ F.conjBy g :=
      centralizer_le_conjBy_of_eq_conj F hcenta g hz
    have hMcard' :
        Nat.card (Subgroup.normalizer (F : Set G)) = 2 * Nat.card F := by
      rw [hMcard, hFcard]
    obtain ⟨hcomm, hplace⟩ :=
      finish F (Subgroup.normalizer (F : Set G))
        hFcomm Subgroup.le_normalizer hMcard' hFTI g
          (hRGcent.trans hcentz)
    exact ⟨hcomm, Or.inr ⟨g, hplace⟩⟩

/-- Bender 3.6 transfer conclusion: a Sylow `p`-subgroup of `N_G(X)` is
normal, and the commutator subgroup of `N_G(X)` lies in it. -/
private theorem bender_3_6_sylow_normal_and_commutator_le
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFcomm : IsMulCommutative F)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    {y : G} (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G)))
    (X : Subgroup G) (hXne : X ≠ ⊥) (hXp : IsPGroup p X)
    (P : Sylow p (Subgroup.normalizer (X : Set G))) :
    (P : Subgroup (Subgroup.normalizer (X : Set G))).Normal ∧
      commutator (Subgroup.normalizer (X : Set G)) ≤
        (P : Subgroup (Subgroup.normalizer (X : Set G))) := by
  classical
  let : Fact p.Prime := ⟨hpPrime⟩
  have hNodd : Odd
      (Nat.card (Subgroup.normalizer (X : Set G))) :=
    bender_3_6_normalizer_card_odd
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex
        hpPrime hpCop X hXne hXp
  apply
    sylow_normal_and_quotient_commutative_of_commutative_sylow_normalizers P
  intro q hqN hqne
  let : Fact q.val.Prime := ⟨q.property⟩
  let R : Sylow q.val (Subgroup.normalizer (X : Set G)) :=
    Classical.choice Sylow.nonempty
  refine ⟨R, ?_⟩
  exact (bender_3_6_sylow_normalizer_commutative
    h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
      hpPrime hy hyP X hNodd q.property hqne hqN R).1

/-- Every `p`-subgroup lies in a fixed normal Sylow `p`-subgroup. -/
private theorem isPGroup_le_normal_sylow
    {H : Type u} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (hPnormal : (P : Subgroup H).Normal)
    (X : Subgroup H) (hXp : IsPGroup p X) : X ≤ (P : Subgroup H) := by
  let : Unique (Sylow p H) := Sylow.unique_of_normal P hPnormal
  obtain ⟨Q, hXQ⟩ := hXp.exists_le_sylow
  have hQP : Q = P := Subsingleton.elim Q P
  simpa [hQP] using hXQ

/-- Strict containment of finite subgroups strictly increases cardinality. -/
private theorem natCard_lt_of_subgroup_lt
    {H : Type u} [Group H] [Finite H]
    {A B : Subgroup H} (hAB : A < B) : Nat.card A < Nat.card B := by
  have hle : Nat.card A ≤ Nat.card B := Subgroup.card_le_of_le hAB.le
  refine lt_of_le_of_ne hle ?_
  intro heq
  exact hAB.ne
    (Subgroup.eq_of_le_of_card_ge hAB.le (Nat.le_of_eq heq.symm))

/-- Bender 3.7 in generic form: if every nontrivial `p`-subgroup normalizer
has a normal Sylow `p`-subgroup, then distinct ambient Sylow `p`-subgroups
are disjoint. -/
private theorem sylow_disjoint_of_normal_local_sylow
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hlocal : ∀ (X : Subgroup G), X ≠ ⊥ → IsPGroup p X →
      ∀ S : Sylow p (Subgroup.normalizer (X : Set G)),
        (S : Subgroup (Subgroup.normalizer (X : Set G))).Normal) :
    ∀ P Q : Sylow p G, P ≠ Q →
      Disjoint (P : Subgroup G) (Q : Subgroup G) := by
  classical
  intro P Q hPQ
  rw [disjoint_iff]
  by_contra hPQinf
  let Pair := {pq : Sylow p G × Sylow p G // pq.1 ≠ pq.2}
  let score : Pair → ℕ := fun pq =>
    Nat.card ↥((pq.1.1 : Subgroup G) ⊓ (pq.1.2 : Subgroup G))
  let : Nonempty Pair := ⟨⟨(P, Q), hPQ⟩⟩
  obtain ⟨pq, hpqMax⟩ := Finite.exists_max score
  let P₁ : Sylow p G := pq.1.1
  let P₂ : Sylow p G := pq.1.2
  let X : Subgroup G := (P₁ : Subgroup G) ⊓ (P₂ : Subgroup G)
  have hPQscore :
      Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤ Nat.card X := by
    simpa [score, X, P₁, P₂] using
      hpqMax (⟨(P, Q), hPQ⟩ : Pair)
  have hXne : X ≠ ⊥ := by
    intro hXbot
    have hcardOne : Nat.card X = 1 := by simp [hXbot]
    have hcurrOne :
        Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ≤ 1 := by
      simpa [hcardOne] using hPQscore
    apply hPQinf
    by_contra hne
    exact (Nat.not_lt_of_ge hcurrOne)
      (((P : Subgroup G) ⊓ (Q : Subgroup G)).one_lt_card_iff_ne_bot.mpr hne)
  have hP₁neP₂ : P₁ ≠ P₂ := by
    simpa [P₁, P₂] using pq.property
  have hXltP₁ : X < (P₁ : Subgroup G) := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro hEq
    have hP₁leP₂ : (P₁ : Subgroup G) ≤ (P₂ : Subgroup G) := by
      rw [← hEq]
      exact inf_le_right
    have hP₂eqP₁ : (P₂ : Subgroup G) = (P₁ : Subgroup G) :=
      P₁.is_maximal' P₂.isPGroup' hP₁leP₂
    exact hP₁neP₂ (Sylow.ext hP₂eqP₁.symm)
  have hXltP₂ : X < (P₂ : Subgroup G) := by
    refine lt_of_le_of_ne inf_le_right ?_
    intro hEq
    have hP₂leP₁ : (P₂ : Subgroup G) ≤ (P₁ : Subgroup G) := by
      rw [← hEq]
      exact inf_le_left
    have hP₁eqP₂ : (P₁ : Subgroup G) = (P₂ : Subgroup G) :=
      P₂.is_maximal' P₁.isPGroup' hP₂leP₁
    exact hP₁neP₂ (Sylow.ext hP₁eqP₂)
  have hXp : IsPGroup p X := P₁.isPGroup'.to_le inf_le_left
  obtain ⟨Y₁, hXY₁, hY₁P₁, hY₁N, hY₁p⟩ :=
    section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
      P₁.isPGroup' hXltP₁
  obtain ⟨Y₂, hXY₂, hY₂P₂, hY₂N, hY₂p⟩ :=
    section10_exists_pSubgroup_gt_le_normalizer_of_lt_pgroup
      P₂.isPGroup' hXltP₂
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let S : Sylow p N := default
  have hSnormal : (S : Subgroup N).Normal := hlocal X hXne hXp S
  have hY₁subp : IsPGroup p (Y₁.subgroupOf N) :=
    hY₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hY₁N).symm
  have hY₂subp : IsPGroup p (Y₂.subgroupOf N) :=
    hY₂p.of_equiv (Subgroup.subgroupOfEquivOfLe hY₂N).symm
  have hY₁subS : Y₁.subgroupOf N ≤ (S : Subgroup N) :=
    isPGroup_le_normal_sylow S hSnormal (Y₁.subgroupOf N) hY₁subp
  have hY₂subS : Y₂.subgroupOf N ≤ (S : Subgroup N) :=
    isPGroup_le_normal_sylow S hSnormal (Y₂.subgroupOf N) hY₂subp
  let SG : Subgroup G := (S : Subgroup N).map N.subtype
  have hY₁SG : Y₁ ≤ SG := by
    have hmap : (Y₁.subgroupOf N).map N.subtype ≤ SG :=
      Subgroup.map_mono hY₁subS
    rw [← Subgroup.map_subgroupOf_eq_of_le hY₁N]
    exact hmap
  have hY₂SG : Y₂ ≤ SG := by
    have hmap : (Y₂.subgroupOf N).map N.subtype ≤ SG :=
      Subgroup.map_mono hY₂subS
    rw [← Subgroup.map_subgroupOf_eq_of_le hY₂N]
    exact hmap
  have hSGp : IsPGroup p SG := S.isPGroup'.map N.subtype
  obtain ⟨P₃, hSGP₃⟩ := hSGp.exists_le_sylow
  have hXP₁P₃ : X < (P₁ : Subgroup G) ⊓ (P₃ : Subgroup G) :=
    hXY₁.trans_le (le_inf hY₁P₁ (hY₁SG.trans hSGP₃))
  have hXP₂P₃ : X < (P₂ : Subgroup G) ⊓ (P₃ : Subgroup G) :=
    hXY₂.trans_le (le_inf hY₂P₂ (hY₂SG.trans hSGP₃))
  have hP₃eqP₁ : P₃ = P₁ := by
    by_contra hne
    have hmax := hpqMax (⟨(P₁, P₃), fun h => hne h.symm⟩ : Pair)
    have hcardlt := natCard_lt_of_subgroup_lt hXP₁P₃
    exact
      (not_lt_of_ge (by simpa [score, X, P₁, P₂] using hmax)) hcardlt
  have hP₃eqP₂ : P₃ = P₂ := by
    by_contra hne
    have hmax := hpqMax (⟨(P₂, P₃), fun h => hne h.symm⟩ : Pair)
    have hcardlt := natCard_lt_of_subgroup_lt hXP₂P₃
    exact
      (not_lt_of_ge (by simpa [score, X, P₁, P₂] using hmax)) hcardlt
  exact hP₁neP₂ (hP₃eqP₁.symm.trans hP₃eqP₂)

/-- Pairwise disjointness of distinct Sylow subgroups, packaged as Suzuki's
relative-TI structure on one Sylow subgroup. -/
private theorem sylow_isTISubsetRelative_of_pairwise_disjoint
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hPne : (P : Subgroup G) ≠ ⊥)
    (hdisj : ∀ Q : Sylow p G, P ≠ Q →
      Disjoint (P : Subgroup G) (Q : Subgroup G)) :
    Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer ((P : Subgroup G) : Set G))
      ((P : Subgroup G) : Set G) := by
  have hPnontrivial : ∃ x : G, x ∈ (P : Subgroup G) ∧ x ≠ 1 := by
    obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
    exact ⟨x, x.property, fun hx => hxne (Subtype.ext hx)⟩
  apply
    (Suzuki.VI.suzuki_ch6_proposition_2_8
      (Subgroup.normalizer ((P : Subgroup G) : Set G))
      ((P : Subgroup G) : Set G)
      (fun _ hx => Subgroup.le_normalizer hx) le_rfl hPnontrivial).2
  intro g hg z hz
  have hPgNe : P ≠ g • P := by
    intro hEq
    apply hg
    exact Sylow.smul_eq_iff_mem_normalizer.mp hEq.symm
  have hzPg : z ∈ (g • P : Sylow p G) := by
    rcases hz.1 with ⟨x, hxP, rfl⟩
    change g * x * g⁻¹ ∈
      (P : Subgroup G).map (MulAut.conj g).toMonoidHom
    exact ⟨x, hxP, rfl⟩
  have hzOne :=
    Subgroup.disjoint_def.mp (hdisj (g • P) hPgNe) hz.2 hzPg
  simpa using hzOne

/-- Bender 3.7: an ambient Sylow subgroup at the residual prime is a
relative-TI subgroup of its normalizer. -/
private theorem bender_3_7_sylow_isTISubsetRelative
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFcomm : IsMulCommutative F)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    {y : G} (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G)))
    (P : Sylow p G) (hpG : p ∣ Nat.card G) :
    Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer ((P : Subgroup G) : Set G))
      ((P : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hpPrime⟩
  apply sylow_isTISubsetRelative_of_pairwise_disjoint P
    (P.ne_bot_of_dvd_card hpG)
  apply sylow_disjoint_of_normal_local_sylow
  intro X hXne hXp S
  exact
    (bender_3_6_sylow_normal_and_commutator_le
      h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
        hpPrime hpCop hy hyP X hXne hXp S).1

/-- Relative fusion into a centralizer representative makes a subgroup
commutative when every punctured element belongs to one of the two inverse
ambient conjugacy classes of that representative. -/
private theorem bender_sylow_commutative_of_two_inverse_classes
    {G : Type u} [Group G]
    (Q : Subgroup G) (y : G)
    (hQeq : Q = Subgroup.centralizer ({y} : Set G))
    (hyQ : y ∈ Q)
    (hTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (Q : Set G)) (Q : Set G))
    (hclass : ∀ a : G, a ∈ Q → a ≠ 1 →
      IsConj a y ∨ IsConj a y⁻¹) :
    IsMulCommutative Q := by
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  by_cases haOne : (a : G) = 1
  · simp [haOne]
  rcases hclass (a : G) a.property haOne with hay | hay
  · obtain ⟨n, hn⟩ := hTI.2.2.1 a.property hyQ (isConj_iff.mp hay)
    have hnbQ : (n : G) * (b : G) * (n : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp n.property (b : G)).mp b.property
    have hQleC : Q ≤ Subgroup.centralizer ({y} : Set G) := le_of_eq hQeq
    have hycomm : Commute y ((n : G) * (b : G) * (n : G)⁻¹) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQleC hnbQ)).symm
    have hconjcomm : Commute
        ((n : G) * (a : G) * (n : G)⁻¹)
        ((n : G) * (b : G) * (n : G)⁻¹) := by
      rw [hn]
      exact hycomm
    simpa [mul_assoc] using (hconjcomm.conj (n : G)⁻¹).eq
  · obtain ⟨n, hn⟩ :=
      hTI.2.2.1 a.property (Q.inv_mem hyQ) (isConj_iff.mp hay)
    have hnbQ : (n : G) * (b : G) * (n : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp n.property (b : G)).mp b.property
    have hQleC : Q ≤ Subgroup.centralizer ({y} : Set G) := le_of_eq hQeq
    have hycomm : Commute y ((n : G) * (b : G) * (n : G)⁻¹) :=
      (Subgroup.mem_centralizer_singleton_iff.mp (hQleC hnbQ)).symm
    have hyinvcomm : Commute y⁻¹ ((n : G) * (b : G) * (n : G)⁻¹) :=
      hycomm.inv_left
    have hconjcomm : Commute
        ((n : G) * (a : G) * (n : G)⁻¹)
        ((n : G) * (b : G) * (n : G)⁻¹) := by
      rw [hn]
      exact hyinvcomm
    simpa [mul_assoc] using (hconjcomm.conj (n : G)⁻¹).eq

/-- If the punctured elements of an abelian self-centralizing Sylow subgroup
form exactly the two inverse ambient conjugacy classes, then its normalizer
index is half the punctured cardinality. -/
private theorem bender_sylow_normalizer_index_count
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G)
    (hPcent : ∀ x : G, x ∈ (P : Subgroup G) → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = (P : Subgroup G))
    {y : G} (hyP : y ∈ (P : Subgroup G)) (hyne : y ≠ 1)
    (hynot : ¬ IsConj y y⁻¹)
    (hclass : ∀ a : G, a ∈ (P : Subgroup G) → a ≠ 1 →
      IsConj a y ∨ IsConj a y⁻¹)
    (hTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (((P : Subgroup G)) : Set G))
      ((P : Subgroup G) : Set G)) :
    Nat.card (P : Subgroup G) - 1 =
      2 * (P.subgroupOf
        (Subgroup.normalizer (((P : Subgroup G)) : Set G))).index := by
  classical
  let N : Subgroup G := Subgroup.normalizer (((P : Subgroup G)) : Set G)
  let QN : Subgroup N := (P : Subgroup G).subgroupOf N
  let rho : N →* MulAut G := MulAut.conj.comp N.subtype
  let : MulAction N G := MulAction.compHom G rho
  let Y : SubMulAction N G :=
    { carrier := ((P : Subgroup G) : Set G) \ {1}
      smul_mem' := by
        intro n x hx
        change (n : G) * x * (n : G)⁻¹ ∈ (P : Subgroup G) ∧
          (n : G) * x * (n : G)⁻¹ ∉ ({1} : Set G)
        constructor
        · exact (Subgroup.mem_normalizer_iff.mp n.property x).mp hx.1
        · simp only [Set.mem_singleton_iff]
          intro hone
          apply hx.2
          simp only [Set.mem_singleton_iff]
          have hback := congrArg
            (fun z : G => (n : G)⁻¹ * z * (n : G)) hone
          simpa [mul_assoc] using hback }
  let Omega := Quotient (MulAction.orbitRel N Y)
  let yY : Y := ⟨y, hyP, by simpa using hyne⟩
  have hyInvP : y⁻¹ ∈ (P : Subgroup G) := (P : Subgroup G).inv_mem hyP
  have hyInvNe : y⁻¹ ≠ 1 := by simpa using hyne
  let yiY : Y := ⟨y⁻¹, hyInvP, by simpa using hyInvNe⟩
  let cy : Omega := Quotient.mk'' yY
  let cyi : Omega := Quotient.mk'' yiY
  have hsmul (n : N) (z : Y) :
      ((n • z : Y) : G) = (n : G) * (z : G) * (n : G)⁻¹ := by
    rfl
  have hquotient_eq_of_isConj
      (a b : Y) (hab : IsConj (a : G) (b : G)) :
      (Quotient.mk'' a : Omega) = Quotient.mk'' b := by
    rcases isConj_iff.mp hab with ⟨g, hg⟩
    obtain ⟨n, hn⟩ := hTI.2.2.1 a.property.1 b.property.1 ⟨g, hg⟩
    apply Quotient.sound
    show MulAction.orbitRel N Y a b
    rw [MulAction.orbitRel_apply]
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨n⁻¹, ?_⟩
    apply Subtype.ext
    rw [hsmul]
    have hback := congrArg
      (fun z : G => (n : G)⁻¹ * z * (n : G)) hn
    simpa [mul_assoc] using hback.symm
  have hcyNe : cy ≠ cyi := by
    intro heq
    apply hynot
    have hrel : MulAction.orbitRel N Y yY yiY := Quotient.exact' heq
    have horbit : yY ∈ MulAction.orbit N yiY := by
      simpa [MulAction.orbitRel_apply] using hrel
    rcases MulAction.mem_orbit_iff.mp horbit with ⟨n, hn⟩
    rw [isConj_comm]
    refine isConj_iff.mpr ⟨(n : G), ?_⟩
    calc
      (n : G) * y⁻¹ * (n : G)⁻¹ = ((n • yiY : Y) : G) :=
        (hsmul n yiY).symm
      _ = y := by simpa [yY] using congrArg Subtype.val hn
  have hall : ∀ c : Omega, c = cy ∨ c = cyi := by
    intro c
    refine Quotient.inductionOn c ?_
    intro z
    rcases hclass (z : G) z.property.1 (by simpa using z.property.2) with hz | hz
    · exact Or.inl (hquotient_eq_of_isConj z yY hz)
    · exact Or.inr (hquotient_eq_of_isConj z yiY hz)
  have hOmegaCard : Nat.card Omega = 2 := by
    apply (Nat.card_eq_two_iff' cy).2
    refine ⟨cyi, hcyNe.symm, ?_⟩
    intro c hc
    rcases hall c with rfl | h
    · exact (hc rfl).elim
    · exact h
  have hPcomm : IsMulCommutative (P : Subgroup G) := by
    rw [isMulCommutative_iff]
    intro a b
    apply Subtype.ext
    by_cases ha : (a : G) = 1
    · simp [ha]
    have hbCent : (b : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [hPcent (a : G) a.property ha]
      exact b.property
    exact (Subgroup.mem_centralizer_singleton_iff.mp hbCent).symm
  have hstab (z : Y) : MulAction.stabilizer N z = QN := by
    ext n
    constructor
    · intro hn
      have hnsmul : n • z = z := by
        simpa [MulAction.mem_stabilizer_iff] using hn
      have hncomm : Commute (n : G) (z : G) := by
        have hconj := congrArg Subtype.val hnsmul
        rw [hsmul] at hconj
        exact mul_inv_eq_iff_eq_mul.mp hconj
      have hnP : (n : G) ∈ (P : Subgroup G) := by
        rw [← hPcent (z : G) z.property.1 (by simpa using z.property.2)]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hncomm
      exact hnP
    · intro hn
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      rw [hsmul]
      have hcomm : Commute (n : G) (z : G) := by
        let : IsMulCommutative (P : Subgroup G) := hPcomm
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm
            ⟨n, hn⟩ ⟨z, z.property.1⟩)
      rw [hcomm.eq]
      simp
  have hQNcard : Nat.card QN = Nat.card (P : Subgroup G) :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe
        (H := (P : Subgroup G)) (K := N) Subgroup.le_normalizer)
  let : Fintype N := Fintype.ofFinite N
  let : Fintype Y := Fintype.ofFinite Y
  have hOrbitCard (z : Y) :
      Nat.card (MulAction.orbit N z) = QN.index := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := QN))
    calc
      Nat.card (MulAction.orbit N z) * Nat.card QN =
          Nat.card (MulAction.orbit N z) *
            Nat.card (MulAction.stabilizer N z) := by rw [hstab z]
      _ = Nat.card N := by
        simpa only [Nat.card_eq_fintype_card] using
          MulAction.card_orbit_mul_card_stabilizer_eq_card_group N z
      _ = QN.index * Nat.card QN := QN.index_mul_card.symm
  have hYcard : Nat.card Y = Nat.card (P : Subgroup G) - 1 := by
    calc
      Nat.card Y = (((P : Subgroup G) : Set G) \ {1}).ncard :=
        Nat.card_coe_set_eq _
      _ = (((P : Subgroup G) : Set G)).ncard - 1 := by
        rw [Set.ncard_sdiff_singleton_of_mem (P : Subgroup G).one_mem]
      _ = Nat.card (P : Subgroup G) - 1 := by congr 1
  let : Fintype Omega := Fintype.ofFinite Omega
  have hsumOrbit :
      Nat.card Y = ∑ omega : Omega,
        Nat.card (MulAction.orbit N (Quotient.out omega : Y)) := by
    calc
      Nat.card Y = Nat.card
          (Sigma fun omega : Omega =>
            MulAction.orbit N (Quotient.out omega : Y)) :=
        Nat.card_congr (MulAction.selfEquivSigmaOrbits N Y)
      _ = ∑ omega : Omega,
          Nat.card (MulAction.orbit N (Quotient.out omega : Y)) :=
        Nat.card_sigma
  calc
    Nat.card (P : Subgroup G) - 1 = Nat.card Y := hYcard.symm
    _ = ∑ _omega : Omega, QN.index := by
      rw [hsumOrbit]
      apply Finset.sum_congr rfl
      intro omega _
      exact hOrbitCard (Quotient.out omega : Y)
    _ = 2 * QN.index := by
      simp [← Nat.card_eq_fintype_card, hOmegaCard]
    _ = 2 * (P.subgroupOf N).index := rfl

/-- Bender 3.8 through the normalizer index calculation: a residual
centralizer is an ambient Sylow subgroup, it is abelian and self-centralizing
on its punctured elements, and its normalizer quotient has order `k - 1`. -/
private theorem bender_3_8_residual_sylow_index_data
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFcomm : IsMulCommutative F)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    {y : G} (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G))) :
    ∃ P : Sylow p G,
      (P : Subgroup G) = Subgroup.centralizer ({y} : Set G) ∧
      IsMulCommutative (P : Subgroup G) ∧
      (∀ x : G, x ∈ (P : Subgroup G) → x ≠ 1 →
        Subgroup.centralizer ({x} : Set G) = (P : Subgroup G)) ∧
      Suzuki.VI.IsTISubsetRelative
        (Subgroup.normalizer ((P : Subgroup G) : Set G))
        ((P : Subgroup G) : Set G) ∧
      (P.subgroupOf
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).index =
          Nat.card h.K - 1 := by
  classical
  let k : ℕ := Nat.card h.K
  let q : ℕ := 2 * k - 1
  let B : ℕ := 2 * k * (k - 1)
  let C : Subgroup G := Subgroup.centralizer ({y} : Set G)
  let : Fact p.Prime := ⟨hpPrime⟩
  have hk' : 4 < k := by simpa [k] using hk
  have hCcard : Nat.card C = q := by
    simpa [C, q, k] using
      bender_3_5_residual_centralizer_card
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  have hqPos : 0 < q := by
    rw [← hCcard]
    exact Nat.card_pos
  have hGcard : Nat.card G = q * B := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
        rw [h.card_H]
        simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
      _ = q * B := by
        dsimp [q, B]
        ring
  have hCindex : C.index = B := by
    apply Nat.eq_of_mul_eq_mul_left hqPos
    calc
      q * C.index = Nat.card C * C.index := by rw [hCcard]
      _ = Nat.card G := C.card_mul_index
      _ = q * B := hGcard
  have hpNotIndex : ¬ p ∣ C.index := by
    rw [hCindex]
    exact hpPrime.coprime_iff_not_dvd.mp (by simpa [B, k] using hpCop)
  let P : Sylow p G := hyP.toSylow hpNotIndex
  have hPcoe : (P : Subgroup G) = C := by
    simp [P, IsPGroup.toSylow_coe, C]
  have hyForbidden :
      y ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hy
  have hyne : y ≠ 1 := by
    intro hyone
    apply hyForbidden
    simp [hyone]
  have hyC : y ∈ C :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)
  have hyPin : y ∈ (P : Subgroup G) := by
    rw [hPcoe]
    exact hyC
  have hpCcard : p ∣ Nat.card C :=
    hyP.card_eq_or_dvd.resolve_left (by rw [hCcard]; omega)
  have hpG : p ∣ Nat.card G :=
    hpCcard.trans (Subgroup.card_subgroup_dvd_card C)
  have hPTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer ((P : Subgroup G) : Set G))
      ((P : Subgroup G) : Set G) :=
    bender_3_7_sylow_isTISubsetRelative
      h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
        hpPrime hpCop hy hyP P hpG
  have hclass : ∀ a : G, a ∈ (P : Subgroup G) → a ≠ 1 →
      IsConj a y ∨ IsConj a y⁻¹ := by
    intro a haP hane
    have haResidual : a ∈ bswResidualSet h F :=
      mem_bswResidualSet_of_mem_residualPrimeSubgroup
        h F hFcard hpPrime hpCop (P : Subgroup G) P.isPGroup'
          haP hane
    exact bender_3_5_residual_isConj_or_inv
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy haResidual
  have hPcomm : IsMulCommutative (P : Subgroup G) :=
    bender_sylow_commutative_of_two_inverse_classes
      (P : Subgroup G) y (hPcoe.trans rfl) hyPin hPTI hclass
  have hPcard : Nat.card (P : Subgroup G) = q := by
    rw [hPcoe, hCcard]
  have hPcent : ∀ x : G, x ∈ (P : Subgroup G) → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = (P : Subgroup G) := by
    intro x hxP hxne
    have hxResidual : x ∈ bswResidualSet h F :=
      mem_bswResidualSet_of_mem_residualPrimeSubgroup
        h F hFcard hpPrime hpCop (P : Subgroup G) P.isPGroup'
          hxP hxne
    have hCxcard : Nat.card (Subgroup.centralizer ({x} : Set G)) = q := by
      simpa [q, k] using
        bender_3_5_residual_centralizer_card
          h hk F hFcard hFCent hFHall hMcard hFTI hHindex hxResidual
    have hPleCx : (P : Subgroup G) ≤
        Subgroup.centralizer ({x} : Set G) := by
      intro z hzP
      rw [Subgroup.mem_centralizer_singleton_iff]
      let : IsMulCommutative (P : Subgroup G) := hPcomm
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := (P : Subgroup G))).comm
          ⟨z, hzP⟩ ⟨x, hxP⟩)
    exact (Subgroup.eq_of_le_of_card_ge hPleCx (by
      rw [hPcard, hCxcard])).symm
  have hynot : ¬ IsConj y y⁻¹ :=
    bender_3_5_residual_not_isConj_inv
      h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
  have hcount := bender_sylow_normalizer_index_count
    P hPcent hyPin hyne hynot hclass hPTI
  have hcount' :
      (2 * k - 1) - 1 =
        2 * (P.subgroupOf
          (Subgroup.normalizer ((P : Subgroup G) : Set G))).index := by
    simpa [hPcard, q] using hcount
  have hindex :
      (P.subgroupOf
        (Subgroup.normalizer ((P : Subgroup G) : Set G))).index = k - 1 := by
    have hsub : 2 * k - 1 - 1 = 2 * (k - 1) := by omega
    rw [hsub] at hcount'
    apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
    exact hcount'.symm
  exact ⟨P, by simpa [C] using hPcoe, hPcomm, hPcent, hPTI,
    by simpa [k] using hindex⟩

/-- The relative index of one factor in a disjoint normalized subgroup
product is the cardinality of the other factor. -/
private theorem subgroupOf_sup_index_eq_card_of_disjoint_of_le_normalizer
    {G : Type u} [Group G] [Finite G]
    (Q D : Subgroup G)
    (hQD : Disjoint Q D)
    (hNorm : D ≤ Subgroup.normalizer (Q : Set G)) :
    (Q.subgroupOf (Q ⊔ D)).index = Nat.card D := by
  let S : Subgroup G := Q ⊔ D
  let toSup : Q × D → S := fun z =>
    ⟨(z.1 : G) * (z.2 : G), Subgroup.mul_mem_sup z.1.2 z.2.2⟩
  have hinjective : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hQD
    exact congrArg Subtype.val hxy
  have hsurjective : Function.Surjective toSup := by
    intro z
    have hz : (z : G) ∈ (Q : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left Q D hNorm]
      exact z.2
    rcases hz with ⟨q, hq, d, hd, hqd⟩
    exact ⟨(⟨q, hq⟩, ⟨d, hd⟩), Subtype.ext hqd⟩
  have hScard : Nat.card S = Nat.card Q * Nat.card D := by
    calc
      Nat.card S = Nat.card (Q × D) :=
        Nat.card_congr (Equiv.ofBijective toSup ⟨hinjective, hsurjective⟩).symm
      _ = Nat.card Q * Nat.card D := Nat.card_prod Q D
  have hQcard : Nat.card (Q.subgroupOf S) = Nat.card Q :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := Q) (K := S) (by
        dsimp [S]
        exact le_sup_left))
  have hprod := (Q.subgroupOf S).index_mul_card
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := Q))
  calc
    (Q.subgroupOf S).index * Nat.card Q =
        (Q.subgroupOf S).index * Nat.card (Q.subgroupOf S) := by
      rw [hQcard]
    _ = Nat.card S := hprod
    _ = Nat.card Q * Nat.card D := hScard
    _ = Nat.card D * Nat.card Q := by ring

/-- Mapping the Frattini product decomposition of a subgroup normalizer back
to the ambient group. -/
private theorem map_sylow_sup_normalizer_eq_ambient_normalizer
    {G : Type u} [Group G] [Finite G]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (Q : Subgroup G) (P : Sylow p G)
    (hPQ : (P : Subgroup G) = Q)
    (R : Sylow r (Subgroup.normalizer (Q : Set G)))
    (hsup :
      ((P.subtype (hPQ.trans_le Subgroup.le_normalizer) :
          Sylow p (Subgroup.normalizer (Q : Set G))) :
          Subgroup (Subgroup.normalizer (Q : Set G))) ⊔
        Subgroup.normalizer
          ((R : Subgroup (Subgroup.normalizer (Q : Set G))) :
            Set (Subgroup.normalizer (Q : Set G))) = ⊤) :
    Subgroup.normalizer (Q : Set G) = Q ⊔
      (Subgroup.normalizer
          ((R : Subgroup (Subgroup.normalizer (Q : Set G))) :
            Set (Subgroup.normalizer (Q : Set G)))).map
        (Subgroup.normalizer (Q : Set G)).subtype := by
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let PN : Sylow p N := P.subtype (hPQ.trans_le Subgroup.le_normalizer)
  let L : Subgroup N := Subgroup.normalizer ((R : Subgroup N) : Set N)
  have hPNmap : (PN : Subgroup N).map N.subtype = Q := by
    simpa [PN, N, hPQ] using
      (Subgroup.map_subgroupOf_eq_of_le
        (H := Q) (K := Subgroup.normalizer (Q : Set G))
          Subgroup.le_normalizer)
  have htopmap : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, N.range_subtype]
  calc
    N = (⊤ : Subgroup N).map N.subtype := htopmap.symm
    _ = ((PN : Subgroup N) ⊔ L).map N.subtype := by rw [hsup]
    _ = (PN : Subgroup N).map N.subtype ⊔ L.map N.subtype := by
      rw [Subgroup.map_sup]
    _ = Q ⊔ L.map N.subtype := by rw [hPNmap]

/-- Commutativity is preserved when a subgroup of a subgroup is mapped into
the ambient group by the subtype embedding. -/
private theorem isMulCommutative_map_subtype
    {G : Type u} [Group G] (N : Subgroup G) (L : Subgroup N)
    (hLcomm : IsMulCommutative L) :
    IsMulCommutative (L.map N.subtype) := by
  rw [isMulCommutative_iff]
  intro a b
  rcases a.property with ⟨aN, haL, ha⟩
  rcases b.property with ⟨bN, hbL, hb⟩
  apply Subtype.ext
  change (a : G) * (b : G) = (b : G) * (a : G)
  rw [← ha, ← hb]
  exact congrArg (fun z : L => (((z : N) : G)))
    (hLcomm.is_comm.comm ⟨aN, haL⟩ ⟨bN, hbL⟩)

/-- A subgroup of order coprime to `p` is cardinally coprime to every finite
`p`-subgroup. -/
private theorem natCard_coprime_of_isPGroup_of_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (Q D E : Subgroup G)
    (hQp : IsPGroup p Q)
    (hpE : Nat.Coprime p (Nat.card E))
    (hDE : D ≤ E) :
    Nat.Coprime (Nat.card Q) (Nat.card D) := by
  obtain ⟨n, hQcard⟩ := IsPGroup.iff_card.mp hQp
  rw [hQcard]
  exact (hpE.pow_left n).of_dvd_right (Subgroup.card_dvd_of_le hDE)

/-- Conjugating a normalizer decomposition by the inverse conjugator moves
the placed complement back to the selected subgroup. -/
private theorem normalizer_conjBy_inv_eq_sup
    {G : Type u} [Group G]
    (Q F : Subgroup G) (g : G)
    (hN : Subgroup.normalizer (Q : Set G) = Q ⊔ F.conjBy g) :
    Subgroup.normalizer (Q.conjBy g⁻¹ : Set G) =
      Q.conjBy g⁻¹ ⊔ F := by
  have hnormMap :
      (Subgroup.normalizer (Q : Set G)).map
          (MulAut.conj g⁻¹).toMonoidHom =
        Subgroup.normalizer (Q.conjBy g⁻¹ : Set G) := by
    simpa [Subgroup.conjBy] using
      Subgroup.map_equiv_normalizer_eq Q (MulAut.conj g⁻¹)
  have hFcancel : (F.conjBy g).conjBy g⁻¹ = F := by
    simpa using Subgroup.conjBy_inv F g
  calc
    Subgroup.normalizer (Q.conjBy g⁻¹ : Set G) =
        (Subgroup.normalizer (Q : Set G)).map
          (MulAut.conj g⁻¹).toMonoidHom := hnormMap.symm
    _ = (Q ⊔ F.conjBy g).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hN]
    _ = Q.conjBy g⁻¹ ⊔ (F.conjBy g).conjBy g⁻¹ := by
      rw [Subgroup.map_sup]
      rfl
    _ = Q.conjBy g⁻¹ ⊔ F := by rw [hFcancel]

/-- The punctured self-centralizing property is invariant under conjugating
the subgroup. -/
private theorem centralizer_eq_conjBy_of_centralizer_eq
    {G : Type u} [Group G]
    (Q : Subgroup G)
    (hQcent : ∀ x : G, x ∈ Q → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Q)
    (g : G) :
    ∀ x : G, x ∈ Q.conjBy g → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Q.conjBy g := by
  intro x hxQ hxne
  rw [Subgroup.conjBy, Subgroup.mem_map] at hxQ
  rcases hxQ with ⟨a, haQ, hax⟩
  have hane : a ≠ 1 := by
    intro haone
    apply hxne
    rw [← hax, haone]
    simp [MulAut.conj_apply]
  have hCa : Subgroup.centralizer ({a} : Set G) = Q :=
    hQcent a haQ hane
  ext z
  constructor
  · intro hzC
    have hzx : Commute z x :=
      Subgroup.mem_centralizer_singleton_iff.mp hzC
    have hz0a : Commute (g⁻¹ * z * g) a := by
      have hc := hzx.conj g⁻¹
      have hback : g⁻¹ * x * g = a := by
        rw [← hax]
        simp [MulAut.conj_apply, mul_assoc]
      simpa [hback, mul_assoc] using hc
    have hz0Q : g⁻¹ * z * g ∈ Q := by
      rw [← hCa, Subgroup.mem_centralizer_singleton_iff]
      exact hz0a
    rw [Subgroup.conjBy, Subgroup.mem_map]
    refine ⟨g⁻¹ * z * g, hz0Q, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · intro hzQg
    rw [Subgroup.conjBy, Subgroup.mem_map] at hzQg
    rcases hzQg with ⟨z0, hz0Q, hz0z⟩
    have hz0a : Commute z0 a := by
      exact Subgroup.mem_centralizer_singleton_iff.mp (by
        rw [hCa]
        exact hz0Q)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := hz0a.conj g
    have hzval : g * z0 * g⁻¹ = z := by
      simpa [MulAut.conj_apply] using hz0z
    have hxval : g * a * g⁻¹ = x := by
      simpa [MulAut.conj_apply] using hax
    rw [hzval, hxval] at hc
    exact hc

/-- In the positive-unoccupied-coset branch, the order-two internal
complement of the selected centralizer normalizer is exactly `⟨t⟩`. -/
private theorem selected_centralizer_normalizer_eq_sup_zpowers_t
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ y : G, y ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * y * h.t⁻¹ = y⁻¹)
    (hAcard : Nat.card
      (h.K ⊓ Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G) : Subgroup G) = 2) :
    Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊔ Subgroup.zpowers h.t := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  have hMdecomp : M = F ⊔ A :=
    selected_centralizer_normalizer_eq_sup_inf_K
      h hxC hxne hFodd hFinv
  have htM : h.t ∈ M :=
    mem_normalizer_of_involution_inverts_subgroup
      F h.t_involution hFinv
  have hZA : Subgroup.zpowers h.t ≤ A := by
    apply Subgroup.zpowers_le.mpr
    exact ⟨h.t_mem_K, htM⟩
  have htOrder : orderOf h.t = 2 :=
    orderOf_eq_prime h.t_involution.2 h.t_involution.1
  have hZcard : Nat.card (Subgroup.zpowers h.t) = 2 := by
    rw [Nat.card_zpowers, htOrder]
  have hZAeq : Subgroup.zpowers h.t = A :=
    Subgroup.eq_of_le_of_card_ge hZA (by
      rw [hZcard]
      simpa [A, M, F] using hAcard.le)
  simpa [F, M, A, ← hZAeq] using hMdecomp

/-- Every nontrivial subgroup of the abelian TI complement has the same
normalizer when that normalizer is generated by the complement and an
inverting involution.  This is the common endpoint of Bender's two branches. -/
private theorem normalizer_eq_of_relativeTI_join_inversion
    {G : Type u} [Group G]
    (N D : Subgroup G)
    (hTI : Suzuki.VI.IsTISubsetRelative N (D : Set G))
    (hDcomm : IsMulCommutative D)
    (u : G) (hu : IsInvolution u)
    (hN : N = D ⊔ Subgroup.zpowers u)
    (huinv : ∀ d : G, d ∈ D → u * d * u⁻¹ = d⁻¹)
    (X : Subgroup G) (hX : X ≠ ⊥) (hXD : X ≤ D) :
    Subgroup.normalizer (X : Set G) = N := by
  apply le_antisymm
  · intro g hg
    obtain ⟨x, hx_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
    have hxX : (x : G) ∈ X := x.property
    have hxD : (x : G) ∈ D := hXD hxX
    have hxgX : g * (x : G) * g⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp hg (x : G)).mp hxX
    have hxgD : g * (x : G) * g⁻¹ ∈ D := hXD hxgX
    have hxg_ne : g * (x : G) * g⁻¹ ≠ 1 := by
      intro hxg
      apply hx_ne
      apply Subtype.ext
      have := congrArg (fun z : G => g⁻¹ * z * g) hxg
      simpa [mul_assoc] using this
    have hx_ne_G : (x : G) ≠ 1 := by
      intro hx
      exact hx_ne (Subtype.ext hx)
    obtain ⟨n, hn⟩ := hTI.2.2.1 hxD hxgD ⟨g, rfl⟩
    have hc : (n : G)⁻¹ * g ∈ Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        (n : G)⁻¹ * g * (x : G) =
            (n : G)⁻¹ * (g * (x : G) * g⁻¹) * g := by group
        _ = (n : G)⁻¹ * ((n : G) * (x : G) * (n : G)⁻¹) * g := by rw [hn]
        _ = (x : G) * ((n : G)⁻¹ * g) := by group
    have hcN : (n : G)⁻¹ * g ∈ N := hTI.2.2.2 (x : G) hxD hx_ne_G hc
    have hmul := N.mul_mem n.property hcN
    simpa using hmul
  · rw [hN]
    apply sup_le
    · intro d hdD
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have hcomm (hxD : x ∈ D) : d * x = x * d := by
        let : IsMulCommutative D := hDcomm
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := D)).comm ⟨d, hdD⟩ ⟨x, hxD⟩)
      constructor
      · intro hxX
        have hxD := hXD hxX
        have hconj : d * x * d⁻¹ = x := by
          rw [hcomm hxD]
          simp
        simpa [hconj] using hxX
      · intro hdxX
        have hxD : x ∈ D := by
          have hdxD : d * x * d⁻¹ ∈ D := hXD hdxX
          have : x = d⁻¹ * (d * x * d⁻¹) * d := by group
          rw [this]
          exact D.mul_mem (D.mul_mem (D.inv_mem hdD) hdxD) hdD
        have hconj : d * x * d⁻¹ = x := by
          rw [hcomm hxD]
          simp
        simpa [hconj] using hdxX
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hxX
        simpa [huinv x (hXD hxX)] using X.inv_mem hxX
      · intro huxX
        let y : G := u * x * u⁻¹
        have hyX : y ∈ X := huxX
        have hyD : y ∈ D := hXD hyX
        have hss : u * u = 1 := by simpa [pow_two] using hu.2
        have hu_inv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hss
        have hdouble : u * y * u⁻¹ = x := by
          dsimp [y]
          rw [hu_inv]
          calc
            u * (u * x * u) * u = (u * u) * x * (u * u) := by group
            _ = x := by rw [hss]; simp
        have hyinv := huinv y hyD
        rw [hdouble] at hyinv
        rw [hyinv]
        exact X.inv_mem hyX

/-- Package the common endpoint data of Bender's two structural branches.
The relative-TI fusion condition supplies conclusion (4) uniformly. -/
private theorem conclusion_nonempty_of_structural_data
    {G : Type u} [Group G] [Finite G]
    (q : ℕ) (Q D : Subgroup G)
    (hqodd : Odd q)
    (hQcard : Nat.card Q = q)
    (hGcard : Nat.card G = q * (q + 1) * (q - 1) / 2)
    (hQcent : ∀ x : G, x ∈ Q → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Q)
    (hDcomm : IsMulCommutative D)
    (hQD : Disjoint Q D)
    (N : Subgroup G)
    (hDTI : Suzuki.VI.IsTISubsetRelative N (D : Set G))
    (u : G) (hu : IsInvolution u) (huD : u ∉ D)
    (hN : N = D ⊔ Subgroup.zpowers u)
    (huinv : ∀ d : G, d ∈ D → u * d * u⁻¹ = d⁻¹)
    (hNormQ : Subgroup.normalizer (Q : Set G) = Q ⊔ D)
    (hDcard : Nat.card D = (q - 1) / 2) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  refine ⟨{
    q := q
    Q := Q
    D := D
    q_odd := hqodd
    Q_card := hQcard
    group_card := hGcard
    centralizer_eq_Q := hQcent
    D_commutative := hDcomm
    Q_disjoint_D := hQD
    normalizer_Q_eq := hNormQ
    D_card := hDcard
    normalizer_subgroup_data := ?_ }⟩
  intro X hX hXD
  refine ⟨u, ?_, ?_, hu, huD, huinv⟩
  · calc
      Subgroup.normalizer (X : Set G) = N :=
        normalizer_eq_of_relativeTI_join_inversion
          N D hDTI hDcomm u hu hN huinv X hX hXD
      _ = Subgroup.normalizer (D : Set G) := hDTI.2.1.symm
  · exact hDTI.2.1.trans hN

/-- Bender 3.8: in the minus order case, the residual Sylow normalizer has a
complement conjugate to the selected centralizer.  Conjugating the Sylow
subgroup back packages the common structural conclusion with `D = F`. -/
private theorem conclusion_nonempty_of_bender_3_8
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) (F : Subgroup G)
    (hFcard : Nat.card F = Nat.card h.K - 1)
    (hFcomm : IsMulCommutative F)
    (hFodd : Odd (Nat.card F))
    (hFinv : ∀ z : G, z ∈ F → h.t * z * h.t⁻¹ = z⁻¹)
    (hFCent : ∀ a : G, a ∈ F → a ≠ 1 →
      Subgroup.centralizer ({a} : Set G) = F)
    (hFHall : Nat.Coprime (Nat.card F) F.index)
    (hMcard : Nat.card (Subgroup.normalizer (F : Set G)) =
      2 * (Nat.card h.K - 1))
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G))
    (hHindex : h.H.index =
      (2 * Nat.card h.K - 1) * (Nat.card h.K - 1))
    (hNormF : Subgroup.normalizer (F : Set G) =
      F ⊔ Subgroup.zpowers h.t)
    {p : ℕ} (hpPrime : Nat.Prime p)
    (hpCop : Nat.Coprime p
      (2 * Nat.card h.K * (Nat.card h.K - 1)))
    {y : G} (hy : y ∈ bswResidualSet h F)
    (hyP : IsPGroup p (Subgroup.centralizer ({y} : Set G))) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  classical
  let k : ℕ := Nat.card h.K
  let q : ℕ := 2 * k - 1
  let : Fact p.Prime := ⟨hpPrime⟩
  have hk' : 4 < k := by simpa [k] using hk
  obtain ⟨P, hPcoe, hPcomm, hPcent, hPTI, hPindex⟩ :=
    bender_3_8_residual_sylow_index_data
      h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
        hpPrime hpCop hy hyP
  let Q : Subgroup G := (P : Subgroup G)
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  have hPQ : (P : Subgroup G) = Q := rfl
  have hyForbidden :
      y ∉ ({1} ∪ bswKConjugates h ∪ bswSubgroupConjugates F) := by
    simpa [bswResidualSet] using hy
  have hyne : y ≠ 1 := by
    intro hyone
    apply hyForbidden
    simp [hyone]
  have hyQ : y ∈ Q := by
    dsimp [Q]
    rw [hPcoe]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl y)
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have : y = 1 := by
      have hybot : y ∈ (⊥ : Subgroup G) := by simpa [hbot] using hyQ
      simpa using hybot
    exact hyne this
  have hQp : IsPGroup p Q := by simpa [Q] using P.isPGroup'
  have hQindex : (Q.subgroupOf N).index = k - 1 := by
    simpa [Q, N, k] using hPindex
  let PN : Sylow p N := P.subtype (hPQ.trans_le Subgroup.le_normalizer)
  have hPNindex : PN.index = k - 1 := by
    simpa [PN, N, Q, k] using hPindex
  obtain ⟨r, hrPrime, hrIndex⟩ :=
    Nat.exists_prime_and_dvd (by omega : k - 1 ≠ 1)
  let : Fact r.Prime := ⟨hrPrime⟩
  have hrPNindex : r ∣ PN.index := by
    rw [hPNindex]
    exact hrIndex
  have hrN : r ∣ Nat.card N := by
    exact hrPNindex.trans
      ⟨Nat.card (PN : Subgroup N), PN.index_mul_card.symm⟩
  have hrne : r ≠ p := by
    intro hrp
    apply PN.not_dvd_index
    simpa [hrp] using hrPNindex
  let R : Sylow r N := default
  have hNodd : Odd (Nat.card N) := by
    simpa [N] using
      bender_3_6_normalizer_card_odd
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex
          hpPrime hpCop Q hQne hQp
  have htransfer :=
    bender_3_6_sylow_normal_and_commutator_le
      h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
        hpPrime hpCop hy hyP Q hQne hQp PN
  have hsup :
      (PN : Subgroup N) ⊔
        Subgroup.normalizer ((R : Subgroup N) : Set N) = ⊤ :=
    sup_normalizer_eq_top_of_commutator_le PN R htransfer.2
  obtain ⟨hLcomm0, hplace0⟩ :=
    bender_3_6_sylow_normalizer_commutative
      h hk F hFcard hFcomm hFCent hFHall hMcard hFTI hHindex
        hpPrime hy hyP Q hNodd hrPrime hrne hrN R
  let L : Subgroup N :=
    Subgroup.normalizer ((R : Subgroup N) : Set N)
  let D : Subgroup G := L.map N.subtype
  have hLcomm : IsMulCommutative L := by
    simpa [L, N] using hLcomm0
  have hDcomm : IsMulCommutative D := by
    exact isMulCommutative_map_subtype N L hLcomm
  have hsup' :
      ((P.subtype (hPQ.trans_le Subgroup.le_normalizer) : Sylow p N) :
          Subgroup N) ⊔
        Subgroup.normalizer ((R : Subgroup N) : Set N) = ⊤ := by
    simpa [PN] using hsup
  have hNormQ : N = Q ⊔ D := by
    simpa [N, L, D] using
      map_sylow_sup_normalizer_eq_ambient_normalizer
        Q P hPQ R hsup'
  have hplace :
      (∃ g : G, D ≤ h.K.conjBy g) ∨
        ∃ g : G, D ≤ F.conjBy g := by
    simpa [N, L, D] using hplace0
  have hDleN : D ≤ N := by
    rw [hNormQ]
    exact le_sup_right
  have hpRest : Nat.Coprime p (2 * k * (k - 1)) := by
    simpa [k] using hpCop
  have hpK : Nat.Coprime p k :=
    hpRest.of_dvd_right ⟨2 * (k - 1), by ring⟩
  have hpF : Nat.Coprime p (Nat.card F) := by
    rw [hFcard]
    simpa [k] using
      hpRest.of_dvd_right ⟨2 * k, by ring⟩
  have finish
      (E : Subgroup G) (hpE : Nat.Coprime p (Nat.card E))
      (hDE : D ≤ E) :
      Disjoint Q D ∧ Nat.card D = k - 1 := by
    have hcardCop : Nat.Coprime (Nat.card Q) (Nat.card D) :=
      natCard_coprime_of_isPGroup_of_le Q D E hQp hpE hDE
    have hQD : Disjoint Q D :=
      Subgroup.disjoint_of_coprime_natCard hcardCop
    have hsupIndex : (Q.subgroupOf (Q ⊔ D)).index = Nat.card D :=
      subgroupOf_sup_index_eq_card_of_disjoint_of_le_normalizer
        Q D hQD (by simpa [N] using hDleN)
    have hindexSup : (Q.subgroupOf (Q ⊔ D)).index = k - 1 := by
      have hindex := hQindex
      rw [hNormQ] at hindex
      exact hindex
    exact ⟨hQD, hsupIndex.symm.trans hindexSup⟩
  rcases hplace with ⟨g, hDK⟩ | ⟨g, hDF⟩
  · have hpKg : Nat.Coprime p (Nat.card (h.K.conjBy g)) := by
      rw [bsw_natCard_conjBy]
      simpa [k] using hpK
    obtain ⟨_hQD, hDcard⟩ := finish (h.K.conjBy g) hpKg hDK
    have hKconjCard : Nat.card (h.K.conjBy g) = k := by
      rw [bsw_natCard_conjBy]
    have hdvd : k - 1 ∣ k := by
      have hdiv := Subgroup.card_dvd_of_le hDK
      rwa [hDcard, hKconjCard] at hdiv
    have hcop : Nat.Coprime (k - 1) k :=
      (Nat.coprime_self_sub_left (by omega : 1 ≤ k)).mpr
        (Nat.coprime_one_left k)
    have hone : k - 1 = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd
    omega
  · have hpFg : Nat.Coprime p (Nat.card (F.conjBy g)) := by
      rw [bsw_natCard_conjBy]
      exact hpF
    obtain ⟨hQD, hDcard⟩ := finish (F.conjBy g) hpFg hDF
    have hFgcard : Nat.card (F.conjBy g) = k - 1 := by
      rw [bsw_natCard_conjBy, hFcard]
    have hDeq : D = F.conjBy g :=
      Subgroup.eq_of_le_of_card_ge hDF (by rw [hDcard, hFgcard])
    have hNormQPlaced :
        Subgroup.normalizer (Q : Set G) = Q ⊔ F.conjBy g := by
      simpa [N, hDeq] using hNormQ
    let Q' : Subgroup G := Q.conjBy g⁻¹
    have hNormQ' : Subgroup.normalizer (Q' : Set G) = Q' ⊔ F := by
      simpa [Q'] using normalizer_conjBy_inv_eq_sup Q F g hNormQPlaced
    have hQcard : Nat.card Q = q := by
      have hQeq : Q = Subgroup.centralizer ({y} : Set G) := by
        simpa [Q] using hPcoe
      calc
        Nat.card Q = Nat.card (Subgroup.centralizer ({y} : Set G)) := by
          rw [hQeq]
        _ = 2 * Nat.card h.K - 1 :=
          bender_3_5_residual_centralizer_card
            h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
        _ = q := by simp [q, k]
    have hQ'card : Nat.card Q' = q := by
      rw [bsw_natCard_conjBy]
      exact hQcard
    have hQ'cent : ∀ x : G, x ∈ Q' → x ≠ 1 →
        Subgroup.centralizer ({x} : Set G) = Q' := by
      simpa [Q'] using
        centralizer_eq_conjBy_of_centralizer_eq Q
          (by simpa [Q] using hPcent) g⁻¹
    have hQ'p : IsPGroup p Q' := by
      change IsPGroup p
        (Q.map (MulAut.conj g⁻¹).toMonoidHom)
      exact hQp.map (MulAut.conj g⁻¹).toMonoidHom
    have hQ'Fcop : Nat.Coprime (Nat.card Q') (Nat.card F) :=
      natCard_coprime_of_isPGroup_of_le Q' F F hQ'p hpF le_rfl
    have hQ'F : Disjoint Q' F :=
      Subgroup.disjoint_of_coprime_natCard hQ'Fcop
    have hqOdd : Odd q := by
      refine ⟨k - 1, ?_⟩
      dsimp [q]
      omega
    have hGminus : Nat.card G = q * (k - 1) * (2 * k) := by
      calc
        Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
        _ = (2 * k) * ((2 * k - 1) * (k - 1)) := by
          rw [h.card_H]
          simpa [k] using congrArg (fun n => (2 * k) * n) hHindex
        _ = q * (k - 1) * (2 * k) := by
          dsimp [q]
          ring
    have hFormula :
        q * (q + 1) * (q - 1) / 2 = q * (k - 1) * (2 * k) := by
      have hqadd : q + 1 = 2 * k := by
        dsimp [q]
        omega
      have hqsub : q - 1 = 2 * (k - 1) := by
        dsimp [q]
        omega
      rw [hqadd, hqsub]
      calc
        q * (2 * k) * (2 * (k - 1)) / 2 =
            2 * (q * (2 * k) * (k - 1)) / 2 := by
          congr 1
          ring
        _ = q * (2 * k) * (k - 1) :=
          Nat.mul_div_cancel_left _ (by omega)
        _ = q * (k - 1) * (2 * k) := by ring
    have hGcard : Nat.card G = q * (q + 1) * (q - 1) / 2 :=
      hGminus.trans hFormula.symm
    have hFhalf : Nat.card F = (q - 1) / 2 := by
      rw [hFcard]
      dsimp [q, k]
      omega
    have htNotF : h.t ∉ F := by
      intro htF
      have htOrder : orderOf h.t = 2 :=
        orderOf_eq_prime h.t_involution.2 h.t_involution.1
      apply hFodd.not_two_dvd_nat
      rw [← htOrder]
      exact Subgroup.orderOf_dvd_natCard F htF
    exact conclusion_nonempty_of_structural_data
      q Q' F hqOdd hQ'card hGcard hQ'cent hFcomm hQ'F
        (Subgroup.normalizer (F : Set G)) hFTI h.t h.t_involution
        htNotF hNormF hFinv hNormQ' hFhalf

/-- Bender 3.3: if the selected normalizer has no additional cosets, the
structural conclusion is obtained with `Q = F` and `D = K`. -/
private theorem conclusion_nonempty_of_selected_centralizer_no_unoccupied
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K) {x : G}
    (hxC : x ∉ bswKConjugates h) (hxne : x ≠ 1)
    (hFcomm : IsMulCommutative
      (Subgroup.centralizer ({x} : Set G)))
    (hFodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFinv : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
      h.t * z * h.t⁻¹ = z⁻¹)
    (hFCent : ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer ({x} : Set G))
    (hbound :
      (h.H.index =
            (2 * Nat.card h.K + 1) * (Nat.card h.K + 1) ∧
          Nat.card h.K + 3 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))) ∨
        (h.H.index =
            (2 * Nat.card h.K - 1) * (Nat.card h.K - 1) ∧
          Nat.card h.K - 1 ≤
            Nat.card (Subgroup.centralizer ({x} : Set G))))
    (hFHall : Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index)
    (hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer
        (Subgroup.centralizer ({x} : Set G) : Set G))
      (Subgroup.centralizer ({x} : Set G) : Set G))
    (he : Nat.card
      (selected_centralizer_unoccupied_nonbase_cosets
        (Subgroup.centralizer ({x} : Set G))) = 0) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let M : Subgroup G := Subgroup.normalizer (F : Set G)
  let A : Subgroup G := h.K ⊓ M
  let k : ℕ := Nat.card h.K
  let f : ℕ := Nat.card F
  let n : ℕ := Nat.card A
  obtain ⟨r, j, hrPos, hrMul, hMindex, _heCases, hjle, hHindex⟩ :=
    selected_centralizer_bender_3_2_count_data
      h hxC hxne hFcomm hFodd hFinv hFHall hFTI
  have hj0 : j = 0 := by omega
  have hHindex0 : h.H.index = f * (k + 1) := by
    simpa [f, k, hj0] using hHindex
  have hf : f = 2 * k + 1 :=
    bender_3_3_card_F k f h.H.index hk h.card_K_even hbound hHindex0
  have hMindex0 : M.index = 1 + f * (r - 1) := by
    simpa [M, F, f, he] using hMindex
  have hMcard : Nat.card M = f * n := by
    simpa [M, F, A, f, n] using
      selected_centralizer_normalizer_card
        h hxC hxne hFodd hFinv
  have hglobal :
      (1 + f * (r - 1)) * (f * n) =
        (2 * k) * (f * (k + 1)) := by
    calc
      (1 + f * (r - 1)) * (f * n) = M.index * Nat.card M := by
        rw [hMindex0, hMcard]
      _ = Nat.card G := M.index_mul_card
      _ = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * (f * (k + 1)) := by
        rw [h.card_H, hHindex0]
  have hfPos : 0 < f := Nat.card_pos
  have hcancel :
      (1 + f * (r - 1)) * n = 2 * k * (k + 1) := by
    apply Nat.eq_of_mul_eq_mul_left hfPos
    calc
      f * ((1 + f * (r - 1)) * n) =
          (1 + f * (r - 1)) * (f * n) := by ring
      _ = (2 * k) * (f * (k + 1)) := hglobal
      _ = f * (2 * k * (k + 1)) := by ring
  have hn : n = k :=
    bender_3_3_internal_card k f n r (by omega) hrPos hf
      (by simpa [n, k, A, M, F] using hrMul) hcancel
  have hAleK : A ≤ h.K := inf_le_left
  have hAK : A = h.K :=
    Subgroup.eq_of_le_of_card_ge hAleK (by
      have : k ≤ n := le_of_eq hn.symm
      simpa [k, n] using this)
  have hMdecomp : M = F ⊔ A :=
    selected_centralizer_normalizer_eq_sup_inf_K
      h hxC hxne hFodd hFinv
  have hNormF : Subgroup.normalizer (F : Set G) = F ⊔ h.K := by
    simpa [M, hAK] using hMdecomp
  have hKleH : h.K ≤ h.H := by
    rw [h.H_eq_join]
    exact le_sup_left
  have hFK : Disjoint F h.K :=
    (selected_centralizer_disjoint_H h hxC hxne).mono_right hKleH
  have hDcard : Nat.card h.K = (f - 1) / 2 := by
    rw [hf]
    omega
  have hFormula :
      f * (f + 1) * (f - 1) / 2 = f * (k + 1) * (2 * k) := by
    rw [hf]
    have hadd : (2 * k + 1) + 1 = 2 * (k + 1) := by omega
    have hsub : (2 * k + 1) - 1 = 2 * k := by omega
    rw [hadd, hsub]
    calc
      (2 * k + 1) * (2 * (k + 1)) * (2 * k) / 2 =
          2 * ((2 * k + 1) * (k + 1) * (2 * k)) / 2 := by
        congr 1
        ring
      _ = (2 * k + 1) * (k + 1) * (2 * k) :=
        Nat.mul_div_cancel_left _ (by omega)
  have hGcard : Nat.card G = f * (f + 1) * (f - 1) / 2 := by
    calc
      Nat.card G = Nat.card h.H * h.H.index := h.H.card_mul_index.symm
      _ = (2 * k) * (f * (k + 1)) := by rw [h.card_H, hHindex0]
      _ = f * (k + 1) * (2 * k) := by ring
      _ = f * (f + 1) * (f - 1) / 2 := hFormula.symm
  exact conclusion_nonempty_of_structural_data
    f F h.K hFodd rfl hGcard hFCent h.K_commutative hFK
      h.H h.isTISubsetRelative h.s h.s_involution h.s_not_mem_K
      h.H_eq_join h.s_inverts_K hNormF hDcard

/-- The high-cardinality Brauer--Suzuki--Wall structural conclusion, assembled
from Bender's two order cases and paragraphs 3.1--3.8. -/
public theorem brauerSuzukiWallConclusion_nonempty_of_order_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : 4 < Nat.card h.K)
    (horder :
      let k := Nat.card h.K
      Nat.card G = (2 * k + 1) * (k + 1) * (2 * k) ∨
        Nat.card G = (2 * k - 1) * (k - 1) * (2 * k)) :
    Nonempty (BrauerSuzukiWallConclusion G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨x, F, hFdef, hxC, hxne, htx, hFcomm, hFodd, hFinv,
      hFCent, hbound⟩ :=
    exists_selected_centralizer_order_bound h hk horder
  subst F
  let F : Subgroup G := Subgroup.centralizer ({x} : Set G)
  have hFHall : Nat.Coprime (Nat.card F) F.index := by
    simpa [F] using selected_centralizer_isHall hFCent
  have hFTI : Suzuki.VI.IsTISubsetRelative
      (Subgroup.normalizer (F : Set G)) (F : Set G) := by
    simpa [F] using selected_centralizer_isTISubsetRelative
      hxne hFcomm hFCent
  by_cases he : Nat.card
      (selected_centralizer_unoccupied_nonbase_cosets F) = 0
  · exact conclusion_nonempty_of_selected_centralizer_no_unoccupied
      h hk hxC hxne hFcomm hFodd hFinv hFCent hbound hFHall hFTI
        (by simpa [F] using he)
  · have hePos : 0 < Nat.card
        (selected_centralizer_unoccupied_nonbase_cosets F) :=
      Nat.pos_of_ne_zero he
    obtain ⟨hFcard, hAcard, hMcard, hHindex⟩ :=
      selected_centralizer_bender_3_4_card_data
        h hk hxC hxne hFcomm hFodd hFinv hFCent hbound
          hFHall hFTI (by simpa [F] using hePos)
    have hNormF : Subgroup.normalizer (F : Set G) =
        F ⊔ Subgroup.zpowers h.t := by
      simpa [F] using
        selected_centralizer_normalizer_eq_sup_zpowers_t
          h hxC hxne hFodd hFinv hAcard
    have hResidualCard : Nat.card ↑(bswResidualSet h F) =
        4 * Nat.card h.K * (Nat.card h.K - 1) :=
      bender_3_5_residual_card
        h hk F hFcard hMcard hFTI hHindex
    have hResidualPos : 0 < Nat.card ↑(bswResidualSet h F) := by
      rw [hResidualCard]
      exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    obtain ⟨yR⟩ := (Nat.card_pos_iff.mp hResidualPos).1
    let y : G := yR
    have hy : y ∈ bswResidualSet h F := yR.property
    obtain ⟨p, hpPrime, hyP, _hpq, _hpOdd, hpCop⟩ :=
      bender_3_6_residual_prime_data
        h hk F hFcard hFCent hFHall hMcard hFTI hHindex hy
    exact conclusion_nonempty_of_bender_3_8
      h hk F hFcard hFcomm hFodd hFinv hFCent hFHall hMcard hFTI
        hHindex hNormF hpPrime hpCop hy hyP

end CFSG.GorensteinWalter
