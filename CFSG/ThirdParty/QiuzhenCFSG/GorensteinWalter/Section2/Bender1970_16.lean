module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.FStarSubnormal
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import Mathlib.GroupTheory.IsPerfect

namespace CFSG
end CFSG
open CFSG

/-!
# Bender (1970) Statement 1.6

This module proves `bender1970_1_6_maximalSubgroups_pGroups` (Bender [1],
Statement 1.6): if `A` and `B` are distinct maximal subgroups of a simple
group `G` with `F*(A) ≤ B` and `F*(B) ≤ A`, then both generalized Fitting
subgroups are `p`-groups for one common prime `p`.

The route follows Kurzweil--Stellmacher 10.1.4 (primitive pairs):

1. `F*(A)` and `F*(B)` are normal subgroups of `A ⊓ B`, and each is
   contained in `F*(A ⊓ B)`.
2. Every component of `A` is a component of `A ⊓ B`; by the
   component--subnormal dichotomy it is contained in `F*(B)`, hence is a
   component of `B`.  Symmetrically `E(A) = E(B)`, and primitivity
   (maximality in a simple group) forces this common layer to be trivial.
3. With trivial layers, `F*(A) = F(A)` and `F*(B) = F(B)`, the prime
   divisors agree, and Thompson's lemma (Statement 1.1) eliminates the
   `p'`-parts.
-/

noncomputable section

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-! ## Component descent infrastructure -/

/-- The image of the center under a group isomorphism is the center. -/
private lemma map_center_eq_center_of_mulEquiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (Subgroup.centerCongr e ⟨y, hy⟩).2
  · intro x hx
    refine ⟨e.symm x, ?_, ?_⟩
    · exact ((Subgroup.centerCongr e).symm ⟨x, hx⟩).2
    · exact e.apply_symm_apply x

/-- Quasisimplicity is invariant under a group isomorphism. -/
private theorem isQuasisimple_mulEquiv
    {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : IsQuasisimple G) :
    IsQuasisimple H := by
  have hNontriv : Nontrivial H := by
    let : Nontrivial G := hG.1
    exact e.toEquiv.injective.nontrivial
  have hPerf : Group.IsPerfect H := by
    let : Group.IsPerfect G := (Group.isPerfect_def).2 hG.2.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.toEquiv.surjective
  have hSimple : IsSimpleGroup (H ⧸ Subgroup.center H) := by
    have he : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H :=
      map_center_eq_center_of_mulEquiv e
    exact (MulEquiv.isSimpleGroup_congr
      (QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e he)).mp hG.2.2
  exact ⟨hNontriv, (Group.isPerfect_def).1 hPerf, hSimple⟩

/-- A component of the ambient group is subnormal in the ambient group. -/
private theorem isSubnormal_of_isComponentOf_top
    {G : Type u} [Group G] {K : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G)) :
    K.IsSubnormal := by
  have h' : ((K.subgroupOf (⊤ : Subgroup G)).map (⊤ : Subgroup G).subtype).IsSubnormal :=
    hK.2.1.map (f := (⊤ : Subgroup G).subtype)
      (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
  rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : K ≤ (⊤ : Subgroup G))] at h'

/-- A component of `G` contained in `H` is a component of `H`. -/
private theorem isComponentOf_subgroupOf
    {G : Type u} [Group G] {K H : Subgroup G}
    (hK : IsComponentOf K (⊤ : Subgroup G))
    (hKH : K ≤ H) :
    IsComponentOf (K.subgroupOf H) (⊤ : Subgroup H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    trivial
  · have hKsn : K.IsSubnormal := isSubnormal_of_isComponentOf_top hK
    have hsn0 : (K.subgroupOf H).IsSubnormal := hKsn.subgroupOf
    exact hsn0.subgroupOf
  · exact isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH).symm hK.2.2

/-- Transport of subgroup containment through `subgroupOf`. -/
private theorem subgroupOf_le_subgroupOf_iff_of_le
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (_hBH : B ≤ H) :
    A.subgroupOf H ≤ B.subgroupOf H ↔ A ≤ B := by
  constructor
  · intro hle x hx
    have hm : (A.subgroupOf H).map H.subtype ≤ (B.subgroupOf H).map H.subtype :=
      Subgroup.map_mono (f := H.subtype) hle
    have hx' : H.subtype ⟨x, hAH hx⟩ ∈ (A.subgroupOf H).map H.subtype := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact ⟨hx, hAH hx⟩
    have hy : H.subtype ⟨x, hAH hx⟩ ∈ (B.subgroupOf H).map H.subtype := hm hx'
    rcases Subgroup.mem_map.mp hy with ⟨y, hyB, hxy⟩
    have hyx : (y : ↥H).1 = x := by
      have hyx' : y = (⟨x, hAH hx⟩ : ↥H) := H.subtype_injective hxy
      simpa using (congrArg (fun z : ↥H => (z : ↥H).1) hyx')
    have hy1 : (y : ↥H).1 ∈ B := (Subgroup.mem_subgroupOf).mp hyB
    simpa [hyx] using hy1
  · intro hle
    exact Subgroup.subgroupOf_mono H hle

/-- Transport of commutator triviality through `subgroupOf`. -/
private theorem commutator_subgroupOf_eq_bot_iff_of_le
    {G : Type u} [Group G] {A B H : Subgroup G}
    (hAH : A ≤ H) (hBH : B ≤ H) :
    ⁅A.subgroupOf H, B.subgroupOf H⁆ = ⊥ ↔ ⁅A, B⁆ = ⊥ := by
  constructor
  · intro hbot
    have hmap : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [hbot]
      exact Subgroup.map_bot H.subtype
    have hm : ⁅(A.subgroupOf H).map H.subtype, (B.subgroupOf H).map H.subtype⁆ = ⊥ := by
      rw [← Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H) (f := H.subtype)]
      exact hmap
    have hA : (A.subgroupOf H).map H.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAH
    have hB : (B.subgroupOf H).map H.subtype = B := Subgroup.map_subgroupOf_eq_of_le hBH
    simpa [hA, hB] using hm
  · intro hbot
    have hm : (⁅A.subgroupOf H, B.subgroupOf H⁆).map H.subtype = ⊥ := by
      rw [Subgroup.map_commutator (H₁ := A.subgroupOf H) (H₂ := B.subgroupOf H) (f := H.subtype)]
      rw [Subgroup.map_subgroupOf_eq_of_le hAH, Subgroup.map_subgroupOf_eq_of_le hBH]
      exact hbot
    exact (Subgroup.map_eq_bot_iff_of_injective (H := ⁅A.subgroupOf H, B.subgroupOf H⁆)
      (f := H.subtype) (hf := H.subtype_injective)).mp hm

/-- Restriction commutes with double `subgroupOf`, through the canonical
equivalence between `H.subgroupOf A` and `H`. -/
private theorem map_subgroupOf_subgroupOf_eq
    {G : Type u} [Group G] {E A H : Subgroup G}
    (hEH : E ≤ H) (hHA : H ≤ A) :
    ((E.subgroupOf A).subgroupOf (H.subgroupOf A)).map
      (Subgroup.subgroupOfEquivOfLe hHA).toMonoidHom = E.subgroupOf H := by
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have hyE : (y.1 : G) ∈ E := by
      have hy1 := (Subgroup.mem_subgroupOf).mp hy
      exact (Subgroup.mem_subgroupOf).mp hy1
    exact (Subgroup.mem_subgroupOf).mpr hyE
  · intro hx
    have hxE : (x : G) ∈ E := (Subgroup.mem_subgroupOf).mp hx
    refine Subgroup.mem_map.mpr ⟨?_, ?_, ?_⟩
    · exact ⟨⟨x, hHA (hEH hxE)⟩, by
        change (x : G) ∈ H
        exact hEH hxE⟩
    · rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf]
      exact hxE
    · apply Subtype.ext
      rfl

/-- A component of `A` which is contained in `H ≤ A` is a component of `H`. -/
private theorem isComponentOf_subgroupOf_of_isComponentOf
    {G : Type u} [Group G] {A H E : Subgroup G}
    (hE : IsComponentOf E A) (hEH : E ≤ H) (hHA : H ≤ A) :
    IsComponentOf (E.subgroupOf H) (⊤ : Subgroup H) := by
  have hE0 : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    ⟨le_top, hE.2.1.subgroupOf,
      isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩
  let HA : Subgroup (↥A) := H.subgroupOf A
  let e : HA ≃* H := Subgroup.subgroupOfEquivOfLe hHA
  have hE0HA : IsComponentOf ((E.subgroupOf A).subgroupOf HA) (⊤ : Subgroup (↥HA)) := by
    apply isComponentOf_subgroupOf (G := ↥A) hE0
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact hEH hx
  have hmap : ((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom = E.subgroupOf H :=
    map_subgroupOf_subgroupOf_eq hEH hHA
  -- transport the component of `HA` through `e`
  have hEcompH : IsComponentOf (((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom)
      (⊤ : Subgroup H) := by
    refine ⟨le_top, ?_, ?_⟩
    · have hsub0 : (((E.subgroupOf A).subgroupOf HA).subgroupOf
          (⊤ : Subgroup (↥HA))).map (⊤ : Subgroup (↥HA)).subtype = (E.subgroupOf A).subgroupOf HA :=
        Subgroup.map_subgroupOf_eq_of_le
          (le_top : (E.subgroupOf A).subgroupOf HA ≤ (⊤ : Subgroup (↥HA)))
      have hKsnHA : ((E.subgroupOf A).subgroupOf HA).IsSubnormal := by
        have hmap := hE0HA.2.1.map (f := (⊤ : Subgroup (↥HA)).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
        rwa [hsub0] at hmap
      have hsub : (((E.subgroupOf A).subgroupOf HA).map e.toMonoidHom).IsSubnormal :=
        hKsnHA.map (f := e.toMonoidHom) e.surjective
      exact hsub.subgroupOf
    · exact isQuasisimple_mulEquiv
        (Subgroup.equivMapOfInjective ((E.subgroupOf A).subgroupOf HA)
          e.toMonoidHom e.injective) hE0HA.2.2
  rwa [hmap] at hEcompH

/-- Restriction of a normalizer-containment to `subgroupOf A`. -/
private theorem subgroup_normalizer_of_le_normalizer
    {G : Type u} [Group G] {H S A : Subgroup G}
    (hH : H ≤ Subgroup.normalizer (S : Set G)) :
    H.subgroupOf A ≤ Subgroup.normalizer ((S.subgroupOf A : Subgroup (↥A)) : Set (↥A)) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hxH : (x : G) ∈ H := (Subgroup.mem_subgroupOf).mp hx
  have hxN : (x : G) ∈ Subgroup.normalizer (S : Set G) := hH hxH
  rw [Subgroup.mem_normalizer_iff] at hxN
  constructor
  · intro hy
    simpa [Subgroup.mem_subgroupOf] using (hxN (y : G)).1 hy
  · intro hy
    simpa [Subgroup.mem_subgroupOf] using (hxN (y : G)).2 hy

/-- A component centralizes any nilpotent subgroup it normalizes. -/
private theorem component_centralizes_normalized_nilpotent
    {G : Type u} [Group G] [Finite G]
    {A E S : Subgroup G} (hE : IsComponentOf E A)
    (hEN : E ≤ Subgroup.normalizer (S : Set G))
    (hSA : S ≤ A)
    (hS : Group.IsNilpotent S) :
    ⁅E, S⁆ = ⊥ := by
  let H : Subgroup G := E ⊔ S
  have hEH : E ≤ H := le_sup_left
  have hSH : S ≤ H := le_sup_right
  have hHA : H ≤ A := sup_le hE.1 hSA
  let HA : Subgroup (↥A) := H.subgroupOf A
  let SA : Subgroup (↥A) := S.subgroupOf A
  let K1 : Subgroup (↥HA) := (E.subgroupOf A).subgroupOf HA
  let S1 : Subgroup (↥HA) := SA.subgroupOf HA
  let e : HA ≃* H := Subgroup.subgroupOfEquivOfLe hHA
  have hE0 : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    ⟨le_top, hE.2.1.subgroupOf,
      isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩
  have hE0HA : IsComponentOf K1 (⊤ : Subgroup (↥HA)) := by
    apply isComponentOf_subgroupOf (G := ↥A) hE0
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    exact hEH hx
  have hHleN : H ≤ Subgroup.normalizer (S : Set G) := sup_le hEN S.le_normalizer
  have hHAleN : HA ≤ Subgroup.normalizer (SA : Set (↥A)) :=
    subgroup_normalizer_of_le_normalizer hHleN
  have hS1normal : S1.Normal := by
    exact Subgroup.normal_subgroupOf_of_le_normalizer (H := HA) (N := SA) hHAleN
  rcases component_le_or_commutator_eq_bot (G := (↥HA)) hE0HA hS1normal.isSubnormal with
    hle | hcomm
  · exfalso
    have hK1map : K1.map e.toMonoidHom = E.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq hEH hHA
    have hS1map : S1.map e.toMonoidHom = S.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq hSH hHA
    have hmaple : K1.map e.toMonoidHom ≤ S1.map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hle
    have hES : E ≤ S := by
      rw [hK1map, hS1map] at hmaple
      exact (subgroupOf_le_subgroupOf_iff_of_le hEH hSH).mp hmaple
    have hEnil : Group.IsNilpotent E := by
      have hrc : ∃ n, S.lowerCentralSeries n = ⊥ :=
        (Subgroup.isNilpotent_iff_lowerCentralSeries (S := S)).mp hS
      rcases hrc with ⟨n, hSbot⟩
      have hEm : E.lowerCentralSeries n ≤ S.lowerCentralSeries n :=
        Subgroup.lowerCentralSeries_mono (n := n) hES
      have hEbot : E.lowerCentralSeries n = ⊥ := by
        rw [hSbot] at hEm
        exact le_bot_iff.mp hEm
      exact (Subgroup.isNilpotent_iff_lowerCentralSeries (S := E)).mpr ⟨n, hEbot⟩
    exact not_isNilpotent_of_isQuasisimple E hE.2.2 hEnil
  · have hK1map : K1.map e.toMonoidHom = E.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq hEH hHA
    have hS1map : S1.map e.toMonoidHom = S.subgroupOf H :=
      map_subgroupOf_subgroupOf_eq hSH hHA
    have hmapcomm : (⁅K1, S1⁆).map e.toMonoidHom = ⊥ := by
      rw [hcomm]
      exact Subgroup.map_bot e.toMonoidHom
    have hcommH : ⁅K1.map e.toMonoidHom, S1.map e.toMonoidHom⁆ = ⊥ := by
      rw [← Subgroup.map_commutator (H₁ := K1) (H₂ := S1) (f := e.toMonoidHom)]
      exact hmapcomm
    have hcomm' : ⁅E.subgroupOf H, S.subgroupOf H⁆ = ⊥ := by
      rw [hK1map, hS1map] at hcommH
      exact hcommH
    exact (commutator_subgroupOf_eq_bot_iff_of_le hEH hSH).mp hcomm'

/-- The layer of `N` is contained in the layer of any supergroup in which
`N` is normal. -/
private theorem componentLayerOf_le_of_isNormalIn
    {G : Type u} [Group G] [Finite G]
    {L N : Subgroup G} (hNL : N ≤ L) (hN : IsNormalIn N L) :
    componentLayerOf N ≤ componentLayerOf L := by
  rw [componentLayerOf, componentLayerOf]
  apply sSup_le
  intro E hE
  refine le_sSup (s := {E' : Subgroup G | IsComponentOf E' L}) ?_
  exact ⟨hE.1.trans hNL,
    isSubnormal_of_isNormalIn_subgroup hNL hN hE.1 hE.2.1, hE.2.2⟩

/-! ## Characteristic/normal layer facts -/

/-- Conjugation by an ambient element transports quasisimplicity. -/
private theorem isQuasisimple_conjugateSubgroup {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : IsQuasisimple E) :
    IsQuasisimple (conjugateSubgroup E g) :=
  isQuasisimple_mulEquiv ((MulAut.conj g).subgroupMap E) hE

/-- Conjugation by an ambient element transports subnormality. -/
private theorem isSubnormal_conjugateSubgroup {G : Type u} [Group G]
    (E : Subgroup G) (g : G) (hE : E.IsSubnormal) :
    (conjugateSubgroup E g).IsSubnormal := by
  simpa [conjugateSubgroup] using hE.map (MulAut.conj g).surjective

/-- A conjugate (by an element of `A`) of a component of `A` is again a
component of `A`. -/
private theorem isComponentOf_conjugateSubgroup_of_mem
    {G : Type u} [Group G]
    {E A : Subgroup G} (hE : IsComponentOf E A) (a : G) (ha : a ∈ A) :
    IsComponentOf (conjugateSubgroup E a) A := by
  refine ⟨?_, ?_, isQuasisimple_conjugateSubgroup E a hE.2.2⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨e, he, rfl⟩
    exact A.mul_mem (A.mul_mem ha (hE.1 he)) (A.inv_mem ha)
  · have hsnA : (E.subgroupOf A).IsSubnormal := hE.2.1
    have hconjA : (conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A)).IsSubnormal :=
      isSubnormal_conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) hsnA
    have hEq : conjugateSubgroup (E.subgroupOf A) (⟨a, ha⟩ : ↥A) =
        (conjugateSubgroup E a).subgroupOf A := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf]
        rcases (Subgroup.mem_map).1 hx with ⟨k, hk, hkx⟩
        exact Subgroup.mem_map.mpr ⟨(k : G), (Subgroup.mem_subgroupOf).1 hk, by
          have hxG := congrArg (fun z : ↥A => (z : G)) hkx
          simpa [conjugateSubgroup] using hxG⟩
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rcases (Subgroup.mem_map).1 hx with ⟨y, hy, hxy⟩
        let k : ↥A := ⟨y, hE.1 hy⟩
        refine Subgroup.mem_map.mpr ⟨k, ?_, ?_⟩
        · rw [Subgroup.mem_subgroupOf]
          exact hy
        · apply Subtype.ext
          simpa [k, conjugateSubgroup] using hxy
    simpa [hEq] using hconjA

/-- `E(A) ≤ A`. -/
private theorem componentLayerOf_le {G : Type u} [Group G] (A : Subgroup G) :
    componentLayerOf A ≤ A := by
  rw [componentLayerOf]
  exact sSup_le (fun E hE => hE.1)

/-- The center of a subgroup is characteristic. -/
private instance center_characteristic {G : Type u} [Group G] (H : Subgroup G) :
    (Subgroup.center H).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact map_center_eq_center_of_mulEquiv e

/-- The center of the layer lies in the Fitting subgroup. -/
private theorem center_layer_le_fitting {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) :
    (Subgroup.center (componentLayerOf B)).map (componentLayerOf B).subtype ≤
      fittingSubgroupOf B := by
  let E : Subgroup G := componentLayerOf B
  let C : Subgroup (↥E) := Subgroup.center E
  have hCE : C.map E.subtype ≤ E := Subgroup.map_subtype_le (H := E) C
  have hCnormalB : IsNormalIn (C.map E.subtype) B := by
    refine ⟨hCE.trans (componentLayerOf_le B), ?_⟩
    intro b hb x hx
    rcases Subgroup.mem_map.mp hx with ⟨c, hc, rfl⟩
    -- `b * c * b⁻¹` lies in `E`; then show it is central in `E`.
    have hcE : (c : G) ∈ E := c.2
    have hbE : b * (c : G) * b⁻¹ ∈ E := (componentLayerOf_isNormalIn B).2 b hb (c : G) hcE
    refine Subgroup.mem_map.mpr ⟨⟨b * (c : G) * b⁻¹, hbE⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro e'
    -- centralizer calculation inside `E`
    have hc_center : ∀ e : ↥E, c * e = e * c :=
      fun e => ((Subgroup.mem_center_iff.mp hc e)).symm
    have hbEinv : b⁻¹ * (e' : G) * b ∈ E :=
      by
        have h := (componentLayerOf_isNormalIn B).2 b⁻¹ (B.inv_mem hb) (e' : G) e'.2
        simpa [mul_assoc] using h
    have hcomm : b * (c : G) * b⁻¹ * (e' : G) = (e' : G) * (b * (c : G) * b⁻¹) := by
      calc
        b * (c : G) * b⁻¹ * (e' : G) = b * (c * (b⁻¹ * (e' : G) * b)) * b⁻¹ := by group
        _ = b * ((b⁻¹ * (e' : G) * b) * c) * b⁻¹ := by
          have hcE' : (c : G) * (b⁻¹ * (e' : G) * b) =
              (b⁻¹ * (e' : G) * b) * (c : G) := by
            exact congrArg Subtype.val (hc_center ⟨b⁻¹ * (e' : G) * b, hbEinv⟩)
          rw [hcE']
        _ = (e' : G) * (b * (c : G) * b⁻¹) := by group
    apply Subtype.ext
    exact hcomm.symm
  have hCnil : Group.IsNilpotent (C.map E.subtype) := by
    have : IsMulCommutative C := Subgroup.center.isMulCommutative (G := ↥E)
    have hlc : (⊤ : Subgroup C).lowerCentralSeries 1 = ⊥ :=
      (Subgroup.lowerCentralSeries_one_eq_bot_iff (G := C)).2 inferInstance
    have hCnil' : Group.IsNilpotent C :=
      (Subgroup.nilpotent_iff_lowerCentralSeries (G := C)).mpr ⟨1, hlc⟩
    let e : C ≃* C.map E.subtype :=
      Subgroup.equivMapOfInjective C E.subtype E.subtype_injective
    have : Group.IsNilpotent C := hCnil'
    exact Group.nilpotent_of_mulEquiv e
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent
    (hCE.trans (componentLayerOf_le B)) hCnormalB hCnil

/-- The centralizer of `F*(B)` inside `F*(B)` lies in the center of `F(B)`. -/
private theorem centralizer_self_le_fitting_center {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) :
    generalizedFittingSubgroupOf B ⊓
        Subgroup.centralizer ((generalizedFittingSubgroupOf B : Set G)) ≤
      (Subgroup.center (fittingSubgroupOf B)).map (fittingSubgroupOf B).subtype := by
  intro x hx
  let F : Subgroup G := fittingSubgroupOf B
  let E : Subgroup G := componentLayerOf B
  have hxX : x ∈ F ⊔ E := by
    simpa [F, E, generalizedFittingSubgroupOf] using hx.1
  have hxC : x ∈ Subgroup.centralizer ((F ⊔ E : Subgroup G) : Set G) := by
    simpa [F, E, generalizedFittingSubgroupOf] using hx.2
  have hEF : E ≤ Subgroup.centralizer (F : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    simpa [F, E] using layer_centralizes_fitting B
  rcases mem_sup_decompose_of_centralizes hxX hEF with ⟨f, hf, e, he, hxeq⟩
  have hxC' : f * e ∈ Subgroup.centralizer ((F ⊔ E : Subgroup G) : Set G) :=
    hxeq ▸ hxC
  have hxFsub : (F : Set G) ⊆ (F ⊔ E : Subgroup G).1 := by
    intro y hy
    exact (le_sup_left : F ≤ F ⊔ E) hy
  have hxEsub : (E : Set G) ⊆ (F ⊔ E : Subgroup G).1 := by
    intro y hy
    exact (le_sup_right : E ≤ F ⊔ E) hy
  have hx_cent_F : f * e ∈ Subgroup.centralizer (F : Set G) :=
    (Subgroup.centralizer_le hxFsub) hxC'
  have hx_cent_E : f * e ∈ Subgroup.centralizer (E : Set G) :=
    (Subgroup.centralizer_le hxEsub) hxC'
  have hFE : F ≤ Subgroup.centralizer (E : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rw [Subgroup.commutator_comm]
    simpa [F, E] using layer_centralizes_fitting B
  have hf_cent_E : f ∈ Subgroup.centralizer (E : Set G) := hFE hf
  have he_cent_E : e ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxy : (f * e) * y = y * (f * e) :=
      ((Subgroup.mem_centralizer_iff.mp hx_cent_E y hy)).symm
    have hfy : f * y = y * f :=
      ((Subgroup.mem_centralizer_iff.mp hf_cent_E y hy)).symm
    have hconj_y : f⁻¹ * y * f = y := by
      calc
        f⁻¹ * y * f = f⁻¹ * (y * f) := by group
        _ = f⁻¹ * (f * y) := by rw [hfy]
        _ = y := by group
    calc
      y * e = (f⁻¹ * y * f) * e := by simpa [hconj_y]
      _ = f⁻¹ * (y * (f * e)) := by group
      _ = f⁻¹ * ((f * e) * y) := by rw [hxy]
      _ = e * y := by group
  have he_center : (⟨e, he⟩ : ↥E) ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact ((Subgroup.mem_centralizer_iff.mp he_cent_E (y : G) y.2))
  have heF : e ∈ F := by
    exact (center_layer_le_fitting B) (Subgroup.mem_map.mpr ⟨⟨e, he⟩, he_center, rfl⟩)
  have hxF' : f * e ∈ F := F.mul_mem hf heF
  have hxF : x ∈ F := hxeq.symm ▸ hxF'
  have hx_center : (⟨x, hxF⟩ : ↥F) ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hxG : (f * e : G) = (x : G) := hxeq.symm
    exact hxG ▸ (Subgroup.mem_centralizer_iff.mp hx_cent_F (y : G) y.2)
  exact Subgroup.mem_map.mpr ⟨⟨x, hxF⟩, hx_center, rfl⟩

/-- Early copy of the `F*(B)`-transport block, so that
`component_centralizes_Fstar_contradiction` can use it before the later
definition. -/
private theorem isComponentOf_of_isComponentOf_subgroup_early
    {G : Type u} [Group G] {A E : Subgroup G} (hE : IsComponentOf E A) :
    IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
  ⟨le_top, hE.2.1.subgroupOf,
    isQuasisimple_mulEquiv (Subgroup.subgroupOfEquivOfLe hE.1).symm hE.2.2⟩

private theorem isComponentOf_of_isComponentOf_top_map_early
    {G : Type u} [Group G] {B : Subgroup G} {E : Subgroup (↥B)}
    (hE : IsComponentOf E (⊤ : Subgroup (↥B))) :
    IsComponentOf (E.map B.subtype) B := by
  refine ⟨Subgroup.map_subtype_le E, ?_, ?_⟩
  · have hEsub : E.IsSubnormal := by
      have hmap : ((E.subgroupOf (⊤ : Subgroup (↥B))).map
          (⊤ : Subgroup (↥B)).subtype).IsSubnormal :=
        hE.2.1.map (f := (⊤ : Subgroup (↥B)).subtype)
          (by intro x; exact ⟨⟨x, trivial⟩, rfl⟩)
      rwa [Subgroup.map_subgroupOf_eq_of_le (le_top : E ≤ (⊤ : Subgroup (↥B)))] at hmap
    have hEq : (E.map B.subtype).subgroupOf B = E := by
      apply le_antisymm
      · intro y hy
        rw [Subgroup.mem_subgroupOf] at hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, hxy⟩
        have hyx : x = y := B.subtype_injective (by simpa using hxy)
        simpa [hyx] using hx
      · intro y hy
        rw [Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    simpa [hEq] using hEsub
  · exact isQuasisimple_mulEquiv
      (Subgroup.equivMapOfInjective E B.subtype B.subtype_injective) hE.2.2

private theorem componentLayer_top_map_eq_componentLayerOf_early
    {G : Type u} [Group G] (B : Subgroup G) :
    (componentLayerOf (⊤ : Subgroup (↥B))).map B.subtype = componentLayerOf B := by
  apply le_antisymm
  · refine (Subgroup.map_le_iff_le_comap).2 ?_
    change sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))} ≤
      Subgroup.comap B.subtype (componentLayerOf B)
    refine sSup_le ?_
    intro E hE
    intro y hy
    rw [Subgroup.mem_comap]
    exact le_sSup (s := {E' : Subgroup G | IsComponentOf E' B})
      (a := E.map B.subtype)
      (isComponentOf_of_isComponentOf_top_map_early hE)
      (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  · 
    change sSup {E : Subgroup G | IsComponentOf E B} ≤
      Subgroup.map B.subtype
        (sSup {E : Subgroup (↥B) | IsComponentOf E (⊤ : Subgroup (↥B))})
    refine sSup_le ?_
    intro E hE
    intro y hy
    exact Subgroup.mem_map.mpr
      ⟨⟨y, hE.1 hy⟩,
        Subgroup.mem_sSup_of_mem
          (isComponentOf_of_isComponentOf_subgroup_early hE)
          (by
            rw [Subgroup.mem_subgroupOf]
            exact hy),
        rfl⟩

private theorem map_fittingSubgroup_le_of_surjective_early
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) :
    (fittingSubgroup G).map f ≤ fittingSubgroup H := by
  have hmap_normal : ((fittingSubgroup G).map f).Normal :=
    Subgroup.Normal.map (H := fittingSubgroup G) inferInstance f hf
  have hmap_nil : Group.IsNilpotent ↥((fittingSubgroup G).map f) := by
    have : Group.IsNilpotent ↥(fittingSubgroup G) := by infer_instance
    let ψ : fittingSubgroup G →* ↥((fittingSubgroup G).map f) :=
      { toFun := fun g => ⟨f g, Subgroup.mem_map.mpr ⟨g.1, g.2, rfl⟩⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
    have hψsurj : Function.Surjective ψ := by
      intro x
      rcases (Subgroup.mem_map).1 x.2 with ⟨g, hg, hx⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      apply Subtype.ext
      exact hx
    exact Group.nilpotent_of_surjective ψ hψsurj
  exact le_sSup ⟨hmap_normal, hmap_nil⟩

private theorem map_fittingSubgroup_of_mulEquiv_early
    {G H : Type u} [Group G] [Group H] [Finite G] [Finite H]
    (e : G ≃* H) :
    (fittingSubgroup G).map e.toMonoidHom = fittingSubgroup H := by
  apply le_antisymm
  · exact map_fittingSubgroup_le_of_surjective_early e.toMonoidHom e.surjective
  · have hback : (fittingSubgroup H).map e.symm.toMonoidHom ≤ fittingSubgroup G :=
      map_fittingSubgroup_le_of_surjective_early e.symm.toMonoidHom e.symm.surjective
    have hmap : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom ≤
        (fittingSubgroup G).map e.toMonoidHom :=
      Subgroup.map_mono (f := e.toMonoidHom) hback
    have hleft : ((fittingSubgroup H).map e.symm.toMonoidHom).map e.toMonoidHom =
        fittingSubgroup H := by
      rw [Subgroup.map_map]
      have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by
        ext x
        simp
      rw [hcomp, Subgroup.map_id]
    rw [hleft] at hmap
    exact hmap

private theorem map_generalizedFittingSubgroupOf_top_subtype_early
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    (generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))).map B.subtype =
      generalizedFittingSubgroupOf B := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf, Subgroup.map_sup]
  rw [componentLayer_top_map_eq_componentLayerOf_early B]
  have : Finite (↥(⊤ : Subgroup (↥B))) :=
    Finite.of_equiv (↥B) (Subgroup.topEquiv (G := ↥B)).toEquiv.symm
  change Subgroup.map B.subtype ((fittingSubgroup (↥(⊤ : Subgroup (↥B)))).map
      (⊤ : Subgroup (↥B)).subtype) ⊔ componentLayerOf B =
    Subgroup.map B.subtype (fittingSubgroup (↥B)) ⊔ componentLayerOf B
  have hTopSubtype :
      (⊤ : Subgroup (↥B)).subtype =
        (Subgroup.topEquiv (G := ↥B)).toMonoidHom := by
    ext x
    rfl
  rw [hTopSubtype]
  rw [map_fittingSubgroup_of_mulEquiv_early (Subgroup.topEquiv (G := ↥B))]

/-- The generalized Fitting subgroup of `B` is self-centralizing inside
`B`, expressed in the ambient group. -/
public theorem centralizer_intersection_fstar_le_fstar
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    Subgroup.centralizer ((generalizedFittingSubgroupOf B : Set G)) ⊓ B ≤
      generalizedFittingSubgroupOf B := by
  let Y : Subgroup (↥B) := generalizedFittingSubgroupOf (⊤ : Subgroup (↥B))
  have hYcent : Subgroup.centralizer (Y : Set (↥B)) ≤ Y :=
    fstar_self_centralizing (G := ↥B)
  intro x hx
  rcases hx with ⟨hxC, hxB⟩
  let b : ↥B := ⟨x, hxB⟩
  have hbcent : b ∈ Subgroup.centralizer (Y : Set (↥B)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : (y : G) ∈ generalizedFittingSubgroupOf B := by
      rw [← map_generalizedFittingSubgroupOf_top_subtype_early B]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    have hxy := (Subgroup.mem_centralizer_iff.mp hxC) (y : G) hyG
    apply Subtype.ext
    exact hxy
  have hbY : b ∈ Y := hYcent hbcent
  have hxY : x ∈ Y.map B.subtype :=
    Subgroup.mem_map.mpr ⟨b, hbY, rfl⟩
  rwa [map_generalizedFittingSubgroupOf_top_subtype_early B] at hxY

/-- A perfect subgroup centralizing `F*(B)` is trivial; a component cannot
centralize it. -/
private theorem component_centralizes_Fstar_contradiction
    {G : Type u} [Group G] [Finite G]
    {B K : Subgroup G} (hK : IsQuasisimple K) (hKB : K ≤ B)
    (hKcent : ⁅K, generalizedFittingSubgroupOf B⁆ = ⊥) :
    False := by
  have hKleC : K ≤ Subgroup.centralizer ((generalizedFittingSubgroupOf B : Set G)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKcent
  have hKleFstar : K ≤ generalizedFittingSubgroupOf B := by
    intro k hk
    exact centralizer_intersection_fstar_le_fstar B ⟨hKleC hk, hKB hk⟩
  have hKleZ : K ≤
      (Subgroup.center (fittingSubgroupOf B)).map (fittingSubgroupOf B).subtype := by
    intro k hk
    exact (centralizer_self_le_fitting_center B) ⟨hKleFstar hk, hKleC hk⟩
  have hKcomm : IsMulCommutative K := by
    refine IsMulCommutative.of_comm (M := K) ?_
    intro a b
    apply Subtype.ext
    have ha : (a : G) ∈ (Subgroup.center (fittingSubgroupOf B)).map
        (fittingSubgroupOf B).subtype := hKleZ a.2
    have hb : (b : G) ∈ (Subgroup.center (fittingSubgroupOf B)).map
        (fittingSubgroupOf B).subtype := hKleZ b.2
    rcases Subgroup.mem_map.mp ha with ⟨za, hza, hza_eq⟩
    rcases Subgroup.mem_map.mp hb with ⟨zb, hzb, hzb_eq⟩
    have hzaG : (za : G) = (a : G) := hza_eq
    have hzbG : (zb : G) = (b : G) := hzb_eq
    have hz : (za : ↥(fittingSubgroupOf B)) * (zb : ↥(fittingSubgroupOf B)) =
        (zb : ↥(fittingSubgroupOf B)) * (za : ↥(fittingSubgroupOf B)) :=
      ((Subgroup.mem_center_iff.mp hza (zb : ↥(fittingSubgroupOf B)))).symm
    have hzG : (za : G) * (zb : G) = (zb : G) * (za : G) := congrArg Subtype.val hz
    calc
      (a : G) * (b : G) = (za : G) * (zb : G) := by rw [hzaG, hzbG]
      _ = (zb : G) * (za : G) := hzG
      _ = (b : G) * (a : G) := by rw [hzaG, hzbG]
  have : Nontrivial K := hK.1
  have : Group.IsPerfect K := (Group.isPerfect_def).2 hK.2.1
  exact Group.IsPerfect.not_isMulCommutative (G := K) hKcomm

/-- If `K` centralizes `F` and `E`, then it centralizes `F ⊔ E`. -/
private lemma centralizer_sup_of_centralizes {G : Type u} [Group G]
    {K F E : Subgroup G} (hKF : K ≤ Subgroup.centralizer (F : Set G))
    (hKE : K ≤ Subgroup.centralizer (E : Set G)) :
    K ≤ Subgroup.centralizer ((F ⊔ E : Subgroup G) : Set G) := by
  intro k hk y hy
  rw [Subgroup.sup_eq_closure] at hy
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hy
  · intro v hv
    rcases hv with hvF | hvE
    · exact (Subgroup.mem_centralizer_iff.mp (hKF hk) v hvF)
    · exact (Subgroup.mem_centralizer_iff.mp (hKE hk) v hvE)
  · intro v hv
    rcases hv with hvF | hvE
    · have hkv : k * v = v * k :=
        ((Subgroup.mem_centralizer_iff.mp (hKF hk) v hvF)).symm
      have hright : (v⁻¹ * k) * v = (k * v⁻¹) * v := by
        calc
          (v⁻¹ * k) * v = v⁻¹ * (k * v) := by group
          _ = v⁻¹ * (v * k) := by rw [hkv]
          _ = k := by group
          _ = (k * v⁻¹) * v := by group
      exact mul_right_cancel hright
    · have hkv : k * v = v * k :=
        ((Subgroup.mem_centralizer_iff.mp (hKE hk) v hvE)).symm
      have hright : (v⁻¹ * k) * v = (k * v⁻¹) * v := by
        calc
          (v⁻¹ * k) * v = v⁻¹ * (k * v) := by group
          _ = v⁻¹ * (v * k) := by rw [hkv]
          _ = k := by group
          _ = (k * v⁻¹) * v := by group
      exact mul_right_cancel hright
  · simpa using (Subgroup.mem_centralizer_iff.mp (hKF hk) (1 : G) F.one_mem)
  · intro a b _ha _hb hka hkb
    calc
      (a * b) * k = a * (b * k) := by group
      _ = a * (k * b) := by rw [hkb]
      _ = (a * k) * b := by group
      _ = (k * a) * b := by rw [hka]
      _ = k * (a * b) := by group

/-- A component cannot centralize both the Fitting and the layer of `B`. -/
private theorem component_centralizes_Fstar_of_commute_E
    {G : Type u} [Group G] [Finite G]
    {B K : Subgroup G} (hK : IsQuasisimple K) (hKB : K ≤ B)
    (hKF : ⁅K, fittingSubgroupOf B⁆ = ⊥)
    (hKE : ⁅K, componentLayerOf B⁆ = ⊥) :
    False := by
  have hKFc : K ≤ Subgroup.centralizer ((fittingSubgroupOf B : Set G)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKF
  have hKEc : K ≤ Subgroup.centralizer ((componentLayerOf B : Set G)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hKE
  have hKsup : K ≤ Subgroup.centralizer
      ((fittingSubgroupOf B ⊔ componentLayerOf B : Subgroup G) : Set G) :=
    centralizer_sup_of_centralizes hKFc hKEc
  have hcomm : ⁅K, generalizedFittingSubgroupOf B⁆ = ⊥ := by
    apply (Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
    simpa [generalizedFittingSubgroupOf] using hKsup
  exact component_centralizes_Fstar_contradiction hK hKB hcomm

/-- Every component of `A` is subnormal in the layer `E(A)`. -/
private theorem component_subnormal_in_layer
    {G : Type u} [Group G] [Finite G] {A E : Subgroup G} (hE : IsComponentOf E A) :
    (E.subgroupOf (componentLayerOf A)).IsSubnormal := by
  have hE0 : IsComponentOf (E.subgroupOf A) (⊤ : Subgroup (↥A)) :=
    isComponentOf_of_isComponentOf_subgroup_early hE
  have hEAlayer : componentLayerOf A ≤ Subgroup.normalizer (E : Set G) := by
    rw [componentLayerOf]
    refine sSup_le ?_
    intro F hF
    by_cases hFE : F = E
    · rw [hFE]
      exact E.le_normalizer
    · have hF0 : IsComponentOf (F.subgroupOf A) (⊤ : Subgroup (↥A)) :=
        isComponentOf_of_isComponentOf_subgroup_early hF
      have hne0 : E.subgroupOf A ≠ F.subgroupOf A := by
        intro h
        have hinf : E ⊓ A = F ⊓ A := (Subgroup.subgroupOf_inj (H₁ := E) (H₂ := F) (K := A)).mp h
        have hEinf : E ⊓ A = E := inf_eq_left.mpr hE.1
        have hFinf : F ⊓ A = F := inf_eq_left.mpr hF.1
        have hEF : E = F := by
          rw [hEinf, hFinf] at hinf
          exact hinf
        exact hFE hEF.symm
      have hcommA : ⁅E.subgroupOf A, F.subgroupOf A⁆ = ⊥ :=
        component_commute_of_ne (G := ↥A) hE0 hF0 hne0
      have hcommG : ⁅E, F⁆ = ⊥ :=
        (commutator_subgroupOf_eq_bot_iff_of_le hE.1 hF.1).mp hcommA
      have hFcent : F ≤ Subgroup.centralizer (E : Set G) := by
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        rw [Subgroup.commutator_comm]
        exact hcommG
      exact (hFcent.trans (Subgroup.centralizer_le_normalizer (E : Set G)))
  have hE_normal : (E.subgroupOf (componentLayerOf A)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := componentLayerOf A) (N := E) hEAlayer
  exact hE_normal.isSubnormal

/-- A component of `A` is a component of every subgroup `L` with
`F*(A) ≤ L ≤ A`. -/
private theorem isComponentOf_of_fstar_le
    {G : Type u} [Group G] [Finite G]
    {L A K : Subgroup G} (hK : IsComponentOf K A)
    (hFL : generalizedFittingSubgroupOf A ≤ L) (hLA : L ≤ A) :
    IsComponentOf K L := by
  have hKleEA : K ≤ componentLayerOf A :=
    le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) (a := K) hK
  have hKleL : K ≤ L :=
    hKleEA.trans ((le_sup_right : componentLayerOf A ≤ generalizedFittingSubgroupOf A).trans hFL)
  have hEAL : componentLayerOf A ≤ L :=
    (le_sup_right : componentLayerOf A ≤ generalizedFittingSubgroupOf A).trans hFL
  have hEAnormL : IsNormalIn (componentLayerOf A) L := by
    refine ⟨hEAL, ?_⟩
    intro l hl e he
    exact (componentLayerOf_isNormalIn A).2 l (hLA hl) e he
  exact ⟨hKleL,
    isSubnormal_of_isNormalIn_subgroup hEAL hEAnormL hKleEA (component_subnormal_in_layer hK),
    hK.2.2⟩

/-- The component--subnormal dichotomy transported to ambient subgroups:
if `K` is a component of `L` and `N` is normal in `L`, then `K ≤ N` or
`⁅K,N⁆ = ⊥`. -/
private theorem component_le_of_normal_dichotomy
    {G : Type u} [Group G] [Finite G]
    {L N K : Subgroup G} (hK : IsComponentOf K L)
    (hNL : N ≤ L) (hN : IsNormalIn N L) :
    K ≤ N ∨ ⁅K, N⁆ = ⊥ := by
  have hKtopL : IsComponentOf (K.subgroupOf L) (⊤ : Subgroup (↥L)) :=
    isComponentOf_of_isComponentOf_subgroup_early hK
  let N' : Subgroup (↥L) := N.subgroupOf L
  have hN'norm : N'.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := N)
      (le_normalizer_of_isNormalIn hN)
  rcases component_le_or_commutator_eq_bot (G := (↥L)) hKtopL hN'norm.isSubnormal with
    hle | hcomm
  · left
    exact (subgroupOf_le_subgroupOf_iff_of_le hK.1 hNL).mp hle
  · right
    exact (commutator_subgroupOf_eq_bot_iff_of_le hK.1 hNL).mp hcomm

/-- Under mutual `F*` containments, every component of `A` lies in the
layer of `B`. -/
private theorem component_le_layer_of_fstar_contained
    {G : Type u} [Group G] [Finite G]
    {A B K : Subgroup G} (hK : IsComponentOf K A)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A) :
    K ≤ componentLayerOf B := by
  let L : Subgroup G := A ⊓ B
  have hFL : generalizedFittingSubgroupOf A ≤ L := by
    exact le_inf (generalizedFittingSubgroupOf_le A) hFAB
  have hLA : L ≤ A := inf_le_left
  have hFLB : generalizedFittingSubgroupOf B ≤ L := by
    exact le_inf hFBA (generalizedFittingSubgroupOf_le B)
  have hLB : L ≤ B := inf_le_right
  have hKcompL : IsComponentOf K L := isComponentOf_of_fstar_le hK hFL hLA
  have hKleL : K ≤ L := hKcompL.1
  have hKleB : K ≤ B := hKleL.trans hLB
  have hFBLnorm : IsNormalIn (generalizedFittingSubgroupOf B) L := by
    refine ⟨hFLB, ?_⟩
    intro l hl x hx
    exact (generalizedFittingSubgroupOf_isNormalIn B).2 l (hLB hl) x hx
  have hKleFstar : K ≤ generalizedFittingSubgroupOf B := by
    rcases component_le_of_normal_dichotomy hKcompL hFLB hFBLnorm with hle | hcomm
    · exact hle
    · exfalso
      exact component_centralizes_Fstar_contradiction hK.2.2 hKleB hcomm
  have hEBL : componentLayerOf B ≤ L :=
    (le_sup_right : componentLayerOf B ≤ generalizedFittingSubgroupOf B).trans hFLB
  have hEBnorm : IsNormalIn (componentLayerOf B) L := by
    refine ⟨hEBL, ?_⟩
    intro l hl e he
    exact (componentLayerOf_isNormalIn B).2 l (hLB hl) e he
  have hKF : ⁅K, fittingSubgroupOf B⁆ = ⊥ := by
    have hFnormB : IsNormalIn (fittingSubgroupOf B) B := fittingSubgroupOf_isNormalIn B
    have hBleN : B ≤ Subgroup.normalizer ((fittingSubgroupOf B : Subgroup G) : Set G) :=
      le_normalizer_of_isNormalIn hFnormB
    have hKN : K ≤ Subgroup.normalizer ((fittingSubgroupOf B : Subgroup G) : Set G) :=
      hKleB.trans hBleN
    have hFA : fittingSubgroupOf B ≤ A :=
      (le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans hFBA
    exact component_centralizes_normalized_nilpotent hK hKN hFA
      (fittingSubgroupOf_isNilpotent B)
  rcases component_le_of_normal_dichotomy hKcompL hEBL hEBnorm with hleE | hcommE
  · exact hleE
  · exfalso
    exact component_centralizes_Fstar_of_commute_E hK.2.2 hKleB hKF hcommE

/-- Under the hypotheses of Statement 1.6, both layers are trivial. -/
private theorem componentLayerOf_eq_bot_of_pair
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G) (A B : Subgroup G)
    (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A) :
    componentLayerOf A = ⊥ := by
  have hEAB : componentLayerOf A ≤ componentLayerOf B := by
    rw [componentLayerOf, componentLayerOf]
    apply sSup_le
    intro K hK
    exact component_le_layer_of_fstar_contained hK hFAB hFBA
  have hEBA : componentLayerOf B ≤ componentLayerOf A := by
    rw [componentLayerOf, componentLayerOf]
    apply sSup_le
    intro K hK
    exact component_le_layer_of_fstar_contained hK hFBA hFAB
  have hEeq : componentLayerOf A = componentLayerOf B := le_antisymm hEAB hEBA
  by_contra hEne
  let N : Subgroup G := componentLayerOf A
  have hNleA : N ≤ A := componentLayerOf_le A
  have hNnormA : IsNormalIn N A := componentLayerOf_isNormalIn A
  have hNnormB : IsNormalIn N B := by
    change IsNormalIn (componentLayerOf A) B
    rw [hEeq]
    exact componentLayerOf_isNormalIn B
  have hAleN : A ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_isNormalIn hNnormA
  have hBleN : B ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_of_isNormalIn hNnormB
  let NG : Subgroup G := Subgroup.normalizer (N : Set G)
  have hNGne_top : NG ≠ ⊤ := by
    intro htop
    have hNnormG : N.Normal := by
      rw [Subgroup.normalizer_eq_top_iff] at htop
      exact htop
    rcases (haveI := hNnormG; hsimple.eq_bot_or_eq_top_of_normal N) with hbot | htopN
    · exact hEne hbot
    · have hAtop : A = ⊤ := by
        have hTopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          exact hNleA (htopN ▸ hx)
        exact le_antisymm le_top hTopLeA
      exact hA.1 hAtop
  have hNGA : NG ≤ A := by
    by_cases hEq : A = NG
    · rw [hEq]
    · have hneNG : A ≠ NG := fun h => hEq h
      have hlt : A < NG := lt_of_le_of_ne hAleN hneNG
      have htop := hA.2 NG hlt
      exact False.elim (hNGne_top htop)
  have hNGB : NG ≤ B := by
    by_cases hEq : B = NG
    · rw [hEq]
    · have hneNG : B ≠ NG := fun h => hEq h
      have hlt : B < NG := lt_of_le_of_ne hBleN hneNG
      have htop := hB.2 NG hlt
      exact False.elim (hNGne_top htop)
  have hAeqNG : A = NG := le_antisymm hAleN hNGA
  have hBeqNG : B = NG := le_antisymm hBleN hNGB
  exact hne (hAeqNG.trans hBeqNG.symm)

/-! ## `O^p(F*(A))` centralizes `O_p(A)` (mirrored from the 1.8 module) -/

private theorem pResidualOf_le_of_quotient_isPGroup_local
    {G : Type u} [Group G] [Finite G]
    (H N : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hNle : N ≤ H)
    (hN : (N.subgroupOf H).Normal)
    (hQ : IsPGroup p (H ⧸ N.subgroupOf H)) :
    pResidualOf H p ≤ N := by
  let : Fact p.Prime := ⟨hp⟩
  rcases (IsPGroup.iff_card.mp hQ) with ⟨n, hn⟩
  have hidx : ∃ n : ℕ, (N.subgroupOf H).index = p ^ n := ⟨n, by
    rw [← hn]
    exact (Subgroup.index_eq_card (N.subgroupOf H)).symm⟩
  have hle := pResidualOf_le_of_normal_index H p (N.subgroupOf H) hN hidx
  simpa [Subgroup.map_subgroupOf_eq_of_le hNle] using hle

private theorem mem_pResidualOf_of_order_coprime_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) {x : G} (hx : x ∈ H)
    (hcop : Nat.Coprime p (orderOf x)) : x ∈ pResidualOf H p := by
  rw [pResidualOf]
  refine Subgroup.mem_map.mpr ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [Subgroup.mem_sInf]
  intro N hN
  rcases hN with ⟨hNnormal, n, hn⟩
  let : Fact p.Prime := ⟨hp⟩
  have hQ : IsPGroup p (H ⧸ N) := IsPGroup.of_card (n := n) (by
    rw [← hn]
    exact (Subgroup.index_eq_card N).symm)
  let q : H ⧸ N := QuotientGroup.mk' N ⟨x, hx⟩
  have hcopH : Nat.Coprime p (orderOf (⟨x, hx⟩ : H)) := by
    have hord : orderOf (⟨x, hx⟩ : H) = orderOf x :=
      (orderOf_injective H.subtype H.subtype_injective (⟨x, hx⟩ : H)).symm
    rwa [hord]
  have hqcop : (orderOf q).Coprime (orderOf (⟨x, hx⟩ : H)) :=
    hQ.orderOf_coprime hcopH q
  have hqdiv : orderOf q ∣ orderOf (⟨x, hx⟩ : H) :=
    orderOf_map_dvd (QuotientGroup.mk' N) (⟨x, hx⟩)
  have hq1 : q = 1 :=
    (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hqcop dvd_rfl hqdiv))
  exact (QuotientGroup.eq_one_iff (N := N) (x := (⟨x, hx⟩ : H))).1 hq1

private theorem isPGroup_of_pResidualOf_isPGroup_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hR : IsPGroup p (pResidualOf H p)) : IsPGroup p H := by
  apply isPGroup_of_primeFactors_subset_singleton H hp
  intro q hq
  by_contra hqp
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvd : q ∣ Nat.card (↥H) := Nat.dvd_of_mem_primeFactors hq
  let : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨x, hxorder⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) q hqdvd
  have hordG : orderOf (x : G) = q := by
    calc
      orderOf (x : G) = orderOf x :=
        by simpa using (orderOf_injective H.subtype H.subtype_injective x).symm
      _ = q := hxorder
  have hcopq : Nat.Coprime p q := (Nat.coprime_primes hp hqprime).2 (by
    intro hpq
    exact hqp hpq.symm)
  have hcop : Nat.Coprime p (orderOf (x : G)) := by
    rwa [hordG]
  have hxR : (x : G) ∈ pResidualOf H p :=
    mem_pResidualOf_of_order_coprime_local H p hp x.2 hcop
  let r : pResidualOf H p := ⟨x, hxR⟩
  let : Fact p.Prime := ⟨hp⟩
  have hRcop : (orderOf r).Coprime q := hR.orderOf_coprime hcopq r
  have hordR : orderOf r = q := by
    calc
      orderOf r = orderOf (r : G) :=
        (orderOf_injective (pResidualOf H p).subtype
          (pResidualOf H p).subtype_injective r).symm
      _ = orderOf (x : G) := rfl
      _ = q := hordG
  have hqcop : q.Coprime q := hordR ▸ hRcop
  exact hqprime.ne_one (Nat.eq_one_of_dvd_coprimes hqcop dvd_rfl dvd_rfl)

private theorem pResidualOf_subgroupOf_characteristic_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Characteristic := by
  classical
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  have hNres : (pResidualOf H p).subgroupOf H = sInf family := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective (sInf family)
  rw [hNres]
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  exact pResidual_map_iso (G := H) (H := H) p e

private instance pResidualOf_subgroupOf_normal_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) :
    ((pResidualOf H p).subgroupOf H).Normal := by
  have : ((pResidualOf H p).subgroupOf H).Characteristic :=
    pResidualOf_subgroupOf_characteristic_local H p
  infer_instance

private theorem isPGroup_quotient_pResidualOf_local
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (hp : p.Prime) :
    IsPGroup p (H ⧸ (pResidualOf H p).subgroupOf H) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have : ((pResidualOf H p).subgroupOf H).Normal := pResidualOf_subgroupOf_normal_local H p
  let family : Set (Subgroup H) :=
    {N : Subgroup H | N.Normal ∧ ∃ n : ℕ, N.index = p ^ n}
  let N : Subgroup H := sInf family
  have hNres : (pResidualOf H p).subgroupOf H = N := by
    unfold pResidualOf
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective N
  let ι : Type u := {M : Subgroup H // M ∈ family}
  have : Finite ι := Finite.of_injective (fun M : ι => (M : Subgroup H)) (by
    intro M N h
    exact Subtype.ext h)
  let : Fintype ι := Fintype.ofFinite ι
  have : ∀ M : ι, (M : Subgroup H).Normal := fun M => M.2.1
  have : N.Normal := by
    change (sInf family).Normal
    rw [sInf_eq_iInf']
    exact Subgroup.normal_iInf_normal (fun M : ι => M.2.1)
  let n : ι → ℕ := fun M => Classical.choose M.2.2
  have hn : ∀ M : ι, (M : Subgroup H).index = p ^ n M := fun M =>
    Classical.choose_spec M.2.2
  have hQcard : ∀ M : ι, Nat.card (H ⧸ (M : Subgroup H)) = p ^ n M := by
    intro M
    rw [← hn M, Subgroup.index_eq_card]
  let T : Type u := ∀ M : ι, H ⧸ (M : Subgroup H)
  have hTcard : Nat.card T = p ^ (∑ M, n M) := by
    rw [Nat.card_pi]
    simp_rw [hQcard]
    rw [Finset.prod_pow_eq_pow_sum]
  have hT : IsPGroup p T := IsPGroup.of_card hTcard
  let f : H →* T :=
    { toFun := fun h M => QuotientGroup.mk' (M : Subgroup H) h
      map_one' := by ext M; rfl
      map_mul' := by intro x y; ext M; rfl }
  have hfker : f.ker = N := by
    ext h
    constructor
    · intro hh
      rw [Subgroup.mem_sInf]
      intro M hM
      have : M.Normal := hM.1
      have hcomp : QuotientGroup.mk' M h = (1 : H ⧸ M) := congrFun hh ⟨M, hM⟩
      exact (QuotientGroup.eq_one_iff (N := M) h).1 hcomp
    · intro hh
      ext M
      have : (M : Subgroup H).Normal := M.2.1
      exact (QuotientGroup.eq_one_iff (N := (M : Subgroup H)) h).2
        ((Subgroup.mem_sInf.mp hh) (M : Subgroup H) M.2)
  let eN : H ⧸ N ≃* f.range :=
    (QuotientGroup.congr (G' := f.ker) (H' := N) (MulEquiv.refl H) (by simpa using hfker)).symm.trans
      (QuotientGroup.quotientKerEquivRange f)
  let eRes : H ⧸ (pResidualOf H p).subgroupOf H ≃* f.range :=
    (QuotientGroup.congr (G' := N)
      (H' := (pResidualOf H p).subgroupOf H) (MulEquiv.refl H)
        (by simpa using hNres.symm)).symm.trans eN
  have hRange : IsPGroup p (f.range : Subgroup T) :=
    hT.to_subgroup (f.range : Subgroup T)
  exact hRange.of_equiv eRes.symm

private theorem qCoreOf_le_fittingSubgroupOf_local {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) : qCoreOf A p ≤ fittingSubgroupOf A := by
  let : Fact p.Prime := ⟨hp⟩
  have hle : pCore p (↥A) ≤ fittingSubgroup (↥A) :=
    pCore_le_fitting (G := ↥A) p
  exact Subgroup.map_mono (f := A.subtype) hle

private theorem qCoreOf_centralizer_of_ne_local {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) :
    qCoreOf A q ≤ Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases (Subgroup.mem_map).1 hx with ⟨x₀, hx₀, rfl⟩
  rcases (Subgroup.mem_map).1 hy with ⟨y₀, hy₀, rfl⟩
  have hdisj : Disjoint (pCore q (↥A)) (pCore p (↥A)) :=
    IsPGroup.disjoint_of_ne q p (hne.symm)
      (pCore q (↥A)) (pCore p (↥A))
      (pCore_isPGroup (p := q) (G := ↥A)) (pCore_isPGroup (p := p) (G := ↥A))
  have hcomm₀ : ⁅x₀, y₀⁆ = (1 : ↥A) := by
    have hmem : ⁅x₀, y₀⁆ ∈ ⁅pCore q (↥A), pCore p (↥A)⁆ :=
      Subgroup.commutator_mem_commutator hx₀ hy₀
    have hle : ⁅pCore q (↥A), pCore p (↥A)⁆ ≤
        pCore q (↥A) ⊓ pCore p (↥A) :=
      Subgroup.commutator_le_inf (H₁ := pCore q (↥A)) (H₂ := pCore p (↥A))
    have hinf : (pCore q (↥A) ⊓ pCore p (↥A) : Subgroup (↥A)) = ⊥ := by
      exact hdisj.eq_bot
    have : ⁅x₀, y₀⁆ ∈ (⊥ : Subgroup (↥A)) := by
      rw [← hinf]
      exact hle hmem
    simpa using this
  exact congrArg Subtype.val ((commutatorElement_eq_one_iff_mul_comm.mp hcomm₀).symm)

private theorem fittingSubgroupOf_eq_iSup_qCoreOf_local {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) :
    fittingSubgroupOf A =
      ⨆ q : (Nat.card (↥A)).primeFactors.attach, qCoreOf A q.1.1 := by
  unfold fittingSubgroupOf qCoreOf
  rw [fitting_eq_sup_pCore, Subgroup.map_iSup]

private theorem pResidualOf_generalizedFitting_centralizer_qCore_local
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    pResidualOf (generalizedFittingSubgroupOf A) p ≤
      Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) := by
  classical
  let H : Subgroup G := generalizedFittingSubgroupOf A
  let F : Subgroup G := fittingSubgroupOf A
  let E : Subgroup G := componentLayerOf A
  let P : Subgroup G := qCoreOf A p
  let Z : Subgroup G := Subgroup.centralizer (P : Set G)
  let K : Subgroup G := H ⊓ Z
  have hHF : F ≤ H := le_sup_left
  have hHE : E ≤ H := le_sup_right
  have hHA : H ≤ A := generalizedFittingSubgroupOf_le A
  have hFA : F ≤ A := by
    exact hHF.trans hHA
  have hPleF : P ≤ F := qCoreOf_le_fittingSubgroupOf_local A p hp
  have hPleH : P ≤ H := hPleF.trans hHF
  have hPleA : P ≤ A := hPleF.trans hFA
  have hEF : E ≤ Subgroup.centralizer (F : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := E) (H₂ := F)).mp (layer_centralizes_fitting A)
  have hZF : Subgroup.centralizer (F : Set G) ≤ Z :=
    Subgroup.centralizer_le (show (P : Set G) ⊆ (F : Set G) from hPleF)
  have hEcentral : E ≤ Z := hEF.trans hZF
  have hHnormP : H ≤ Subgroup.normalizer (P : Set G) := by
    refine (Subgroup.le_normalizer_iff).mpr ?_
    intro h hh z hz
    exact (qCoreOf_normal_in A p).2 h (hHA hh) z hz
  have hKleH : K ≤ H := inf_le_left
  have hKnormal : (K.subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKleH]
    intro x h hx hh
    have hxH : x ∈ H := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxZ' : x ∈ Subgroup.centralizer (P : Set G) := hxZ
    have hmH : h * x * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hxH) (H.inv_mem hh)
    have hmZ : h * x * h⁻¹ ∈ Z := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : h⁻¹ * z * h ∈ P :=
        by simpa using
          (Subgroup.le_set_normalizer_iff).1 hHnormP (h⁻¹) (H.inv_mem hh) z hz
      have hkx : x * (h⁻¹ * z * h) = (h⁻¹ * z * h) * x :=
        (Subgroup.mem_centralizer_iff.mp hxZ' (h⁻¹ * z * h) hz').symm
      have hmain : (h * x * h⁻¹) * z = z * (h * x * h⁻¹) := by
        calc
          (h * x * h⁻¹) * z = h * (x * (h⁻¹ * z * h)) * h⁻¹ := by group
          _ = h * ((h⁻¹ * z * h) * x) * h⁻¹ := by rw [hkx]
          _ = z * (h * x * h⁻¹) := by group
      exact hmain.symm
    exact ⟨hmH, hmZ⟩
  let π : H →* H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H)
  have hKmap : (K.subgroupOf H).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := K.subgroupOf H) (f := π)).2
    intro x hx
    simpa [π, QuotientGroup.ker_mk'] using hx
  have hPsub : IsPGroup p (P.subgroupOf H) :=
    (qCoreOf_isPGroup A p).of_equiv (Subgroup.subgroupOfEquivOfLe hPleH).symm
  have hPm : IsPGroup p ((P.subgroupOf H).map π) :=
    IsPGroup.map hPsub π
  have hFleKP : F ≤ K ⊔ P := by
    change fittingSubgroupOf A ≤ K ⊔ P
    rw [fittingSubgroupOf_eq_iSup_qCoreOf_local A]
    refine iSup_le ?_
    intro q
    by_cases hqp : q.1.1 = p
    · rw [hqp]
      exact le_sup_right
    · have hqprime : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
      have hQleZ : qCoreOf A q.1.1 ≤ Z :=
        qCoreOf_centralizer_of_ne_local A hp hqprime (by
          intro hpq
          exact hqp hpq.symm)
      have hQleH : qCoreOf A q.1.1 ≤ H :=
        (qCoreOf_le_fittingSubgroupOf_local A q.1.1 hqprime).trans hHF
      exact le_trans (le_inf hQleH hQleZ) le_sup_left
  have hFm_le : (F.subgroupOf H).map π ≤ (P.subgroupOf H).map π := by
    calc
      (F.subgroupOf H).map π ≤ ((K ⊔ P).subgroupOf H).map π :=
        Subgroup.map_mono (f := π) (Subgroup.subgroupOf_mono H hFleKP)
      _ = ((K.subgroupOf H ⊔ P.subgroupOf H).map π) := by
        rw [Subgroup.subgroupOf_sup hKleH hPleH]
      _ = (P.subgroupOf H).map π := by
        rw [Subgroup.map_sup, hKmap]
        simp
  have hFm : IsPGroup p ((F.subgroupOf H).map π) :=
    IsPGroup.to_le hPm hFm_le
  have hEm : IsPGroup p ((E.subgroupOf H).map π) := by
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    rw [hEmap]
    exact IsPGroup.of_bot
  have htop_eq : (⊤ : Subgroup H) = F.subgroupOf H ⊔ E.subgroupOf H := by
    rw [← Subgroup.subgroupOf_self H]
    change (F ⊔ E).subgroupOf H = F.subgroupOf H ⊔ E.subgroupOf H
    exact Subgroup.subgroupOf_sup hHF hHE
  have hQ : IsPGroup p ((⊤ : Subgroup H).map π) := by
    rw [htop_eq, Subgroup.map_sup]
    have hEmap : (E.subgroupOf H).map π = ⊥ := by
      apply (Subgroup.map_eq_bot_iff (H := E.subgroupOf H) (f := π)).2
      intro e he
      have heH : e.1 ∈ H := hHE (Subgroup.mem_subgroupOf.mp he)
      have heZ : e.1 ∈ Z := hEcentral (Subgroup.mem_subgroupOf.mp he)
      have heK : (e : G) ∈ K := ⟨heH, heZ⟩
      simpa [π, QuotientGroup.ker_mk'] using (Subgroup.mem_subgroupOf).mpr heK
    have : ((E.subgroupOf H).map π).Normal := by
      rw [hEmap]
      infer_instance
    exact IsPGroup.to_sup_of_normal_right hFm hEm
  have hQquot : IsPGroup p (H ⧸ K.subgroupOf H) := by
    have htopmap : (⊤ : Subgroup H).map π = ⊤ :=
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective (K.subgroupOf H))
    have hQtop : IsPGroup p (⊤ : Subgroup (H ⧸ K.subgroupOf H)) := by
      rw [← htopmap]
      exact hQ
    exact hQtop.of_equiv Subgroup.topEquiv
  have hRes : pResidualOf H p ≤ K :=
    pResidualOf_le_of_quotient_isPGroup_local H K p hp hKleH hKnormal hQquot
  exact hRes.trans inf_le_right

/-- `F(A) ≤ F(L)` when `F*(A) ≤ L ≤ A`. -/
private theorem fittingSubgroupOf_le_of_le
    {G : Type u} [Group G] [Finite G]
    {L A : Subgroup G} (hFL : generalizedFittingSubgroupOf A ≤ L) (hLA : L ≤ A) :
    fittingSubgroupOf A ≤ fittingSubgroupOf L := by
  have hFleL : fittingSubgroupOf A ≤ L :=
    (le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFL
  have hFnormL : IsNormalIn (fittingSubgroupOf A) L := by
    refine ⟨hFleL, ?_⟩
    intro l hl f hf
    exact (fittingSubgroupOf_isNormalIn A).2 l (hLA hl) f hf
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent hFleL hFnormL
    (fittingSubgroupOf_isNilpotent A)

/-- `E(A) ≤ E(L)` when `F*(A) ≤ L ≤ A`. -/
private theorem componentLayerOf_le_of_le
    {G : Type u} [Group G] [Finite G]
    {L A : Subgroup G} (hFL : generalizedFittingSubgroupOf A ≤ L) (hLA : L ≤ A) :
    componentLayerOf A ≤ componentLayerOf L := by
  have hEA_le_L : componentLayerOf A ≤ L :=
    (le_sup_right : componentLayerOf A ≤ generalizedFittingSubgroupOf A).trans hFL
  have hEA_normL : IsNormalIn (componentLayerOf A) L := by
    refine ⟨hEA_le_L, ?_⟩
    intro l hl e he
    exact (componentLayerOf_isNormalIn A).2 l (hLA hl) e he
  rw [componentLayerOf, componentLayerOf]
  apply sSup_le
  intro E hE
  have hE_le_EA : E ≤ componentLayerOf A :=
    le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) (a := E) hE
  refine le_sSup (s := {E' : Subgroup G | IsComponentOf E' L}) ?_
  exact ⟨hE_le_EA.trans hEA_le_L,
    isSubnormal_of_isNormalIn_subgroup hEA_le_L hEA_normL
      (le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) (a := E) hE)
      (component_subnormal_in_layer hE),
    hE.2.2⟩

/-- `F*(A) ≤ F*(L)` when `F*(A) ≤ L ≤ A`. -/
private theorem generalizedFittingSubgroupOf_le_of_le
    {G : Type u} [Group G] [Finite G]
    {L A : Subgroup G} (hFL : generalizedFittingSubgroupOf A ≤ L) (hLA : L ≤ A) :
    generalizedFittingSubgroupOf A ≤ generalizedFittingSubgroupOf L := by
  rw [generalizedFittingSubgroupOf, generalizedFittingSubgroupOf]
  exact sup_le
    ((fittingSubgroupOf_le_of_le hFL hLA).trans le_sup_left)
    ((componentLayerOf_le_of_le hFL hLA).trans le_sup_right)

/-- A subnormal subgroup which is contained in a normal subgroup is
subnormal in that normal subgroup. -/
private theorem isSubnormal_of_subnormal_le_normal
    {G : Type u} [Group G] {S X : Subgroup G}
    (hS : S.IsSubnormal) (hSX : S ≤ X) (hX : X.Normal) :
    (S.subgroupOf X).IsSubnormal := by
  classical
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := G) (H := S)).1 hS with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  let g : ℕ → Subgroup (↥X) := fun i => (f i ⊓ X).subgroupOf X
  have hg0 : g 0 = S.subgroupOf X := by
    simp [g, hf0, Subgroup.inf_subgroupOf_right]
  have hgn : g n = ⊤ := by
    simp [g, hfn]
  have hgmono : Monotone g := by
    intro i j hij
    exact Subgroup.subgroupOf_mono X (inf_le_inf (hmono hij) le_rfl)
  have hgnorm : ∀ i, ((g i).subgroupOf (g (i + 1))).Normal := by
    intro i
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (h := hgmono (Nat.le_succ i))]
    rw [Subgroup.le_normalizer_iff]
    intro x hx y hy
    rw [Subgroup.mem_subgroupOf]
    have hxval : (x : G) ∈ f (i + 1) ⊓ X := (Subgroup.mem_subgroupOf).mp hx
    have hyval : (y : G) ∈ f i ⊓ X := (Subgroup.mem_subgroupOf).mp hy
    constructor
    · have hxfi : (x : G) ∈ f (i + 1) := hxval.1
      have hyfi : (y : G) ∈ f i := hyval.1
      have hyfi' : (y : G) ∈ f (i + 1) := hmono (Nat.le_succ i) hyfi
      have hz := (hnorm i).conj_mem
        (n := (⟨y, hyfi'⟩ : ↥(f (i + 1))))
        (by rw [Subgroup.mem_subgroupOf]; exact hyfi)
        (g := (⟨x, hxfi⟩ : ↥(f (i + 1))))
      rw [Subgroup.mem_subgroupOf] at hz
      exact hz
    · exact X.mul_mem (X.mul_mem hxval.2 hyval.2) (X.inv_mem hxval.2)
  refine (Subgroup.IsSubnormal.isSubnormal_iff (G := X) (H := S.subgroupOf X)).2 ?_
  exact ⟨n, g, hgmono, hgnorm, hg0, hgn⟩

/-! ## `p`-part infrastructure (normalizer of `Z(O_p(F(A)))`) -/

/-- The image of a characteristic subgroup of a subgroup normal in `A` is
normal in `A`. -/
private theorem characteristic_subgroupOf_map_normal_in
    {G : Type u} [Group G] {A F : Subgroup G} {K : Subgroup (↥F)}
    (hK : K.Characteristic) (hF : IsNormalIn F A) :
    IsNormalIn (K.map F.subtype) A := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, _hy, rfl⟩
    exact hF.1 y.2
  · intro a ha z hz
    rcases (Subgroup.mem_map).1 hz with ⟨y, hy, rfl⟩
    let α : ↥F ≃* ↥F :=
      { toFun := fun y => ⟨a * (y : G) * a⁻¹, hF.2 a ha (y : G) y.2⟩
        invFun := fun y =>
          ⟨a⁻¹ * (y : G) * a, by
            have h := hF.2 a⁻¹ (A.inv_mem ha) (y : G) y.2
            simpa [mul_assoc] using h⟩
        left_inv := by intro y; ext; group
        right_inv := by intro y; ext; group
        map_mul' := by
          intro x y
          ext
          change a * ((x * y : ↥F) : G) * a⁻¹ =
            (a * (x : G) * a⁻¹) * (a * (y : G) * a⁻¹)
          rw [Subgroup.coe_mul]
          group }
    have hmap : K.map α.toMonoidHom = K :=
      (Subgroup.characteristic_iff_map_eq.mp hK) α
    have hαy : α y ∈ K := by
      rw [← hmap]
      exact (Subgroup.mem_map).mpr ⟨y, hy, rfl⟩
    refine (Subgroup.mem_map).mpr ⟨α y, hαy, ?_⟩
    change (α y).1 = a * (y : G) * a⁻¹
    rfl

/-- The normalizer of `Z(O_p(F(A)))` is the maximal subgroup `A` (when
`p ∈ π(F(A))`). -/
private theorem normalizer_center_qCoreOf_fitting_eq_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.normalizer
      ((Subgroup.center (↥(qCoreOf (fittingSubgroupOf A) p))).map
        (qCoreOf (fittingSubgroupOf A) p).subtype : Set G) = A := by
  classical
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hFleA : F ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hPleF : P ≤ F := qCoreOf_le F p
  have hPleA : P ≤ A := hPleF.trans hFleA
  have hZleP : Z ≤ P := by
    simpa [Z] using
      (Subgroup.map_subtype_le (H := P) (Subgroup.center (↥P)))
  have hZleA : Z ≤ A := hZleP.trans hPleA
  have hPnormalA : IsNormalIn P A := by
    simpa [P, qCoreOf] using
      (characteristic_subgroupOf_map_normal_in (F := fittingSubgroupOf A)
        (K := pCore p (↥(fittingSubgroupOf A)))
        (pCore_characteristic (p := p)) (fittingSubgroupOf_isNormalIn A))
  have hZnormalA : IsNormalIn Z A := by
    simpa [Z] using
      (characteristic_subgroupOf_map_normal_in (F := P)
        (K := Subgroup.center (↥P)) (center_characteristic (H := P)) hPnormalA)
  have hAleN : A ≤ Subgroup.normalizer (Z : Set G) :=
    le_normalizer_of_isNormalIn hZnormalA
  have hPne : P ≠ ⊥ := by
    simpa [P, F] using
      (fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder A p hp hpF)
  have hPnt : Nontrivial (↥P) := (Subgroup.nontrivial_iff_ne_bot P).2 hPne
  have : Fact p.Prime := ⟨hp⟩
  have hCne : (Subgroup.center (↥P)) ≠ ⊥ := by
    intro hbot
    have hnt : Nontrivial (Subgroup.center (↥P)) :=
      IsPGroup.center_nontrivial (qCoreOf_isPGroup F p)
    exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center (↥P))).1 hnt hbot
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hcbot :=
      (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center (↥P))
        (f := P.subtype) P.subtype_injective).1 hZbot
    exact hCne hcbot
  have hNne_top : Subgroup.normalizer (Z : Set G) ≠ ⊤ := by
    intro htop
    have hZnormalG : Z.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hZnormalG; hsimple.eq_bot_or_eq_top_of_normal Z) with hbot | htopZ
    · exact hZne hbot
    · have hAtop : A = ⊤ := by
        have htopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          exact hZleA (htopZ ▸ hx)
        exact le_antisymm le_top htopLeA
      exact hA.1 hAtop
  have hNleA : Subgroup.normalizer (Z : Set G) ≤ A := by
    by_cases hEq : A = Subgroup.normalizer (Z : Set G)
    · rw [hEq]
    · have hlt : A < Subgroup.normalizer (Z : Set G) :=
        lt_of_le_of_ne hAleN (by
          intro h
          exact hEq h)
      have htop := hA.2 (Subgroup.normalizer (Z : Set G)) hlt
      exact False.elim (hNne_top htop)
  exact le_antisymm hNleA hAleN

/-- For the 1.7 hypotheses with `p ∈ π(F(A))`, the centralizer of
`O_p(S)` lies in the maximal subgroup `A`. -/
private theorem centralizer_qCoreOf_S_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A S : Subgroup G) (hA : IsCoatom A)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A := by
  let F : Subgroup G := fittingSubgroupOf A
  let P : Subgroup G := qCoreOf F p
  let Z : Subgroup G := (Subgroup.center (↥P)).map P.subtype
  have hZleQ : Z ≤ qCoreOf S p := by
    simpa [Z, P] using
      (fstar_center_qCoreOf_fitting_le_qCoreOf_S A S hSF hSsub hCS p hp hpF)
  have hNZ : Subgroup.normalizer (Z : Set G) = A := by
    simpa [Z, P] using
      (normalizer_center_qCoreOf_fitting_eq_A hsimple A hA hp hpF)
  calc
    Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G)
        ≤ Subgroup.centralizer (Z : Set G) :=
      Subgroup.centralizer_le (show (Z : Set G) ⊆ (qCoreOf S p : Set G) from hZleQ)
    _ ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer (Z : Set G)
    _ = A := hNZ

/-- A normal `p`-subgroup of `A` lies in `O_p(A)`. -/
private theorem le_qCoreOf_of_isNormalIn_pGroup
    {G : Type u} [Group G] [Finite G]
    (A Q : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hQA : Q ≤ A) (hQ : IsNormalIn Q A) (hQp : IsPGroup p Q) :
    Q ≤ qCoreOf A p := by
  let : Fact p.Prime := ⟨hp⟩
  have hQsub : Q.subgroupOf A ≤ pCore p (↥A) :=
    le_sSup ⟨by
      exact Subgroup.normal_subgroupOf_of_le_normalizer (H := A) (N := Q)
        (le_normalizer_of_isNormalIn hQ), by
      exact hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQA).symm⟩
  have hmap := Subgroup.map_mono (f := A.subtype) hQsub
  have hQmap : (Q.subgroupOf A).map A.subtype = Q :=
    Subgroup.map_subgroupOf_eq_of_le hQA
  simpa [qCoreOf, hQmap] using hmap

/-- `O_p(F*(A)) ≤ O_p(A)`. -/
private theorem qCoreOf_generalizedFitting_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) (hp : p.Prime) :
    qCoreOf (generalizedFittingSubgroupOf A) p ≤ qCoreOf A p := by
  let S : Subgroup G := generalizedFittingSubgroupOf A
  let Q : Subgroup G := qCoreOf S p
  have hQnormalA : IsNormalIn Q A := by
    simpa [Q, qCoreOf] using
      (characteristic_subgroupOf_map_normal_in (F := S)
        (K := pCore p (↥S)) (pCore_characteristic (p := p))
        (generalizedFittingSubgroupOf_isNormalIn A))
  have hQp : IsPGroup p Q := qCoreOf_isPGroup S p
  exact le_qCoreOf_of_isNormalIn_pGroup A Q p hp hQnormalA.1 hQnormalA hQp

/-- For `p ∈ π(F(A))`, the centralizer of `O_p(A)` lies in the maximal
subgroup `A`. -/
private theorem centralizer_qCoreOf_A_le_A
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {p : ℕ} (hp : p.Prime)
    (hpF : p ∈ primesOfOrder (fittingSubgroupOf A)) :
    Subgroup.centralizer ((qCoreOf A p : Subgroup G) : Set G) ≤ A := by
  let S : Subgroup G := generalizedFittingSubgroupOf A
  have hSF : S ≤ S := le_rfl
  have hSsub : (S.subgroupOf S).IsSubnormal := by
    simpa [Subgroup.subgroupOf_self] using
      (Subgroup.IsSubnormal.top : (⊤ : Subgroup (↥S)).IsSubnormal)
  have hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S :=
    inf_le_left
  have hcentS : Subgroup.centralizer ((qCoreOf S p : Subgroup G) : Set G) ≤ A :=
    centralizer_qCoreOf_S_le_A hsimple A S hA hSF hSsub hCS hp hpF
  exact (Subgroup.centralizer_le
    (show (qCoreOf S p : Set G) ⊆ (qCoreOf A p : Set G) from
      qCoreOf_generalizedFitting_le_qCoreOf A p hp)).trans hcentS

/-- Every element of a subgroup whose prime divisors avoid `p` has order
coprime to `p`. -/
private theorem order_coprime_of_primeDivisors_avoid
    {G : Type u} [Group G] [Finite G]
    (R : Subgroup G) (p : ℕ) (hp : p.Prime)
    (havoid : ∀ q : ℕ, q ∈ (Nat.card (↥R)).primeFactors → q ≠ p)
    {x : G} (hx : x ∈ R) :
    Nat.Coprime p (orderOf x) := by
  classical
  have hord_dvd : orderOf x ∣ Nat.card (↥R) := by
    let r : ↥R := ⟨x, hx⟩
    have : Fintype (↥R) := Fintype.ofFinite _
    have hord : orderOf r = orderOf x := by
      exact (orderOf_injective R.subtype R.subtype_injective r).symm
    have hdvd : orderOf r ∣ Fintype.card (↥R) := orderOf_dvd_card (G := ↥R) (x := r)
    simpa [hord, Nat.card_eq_fintype_card] using hdvd
  exact Nat.coprime_of_dvd (fun k hk hkp hkord => by
    have hkcard : k ∣ Nat.card (↥R) := hkord.trans hord_dvd
    have hkpf : k ∈ (Nat.card (↥R)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hk, hkcard, Nat.card_pos.ne'⟩
    have hkp_eq : k = p := (Nat.prime_dvd_prime_iff_eq hk hp).mp hkp
    exact (havoid k hkpf) hkp_eq)

/-- `O_π(H) ≤ O^p(H)` whenever every prime in `π` differs from `p`. -/
private theorem piCoreOf_le_pResidualOf
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (π : Set ℕ) (p : ℕ) (hp : p.Prime)
    (hπ : ∀ q : ℕ, q ∈ π → q ≠ p) :
    piCoreOf H π ≤ pResidualOf H p := by
  intro x hx
  have hxH : x ∈ H := piCoreOf_le H π hx
  have havoid : ∀ q : ℕ,
      q ∈ (Nat.card (↥(piCoreOf H π))).primeFactors → q ≠ p := by
    intro q hq
    exact hπ q (piCoreOf_primeDivisors H π q hq)
  exact fstar_mem_pResidualOf_of_order_coprime H p hp hxH
    (order_coprime_of_primeDivisors_avoid (piCoreOf H π) p hp havoid hx)

/-- `O_π(G)` is normal. -/
private theorem piCore_normal
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) :
    (piCore π G).Normal := by
  refine ⟨?_⟩
  intro n hn g
  change n ∈ sSup (normalPiSubgroups (G := G) π) at hn
  rw [sSup_eq_iSup', Subgroup.iSup_eq_closure] at hn
  have hgen : ∀ y : G,
      y ∈ ⋃ N : {N : Subgroup G // N ∈ normalPiSubgroups (G := G) π},
        (N.1 : Set G) → g * y * g⁻¹ ∈ piCore π G := by
    intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨N, hN⟩
    have hNnorm : (N : Subgroup G).Normal := N.2.1
    have hy' : g * y * g⁻¹ ∈ (N : Subgroup G) := hNnorm.conj_mem y hN g
    exact Subgroup.mem_sSup_of_mem N.2 hy'
  refine Subgroup.closure_induction'' hgen ?_ ?_ ?_ hn
  · intro y hy
    simpa [mul_assoc] using (piCore π G).inv_mem (hgen y hy)
  · simpa using (piCore π G).one_mem
  · intro a b _ _ ha hb
    simpa [mul_assoc, mul_left_comm, mul_right_comm] using
      (piCore π G).mul_mem ha hb

/-- `O_π(H)` is normal in `H`. -/
private theorem piCoreOf_isNormalIn
    {G : Type u} [Group G] [Finite G] (H : Subgroup G) (π : Set ℕ) :
    IsNormalIn (piCoreOf H π) H := by
  refine ⟨piCoreOf_le H π, ?_⟩
  intro h hh x hx
  rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
  have hy' : (⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹ ∈ piCore π (↥H) :=
    (piCore_normal (G := ↥H) π).conj_mem y hy (⟨h, hh⟩ : ↥H)
  refine Subgroup.mem_map.mpr
    ⟨(⟨h, hh⟩ : ↥H) * y * (⟨h, hh⟩ : ↥H)⁻¹, hy', ?_⟩
  rfl

/-- A component of a normal subgroup of `A` is a component of `A`. -/
private theorem componentLayerOf_eq_bot_of_normal_subgroup
    {G : Type u} [Group G] [Finite G]
    {A R : Subgroup G} (hRA : R ≤ A) (hR : IsNormalIn R A)
    (hEAbot : componentLayerOf A = ⊥) :
    componentLayerOf R = ⊥ := by
  apply le_bot_iff.mp
  rw [componentLayerOf]
  refine sSup_le ?_
  intro E hE
  have hER : E ≤ R := hE.1
  have hEA : E ≤ A := hER.trans hRA
  have hEsubA : (E.subgroupOf A).IsSubnormal :=
    isSubnormal_of_isNormalIn_subgroup hRA hR hER hE.2.1
  have hEcompA : IsComponentOf E A := ⟨hEA, hEsubA, hE.2.2⟩
  have hEleLayer : E ≤ componentLayerOf A :=
    le_sSup (s := {E' : Subgroup G | IsComponentOf E' A}) hEcompA
  have hEbot : E ≤ ⊥ := hEleLayer.trans (le_of_eq hEAbot)
  exact False.elim ((Subgroup.nontrivial_iff_ne_bot E).1 hE.2.2.1 (le_bot_iff.mp hEbot))

/-- The Fitting subgroup of a normal subgroup is normal in the supergroup. -/
private theorem fittingSubgroupOf_normal_in_of_normal
    {G : Type u} [Group G]
    {A R : Subgroup G} (hR : IsNormalIn R A) :
    IsNormalIn (fittingSubgroupOf R) A := by
  simpa [fittingSubgroupOf] using
    (characteristic_subgroupOf_map_normal_in (F := R)
      (K := fittingSubgroup (↥R)) fittingSubgroup_characteristic hR)

/-- The Fitting subgroup of a normal subgroup lies in the Fitting subgroup
of the supergroup. -/
private theorem fittingSubgroupOf_le_fittingSubgroupOf_of_normal
    {G : Type u} [Group G] [Finite G]
    {A R : Subgroup G} (hRA : R ≤ A) (hR : IsNormalIn R A) :
    fittingSubgroupOf R ≤ fittingSubgroupOf A := by
  have hFRR : fittingSubgroupOf R ≤ R := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  exact le_fittingSubgroupOf_of_isNormalIn_nilpotent
    (hFRR.trans hRA) (fittingSubgroupOf_normal_in_of_normal hR)
    (fittingSubgroupOf_isNilpotent R)

/-- A normal subgroup of order coprime to `p` lies in the ambient image of
`O_p'(H)`. -/
private theorem le_pPrimeCore_map_of_normal_of_coprime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hKH : K ≤ H) (hKnorm : (K.subgroupOf H).Normal)
    (hcop : Nat.Coprime p (Nat.card K)) :
    K ≤ (pPrimeCore p (↥H)).map H.subtype := by
  have hcard : Nat.card (K.subgroupOf H) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
  have hcop' : Nat.Coprime p (Nat.card (K.subgroupOf H)) := by
    rwa [hcard]
  have hsub : K.subgroupOf H ≤ pPrimeCore p (↥H) := le_sSup ⟨hKnorm, hcop'⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hsub
  have hmapK : (K.subgroupOf H).map H.subtype = K :=
    Subgroup.map_subgroupOf_eq_of_le hKH
  simpa [hmapK] using hmap

/-- A normal `p`-subgroup and a normal subgroup of order coprime to `p`
of the same subgroup commute. -/
private theorem commutator_eq_bot_of_normal_pgroup_pPrime
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) (p : ℕ) (hp : p.Prime)
    (P K : Subgroup G)
    (hPL : P ≤ L) (hPnorm : IsNormalIn P L) (hPp : IsPGroup p P)
    (hKL : K ≤ L) (hKnorm : IsNormalIn K L)
    (hKcop : Nat.Coprime p (Nat.card K)) :
    ⁅P, K⁆ = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hPle : P ≤ qCoreOf L p :=
    le_qCoreOf_of_isNormalIn_pGroup L P p hp hPL hPnorm hPp
  have hKle : K ≤ (pPrimeCore p (↥L)).map L.subtype :=
    le_pPrimeCore_map_of_normal_of_coprime (H := L) (K := K) hKL
      (Subgroup.normal_subgroupOf_of_le_normalizer (H := L) (N := K)
        (le_normalizer_of_isNormalIn hKnorm)) hKcop
  have hcentK : K ≤ Subgroup.centralizer ((qCoreOf L p : Subgroup G) : Set G) :=
    hKle.trans (pPrimeCore_map_le_centralizer_pCore_map (p := p) L)
  have hPcentK : P ≤ Subgroup.centralizer (K : Set G) := by
    intro x hx y hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp (hcentK hy)) x (hPle hx)
    exact hcomm.symm
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := P) (H₂ := K)).mpr hPcentK

/-- If the prime divisors of `|R|` avoid `p`, then the order of every
subgroup of `R` is coprime to `p`. -/
private theorem coprime_card_of_subset_primeDivisors
    {G : Type u} [Group G] [Finite G]
    {K R : Subgroup G} (hKR : K ≤ R) (p : ℕ) (hp : p.Prime)
    (havoid : ∀ q : ℕ, q ∈ (Nat.card (↥R)).primeFactors → q ≠ p) :
    Nat.Coprime p (Nat.card (↥K)) := by
  exact Nat.coprime_of_dvd (fun k hk hkp hkd => by
    have hkR : k ∣ Nat.card (↥R) := hkd.trans (Subgroup.card_dvd_of_le hKR)
    have hkpf : k ∈ (Nat.card (↥R)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hk, hkR, Nat.card_pos.ne'⟩
    exact (havoid k hkpf) ((Nat.prime_dvd_prime_iff_eq hk hp).mp hkp))

/-- `O_p(B)` centralizes `F(O_π(A))` whenever the primes of `π` avoid
`p`. -/
private theorem qCoreOf_B_p_commute_fitting_piCore
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hp : p.Prime) (π : Set ℕ)
    (hπ : ∀ q : ℕ, q ∈ π → q ≠ p)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A) :
    ⁅qCoreOf B p, fittingSubgroupOf (piCoreOf A π)⁆ = ⊥ := by
  let L : Subgroup G := A ⊓ B
  let R : Subgroup G := piCoreOf A π
  let K : Subgroup G := fittingSubgroupOf R
  let Q : Subgroup G := qCoreOf B p
  have hLA : L ≤ A := inf_le_left
  have hLB : L ≤ B := inf_le_right
  have hRA : R ≤ A := piCoreOf_le A π
  have hRnormA : IsNormalIn R A := piCoreOf_isNormalIn A π
  have hQleFB : Q ≤ fittingSubgroupOf B := qCoreOf_le_fittingSubgroupOf B p hp
  have hFBleA : fittingSubgroupOf B ≤ A :=
    (le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans hFBA
  have hFBleB : fittingSubgroupOf B ≤ B :=
    (le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans
      (generalizedFittingSubgroupOf_le B)
  have hQleL : Q ≤ L := le_inf (hQleFB.trans hFBleA) (hQleFB.trans hFBleB)
  have hQnormL : IsNormalIn Q L := by
    refine ⟨hQleL, ?_⟩
    intro l hl q hq
    exact (qCoreOf_normal_in B p).2 l (hLB hl) q hq
  have hKleFA : K ≤ fittingSubgroupOf A :=
    fittingSubgroupOf_le_fittingSubgroupOf_of_normal hRA hRnormA
  have hFAleA : fittingSubgroupOf A ≤ A := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hFAleB : fittingSubgroupOf A ≤ B :=
    (le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFAB
  have hKleL : K ≤ L := le_inf (hKleFA.trans hFAleA) (hKleFA.trans hFAleB)
  have hKnormA : IsNormalIn K A := fittingSubgroupOf_normal_in_of_normal hRnormA
  have hKnormL : IsNormalIn K L := by
    refine ⟨hKleL, ?_⟩
    intro l hl k hk
    exact hKnormA.2 l (hLA hl) k hk
  have havoid : ∀ q : ℕ,
      q ∈ (Nat.card (↥R)).primeFactors → q ≠ p := by
    intro q hq
    exact hπ q (piCoreOf_primeDivisors A π q hq)
  have hKR : K ≤ R := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hKcop : Nat.Coprime p (Nat.card (↥K)) :=
    coprime_card_of_subset_primeDivisors hKR p hp havoid
  exact commutator_eq_bot_of_normal_pgroup_pPrime L p hp Q K
    hQleL hQnormL (qCoreOf_isPGroup B p) hKleL hKnormL hKcop

/-! ## Final p-part infrastructure (Thompson/normalizer chain) -/

/-- The pointwise product of a normal subgroup with any subgroup is their
join. -/
private theorem mul_eq_sup_of_normal_local
    {G : Type u} [Group G] (A B : Subgroup G)
    (hA : A.Normal) : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  apply le_antisymm
  · intro x hx
    change x ∈ A ⊔ B at hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyA | hyB
      · exact Set.mem_mul.mpr ⟨y, hyA, 1, B.one_mem, mul_one y⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, y, hyB, one_mul y⟩
    · intro x hx
      rcases hx with hxA | hxB
      · exact Set.mem_mul.mpr ⟨x⁻¹, A.inv_mem hxA, 1, B.one_mem, mul_one x⁻¹⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, x⁻¹, B.inv_mem hxB, one_mul x⁻¹⟩
    · exact Set.mem_mul.mpr ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
    · intro a b hx hy ha hb
      rcases (Set.mem_mul).1 ha with ⟨a₁, ha₁, b₁, hb₁, rfl⟩
      rcases (Set.mem_mul).1 hb with ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine Set.mem_mul.mpr ⟨a₁ * (b₁ * a₂ * b₁⁻¹), ?_, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      · exact A.mul_mem ha₁ (hA.conj_mem a₂ ha₂ b₁)
      · group
  · intro x hx
    rcases (Set.mem_mul).1 hx with ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

/-- The join of a normal subgroup with a subgroup has cardinality dividing
the product of the cardinalities. -/
private theorem card_sup_dvd_card_mul_local
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (hA : A.Normal) :
    Nat.card (↥(A ⊔ B)) ∣ Nat.card (↥A) * Nat.card (↥B) := by
  have hset : ((A ⊔ B : Subgroup G) : Set G) = (B : Set G) * (A : Set G) := by
    have h1 : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
      mul_eq_sup_of_normal_local A B hA
    have h2 : (A : Set G) * (B : Set G) = (B : Set G) * (A : Set G) := by
      apply le_antisymm
      · intro x hx
        rcases (Set.mem_mul).1 hx with ⟨a, ha, b, hb, rfl⟩
        refine Set.mem_mul.mpr ⟨b, hb, b⁻¹ * a * b, by simpa using hA.conj_mem a ha b⁻¹, ?_⟩
        group
      · intro x hx
        rcases (Set.mem_mul).1 hx with ⟨b, hb, a, ha, rfl⟩
        refine Set.mem_mul.mpr ⟨b * a * b⁻¹, hA.conj_mem a ha b, b, hb, ?_⟩
        group
    exact h1.trans h2
  have h1 : Nat.card ((B : Set G) * (A : Set G)) =
      Nat.card ↥A * Nat.card ((B : Set G).image (QuotientGroup.mk' A)) :=
    Subgroup.card_mul_eq_card_subgroup_mul_card_quotient (s := A) (t := (B : Set G))
  have h2 : Nat.card ((B : Set G).image (QuotientGroup.mk' A)) =
      Nat.card (B.map (QuotientGroup.mk' A)) := by
    rfl
  have h3 : Nat.card (B.map (QuotientGroup.mk' A)) ∣ Nat.card ↥B :=
    Subgroup.card_map_dvd (f := QuotientGroup.mk' A) (H := B)
  calc
    Nat.card (↥(A ⊔ B)) = Nat.card (((A ⊔ B : Subgroup G) : Set G)) := rfl
    _ = Nat.card ((B : Set G) * (A : Set G)) := by rw [hset]
    _ = Nat.card ↥A * Nat.card ((B : Set G).image (QuotientGroup.mk' A)) := h1
    _ = Nat.card ↥A * Nat.card (B.map (QuotientGroup.mk' A)) := by rw [h2]
    _ ∣ Nat.card ↥A * Nat.card ↥B := Nat.mul_dvd_mul_left (Nat.card ↥A) h3

/-- The normal `π`-subgroups are directed by inclusion. -/
private theorem directedOn_normalPiSubgroups_local
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) :
    DirectedOn (· ≤ ·) (normalPiSubgroups (G := G) π) := by
  intro A hA B hB
  have hA_normal : A.Normal := hA.1
  have hB_normal : B.Normal := hB.1
  refine ⟨A ⊔ B, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
  · exact Subgroup.sup_normal A B
  · intro q hq
    have hqpf : q ∈ (Nat.card (↥(A ⊔ B))).primeFactors := hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hqpf
    have hdvd : q ∣ Nat.card (↥A) * Nat.card (↥B) :=
      (Nat.dvd_of_mem_primeFactors hqpf).trans (card_sup_dvd_card_mul_local A B hA.1)
    rcases (Nat.Prime.dvd_mul hqprime).mp hdvd with hqA | hqB
    · exact hA.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hqA, Nat.card_pos.ne'⟩)
    · exact hB.2 q (Nat.mem_primeFactors.mpr ⟨hqprime, hqB, Nat.card_pos.ne'⟩)

/-- The empty set of normal `π`-subgroups is inhabited by the trivial group. -/
private theorem normalPiSubgroups_nonempty_local
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) :
    (normalPiSubgroups (G := G) π).Nonempty := by
  refine ⟨⊥, ?_, ?_⟩
  · infer_instance
  · intro q hq
    simp at hq

/-- `O_π(G)` is characteristic. -/
private theorem piCore_characteristic_local
    {G : Type u} [Group G] [Finite G] (π : Set ℕ) :
    (piCore π G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  let φ : G →* G := e.toMonoidHom
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hdir := directedOn_normalPiSubgroups_local (G := G) π
    rcases ((Subgroup.mem_sSup_of_directedOn (normalPiSubgroups_nonempty_local (G := G) π)
      hdir).mp hy) with ⟨K, hK, hyK⟩
    have hKmap : K.map φ ∈ normalPiSubgroups (G := G) π := by
      refine ⟨(Subgroup.Normal.map hK.1 φ e.surjective), ?_⟩
      intro q hq
      have hq' : q ∈ (Nat.card (↥K)).primeFactors := by
        have hcard : Nat.card (↥(K.map φ)) = Nat.card (↥K) := by
          exact (Nat.card_congr (Subgroup.equivMapOfInjective K φ e.injective).toEquiv).symm
        rwa [hcard] at hq
      exact hK.2 q hq'
    have hmem : φ y ∈ K.map φ := Subgroup.mem_map.mpr ⟨y, hyK, rfl⟩
    exact Subgroup.mem_sSup_of_mem hKmap hmem
  · intro x hx
    rw [Subgroup.mem_map]
    refine ⟨e.symm x, ?_, by simp⟩
    have hdir := directedOn_normalPiSubgroups_local (G := G) π
    rcases ((Subgroup.mem_sSup_of_directedOn (normalPiSubgroups_nonempty_local (G := G) π)
      hdir).mp hx) with ⟨K, hK, hxK⟩
    let ψ : G →* G := e.symm.toMonoidHom
    have hKmap : K.map ψ ∈ normalPiSubgroups (G := G) π := by
      refine ⟨(Subgroup.Normal.map hK.1 ψ e.symm.surjective), ?_⟩
      intro q hq
      have hq' : q ∈ (Nat.card (↥K)).primeFactors := by
        have hcard : Nat.card (↥(K.map ψ)) = Nat.card (↥K) := by
          exact (Nat.card_congr (Subgroup.equivMapOfInjective K ψ e.symm.injective).toEquiv).symm
        rwa [hcard] at hq
      exact hK.2 q hq'
    have hmem : ψ x ∈ K.map ψ :=
      Subgroup.mem_map.mpr ⟨x, hxK, rfl⟩
    exact Subgroup.mem_sSup_of_mem hKmap hmem

/-- The centralizer in `B` of a subgroup normal in `B` is normal in `B`. -/
private theorem isNormalIn_centralizer_of_isNormalIn
    {G : Type u} [Group G]
    {B N : Subgroup G} (hN : IsNormalIn N B) :
    IsNormalIn (Subgroup.centralizer (N : Set G) ⊓ B) B := by
  refine ⟨inf_le_right, ?_⟩
  intro b hb c hc
  have hcC : c ∈ Subgroup.centralizer (N : Set G) := hc.1
  have hcB : c ∈ B := hc.2
  have hbC : b * c * b⁻¹ ∈ B := B.mul_mem (B.mul_mem hb hcB) (B.inv_mem hb)
  have hbC' : b * c * b⁻¹ ∈ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hbn : b⁻¹ * n * b ∈ N := by
      simpa using hN.2 b⁻¹ (B.inv_mem hb) n hn
    have hcomm : c * (b⁻¹ * n * b) = (b⁻¹ * n * b) * c :=
      ((Subgroup.mem_centralizer_iff.mp hcC) (b⁻¹ * n * b) hbn).symm
    calc
      n * (b * c * b⁻¹) = b * ((b⁻¹ * n * b) * c) * b⁻¹ := by group
      _ = b * (c * (b⁻¹ * n * b)) * b⁻¹ := by rw [hcomm]
      _ = (b * c * b⁻¹) * n := by group
  exact ⟨hbC', hbC⟩

/-- A commutator of an element centralizing `N` with an element of `B`
centralizes `N`, when `N` is normal in `B`. -/
private theorem commutatorElement_mem_centralizer_of_mem_centralizer_normal
    {G : Type u} [Group G]
    {B N : Subgroup G} (hN : IsNormalIn N B)
    {x h : G} (hxB : x ∈ B) (hhB : h ∈ B)
    (hxN : x ∈ Subgroup.centralizer (N : Set G)) :
    ⁅x, h⁆ ∈ Subgroup.centralizer (N : Set G) := by
  let X : Subgroup G := Subgroup.zpowers x
  let H : Subgroup G := Subgroup.zpowers h
  have hXleC : X ≤ Subgroup.centralizer (N : Set G) :=
    Subgroup.zpowers_le.mpr hxN
  have hXc : ⁅N, X⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer
      (H₁ := X) (H₂ := N)).2 hXleC
  have hHleN : H ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.mpr (le_normalizer_of_isNormalIn hN hhB)
  have hHn : ⁅H, N⁆ ≤ N := by
    have hNn : ⁅N, H⁆ ≤ N :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := H) (K := N)).1 hHleN
    rwa [Subgroup.commutator_comm] at hNn
  have h1 : ⁅⁅H, N⁆, X⁆ = ⊥ := by
    apply le_antisymm
    · calc
        ⁅⁅H, N⁆, X⁆ ≤ ⁅N, X⁆ := Subgroup.commutator_mono hHn le_rfl
        _ = ⊥ := hXc
    · exact bot_le
  have h2 : ⁅⁅N, X⁆, H⁆ = ⊥ := by
    rw [hXc]
    simp
  have hRot : ⁅⁅X, H⁆, N⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate
      (H₁ := X) (H₂ := H) (H₃ := N)
      (by simpa [Subgroup.commutator_comm] using h1)
      (by simpa [Subgroup.commutator_comm] using h2)
  have hmem : ⁅x, h⁆ ∈ ⁅X, H⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers x) (Subgroup.mem_zpowers h)
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer
    (H₁ := ⁅X, H⁆) (H₂ := N)).1 hRot hmem

/-- If one side of a commutator centralizes a subgroup whose centralizer is
normal in the containing group, the whole commutator centralizes it. -/
private theorem commutator_le_centralizer_of_le_centralizer_normal
    {G : Type u} [Group G]
    {B N X H : Subgroup G}
    (hXB : X ≤ B) (hHB : H ≤ B)
    (hNnorm : IsNormalIn N B)
    (hXc : X ≤ Subgroup.centralizer (N : Set G)) :
    ⁅X, H⁆ ≤ Subgroup.centralizer (N : Set G) ⊓ B := by
  have hC : ⁅X, H⁆ ≤ Subgroup.centralizer (N : Set G) := by
    rw [Subgroup.commutator_le]
    intro x hx h hh
    exact commutatorElement_mem_centralizer_of_mem_centralizer_normal
      hNnorm (hXB hx) (hHB hh) (hXc hx)
  intro x hx
  exact ⟨hC hx, (Subgroup.commutator_le_sup X H).trans (sup_le hXB hHB) hx⟩

/-- A subgroup centralizing two subgroups centralizes their join. -/
private theorem le_centralizer_of_centralizes_join
    {G : Type u} [Group G]
    {C F E : Subgroup G}
    (hCF : C ≤ Subgroup.centralizer (F : Set G))
    (hCE : C ≤ Subgroup.centralizer (E : Set G)) :
    C ≤ Subgroup.centralizer ((F ⊔ E : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyF | hyE
    · exact (Subgroup.mem_centralizer_iff.mp (hCF hc)) y hyF
    · exact (Subgroup.mem_centralizer_iff.mp (hCE hc)) y hyE
  · intro y hy
    rcases hy with hyF | hyE
    · have h := (Subgroup.mem_centralizer_iff.mp (hCF hc)) y hyF
      exact by
        have h' : c = y⁻¹ * c * y := by
          calc
            c = y⁻¹ * (y * c) * y⁻¹ * y := by group
            _ = y⁻¹ * (c * y) * y⁻¹ * y := by rw [h]
            _ = y⁻¹ * c * y := by group
        calc
          y⁻¹ * c = (y⁻¹ * c * y) * y⁻¹ := by group
          _ = c * y⁻¹ := by rw [← h']
    · have h := (Subgroup.mem_centralizer_iff.mp (hCE hc)) y hyE
      exact by
        have h' : c = y⁻¹ * c * y := by
          calc
            c = y⁻¹ * (y * c) * y⁻¹ * y := by group
            _ = y⁻¹ * (c * y) * y⁻¹ * y := by rw [h]
            _ = y⁻¹ * c * y := by group
        calc
          y⁻¹ * c = (y⁻¹ * c * y) * y⁻¹ := by group
          _ = c * y⁻¹ := by rw [← h']
  · simp
  · intro y z _ _ hy hz
    calc
      (y * z) * c = y * (z * c) := by group
      _ = y * (c * z) := by rw [hz]
      _ = (y * c) * z := by group
      _ = (c * y) * z := by rw [hy]
      _ = c * (y * z) := by group

/-- The image of a Sylow subgroup of a normal nilpotent subgroup lies in the
corresponding `p`-core. -/
private theorem map_sylow_normal_nilpotent_le_pCore
    {G : Type u} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hnil : Group.IsNilpotent N) (p : ℕ) [Fact p.Prime]
    (S : Sylow p N) :
    S.map N.subtype ≤ pCore p G := by
  have hSchar : (S : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal S (Group.IsNilpotent.sylow_normal hnil p S)
  have hNtop : IsNormalIn N (⊤ : Subgroup G) := by
    refine ⟨fun x hx => trivial, ?_⟩
    intro g _hg x hx
    exact (inferInstance : N.Normal).conj_mem x hx g
  have hSmapN : IsNormalIn (S.map N.subtype) (⊤ : Subgroup G) :=
    characteristic_subgroupOf_map_normal_in (F := N) (K := S) hSchar hNtop
  have hSmapP : IsPGroup p (S.map N.subtype) :=
    S.isPGroup'.map N.subtype
  have hmem : S.map N.subtype ∈
      {K : Subgroup G | K.Normal ∧ IsPGroup p K} :=
    ⟨(Subgroup.normalizer_eq_top_iff).mp (by
      have hle : (⊤ : Subgroup G) ≤ Subgroup.normalizer (S.map N.subtype : Set G) :=
        le_normalizer_of_isNormalIn hSmapN
      simpa using hle), hSmapP⟩
  exact le_sSup hmem

/-- A `p`-subgroup of the Fitting subgroup of `B` lies in `O_p(B)`. -/
private theorem le_qCoreOf_of_isPGroup_of_le_fitting
    {G : Type u} [Group G] [Finite G]
    (B P : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hPB : P ≤ B) (hPF : P ≤ fittingSubgroupOf B)
    (hPp : IsPGroup p P) :
    P ≤ qCoreOf B p := by
  let : Fact p.Prime := ⟨hp⟩
  let F : Subgroup (↥B) := (fittingSubgroupOf B).subgroupOf B
  have hFleB : fittingSubgroupOf B ≤ B := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hFnormB : IsNormalIn (fittingSubgroupOf B) B := fittingSubgroupOf_isNormalIn B
  have : F.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFleB]
    exact le_normalizer_of_isNormalIn hFnormB
  have hFnil : Group.IsNilpotent F := by
    have hFnil' : Group.IsNilpotent (↥(fittingSubgroupOf B)) :=
      fittingSubgroupOf_isNilpotent B
    have : Group.IsNilpotent (↥(fittingSubgroupOf B)) := hFnil'
    exact Group.nilpotent_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hFleB).symm
  let P' : Subgroup (↥B) := P.subgroupOf B
  have hP'F : P' ≤ F := Subgroup.subgroupOf_mono B hPF
  have hP'p : IsPGroup p (↥P') :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPB).symm
  let P'' : Subgroup (↥F) := P'.subgroupOf F
  have hP''p : IsPGroup p (↥P'') :=
    hP'p.of_equiv (Subgroup.subgroupOfEquivOfLe hP'F).symm
  rcases IsPGroup.exists_le_sylow hP''p with ⟨S, hP''S⟩
  have hSp : S.map F.subtype ≤ pCore p (↥B) :=
    map_sylow_normal_nilpotent_le_pCore (G := ↥B) F hFnil p S
  have hPleSp : P' ≤ S.map F.subtype := by
    intro x hx
    have hxF : x ∈ F := by
      exact Subgroup.subgroupOf_mono B hPF (Subgroup.mem_subgroupOf.mp hx)
    let y : ↥F := ⟨x, hxF⟩
    have hxP'' : y ∈ P'' := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxS : y ∈ (S : Subgroup (↥F)) := hP''S hxP''
    exact Subgroup.mem_map.mpr ⟨y, hxS, rfl⟩
  have hPmap : (S.map F.subtype).map B.subtype ≤ qCoreOf B p := by
    exact Subgroup.map_mono (f := B.subtype) hSp
  have hPle : P ≤ (S.map F.subtype).map B.subtype := by
    intro x hx
    have hxP' : (⟨x, hPB hx⟩ : ↥B) ∈ P' := by
      rw [Subgroup.mem_subgroupOf]
      exact hx
    have hxS : (⟨x, hPB hx⟩ : ↥B) ∈ S.map F.subtype := hPleSp hxP'
    exact Subgroup.mem_map.mpr ⟨⟨x, hPB hx⟩, hxS, rfl⟩
  exact hPle.trans hPmap

/-- A subgroup normalizing two subgroups normalizes their join. -/
private theorem le_normalizer_of_normalizes_join
    {G : Type u} [Group G]
    {H A B : Subgroup G}
    (hHA : H ≤ Subgroup.normalizer (A : Set G))
    (hHB : H ≤ Subgroup.normalizer (B : Set G)) :
    H ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have hsup_closure :
        A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    have hxcl : x ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
      simpa [hsup_closure] using hx
    refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
      (p := fun y _hy => n * y * n⁻¹ ∈ (A ⊔ B : Subgroup G)) ?_ ?_ ?_ ?_
      hxcl
    · intro y hy
      rcases hy with hyA | hyB
      · exact (le_sup_left : A ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hHA hn) y).mp hyA)
      · exact (le_sup_right : B ≤ A ⊔ B)
          ((Subgroup.mem_normalizer_iff.mp (hHB hn) y).mp hyB)
    · simp
    · intro y z _hy _hz hyP hzP
      simpa [mul_assoc] using (A ⊔ B).mul_mem hyP hzP
    · intro y _hy hyP
      simpa [mul_assoc] using (A ⊔ B).inv_mem hyP
  · intro hx
    have hninv : n⁻¹ ∈ H := H.inv_mem hn
    have hforward_inv :
        ∀ y : G, y ∈ A ⊔ B → n⁻¹ * y * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G) := by
      intro y hy
      have hsup_closure :
          A ⊔ B = Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
      have hycl : y ∈ Subgroup.closure ((A : Set G) ∪ (B : Set G)) := by
        simpa [hsup_closure] using hy
      refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
        (p := fun z _hz => n⁻¹ * z * (n⁻¹)⁻¹ ∈ (A ⊔ B : Subgroup G))
        ?_ ?_ ?_ ?_ hycl
      · intro z hz
        rcases hz with hzA | hzB
        · exact (le_sup_left : A ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hHA hninv) z).mp hzA)
        · exact (le_sup_right : B ≤ A ⊔ B)
            ((Subgroup.mem_normalizer_iff.mp (hHB hninv) z).mp hzB)
      · simp
      · intro z w _hz _hw hzP hwP
        simpa [mul_assoc] using (A ⊔ B).mul_mem hzP hwP
      · intro z _hz hzP
        simpa [mul_assoc] using (A ⊔ B).inv_mem hzP
    have := hforward_inv (n * x * n⁻¹) hx
    simpa [mul_assoc] using this

/-! ## Final assembly: the two-prime contradiction (KS 10.1.4) -/

/-- The Fitting subgroup of an `r`-group is the whole group. -/
private lemma fittingSubgroupOf_qCoreOf_eq_self
    {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) {r : ℕ} (hr : r.Prime) :
    fittingSubgroupOf (qCoreOf B r) = qCoreOf B r := by
  let : Fact r.Prime := ⟨hr⟩
  have hnil : Group.IsNilpotent (↥(qCoreOf B r)) :=
    IsPGroup.isNilpotent (p := r) (qCoreOf_isPGroup B r)
  have htop : fittingSubgroup (↥(qCoreOf B r)) = ⊤ :=
    fitting_eq_top_of_nilpotent (↥(qCoreOf B r))
  unfold fittingSubgroupOf
  rw [htop]
  ext x
  simp

/-- The Fitting subgroup of the Fitting subgroup is itself. -/
private lemma fittingSubgroupOf_fittingSubgroupOf_eq_self
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    fittingSubgroupOf (fittingSubgroupOf B) = fittingSubgroupOf B := by
  have hnil : Group.IsNilpotent (↥(fittingSubgroupOf B)) :=
    fittingSubgroupOf_isNilpotent B
  have htop : fittingSubgroup (↥(fittingSubgroupOf B)) = ⊤ :=
    fitting_eq_top_of_nilpotent (↥(fittingSubgroupOf B))
  change (fittingSubgroup (↥(fittingSubgroupOf B))).map
      (fittingSubgroupOf B).subtype = fittingSubgroupOf B
  rw [htop]
  ext x
  simp

/-- Under the 1.6 containments, `O_p(A)` centralizes `O_q(B)` for distinct
primes `p ≠ q` (KS 10.1.4: "subgroups of coprime order of `F(A)` and
`F(B)` centralize each other"). -/
private lemma qCoreOf_commute_cross
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A) :
    ⁅qCoreOf A p, qCoreOf B q⁆ = ⊥ := by
  have h1 : ⁅qCoreOf B q, fittingSubgroupOf (piCoreOf A {p})⁆ = ⊥ :=
    qCoreOf_B_p_commute_fitting_piCore A B q hq {p}
      (by intro r hr; rw [Set.mem_singleton_iff] at hr; rw [hr]; exact hne)
      hFAB hFBA
  have h2 : ⁅qCoreOf B q, qCoreOf A p⁆ = ⊥ := by
    rw [← qCoreOf_eq_piCoreOf_singleton A p hp] at h1
    rw [fittingSubgroupOf_qCoreOf_eq_self A hp] at h1
    exact h1
  exact (Subgroup.commutator_comm (H₁ := qCoreOf B q) (H₂ := qCoreOf A p)).symm.trans h2

/-- A subgroup centralizing every member of a family centralizes the
join. -/
private lemma le_centralizer_of_centralizes_iSup
    {G : Type u} [Group G] {ι : Type*} (C : Subgroup G) (X : ι → Subgroup G)
    (h : ∀ i : ι, C ≤ Subgroup.centralizer ((X i : Subgroup G) : Set G)) :
    C ≤ Subgroup.centralizer ((⨆ i : ι, X i : Subgroup G) : Set G) := by
  intro c hc
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rw [Subgroup.iSup_eq_closure] at hx
  refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
    exact (Subgroup.mem_centralizer_iff.mp (h i hc)) y hyi
  · intro y hy
    rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
    exact (Subgroup.mem_centralizer_iff.mp (h i hc)) y⁻¹ ((X i).inv_mem hyi)
  · simp
  · intro y z _ _ hyP hzP
    calc
      (y * z) * c = y * (z * c) := by group
      _ = y * (c * z) := by rw [hzP]
      _ = (y * c) * z := by group
      _ = (c * y) * z := by rw [hyP]
      _ = c * (y * z) := by group

/-- The join of subgroups normal in `B` is normal in `B`. -/
private lemma isNormalIn_iSup
    {G : Type u} [Group G] {ι : Type*} (X : ι → Subgroup G) (B : Subgroup G)
    (h : ∀ i : ι, IsNormalIn (X i) B) :
    IsNormalIn (⨆ i : ι, X i) B := by
  refine ⟨?_, ?_⟩
  · exact iSup_le (fun i => (h i).1)
  · intro b hb x hx
    rw [Subgroup.iSup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
      exact (le_iSup (f := fun i : ι => X i) i) ((h i).2 b hb y hyi)
    · intro y hy
      rcases (Set.mem_iUnion).1 hy with ⟨i, hyi⟩
      exact (le_iSup (f := fun i : ι => X i) i) ((h i).2 b hb y⁻¹ ((X i).inv_mem hyi))
    · simpa using (⨆ i : ι, X i).one_mem
    · intro y z _ _ hyP hzP
      simpa [mul_assoc, mul_left_comm, mul_right_comm] using (⨆ i : ι, X i).mul_mem hyP hzP

/-- If `A` and `B` both normalize `D` and both commute with `C` modulo
`D`, then the join of `A` and `B` commutes with `C` modulo `D`. -/
private lemma commutator_sup_le_of_commutator_le_and_normalize
    {G : Type u} [Group G]
    (A B C D : Subgroup G)
    (hAC : ⁅A, C⁆ ≤ D) (hBC : ⁅B, C⁆ ≤ D)
    (hAD : A ≤ Subgroup.normalizer (D : Set G))
    (hBD : B ≤ Subgroup.normalizer (D : Set G)) :
    ⁅A ⊔ B, C⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro x hx c hc
  rw [Subgroup.sup_eq_closure] at hx
  have hsupN : A ⊔ B ≤ Subgroup.normalizer (D : Set G) := sup_le hAD hBD
  refine Subgroup.closure_induction (k := ((A : Set G) ∪ (B : Set G)))
    (p := fun y _hy => ⁅y, c⁆ ∈ D) ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with hyA | hyB
    · exact hAC (Subgroup.commutator_mem_commutator hyA hc)
    · exact hBC (Subgroup.commutator_mem_commutator hyB hc)
  · simp
  · intro y z _hy _hz hyP hzP
    have hyN : y ∈ Subgroup.normalizer (D : Set G) := hsupN (by
      simpa [Subgroup.sup_eq_closure] using _hy)
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact D.mul_mem (((Subgroup.mem_normalizer_iff.mp hyN) ⁅z, c⁆).1 hzP) hyP
  · intro y _hy hyP
    have hyN : y ∈ Subgroup.normalizer (D : Set G) := hsupN (by
      simpa [Subgroup.sup_eq_closure] using _hy)
    have hyNinv : y⁻¹ ∈ Subgroup.normalizer (D : Set G) :=
      (Subgroup.normalizer (D : Set G)).inv_mem hyN
    have hcyD : ⁅c, y⁆ ∈ D := by
      simpa [commutatorElement_inv] using D.inv_mem hyP
    rw [commutatorElement_inv_left]
    simpa using ((Subgroup.mem_normalizer_iff.mp hyNinv) ⁅c, y⁆).1 hcyD

/-- The commutator of two `subgroupOf`-restricted subgroups is the
restriction of the commutator. -/
private lemma commutator_subgroupOf_eq
    {G : Type u} [Group G] (B X Q : Subgroup G)
    (hXB : X ≤ B) (hQB : Q ≤ B) :
    ⁅X.subgroupOf B, Q.subgroupOf B⁆ = (⁅X, Q⁆).subgroupOf B := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    have hmap : (⁅X.subgroupOf B, Q.subgroupOf B⁆).map B.subtype = ⁅X, Q⁆ :=
      commutator_subgroupOf_map_eq B Q X hQB hXB
    have hxmap : (x : G) ∈ (⁅X.subgroupOf B, Q.subgroupOf B⁆).map B.subtype :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact hmap ▸ hxmap
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxmap : (x : G) ∈ (⁅X.subgroupOf B, Q.subgroupOf B⁆).map B.subtype := by
      rw [commutator_subgroupOf_map_eq B Q X hQB hXB]
      exact hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hyx' : y = x := by
      apply Subtype.ext
      exact hyx
    simpa [hyx'] using hy

/-- Three-Subgroups Lemma with containment: if `[X, Q, P]` lies in the
normal subgroup `O` of `B` and `[P, Q] = 1`, then `[X, P, Q]` lies in
`O` (all subgroups inside `B`). -/
private lemma commutator_three_subgroups_le
    {G : Type u} [Group G] [Finite G]
    (B O X P Q : Subgroup G)
    (hOB : IsNormalIn O B) (hXB : X ≤ B) (hPB : P ≤ B) (hQB : Q ≤ B)
    (h1 : ⁅⁅X, Q⁆, P⁆ ≤ O) (hPQ : ⁅P, Q⁆ = ⊥) :
    ⁅⁅X, P⁆, Q⁆ ≤ O := by
  let H : Type u := ↥B
  let O' : Subgroup H := O.subgroupOf B
  have hO'norm : O'.Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOB.1]
    exact le_normalizer_of_isNormalIn hOB
  let : O'.Normal := hO'norm
  let π : H →* H ⧸ O' := QuotientGroup.mk' O'
  let X' : Subgroup (H ⧸ O') := (X.subgroupOf B).map π
  let P' : Subgroup (H ⧸ O') := (P.subgroupOf B).map π
  let Q' : Subgroup (H ⧸ O') := (Q.subgroupOf B).map π
  have hXQ_leB : ⁅X, Q⁆ ≤ B := (Subgroup.commutator_le_sup X Q).trans (sup_le hXB hQB)
  have hXQP_leB : ⁅⁅X, Q⁆, P⁆ ≤ B :=
    (Subgroup.commutator_le_sup ⁅X, Q⁆ P).trans (sup_le hXQ_leB hPB)
  have hXP_leB : ⁅X, P⁆ ≤ B := (Subgroup.commutator_le_sup X P).trans (sup_le hXB hPB)
  have hXQP_leB' : ⁅⁅X, P⁆, Q⁆ ≤ B :=
    (Subgroup.commutator_le_sup ⁅X, P⁆ Q).trans (sup_le hXP_leB hQB)
  have hsub1 : (⁅⁅X, Q⁆, P⁆).subgroupOf B =
      ⁅⁅X.subgroupOf B, Q.subgroupOf B⁆, P.subgroupOf B⁆ := by
    rw [← commutator_subgroupOf_eq B ⁅X, Q⁆ P hXQ_leB hPB]
    rw [← commutator_subgroupOf_eq B X Q hXB hQB]
  have htrans1 : ((⁅⁅X, Q⁆, P⁆).subgroupOf B).map π = ⁅⁅X', Q'⁆, P'⁆ := by
    rw [hsub1]
    simp [X', P', Q', Subgroup.map_commutator]
  have hOmap : O'.map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := π) (H := O')).2
    intro x hx
    exact (QuotientGroup.ker_mk' O').symm ▸ hx
  have hmapbot1 : ((⁅⁅X, Q⁆, P⁆).subgroupOf B).map π = ⊥ := by
    have hleO' : (⁅⁅X, Q⁆, P⁆).subgroupOf B ≤ O' := Subgroup.subgroupOf_mono B h1
    exact le_antisymm
      ((Subgroup.map_mono (f := π) hleO').trans (le_of_eq hOmap)) bot_le
  have h1' : ⁅⁅X', Q'⁆, P'⁆ = ⊥ := by
    simpa [htrans1] using hmapbot1
  have hPQs : ⁅⁅P, Q⁆, X⁆ = ⊥ := by
    simp [hPQ]
  have hsub2 : (⁅⁅P, Q⁆, X⁆).subgroupOf B =
      ⁅⁅P.subgroupOf B, Q.subgroupOf B⁆, X.subgroupOf B⁆ := by
    rw [← commutator_subgroupOf_eq B ⁅P, Q⁆ X
      ((Subgroup.commutator_le_sup P Q).trans (sup_le hPB hQB)) hXB]
    rw [← commutator_subgroupOf_eq B P Q hPB hQB]
  have htrans2 : ((⁅⁅P, Q⁆, X⁆).subgroupOf B).map π = ⁅⁅P', Q'⁆, X'⁆ := by
    rw [hsub2]
    simp [X', P', Q', Subgroup.map_commutator]
  have h2' : ⁅⁅P', Q'⁆, X'⁆ = ⊥ := by
    simpa [hPQs] using htrans2.symm
  have hrot2 : ⁅⁅Q', X'⁆, P'⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (H₁ := Q') (H₂ := X')]
    exact h1'
  have h3' : ⁅⁅X', P'⁆, Q'⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := X') (H₂ := P') (H₃ := Q')
      h2' hrot2
  have hsub3 : (⁅⁅X, P⁆, Q⁆).subgroupOf B =
      ⁅⁅X.subgroupOf B, P.subgroupOf B⁆, Q.subgroupOf B⁆ := by
    rw [← commutator_subgroupOf_eq B ⁅X, P⁆ Q hXP_leB hQB]
    rw [← commutator_subgroupOf_eq B X P hXB hPB]
  have htrans3 : ((⁅⁅X, P⁆, Q⁆).subgroupOf B).map π = ⁅⁅X', P'⁆, Q'⁆ := by
    rw [hsub3]
    simp [X', P', Q', Subgroup.map_commutator]
  have hmapbot3 : ((⁅⁅X, P⁆, Q⁆).subgroupOf B).map π = ⊥ := by
    simpa [htrans3] using h3'
  have hleO'3 : (⁅⁅X, P⁆, Q⁆).subgroupOf B ≤ O' := by
    have hker : π.ker = O' := QuotientGroup.ker_mk' O'
    simpa [hker] using (Subgroup.map_eq_bot_iff (f := π)
      (H := (⁅⁅X, P⁆, Q⁆).subgroupOf B)).1 (by simpa [hker] using hmapbot3)
  intro x hx
  have hxB' : x ∈ B := hXQP_leB' hx
  have hxsub : (⟨x, hxB'⟩ : ↥B) ∈ (⁅⁅X, P⁆, Q⁆).subgroupOf B := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  have hxO' : (⟨x, hxB'⟩ : ↥B) ∈ O' := hleO'3 hxsub
  exact (Subgroup.mem_subgroupOf).1 hxO'

/-- A normal `p`-subgroup of a subgroup which is normal in `B` lies in
`O_p(B)`. -/
private lemma le_qCoreOf_of_isNormalIn_chain
    {G : Type u} [Group G] [Finite G]
    (M B : Subgroup G) (p : ℕ) (hp : p.Prime)
    {N : Subgroup G} (hNM : IsNormalIn N M) (hMB : IsNormalIn M B) (hNp : IsPGroup p N) :
    N ≤ qCoreOf B p := by
  have h1 : N ≤ qCoreOf M p := le_qCoreOf_of_normal_isPGroup M N p hNM.1 (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNM.1]
    exact le_normalizer_of_isNormalIn hNM) hNp
  have h2 : qCoreOf M p ≤ qCoreOf B p := by
    have hOMB : IsNormalIn (qCoreOf M p) B := by
      have h := map_characteristic_isNormalIn_of_isNormalIn (H := M) (N := B)
        (pCore p (↥M)) (pCore_characteristic (p := p)) hMB
      simpa [qCoreOf] using h
    exact le_qCoreOf_of_normal_isPGroup B (qCoreOf M p) p hOMB.1 (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOMB.1]
      exact le_normalizer_of_isNormalIn hOMB) (qCoreOf_isPGroup M p)
  exact h1.trans h2

/-- For distinct primes, a `q`-group has order coprime to `p`. -/
private lemma coprime_card_of_isPGroup_ne
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q) (hP : IsPGroup q P) :
    Nat.Coprime p (Nat.card (↥P)) := by
  let : Fact q.Prime := ⟨hq⟩
  rcases IsPGroup.iff_card.mp hP with ⟨n, hn⟩
  rw [hn]
  simpa using ((Nat.coprime_primes hp hq).2 hne).pow 1 n

/-- `O_q(F(A)) ≤ O_q(A)`. -/
private lemma qCoreOf_fittingSubgroupOf_le_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) (q : ℕ) (hq : q.Prime) :
    qCoreOf (fittingSubgroupOf A) q ≤ qCoreOf A q := by
  let F : Subgroup G := fittingSubgroupOf A
  have hQF : qCoreOf F q ≤ F := qCoreOf_le F q
  have hQFnormA : IsNormalIn (qCoreOf F q) A := by
    have h := map_characteristic_isNormalIn_of_isNormalIn (H := F) (N := A)
      (pCore q (↥F)) (pCore_characteristic (p := q)) (fittingSubgroupOf_isNormalIn A)
    simpa [qCoreOf] using h
  exact le_qCoreOf_of_normal_isPGroup A (qCoreOf F q) q hQFnormA.1 (by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQFnormA.1]
    exact le_normalizer_of_isNormalIn hQFnormA) (qCoreOf_isPGroup F q)

/-- If `q ∈ π(F(A))`, then `O_q(A) ≠ 1`. -/
private lemma qCoreOf_ne_bot_of_mem_primesOfOrder
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {q : ℕ} (hq : q.Prime) (hqA : q ∈ primesOfOrder (fittingSubgroupOf A)) :
    qCoreOf A q ≠ ⊥ := by
  have hQFA : qCoreOf (fittingSubgroupOf A) q ≠ ⊥ :=
    fstar_qCoreOf_fitting_ne_bot_of_mem_primesOfOrder A q hq hqA
  have hle : qCoreOf (fittingSubgroupOf A) q ≤ qCoreOf A q :=
    qCoreOf_fittingSubgroupOf_le_qCoreOf A q hq
  intro hbot
  exact hQFA (le_bot_iff.mp (hle.trans (le_of_eq hbot)))

/-- If `O_q(A) ≠ 1`, then `q ∈ π(F(A))`. -/
private lemma mem_primesOfOrder_of_qCoreOf_ne_bot
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {q : ℕ} (hq : q.Prime) (hQ : qCoreOf A q ≠ ⊥) :
    q ∈ primesOfOrder (fittingSubgroupOf A) := by
  let P : Subgroup G := qCoreOf A q
  have hPleF : P ≤ fittingSubgroupOf A := qCoreOf_le_fittingSubgroupOf A q hq
  have hPp : IsPGroup q P := qCoreOf_isPGroup A q
  let : Fact q.Prime := ⟨hq⟩
  rcases IsPGroup.iff_card.mp hPp with ⟨n, hn⟩
  have hnt : Nontrivial (↥P) := (Subgroup.nontrivial_iff_ne_bot P).2 hQ
  let : Fintype (↥P) := Fintype.ofFinite _
  have hcard_ne_one : Fintype.card (↥P) ≠ 1 :=
    ne_of_gt (Fintype.one_lt_card_iff_nontrivial.2 hnt)
  have hkpos : n ≠ 0 := by
    intro hn0
    have hcard : Fintype.card (↥P) = 1 := by
      simpa [hn0, Nat.card_eq_fintype_card] using hn
    exact hcard_ne_one hcard
  have hqdvd : q ∣ Nat.card (↥P) := by
    rw [hn]
    exact ⟨q ^ (n - 1), by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hkpos)]⟩
  have hqdvdF : q ∣ Nat.card (↥(fittingSubgroupOf A)) :=
    hqdvd.trans (Subgroup.card_dvd_of_le hPleF)
  exact Nat.mem_primeFactors.mpr ⟨hq, hqdvdF, Nat.card_pos.ne'⟩

/-- `O_q(F(B)) = O_q(B)`: the `q`-core of the Fitting subgroup is the
`q`-core. -/
private lemma qCoreOf_fittingSubgroupOf_eq_qCoreOf
    {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) (q : ℕ) (hq : q.Prime) :
    qCoreOf (fittingSubgroupOf B) q = qCoreOf B q := by
  apply le_antisymm
  · exact qCoreOf_fittingSubgroupOf_le_qCoreOf B q hq
  · have hQBF : qCoreOf B q ≤ fittingSubgroupOf B := qCoreOf_le_fittingSubgroupOf B q hq
    have hQBnF : IsNormalIn (qCoreOf B q) (fittingSubgroupOf B) := by
      refine ⟨hQBF, ?_⟩
      intro f hf x hx
      have hfB : f ∈ B := by
        rcases (Subgroup.mem_map).1 hf with ⟨g, _hg, rfl⟩
        exact g.2
      exact (qCoreOf_normal_in B q).2 f hfB x hx
    exact le_qCoreOf_of_normal_isPGroup (fittingSubgroupOf B) (qCoreOf B q) q hQBF (by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hQBF]
      exact le_normalizer_of_isNormalIn hQBnF) (qCoreOf_isPGroup B q)

/-- If `O_q(A) ≠ 1`, its ambient normalizer is exactly the maximal
subgroup `A`. -/
private lemma normalizer_qCoreOf_eq_self_of_ne_bot
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    {q : ℕ} (hQne : qCoreOf A q ≠ ⊥) :
    Subgroup.normalizer ((qCoreOf A q : Subgroup G) : Set G) = A := by
  classical
  let P : Subgroup G := qCoreOf A q
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hPnormalA : IsNormalIn P A := qCoreOf_normal_in A q
  have hAleN : A ≤ N := le_normalizer_of_isNormalIn hPnormalA
  have hNne_top : N ≠ ⊤ := by
    intro htop
    have hPnormG : P.Normal := (Subgroup.normalizer_eq_top_iff).mp htop
    rcases (haveI := hPnormG; hsimple.eq_bot_or_eq_top_of_normal P) with hbot | htopP
    · exact hQne hbot
    · have hAtop : A = ⊤ := by
        have hTopLeA : (⊤ : Subgroup G) ≤ A := by
          intro x hx
          have hxP : x ∈ P := htopP ▸ hx
          exact (qCoreOf_le A q) (by simpa [P] using hxP)
        exact le_antisymm le_top hTopLeA
      exact hA.1 hAtop
  refine le_antisymm ?_ hAleN
  intro x hx
  by_cases hEq : A = N
  · rw [hEq]
    exact hx
  · have hlt : A < N := lt_of_le_of_ne hAleN (by intro h; exact hEq h)
    have htop := hA.2 N hlt
    exact False.elim (hNne_top htop)

/-- The pointwise product of a subgroup normal in the join with any
subgroup is the join (local normality version). -/
private lemma mul_eq_sup_of_isNormalIn
    {G : Type u} [Group G] (A B : Subgroup G)
    (hA : IsNormalIn A (A ⊔ B)) :
    ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) := by
  apply le_antisymm
  · intro x hx
    change x ∈ A ⊔ B at hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction'' ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with hyA | hyB
      · exact Set.mem_mul.mpr ⟨y, hyA, 1, B.one_mem, mul_one y⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, y, hyB, one_mul y⟩
    · intro x hx
      rcases hx with hxA | hxB
      · exact Set.mem_mul.mpr ⟨x⁻¹, A.inv_mem hxA, 1, B.one_mem, mul_one x⁻¹⟩
      · exact Set.mem_mul.mpr ⟨1, A.one_mem, x⁻¹, B.inv_mem hxB, one_mul x⁻¹⟩
    · exact Set.mem_mul.mpr ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
    · intro a b hx hy ha hb
      rcases (Set.mem_mul).1 ha with ⟨a₁, ha₁, b₁, hb₁, rfl⟩
      rcases (Set.mem_mul).1 hb with ⟨a₂, ha₂, b₂, hb₂, rfl⟩
      refine Set.mem_mul.mpr ⟨a₁ * (b₁ * a₂ * b₁⁻¹), ?_, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
      · exact A.mul_mem ha₁ (hA.2 b₁ (Subgroup.mem_sup_right (S := A) (T := B) hb₁) a₂ ha₂)
      · group
  · intro x hx
    rcases (Set.mem_mul).1 hx with ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

/-- A `p`-subgroup of a product of a `p`-group and a `q`-group (`p ≠ q`)
which commute lies in the `p`-factor. -/
private lemma le_qCoreOf_of_isPGroup_of_mem_sup
    {G : Type u} [Group G] [Finite G]
    (Q B T : Subgroup G) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hTle : T ≤ Q ⊔ B) (hTp : IsPGroup p T) (hQp : IsPGroup p Q) (hBq : IsPGroup q B)
    (hQnorm : IsNormalIn Q (Q ⊔ B)) (hcomm : ⁅Q, B⁆ = ⊥) :
    T ≤ Q := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hQcB : Q ≤ Subgroup.centralizer (B : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := Q) (H₂ := B)).1 hcomm
  have hprod : ((Q ⊔ B : Subgroup G) : Set G) = (Q : Set G) * (B : Set G) :=
    mul_eq_sup_of_isNormalIn Q B hQnorm
  intro t ht
  rcases (Set.mem_mul).1
    (show t ∈ (Q : Set G) * (B : Set G) from hprod ▸ hTle ht) with ⟨a, ha, b, hb, rfl⟩
  have hcomm_ab : Commute a b :=
    ((Subgroup.mem_centralizer_iff.mp (hQcB ha)) b hb).symm
  rcases IsPGroup.iff_orderOf.mp hTp ⟨a * b, ht⟩ with ⟨n, hn⟩
  have hn' : orderOf (a * b) = p ^ n := by
    simpa using (orderOf_injective T.subtype T.subtype_injective ⟨a * b, ht⟩).trans hn
  rcases IsPGroup.iff_orderOf.mp hQp ⟨a, ha⟩ with ⟨m, hm⟩
  have hm' : orderOf a = p ^ m := by
    simpa using (orderOf_injective Q.subtype Q.subtype_injective ⟨a, ha⟩).trans hm
  rcases IsPGroup.iff_orderOf.mp hBq ⟨b, hb⟩ with ⟨k, hk⟩
  have hk' : orderOf b = q ^ k := by
    simpa using (orderOf_injective B.subtype B.subtype_injective ⟨b, hb⟩).trans hk
  have hcop : Nat.Coprime (orderOf a) (orderOf b) := by
    rw [hm', hk']
    exact ((Nat.coprime_primes hp hq).2 hne).pow m k
  have hord : orderOf (a * b) = orderOf a * orderOf b :=
    Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm_ab hcop
  have hb1 : b = 1 := by
    by_contra hbne
    have hkpos : k ≠ 0 := by
      intro hk0
      have hb1' : b = 1 := by
        have hbord : orderOf b = 1 := by simpa [hk0] using hk'
        exact (orderOf_eq_one_iff.mp hbord)
      exact hbne hb1'
    have hqdvdb : q ∣ orderOf b := by
      rw [hk']
      exact ⟨q ^ (k - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hkpos)]⟩
    have hqdvda : q ∣ orderOf (a * b) := by
      rw [hord]
      exact hqdvdb.trans ⟨orderOf a, by rw [mul_comm]⟩
    have hqdvdp : q ∣ p ^ n := by
      rwa [hn'] at hqdvda
    have hqdvdp' : q ∣ p := hq.dvd_of_dvd_pow hqdvdp
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp hqdvdp'
    exact hne hqeq.symm
  simpa [hb1] using ha

/-- The Fitting subgroup is the join of all `O_r(B)` over primes `r`. -/
private lemma fittingSubgroupOf_eq_iSup_qCoreOf_prime
    {G : Type u} [Group G] [Finite G] (B : Subgroup G) :
    fittingSubgroupOf B = ⨆ r : {r : ℕ // r.Prime}, qCoreOf B r.1 := by
  apply le_antisymm
  · rw [fittingSubgroupOf_eq_iSup_qCoreOf B]
    exact iSup_le (fun q => le_iSup
      (f := fun r : {r : ℕ // r.Prime} => qCoreOf B r.1)
      ⟨q.1.1, Nat.prime_of_mem_primeFactors q.1.2⟩)
  · exact iSup_le (fun r => qCoreOf_le_fittingSubgroupOf B r.1 r.2)

/-- A subgroup normalizes itself. -/
private lemma le_normalizer_self {G : Type u} [Group G] (H : Subgroup G) :
    H ≤ Subgroup.normalizer (H : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)
  · intro hy
    have hxinv : x⁻¹ ∈ H := H.inv_mem hx
    have hy' : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem hxinv hy) (H.inv_mem hxinv)
    simpa [mul_assoc] using hy'

/-- The prime divisors of `F(A)` and `F(B)` agree under the 1.6
hypotheses. -/
private lemma mem_primesOfOrder_fittingB_of_mem_primesOfOrder_fittingA
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A B : Subgroup G) (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A)
    {q : ℕ} (hq : q.Prime) (hqA : q ∈ primesOfOrder (fittingSubgroupOf A)) :
    q ∈ primesOfOrder (fittingSubgroupOf B) := by
  have hEB : componentLayerOf B = ⊥ :=
    componentLayerOf_eq_bot_of_pair hsimple B A hB hA hne.symm hFBA hFAB
  have hFstB : generalizedFittingSubgroupOf B = fittingSubgroupOf B := by
    rw [generalizedFittingSubgroupOf, hEB]
    simp
  have hQne : qCoreOf A q ≠ ⊥ := qCoreOf_ne_bot_of_mem_primesOfOrder A hq hqA
  by_contra hqB
  have hQBbot : qCoreOf B q = ⊥ := by
    by_contra hQ'
    exact hqB (mem_primesOfOrder_of_qCoreOf_ne_bot B hq hQ')
  have hQcF : qCoreOf A q ≤ Subgroup.centralizer
      ((fittingSubgroupOf B : Subgroup G) : Set G) := by
    rw [fittingSubgroupOf_eq_iSup_qCoreOf_prime B]
    exact le_centralizer_of_centralizes_iSup (C := qCoreOf A q)
      (X := fun r : {r : ℕ // r.Prime} => qCoreOf B r.1) (by
        intro r
        by_cases hqr : q = r.1
        · have hbot : qCoreOf B r.1 = ⊥ := by simpa [hqr] using hQBbot
          have hcomm : ⁅qCoreOf A q, qCoreOf B r.1⁆ = ⊥ := by
            simpa [hbot] using (Subgroup.commutator_bot_right (H₁ := qCoreOf A q))
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer
            (H₁ := qCoreOf A q) (H₂ := qCoreOf B r.1)).1 hcomm
        · have hcomm : ⁅qCoreOf A q, qCoreOf B r.1⁆ = ⊥ :=
            qCoreOf_commute_cross A B hq r.2 hqr hFAB hFBA
          exact (Subgroup.commutator_eq_bot_iff_le_centralizer
            (H₁ := qCoreOf A q) (H₂ := qCoreOf B r.1)).1 hcomm)
  have hQleB : qCoreOf A q ≤ B :=
    (qCoreOf_le_fittingSubgroupOf A q hq).trans
      ((le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFAB)
  have hQleF : qCoreOf A q ≤ fittingSubgroupOf B := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer
        ((generalizedFittingSubgroupOf B : Set G)) := by
      have hx' : x ∈ Subgroup.centralizer ((fittingSubgroupOf B : Set G)) := hQcF hx
      simpa [hFstB] using hx'
    have hxF : x ∈ generalizedFittingSubgroupOf B :=
      (centralizer_intersection_fstar_le_fstar B) ⟨hxC, hQleB hx⟩
    simpa [hFstB] using hxF
  have hQleQF : qCoreOf A q ≤ qCoreOf (fittingSubgroupOf B) q :=
    le_qCoreOf_of_isPGroup_of_le_fitting (fittingSubgroupOf B) (qCoreOf A q) q hq
      hQleF (by
        rw [fittingSubgroupOf_fittingSubgroupOf_eq_self B]
        exact hQleF) (qCoreOf_isPGroup A q)
  have hQleQB : qCoreOf A q ≤ qCoreOf B q :=
    hQleQF.trans (le_of_eq (qCoreOf_fittingSubgroupOf_eq_qCoreOf B q hq))
  exact hQne (le_bot_iff.mp (hQleQB.trans (le_of_eq hQBbot)))

/-- The symmetric direction of the prime-divisor agreement. -/
private lemma mem_primesOfOrder_fittingA_of_mem_primesOfOrder_fittingB
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A B : Subgroup G) (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A)
    {q : ℕ} (hq : q.Prime) (hqB : q ∈ primesOfOrder (fittingSubgroupOf B)) :
    q ∈ primesOfOrder (fittingSubgroupOf A) :=
  mem_primesOfOrder_fittingB_of_mem_primesOfOrder_fittingA
    hsimple B A hB hA hne.symm hFBA hFAB hq hqB

/-- Under the 1.6 hypotheses, `Y_2 := [B, O_p(A), O_p(A)]` lies in
`A ∩ B` (KS 10.1.4, claim `(′′)` for the `Y_2` half). -/
private lemma commutator_double_le_intersection
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A B : Subgroup G) (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpA : p ∈ primesOfOrder (fittingSubgroupOf A))
    (hqA : q ∈ primesOfOrder (fittingSubgroupOf A)) :
    ⁅⁅B, qCoreOf A p⁆, qCoreOf A p⁆ ≤ A ⊓ B := by
  let P : Subgroup G := qCoreOf A p
  let Q : Subgroup G := qCoreOf A q
  let X : Subgroup G := ⁅B, P⁆
  let Y : Subgroup G := ⁅X, P⁆
  let Sp : Subgroup G := ⨆ r : {r : ℕ // r.Prime ∧ r ≠ p}, qCoreOf B r.1
  let Sq : Subgroup G := ⨆ r : {r : ℕ // r.Prime ∧ r ≠ q}, qCoreOf B r.1
  have hPA : P ≤ A := qCoreOf_le A p
  have hQA : Q ≤ A := qCoreOf_le A q
  have hPB : P ≤ B :=
    (qCoreOf_le_fittingSubgroupOf A p hp).trans
      ((le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFAB)
  have hQB : Q ≤ B :=
    (qCoreOf_le_fittingSubgroupOf A q hq).trans
      ((le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFAB)
  have hOpA : qCoreOf B p ≤ A :=
    (qCoreOf_le_fittingSubgroupOf B p hp).trans
      ((le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans hFBA)
  have hXB : X ≤ B :=
    (Subgroup.commutator_le_sup B P).trans (sup_le (le_rfl : B ≤ B) hPB)
  have hYB : Y ≤ B :=
    (Subgroup.commutator_le_sup X P).trans (sup_le hXB hPB)
  have hEB : componentLayerOf B = ⊥ :=
    componentLayerOf_eq_bot_of_pair hsimple B A hB hA hne.symm hFBA hFAB
  have hFstB : generalizedFittingSubgroupOf B = fittingSubgroupOf B := by
    rw [generalizedFittingSubgroupOf, hEB]
    simp
  have hFleB : fittingSubgroupOf B ≤ B := by
    intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨f, _hf, rfl⟩
    exact f.2
  have hSpB : IsNormalIn Sp B := by
    dsimp [Sp]
    exact isNormalIn_iSup (fun r : {r : ℕ // r.Prime ∧ r ≠ p} => qCoreOf B r.1) B
      (fun r => qCoreOf_normal_in B r.1)
  have hSqB : IsNormalIn Sq B := by
    dsimp [Sq]
    exact isNormalIn_iSup (fun r : {r : ℕ // r.Prime ∧ r ≠ q} => qCoreOf B r.1) B
      (fun r => qCoreOf_normal_in B r.1)
  have hPcSp : P ≤ Subgroup.centralizer (Sp : Set G) := by
    dsimp [Sp]
    exact le_centralizer_of_centralizes_iSup (C := P)
      (X := fun r : {r : ℕ // r.Prime ∧ r ≠ p} => qCoreOf B r.1) (by
        intro r
        have hcomm : ⁅P, qCoreOf B r.1⁆ = ⊥ :=
          qCoreOf_commute_cross A B hp r.2.1 r.2.2.symm hFAB hFBA
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := P) (H₂ := qCoreOf B r.1)).1 hcomm)
  have hQcSq : Q ≤ Subgroup.centralizer (Sq : Set G) := by
    dsimp [Sq]
    exact le_centralizer_of_centralizes_iSup (C := Q)
      (X := fun r : {r : ℕ // r.Prime ∧ r ≠ q} => qCoreOf B r.1) (by
        intro r
        have hcomm : ⁅Q, qCoreOf B r.1⁆ = ⊥ :=
          qCoreOf_commute_cross A B hq r.2.1 r.2.2.symm hFAB hFBA
        exact (Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := Q) (H₂ := qCoreOf B r.1)).1 hcomm)
  have hXcSp : X ≤ Subgroup.centralizer (Sp : Set G) ⊓ B := by
    simpa [X, Subgroup.commutator_comm (H₁ := P) (H₂ := B)] using
      (commutator_le_centralizer_of_le_centralizer_normal
      (X := P) (H := B) (N := Sp) (B := B) hPB (le_rfl : B ≤ B) hSpB hPcSp)
  have hXQcSp : ⁅X, Q⁆ ≤ Subgroup.centralizer (Sp : Set G) ⊓ B :=
    commutator_le_centralizer_of_le_centralizer_normal
      (X := X) (H := Q) (N := Sp) (B := B) hXB hQB hSpB
      (by intro x hx; exact (hXcSp hx).1)
  have hXQcSq : ⁅X, Q⁆ ≤ Subgroup.centralizer (Sq : Set G) ⊓ B :=
    by
      have h' : ⁅Q, X⁆ ≤ Subgroup.centralizer (Sq : Set G) ⊓ B :=
        commutator_le_centralizer_of_le_centralizer_normal
          (X := Q) (H := X) (N := Sq) (B := B) hQB hXB hSqB hQcSq
      simpa [Subgroup.commutator_comm (H₁ := Q) (H₂ := X)] using h'
  have hSpSq : Sp ⊔ Sq = fittingSubgroupOf B := by
    rw [fittingSubgroupOf_eq_iSup_qCoreOf_prime B]
    apply le_antisymm
    · exact sup_le
        (iSup_le (fun r => le_iSup
          (f := fun s : {s : ℕ // s.Prime} => qCoreOf B s.1) ⟨r.1, r.2.1⟩))
        (iSup_le (fun r => le_iSup
          (f := fun s : {s : ℕ // s.Prime} => qCoreOf B s.1) ⟨r.1, r.2.1⟩))
    · exact iSup_le (fun r => by
        by_cases hr : r.1 = p
        · exact (le_iSup
            (f := fun s : {s : ℕ // s.Prime ∧ s ≠ q} => qCoreOf B s.1)
            ⟨r.1, r.2, by rw [hr]; exact hpq⟩).trans
            (le_sup_right : Sq ≤ Sp ⊔ Sq)
        · exact (le_iSup
            (f := fun s : {s : ℕ // s.Prime ∧ s ≠ p} => qCoreOf B s.1)
            ⟨r.1, r.2, hr⟩).trans (le_sup_left : Sp ≤ Sp ⊔ Sq))
  have hXQcF : ⁅X, Q⁆ ≤ Subgroup.centralizer
      ((fittingSubgroupOf B : Subgroup G) : Set G) ⊓ B := by
    intro x hx
    have hx1 : x ∈ Subgroup.centralizer (Sp : Set G) ⊓ B := hXQcSp hx
    have hx2 : x ∈ Subgroup.centralizer (Sq : Set G) ⊓ B := hXQcSq hx
    have hxc : x ∈ Subgroup.centralizer ((Sp ⊔ Sq : Subgroup G) : Set G) :=
      (le_centralizer_of_centralizes_join
        (C := Subgroup.centralizer (Sp : Set G) ⊓ Subgroup.centralizer (Sq : Set G))
        (F := Sp) (E := Sq)
        (by intro y hy; exact hy.1) (by intro y hy; exact hy.2)) ⟨hx1.1, hx2.1⟩
    rw [hSpSq] at hxc
    exact ⟨hxc, hx1.2⟩
  have hXQcZ : ⁅X, Q⁆ ≤
      fittingSubgroupOf B ⊓ Subgroup.centralizer ((fittingSubgroupOf B : Set G)) := by
    intro x hx
    have hxFB : x ∈ fittingSubgroupOf B := by
      have hx' : x ∈ generalizedFittingSubgroupOf B :=
        (centralizer_intersection_fstar_le_fstar B) ⟨(by
          have hx1 := hXQcF hx
          simpa [hFstB] using hx1.1), (hXQcF hx).2⟩
      simpa [hFstB] using hx'
    exact ⟨hxFB, (hXQcF hx).1⟩
  let Z : Subgroup G :=
    fittingSubgroupOf B ⊓ Subgroup.centralizer ((fittingSubgroupOf B : Set G))
  have hZPe : ⁅Z, P⁆ ≤ qCoreOf B p := by
    have h1 : ⁅Z, P⁆ ≤ P := by
      rw [Subgroup.commutator_le]
      intro z hz a ha
      have hzA : z ∈ A :=
        (inf_le_left : Z ≤ fittingSubgroupOf B).trans
          ((le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans
            hFBA) hz
      have hconj : z * a * z⁻¹ ∈ P := (qCoreOf_normal_in A p).2 z hzA a ha
      exact P.mul_mem hconj (P.inv_mem ha)
    have h2 : ⁅Z, P⁆ ≤ fittingSubgroupOf B := by
      rw [Subgroup.commutator_le]
      intro z hz a ha
      have hzF : z ∈ fittingSubgroupOf B := (inf_le_left : Z ≤ fittingSubgroupOf B) hz
      have haN : a ∈ Subgroup.normalizer ((fittingSubgroupOf B : Set G)) :=
        le_normalizer_of_isNormalIn (fittingSubgroupOf_isNormalIn B) (hPB ha)
      have haz : a * z⁻¹ * a⁻¹ ∈ fittingSubgroupOf B :=
        (Subgroup.mem_normalizer_iff.mp haN z⁻¹).1
          ((fittingSubgroupOf B).inv_mem hzF)
      change z * a * z⁻¹ * a⁻¹ ∈ fittingSubgroupOf B
      simpa [mul_assoc] using (fittingSubgroupOf B).mul_mem hzF haz
    exact (le_inf h1 h2).trans (le_qCoreOf_of_isPGroup_of_le_fitting B (P ⊓ fittingSubgroupOf B) p hp
      ((inf_le_left : P ⊓ fittingSubgroupOf B ≤ P).trans hPB) inf_le_right
      (IsPGroup.to_inf_left (qCoreOf_isPGroup A p)))
  have hXQPe : ⁅⁅X, Q⁆, P⁆ ≤ qCoreOf B p :=
    (Subgroup.commutator_mono hXQcZ le_rfl).trans hZPe
  have hPQ : ⁅P, Q⁆ = ⊥ :=
    commutator_eq_bot_of_normal_pgroup_pPrime A p hp P Q hPA (qCoreOf_normal_in A p)
      (qCoreOf_isPGroup A p) hQA (qCoreOf_normal_in A q)
      (coprime_card_of_isPGroup_ne Q hp hq hpq (qCoreOf_isPGroup A q))
  have hYXQ : ⁅⁅X, P⁆, Q⁆ ≤ qCoreOf B p :=
    commutator_three_subgroups_le B (qCoreOf B p) X P Q
      (qCoreOf_normal_in B p) hXB hPB hQB hXQPe hPQ
  have hYQ : ⁅Y, Q⁆ ≤ qCoreOf B p := by
    simpa [Y] using hYXQ
  have hYOp : ⁅Y, qCoreOf B p⁆ ≤ qCoreOf B p := by
    have h : ⁅qCoreOf B p, Y⁆ ≤ qCoreOf B p :=
      (Subgroup.le_normalizer_iff_commutator_le_left (H := Y) (K := qCoreOf B p)).1
        (hYB.trans (le_normalizer_of_isNormalIn (qCoreOf_normal_in B p)))
    simpa [Subgroup.commutator_comm (H₁ := qCoreOf B p) (H₂ := Y)] using h
  have hYleND : Y ≤ Subgroup.normalizer ((Q ⊔ qCoreOf B p : Subgroup G) : Set G) := by
    have h1 : ⁅Q ⊔ qCoreOf B p, Y⁆ ≤ qCoreOf B p := by
      apply commutator_sup_le_of_commutator_le_and_normalize
        (A := Q) (B := qCoreOf B p) (C := Y) (D := qCoreOf B p)
      · simpa [Subgroup.commutator_comm (H₁ := Q) (H₂ := Y)] using hYQ
      · simpa [Subgroup.commutator_comm (H₁ := qCoreOf B p) (H₂ := Y)] using hYOp
      · have hcomm : ⁅Q, qCoreOf B p⁆ = ⊥ :=
          qCoreOf_commute_cross A B hq hp hpq.symm hFAB hFBA
        exact ((Subgroup.commutator_eq_bot_iff_le_centralizer
          (H₁ := Q) (H₂ := qCoreOf B p)).1 hcomm).trans
          (Subgroup.centralizer_le_normalizer _)
      · exact (Subgroup.le_normalizer_iff).2 (by
          intro y hy z hz
          exact (qCoreOf B p).mul_mem ((qCoreOf B p).mul_mem hy hz) ((qCoreOf B p).inv_mem hy))
    exact (Subgroup.le_normalizer_iff_commutator_le_left
      (H := Y) (K := Q ⊔ qCoreOf B p)).2
      (h1.trans (le_sup_right : qCoreOf B p ≤ Q ⊔ qCoreOf B p))
  have hQnormD : IsNormalIn Q (Q ⊔ qCoreOf B p) := by
    refine ⟨le_sup_left, ?_⟩
    intro d hd q0 hq0
    exact (qCoreOf_normal_in A q).2 d (sup_le hQA hOpA hd) q0 hq0
  have hYleNQ : Y ≤ Subgroup.normalizer (Q : Set G) := by
    have hfwd : ∀ y : G, y ∈ Y → ∀ x : G, x ∈ Q → y * x * y⁻¹ ∈ Q := by
      intro y hy x hx
      let T : Subgroup G := Q.map (MulAut.conj y).toMonoidHom
      have hTle : T ≤ Q ⊔ qCoreOf B p := by
        intro z hz
        rcases (Subgroup.mem_map).1 hz with ⟨q0, hq0, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hYleND hy) q0).1 (by
          simpa using (le_sup_left : Q ≤ Q ⊔ qCoreOf B p) hq0)
      have hTp : IsPGroup q T :=
        IsPGroup.map (qCoreOf_isPGroup A q) (MulAut.conj y).toMonoidHom
      have hTleQ : T ≤ Q := le_qCoreOf_of_isPGroup_of_mem_sup Q (qCoreOf B p) T
        q p hq hp hpq.symm hTle hTp (qCoreOf_isPGroup A q) (qCoreOf_isPGroup B p)
        hQnormD (qCoreOf_commute_cross A B hq hp hpq.symm hFAB hFBA)
      exact hTleQ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hfwd y hy x
    · intro hx
      have hx' : y⁻¹ * (y * x * y⁻¹) * (y⁻¹)⁻¹ ∈ Q :=
        hfwd y⁻¹ (Y.inv_mem hy) (y * x * y⁻¹) hx
      simpa [mul_assoc] using hx'
  have hQne : qCoreOf A q ≠ ⊥ := qCoreOf_ne_bot_of_mem_primesOfOrder A hq hqA
  have hNQ : Subgroup.normalizer (Q : Set G) = A :=
    normalizer_qCoreOf_eq_self_of_ne_bot hsimple A hA hQne
  intro x hx
  exact ⟨hNQ ▸ hYleNQ hx, hYB hx⟩

/-- Normality transports through `subgroupOf`. -/
private lemma isNormal_subgroupOf_of_isNormalIn
    {G : Type u} [Group G] {B H K : Subgroup G} (hK : K ≤ H) (hH : H ≤ B)
    (hKH : IsNormalIn K H) :
    ((K.subgroupOf B).subgroupOf (H.subgroupOf B)).Normal := by
  exact (Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono B hK)).mpr (by
    intro x hx y hy
    have hxK : (x : G) ∈ K := (@Subgroup.mem_subgroupOf G _ K B x).mp y
    have hyH : (hx : G) ∈ H := (@Subgroup.mem_subgroupOf G _ H B hx).mp hy
    rw [Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hKH.2 (hx : G) hyH (x : G) hxK)

/-- A two-step normal chain `K ⊴ H ⊴ B` makes `K` subnormal in `B`. -/
private lemma isSubnormal_of_normal_chain
    {G : Type u} [Group G]
    {B H K : Subgroup G} (hK : K ≤ H) (hH : H ≤ B)
    (hKH : IsNormalIn K H) (hHB : IsNormalIn H B) :
    (K.subgroupOf B).IsSubnormal := by
  refine Subgroup.IsSubnormal.step (K.subgroupOf B) (H.subgroupOf B) ?_ ?_ ?_
  · exact Subgroup.subgroupOf_mono B hK
  · have hHsub : (H.subgroupOf B).IsSubnormal := by
      refine Subgroup.IsSubnormal.step (H.subgroupOf B) (B.subgroupOf B) ?_ ?_ ?_
      · exact Subgroup.subgroupOf_mono B hH
      · simpa [Subgroup.subgroupOf_self] using
          (Subgroup.IsSubnormal.top : (⊤ : Subgroup (↥B)).IsSubnormal)
      · exact isNormal_subgroupOf_of_isNormalIn hH le_rfl hHB
    exact hHsub
  · exact isNormal_subgroupOf_of_isNormalIn hK hH hKH

/-- A subnormal `p`-subgroup of `B` lies in `O_p(B)`. -/
private lemma le_qCoreOf_of_isSubnormal_isPGroup
    {G : Type u} [Group G] [Finite G]
    (B S : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hSB : S ≤ B) (hS : (S.subgroupOf B).IsSubnormal) (hSp : IsPGroup p S) :
    S ≤ qCoreOf B p := by
  rcases (Subgroup.IsSubnormal.isSubnormal_iff (G := ↥B) (H := S.subgroupOf B)).1 hS with
    ⟨n, f, hmono, hnorm, hf0, hfn⟩
  have hmain : ∀ i : ℕ, i ≤ n → S ≤ qCoreOf ((f i).map B.subtype) p := by
    intro i hi
    induction i with
    | zero =>
      have hK0 : (f 0).map B.subtype = S := by
        rw [hf0]
        exact Subgroup.map_subgroupOf_eq_of_le hSB
      have hSleK : S ≤ (f 0).map B.subtype := by rw [hK0]
      have hSnorm : IsNormalIn S ((f 0).map B.subtype) := by
        rw [hK0]
        refine ⟨le_rfl, ?_⟩
        intro a ha x hx
        exact S.mul_mem (S.mul_mem ha hx) (S.inv_mem ha)
      exact le_qCoreOf_of_normal_isPGroup ((f 0).map B.subtype) S p hSleK (by
        rw [Subgroup.normal_subgroupOf_iff_le_normalizer hSleK]
        exact le_normalizer_of_isNormalIn hSnorm) hSp
    | succ i ih =>
      have hKi : IsNormalIn ((f i).map B.subtype) ((f (i + 1)).map B.subtype) := by
        refine ⟨Subgroup.map_mono (f := B.subtype) (hmono (Nat.le_succ i)), ?_⟩
        intro b hb x hx
        rcases (Subgroup.mem_map).1 hx with ⟨x0, hx0, rfl⟩
        rcases (Subgroup.mem_map).1 hb with ⟨b0, hb0, rfl⟩
        have hconj : b0 * x0 * b0⁻¹ ∈ f i :=
          (Subgroup.normal_subgroupOf_iff (hmono (Nat.le_succ i))).mp (hnorm i)
            x0 b0 hx0 hb0
        exact Subgroup.mem_map.mpr ⟨b0 * x0 * b0⁻¹, hconj, by simp [mul_assoc]⟩
      exact (ih (Nat.le_of_succ_le hi)).trans
        (le_qCoreOf_of_isNormalIn_chain ((f i).map B.subtype) ((f (i + 1)).map B.subtype)
          p hp (qCoreOf_normal_in ((f i).map B.subtype) p) hKi
          (qCoreOf_isPGroup ((f i).map B.subtype) p))
  have hKn : (f n).map B.subtype = B := by
    rw [hfn]
    ext x
    simp
  exact (hmain n (le_rfl : n ≤ n)).trans (le_of_eq (by rw [hKn]))

/-- From `Y_2 ≤ A ∩ B`, the subnormal chain gives `O_p(A) ≤ O_p(B)`
(KS 10.1.4, step after claim `(′′)`). -/
private lemma qCoreOf_le_qCoreOf_of_double_commutator_le
    {G : Type u} [Group G] [Finite G]
    (A B : Subgroup G) (p : ℕ) (hp : p.Prime)
    (hPB : qCoreOf A p ≤ B)
    (hY : ⁅⁅B, qCoreOf A p⁆, qCoreOf A p⁆ ≤ A ⊓ B) :
    qCoreOf A p ≤ qCoreOf B p := by
  set P : Subgroup G := qCoreOf A p with hP
  set X : Subgroup G := ⁅B, P⁆ with hX
  set Y : Subgroup G := ⁅X, P⁆ with hYdef
  set H : Subgroup G := P ⊔ Y with hH
  set M : Subgroup G := P ⊔ X with hM
  have hXB : X ≤ B := by
    rw [hX]
    exact (Subgroup.commutator_le_sup B P).trans (sup_le (le_rfl : B ≤ B) hPB)
  have hYB : Y ≤ B := by
    rw [hYdef]
    exact (Subgroup.commutator_le_sup X P).trans (sup_le hXB hPB)
  have hYleA : Y ≤ A := by
    rw [hYdef, hX, hP]
    exact hY.trans inf_le_left
  have hHleA : H ≤ A := by
    rw [hH]
    exact sup_le (by rw [hP]; exact qCoreOf_le A p) hYleA
  have hMleB : M ≤ B := by
    rw [hM]
    exact sup_le hPB hXB
  have hPH : IsNormalIn P H := by
    refine ⟨by rw [hH]; exact le_sup_left, ?_⟩
    intro h hh p0 hp0
    have hhA : h ∈ A := hHleA hh
    have hp0P : p0 ∈ qCoreOf A p := hP ▸ hp0
    exact (qCoreOf_normal_in A p).2 h hhA p0 hp0P
  have hHX : ⁅H, X⁆ ≤ Y := by
    rw [hH]
    apply commutator_sup_le_of_commutator_le_and_normalize
      (A := P) (B := Y) (C := X) (D := Y)
    · rw [Subgroup.commutator_le]
      intro p hp x hx
      have hmem : ⁅x, p⁆ ∈ ⁅X, P⁆ := Subgroup.commutator_mem_commutator hx hp
      rw [hYdef]
      simpa [commutatorElement_inv] using (⁅X, P⁆).inv_mem hmem
    · exact (Subgroup.le_normalizer_iff_commutator_le_left (H := X) (K := Y)).1
        (Subgroup.normalizer_commutator_ge_left (H₁ := X) (H₂ := P))
    · exact Subgroup.normalizer_commutator_ge_right (H₁ := X) (H₂ := P)
    · exact (Subgroup.le_normalizer_iff).2 (by
        intro y hy z hz
        exact Y.mul_mem (Y.mul_mem hy hz) (Y.inv_mem hy))
  have hXleNH : X ≤ Subgroup.normalizer (H : Set G) := by
    have hXY : ⁅X, H⁆ ≤ Y :=
      (le_of_eq (Subgroup.commutator_comm (H₁ := X) (H₂ := H))).trans hHX
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hxh : ⁅x, h⁆ ∈ Y := hXY (Subgroup.commutator_mem_commutator hx hh)
      have hprod : x * h * x⁻¹ = ⁅x, h⁆ * h := by
        rw [commutatorElement_def]
        group
      rw [hprod]
      change ⁅x, h⁆ * h ∈ P ⊔ Y
      exact (P ⊔ Y).mul_mem (Subgroup.mem_sup_right (S := P) (T := Y) hxh) hh
    · intro h'
      have hxinv : x⁻¹ ∈ X := X.inv_mem hx
      have h1 : ⁅x⁻¹, x * h * x⁻¹⁆ ∈ Y := hXY
        (Subgroup.commutator_mem_commutator hxinv h')
      have hprod : x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ = ⁅x⁻¹, x * h * x⁻¹⁆ * (x * h * x⁻¹) := by
        rw [commutatorElement_def]
        group
      have hh : x⁻¹ * (x * h * x⁻¹) * (x⁻¹)⁻¹ ∈ H := by
        rw [hprod]
        change ⁅x⁻¹, x * h * x⁻¹⁆ * (x * h * x⁻¹) ∈ P ⊔ Y
        exact (P ⊔ Y).mul_mem (Subgroup.mem_sup_right (S := P) (T := Y) h1) h'
      simpa [mul_assoc] using hh
  have hHM : IsNormalIn H M := by
    refine ⟨?_, ?_⟩
    · rw [hH, hM]
      exact sup_le le_sup_left
        ((Subgroup.commutator_le_sup X P).trans
          (sup_le (le_sup_right : X ≤ P ⊔ X) (le_sup_left : P ≤ P ⊔ X)))
    · have hPleN : P ≤ Subgroup.normalizer ((P ⊔ Y : Subgroup G) : Set G) := by
        exact (le_sup_left : P ≤ P ⊔ Y).trans ((Subgroup.le_normalizer_iff).2 (by
          intro y hy z hz
          exact (P ⊔ Y).mul_mem ((P ⊔ Y).mul_mem hy hz) ((P ⊔ Y).inv_mem hy)))
      rw [hH, hM]
      exact (Subgroup.le_normalizer_iff.mp (sup_le hPleN hXleNH))
  have hBX : ⁅M, B⁆ ≤ X := by
    rw [hM]
    apply commutator_sup_le_of_commutator_le_and_normalize
      (A := P) (B := X) (C := B) (D := X)
    · rw [Subgroup.commutator_le]
      intro p hp b hb
      have hmem : ⁅b, p⁆ ∈ ⁅B, P⁆ := Subgroup.commutator_mem_commutator hb hp
      rw [hX]
      simpa [commutatorElement_inv] using (⁅B, P⁆).inv_mem hmem
    · exact (Subgroup.le_normalizer_iff_commutator_le_left (H := B) (K := X)).1
        (Subgroup.normalizer_commutator_ge_left (H₁ := B) (H₂ := P))
    · exact Subgroup.normalizer_commutator_ge_right (H₁ := B) (H₂ := P)
    · exact (Subgroup.le_normalizer_iff).2 (by
        intro y hy z hz
        exact X.mul_mem (X.mul_mem hy hz) (X.inv_mem hy))
  have hMB : IsNormalIn M B := by
    refine ⟨?_, ?_⟩
    · rw [hM]
      exact sup_le hPB hXB
    · have hBleNM : B ≤ Subgroup.normalizer ((P ⊔ X : Subgroup G) : Set G) := by
        have hBX' : ⁅B, P ⊔ X⁆ ≤ X :=
          (le_of_eq (Subgroup.commutator_comm (H₁ := B) (H₂ := P ⊔ X))).trans hBX
        intro b hb
        rw [Subgroup.mem_normalizer_iff]
        intro m
        constructor
        · intro hm
          have hbm : ⁅b, m⁆ ∈ X := hBX' (Subgroup.commutator_mem_commutator hb hm)
          have hprod : b * m * b⁻¹ = ⁅b, m⁆ * m := by
            rw [commutatorElement_def]
            group
          rw [hprod]
          exact (P ⊔ X).mul_mem (Subgroup.mem_sup_right (S := P) (T := X) hbm) hm
        · intro h'
          have hbInv : b⁻¹ ∈ B := B.inv_mem hb
          have h1 : ⁅b⁻¹, b * m * b⁻¹⁆ ∈ X := hBX'
            (Subgroup.commutator_mem_commutator hbInv h')
          have hprod : b⁻¹ * (b * m * b⁻¹) * (b⁻¹)⁻¹ = ⁅b⁻¹, b * m * b⁻¹⁆ * (b * m * b⁻¹) := by
            rw [commutatorElement_def]
            group
          have hh : b⁻¹ * (b * m * b⁻¹) * (b⁻¹)⁻¹ ∈ P ⊔ X := by
            rw [hprod]
            exact (P ⊔ X).mul_mem (Subgroup.mem_sup_right (S := P) (T := X) h1) h'
          simpa [mul_assoc] using hh
      rw [hM]
      intro b hb m hm
      exact (Subgroup.mem_normalizer_iff.mp (hBleNM hb) m).1 hm
  have hHleB : H ≤ B := by
    rw [hH]
    exact sup_le hPB hYB
  have hHsub : (H.subgroupOf B).IsSubnormal :=
    isSubnormal_of_normal_chain (K := H) (H := M) (B := B)
      hHM.1 hMleB hHM hMB
  have hPsub : (P.subgroupOf B).IsSubnormal := by
    refine Subgroup.IsSubnormal.step (P.subgroupOf B) (H.subgroupOf B) ?_ hHsub ?_
    · exact Subgroup.subgroupOf_mono B (le_sup_left : P ≤ P ⊔ Y)
    · exact isNormal_subgroupOf_of_isNormalIn
        (le_sup_left : P ≤ P ⊔ Y) hHleB hPH
  exact le_qCoreOf_of_isSubnormal_isPGroup B P p hp (by rwa [hP]) hPsub
    (by simpa [hP] using (qCoreOf_isPGroup A p))

/-- Bender (1970), Statement 1.6: if `A` and `B` are distinct maximal
subgroups of a simple group `G` with `F*(A) ≤ B` and `F*(B) ≤ A`, then
`F*(A)` and `F*(B)` are `p`-groups for one common prime `p`.

The assembly is the KS 10.1.4 route implemented by the helpers above:
both layers are trivial, so `F*(A) = F(A)` and `F*(B) = F(B)`; if two
distinct primes divided `|F(A)|`, the double-commutator chain would give
`O_p(A) = O_p(B)`, a nontrivial subgroup normalized by both maximal
subgroups, contradicting simplicity.  Hence `π(F(A))` is empty or a
singleton; in the singleton case every `O_q` with `q ≠ p` vanishes, so
both Fitting subgroups lie in the corresponding `O_p` and are `p`-groups. -/
public theorem bender1970_1_6_maximalSubgroups_pGroups
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A B : Subgroup G)
    (hA : IsCoatom A) (hB : IsCoatom B) (hne : A ≠ B)
    (hFAB : generalizedFittingSubgroupOf A ≤ B)
    (hFBA : generalizedFittingSubgroupOf B ≤ A) :
    ∃ p : ℕ, p.Prime ∧
      IsPGroup p (generalizedFittingSubgroupOf A) ∧
        IsPGroup p (generalizedFittingSubgroupOf B) := by
  have hEA : componentLayerOf A = ⊥ :=
    componentLayerOf_eq_bot_of_pair hsimple A B hA hB hne hFAB hFBA
  have hEB : componentLayerOf B = ⊥ :=
    componentLayerOf_eq_bot_of_pair hsimple B A hB hA hne.symm hFBA hFAB
  have hFstA : generalizedFittingSubgroupOf A = fittingSubgroupOf A := by
    rw [generalizedFittingSubgroupOf, hEA]
    simp
  have hFstB : generalizedFittingSubgroupOf B = fittingSubgroupOf B := by
    rw [generalizedFittingSubgroupOf, hEB]
    simp
  let S : Set ℕ := primesOfOrder (fittingSubgroupOf A)
  have hsing : ∀ ⦃r s : ℕ⦄, r ∈ S → s ∈ S → r = s := by
    intro r s hr hs
    by_contra hpq
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
    have hsp : s.Prime := Nat.prime_of_mem_primeFactors hs
    have hPB : qCoreOf A r ≤ B :=
      (qCoreOf_le_fittingSubgroupOf_local A r hrp).trans
        ((le_sup_left : fittingSubgroupOf A ≤ generalizedFittingSubgroupOf A).trans hFAB)
    have hYAB : ⁅⁅B, qCoreOf A r⁆, qCoreOf A r⁆ ≤ A ⊓ B :=
      commutator_double_le_intersection hsimple A B hA hB hne hFAB hFBA
        hrp hsp hpq hr hs
    have hPrB : qCoreOf A r ≤ qCoreOf B r :=
      qCoreOf_le_qCoreOf_of_double_commutator_le A B r hrp hPB hYAB
    have hrB : r ∈ primesOfOrder (fittingSubgroupOf B) :=
      mem_primesOfOrder_fittingB_of_mem_primesOfOrder_fittingA
        hsimple A B hA hB hne hFAB hFBA hrp hr
    have hsB : s ∈ primesOfOrder (fittingSubgroupOf B) :=
      mem_primesOfOrder_fittingB_of_mem_primesOfOrder_fittingA
        hsimple A B hA hB hne hFAB hFBA hsp hs
    have hPA : qCoreOf B r ≤ A :=
      (qCoreOf_le_fittingSubgroupOf_local B r hrp).trans
        ((le_sup_left : fittingSubgroupOf B ≤ generalizedFittingSubgroupOf B).trans hFBA)
    have hYBA : ⁅⁅A, qCoreOf B r⁆, qCoreOf B r⁆ ≤ B ⊓ A :=
      commutator_double_le_intersection hsimple B A hB hA hne.symm hFBA hFAB
        hrp hsp hpq hrB hsB
    have hBrA : qCoreOf B r ≤ qCoreOf A r :=
      qCoreOf_le_qCoreOf_of_double_commutator_le B A r hrp hPA hYBA
    let P : Subgroup G := qCoreOf A r
    have hPeq : P = qCoreOf B r := by
      dsimp [P]
      exact le_antisymm hPrB hBrA
    have hPne : P ≠ ⊥ := by
      simpa [P] using (qCoreOf_ne_bot_of_mem_primesOfOrder A hrp hr)
    have hPleA : P ≤ A := by
      simpa [P] using (qCoreOf_normal_in A r).1
    have hAleN : A ≤ Subgroup.normalizer (P : Set G) := by
      simpa [P] using le_normalizer_of_isNormalIn (qCoreOf_normal_in A r)
    have hBleN : B ≤ Subgroup.normalizer (P : Set G) := by
      have hPnormB : IsNormalIn P B := by
        rw [hPeq]
        exact qCoreOf_normal_in B r
      exact le_normalizer_of_isNormalIn hPnormB
    let NG : Subgroup G := Subgroup.normalizer (P : Set G)
    have hNGne_top : NG ≠ ⊤ := by
      intro htop
      have hPnormG : P.Normal := by
        rw [Subgroup.normalizer_eq_top_iff] at htop
        exact htop
      rcases (haveI := hPnormG; hsimple.eq_bot_or_eq_top_of_normal P) with hbot | htopP
      · exact hPne hbot
      · have hAtop : A = ⊤ := by
          have hTopLeA : (⊤ : Subgroup G) ≤ A := by
            intro x hx
            exact hPleA (htopP ▸ hx)
          exact le_antisymm le_top hTopLeA
        exact hA.1 hAtop
    have hNGA : NG ≤ A := by
      by_cases hEq : A = NG
      · rw [hEq]
      · have hlt : A < NG := lt_of_le_of_ne hAleN (fun h => hEq h)
        have htop := hA.2 NG hlt
        exact False.elim (hNGne_top htop)
    have hNGB : NG ≤ B := by
      by_cases hEq : B = NG
      · rw [hEq]
      · have hlt : B < NG := lt_of_le_of_ne hBleN (fun h => hEq h)
        have htop := hB.2 NG hlt
        exact False.elim (hNGne_top htop)
    have hAeqNG : A = NG := le_antisymm hAleN hNGA
    have hBeqNG : B = NG := le_antisymm hBleN hNGB
    exact hne (hAeqNG.trans hBeqNG.symm)
  by_cases hSempty : S = ∅
  · obtain ⟨p, hp, _⟩ := Nat.exists_prime_and_dvd (by norm_num : 3 ≠ 1)
    have hFA : fittingSubgroupOf A = ⊥ := by
      by_contra hFne
      have hFnt : Nontrivial (↥(fittingSubgroupOf A)) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hFne
      let : Fintype (↥(fittingSubgroupOf A)) := Fintype.ofFinite _
      have hcard : Nat.card (↥(fittingSubgroupOf A)) ≠ 1 := by
        have hc : Fintype.card (↥(fittingSubgroupOf A)) ≠ 1 :=
          ne_of_gt (Fintype.one_lt_card_iff_nontrivial.2 hFnt)
        simpa [Nat.card_eq_fintype_card] using hc
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard
      have hqS : q ∈ S :=
        Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
      rw [hSempty] at hqS
      exact hqS.elim
    have hFB : fittingSubgroupOf B = ⊥ := by
      by_contra hFne
      have hFnt : Nontrivial (↥(fittingSubgroupOf B)) :=
        (Subgroup.nontrivial_iff_ne_bot _).2 hFne
      let : Fintype (↥(fittingSubgroupOf B)) := Fintype.ofFinite _
      have hcard : Nat.card (↥(fittingSubgroupOf B)) ≠ 1 := by
        have hc : Fintype.card (↥(fittingSubgroupOf B)) ≠ 1 :=
          ne_of_gt (Fintype.one_lt_card_iff_nontrivial.2 hFnt)
        simpa [Nat.card_eq_fintype_card] using hc
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hcard
      have hqB : q ∈ primesOfOrder (fittingSubgroupOf B) :=
        Nat.mem_primeFactors.mpr ⟨hq, hqdvd, Nat.card_pos.ne'⟩
      have hqA : q ∈ S :=
        mem_primesOfOrder_fittingA_of_mem_primesOfOrder_fittingB
          hsimple A B hA hB hne hFAB hFBA hq hqB
      rw [hSempty] at hqA
      exact hqA.elim
    refine ⟨p, hp, ?_, ?_⟩
    · rw [hFstA, hFA]
      exact IsPGroup.of_bot
    · rw [hFstB, hFB]
      exact IsPGroup.of_bot
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hSempty
    rcases hSne with ⟨p, hpS⟩
    have hp : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpB : p ∈ primesOfOrder (fittingSubgroupOf B) :=
      mem_primesOfOrder_fittingB_of_mem_primesOfOrder_fittingA
        hsimple A B hA hB hne hFAB hFBA hp hpS
    have hFpA : IsPGroup p (fittingSubgroupOf A) := by
      have hFleOp : fittingSubgroupOf A ≤ qCoreOf A p := by
        rw [fittingSubgroupOf_eq_iSup_qCoreOf_prime A]
        exact iSup_le (fun r => by
          by_cases hrp : r.1 = p
          · rw [hrp]
          · have hQbot : qCoreOf A r.1 = ⊥ := by
              by_contra hQ
              have hrS : r.1 ∈ S := mem_primesOfOrder_of_qCoreOf_ne_bot A r.2 hQ
              exact hrp (hsing hrS hpS)
            simpa [hQbot] using (bot_le : (⊥ : Subgroup G) ≤ qCoreOf A p))
      exact IsPGroup.to_le (qCoreOf_isPGroup A p) hFleOp
    have hFpB : IsPGroup p (fittingSubgroupOf B) := by
      have hFleOp : fittingSubgroupOf B ≤ qCoreOf B p := by
        rw [fittingSubgroupOf_eq_iSup_qCoreOf_prime B]
        exact iSup_le (fun r => by
          by_cases hrp : r.1 = p
          · rw [hrp]
          · have hQbot : qCoreOf B r.1 = ⊥ := by
              by_contra hQ
              have hrS : r.1 ∈ S :=
                mem_primesOfOrder_fittingA_of_mem_primesOfOrder_fittingB
                  hsimple A B hA hB hne hFAB hFBA r.2
                    (mem_primesOfOrder_of_qCoreOf_ne_bot B r.2 hQ)
              exact hrp (hsing hrS hpS)
            simpa [hQbot] using (bot_le : (⊥ : Subgroup G) ≤ qCoreOf B p))
      exact IsPGroup.to_le (qCoreOf_isPGroup B p) hFleOp
    refine ⟨p, hp, ?_, ?_⟩
    · rw [hFstA]
      exact hFpA
    · rw [hFstB]
      exact hFpB

end CFSG.GorensteinWalter
