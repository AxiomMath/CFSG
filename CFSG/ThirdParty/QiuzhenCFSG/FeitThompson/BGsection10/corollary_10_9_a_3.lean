module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.corollary_10_9_a_2
import Mathlib.GroupTheory.Schreier
import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Statements from BG Section 10

This file records a statement-only scaffold for Section 10 of
`Local Analysis for the Odd Order Theorem`.

The local PDF extraction mangles the Greek letters used in the book. This
module imports the shared Section 10 notation from `FeitThompson.BGsection10.Defs`.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] in
public theorem CFSG.section10_ambient_sylow_le_base
    {S : Subgroup G} {p : Nat.Primes} (P : Sylow p.val S) :
    section10AmbientSylowSubgroup S P ≤ S := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
  exact y.property

private theorem CFSG.section10_lemma_6_5_ambient_normalizer_endpoint
    {M X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (hpβ : p ∉ section10BetaPrimes M)
    {P : Sylow p.val (ambientDerivedSubgroup M)}
    (hKU :
      section10MbetaSubgroup M ⊔
          (subgroupNormalizerIn M (X : Set G)).subgroupOf M =
        ⊤)
    (hPU :
      section10AmbientSylowSubgroup (ambientDerivedSubgroup M) P ≤
        subgroupNormalizerIn M (X : Set G)) :
    section10AmbientSylowSubgroup (ambientDerivedSubgroup M) P ≤
      ambientDerivedSubgroup (subgroupNormalizerIn M (X : Set G)) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let PG : Subgroup G := section10AmbientSylowSubgroup Dg P
  let U : Subgroup G := subgroupNormalizerIn M (X : Set G)
  have hDg_le_M : Dg ≤ M := by
    intro x hx
    change x ∈ ambientDerivedSubgroup M at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hPG_le_M : PG ≤ M :=
    (section10_ambient_sylow_le_base (G := G) P).trans hDg_le_M
  let H : Subgroup M := PG.subgroupOf M
  let K : Subgroup M := section10MbetaSubgroup M
  let UM : Subgroup M := U.subgroupOf M
  let D : Subgroup M := derivedSubgroup M
  have hH_le_D : H ≤ D := by
    intro x hx
    have hxDg : (x : G) ∈ Dg :=
      section10_ambient_sylow_le_base (G := G) P hx
    change (x : G) ∈ ambientDerivedSubgroup M at hxDg
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
    rcases hxDg with ⟨y, hyD, hyx⟩
    have hyxM : y = x := Subtype.ext hyx
    simpa [D, hyxM] using hyD
  have hH_le_UM : H ≤ UM := by
    intro x hx
    exact hPU hx
  have hPGp : IsPGroup p.val PG := by
    change IsPGroup p.val
      ((P : Subgroup (ambientDerivedSubgroup M)).map (ambientDerivedSubgroup M).subtype)
    exact IsPGroup.map (p := p.val) (H := (P : Subgroup (ambientDerivedSubgroup M)))
      P.isPGroup' (ambientDerivedSubgroup M).subtype
  have hHp : IsPGroup p.val H := by
    exact hPGp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := PG) (K := M) hPG_le_M).symm
  have hKpi : IsPiSubgroup (G := M) ({p} : Set Nat.Primes)ᶜ K := by
    intro r hr_dvd
    rw [Set.mem_compl_iff]
    intro hrp
    have hrβ : r ∈ section10BetaPrimes M :=
      (section10_mbetaSubgroup_isHall hM).p_in_pi_of_p_dvd_card r hr_dvd
    have hr_eq : r = p := Set.mem_singleton_iff.mp hrp
    exact hpβ (by simpa [hr_eq] using hrβ)
  have hcopHK : Nat.Coprime (Nat.card H) (Nat.card K) := by
    exact section8_coprime_card_of_isPGroup_of_isPiSubgroup_compl
      (G := M) (π := ({p} : Set Nat.Primes)) (r := p)
      (R := H) (Y := K) (by simp) hHp hKpi
  have : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have hHU_eq :
      H ⊓ D = H ⊓ ⁅UM, UM⁆ := by
    simpa [K, UM, D, H] using
      lemma_6_5_a (G := M) (K := K) (U := UM) (H := H)
        hKU hH_le_UM hcopHK
  have hUleM : U ≤ M := by
    simpa [U] using section10_subgroupNormalizerIn_le M (X : Set G)
  have hUMmap : UM.map M.subtype = U := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUleM hx⟩, hx, rfl⟩
  have hcomm_map : (⁅UM, UM⁆).map M.subtype = ⁅U, U⁆ := by
    calc
      (⁅UM, UM⁆).map M.subtype =
          ⁅UM.map M.subtype, UM.map M.subtype⁆ := by
        simpa using (Subgroup.map_commutator (H₁ := UM) (H₂ := UM) M.subtype)
      _ = ⁅U, U⁆ := by rw [hUMmap]
  intro x hxPG
  let xM : M := ⟨x, hPG_le_M hxPG⟩
  have hxH : xM ∈ H := hxPG
  have hxD : xM ∈ D := hH_le_D hxH
  have hx_comm_M : xM ∈ ⁅UM, UM⁆ := by
    have hx_inf : xM ∈ H ⊓ D := ⟨hxH, hxD⟩
    have hx_inf' : xM ∈ H ⊓ ⁅UM, UM⁆ := by
      simpa [hHU_eq] using hx_inf
    exact hx_inf'.2
  have hx_comm_G : x ∈ ⁅U, U⁆ := by
    have hx_map : x ∈ (⁅UM, UM⁆).map M.subtype :=
      ⟨xM, hx_comm_M, rfl⟩
    simpa [hcomm_map] using hx_map
  have hx_map_comm : x ∈ (_root_.commutator U).map U.subtype := by
    simpa [Subgroup.map_subtype_commutator] using hx_comm_G
  change x ∈ (_root_.commutator U).map U.subtype
  exact hx_map_comm

omit [Finite G] in
private theorem CFSG.section10_local_normalizer_le_subgroupNormalizerIn
    {M X : Subgroup G} (hXleM : X ≤ M) :
    Subgroup.normalizer (((X.subgroupOf M) : Subgroup M) : Set M) ≤
      (subgroupNormalizerIn M (X : Set G)).subgroupOf M := by
  classical
  let XM : Subgroup M := X.subgroupOf M
  let U : Subgroup G := subgroupNormalizerIn M (X : Set G)
  let UM : Subgroup M := U.subgroupOf M
  intro x hx
  change (x : G) ∈ U
  change (x : G) ∈ subgroupNormalizerIn M (X : Set G)
  rw [section10_mem_subgroupNormalizerIn]
  constructor
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyX
      have hyM : y ∈ M := hXleM hyX
      let yM : M := ⟨y, hyM⟩
      have hyXM : yM ∈ XM := hyX
      have hconjM :
          ((x : M) * yM * (x : M)⁻¹ : M) ∈ XM :=
        (Subgroup.mem_normalizer_iff.mp hx yM).1 hyXM
      simpa [yM, XM, Subgroup.mem_subgroupOf, mul_assoc] using hconjM
    · intro hconjX
      have hyM : y ∈ M := by
        have hxM : (x : G) ∈ M := x.property
        have hconjM : (x : G) * y * (x : G)⁻¹ ∈ M := hXleM hconjX
        have hy_eq : y = (x : G)⁻¹ * ((x : G) * y * (x : G)⁻¹) * (x : G) := by
          simp [mul_assoc]
        rw [hy_eq]
        exact M.mul_mem (M.mul_mem (M.inv_mem hxM) hconjM) hxM
      let yM : M := ⟨y, hyM⟩
      have hconjXM :
          ((x : M) * yM * (x : M)⁻¹ : M) ∈ XM := by
        simpa [yM, XM, Subgroup.mem_subgroupOf, mul_assoc] using hconjX
      exact (Subgroup.mem_normalizer_iff.mp hx yM).2 hconjXM
  · exact x.property

omit [IsMinCE G] in
private theorem CFSG.section10_mbeta_sup_normalizer_of_frattini_join
    {M X : Subgroup G} {q : Nat.Primes} (hXleM : X ≤ M)
    {J : Subgroup M} [J.Normal]
    (hJ_eq : J = section10MbetaSubgroup M ⊔ X.subgroupOf M)
    (P : Sylow q.val J)
    (hPmap : (P : Subgroup J).map J.subtype = X.subgroupOf M) :
    section10MbetaSubgroup M ⊔
        (subgroupNormalizerIn M (X : Set G)).subgroupOf M =
      ⊤ := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let XM : Subgroup M := X.subgroupOf M
  let K : Subgroup M := section10MbetaSubgroup M
  let U : Subgroup G := subgroupNormalizerIn M (X : Set G)
  let UM : Subgroup M := U.subgroupOf M
  have hFr :
      Subgroup.normalizer ((XM : Subgroup M) : Set M) ⊔ J = ⊤ := by
    have h := Sylow.normalizer_sup_eq_top (G := M) (N := J) P
    simpa [XM, hPmap] using h
  have hXM_le_UM : XM ≤ UM := by
    intro x hx
    change (x : G) ∈ U
    exact section10_le_subgroupNormalizerIn hXleM hx
  have hnorm_le_UM :
      Subgroup.normalizer ((XM : Subgroup M) : Set M) ≤ UM := by
    simpa [XM, U, UM] using section10_local_normalizer_le_subgroupNormalizerIn
      (G := G) hXleM
  refine eq_top_iff.2 ?_
  rw [← hFr, hJ_eq]
  exact sup_le
    (hnorm_le_UM.trans le_sup_right)
    (sup_le le_sup_left (hXM_le_UM.trans le_sup_right))

private theorem CFSG.section10_exists_ambient_derived_sylow_le_normalizer_of_le_derived
    {M X : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hpβ : p ∉ section10BetaPrimes M) (hqβ : q ∉ section10BetaPrimes M)
    (hpq : p ≠ q) (hXleM : X ≤ M) (hXq : IsPGroup q.val X)
    (hXD : X ≤ ambientDerivedSubgroup M) :
    ∃ P : Sylow p.val (ambientDerivedSubgroup M),
      section10AmbientSylowSubgroup (ambientDerivedSubgroup M) P ≤
        subgroupNormalizerIn M (X : Set G) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let D : Subgroup M := derivedSubgroup M
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let XM : Subgroup M := X.subgroupOf M
  have hXMD : XM ≤ D := by
    intro x hx
    have hxG : ((x : M) : G) ∈ ambientDerivedSubgroup M := hXD hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxG
    rcases hxG with ⟨y, hyD, hyx⟩
    change x ∈ D
    have hyxM : y = x := Subtype.ext hyx
    simpa [D, hyxM] using hyD
  have hXMq : IsPGroup q.val XM := by
    exact hXq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := X) (K := M) hXleM).symm
  let XsubD : Subgroup D := XM.subgroupOf D
  have hXsubDq : IsPGroup q.val XsubD := by
    exact hXMq.of_equiv (Subgroup.subgroupOfEquivOfLe (H := XM) (K := D) hXMD).symm
  have hXsubDπ : IsPiSubgroup (G := D) (section10BetaPrimes M)ᶜ XsubD :=
    section10_isPiSubgroup_compl_of_isPGroup_not_mem
      (π := section10BetaPrimes M) hqβ hXsubDq
  have hMsolv : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have : Group.IsSolvable M := hMsolv
  have hDsolv : Group.IsSolvable D := by infer_instance
  obtain ⟨L, hLD, hXML, hLHallD, hLnil⟩ :=
    section10_exists_nilpotent_hall_containing
      (H := M) (π := (section10BetaPrimes M)ᶜ) (K := D) (X := XM)
      hDsolv (lemma_10_8_b (G := G) hM).1 hXMD hXsubDπ
  let LsubD : Subgroup D := L.subgroupOf D
  have hLsubDnil : Group.IsNilpotent LsubD := by
    let e : L ≃* LsubD := (Subgroup.subgroupOfEquivOfLe hLD).symm
    let : Group.IsNilpotent L := hLnil
    exact Group.nilpotent_of_mulEquiv (G := L) (G' := LsubD) e
  have hXsubD_le_LsubD : XsubD ≤ LsubD := by
    intro x hx
    exact hXML hx
  let Xloc : Subgroup LsubD := XsubD.subgroupOf LsubD
  have hXlocq : IsPGroup q.val Xloc := by
    exact hXsubDq.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := XsubD) (K := LsubD) hXsubD_le_LsubD).symm
  have hpβc : p ∈ (section10BetaPrimes M)ᶜ := by
    simpa using hpβ
  obtain ⟨PD, hPDcent⟩ :=
    section10_exists_sylow_centralized_of_local_nilpotent_hall_pair
      (G := M) (S := D) (π := (section10BetaPrimes M)ᶜ) (p := p) (q := q)
      (L := LsubD) (X := Xloc) hpq hpβc hLHallD hLsubDnil hXlocq
  have hXloc_map_eq :
      ((Xloc.map LsubD.subtype).map D.subtype : Subgroup M) = XM := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨xD, hxD, rfl⟩
      rcases Subgroup.mem_map.mp hxD with ⟨xL, hxL, rfl⟩
      exact hxL
    · intro hx
      have hxD : x ∈ D := hXMD hx
      let xD : D := ⟨x, hxD⟩
      have hxXsubD : xD ∈ XsubD := hx
      have hxLsubD : xD ∈ LsubD := hXsubD_le_LsubD hxXsubD
      let xL : LsubD := ⟨xD, hxLsubD⟩
      have hxXloc : xL ∈ Xloc := hxXsubD
      exact ⟨xD, ⟨xL, hxXloc, rfl⟩, rfl⟩
  let e : D ≃* Dg := by
    change D ≃* D.map M.subtype
    exact Subgroup.equivMapOfInjective D M.subtype M.subtype_injective
  let P : Sylow p.val Dg := PD.mapSurjective (f := e.toMonoidHom) e.surjective
  refine ⟨P, ?_⟩
  intro y hy
  rw [section10AmbientSylowSubgroup] at hy
  rcases Subgroup.mem_map.mp hy with ⟨yDg, hyP, rfl⟩
  have hyP' : yDg ∈ (PD : Subgroup D).map e.toMonoidHom := by
    simpa [P] using hyP
  rcases Subgroup.mem_map.mp hyP' with ⟨yD, hyPD, hyD_eq⟩
  have hy_val : (yDg : G) = (((yD : D) : M) : G) := by
    calc
      (yDg : G) = (e yD : G) := by
        exact congrArg Subtype.val hyD_eq.symm
      _ = (((yD : D) : M) : G) := by
        unfold e
        exact Subgroup.coe_equivMapOfInjective_apply
          D M.subtype M.subtype_injective yD
  have hyLocal : ((yD : D) : M) ∈ section10AmbientSylowSubgroup D PD :=
    ⟨yD, hyPD, rfl⟩
  have hyCentXM : ((yD : D) : M) ∈ Subgroup.centralizer (XM : Set M) := by
    simpa [hXloc_map_eq] using hPDcent hyLocal
  have hyNormXM :
      ((yD : D) : M) ∈ Subgroup.normalizer (XM : Set M) :=
    centralizer_le_normalizer XM hyCentXM
  have hyUM :
      ((yD : D) : M) ∈ (subgroupNormalizerIn M (X : Set G)).subgroupOf M :=
    section10_local_normalizer_le_subgroupNormalizerIn (G := G) hXleM hyNormXM
  change (yDg : G) ∈ subgroupNormalizerIn M (X : Set G)
  simpa [hy_val, Subgroup.mem_subgroupOf] using hyUM

omit [IsMinCE G] in
private theorem CFSG.section10_sylow_ambientDerived_to_local
    {M : Subgroup G} {q : Nat.Primes}
    (X : Sylow q.val (ambientDerivedSubgroup M)) :
    ∃ XD : Sylow q.val (derivedSubgroup M),
      (XD : Subgroup (derivedSubgroup M)).map (derivedSubgroup M).subtype =
        (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let D : Subgroup M := derivedSubgroup M
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let e : D ≃* Dg := by
    change D ≃* D.map M.subtype
    exact Subgroup.equivMapOfInjective D M.subtype M.subtype_injective
  let XD : Sylow q.val D := X.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  refine ⟨XD, ?_⟩
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨yD, hyXD, rfl⟩
    have hyXD' : yD ∈ (X : Subgroup Dg).map e.symm.toMonoidHom := by
      change yD ∈ (X : Subgroup Dg).map e.symm.toMonoidHom at hyXD
      exact hyXD
    rcases Subgroup.mem_map.mp hyXD' with ⟨yDg, hyX, hy_eq⟩
    have hy_val : (((yD : D) : M) : G) = (yDg : G) := by
      calc
        (((yD : D) : M) : G) = (e yD : G) := by
          unfold e
          exact (Subgroup.coe_equivMapOfInjective_apply
            D M.subtype M.subtype_injective yD).symm
        _ = (yDg : G) := by
          have hy_e : e yD = yDg := by
            rw [← hy_eq]
            exact e.apply_symm_apply yDg
          exact congrArg Subtype.val hy_e
    exact ⟨yDg, hyX, hy_val.symm⟩
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨yDg, hyX, hy_eq⟩
    let yD : D := e.symm yDg
    have hyXD : yD ∈ XD := by
      change yD ∈ (X : Subgroup Dg).map e.symm.toMonoidHom
      exact
        ⟨yDg, hyX, rfl⟩
    refine ⟨yD, hyXD, ?_⟩
    have hy_val : (((yD : D) : M) : G) = (yDg : G) := by
      calc
        (((yD : D) : M) : G) = (e yD : G) := by
          unfold e
          exact (Subgroup.coe_equivMapOfInjective_apply
            D M.subtype M.subtype_injective yD).symm
        _ = (yDg : G) := congrArg Subtype.val (e.apply_symm_apply yDg)
    exact Subtype.ext (hy_val.trans hy_eq)

private theorem CFSG.section10_malpha_subgroupOf_derived_eq_piCore
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    (section10MalphaSubgroup M).subgroupOf (derivedSubgroup M) =
      piCore (section10AlphaPrimes M) (derivedSubgroup M) := by
  classical
  let K : Subgroup M := section10MalphaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let KD : Subgroup D := K.subgroupOf D
  let C : Subgroup D := piCore (section10AlphaPrimes M) D
  have hKleD : K ≤ D :=
    (theorem_10_2_c (G := G) hM).1.trans (theorem_10_2_c (G := G) hM).2
  have hKDHall : IsHallSubgroup (section10AlphaPrimes M) KD := by
    simpa [KD, K, D] using
      (theorem_10_2_a (G := G) hM).2.subgroupOf hKleD
  have hKDpi : IsPiSubgroup (G := D) (section10AlphaPrimes M) KD := by
    intro r hr
    exact hKDHall.p_in_pi_of_p_dvd_card r hr
  have hKD_le_C : KD ≤ C := by
    have : KD.Normal := by
      simpa [KD, K, D] using (Subgroup.Normal.subgroupOf (inferInstance : K.Normal) D)
    simpa [C] using
      le_piCore_of_normal_isPiSubgroup (G := D) (section10AlphaPrimes M) KD hKDpi
  have hCpi : IsPiSubgroup (G := D) (section10AlphaPrimes M) C := by
    simpa [C] using piCore_isPiSubgroup (G := D) (section10AlphaPrimes M)
  have hcop : Nat.Coprime (Nat.card C) KD.index := by
    refine Nat.coprime_of_dvd ?_
    intro r hrprime hrC hridx
    let r' : Nat.Primes := ⟨r, hrprime⟩
    have hrπ : r' ∈ section10AlphaPrimes M := hCpi r' hrC
    have hrnotπ : r' ∉ section10AlphaPrimes M :=
      hKDHall.p_in_pi_of_p_dvd_index r' hridx
    exact hrnotπ hrπ
  have hC_dvd_D : Nat.card C ∣ Nat.card D :=
    Subgroup.card_subgroup_dvd_card C
  have hC_dvd_mul : Nat.card C ∣ Nat.card KD * KD.index := by
    have hmul : KD.index * Nat.card KD = Nat.card D :=
      Subgroup.index_mul_card (H := KD)
    have hdiv : Nat.card C ∣ KD.index * Nat.card KD := by
      simpa [hmul] using hC_dvd_D
    simpa [Nat.mul_comm] using hdiv
  have hC_dvd_KD : Nat.card C ∣ Nat.card KD :=
    hcop.dvd_of_dvd_mul_right hC_dvd_mul
  have hcard_ge : Nat.card C ≤ Nat.card KD :=
    Nat.le_of_dvd (Nat.card_pos (α := KD)) hC_dvd_KD
  have hKD_eq_C : KD = C :=
    Subgroup.eq_of_le_of_card_ge hKD_le_C hcard_ge
  simpa [KD, K, D, C] using hKD_eq_C

private theorem CFSG.section10_mbeta_subgroupOf_derived_eq_piCore
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G) :
    (section10MbetaSubgroup M).subgroupOf (derivedSubgroup M) =
      piCore (section10BetaPrimes M) (derivedSubgroup M) := by
  classical
  let K : Subgroup M := section10MbetaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let KD : Subgroup D := K.subgroupOf D
  let C : Subgroup D := piCore (section10BetaPrimes M) D
  have hKleD : K ≤ D := by
    exact (section10_mbetaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  have hKDHall : IsHallSubgroup (section10BetaPrimes M) KD := by
    simpa [KD, K, D] using
      (section10_mbetaSubgroup_isHall hM).subgroupOf hKleD
  have hKDpi : IsPiSubgroup (G := D) (section10BetaPrimes M) KD := by
    intro r hr
    exact hKDHall.p_in_pi_of_p_dvd_card r hr
  have hKD_le_C : KD ≤ C := by
    have : KD.Normal := by
      simpa [KD, K, D] using (Subgroup.Normal.subgroupOf (inferInstance : K.Normal) D)
    simpa [C] using
      le_piCore_of_normal_isPiSubgroup (G := D) (section10BetaPrimes M) KD hKDpi
  have hCpi : IsPiSubgroup (G := D) (section10BetaPrimes M) C := by
    simpa [C] using piCore_isPiSubgroup (G := D) (section10BetaPrimes M)
  have hcop : Nat.Coprime (Nat.card C) KD.index := by
    refine Nat.coprime_of_dvd ?_
    intro r hrprime hrC hridx
    let r' : Nat.Primes := ⟨r, hrprime⟩
    have hrπ : r' ∈ section10BetaPrimes M := hCpi r' hrC
    have hrnotπ : r' ∉ section10BetaPrimes M :=
      hKDHall.p_in_pi_of_p_dvd_index r' hridx
    exact hrnotπ hrπ
  have hC_dvd_D : Nat.card C ∣ Nat.card D :=
    Subgroup.card_subgroup_dvd_card C
  have hC_dvd_mul : Nat.card C ∣ Nat.card KD * KD.index := by
    have hmul : KD.index * Nat.card KD = Nat.card D :=
      Subgroup.index_mul_card (H := KD)
    have hdiv : Nat.card C ∣ KD.index * Nat.card KD := by
      simpa [hmul] using hC_dvd_D
    simpa [Nat.mul_comm] using hdiv
  have hC_dvd_KD : Nat.card C ∣ Nat.card KD :=
    hcop.dvd_of_dvd_mul_right hC_dvd_mul
  have hcard_ge : Nat.card C ≤ Nat.card KD :=
    Nat.le_of_dvd (Nat.card_pos (α := KD)) hC_dvd_KD
  have hKD_eq_C : KD = C :=
    Subgroup.eq_of_le_of_card_ge hKD_le_C hcard_ge
  simpa [KD, K, D, C] using hKD_eq_C

private theorem CFSG.section10_mbeta_sup_local_derived_sylow_characteristic
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (X : Sylow q.val (derivedSubgroup M)) :
    ((section10MbetaSubgroup M).subgroupOf (derivedSubgroup M) ⊔
        (X : Subgroup (derivedSubgroup M))).Characteristic := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let K : Subgroup M := section10MbetaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  have hKleD : K ≤ D := by
    exact (section10_mbetaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  let KsubD : Subgroup D := K.subgroupOf D
  have hKsubD_char : KsubD.Characteristic := by
    rw [show KsubD = piCore (section10BetaPrimes M) D by
      simpa [KsubD, K, D] using section10_mbeta_subgroupOf_derived_eq_piCore (G := G) hM]
    exact piCore_characteristic (G := D) (section10BetaPrimes M)
  let : KsubD.Characteristic := hKsubD_char
  have : KsubD.Normal := by
    simpa [KsubD, K, D] using (Subgroup.Normal.subgroupOf (inferInstance : K.Normal) D)
  have hquotNil : Group.IsNilpotent (D ⧸ KsubD) := by
    simpa [KsubD, K, D] using
      section10_quotient_mbeta_nilpotent_of_le_derived
        (G := G) hM hKleD (by simp [D])
  let π : D →* D ⧸ KsubD := QuotientGroup.mk' KsubD
  let Xbar : Sylow q.val (D ⧸ KsubD) :=
    X.mapSurjective (f := π) (QuotientGroup.mk'_surjective KsubD)
  have hXbar_normal : (Xbar : Subgroup (D ⧸ KsubD)).Normal := by
    let : Group.IsNilpotent (D ⧸ KsubD) := hquotNil
    exact Group.IsNilpotent.sylow_normal (p := q.val) inferInstance Xbar
  have hXbar_char : (Xbar : Subgroup (D ⧸ KsubD)).Characteristic :=
    Sylow.characteristic_of_normal Xbar hXbar_normal
  have hcomap_char :
      ((Xbar : Subgroup (D ⧸ KsubD)).comap π).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk
      (H := KsubD) (K := (Xbar : Subgroup (D ⧸ KsubD))) hXbar_char
  have hcomap_eq :
      (Xbar : Subgroup (D ⧸ KsubD)).comap π =
        KsubD ⊔ (X : Subgroup D) := by
    simp [Xbar, π]
  rw [hcomap_eq] at hcomap_char
  simpa [KsubD, K, D] using hcomap_char


private theorem CFSG.section10_mbeta_sup_ambient_derived_sylow_normal
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (X : Sylow q.val (ambientDerivedSubgroup M)) :
    (section10MbetaSubgroup M ⊔
      (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M).Normal := by
  classical
  obtain ⟨XD, hXDmap⟩ := section10_sylow_ambientDerived_to_local (G := G) X
  let K : Subgroup M := section10MbetaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let XG : Subgroup G := section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X
  let XM : Subgroup M := XG.subgroupOf M
  have hKleD : K ≤ D := by
    exact (section10_mbetaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  let KsubD : Subgroup D := K.subgroupOf D
  let L : Subgroup D := KsubD ⊔ (XD : Subgroup D)
  have hLchar : L.Characteristic := by
    simpa [L, KsubD, K, D] using
      section10_mbeta_sup_local_derived_sylow_characteristic hM XD
  have : D.Characteristic := by infer_instance
  have hLmap_char : (L.map D.subtype).Characteristic := by
    let : L.Characteristic := hLchar
    simpa using characteristic_map_subtype_of_characteristic (G := M) D L
  have hKsubD_map : KsubD.map D.subtype = K := by
    simpa [KsubD, K, D] using
      (Subgroup.map_subgroupOf_eq_of_le (G := M) (H := K) (K := D) hKleD)
  have hXDmap' : (XD : Subgroup D).map D.subtype = XM := by
    change (XD : Subgroup (derivedSubgroup M)).map (derivedSubgroup M).subtype =
      (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M
    exact hXDmap
  have hLmap_eq : L.map D.subtype = K ⊔ XM := by
    calc
      L.map D.subtype =
          KsubD.map D.subtype ⊔ (XD : Subgroup D).map D.subtype := by
        simpa [L] using (Subgroup.map_sup KsubD (XD : Subgroup D) D.subtype)
      _ = K ⊔ XM := by rw [hKsubD_map, hXDmap']
  have hJchar : (K ⊔ XM).Characteristic := by
    simpa [hLmap_eq] using hLmap_char
  let : (K ⊔ XM).Characteristic := hJchar
  simpa [K, XM, XG] using (inferInstance : (K ⊔ XM).Normal)

/-- The `M_alpha` analogue of the derived-Sylow normality step used in
Lemma 13.1: if `X` is a Sylow subgroup of `M'`, then `M_alpha X` is
normal in `M`. -/
public theorem CFSG.section10_malpha_sup_ambient_derived_sylow_normal
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (X : Sylow q.val (ambientDerivedSubgroup M)) :
    (section10MalphaSubgroup M ⊔
      (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M).Normal := by
  classical
  obtain ⟨XD, hXDmap⟩ := section10_sylow_ambientDerived_to_local (G := G) X
  let K : Subgroup M := section10MalphaSubgroup M
  let D : Subgroup M := derivedSubgroup M
  let XG : Subgroup G := section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X
  let XM : Subgroup M := XG.subgroupOf M
  have : Fact q.val.Prime := ⟨q.property⟩
  have hKleD : K ≤ D :=
    (theorem_10_2_c (G := G) hM).1.trans (theorem_10_2_c (G := G) hM).2
  let KsubD : Subgroup D := K.subgroupOf D
  have hKsubD_char : KsubD.Characteristic := by
    rw [show KsubD = piCore (section10AlphaPrimes M) D by
      simpa [KsubD, K, D] using section10_malpha_subgroupOf_derived_eq_piCore (G := G) hM]
    exact piCore_characteristic (G := D) (section10AlphaPrimes M)
  let : KsubD.Characteristic := hKsubD_char
  have : KsubD.Normal := by
    simpa [KsubD, K, D] using (Subgroup.Normal.subgroupOf (inferInstance : K.Normal) D)
  have hquotNil : Group.IsNilpotent (D ⧸ KsubD) := by
    rcases (theorem_10_2_d (G := G) hM).2 with ⟨hKD, hKnormalD, hnil⟩
    simpa [KsubD, K, D] using hnil
  let π : D →* D ⧸ KsubD := QuotientGroup.mk' KsubD
  let Xbar : Sylow q.val (D ⧸ KsubD) :=
    XD.mapSurjective (f := π) (QuotientGroup.mk'_surjective KsubD)
  have hXbar_normal : (Xbar : Subgroup (D ⧸ KsubD)).Normal := by
    let : Group.IsNilpotent (D ⧸ KsubD) := hquotNil
    exact Group.IsNilpotent.sylow_normal (p := q.val) inferInstance Xbar
  have hXbar_char : (Xbar : Subgroup (D ⧸ KsubD)).Characteristic :=
    Sylow.characteristic_of_normal Xbar hXbar_normal
  have hcomap_char :
      ((Xbar : Subgroup (D ⧸ KsubD)).comap π).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk
      (H := KsubD) (K := (Xbar : Subgroup (D ⧸ KsubD))) hXbar_char
  have hcomap_eq :
      (Xbar : Subgroup (D ⧸ KsubD)).comap π =
        KsubD ⊔ (XD : Subgroup D) := by
    simp [Xbar, π]
  let L : Subgroup D := KsubD ⊔ (XD : Subgroup D)
  have hLchar : L.Characteristic := by
    simpa [L, hcomap_eq] using hcomap_char
  have : D.Characteristic := by infer_instance
  have hLmap_char : (L.map D.subtype).Characteristic := by
    let : L.Characteristic := hLchar
    simpa using characteristic_map_subtype_of_characteristic (G := M) D L
  have hKsubD_map : KsubD.map D.subtype = K := by
    simpa [KsubD, K, D] using
      (Subgroup.map_subgroupOf_eq_of_le (G := M) (H := K) (K := D) hKleD)
  have hXDmap' : (XD : Subgroup D).map D.subtype = XM := by
    change (XD : Subgroup (derivedSubgroup M)).map (derivedSubgroup M).subtype =
      (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M
    exact hXDmap
  have hLmap_eq : L.map D.subtype = K ⊔ XM := by
    calc
      L.map D.subtype =
          KsubD.map D.subtype ⊔ (XD : Subgroup D).map D.subtype := by
        simpa [L] using (Subgroup.map_sup KsubD (XD : Subgroup D) D.subtype)
      _ = K ⊔ XM := by rw [hKsubD_map, hXDmap']
  have hJchar : (K ⊔ XM).Characteristic := by
    simpa [hLmap_eq] using hLmap_char
  let : (K ⊔ XM).Characteristic := hJchar
  simpa [K, XM, XG] using (inferInstance : (K ⊔ XM).Normal)

public theorem CFSG.section10_mbeta_sup_ambient_normalizer_of_derived_sylow
    {M : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    {q : Nat.Primes} (X : Sylow q.val (ambientDerivedSubgroup M)) :
    section10MbetaSubgroup M ⊔
        (subgroupNormalizerIn M
          (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X : Set G)).subgroupOf M =
      ⊤ := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let D : Subgroup M := derivedSubgroup M
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let XG : Subgroup G := section10AmbientSylowSubgroup Dg X
  let XM : Subgroup M := XG.subgroupOf M
  let J : Subgroup M := section10MbetaSubgroup M ⊔ XM
  obtain ⟨XD, hXDmap⟩ := section10_sylow_ambientDerived_to_local (G := G) X
  have hDg_le_M : Dg ≤ M := by
    intro x hx
    change x ∈ ambientDerivedSubgroup M at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hXG_le_Dg : XG ≤ Dg := by
    simpa [XG, Dg] using section10_ambient_sylow_le_base (G := G) X
  have hXG_le_M : XG ≤ M := hXG_le_Dg.trans hDg_le_M
  have hXM_le_D : XM ≤ D := by
    intro x hx
    have hxDg : ((x : M) : G) ∈ Dg := hXG_le_Dg hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M at hxDg
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hxDg
    rcases hxDg with ⟨y, hyD, hyx⟩
    have hyxM : y = x := Subtype.ext hyx
    simpa [D, hyxM] using hyD
  have hKleD : section10MbetaSubgroup M ≤ D := by
    exact (section10_mbetaSubgroup_le_msigmaSubgroup hM).trans
      (section10_msigmaSubgroup_le_derivedSubgroup hM)
  have hJleD : J ≤ D := by
    simpa [J, XM] using sup_le hKleD hXM_le_D
  have hXD_le_JsubD : (XD : Subgroup D) ≤ J.subgroupOf D := by
    intro x hx
    change ((x : D) : M) ∈ J
    have hxXM : ((x : D) : M) ∈ XM := by
      have hxmap : ((x : D) : M) ∈ (XD : Subgroup D).map D.subtype :=
        ⟨x, hx, rfl⟩
      have hxmap' : ((x : D) : M) ∈
          (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X).subgroupOf M := by
        simpa [D] using (hXDmap ▸ hxmap)
      simpa [XM, XG, Dg] using hxmap'
    exact Subgroup.mem_sup_right hxXM
  obtain ⟨PJ, hPJmapD⟩ :=
    section10_exists_sylow_subgroupOf_with_same_ambient
      (H := M) (S := J) (D := D) hJleD XD hXD_le_JsubD
  have hPJmap : (PJ : Subgroup J).map J.subtype = XM := by
    simpa [XM] using hPJmapD.trans hXDmap
  have hJnormal : J.Normal := by
    simpa [J, XM, XG, Dg] using
      section10_mbeta_sup_ambient_derived_sylow_normal hM X
  let : J.Normal := hJnormal
  simpa [J, XG, Dg] using
    section10_mbeta_sup_normalizer_of_frattini_join
      (G := G) (M := M) (X := XG) (q := q) hXG_le_M
      (J := J) (hJ_eq := by rfl) PJ hPJmap

/-- Corollary 10.9(a)(3). -/
public theorem CFSG.corollary_10_9_a_3
    {M : Subgroup G} {p q : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G) (_hpM : p ∈ subgroupPrimeSet M)
    (_hqM : q ∈ subgroupPrimeSet M) (hpβ : p ∉ section10BetaPrimes M)
    (hqβ : q ∉ section10BetaPrimes M) (hpq : p ≠ q)
    (X : Sylow q.val (ambientDerivedSubgroup M)) :
    ∃ P' : Sylow p.val (ambientDerivedSubgroup M),
      section10AmbientSylowSubgroup (ambientDerivedSubgroup M) P' ≤
        ambientDerivedSubgroup
          (subgroupNormalizerIn M (section10AmbientSylowSubgroup (ambientDerivedSubgroup M) X : Set G)) := by
  classical
  have : Fact p.val.Prime := ⟨p.property⟩
  have : Fact q.val.Prime := ⟨q.property⟩
  let Dg : Subgroup G := ambientDerivedSubgroup M
  let XG : Subgroup G := section10AmbientSylowSubgroup Dg X
  have hDg_le_M : Dg ≤ M := by
    intro x hx
    change x ∈ ambientDerivedSubgroup M at hx
    rw [ambientDerivedSubgroup, Subgroup.mem_map] at hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hXG_le_Dg : XG ≤ Dg := by
    simpa [XG, Dg] using section10_ambient_sylow_le_base (G := G) X
  have hXG_le_M : XG ≤ M := hXG_le_Dg.trans hDg_le_M
  have hXG_q : IsPGroup q.val XG := by
    change IsPGroup q.val
      ((X : Subgroup (ambientDerivedSubgroup M)).map (ambientDerivedSubgroup M).subtype)
    exact IsPGroup.map (p := q.val) (H := (X : Subgroup (ambientDerivedSubgroup M)))
      X.isPGroup' (ambientDerivedSubgroup M).subtype
  obtain ⟨P, hP_le_U⟩ :=
    section10_exists_ambient_derived_sylow_le_normalizer_of_le_derived
      (G := G) (M := M) (X := XG) (p := p) (q := q)
      hM hpβ hqβ hpq hXG_le_M hXG_q hXG_le_Dg
  have hKU :
      section10MbetaSubgroup M ⊔
          (subgroupNormalizerIn M (XG : Set G)).subgroupOf M =
        ⊤ := by
    simpa [XG, Dg] using
      section10_mbeta_sup_ambient_normalizer_of_derived_sylow
        (G := G) hM X
  refine ⟨P, ?_⟩
  simpa [XG, Dg] using
    section10_lemma_6_5_ambient_normalizer_endpoint
      (G := G) (M := M) (X := XG) (p := p) hM hpβ hKU hP_le_U
