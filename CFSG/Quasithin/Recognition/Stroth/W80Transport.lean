module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5System
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4OctSys
public import CFSG.Quasithin.Background.A318PF4Frame
public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.GH74.GLS.Stage2.Local.P34Embed
public import CFSG.Quasithin.Vol2.GoldschmidtF431BNRad
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Stroth

namespace W80Model

open CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Quasithin.H13.F431.Un
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary

theorem un5System_B_inf_N {F : Type} [Field F] [Finite F] {f : ℕ} [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (ζ : traceZero (unitaryInvolution F 2 f))
    [Fact ((ζ : F) ≠ 0)] :
    (un5System hF ζ).B ⊓ (un5System hF ζ).N =
      (unT (F := F) (p := 2) (f := f) 5).map (un5Proj (F := F) (f := f)) := by
  change (un5PreQ hF ζ).B ⊓ (un5PreQ hF ζ).N =
    (unT (F := F) (p := 2) (f := f) 5).map (un5Proj (F := F) (f := f))
  unfold un5PreQ
  change (unB hF 5).map (un5Proj (F := F) (f := f)) ⊓
      (unN hF 5 ζ).map (un5Proj (F := F) (f := f)) = _
  rw [map_inf_map_of_ker_le (un5Proj (F := F) (f := f))
    ((un5_ker_le hF ζ).trans inf_le_left), un5B_inf_N]

theorem octH_eq_reeTorusPart {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ} :
    (octH K a).map (F4.reeGamma K a).subtype =
      ((CFSG.LieType.Ree.reeTorusPart F4 K a).map
        (CFSG.LieType.Ree.reeFixed F4 K a).subtype).map
          (adjointGroup F4.tag K).subtype := by
  have hH : (nativeData F4.tag K).H =
      (torusGroup F4.tag K).subgroupOf (adjointGroup F4.tag K) := by
    refine le_antisymm ?_ ?_
    · intro h hh
      have hN : h ∈ (nativeData F4.tag K).N := by
        obtain ⟨k, hk, hkh⟩ :=
          (CFSG.LieType.Chevalley.RootGroupData.mem_H_iff
            (D := nativeData F4.tag K)).mp hh
        rw [← hkh]
        exact k.2
      have hmono : h ∈ (monomialSubgroup F4.tag K).subgroupOf
          (adjointGroup F4.tag K) := by
        rw [CFSG.LieType.Ree.ReeTag.monomialSub_eq_monomialGroup]
        exact hN
      have hmono' : (h : ModGL F4.tag K) ∈ monomialSubgroup F4.tag K :=
        Subgroup.mem_subgroupOf.1 hmono
      have hup : CFSG.LieType.Chevalley.IsUpperTriangular F4.tag K
          ((h : ModGL F4.tag K) : Module.End K (RootModule F4.tag K)) := by
        intro x y hxy
        obtain ⟨μ, hμ⟩ :=
          CFSG.LieType.Simplicity.exists_apply_single_eq_smul_of_mem_H
            (τ := F4.tag) hh y
        rw [hμ, Finsupp.smul_apply, Finsupp.single_eq_of_ne]
        · simp
        · intro hEq
          exact CFSG.Blueprint.Chevalley.Label.Precedes.irrefl y (hEq ▸ hxy)
      exact Subgroup.mem_subgroupOf.2
        (CFSG.LieType.Chevalley.mem_torusGroup_of_isUpperTriangular hmono' hup)
    · intro h hh
      have hh' : (h : ModGL F4.tag K) ∈ torusGroup F4.tag K :=
        Subgroup.mem_subgroupOf.1 hh
      simpa using CFSG.LieType.Ree.ReeTag.mem_nativeData_H_of_mem_torusGroup (t := F4) hh'

  have hleft : (octH K a).map (F4.reeGamma K a).subtype = F4.reeFixedTorus K a := by
    change (((F4.reeFixedTorus K a).subgroupOf (F4.reeGamma K a)).map
      (F4.reeGamma K a).subtype) = _
    exact Subgroup.map_subgroupOf_eq_of_le
      (show F4.reeFixedTorus K a ≤ F4.reeGamma K a from inf_le_right)
  have hright : ((CFSG.LieType.Ree.reeTorusPart F4 K a).map
      (CFSG.LieType.Ree.reeFixed F4 K a).subtype).map
        (adjointGroup F4.tag K).subtype = F4.reeFixedTorus K a := by
    rw [Subgroup.map_map]
    change (((nativeData F4.tag K).H.comap
      (CFSG.LieType.Ree.reeFixed F4 K a).subtype).map
        ((adjointGroup F4.tag K).subtype.comp
          (CFSG.LieType.Ree.reeFixed F4 K a).subtype)) = _
    rw [← Subgroup.map_map, Subgroup.map_comap_eq, Subgroup.range_subtype,
      Subgroup.map_inf _ _ _ (adjointGroup F4.tag K).subtype_injective,
      hH,
      Subgroup.map_subgroupOf_eq_of_le
        (CFSG.LieType.Ree.ReeTag.torusGroup_le_adjointGroup (t := F4) (K := K)),
      CFSG.Quasithin.A318P.map_reeFixed_eq_reeGamma']
    rw [inf_comm]
    rfl
  rw [hleft, hright]

theorem le_twoPrimeResidualOf_of_isPGroup {G : Type} [Group G] [Finite G]
    {H A : Subgroup G} (hAH : A ≤ H) (hA : IsPGroup 2 A) :
    A ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
  intro x hx
  rw [CFSG.Quasithin.SimsG4.twoPrimeResidualOf, Subgroup.mem_map]
  refine ⟨⟨x, hAH hx⟩, ?_, rfl⟩
  rw [CFSG.Quasithin.SimsG4.twoPrimeResidual, Subgroup.mem_sInf]
  intro N hN
  obtain ⟨hNnorm, hNodd⟩ := hN
  have hNsub : (N.map H.subtype).subgroupOf H = N := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzy⟩
      rwa [← H.subtype_injective hzy]
    · intro hy
      exact ⟨y, hy, rfl⟩
  have hNnorm' : (N.map H.subtype).subgroupOf H |>.Normal := by
    rw [hNsub]; exact hNnorm
  have hxN : x ∈ N.map H.subtype := by
    refine CFSG.Quasithin.B6.le_of_isPGroup_of_odd_relIndex hAH hA
      (Subgroup.map_subtype_le N) ?_ ?_ hx
    · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.map_subtype_le N)).mp hNnorm'
    · have hri := Subgroup.relIndex_map_map_of_injective (f := H.subtype) N ⊤
        H.subtype_injective
      rw [Subgroup.map_top, Subgroup.subtype_range, Subgroup.relIndex_top_right] at hri
      rw [hri]
      simpa [even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hNodd)
  exact (Subgroup.mem_map_iff_mem H.subtype_injective).1 hxN

theorem closure_isPGroup_zpowers_le_twoPrimeResidualOf {G : Type} [Group G] [Finite G]
    {H : Subgroup G} :
    Subgroup.closure {x : G | x ∈ H ∧ IsPGroup 2 (Subgroup.zpowers x)} ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
  rw [Subgroup.closure_le]
  rintro x ⟨hxH, hx2⟩
  have hle : Subgroup.zpowers x ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
    refine le_twoPrimeResidualOf_of_isPGroup (A := Subgroup.zpowers x) ?_ hx2
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact H.zpow_mem hxH k
  exact hle (Subgroup.mem_zpowers x)

theorem closure_orderOf_two_le_twoPrimeResidualOf {G : Type} [Group G] [Finite G]
    {H : Subgroup G} :
    Subgroup.closure {x : G | x ∈ H ∧ orderOf x = 2} ≤
      CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
  rw [Subgroup.closure_le]
  rintro x ⟨hxH, hx2⟩
  have hle : Subgroup.zpowers x ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
    refine le_twoPrimeResidualOf_of_isPGroup (A := Subgroup.zpowers x) ?_ ?_
    · intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact H.zpow_mem hxH k
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx2]
      norm_num
  exact hle (Subgroup.mem_zpowers x)

theorem le_twoPrimeResidualOf_of_simple {G : Type} [Group G] [Finite G]
    {H R : Subgroup G} (hRH : R ≤ H) (hR : IsSimpleGroup R)
    (h2 : ∃ x : R, orderOf x = 2) :
    R ≤ CFSG.Quasithin.SimsG4.twoPrimeResidualOf H := by
  obtain ⟨x, hx⟩ := h2
  have htop : Subgroup.closure {x : R | orderOf x = 2} = ⊤ :=
    CFSG.GH74.GLS.Stage2.Local.P34.closure_involutions_eq_top hR hx
  have hmap : R ≤ Subgroup.closure {x : G | x ∈ H ∧ orderOf x = 2} := by
    have h1 : R ≤ (Subgroup.closure {x : R | orderOf x = 2}).map R.subtype := by
      rw [htop, Subgroup.map_top, Subgroup.range_subtype]
    refine h1.trans ?_
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro y ⟨x, hx, rfl⟩
    exact ⟨hRH x.2, (Subgroup.orderOf_coe x).trans hx⟩
  exact hmap.trans (closure_orderOf_two_le_twoPrimeResidualOf (H := H))

theorem rankTwo_root_neg_one_le_P1 {G : Type} [Group G] {n : ℕ}
    (D : RankTwoSystem G n) : D.root (-1) ≤ D.P₁ := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₁
  have hmdc : (m : G) ∈ CFSG.GH74.BNPair.dc D.B D.N D.w₁ := by
    have h := CFSG.GH74.BNPair.coe_mem_dc (B := D.B) (N := D.N) m
    rwa [hm] at h
  have hmP : (m : G) ∈ D.P₁ :=
    Subgroup.subset_closure (CFSG.GH74.BNPair.dc_subset_parabolicSet
      (J := {D.w₁}) (Subgroup.subset_closure (Set.mem_singleton D.w₁)) hmdc)
  have hconj := (D.roots.action₁ m hm).1
  have hn := D.three_le
  rw [← hconj]
  rintro y ⟨x, hx, rfl⟩
  have hxB : x ∈ D.B := D.root_le_B (k := 1) (by norm_num) (by omega) hx
  have hBP1 : D.B ≤ D.P₁ := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_true] using
      CFSG.Quasithin.H13.F431.BN.B_le_P D true
  have hmP' : ((m : G)⁻¹)⁻¹ ∈ D.P₁ := by simpa using hmP
  have h : (m : G)⁻¹ * x * ((m : G)⁻¹)⁻¹ ∈ D.P₁ :=
    D.P₁.mul_mem (D.P₁.mul_mem (D.P₁.inv_mem hmP) (hBP1 hxB)) hmP'
  simpa [MulAut.conj_apply] using h

theorem rankTwo_root_neg_n_le_P2 {G : Type} [Group G] {n : ℕ}
    (D : RankTwoSystem G n) : D.root (-(n : ℤ)) ≤ D.P₂ := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective D.w₂
  have hmdc : (m : G) ∈ CFSG.GH74.BNPair.dc D.B D.N D.w₂ := by
    have h := CFSG.GH74.BNPair.coe_mem_dc (B := D.B) (N := D.N) m
    rwa [hm] at h
  have hmP : (m : G) ∈ D.P₂ :=
    Subgroup.subset_closure (CFSG.GH74.BNPair.dc_subset_parabolicSet
      (J := {D.w₂}) (Subgroup.subset_closure (Set.mem_singleton D.w₂)) hmdc)
  have hconj := (D.roots.action₂ m hm).1
  have hn := D.three_le
  rw [← hconj]
  rintro y ⟨x, hx, rfl⟩
  have hxB : x ∈ D.B := D.root_le_B (k := (n : ℤ)) (by omega) le_rfl hx
  have hBP2 : D.B ≤ D.P₂ := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using
      CFSG.Quasithin.H13.F431.BN.B_le_P D false
  have hmP' : ((m : G)⁻¹)⁻¹ ∈ D.P₂ := by simpa using hmP
  have h : (m : G)⁻¹ * x * ((m : G)⁻¹)⁻¹ ∈ D.P₂ :=
    D.P₂.mul_mem (D.P₂.mul_mem (D.P₂.inv_mem hmP) (hBP2 hxB)) hmP'
  simpa [MulAut.conj_apply] using h

section T3

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hR : CFSG.GH74.GLS.SP.RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a)
      (octRoot K a)) [IsSimpleGroup (Gm K a)]

theorem octH_le_P1 : octH K a ≤ (octSystemOf hR).P₁ := by
  intro x hx
  have hB : x ∈ (octSystemOf hR).B := by
    rw [octSystemOf_B hR]
    exact Subgroup.mem_sup_left hx
  exact Subgroup.subset_closure
    (CFSG.GH74.BNPair.le_parabolic_one (J := {(octSystemOf hR).w₁}) hB)

theorem Ug_le_P1 : Ug K a ≤ (octSystemOf hR).P₁ := by
  intro x hx
  have hB : x ∈ (octSystemOf hR).B := by
    rw [octSystemOf_B hR]
    exact Subgroup.mem_sup_right hx
  exact Subgroup.subset_closure
    (CFSG.GH74.BNPair.le_parabolic_one (J := {(octSystemOf hR).w₁}) hB)

theorem octR1_mem_P1 : octR1 K a ∈ (octSystemOf hR).P₁ := by
  have hcoe : ((⟨octR1 K a, CFSG.GH74.GLS.SP.RGD2.r₁_mem_N hR⟩ : (octSystemOf hR).N) :
      CFSG.GH74.BNPair.WeylGroup (octSystemOf hR).B (octSystemOf hR).N) =
        (octSystemOf hR).w₁ := rfl
  have hdc : octR1 K a ∈ CFSG.GH74.BNPair.dc (octSystemOf hR).B (octSystemOf hR).N
      (octSystemOf hR).w₁ := by
    rw [← hcoe]
    exact CFSG.GH74.BNPair.coe_mem_dc
      (⟨octR1 K a, CFSG.GH74.GLS.SP.RGD2.r₁_mem_N hR⟩ : (octSystemOf hR).N)
  change octR1 K a ∈ (octSystemOf hR).P₁
  exact (CFSG.GH74.BNPair.mem_parabolic_single_iff (octSystemOf hR).isTits (by simp)).2
    (Or.inr hdc)

theorem r2_image_le_P1 (hR : CFSG.GH74.GLS.SP.RGD2 8 (octH K a) (octR1 K a) (octR2 K a)
    (Ug K a) (octRoot K a)) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    (CFSG.SectionRank.LargeRee.r2 K a hK).map
        (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
      (octSystemOf hR).P₁ := by
  refine (Subgroup.map_le_iff_le_comap).mpr ?_
  refine CFSG.SectionRank.LargeRee.r2_le hK ?_ ?_ ?_
  · intro x hxU
    change (CFSG.Quasithin.A318P.reeFixedEquivGamma a x : Gm K a) ∈ (octSystemOf hR).P₁
    have hxU' : (x : adjointGroup F4.tag K) ∈ (nativeData F4.tag K).U :=
      CFSG.LieType.Chevalley.Uminus_le_U F4.tag K
        (F4.blockElt (CFSG.SectionRank.LargeRee.fi 1)) hxU
    have hxUnip : x ∈ CFSG.LieType.Ree.reeUnipPart F4 K a := hxU'
    have hxUg : (CFSG.Quasithin.A318P.reeFixedEquivGamma a x : Gm K a) ∈ Ug K a := by
      refine Subgroup.mem_subgroupOf.2 ?_
      have hxmap : CFSG.LieType.Ree.LargeReeInvolution.reeFixedEmb K a x ∈
          F4.reeFixedPosUnipotent K a := by
        rw [← CFSG.LieType.Ree.LargeReeInvolution.map_reeUnipPart]
        exact ⟨x, hxUnip, rfl⟩
      rw [CFSG.Quasithin.A318P.coe_reeFixedEquivGamma]
      simpa [CFSG.LieType.Ree.LargeReeInvolution.reeFixedEmb] using hxmap
    exact Ug_le_P1 hR hxUg
  · intro u
    change (CFSG.Quasithin.A318P.reeFixedEquivGamma a
      ((CFSG.SectionRank.LargeRee.reeTorusHom a hK
        CFSG.SectionRank.LargeRee.fi_one_mem_longSet) u) : Gm K a) ∈ (octSystemOf hR).P₁
    have hTmem : (CFSG.Quasithin.A318P.reeFixedEquivGamma a
        ((CFSG.SectionRank.LargeRee.reeTorusHom a hK
          CFSG.SectionRank.LargeRee.fi_one_mem_longSet) u) : Gm K a) ∈ octH K a := by
      refine Subgroup.mem_subgroupOf.2 ?_
      rw [CFSG.Quasithin.A318P.coe_reeFixedEquivGamma]
      change (↑(F4.reeTorus a (CFSG.SectionRank.LargeRee.fi 1) u) :
        ModGL F4.tag K) ∈ F4.reeFixedTorus K a
      exact CFSG.LieType.Ree.ReeTag.coe_reeTorus_mem_reeFixedTorus (t := F4)
        (a := a) hK CFSG.SectionRank.LargeRee.fi_one_mem_longSet u
    exact octH_le_P1 hR hTmem
  · change (CFSG.Quasithin.A318P.reeFixedEquivGamma a
      (CFSG.SectionRank.LargeRee.relNrepHom K a
        (CFSG.SectionRank.LargeRee.blockGen 1)) : Gm K a) ∈ (octSystemOf hR).P₁
    have hrel : (CFSG.Quasithin.A318P.reeFixedEquivGamma a
        (CFSG.SectionRank.LargeRee.relNrepHom K a
          (CFSG.SectionRank.LargeRee.blockGen 1)) : Gm K a) = octR1 K a := by
      apply Subtype.ext
      rw [CFSG.Quasithin.A318P.coe_reeFixedEquivGamma]
      rfl
    rw [hrel]
    exact octR1_mem_P1 hR

theorem octH_le_P2 : octH K a ≤ (octSystemOf hR).P₂ := by
  have hBP2 : (octSystemOf hR).B ≤ (octSystemOf hR).P₂ := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using
      CFSG.Quasithin.H13.F431.BN.B_le_P (octSystemOf hR) false
  intro x hx
  apply hBP2
  rw [octSystemOf_B hR]
  exact Subgroup.mem_sup_left hx

theorem Ug_le_P2 : Ug K a ≤ (octSystemOf hR).P₂ := by
  have hBP2 : (octSystemOf hR).B ≤ (octSystemOf hR).P₂ := by
    simpa [CFSG.Quasithin.H13.F431.BN.P_false] using
      CFSG.Quasithin.H13.F431.BN.B_le_P (octSystemOf hR) false
  intro x hx
  apply hBP2
  rw [octSystemOf_B hR]
  exact Subgroup.mem_sup_right hx

theorem octR2_mem_P2 : octR2 K a ∈ (octSystemOf hR).P₂ := by
  have hcoe : ((⟨octR2 K a, CFSG.GH74.GLS.SP.RGD2.r₂_mem_N hR⟩ : (octSystemOf hR).N) :
      CFSG.GH74.BNPair.WeylGroup (octSystemOf hR).B (octSystemOf hR).N) =
        (octSystemOf hR).w₂ := rfl
  have hdc : octR2 K a ∈ CFSG.GH74.BNPair.dc (octSystemOf hR).B (octSystemOf hR).N
      (octSystemOf hR).w₂ := by
    rw [← hcoe]
    exact CFSG.GH74.BNPair.coe_mem_dc
      (⟨octR2 K a, CFSG.GH74.GLS.SP.RGD2.r₂_mem_N hR⟩ : (octSystemOf hR).N)
  change octR2 K a ∈ (octSystemOf hR).P₂
  exact (CFSG.GH74.BNPair.mem_parabolic_single_iff (octSystemOf hR).isTits (by simp)).2
    (Or.inr hdc)

theorem closure_blockX_zero_octR2_image_le_P2
    (hR : CFSG.GH74.GLS.SP.RGD2 8 (octH K a) (octR1 K a) (octR2 K a) (Ug K a)
      (octRoot K a)) :
    (Subgroup.closure
      ((CFSG.SectionRank.LargeRee.blockX (K := K) a 0 : Set
          (CFSG.LieType.Ree.reeFixed F4 K a)) ∪
        {CFSG.SectionRank.LargeRee.relNrepHom K a
          (CFSG.SectionRank.LargeRee.blockGen 0)})).map
        (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
      (octSystemOf hR).P₂ := by
  rw [MonoidHom.map_closure]
  rw [Subgroup.closure_le]
  rintro y ⟨x, hx, rfl⟩
  rcases hx with hx | hx
  ·
    apply Ug_le_P2 hR
    refine Subgroup.mem_subgroupOf.2 ?_
    have hxU : (x : adjointGroup F4.tag K) ∈
        CFSG.LieType.Chevalley.Uminus F4.tag K
          (F4.blockElt (CFSG.SectionRank.LargeRee.fi 0)) := hx
    have hxU' : (x : adjointGroup F4.tag K) ∈ (nativeData F4.tag K).U :=
      CFSG.LieType.Chevalley.Uminus_le_U F4.tag K
        (F4.blockElt (CFSG.SectionRank.LargeRee.fi 0)) hxU
    have hxUnip : x ∈ CFSG.LieType.Ree.reeUnipPart F4 K a := hxU'
    have hxmap : CFSG.LieType.Ree.LargeReeInvolution.reeFixedEmb K a x ∈
        F4.reeFixedPosUnipotent K a := by
      rw [← CFSG.LieType.Ree.LargeReeInvolution.map_reeUnipPart]
      exact ⟨x, hxUnip, rfl⟩
    change ((x : adjointGroup F4.tag K) : ModGL F4.tag K) ∈
      F4.reeFixedPosUnipotent K a
    simpa [CFSG.LieType.Ree.LargeReeInvolution.reeFixedEmb] using hxmap
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have hrel : (CFSG.Quasithin.A318P.reeFixedEquivGamma a
        (CFSG.SectionRank.LargeRee.relNrepHom K a
          (CFSG.SectionRank.LargeRee.blockGen 0)) : Gm K a) = octR2 K a := by
      apply Subtype.ext
      rw [CFSG.Quasithin.A318P.coe_reeFixedEquivGamma]
      rfl
    simpa [hrel] using octR2_mem_P2 hR

open CFSG.SectionRank.LargeRee CFSG.LieType.Steinberg Matrix

theorem blockGen_zero_eq_blockElt :
    (CFSG.SectionRank.LargeRee.blockGen 0 : WeylGroup ReeTag.F4.tag) =
      ReeTag.F4.blockElt (CFSG.SectionRank.LargeRee.ix 0) := by
  rw [CFSG.SectionRank.LargeRee.coe_blockGen, CFSG.SectionRank.LargeRee.blockIdx_zero]
  rfl

theorem xElement_mul_xElement_mem_Uminus_blockGen_zero (c : K) :
    xElement (CFSG.SectionRank.LargeRee.ix 0) c *
        xElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a) ∈
      Uminus ReeTag.F4.tag K (CFSG.SectionRank.LargeRee.blockGen 0) := by
  rw [blockGen_zero_eq_blockElt]
  exact mul_mem
    (mem_Uminus_of_mem_X (height_simpleRoot_pos _) height_blockElt_zero_smul_zero
      (xElement_mem_X _ c))
    (mem_Uminus_of_mem_X (height_simpleRoot_pos _) height_blockElt_zero_smul_three
      (xElement_mem_X _ _))

theorem sl2Upper_eq_componentInitial (c : K) :
    sl2Upper c = CFSG.LocalAnalysis.ComponentInitial.sl2Upper K c :=
  Subtype.ext rfl

theorem sl2Lower_eq_componentInitial (c : K) :
    sl2Lower c = CFSG.LocalAnalysis.ComponentInitial.sl2Lower K c :=
  Subtype.ext rfl

theorem mem_blockX_zero_of_sl2Upper
    (ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a)
    (hup : ∀ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) =
      xElement (CFSG.SectionRank.LargeRee.ix 0) c *
        xElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a)) (c : K) :
    ψ (sl2Upper c) ∈ CFSG.SectionRank.LargeRee.blockX (K := K) a 0 := by
  rw [CFSG.SectionRank.LargeRee.blockX, CFSG.SectionRank.LargeRee.UminusFixed,
    Subgroup.mem_comap]
  change (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) ∈
    Uminus ReeTag.F4.tag K (CFSG.SectionRank.LargeRee.blockGen 0)
  rw [hup c]
  exact xElement_mul_xElement_mem_Uminus_blockGen_zero c

theorem sl2Lower_eq_sl2Weyl_mul_sl2Upper_mul_inv (c : K) :
    sl2Lower c = CFSG.SectionRank.LargeRee.sl2Weyl (K := K) * sl2Upper c *
      (CFSG.SectionRank.LargeRee.sl2Weyl (K := K))⁻¹ := by
  haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hww : CFSG.SectionRank.LargeRee.sl2Weyl (K := K) *
      CFSG.SectionRank.LargeRee.sl2Weyl (K := K) = 1 :=
    CFSG.SectionRank.LargeRee.sl2Weyl_mul_self (K := K)
  rw [inv_eq_of_mul_eq_one_right hww]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    CFSG.SectionRank.LargeRee.coe_sl2Weyl, CFSG.LieType.Steinberg.coe_sl2Upper,
    CFSG.LieType.Steinberg.coe_sl2Lower]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem map_sl2Weyl_eq_map_relNrepHom
    (ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a)
    (hw : (ψ CFSG.SectionRank.LargeRee.sl2Weyl : adjointGroup ReeTag.F4.tag K) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (CFSG.SectionRank.LargeRee.ix 0))) :
    (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom
        (ψ CFSG.SectionRank.LargeRee.sl2Weyl) =
      (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom
        (CFSG.SectionRank.LargeRee.relNrepHom K a (CFSG.SectionRank.LargeRee.blockGen 0)) := by
  apply Subtype.ext
  change ((CFSG.Quasithin.A318P.reeFixedEquivGamma a
      (ψ CFSG.SectionRank.LargeRee.sl2Weyl) : ↥(ReeTag.F4.reeGamma K a)) :
        ModGL ReeTag.F4.tag K) =
    ((CFSG.Quasithin.A318P.reeFixedEquivGamma a
      (CFSG.SectionRank.LargeRee.relNrepHom K a
        (CFSG.SectionRank.LargeRee.blockGen 0)) : ↥(ReeTag.F4.reeGamma K a)) :
      ModGL ReeTag.F4.tag K)
  rw [CFSG.Quasithin.A318P.coe_reeFixedEquivGamma,
    CFSG.Quasithin.A318P.coe_reeFixedEquivGamma, hw,
    CFSG.SectionRank.LargeRee.coe_relNrepHom, blockGen_zero_eq_blockElt]

theorem sl2_image_le_P2
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a)
    (hup : ∀ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) =
      xElement (CFSG.SectionRank.LargeRee.ix 0) c *
        xElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a))
    (hlow : ∀ c, (ψ (sl2Lower c) : adjointGroup ReeTag.F4.tag K) =
      yElement (CFSG.SectionRank.LargeRee.ix 0) c *
        yElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a))
    (hw : (ψ CFSG.SectionRank.LargeRee.sl2Weyl : adjointGroup ReeTag.F4.tag K) =
      nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (CFSG.SectionRank.LargeRee.ix 0))) :
    ψ.range.map (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
      (octSystemOf hR).P₂ := by
  let ρ : ↥(reeFixed ReeTag.F4 K a) →* Gm K a :=
    (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom
  have hU : ∀ c, ρ (ψ (sl2Upper c)) ∈ (octSystemOf hR).P₂ := by
    intro c
    have hmem : ψ (sl2Upper c) ∈ Subgroup.closure
        ((CFSG.SectionRank.LargeRee.blockX (K := K) a 0 : Set
            (reeFixed ReeTag.F4 K a)) ∪
          {CFSG.SectionRank.LargeRee.relNrepHom K a
            (CFSG.SectionRank.LargeRee.blockGen 0)}) :=
      Subgroup.subset_closure (Or.inl (mem_blockX_zero_of_sl2Upper ψ hup c))
    exact closure_blockX_zero_octR2_image_le_P2 hR (Subgroup.mem_map_of_mem ρ hmem)
  have hW : ρ (ψ CFSG.SectionRank.LargeRee.sl2Weyl) ∈ (octSystemOf hR).P₂ := by
    have hP2 : ρ (CFSG.SectionRank.LargeRee.relNrepHom K a
        (CFSG.SectionRank.LargeRee.blockGen 0)) ∈ (octSystemOf hR).P₂ :=
      closure_blockX_zero_octR2_image_le_P2 hR
        (Subgroup.mem_map_of_mem ρ (Subgroup.subset_closure
          (Or.inr (Set.mem_singleton _))))
    have heq : ρ (ψ CFSG.SectionRank.LargeRee.sl2Weyl) =
        ρ (CFSG.SectionRank.LargeRee.relNrepHom K a
          (CFSG.SectionRank.LargeRee.blockGen 0)) :=
      map_sl2Weyl_eq_map_relNrepHom ψ hw
    rwa [heq]
  have hgen : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) ≤
      ((octSystemOf hR).P₂.comap ρ).comap ψ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := K),
      Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · rw [← sl2Upper_eq_componentInitial (K := K) c]
      exact hU c
    · rw [← sl2Lower_eq_componentInitial (K := K) c]
      change ρ (ψ (sl2Lower c)) ∈ (octSystemOf hR).P₂
      rw [sl2Lower_eq_sl2Weyl_mul_sl2Upper_mul_inv c, map_mul, map_mul, map_inv,
        map_mul, map_mul, map_inv]
      exact mul_mem (mul_mem hW (hU c)) (inv_mem hW)
  rw [Subgroup.map_le_iff_le_comap]
  intro y hy
  obtain ⟨g, rfl⟩ := hy
  exact hgen (Subgroup.mem_top g)

theorem exists_sl2_le_P2
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a,
      Function.Injective ψ ∧
      (∀ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) =
        xElement (CFSG.SectionRank.LargeRee.ix 0) c *
          xElement (CFSG.SectionRank.LargeRee.ix 3) (c ^ 2 ^ a)) ∧
      (∀ t : Kˣ, (ψ (CFSG.SectionRank.LargeRee.sl2Diag t) :
          adjointGroup ReeTag.F4.tag K) = ReeTag.F4.reeTorus a
            (CFSG.SectionRank.LargeRee.ix 0) t) ∧
      (ψ CFSG.SectionRank.LargeRee.sl2Weyl : adjointGroup ReeTag.F4.tag K) =
        nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (CFSG.SectionRank.LargeRee.ix 0)) ∧
      ψ.range.map (CFSG.Quasithin.A318P.reeFixedEquivGamma a).toMonoidHom ≤
        (octSystemOf hR).P₂ := by
  obtain ⟨ψ, hψ, hup, hlow, -, -, hdiag, hweyl⟩ :=
    CFSG.SectionRank.LargeRee.exists_sl2_rankOne (K := K) (a := a) hK
  exact ⟨ψ, hψ, hup, hdiag, hweyl, sl2_image_le_P2 hR hK ψ hup hlow hweyl⟩

end T3

end W80Model

end CFSG.Quasithin.Stroth
