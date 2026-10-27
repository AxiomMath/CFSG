module

public import CFSG.Quasithin.H13.NQCoreSChainOrbitsCore
public import CFSG.Quasithin.H13.NQCoreSChainSylow
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation
public import CFSG.Quasithin.H13.NQRigidAsmPair

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.NQRigid
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem generalizedFitting_eq_pCore_of_isLocal_map (hQ : quasithinIsQTKECat G) {T H : Subgroup G}
    (hT : quasithinIsSylowTwo T) {K : Subgroup ↥H} (hK : quasithinIsLocal T (K.map H.subtype)) :
    CFSG.generalizedFitting ↥K = CFSG.pCore 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := K.map H.subtype with hL
  have h1 := (quasithinGenFitting_eq_pCoreOf_iff L 2).mp
    (qt_full_Sylow_local_characteristic_two hQ hT hK).1
  have h2 := (CFSG.Quasithin.centralizer_pCore_le_iff_pCoreOf 2 L).mpr h1
  have hFL := (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mp h2
  let e : ↥K ≃* ↥L := K.equivMapOfInjective H.subtype H.subtype_injective
  rw [← CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv e.symm, hFL,
    CFSG.pCore_map_iso 2 e.symm]

theorem sylow_normalized_prime_residual_nonnormal_overgroup_component_orbits
    (hB1 : StmtEscapingComponentAction)
    (hB2 : StmtOuterRankContainment) (hB3 : StmtPairContainment)
    (hOD : StmtOuterDerivedCoprime) (hcen : FactCenterOddPart) (houter : FactOuterPrime)
    (hthin : FactThinCentralQuotient) (h36 : Vol2Native.A36CoreForSQTKCat) :
    StmtSCComponentOrbits := by
  intro G _ _ T D X P H p hS hH hXTH hXn hP
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.simple
  have hp := hS.prime
  have hp5 := hS.five_le
  have hC := hS.canonical
  set J := normalizer (D : Set G) with hJ
  have hXH : X ≤ H := le_sup_left.trans hXTH
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have hTJ : T ≤ J := hS.le_normalizer
  have hXJ : X ≤ J := hC.le.trans le_normalizer
  have hNX : normalizer (X : Set G) = J := hC.normalizer_eq.symm
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hHSQ : CFSG.SectionRank.IsSQTKCat ↥H :=
    (qt_positive_two_core_SQTK hS.nonabelian hS.qtke hH2).2
  have hT' : IsSylowTwoOf T ⊤ := isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow le_top
  have hcharH : CharTwo H := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hS.qtke.2.1 hT' hTH hH2
  have h4 : H ⊓ normalizer (X : Set G) = H ⊓ J := by rw [hNX]
  have h5 : H ⊓ J < H := by
    refine lt_of_le_of_ne inf_le_left fun heq => hXn ?_
    have hHJ : H ≤ J := heq ▸ (inf_le_right : H ⊓ J ≤ J)
    exact (normal_subgroupOf_iff_le_normalizer hXH).mpr (hHJ.trans hNX.ge)
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow hTH
  have h6 : pCoreOf 2 H ≤ pCoreOf 2 (X ⊔ T) := by
    have hOT : pCoreOf 2 H ≤ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTs
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
      (hXTH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  obtain ⟨hqT, -, hPT, hset, hfrat⟩ := sc_sylow_structure hS hP
  set X' := X.subgroupOf H with hX'
  set A := (H ⊓ J).subgroupOf H with hA
  have hirrX : IsFrattiniIrreducible X (H ⊓ J) :=
    IsFrattiniIrreducible.mono (H := T) hC.irreducible_T (le_inf hTH hTJ)
  obtain ⟨hX'2, hexp', hrk', hirr'⟩ :=
    subgroupOf_transport hXH (inf_le_left : H ⊓ J ≤ H) hC.noTwoQuotient hC.exponent hC.pRank
      hp.one_lt hirrX
  have hW' : Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) = p ^ 2 :=
    (card_frattini_subgroupOf hXH).trans hC.card_W
  have hX'A : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨x.2, hXJ (mem_subgroupOf.mp hx)⟩
  have hNA : normalizer (X' : Set ↥H) = A := by
    ext h
    constructor
    · intro hh
      have hhN : (h : G) ∈ normalizer (X : Set G) := by
        rw [mem_normalizer_iff]
        intro g
        by_cases hg : g ∈ H
        · have := mem_normalizer_iff.mp hh ⟨g, hg⟩
          simpa [hX', mem_subgroupOf] using this
        · have h1 : g ∉ X := fun hgX => hg (hXH hgX)
          have h2 : (h : G) * g * (h : G)⁻¹ ∉ X := fun hgX => hg (by
            have := H.mul_mem (H.mul_mem (H.inv_mem h.2) (hXH hgX)) h.2
            simpa [mul_assoc] using this)
          exact iff_of_false h1 h2
      rw [hNX] at hhN
      exact mem_subgroupOf.mpr (mem_inf.mpr ⟨h.2, hhN⟩)
    · intro hh
      rw [hA, mem_subgroupOf] at hh
      rw [mem_normalizer_iff]
      intro y
      simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
      exact mem_normalizer_iff.mp (hNX.ge (mem_inf.mp hh).2) y
  have hAlt : A < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => h5.ne ?_
    refine le_antisymm inf_le_left fun h hh => ?_
    have : (⟨h, hh⟩ : ↥H) ∈ A := htop ▸ mem_top _
    exact mem_subgroupOf.mp this
  have hTH2 : IsPGroup 2 (T.subgroupOf H) := hTs.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hTHi : ¬ 2 ∣ (T.subgroupOf H).index := hTs.2.2
  have hAS : ∃ S : Sylow 2 ↥H, (S : Subgroup ↥H) ≤ A := by
    refine ⟨hTH2.toSylow hTHi, ?_⟩
    rw [IsPGroup.toSylow_coe hTH2 hTHi]
    intro x hx
    rw [hA]
    exact mem_subgroupOf.mpr ⟨x.2, hTJ (mem_subgroupOf.mp hx)⟩
  have hXn' : (X'.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hX'A).mpr hNA.ge
  obtain ⟨hFA, hcomm, hcyc, K, hKc, hKq, hKA, hJc, hJX, hKC, hXK, hKXeq, hZ13, hbr⟩ :=
    sc_orbits_core hB1 hB2 hB3 hOD hcen houter hthin h36 hHSQ hp hp5 hX'A hXn' hAS hX'2 hexp'
      hrk' hW' hirr' hNA hAlt
  have hKG : K.map H.subtype ∈ cComp H :=
    map_subtype_mem_cComp (mem_cComp_top_iff_isCComponent.mpr hKc)
  have hKloc : quasithinIsLocal T (K.map H.subtype) := isLocal_of_mem_cComp_of_sylow hTs hH2 hKG
  have hKnot : ¬ K.map H.subtype ≤ J := by
    intro hle
    apply hKA
    intro k hk
    rw [hA, mem_subgroupOf]
    exact ⟨k.2, hle ⟨k, hk, rfl⟩⟩
  have hKF := generalizedFitting_eq_pCore_of_isLocal_map hS.qtke hS.sylow hKloc
  have hFit : ((CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H)).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype ≤ H ⊓ J := by
    refine (map_mono hFA).trans ?_
    rw [hA, subgroupOf_map_subtype]
    exact inf_le_left
  refine ⟨hH2, hHSQ, hcharH, h4, h5, h6, hPT, hset, hfrat, hFit, hcyc, hcomm, K, ?_⟩
  rcases hbr with ⟨hKn, hX'K, hrkJ⟩ | ⟨h₀, hh₀, hdich, hJ₂c, hK₁n, hK₂n, hK₀n, hXK₀, hXK₂,
      hrkK, hrkK₂, hrk₁, hrk₂, hthinJ, hcardX, hsplit⟩
  ·
    left
    exact
      { ccomp := hKc
        isLocal := hKloc
        normal := hKn
        not_le := hKnot
        genFitting := hKF
        quasi := hKq
        comp_e := hJc
        core_inf := hKC
        card_center := hZ13
        escapes_e := hJX
        le := hX'K
        comm_eq := hKXeq
        core_le_normalizer := by
          rw [normalizer_eq_top_iff.mpr hKn]
          exact le_top
        pRank := hrkJ }
  ·
    right
    set N := normalizer (K : Set ↥H) with hNdef
    have hh₀N : h₀ ∉ N := fun hm => hh₀ (conjugate_eq_self_iff.mpr hm)
    have hNidx : N.index = 2 := by
      rw [index_eq_two_iff']
      refine ⟨h₀, fun b => ?_⟩
      by_cases hb : b ∈ N
      · refine Or.inr ⟨hb, fun hab => hh₀N ?_⟩
        have := N.mul_mem hab (N.inv_mem hb)
        simpa [mul_assoc] using this
      · refine Or.inl ⟨?_, hb⟩
        have hKb : CFSG.conjugate K b = CFSG.conjugate K h₀ := by
          rcases hdich b with h1 | h1
          · exact absurd (conjugate_eq_self_iff.mp h1) hb
          · exact h1
        rcases hdich (h₀ * b) with h1 | h1
        · exact conjugate_eq_self_iff.mp h1
        · exfalso
          rw [← conjugate_conjugate] at h1
          have h2 : CFSG.conjugate (CFSG.conjugate K h₀) b = CFSG.conjugate K b := by
            rw [h1, hKb]
          exact hh₀ (conjugate_injective h2)
    obtain ⟨t₀, ht₀T, ht₀P, ht₀N⟩ : ∃ t₀ : G, ∃ h : t₀ ∈ T, t₀ ∈ normalizer (P : Set G) ∧
        (⟨t₀, hTH h⟩ : ↥H) ∉ N := by
      by_contra hall
      push Not at hall
      have hTN : T ≤ N.map H.subtype := by
        rw [hfrat]
        refine sup_le ?_ ?_
        · intro q hq
          have hqH : q ∈ H := hTH (hqT hq)
          have hqX : q ∈ X := (map_subtype_le _ : pCoreOf 2 X ≤ X) hq
          exact ⟨⟨q, hqH⟩, hXK (mem_subgroupOf.mpr hqX), rfl⟩
        · rintro s ⟨hsT, hsP⟩
          exact ⟨⟨s, hTH hsT⟩, hall s hsT hsP, rfl⟩
      have hTHN : T.subgroupOf H ≤ N := by
        intro x hx
        obtain ⟨y, hy, hyx⟩ := hTN (mem_subgroupOf.mp hx)
        rwa [show y = x from Subtype.ext hyx] at hy
      apply hTHi
      rw [← hNidx]
      exact index_dvd_of_le hTHN
    set t : ↥H := ⟨t₀, hTH ht₀T⟩ with ht
    have hKt : CFSG.conjugate K t ≠ K := fun h1 => ht₀N (conjugate_eq_self_iff.mp h1)
    have htK₂ : CFSG.conjugate K t = CFSG.conjugate K h₀ := by
      rcases hdich t with h1 | h1
      · exact absurd h1 hKt
      · exact h1
    rw [← htK₂] at hJ₂c hK₁n hK₂n hK₀n hXK₀ hXK₂ hrkK₂ hrk₂ hsplit
    have hdich' : ∀ g : ↥H, CFSG.conjugate K g = K ∨ CFSG.conjugate K g = CFSG.conjugate K t :=
      fun g => htK₂ ▸ hdich g
    have hP' : IsSylowOf p (P.subgroupOf H) X' :=
      (isSylowOf_subgroupOf_iff (hP.le.trans hXH) hXH).mpr hP
    obtain ⟨hPsup, hPinf, hP₁card, hP₂card⟩ := hsplit _ hP'
    set Y := X' ⊔ T.subgroupOf H with hY
    have hXY : X' ≤ Y := le_sup_left
    have hTHA : T.subgroupOf H ≤ A := fun x hx => by
      rw [hA]
      exact mem_subgroupOf.mpr ⟨x.2, hTJ (mem_subgroupOf.mp hx)⟩
    have hXYn : (X'.subgroupOf Y).Normal :=
      (normal_subgroupOf_iff_le_normalizer hXY).mpr
        (sup_le le_normalizer (hTHA.trans hNA.ge))
    have hperm : ∀ y : ↥H, ({CFSG.conjugate K y, CFSG.conjugate (CFSG.conjugate K t) y} :
        Set (Subgroup ↥H)) = {K, CFSG.conjugate K t} := by
      intro y
      have hKy := hdich' y
      have hK₂y : CFSG.conjugate (CFSG.conjugate K t) y = K ∨
          CFSG.conjugate (CFSG.conjugate K t) y = CFSG.conjugate K t := by
        rw [conjugate_conjugate]
        exact hdich' (t * y)
      have hne : CFSG.conjugate K y ≠ CFSG.conjugate (CFSG.conjugate K t) y := fun h1 =>
        hKt (conjugate_injective h1).symm
      rcases hKy with h1 | h1 <;> rcases hK₂y with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2]
      · rw [h1, h2, Set.pair_comm]
      · exact absurd (h1.trans h2.symm) hne
    have hcardX' : Nat.card (X' ⧸ CFSG.pCore 2 X') = p ^ 2 := hcardX
    obtain ⟨hfp, -, -, -, -, -, -⟩ :=
      SteinbergCD.normal_prime_core_fixes_ambient_coprime_plane_factor_pair Nat.prime_two hp
        (by omega) hXY hXYn hcardX' (fun y _ => hperm y) hXK hXK₂ hP' hPinf hP₁card hP₂card
    set RH := (pCoreOf 2 (X ⊔ T)).subgroupOf H with hRH
    have hXTsub : (X ⊔ T).subgroupOf H = Y := by rw [subgroupOf_sup hXH hTH]
    have hRY : RH ≤ Y := by
      rw [← hXTsub]
      intro r hr
      exact mem_subgroupOf.mpr ((map_subtype_le _ : pCoreOf 2 (X ⊔ T) ≤ X ⊔ T)
        (mem_subgroupOf.mp hr))
    have hRYn : (RH.subgroupOf Y).Normal := by
      refine (normal_subgroupOf_iff_le_normalizer hRY).mpr ?_
      rw [← hXTsub]
      exact subgroupOf_le_normalizer_of_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    have hR2 : IsPGroup 2 RH := by
      rw [hRH, ← comap_subtype]
      exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)).comap_subtype
    have hRK := (hfp RH hRY hRYn hR2).1
    have hcardXG : Nat.card (X ⧸ CFSG.pCore 2 X) = p ^ 2 := by
      rw [← Nat.card_congr (coreQuotEquivSubgroupOf hXH).toEquiv]
      exact hcardX
    refine ⟨t, ?_⟩
    exact
      { ccomp := hKc
        isLocal := hKloc
        mem := ⟨ht₀T, ht₀P⟩
        ne := hKt
        conj := hdich'
        not_le := hKnot
        genFitting := hKF
        quasi := hKq
        comp_e := hJc
        comp_e_conj := hJ₂c
        core_inf := hKC
        card_center := hZ13
        escapes_e := hJX
        normal_left := hK₁n
        normal_right := hK₂n
        normal_sup := hK₀n
        le_sup := hXK₀
        le_normalizer := le_inf hXK hXK₂
        comm_eq := hKXeq
        core_le_normalizer := hRK
        pRank_K := hrkK
        pRank_conj := hrkK₂
        pRank_S := hrk₁
        pRank_S₂ := hrk₂
        pRank_central := hthinJ
        elemAbelian := ⟨isElementaryAbelian_coreQuot hcardXG hC.exponent, hcardXG⟩
        eq_sup := hPsup
        inf_eq_bot := hPinf
        card_left := hP₁card
        card_right := hP₂card }

end CFSG.Quasithin.H13.NQCore
