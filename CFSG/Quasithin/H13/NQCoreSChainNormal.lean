module

public import CFSG.Quasithin.H13.NQCoreSChainCharNorm
public import CFSG.Quasithin.H13.NQCoreSChainNormalTools
public import CFSG.Quasithin.H13.NQRigidAsmSingleExcl
public import CFSG.Quasithin.H13.NQCoreSChainSylow
public import CFSG.Quasithin.H13.NQRigidAsmSubgroupOf
public import CFSG.Quasithin.H13.NQRigidAsmTransport
public import CFSG.Quasithin.SteinbergCDPermutableIntersection

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.NQRigid
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

theorem sylow_normalized_prime_residual_normal_component_exclusion
    (hTPC : NQBlock.StmtTwoPrimeCaptureConfinesCharNormalizer)
    (hCNC : NQBlock.StmtCharNormalizersConfined) (hcen : FactCenterOddPart)
    (hsect : FactSimpleQuotientSQT) (hQTE : QTESylow.StmtCatalogNoncyclicPrimeSylowProduct)
    (hB5 : StmtNoncyclicLocalSylowFourEven) (hB8 : StmtCPUOffenderSection)
    (hJ4 : StmtJ4SingleComponent) (hTits : StmtTitsSylowProduct) : StmtSCNormalExclusion := by
  intro G _ _ T D X H K p hS hH hXTH hXn hK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.simple
  have hp := hS.prime
  have hp5 := hS.five_le
  have hp2 : p ≠ 2 := by omega
  have hC := hS.canonical
  set J := normalizer (D : Set G) with hJ
  have hXH : X ≤ H := le_sup_left.trans hXTH
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have hTJ : T ≤ J := hS.le_normalizer
  have hXJ : X ≤ J := hC.le.trans le_normalizer
  have hNX : normalizer (X : Set G) = J := hC.normalizer_eq.symm
  have hTN : T ≤ normalizer (X : Set G) := hTJ.trans hNX.ge
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hHSQ : CFSG.SectionRank.IsSQTKCat ↥H :=
    (qt_positive_two_core_SQTK hS.nonabelian hS.qtke hH2).2
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow hTH
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p X
  obtain ⟨hqT, -, -, -, -⟩ := sc_sylow_structure hS hP
  set X' := X.subgroupOf H with hX'
  set A := (J ⊓ H).subgroupOf H with hA
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := hC.isPGroup
  have hX'A : IsPGroup p (X' ⧸ CFSG.pCore 2 X') := isPGroup_coreQuot_subgroupOf hXH hXA
  have hirrX : IsFrattiniIrreducible X (J ⊓ H) :=
    IsFrattiniIrreducible.mono (H := T) hC.irreducible_T (le_inf hTJ hTH)
  obtain ⟨-, hexp', -, hirrA'⟩ :=
    subgroupOf_transport hXH (inf_le_right : J ⊓ H ≤ H) hC.noTwoQuotient hC.exponent hC.pRank
      hp.one_lt hirrX
  obtain ⟨-, -, -, hirrT'⟩ :=
    subgroupOf_transport hXH hTH hC.noTwoQuotient hC.exponent hC.pRank hp.one_lt
      hC.irreducible_T
  have hW' : Nat.card ((X' ⧸ CFSG.pCore 2 X') ⧸ frattini (X' ⧸ CFSG.pCore 2 X')) = p ^ 2 :=
    (card_frattini_subgroupOf hXH).trans hC.card_W
  have hX'A' : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨hXJ (mem_subgroupOf.mp hx), x.2⟩
  have hAN : A ≤ normalizer (X' : Set ↥H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hNX.ge (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'n : (X'.subgroupOf A).Normal := (normal_subgroupOf_iff_le_normalizer hX'A').mpr hAN
  have hKn : K.Normal := hK.normal
  have hXK : X' ≤ K := hK.le
  have hKtop : normalizer (K : Set ↥H) = ⊤ := normalizer_eq_top_iff.mpr hKn
  have hTH2 : IsPGroup 2 (T.subgroupOf H) := hTs.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  have hTHi : ¬ 2 ∣ (T.subgroupOf H).index := hTs.2.2
  set Q' : Sylow 2 ↥H := hTH2.toSylow hTHi with hQ'def
  have hQ' : (Q' : Subgroup ↥H) = T.subgroupOf H := IsPGroup.toSylow_coe hTH2 hTHi
  have hTHA : T.subgroupOf H ≤ A := fun x hx =>
    mem_subgroupOf.mpr ⟨hTJ (mem_subgroupOf.mp hx), x.2⟩
  have hQ'A : (Q' : Subgroup ↥H) ≤ A := by
    rw [hQ']
    exact hTHA
  have hQ'top : IsSylowOf 2 (Q' : Subgroup ↥H) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
    exact ⟨le_top, Q'.isPGroup', Q'.not_dvd_index⟩
  have hQK : IsSylowOf 2 ((Q' : Subgroup ↥H) ⊓ K) K :=
    hQ'top.inf_of_le_normalizer le_top hKtop.ge
  set QX := (CFSG.pCore 2 X').map X'.subtype with hQX
  have hOT : QX ≤ T.subgroupOf H := by
    intro x hx
    rw [mem_subgroupOf]
    have h1 : (x : G) ∈ QX.map H.subtype := ⟨x, hx, rfl⟩
    rw [hQX, CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX',
      subgroupOf_map_subtype, inf_of_le_left hXH] at h1
    have h2 : (x : G) ∈ pCoreOf 2 X := by
      unfold CFSG.Open.pCoreOf
      exact h1
    exact hqT h2
  have hOQ : QX ≤ (Q' : Subgroup ↥H) := by
    rw [hQ']
    exact hOT
  have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
  have hZ : ¬ p ∣ Nat.card (center (K ⧸ CFSG.pCore 2 K)) := hcen _ hK.quasi hKSQ p hp hp5
  have hSs : IsSimpleGroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
    hK.quasi.2.1
  have hSnab := hK.quasi.2.2
  obtain ⟨hSsqt, hScat⟩ := hsect _ hKSQ (center _) hSs hSnab
  have hσker := not_dvd_card_ker_coreCenterQuot hp hp2 hZ
  set PH := P.subgroupOf H with hPHdef
  have hPH : IsSylowOf p PH X' := (isSylowOf_subgroupOf_iff (hP.le.trans hXH) hXH).mpr hP
  have hPHX : PH ≤ X' := hPH.le
  have hPHK : PH ≤ K := hPHX.trans hXK
  have hPQ' : (PH : Set ↥H) * ((Q' : Subgroup ↥H) : Set ↥H) =
      ((Q' : Subgroup ↥H) : Set ↥H) * (PH : Set ↥H) :=
    mul_comm_sylow_of_core_le hX'A hPH (hQ'A.trans hAN) hOQ
  have hcop : Nat.Coprime (Nat.card PH) (Nat.card (Q' : Subgroup ↥H)) := by
    obtain ⟨a, ha⟩ := hPH.isPGroup.exists_card_eq
    obtain ⟨b, hb⟩ := Q'.isPGroup'.exists_card_eq
    rw [ha, hb]
    exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hPN : PH ≤ normalizer (K : Set ↥H) := by
    rw [hKtop]
    exact le_top
  obtain ⟨-, -, hPQK⟩ :=
    SteinbergCD.coprime_permutable_product_normalized_subgroup_intersection hcop hPQ' hPN
  rw [inf_of_le_left hPHK] at hPQK
  obtain ⟨QKs, hQKs⟩ := hQK.exists_sylow_eq_subgroupOf
  have hPQKK : ((PH.subgroupOf K : Subgroup K) : Set K) * ((QKs : Subgroup K) : Set K) =
      ((QKs : Subgroup K) : Set K) * ((PH.subgroupOf K : Subgroup K) : Set K) := by
    apply Set.image_injective.mpr K.subtype_injective
    rw [Set.image_mul, Set.image_mul, ← coe_map, ← coe_map, hQKs, subgroupOf_map_subtype,
      subgroupOf_map_subtype, inf_of_le_left hPHK, inf_of_le_left inf_le_right, hPQK]
  have hPKp : IsPGroup p (PH.subgroupOf K) := by
    rw [← comap_subtype]
    exact hPH.isPGroup.comap_subtype
  have hPHnc : ¬ IsCyclic PH := NQCat.not_isCyclic_of_isSylowOf_of_card_eq_sq hX'A hW' hPH
  have hPKnc : ¬ IsCyclic (PH.subgroupOf K) := fun hc =>
    hPHnc (isCyclic_of_surjective (subgroupOfEquivOfLe hPHK).toMonoidHom
      (subgroupOfEquivOfLe hPHK).surjective)
  have hσinj := injective_of_not_dvd_card_ker hp (coreCenterQuot K) hσker hPKp
  set AS := (PH.subgroupOf K).map (coreCenterQuot K) with hAS
  have hrange : ((coreCenterQuot K).comp (PH.subgroupOf K).subtype).range = AS := by
    rw [MonoidHom.range_comp, range_subtype]
  let eA : PH.subgroupOf K ≃* AS :=
    (MonoidHom.ofInjective hσinj).trans (MulEquiv.subgroupCongr hrange)
  have hASp : IsPGroup p AS := hPKp.map _
  have hASnc : ¬ IsCyclic AS := fun hc =>
    hPKnc (isCyclic_of_surjective eA.symm.toMonoidHom eA.symm.surjective)
  set US := QKs.mapSurjective (coreCenterQuot_surjective K) with hUS
  have hAU : (AS : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
      ((US : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
      ((US : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
        ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) * AS := by
    rw [hUS, Sylow.coe_mapSurjective, hAS]
    exact map_mul_comm_of_mul_comm (coreCenterQuot K) hPQKK
  have hCC := sylow_normalized_prime_residual_characteristic_normalizers_and_core_control hTPC hCNC
    hS
  set R := pCoreOf 2 (X ⊔ T) with hRdef
  have hRH : R ≤ H := (map_subtype_le _).trans hXTH
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T)
  have hRH2 : IsPGroup 2 (R.subgroupOf H) := by
    rw [← comap_subtype]
    exact hR2.comap_subtype
  have hRpush' : R = (CFSG.pCore 2 (H ⊓ normalizer (R : Set G) : Subgroup G)).map
      (H ⊓ normalizer (R : Set G)).subtype := by
    exact (hCC.local_core H hXTH).symm
  have hRpush := eq_pCore_normalizer_subgroupOf hRH hRpush'
  have hRchar := normalizer_le_subgroupOf_of_characteristic (M := J) hRH (fun D' hD' hD1 => by
    have hD'R : D'.map R.subtype ≤ R := map_subtype_le _
    have hD'c : ((D'.map R.subtype).subgroupOf R).Characteristic := by
      rw [show (D'.map R.subtype).subgroupOf R = D' from
        comap_map_eq_self_of_injective R.subtype_injective D']
      exact hD'
    have hD'ne : D'.map R.subtype ≠ ⊥ := by
      rw [Ne, map_eq_bot_iff_of_injective _ R.subtype_injective]
      exact hD1
    exact hCC.char_normalizer_le _ hD'ne hD'R hD'c)
  have hKA : ¬ K ≤ A := by
    intro hle
    apply hK.not_le
    rintro _ ⟨k, hk, rfl⟩
    exact (mem_inf.mp (mem_subgroupOf.mp (hle hk))).1
  have hRK : R.subgroupOf H ≤ normalizer (K : Set ↥H) := by
    rw [hKtop]
    exact le_top
  have hnc : ¬ IsCyclic (((Q' : Subgroup ↥H).subgroupOf (normalizer (X' : Set ↥H))).map
      (normalizerFrattiniConj X')) := by
    rw [hQ']
    intro hc
    exact sc_image_not_isCyclic hS
      ((isCyclic_congr (imageEquivSubgroupOf hXH hTH hTN)).mp hc)
  rcases hQTE _ hSnab hScat hSsqt p hp hp5 US AS hASp hASnc hAU with
    ⟨ℓ, hℓ, hℓ5, hSm⟩ | ⟨f, -, hSm⟩ | ⟨f, hf, hSm⟩ | (⟨f, hf, hSm⟩ | ⟨f, hf, hSm⟩) |
      (⟨a, ha, hSm⟩ | hSm) | ⟨⟨ψ₀⟩, -⟩
  ·
    obtain ⟨W, _, _, _, _, L₁, B₁, hLq, hirr, hBe, hB1, hBN, -, hoff, ⟨e⟩⟩ :=
      hB8 ↥H (R.subgroupOf H) hRH2 hRpush K hK.ccomp hK.genFitting hK.quasi hRK A hKA hRchar
    exact offender_excludes_odd_three L₁ B₁ hLq hirr hBe hB1 hBN hoff e hℓ hℓ5 hSm
  ·
    have hTXN : T.subgroupOf H ≤ normalizer (X' : Set ↥H) := hTHA.trans hAN
    have hirrN := isFrattiniIrreducible_inf_normalizer hX'A hTXN hOT hPH hirrT'
    have hTK : T.subgroupOf H ≤ normalizer (K : Set ↥H) := by
      rw [hKtop]
      exact le_top
    exact not_statedClassicalModel_linear_three hp hp5 hXK hTK hTH2 hX'A hexp' hW' hZ hPH hirrN
      Nat.prime_two (Ne.symm hp2) f hSm
  ·
    exact (hB5 ↥H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A hnc hZ).1 f hf hSm
  ·
    exact (hB5 ↥H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A hnc hZ).2.1 f hf hSm
  ·
    exact (hB5 ↥H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A hnc hZ).2.2.1 f hf hSm
  ·
    exact (hB5 ↥H p hp hp5 A Q' hQ'A K X' hX'A' hX'n hXK hX'A hnc hZ).2.2.2 a ha hSm
  ·
    exact hTits K _ p hp hp2 (coreCenterQuot K) (coreCenterQuot_surjective K) hσker
      (PH.subgroupOf K) hPKp hPKnc QKs hPQKK hSm
  ·
    have hDK : A ≤ normalizer (K : Set ↥H) := by
      rw [hKtop]
      exact le_top
    exact (hJ4 ↥H A K X' hDK hX'A' hX'n hXK p hp hp5 hX'A hW'.ge hirrA' hZ PH
      ((Q' : Subgroup ↥H) ⊓ K) hPH hQK hPQK).false ψ₀

end CFSG.Quasithin.H13.NQCore
