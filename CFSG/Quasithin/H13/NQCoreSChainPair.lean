module

public import CFSG.Quasithin.H13.NQCoreSChainCharNorm
public import CFSG.Quasithin.H13.NQCoreSChainSylow
public import CFSG.Quasithin.H13.NQRigidAsmPair

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.NQRigid
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped Pointwise

theorem sylow_normalized_prime_residual_paired_component_exclusion
    (hTPC : NQBlock.StmtTwoPrimeCaptureConfinesCharNormalizer)
    (hCNC : NQBlock.StmtCharNormalizersConfined) (hcen : FactCenterOddPart)
    (hsect : FactSimpleQuotientSQT) (hquad : FactQuadraticOffender)
    (hB8 : StmtCPUOffenderSection) (hB9 : StmtCPUShortBlock) : StmtSCPairedExclusion := by
  intro G _ _ T D X P H K t p hS hH hXTH hXn hP hK
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.simple
  have hp := hS.prime
  have hp5 := hS.five_le
  have hp2 : p ≠ 2 := by omega
  have hC := hS.canonical
  have hAmb := hS.ambient
  set J := normalizer (D : Set G) with hJ
  have hXH : X ≤ H := le_sup_left.trans hXTH
  have hTH : T ≤ H := le_sup_right.trans hXTH
  have hTJ : T ≤ J := hS.le_normalizer
  have hXJ : X ≤ J := hC.le.trans le_normalizer
  have hNX : normalizer (X : Set G) = J := hC.normalizer_eq.symm
  have hH2 : pCoreOf 2 H ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hHSQ : CFSG.SectionRank.IsSQTKCat ↥H :=
    (qt_positive_two_core_SQTK hS.nonabelian hS.qtke hH2).2
  have hTs : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow hTH
  obtain ⟨hqT, -, -, -, -⟩ := sc_sylow_structure hS hP
  set X' := X.subgroupOf H with hX'
  set A := (J ⊓ H).subgroupOf H with hA
  set C := CFSG.pCore 2 ↥H with hCdef
  set π := QuotientGroup.mk' C with hπ
  have hC2 : IsPGroup 2 C := CFSG.pCore_isPGroup
  have hCn : C.Normal := CFSG.pCore_normal
  have hCsolv : Group.IsSolvable C := by
    have : Group.IsNilpotent C := hC2.isNilpotent
    infer_instance
  have hXA : IsPGroup p (X ⧸ CFSG.pCore 2 X) := hC.isPGroup
  have hX'A : IsPGroup p (X' ⧸ CFSG.pCore 2 X') := isPGroup_coreQuot_subgroupOf hXH hXA
  have hirrX : IsFrattiniIrreducible X (J ⊓ H) :=
    IsFrattiniIrreducible.mono (H := T) hC.irreducible_T (le_inf hTJ hTH)
  obtain ⟨hX'2, hexp', -, -⟩ :=
    subgroupOf_transport hXH (inf_le_right : J ⊓ H ≤ H) hC.noTwoQuotient hC.exponent hC.pRank
      hp.one_lt hirrX
  have hX'O2 : CFSG.pCore 2 X' ≠ ⊥ := by
    intro h0
    apply hC.pCore_ne_bot
    rw [← CFSG.pCore_map_iso 2 (subgroupOfEquivOfLe hXH), h0, Subgroup.map_bot]
  have hX'A' : X' ≤ A := fun x hx => mem_subgroupOf.mpr ⟨hXJ (mem_subgroupOf.mp hx), x.2⟩
  have hAN : A ≤ normalizer (X' : Set ↥H) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro y
    simp only [hX', mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp (hNX.ge (mem_inf.mp (mem_subgroupOf.mp ha)).1) y
  have hX'Cn : (CFSG.pCore 2 X').Normal := CFSG.pCore_normal
  set QX := (CFSG.pCore 2 X').map X'.subtype with hQX
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
  have hRK : R.subgroupOf H ≤ normalizer (K : Set ↥H) := hK.core_le_normalizer.trans inf_le_left
  set K₂ := CFSG.conjugate K t with hK₂
  have hK₂c : CFSG.IsCComponent K₂ := isCComponent_conjugate hK.ccomp t
  have hdich := hK.conj
  set J₁ := K.map π with hJ₁
  set J₂ := K₂.map π with hJ₂
  have hJne : J₁ ≠ J₂ := fun heq =>
    hK.ne (eq_of_map_eq_of_isCComponent hCsolv hK₂c hK.ccomp heq.symm)
  have hJcomm : ⁅J₁, J₂⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hK.comp_e hK.comp_e_conj with h1 | h1
    · exact absurd h1 hJne
    · exact h1
  have hK₂N : K₂ ≤ normalizer (K : Set ↥H) :=
    normalizer_ge_of_commute_images hCsolv hK.ccomp hJcomm
  have hperm : ∀ y : ↥H, ({CFSG.conjugate K y, CFSG.conjugate K₂ y} :
      Set (Subgroup ↥H)) = {K, K₂} := by
    intro y
    have hKy := hdich y
    have hK₂y : CFSG.conjugate K₂ y = K ∨ CFSG.conjugate K₂ y = K₂ := by
      rw [hK₂, conjugate_conjugate]
      exact hdich (t * y)
    have hne : CFSG.conjugate K y ≠ CFSG.conjugate K₂ y := fun h1 =>
      hK.ne (conjugate_injective h1).symm
    rcases hKy with h1 | h1 <;> rcases hK₂y with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, h2]
    · rw [h1, h2, Set.pair_comm]
    · exact absurd (h1.trans h2.symm) hne
  set PH := P.subgroupOf H with hPHdef
  have hPH : IsSylowOf p PH X' := (isSylowOf_subgroupOf_iff (hP.le.trans hXH) hXH).mpr hP
  have hPHX : PH ≤ X' := hPH.le
  have hPsup' : (PH ⊓ K) ⊔ (PH ⊓ K₂) = PH := hK.eq_sup
  have hPinf : (PH ⊓ K) ⊓ (PH ⊓ K₂) = ⊥ := hK.inf_eq_bot
  have hP₁card : Nat.card (PH ⊓ K : Subgroup ↥H) = p := hK.card_left
  have hP₂card : Nat.card (PH ⊓ K₂ : Subgroup ↥H) = p := hK.card_right
  have hXK₀ : X' ≤ K ⊔ K₂ := hK.le_sup
  have hK₀n : (K ⊔ K₂).Normal := hK.normal_sup
  have hK₁K₀ : K ≤ K ⊔ K₂ := le_sup_left
  have hKK₂ : ⁅K, K₂⁆ = ⊥ := by
    have hF := hK.genFitting
    obtain ⟨W, _, _, _, _, L₁, B₁, hLq, hirr, hBe, hB1, hBN, hquadB, hoff, ⟨e⟩⟩ :=
      hB8 ↥H (R.subgroupOf H) hRH2 hRpush K hK.ccomp hF hK.quasi hRK A hKA hRchar
    have : Finite (Module.End (ZMod 2) W) :=
      Finite.of_injective (fun f : Module.End (ZMod 2) W => (f : W → W)) LinearMap.coe_injective
    have hKSQ := isSQTKCat_subgroup_quotient_pCore hHSQ K
    have hSs : IsSimpleGroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
      hK.quasi.2.1
    have hSnab := hK.quasi.2.2
    obtain ⟨-, hScat⟩ := hsect _ hKSQ (center _) hSs hSnab
    have hcap : (CFSG.pCore 2 K).map K.subtype = K ⊓ π.ker := by
      rw [hπ, QuotientGroup.ker_mk']
      exact hK.core_inf.symm
    obtain ⟨eJ⟩ := NQBlock.nonempty_quotient_mulEquiv π rfl (CFSG.pCore 2 K) hcap
    let eS : ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) ≃* (J₁ ⧸ center J₁) :=
      QuotientGroup.congr _ _ eJ (map_center_mulEquiv eJ)
    have hthinS : ∀ r : ℕ, r.Prime → r ≠ 2 →
        CFSG.pRank r (L₁ ⧸ center L₁) ≤ 1 := by
      intro r hr hr2
      rw [pRank_congr hr.one_lt (e.trans eS)]
      exact hK.pRank_central r hr hr2
    have hcatL : CFSG.Blueprint.Catalog (L₁ ⧸ center L₁) :=
      (CFSG.SectionRank.catalog_congr e).mpr hScat
    have hP₁K : PH ⊓ K ≤ K := inf_le_right
    have hP₁p : IsPGroup p ((PH ⊓ K).subgroupOf K) := by
      rw [← comap_subtype]
      exact (hPH.isPGroup.to_le inf_le_left).comap_subtype
    have hσker := not_dvd_card_ker_coreCenterQuot hp hp2 (hcen _ hK.quasi hKSQ p hp hp5)
    have hσinj := injective_of_not_dvd_card_ker hp (coreCenterQuot K) hσker hP₁p
    set D₀ := ((PH ⊓ K).subgroupOf K).map (coreCenterQuot K) with hD₀
    have hrange : ((coreCenterQuot K).comp ((PH ⊓ K).subgroupOf K).subtype).range = D₀ := by
      rw [MonoidHom.range_comp, range_subtype]
    have hD₀card : Nat.card D₀ = p := by
      rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hσinj).toEquiv,
        card_subgroupOf_of_le hP₁K]
      exact hP₁card
    have hTH2 : IsPGroup 2 (T.subgroupOf H) := hTs.2.1.of_equiv (subgroupOfEquivOfLe hTH).symm
    have hTHi : ¬ 2 ∣ (T.subgroupOf H).index := hTs.2.2
    set Q' : Sylow 2 ↥H := hTH2.toSylow hTHi with hQ'def
    have hQ' : (Q' : Subgroup ↥H) = T.subgroupOf H := IsPGroup.toSylow_coe hTH2 hTHi
    have hQ'A : (Q' : Subgroup ↥H) ≤ A := by
      rw [hQ']
      intro x hx
      exact mem_subgroupOf.mpr ⟨hTJ (mem_subgroupOf.mp hx), x.2⟩
    have hQ'top : IsSylowOf 2 (Q' : Subgroup ↥H) ⊤ := by
      rw [CFSG.ABGLocalTools.isSylowOf_iff, relIndex_top_right]
      exact ⟨le_top, Q'.isPGroup', Q'.not_dvd_index⟩
    have hQK₀ : IsSylowOf 2 ((Q' : Subgroup ↥H) ⊓ (K ⊔ K₂)) (K ⊔ K₂) :=
      hQ'top.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hK₀n).ge
    have hQK : IsSylowOf 2 ((Q' : Subgroup ↥H) ⊓ K) K := by
      have h1 := hQK₀.inf_of_le_normalizer hK₁K₀ (sup_le le_normalizer hK₂N)
      rwa [inf_assoc, inf_of_le_right hK₁K₀] at h1
    have hOQ : QX ≤ (Q' : Subgroup ↥H) := by
      rw [hQ']
      intro x hx
      rw [mem_subgroupOf]
      have h1 : (x : G) ∈ QX.map H.subtype := ⟨x, hx, rfl⟩
      rw [hQX, CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX',
        subgroupOf_map_subtype, inf_of_le_left hXH] at h1
      have h2 : (x : G) ∈ pCoreOf 2 X := by
        unfold CFSG.Open.pCoreOf
        exact h1
      exact hqT h2
    have hPQ' : (PH : Set ↥H) * ((Q' : Subgroup ↥H) : Set ↥H) =
        ((Q' : Subgroup ↥H) : Set ↥H) * (PH : Set ↥H) :=
      mul_comm_sylow_of_core_le hX'A hPH (hQ'A.trans hAN) hOQ
    have hcop : Nat.Coprime (Nat.card PH) (Nat.card (Q' : Subgroup ↥H)) := by
      obtain ⟨a, ha⟩ := hPH.isPGroup.exists_card_eq
      obtain ⟨b, hb⟩ := Q'.isPGroup'.exists_card_eq
      rw [ha, hb]
      exact Nat.Coprime.pow a b ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    obtain ⟨-, -, hPQK⟩ :=
      SteinbergCD.coprime_permutable_product_normalized_subgroup_intersection hcop hPQ'
        (hPHX.trans (hK.le_normalizer.trans inf_le_left))
    obtain ⟨QKs, hQKs⟩ := hQK.exists_sylow_eq_subgroupOf
    have hPQKK : (((PH ⊓ K).subgroupOf K : Subgroup K) : Set K) * ((QKs : Subgroup K) : Set K) =
        ((QKs : Subgroup K) : Set K) * (((PH ⊓ K).subgroupOf K : Subgroup K) : Set K) := by
      apply Set.image_injective.mpr K.subtype_injective
      rw [Set.image_mul, Set.image_mul, ← coe_map, ← coe_map, hQKs, subgroupOf_map_subtype,
        subgroupOf_map_subtype, inf_of_le_left hP₁K, inf_of_le_left inf_le_right, hPQK]
    set T₀ := QKs.mapSurjective (coreCenterQuot_surjective K) with hT₀
    have hDT₀ : (D₀ : Set ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
        ((T₀ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
          ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) =
        ((T₀ : Subgroup ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) : Set
          ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K))) *
          D₀ := by
      rw [hT₀, Sylow.coe_mapSurjective, hD₀]
      exact map_mul_comm_of_mul_comm (coreCenterQuot K) hPQKK
    set Dℓ := D₀.map e.symm.toMonoidHom with hDℓ
    have hDcard : Nat.card Dℓ = p := by
      rw [hDℓ, card_map_of_injective e.symm.injective, hD₀card]
    have hes : Function.Surjective e.symm.toMonoidHom := e.symm.surjective
    set Tℓ := T₀.mapSurjective hes with hTℓ
    have hDT : (Dℓ : Set (L₁ ⧸ center L₁)) *
        ((Tℓ : Subgroup (L₁ ⧸ center L₁)) : Set (L₁ ⧸ center L₁)) =
        ((Tℓ : Subgroup (L₁ ⧸ center L₁)) : Set (L₁ ⧸ center L₁)) *
          (Dℓ : Set (L₁ ⧸ center L₁)) := by
      rw [hTℓ, Sylow.coe_mapSurjective, hDℓ]
      exact map_mul_comm_of_mul_comm e.symm.toMonoidHom hDT₀
    obtain ⟨f, hf, F, hFf, hFt, hFcard, ⟨θ⟩⟩ := hquad W L₁ hLq hirr hcatL hthinS p hp hp5 Dℓ
      hDcard Tℓ hDT B₁ hBe hB1 hBN hquadB hoff
    have hShort := hB9 ↥H (R.subgroupOf H) hRH2 hRpush K hK.ccomp hF hK.quasi hRK A hKA
      hRchar f hf F hFcard ⟨e.symm.trans θ⟩
    exact NQTerm.short_Ccomponent_centralizes_every_distinct_Ccomponent hK.ccomp hK₂c
      (Ne.symm hK.ne) hShort
  have htA : t ∈ A := mem_subgroupOf.mpr ⟨hTJ (mem_inf.mp hK.mem).1, t.2⟩
  have hK₁h : CFSG.conjugate K t = K₂ := rfl
  have hK₂h : CFSG.conjugate K₂ t = K := by
    have h1 := hperm t
    rw [hK₁h] at h1
    have h2 : CFSG.conjugate K₂ t ∈ ({K, K₂} : Set (Subgroup ↥H)) := by
      rw [← h1]
      exact Set.mem_insert_of_mem _ rfl
    rcases h2 with h2 | h2
    · exact h2
    · exfalso
      apply hK.ne
      exact conjugate_injective (h2.trans hK₁h.symm)
  have hXQP : QX ⊔ PH = X' := by
    apply le_antisymm (sup_le (map_subtype_le _) hPHX)
    intro x hx
    obtain ⟨y, hyP, hyx⟩ := NQSetup.exists_mem_sylow_mk_eq hX'A hPH ⟨x, hx⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyx
    have h1 : (y : ↥H)⁻¹ * x ∈ QX := ⟨y⁻¹ * ⟨x, hx⟩, QuotientGroup.eq.mp hyx, rfl⟩
    have h2 : x = (y : ↥H) * ((y : ↥H)⁻¹ * x) := by group
    rw [h2]
    exact mul_mem (le_sup_right (a := QX) hyP) (le_sup_left (b := PH) h1)
  have hQX1 : QX ≠ ⊥ := by
    rw [hQX, Ne, map_eq_bot_iff_of_injective _ X'.subtype_injective]
    exact hX'O2
  obtain ⟨hA₁K, hA₂K, hPA₁, hPA₂, hQA₁A₂, hA₁A₂, hA₁P₂, hA₂P₁, hA₁P₁, hA₂P₂, -⟩ :=
    SteinbergCD.commuting_swapped_factors_produce_full_core_supports Nat.prime_two hp
      (Ne.symm hp2) hKK₂ hXK₀ hQX1 hX'2 hPH hXQP hP₁card hP₂card hPsup' (hAN htA) hK₁h hK₂h
  set φ : Subgroup ↥H → Subgroup ↥D := fun S => (S.map H.subtype).subgroupOf D with hφ
  have hXL : X ≤ D := hC.le
  have hX'G : X'.map H.subtype = X := by
    rw [hX', subgroupOf_map_subtype, inf_of_le_left hXH]
  have hleL : ∀ S : Subgroup ↥H, S ≤ X' → S.map H.subtype ≤ D := fun S hS =>
    (map_mono hS).trans (hX'G.le.trans hXL)
  have hQXG : QX.map H.subtype = (CFSG.pCore 2 X).map X.subtype := by
    rw [hQX, CFSG.LocalAnalysis.GorensteinLyons.map_subtype_pCore_map, hX'G]
  have hQXL : φ QX = (CFSG.pCore 2 (X.subgroupOf D)).map (X.subgroupOf D).subtype := by
    rw [pCore_subgroupOf_of_le hXL]
    show (QX.map H.subtype).subgroupOf D = _
    rw [hQXG]
  have hφle : ∀ {S₁ S₂ : Subgroup ↥H}, S₁ ≤ S₂ → φ S₁ ≤ φ S₂ := fun h12 =>
    comap_mono (map_mono h12)
  have hφcard : ∀ S : Subgroup ↥H, S ≤ X' → Nat.card (φ S) = Nat.card S := fun S hS => by
    rw [hφ]
    dsimp only
    rw [card_subgroupOf_of_le (hleL S hS), card_map_of_injective H.subtype_injective]
  have hφsup : ∀ S₁ S₂ : Subgroup ↥H, S₁ ≤ X' → S₂ ≤ X' → φ (S₁ ⊔ S₂) = φ S₁ ⊔ φ S₂ :=
    fun S₁ S₂ h₁ h₂ => by
      rw [hφ]
      dsimp only
      rw [Subgroup.map_sup, subgroupOf_sup (hleL S₁ h₁) (hleL S₂ h₂)]
  have hφinf : ∀ S₁ S₂ : Subgroup ↥H, φ (S₁ ⊓ S₂) = φ S₁ ⊓ φ S₂ := fun S₁ S₂ => by
    rw [hφ]
    dsimp only
    rw [Subgroup.map_inf_eq _ _ _ H.subtype_injective, subgroupOf_inf]
  have hφbot : ∀ S : Subgroup ↥H, S ≤ X' → (φ S = ⊥ ↔ S = ⊥) := fun S hS => by
    rw [hφ]
    dsimp only
    rw [subgroupOf_eq_bot_iff_of_le (hleL S hS), map_eq_bot_iff_of_injective _
      H.subtype_injective]
  have hφcomm : ∀ S₁ S₂ : Subgroup ↥H, S₁ ≤ X' → S₂ ≤ X' → φ ⁅S₁, S₂⁆ = ⁅φ S₁, φ S₂⁆ :=
    fun S₁ S₂ h₁ h₂ => by
      rw [hφ]
      dsimp only
      rw [map_commutator, subgroupOf_commutator_of_le (hleL S₁ h₁) (hleL S₂ h₂)]
  have hφnorm : ∀ S₁ S₂ : Subgroup ↥H, S₁ ≤ normalizer (S₂ : Set ↥H) →
      φ S₁ ≤ normalizer ((φ S₂ : Subgroup ↥D) : Set ↥D) := fun S₁ S₂ h12 =>
    subgroupOf_le_normalizer_of_le ((map_mono h12).trans (le_normalizer_map _))
  have hφmul : ∀ S₀ S₁ S₂ : Subgroup ↥H, S₀ ≤ X' → S₁ ≤ X' → S₂ ≤ X' →
      (S₀ : Set ↥H) = (S₁ : Set ↥H) * (S₂ : Set ↥H) →
      ((φ S₀ : Subgroup ↥D) : Set ↥D) =
        ((φ S₁ : Subgroup ↥D) : Set ↥D) * ((φ S₂ : Subgroup ↥D) : Set ↥D) :=
    fun S₀ S₁ S₂ h₀ h₁ h₂ h012 => by
      refine coe_subgroupOf_mul_of_le (hleL S₀ h₀) (hleL S₁ h₁) (hleL S₂ h₂) ?_
      rw [coe_map, coe_map, coe_map, h012, Set.image_mul]
  have hP₁X : PH ⊓ K ≤ X' := inf_le_left.trans hPHX
  have hP₂X : PH ⊓ K₂ ≤ X' := inf_le_left.trans hPHX
  have hQXX : QX ≤ X' := map_subtype_le _
  have hA₁X : ⁅QX, PH ⊓ K⁆ ≤ X' := (hA₁K.trans inf_le_left).trans hQXX
  have hA₂X : ⁅QX, PH ⊓ K₂⁆ ≤ X' := (hA₂K.trans inf_le_left).trans hQXX
  have hLperf : Group.IsPerfect ↥D :=
    ⟨by rw [_root_.commutator_def]; exact hAmb.isCComponent_top.2.1⟩
  have hXLn : (X.subgroupOf D).Normal := by
    have := hC.characteristic
    infer_instance
  have hXLexp : Monoid.exponent (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D)) = p := by
    rw [Monoid.exponent_eq_of_mulEquiv (coreQuotEquivSubgroupOf hXL), hC.exponent]
  have hXLcard : Nat.card (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D)) = p ^ 2 := by
    rw [Nat.card_congr (coreQuotEquivSubgroupOf hXL).toEquiv]
    exact hK.elemAbelian.2
  have hWL : Nat.card ((X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D)) ⧸
      frattini (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D))) = p ^ 2 := by
    rw [card_frattini_subgroupOf hXL, hC.card_W]
  have hΦ : frattini (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D)) = ⊥ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (frattini (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D)))
    rw [hXLcard, hWL] at h1
    have hpos : 0 < p ^ 2 := by positivity
    have h2 : Nat.card (frattini (X.subgroupOf D ⧸ CFSG.pCore 2 (X.subgroupOf D))) = 1 :=
      Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans (mul_one _).symm)
    exact Subgroup.eq_bot_of_card_eq _ h2
  have hirrL := coreQuotConj_irreducible_of hΦ
    (frattiniQuotConj_irreducible_of hXL hC.irreducible_D)
  have hXe := isElementaryAbelian_coreQuot hXLcard hXLexp
  have hSylL : IsSylowOf p (φ PH) (X.subgroupOf D) := by
    have h1 : IsSylowOf p (PH.map H.subtype) X := by
      rw [← hX'G]
      exact (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mpr hPH
    exact (isSylowOf_subgroupOf_iff (hleL PH hPHX) hXL).mpr h1
  have hP₁L : Nat.card (φ (PH ⊓ K)) = p := by rw [hφcard _ hP₁X, hP₁card]
  have hP₂L : Nat.card (φ (PH ⊓ K₂)) = p := by rw [hφcard _ hP₂X, hP₂card]
  have hsupL : φ (PH ⊓ K) ⊔ φ (PH ⊓ K₂) = φ PH := by rw [← hφsup _ _ hP₁X hP₂X, hPsup']
  have hinfL : φ (PH ⊓ K) ⊓ φ (PH ⊓ K₂) = ⊥ := by
    rw [← hφinf, hPinf, hφbot ⊥ bot_le]
  have hP₁₂ : ⁅PH ⊓ K, PH ⊓ K₂⁆ = ⊥ :=
    le_bot_iff.mp ((commutator_mono inf_le_right inf_le_right).trans hKK₂.le)
  have hcommL : ⁅φ (PH ⊓ K), φ (PH ⊓ K₂)⁆ = ⊥ := by
    rw [← hφcomm _ _ hP₁X hP₂X, hP₁₂, hφbot ⊥ bot_le]
  have hA₁L : φ ⁅QX, PH ⊓ K⁆ ≤ (CFSG.pCore 2 (X.subgroupOf D)).map (X.subgroupOf D).subtype := by
    rw [← hQXL]
    exact hφle (hA₁K.trans inf_le_left)
  have hA₂L : φ ⁅QX, PH ⊓ K₂⁆ ≤
      (CFSG.pCore 2 (X.subgroupOf D)).map (X.subgroupOf D).subtype := by
    rw [← hQXL]
    exact hφle (hA₂K.trans inf_le_left)
  have hprodL : (((CFSG.pCore 2 (X.subgroupOf D)).map (X.subgroupOf D).subtype : Subgroup ↥D) :
      Set ↥D) = ((φ ⁅QX, PH ⊓ K⁆ : Subgroup ↥D) : Set ↥D) *
        ((φ ⁅QX, PH ⊓ K₂⁆ : Subgroup ↥D) : Set ↥D) := by
    rw [← hQXL]
    exact hφmul _ _ _ hQXX hA₁X hA₂X hQA₁A₂
  have hA₁₂L : ⁅φ ⁅QX, PH ⊓ K⁆, φ ⁅QX, PH ⊓ K₂⁆⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₁X hA₂X, show ⁅⁅QX, PH ⊓ K⁆, ⁅QX, PH ⊓ K₂⁆⁆ = ⊥ from hA₁A₂,
      hφbot ⊥ bot_le]
  have hA₁P₂L : ⁅φ ⁅QX, PH ⊓ K⁆, φ (PH ⊓ K₂)⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₁X hP₂X, show ⁅⁅QX, PH ⊓ K⁆, PH ⊓ K₂⁆ = ⊥ from hA₁P₂, hφbot ⊥ bot_le]
  have hA₂P₁L : ⁅φ ⁅QX, PH ⊓ K₂⁆, φ (PH ⊓ K)⁆ = ⊥ := by
    rw [← hφcomm _ _ hA₂X hP₁X, show ⁅⁅QX, PH ⊓ K₂⁆, PH ⊓ K⁆ = ⊥ from hA₂P₁, hφbot ⊥ bot_le]
  have hA₁P₁L : ⁅φ ⁅QX, PH ⊓ K⁆, φ (PH ⊓ K)⁆ ≠ ⊥ := by
    rw [← hφcomm _ _ hA₁X hP₁X, Ne, hφbot _ (Subgroup.commutator_le_of_le hA₁X hP₁X)]
    exact hA₁P₁
  have hA₂P₂L : ⁅φ ⁅QX, PH ⊓ K₂⁆, φ (PH ⊓ K₂)⁆ ≠ ⊥ := by
    rw [← hφcomm _ _ hA₂X hP₂X, Ne, hφbot _ (Subgroup.commutator_le_of_le hA₂X hP₂X)]
    exact hA₂P₂
  exact (NQTerm.perfect_odd_plane_excludes_terminal_support_models hLperf hp hp5 hXe hXLcard
    hirrL).1 ⟨φ PH, φ (PH ⊓ K), φ (PH ⊓ K₂), φ ⁅QX, PH ⊓ K⁆, φ ⁅QX, PH ⊓ K₂⁆, hSylL,
      hφle inf_le_left, hφle inf_le_left, hP₁L, hP₂L, hsupL, hinfL, hcommL, hA₁L, hA₂L,
      hφnorm _ _ hPA₁, hφnorm _ _ hPA₂, hprodL, hA₁₂L, hA₁P₂L, hA₂P₁L, hA₁P₁L, hA₂P₂L⟩

end CFSG.Quasithin.H13.NQCore
