module

public import CFSG.Quasithin.H13.NQCoreSChainStmts
public import CFSG.Quasithin.H13.NQBlockCharNormalizerConfine

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Quasithin.H13.NQBlock
  (original_multiple_prime_radical_captures_two_primes_in_actual_characteristic_normalizer)

variable {G : Type} [Group G] [Finite G]

structure SCCharControl (T D X : Subgroup G) (p : ℕ) : Prop where
  core_ne_bot : pCoreOf 2 X ≠ ⊥
  core_le_core : pCoreOf 2 X ≤ pCoreOf 2 D
  core_le : pCoreOf 2 D ≤ pCoreOf 2 (X ⊔ T)
  normalizer_eq : normalizer (X : Set G) = normalizer (D : Set G)
  char_normalizer_le : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
    (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
      normalizer (C : Set G) ≤ normalizer (D : Set G)
  normalizer_le : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (D : Set G)
  core_eq : pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T)
  sylow_closure : IsSylowOf 2 (pCoreOf 2 (X ⊔ T))
    (⨆ j ∈ normalizer (D : Set G), CFSG.conjugate (pCoreOf 2 (X ⊔ T)) j)
  eq_of_le : ∀ U : Subgroup G, IsPGroup 2 U → X ≤ normalizer (U : Set G) →
    pCoreOf 2 (X ⊔ T) ≤ U → U = pCoreOf 2 (X ⊔ T)
  local_char : ∀ H : Subgroup G, X ⊔ T ≤ H → ∀ C : Subgroup G, C ≠ ⊥ →
    C ≤ pCoreOf 2 (X ⊔ T) → (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
      H ⊓ normalizer (C : Set G) ≤ H ⊓ normalizer (D : Set G)
  local_core : ∀ H : Subgroup G, X ⊔ T ≤ H →
    pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T)
  local_sylow : ∀ H : Subgroup G, X ⊔ T ≤ H → IsSylowOf 2 (pCoreOf 2 (X ⊔ T))
    (⨆ a ∈ H ⊓ normalizer (D : Set G), CFSG.conjugate (pCoreOf 2 (X ⊔ T)) a)
  single_prime : CFSG.fittingSubgroup (↥D ⧸ CFSG.pCore 2 ↥D) =
      CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) →
    ⁅pCoreOf 2 (X ⊔ T), D⁆ ≤ pCoreOf 2 D ∧ ((pCoreOf 2 (X ⊔ T)).subgroupOf (D ⊔ T)).Normal

omit [Finite G] in
theorem maximalTwoLocalsContaining_eq_of_unique {Y M : Subgroup G}
    (h : U3.UniqueMaxTwoLocal Y M) :
    CFSG.maximalTwoLocalsContaining (Y : Set G) = {M} := by
  ext M'
  simp only [CFSG.maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hM', hsub⟩
    exact h.2.2 M' (NQBlock.isMaximalTwoLocal_iff_maxTwoLocal.mp hM')
      (SetLike.coe_subset_coe.mp hsub)
  · rintro rfl
    exact ⟨NQBlock.isMaximalTwoLocal_iff_maxTwoLocal.mpr h.1, SetLike.coe_subset_coe.mpr h.2.1⟩

theorem sylow_normalized_prime_residual_characteristic_normalizers_and_core_control
    (hTPC : NQBlock.StmtTwoPrimeCaptureConfinesCharNormalizer)
    (hCNC : NQBlock.StmtCharNormalizersConfined) {T D X : Subgroup G} {p : ℕ}
    (hS : SCSetup T D X p) : SCCharControl T D X p := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hS.prime⟩
  have := hS.simple
  have hA := hS.ambient
  have hC := hS.canonical
  have hp5 := hS.five_le
  have hXD : X ≤ D := hC.le
  have hDJ : D ≤ normalizer (D : Set G) := le_normalizer
  have hTJ : T ≤ normalizer (D : Set G) := hS.le_normalizer
  have hNX : normalizer (X : Set G) = normalizer (D : Set G) := hC.normalizer_eq.symm
  have hJX : normalizer (D : Set G) ≤ normalizer (X : Set G) := hNX.ge
  have hXJ : X ≤ normalizer (D : Set G) := hXD.trans hDJ
  have hXw : NQBlock.IsOddResidualWitness p (X.subgroupOf D) :=
    NQBlock.isOddResidualWitness_subgroupOf hC.le_rad hC.characteristic hC.noTwoQuotient
      hC.isPGroup hC.exponent hC.pRank hC.card_W hC.nontrivial hC.irreducible_D
  let eXD : X.subgroupOf D ≃* X := subgroupOfEquivOfLe hXD
  have hO2X' : CFSG.pCore 2 (X.subgroupOf D) ≠ ⊥ := by
    intro hb
    apply hC.pCore_ne_bot
    rw [← CFSG.pCore_map_iso 2 eXD, hb, Subgroup.map_bot]
  have hXDmap : (X.subgroupOf D).map D.subtype = X := map_subgroupOf_eq_of_le hXD
  have hTs : IsSylowOf 2 T (D ⊔ T) := CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_right,
    hS.sylow.1, fun h2 => hS.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hMLT := maximalTwoLocalsContaining_eq_of_unique hA.unique
  have hR' : pCoreOf 2 (X ⊔ T) = (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hqD : (CFSG.pCore 2 D).map D.subtype = pCoreOf 2 D := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hsingle : CFSG.fittingSubgroup (↥D ⧸ CFSG.pCore 2 ↥D) =
        CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D) →
      ⁅pCoreOf 2 (X ⊔ T), D⁆ ≤ pCoreOf 2 D ∧
        ((pCoreOf 2 (X ⊔ T)).subgroupOf (D ⊔ T)).Normal ∧
        ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
          (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
          normalizer (C : Set G) ≤ normalizer (D : Set G) := by
    intro hFQ
    obtain ⟨-, -, hRL, hRLT, hLTR, hconf⟩ :=
      NQBlock.single_odd_prime_radical_gives_pre_singleton_characteristic_normalizer_control hTJ
        hTs hA.sqt hA.isCComponent_top hS.not_quasisimple hp5 hXw hO2X' hFQ
    rw [hXDmap] at hRL hRLT hLTR hconf
    obtain ⟨hD, -⟩ := hconf _ hMLT
    rw [← hR'] at hRL hRLT hLTR hD
    refine ⟨?_, (Subgroup.normal_subgroupOf_iff_le_normalizer hRLT).mpr hLTR,
      fun C hC1 hCR hCc => hD C hCR hCc hC1⟩
    rwa [hqD] at hRL
  have hconf : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (D : Set G) := by
    by_cases hFQ : CFSG.fittingSubgroup (↥D ⧸ CFSG.pCore 2 ↥D) =
        CFSG.pCore p (↥D ⧸ CFSG.pCore 2 ↥D)
    · obtain ⟨-, -, -, -, -, hconf⟩ :=
        NQBlock.single_odd_prime_radical_gives_pre_singleton_characteristic_normalizer_control
          hTJ hTs hA.sqt hA.isCComponent_top hS.not_quasisimple hp5 hXw hO2X' hFQ
      have h3 := (hconf _ hMLT).2
      rw [hXDmap, ← hR'] at h3
      exact h3
    · obtain ⟨q, hqF, hqp⟩ := NQBlock.exists_prime_ne_of_fittingSubgroup_ne hFQ
      have hLH : D ≤ D ⊔ T := le_sup_left
      have hTH : T ≤ D ⊔ T := le_sup_right
      have hLHn : (D.subgroupOf (D ⊔ T)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr (sup_le le_normalizer hTJ)
      have hLT : D.subgroupOf (D ⊔ T) ⊔ T.subgroupOf (D ⊔ T) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hLH hTH, Subgroup.subgroupOf_self]
      let φ : D ≃* D.subgroupOf (D ⊔ T) := (subgroupOfEquivOfLe hLH).symm
      have hSQT : CFSG.IsStronglyQuasithin (D.subgroupOf (D ⊔ T)) :=
        CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv φ.symm hA.sqt
      have hLC : CFSG.IsCComponent (⊤ : Subgroup (D.subgroupOf (D ⊔ T))) := by
        have h3 := mem_cComp_top_iff_isCComponent.mp
          (subgroupOf_mem_cComp (subgroupOf_mem_cComp_of_le hLH hA.cComp_self))
        rwa [Subgroup.subgroupOf_self] at h3
      have hq' : ¬ CFSG.IsQuasisimple
          (D.subgroupOf (D ⊔ T) ⧸ CFSG.pCore 2 (D.subgroupOf (D ⊔ T))) := by
        intro hq
        apply hS.not_quasisimple
        exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
          (QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ))).2 hq
      have hFD : CFSG.generalizedFitting D = CFSG.pCore 2 D := by
        have h1 := (quasithinGenFitting_eq_pCoreOf_iff D 2).mp hA.genFitting
        have h2 := (CFSG.Quasithin.centralizer_pCore_le_iff_pCoreOf 2 D).mpr h1
        exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore D 2).mp h2
      have hF : CFSG.generalizedFitting (D.subgroupOf (D ⊔ T)) =
          CFSG.pCore 2 (D.subgroupOf (D ⊔ T)) := by
        rw [← CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv φ, hFD,
          CFSG.pCore_map_iso 2 φ]
      have hXw' : NQBlock.IsOddResidualWitness p ((X.subgroupOf D).map φ.toMonoidHom) :=
        hXw.map_mulEquiv φ
      let ψ : D ⧸ CFSG.pCore 2 D ≃*
          D.subgroupOf (D ⊔ T) ⧸ CFSG.pCore 2 (D.subgroupOf (D ⊔ T)) :=
        QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
      have hqF' : q ∈ (Nat.card (CFSG.fittingSubgroup
          (D.subgroupOf (D ⊔ T) ⧸ CFSG.pCore 2 (D.subgroupOf (D ⊔ T))))).primeFactors := by
        rw [← CFSG.SignalizerFunctorTheorem.McBride.fittingSubgroup_map_equiv ψ,
          Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
        exact hqF
      obtain ⟨⟨A, hA12, hXA, hXqA⟩, hconfine⟩ :=
        hTPC G hS.nonabelian hS.qtke T (D ⊔ T) hS.sylow hTH (D.subgroupOf (D ⊔ T)) hLT hSQT
          hLC hq' hF p hS.prime hp5 _ hXw' q hqF' hqp _ _ _ _ rfl rfl rfl rfl
      have hT' := NQBlock.quasithinIsSylowTwo_subgroupOf hS.sylow hTH
      let T' : Sylow 2 ↥(D ⊔ T) := hT'.1.toSylow hT'.2
      have hLT' : D.subgroupOf (D ⊔ T) ⊔ (T' : Subgroup ↥(D ⊔ T)) = ⊤ := hLT
      obtain ⟨-, -, -, -, hC₁R, hC₁c, -, hC₂R, hC₂c, -⟩ :=
        original_multiple_prime_radical_captures_two_primes_in_actual_characteristic_normalizer
          hSQT hLC T' hLT' hq' hF hp5 hXw' hqF' hqp _ _ _ _ rfl rfl rfl rfl
      have hXG : (((X.subgroupOf D).map φ.toMonoidHom).map (D.subgroupOf (D ⊔ T)).subtype).map
          (D ⊔ T).subtype = X := by
        rw [Subgroup.map_map, Subgroup.map_map]
        have he : ((D ⊔ T).subtype.comp (D.subgroupOf (D ⊔ T)).subtype).comp φ.toMonoidHom =
            D.subtype := by
          ext x
          rfl
        rw [he, map_subgroupOf_eq_of_le hXD]
      have hRG : ((CFSG.pCore 2 (((X.subgroupOf D).map φ.toMonoidHom).map
          (D.subgroupOf (D ⊔ T)).subtype ⊔ T.subgroupOf (D ⊔ T) : Subgroup ↥(D ⊔ T))).map
            (((X.subgroupOf D).map φ.toMonoidHom).map (D.subgroupOf (D ⊔ T)).subtype ⊔
              T.subgroupOf (D ⊔ T)).subtype).map (D ⊔ T).subtype = pCoreOf 2 (X ⊔ T) := by
        have h1 := NQBlock.pCoreOf_map_subtype (H := D ⊔ T) (((X.subgroupOf D).map
          φ.toMonoidHom).map (D.subgroupOf (D ⊔ T)).subtype ⊔ T.subgroupOf (D ⊔ T))
        unfold CFSG.Open.pCoreOf at h1
        rw [h1, Subgroup.map_sup, map_subgroupOf_eq_of_le hTH, hXG]
        unfold CFSG.Open.pCoreOf
        try with_reducible rfl
      have hconfC : ∀ C : Subgroup ↥(D ⊔ T), C ≤ (CFSG.pCore 2 (((X.subgroupOf D).map
          φ.toMonoidHom).map (D.subgroupOf (D ⊔ T)).subtype ⊔ T.subgroupOf (D ⊔ T) :
            Subgroup ↥(D ⊔ T))).map (((X.subgroupOf D).map φ.toMonoidHom).map
              (D.subgroupOf (D ⊔ T)).subtype ⊔ T.subgroupOf (D ⊔ T)).subtype →
          (C.subgroupOf ((CFSG.pCore 2 (((X.subgroupOf D).map φ.toMonoidHom).map
            (D.subgroupOf (D ⊔ T)).subtype ⊔ T.subgroupOf (D ⊔ T) : Subgroup ↥(D ⊔ T))).map
              (((X.subgroupOf D).map φ.toMonoidHom).map (D.subgroupOf (D ⊔ T)).subtype ⊔
                T.subgroupOf (D ⊔ T)).subtype)).Characteristic →
          normalizer ((C.map (D ⊔ T).subtype : Subgroup G) : Set G) ≤ normalizer (X : Set G) →
          normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ normalizer (D : Set G) := by
        intro C hCR hCc hNC
        have hc := NQBlock.characteristic_map_subtype_subgroupOf hCc
        rw [hRG] at hc
        have hCG : C.map (D ⊔ T).subtype ≤ pCoreOf 2 (X ⊔ T) :=
          (Subgroup.map_mono hCR).trans hRG.le
        have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
          ((C.map (D ⊔ T).subtype).subgroupOf (pCoreOf 2 (X ⊔ T)))
        rw [map_subgroupOf_eq_of_le hCG] at h1
        exact h1.trans (hNC.trans hNX.le)
      have hXeq : normalizer ((((((X.subgroupOf D).map φ.toMonoidHom).map
          (D.subgroupOf (D ⊔ T)).subtype).map (D ⊔ T).subtype : Subgroup G)) : Set G) =
            normalizer (X : Set G) := by
        rw [hXG]
      rcases hA12 with hA | hA
      · exact hconfC _ hC₁R hC₁c ((hconfine _ A (Or.inl ⟨rfl, hA⟩) hXA hXqA).trans hXeq.le)
      · exact hconfC _ hC₂R hC₂c ((hconfine _ A (Or.inr ⟨rfl, hA⟩) hXA hXqA).trans hXeq.le)
  have hXDTn : (X.subgroupOf (D ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hXD.trans le_sup_left)).mpr
      ((sup_le hDJ hTJ).trans hJX)
  have hDDTn : (D.subgroupOf (D ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTJ)
  have hall : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ pCoreOf 2 (X ⊔ T) →
      (C.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic →
      normalizer (C : Set G) ≤ normalizer (D : Set G) := by
    intro C hC1 hCR hCc
    have h1 := hCNC G hS.nonabelian hS.qtke T (D ⊔ T) D hS.sylow le_sup_right le_sup_left
      hDDTn rfl hA.cComp_self p hS.prime hp5 X hXD hXDTn hC.noTwoQuotient hC.isPGroup
      hC.exponent hC.pRank hC.card_W hC.nontrivial hC.irreducible_D (hconf.trans hJX) C hC1 hCR
      hCc
    exact h1.trans hNX.le
  have hXMn : (X.subgroupOf (normalizer (D : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXJ).mpr hJX
  have hTsM : IsSylowOf 2 T (normalizer (D : Set G)) :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hTJ, hS.sylow.1,
      fun h2 => hS.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTJ))⟩
  have hconf' : normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype :
      Subgroup G) : Set G) ≤ normalizer (D : Set G) := by
    rw [← hR']
    exact hconf
  obtain ⟨-, -, -, -, -, hRN, hRS, hXR, hRB⟩ :=
    CFSG.Quasithin.SteinbergCC.prime_residual_sylow_normalizer_core_bootstrap Nat.prime_two
      hXJ hXMn hC.noTwoQuotient hTsM hconf'
  rw [← hR'] at hRN hRS hXR hRB
  have hN : (CFSG.pCore 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G) : Subgroup G)).map
      (normalizer (pCoreOf 2 (X ⊔ T) : Set G)).subtype =
        pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hRN' : pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) := by
    rw [← hN]
    exact hRN.symm
  have hqX : pCoreOf 2 X ≠ ⊥ := by
    intro hb
    apply hC.pCore_ne_bot
    unfold CFSG.Open.pCoreOf at hb
    exact (map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb
  have hqXD : pCoreOf 2 X ≤ pCoreOf 2 D := by
    have hn : D ≤ normalizer (pCoreOf 2 X : Set G) :=
      hDJ.trans (hJX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X))
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((map_subtype_le _).trans hXD) hn (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hqDR : pCoreOf 2 D ≤ pCoreOf 2 (X ⊔ T) := by
    have hJs : IsSylowTwoOf T (normalizer (D : Set G)) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hS.sylow hTJ
    have hqJ : pCoreOf 2 D ≤ pCoreOf 2 (normalizer (D : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ((map_subtype_le _).trans hDJ)
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D)
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D)
    have hqT : pCoreOf 2 D ≤ T := hqJ.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hJs)
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hqT.trans le_sup_right)
      ((sup_le hXJ hTJ).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 D))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D)
  have hloc : ∀ H : Subgroup G, X ⊔ T ≤ H →
      pCoreOf 2 (H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) := by
    intro H hXTH
    set N := H ⊓ normalizer (pCoreOf 2 (X ⊔ T) : Set G) with hNdef
    have hRH : pCoreOf 2 (X ⊔ T) ≤ H := (map_subtype_le _).trans hXTH
    have hRN : pCoreOf 2 (X ⊔ T) ≤ N := le_inf hRH le_normalizer
    have h1 : pCoreOf 2 (X ⊔ T) ≤ pCoreOf 2 N :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRN inf_le_right
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (X ⊔ T))
    have hXN : X ≤ N := le_inf (le_sup_left.trans hXTH) hXR
    refine hRB _ (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hXN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)) h1
  have hsylJ : ∀ H : Subgroup G, X ⊔ T ≤ H → IsSylowOf 2 (pCoreOf 2 (X ⊔ T))
      (⨆ a ∈ H ⊓ normalizer (D : Set G), CFSG.conjugate (pCoreOf 2 (X ⊔ T)) a) := by
    intro H hXTH
    refine hRS.of_le ?_ ?_
    · have h1 : CFSG.conjugate (pCoreOf 2 (X ⊔ T)) 1 = pCoreOf 2 (X ⊔ T) := by
        ext x
        simp [CFSG.conjugate]
      calc pCoreOf 2 (X ⊔ T) = CFSG.conjugate (pCoreOf 2 (X ⊔ T)) 1 := h1.symm
        _ ≤ ⨆ a ∈ H ⊓ normalizer (D : Set G), CFSG.conjugate (pCoreOf 2 (X ⊔ T)) a :=
          le_iSup₂ (f := fun a (_ : a ∈ H ⊓ normalizer (D : Set G)) =>
            CFSG.conjugate (pCoreOf 2 (X ⊔ T)) a) 1 (one_mem _)
    · exact iSup₂_le fun a ha => le_iSup₂ (f := fun j (_ : j ∈ normalizer (D : Set G)) =>
        CFSG.conjugate (pCoreOf 2 (X ⊔ T)) j) a (mem_inf.mp ha).2
  exact
    { core_ne_bot := hqX
      core_le_core := hqXD
      core_le := hqDR
      normalizer_eq := hNX
      char_normalizer_le := hall
      normalizer_le := hconf
      core_eq := hRN'
      sylow_closure := hRS
      eq_of_le := hRB
      local_char := fun H _ C hC1 hCR hCc =>
        inf_le_inf_left H (hall C hC1 hCR hCc)
      local_core := hloc
      local_sylow := hsylJ
      single_prime := fun hFQ => ⟨(hsingle hFQ).1, (hsingle hFQ).2.1⟩ }

end CFSG.Quasithin.H13.NQCore
