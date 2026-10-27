module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.Conjugation

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

@[expose] public def H0CLinearCandidateXmuTransportedRawData_sec9
    {G : Type u} [Group G] [Finite G]
    (M W1 : Subgroup G)
    (p : ℕ)
    (κ : Type u)
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (orbit : κ → ι)
    (θ : ι → Section1.ClassFunction ((ambientDerivedSubgroup M).subgroupOf M)) :
    Prop :=
  ∃ μraw : H0CLinearCandidateXmuRawIndex_sec9 p → κ,
    let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
      fun i => orbit (μraw i)
    H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
        μorbit θ ∧
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ

set_option maxHeartbeats 800000 in
public theorem H0CLinearCandidateXmu_transported_generator_raw_smul_source_core_sec9
    {G : Type u} [Group G] [Finite G]
    {MF U W1 H0 C : Subgroup G}
    (p q : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1card : Nat.card W1 = q)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (x : U ⧸ C.subgroupOf U)
    {i j : H0CLinearCandidateXmuRawIndex_sec9 p} :
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
      quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    x • μraw j = μraw i →
      (w0 • x) • μraw j = μraw i := by
  classical
  intro _instAction hx
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, hE, hμraw_eq⟩
  let base : Fin q := ⟨0, hqposμ⟩
  rcases hsucc ⟨0, hqpos⟩ with ⟨hconjMF, action, haction, _hmap0⟩
  have hmap_each :
      ∀ k : Fin q,
        (H k).map action.toMonoidHom =
          H (theorem_9_7_fin_cyclic_succ_sec9 hqpos k) := by
    intro k
    rcases hsucc k with ⟨hconjMF_k, action_k, haction_k, hmap_k⟩
    have haction_eq : action_k = action := by
      ext z
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) z with ⟨m, rfl⟩
      calc
        action_k (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF_k m⟩ := haction_k m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    simpa [haction_eq] using hmap_k.symm
  have hE_step :
      ∀ k : Fin q, ∀ z : H base,
        (E (theorem_9_7_fin_cyclic_succ_sec9 hqpos k) z :
            MF ⧸ H0.subgroupOf MF) =
          action (E k z : MF ⧸ H0.subgroupOf MF) := by
    intro k z
    let sk : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos k
    have hw0q : w0 ^ q = 1 := by
      rw [← hW1card, ← orderOf_eq_card_of_zpowers_eq_top hw0gen]
      exact pow_orderOf_eq_one w0
    have hpow_stepW1 : w0 ^ sk.1 = w0 ^ k.1 * w0 := by
      by_cases hnext : k.1 + 1 < q
      · simp [sk, theorem_9_7_fin_cyclic_succ_sec9, hnext, pow_succ]
      · have hkq : k.1 + 1 = q := by omega
        calc
          w0 ^ sk.1 = 1 := by
            simp [sk, theorem_9_7_fin_cyclic_succ_sec9, hnext]
          _ = w0 ^ k.1 * w0 := by
            symm
            calc
              w0 ^ k.1 * w0 = w0 ^ (k.1 + 1) := (pow_succ w0 k.1).symm
              _ = w0 ^ q := by rw [hkq]
              _ = 1 := hw0q
    have hpow_stepG :
        (((w0 ^ sk.1 : W1) : G) =
          (((w0 ^ k.1 : W1) : G) * (w0 : G))) := by
      simpa using congrArg Subtype.val hpow_stepW1
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
        (z : MF ⧸ H0.subgroupOf MF) with ⟨m, hm⟩
    have hmBase : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H base := by
      simp [base, hm]
    have hzmk :
        z = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ := by
      apply Subtype.ext
      simpa using hm.symm
    rcases hE k with ⟨hconj_k, hE_k⟩
    rcases hE sk with ⟨hconj_sk, hE_sk⟩
    rw [hzmk]
    calc
      (E sk ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
          MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(((w0 ^ sk.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ sk.1 : W1) : G)), hconj_sk m⟩ :=
        hE_sk m hmBase
      _ = action
          (QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(((w0 ^ k.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ k.1 : W1) : G)), hconj_k m⟩) := by
        rw [haction]
        apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
        apply Subtype.ext
        change (((w0 ^ sk.1 : W1) : G))⁻¹ * (m : G) *
            (((w0 ^ sk.1 : W1) : G)) =
          (w0 : G)⁻¹ *
            ((((w0 ^ k.1 : W1) : G))⁻¹ * (m : G) *
              (((w0 ^ k.1 : W1) : G))) * (w0 : G)
        rw [hpow_stepG]
        group
      _ = action
          (E k ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
            MF ⧸ H0.subgroupOf MF) := by
        rw [hE_k m hmBase]
  apply ULift.ext
  funext k
  apply (nonprincipalLinearCharacterEquivFin_sec9 (H k) p (hHcard k)).injective
  apply Subtype.ext
  apply MonoidHom.ext
  intro z
  let sk : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos k
  let eStep : H k ≃* H sk := (E k).symm.trans (E sk)
  have htransport :
      ∃ e0 : H k ≃* H sk,
        (∃ hconjW : ∀ h : MF, (w0 : G)⁻¹ * (h : G) * (w0 : G) ∈ MF,
          (∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H k,
            (e0 ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(w0 : G)⁻¹ * (h : G) * (w0 : G), hconjW h⟩) ∧
          ∃ hconjWinv : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF,
            ∀ h : MF, ∀ hhR : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H sk,
              (e0.symm ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhR⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjWinv h⟩) ∧
        theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 e0
            (ρ k) =
          ρ sk := by
    simpa [sk] using
      theorem_9_7_successorTransportFactorAction_eq_of_action_field_sec9
        hnormalC hCinv w0 (hsucc k) (ρ := ρ k)
        (σ := ρ (theorem_9_7_fin_cyclic_succ_sec9 hqpos k))
        (hρaction k)
        (hρaction (theorem_9_7_fin_cyclic_succ_sec9 hqpos k))
  let e0 : H k ≃* H sk := Classical.choose htransport
  have heData0 := (Classical.choose_spec htransport).1
  have heq0 := (Classical.choose_spec htransport).2
  rcases heData0 with ⟨hconjStep, he0, _hconjStepInv, _he0symm⟩
  have he0_eStep : e0 = eStep := by
    ext y
    rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
        (y : MF ⧸ H0.subgroupOf MF) with ⟨m, hm⟩
    have hmK : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H k := by
      simp [hm]
    have hymk : y = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmK⟩ := by
      apply Subtype.ext
      simpa using hm.symm
    have he0val :
        (e0 y : MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjStep m⟩ := by
      rw [hymk]
      exact he0 m hmK
    have heStep_action :
        (eStep y : MF ⧸ H0.subgroupOf MF) =
          action (y : MF ⧸ H0.subgroupOf MF) := by
      dsimp [eStep]
      simpa [sk] using hE_step k ((E k).symm y)
    have heStep_val :
        (eStep y : MF ⧸ H0.subgroupOf MF) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
      calc
        (eStep y : MF ⧸ H0.subgroupOf MF) =
            action (y : MF ⧸ H0.subgroupOf MF) := heStep_action
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := by rw [hm]
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := haction m
    exact he0val.trans heStep_val.symm
  have heqStep :
      theorem_9_7_successorTransportFactorAction_sec9 hnormalC hCinv w0 eStep
          (ρ k) =
        ρ sk := by
    rw [← he0_eStep]
    exact heq0
  have hfactor_eStep :
      ∀ y : H k, (ρ sk x) (eStep y) = eStep (ρ k (w0 • x) y) := by
    intro y
    rw [← heqStep]
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    simpa using theorem_9_7_successorTransportFactorAction_apply_mk_sec9
      hnormalC hCinv w0 eStep (ρ k) u (eStep y)
  let yk : H k := (ρ k (w0 • x)).symm z
  have hpre :
      (ρ sk x).symm (eStep z) = eStep yk := by
    apply (ρ sk x).injective
    simpa [yk] using (hfactor_eStep yk).symm
  have hβ :
      (E sk).symm ((ρ sk x).symm (eStep z)) =
        (E k).symm yk := by
    calc
      (E sk).symm ((ρ sk x).symm (eStep z)) =
          (E sk).symm (eStep yk) := by rw [hpre]
      _ = (E k).symm yk := by
          simp [eStep]
  have hsk :
      (x • μraw j).down sk = (μraw i).down sk := by
    exact congrArg
      (fun f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q => f.down sk) hx
  have hsk_eval :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
          ((x • μraw j).down sk)).1 (eStep z) =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
          ((μraw i).down sk)).1 (eStep z) := by
    rw [hsk]
  have hbase_eval :
      ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) j).1 ((E k).symm yk) =
        ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
          (hHcard base)) i).1 ((E k).symm z) := by
    have hleft :
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((x • μraw j).down sk)).1 (eStep z) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
            (hHcard base)) j).1 ((E k).symm yk) := by
      calc
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((x • μraw j).down sk)).1 (eStep z) =
            ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
              ((μraw j).down sk)).1 ((ρ sk x).symm (eStep z)) := by
              simp [rawCoordinateMulAction_down_sec9,
                nonprincipalLinearCharacterIndexMulAction_spec_sec9,
                MonoidHom.comp_apply]
        _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
              (hHcard base)) j).1 ((E k).symm yk) := by
              have hspec :=
                H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
                  p q H hHcard base E j sk
              have happ := congrArg
                (fun χ : H sk →* ℂˣ => χ ((ρ sk x).symm (eStep z))) hspec
              simpa [base, hμraw_eq, MonoidHom.comp_apply, hβ] using happ
    have hright :
        ((nonprincipalLinearCharacterEquivFin_sec9 (H sk) p (hHcard sk))
            ((μraw i).down sk)).1 (eStep z) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p
            (hHcard base)) i).1 ((E k).symm z) := by
      have hspec :=
        H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
          p q H hHcard base E i sk
      have happ := congrArg (fun χ : H sk →* ℂˣ => χ (eStep z)) hspec
      simpa [base, hμraw_eq, MonoidHom.comp_apply, eStep] using happ
    exact hleft.symm.trans (hsk_eval.trans hright)
  simpa [base, hμraw_eq, rawCoordinateMulAction_down_sec9,
    nonprincipalLinearCharacterIndexMulAction_spec_sec9,
    H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9,
    MonoidHom.comp_apply, yk] using hbase_eval

public theorem H0CLinearCandidateXmu_transported_muorbit_injective_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (_hρcyc : ∀ i, IsCyclic (ρ i).range)
    (_hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (_hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (_horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw)
    (_hW1Inertia :
      let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
      let HCD : Subgroup Dm := HCm.subgroupOf Dm
      let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
      let instFintypeι : Fintype ι := Fintype.ofFinite ι
      let instDecidableEqι : DecidableEq ι := Classical.decEq ι
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      let orbit : κ → ι := fun k => Quotient.mk'' k
      let ψ : ι → Section1.ClassFunction HCm :=
        fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
      let θ : ι → Section1.ClassFunction Dm :=
        fun i =>
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (ψ i))
      let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
        fun i => orbit (μraw i)
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        Function.Injective
          (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) := by
  classical
  intro _hψformula hcase _hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  rcases hμrawOrderedActionData with
    ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, _χbar,
      _hχsep, _hχtransition⟩
  have hμraw_inj : Function.Injective μraw := by
    rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, _hEμ, hμraw_eq⟩
    rw [hμraw_eq]
    exact
      H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_injective_sec9
        p q H hHcard ⟨0, hqposμ⟩ E
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases case_9_7_a_hoReductionData_sec9 hcase with ⟨hp, _hp_eq, hpData⟩
  have hW1normMF : W1 ≤ Subgroup.normalizer (MF : Set G) := by
    exact le_sup_right.trans
      (theorem_9_3_action_normalizes_and_solvable_sec9 M MF U W1 W2 q h92).1
  have hCinv :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      IsInvariant W1 U (C.subgroupOf U) := by
    letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
    exact theorem_9_7_quotientCentralizerIn_isInvariant_W1_sec9
      h92 hpData (case_9_7_a_quotientCentralizerIn_sec9 hcase)
      hW1normU hW1normMF
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  have hfixedBot :
      fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) = ⊥ :=
    theorem_9_7_fixedPointSubgroup_W1_barU_eq_bot_of_isInvariant_sec9
      h92 hnormalC hW1normU hCinv
  change Function.Injective
    (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i))
  intro i j hij
  have hrel :
      MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (μraw i) (μraw j) := by
    exact Quotient.exact (by simpa [orbit] using hij)
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨x, hx⟩
  have hW1card : Nat.card W1 = q := h92.q_eq
  have hx_gen :
      (w0 • x) • μraw j = μraw i :=
    H0CLinearCandidateXmu_transported_generator_raw_smul_source_core_sec9
      (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
      p q H hHcard ρ hρaction μraw w0 hw0gen hW1card hW1normU hCinv
      hμrawOrderedData hqpos hsucc x hx
  have hsame :
      (w0 • x) • μraw j = x • μraw j := hx_gen.trans hx.symm
  have hfix_delta :
      (x⁻¹ * (w0 • x)) • μraw j = μraw j := by
    calc
      (x⁻¹ * (w0 • x)) • μraw j =
          x⁻¹ • ((w0 • x) • μraw j) := by rw [mul_smul]
      _ = x⁻¹ • (x • μraw j) := by rw [hsame]
      _ = μraw j := by rw [inv_smul_smul]
  have hdelta_mem :
      x⁻¹ * (w0 • x) ∈
        MulAction.stabilizer (U ⧸ C.subgroupOf U) (μraw j) := by
    rw [MulAction.mem_stabilizer_iff]
    exact hfix_delta
  have hdelta_one : x⁻¹ * (w0 • x) = 1 := by
    have hstab :=
      rawCoordinateMulAction_stabilizer_eq_bot_sec9
        (hcase := hcase) H hHcard hHnorm hHsup ρ hρaction (μraw j)
    have hbot :
        x⁻¹ * (w0 • x) ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
      simpa [instAction] using (by simpa [hstab] using hdelta_mem)
    exact Subgroup.mem_bot.mp hbot
  have hgen_fix :
      w0 • x = x := by
    have hmul := congrArg (fun y : U ⧸ C.subgroupOf U => x * y) hdelta_one
    simpa [mul_assoc] using hmul
  have hxfix :
      x ∈ fixedPointSubgroup W1 (U ⧸ C.subgroupOf U) := by
    intro w
    have hw : w ∈ Subgroup.zpowers w0 := by
      rw [hw0gen]
      exact Subgroup.mem_top w
    exact smul_eq_self_of_mem_zpowers hw hgen_fix
  have hxone : x = 1 := by
    have hxbot :
        x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
      simpa [hfixedBot] using hxfix
    exact Subgroup.mem_bot.mp hxbot
  have hraw_eq : μraw j = μraw i := by
    simpa [hxone] using hx
  exact (hμraw_inj hraw_eq).symm

public theorem H0CLinearCandidateXmu_transported_final_injective_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw)
    (hW1Inertia :
      let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
      let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
      let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
      let HCD : Subgroup Dm := HCm.subgroupOf Dm
      let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
      let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
      let instFintypeι : Fintype ι := Fintype.ofFinite ι
      let instDecidableEqι : DecidableEq ι := Classical.decEq ι
      letI : Fintype ι := instFintypeι
      letI : DecidableEq ι := instDecidableEqι
      let orbit : κ → ι := fun k => Quotient.mk'' k
      let ψ : ι → Section1.ClassFunction HCm :=
        fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
      let θ : ι → Section1.ClassFunction Dm :=
        fun i =>
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (ψ i))
      let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
        fun i => orbit (μraw i)
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        μorbit θ) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
          μorbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hμinj : Function.Injective μorbit := by
    simpa [κ, instAction, orbit, μorbit] using
      H0CLinearCandidateXmu_transported_muorbit_injective_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        (by simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using hW1Inertia)
        hψformula hcase hBarU
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
    H0CLinearCandidateXmuFinalInjectiveDataWithRaw_of_finalInertiaData_sec9
      M MF H0 C p μorbit θ hμinj hfinalInertia


public theorem
    H0CLinearCandidateXmu_ordered_generator_quotient_product_rotation_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (_hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [_hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (_hρcyc : ∀ i, IsCyclic (ρ i).range)
    (_hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (_hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (_hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (_horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (_hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (_hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C ubar) :
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
    ∀ hconjHC : ∀ h : HC, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ HC,
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ h : HC,
          θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩)) =
            θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  -- restrictions: `w0` rotates the ordered internal-product factors of
  -- the transported `mu_f`, including the wraparound coordinate.
  classical
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  rcases hsucc ⟨0, hqpos⟩ with ⟨hconjMF, action, haction, _hmap0⟩
  have hmap_each :
      ∀ j : Fin q,
        (H j).map action.toMonoidHom =
          H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j) := by
    intro j
    rcases hsucc j with ⟨hconjMF_j, action_j, haction_j, hmap_j⟩
    have haction_eq : action_j = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
      calc
        action_j (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF_j m⟩ := haction_j m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    simpa [haction_eq] using hmap_j.symm
  have hconjMFpos : ∀ h : MF, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ MF :=
    conj_inv_mem_of_conj_mem_finite_sec9 hconjMF
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hCcent : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : (H0C.subgroupOf M).Normal := by
    dsimp [H0C]
    exact theorem_9_H0C_normal_M_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hCcent hpprime hpData
  have hH0CleD : H0C ≤ ambientDerivedSubgroup M := by
    dsimp [H0C]
    exact theorem_9_H0C_le_ambientDerived_of_source_sec9
      M MF U W1 W2 H0 C q h92 hH0MF hCcent
  have hDleM : ambientDerivedSubgroup M ≤ M :=
    section12_ambientDerivedSubgroup_le (E := M)
  have hH0CleM : H0C ≤ M := hH0CleD.trans hDleM
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  have hconjH0C : ∀ h : H0C, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ H0C := by
    intro h
    let hM : M := ⟨(h : G), hH0CleM h.property⟩
    let hH0CM : H0C.subgroupOf M := ⟨hM, by
      simp [H0C, hM, Subgroup.mem_subgroupOf]⟩
    have hmem :
        w0M * hH0CM * w0M⁻¹ ∈ H0C.subgroupOf M :=
      hH0CnormalM.conj_mem hH0CM hH0CM.property w0M
    simpa [H0C, w0M, hM, hH0CM, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  have haction_symm :
      ∀ h : MF,
        action.symm (QuotientGroup.mk' (H0.subgroupOf MF) h) =
          QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjMFpos h⟩ := by
    rcases quotientSubgroupConjugateByElement_action_symm_apply_sec9
        (hsucc ⟨0, hqpos⟩) with
      ⟨_hconjMF', action', haction', _hmap', _hconjInvMF', hactionInv'⟩
    have haction_eq : action' = action := by
      ext x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨m, rfl⟩
      calc
        action' (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), _hconjMF' m⟩ := haction' m
        _ = QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(w0 : G)⁻¹ * (m : G) * (w0 : G), hconjMF m⟩ := by
              congr 1
        _ = action (QuotientGroup.mk' (H0.subgroupOf MF) m) := (haction m).symm
    intro h
    have hval := hactionInv' h
    simpa [haction_eq] using hval
  have htheta_action :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        (θH (μraw i)).comp action.symm.toMonoidHom = θH (μraw i) := by
    have hsucc_surj :
        Function.Surjective (theorem_9_7_fin_cyclic_succ_sec9 hqpos) := by
      intro j
      by_cases hj0 : j.1 = 0
      · refine ⟨⟨q - 1, by omega⟩, ?_⟩
        apply Fin.ext
        have hwrap : ¬ q - 1 + 1 < q := by omega
        simp [theorem_9_7_fin_cyclic_succ_sec9, hwrap, hj0]
      · refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
        apply Fin.ext
        have hnext : j.1 - 1 + 1 < q := by omega
        simp [theorem_9_7_fin_cyclic_succ_sec9, hnext]
        omega
    have hiSup_succ :
        (iSup fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) =
          iSup H := by
      apply le_antisymm
      · refine iSup_le ?_
        intro j
        exact le_iSup H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)
      · refine iSup_le ?_
        intro j
        rcases hsucc_surj j with ⟨k, hk⟩
        simpa [hk] using
          (le_iSup
            (fun k : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos k)) k)
    have hsup_succ :
        (iSup fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) =
          ⊤ := by
      rw [hiSup_succ, hHsup]
    have hcomponent_step :
        ∀ idx : H0CLinearCandidateXmuRawIndex_sec9 p,
          ∀ j : Fin q,
            ∀ x : H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j),
              ∀ y : H j,
                action (y : MF ⧸ H0.subgroupOf MF) = x →
                  ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
                      ((μraw idx).down j)).1 y =
                    ((nonprincipalLinearCharacterEquivFin_sec9
                        (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
                        (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
                      ((μraw idx).down
                        (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x := by
      -- the wraparound case uses `w0 ^ q = 1` from `hw0gen`.
      rcases hμrawOrderedData with ⟨hqposμ, _hwμ, E, hE, hμraw_eq⟩
      let base : Fin q := ⟨0, hqposμ⟩
      intro idx j x y hyx
      let sj : Fin q := theorem_9_7_fin_cyclic_succ_sec9 hqpos j
      have hw0q : w0 ^ q = 1 := by
        rw [← h92.q_eq, ← orderOf_eq_card_of_zpowers_eq_top hw0gen]
        exact pow_orderOf_eq_one w0
      have hpow_stepW1 : w0 ^ sj.1 = w0 ^ j.1 * w0 := by
        by_cases hnext : j.1 + 1 < q
        · simp [sj, theorem_9_7_fin_cyclic_succ_sec9, hnext, pow_succ]
        · have hjq : j.1 + 1 = q := by omega
          calc
            w0 ^ sj.1 = 1 := by
              simp [sj, theorem_9_7_fin_cyclic_succ_sec9, hnext]
            _ = w0 ^ j.1 * w0 := by
              symm
              calc
                w0 ^ j.1 * w0 = w0 ^ (j.1 + 1) := (pow_succ w0 j.1).symm
                _ = w0 ^ q := by rw [hjq]
                _ = 1 := hw0q
      have hpow_stepG :
          (((w0 ^ sj.1 : W1) : G) =
            (((w0 ^ j.1 : W1) : G) * (w0 : G))) := by
        simpa using congrArg Subtype.val hpow_stepW1
      have hE_step :
          ∀ z : H base, (E sj z : MF ⧸ H0.subgroupOf MF) =
            action (E j z : MF ⧸ H0.subgroupOf MF) := by
        intro z
        rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
            (z : MF ⧸ H0.subgroupOf MF) with
          ⟨m, hm⟩
        have hmBase : QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H base := by
          simp [base, hm]
        have hzmk :
            z = ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ := by
          apply Subtype.ext
          simpa using hm.symm
        rcases hE j with ⟨hconj_j, hE_j⟩
        rcases hE sj with ⟨hconj_sj, hE_sj⟩
        rw [hzmk]
        calc
          (E sj ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
              MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(((w0 ^ sj.1 : W1) : G))⁻¹ * (m : G) *
                    (((w0 ^ sj.1 : W1) : G)), hconj_sj m⟩ :=
            hE_sj m hmBase
          _ = action
              (QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(((w0 ^ j.1 : W1) : G))⁻¹ * (m : G) *
                    (((w0 ^ j.1 : W1) : G)), hconj_j m⟩) := by
            rw [haction]
            apply congrArg (QuotientGroup.mk' (H0.subgroupOf MF))
            apply Subtype.ext
            change (((w0 ^ sj.1 : W1) : G))⁻¹ * (m : G) *
                (((w0 ^ sj.1 : W1) : G)) =
              (w0 : G)⁻¹ *
                ((((w0 ^ j.1 : W1) : G))⁻¹ * (m : G) *
                  (((w0 ^ j.1 : W1) : G))) * (w0 : G)
            rw [hpow_stepG]
            group
          _ = action
              (E j ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase⟩ :
                MF ⧸ H0.subgroupOf MF) := by
            rw [hE_j m hmBase]
      let χbase :=
        ((nonprincipalLinearCharacterEquivFin_sec9 (H base) p (hHcard base)) idx).1
      have hleft :
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 y =
            χbase ((E j).symm y) := by
        have hspec :=
          H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
            p q H hHcard base E idx j
        have happ := congrArg (fun χ : H j →* ℂˣ => χ y) hspec
        simpa [χbase, hμraw_eq, MonoidHom.comp_apply] using happ
      have hright :
          ((nonprincipalLinearCharacterEquivFin_sec9 (H sj) p (hHcard sj))
              ((μraw idx).down sj)).1 x =
            χbase ((E sj).symm x) := by
        have hspec :=
          H0CLinearCandidateXmuTransportedRawCoordinateOfEquiv_component_spec_sec9
            p q H hHcard base E idx sj
        have happ := congrArg (fun χ : H sj →* ℂˣ => χ x) hspec
        simpa [χbase, hμraw_eq, sj, MonoidHom.comp_apply] using happ
      have harg :
          (E j).symm y = (E sj).symm x := by
        have hEz :
            E sj ((E j).symm y) = x := by
          apply Subtype.ext
          calc
            (E sj ((E j).symm y) : MF ⧸ H0.subgroupOf MF) =
                action
                  (E j ((E j).symm y) : MF ⧸ H0.subgroupOf MF) :=
              hE_step ((E j).symm y)
            _ = action (y : MF ⧸ H0.subgroupOf MF) := by
              simp
            _ = (x : MF ⧸ H0.subgroupOf MF) := hyx
        rw [← hEz]
        simp
      calc
        ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
            ((μraw idx).down j)).1 y = χbase ((E j).symm y) := hleft
        _ = χbase ((E sj).symm x) := by rw [harg]
        _ = ((nonprincipalLinearCharacterEquivFin_sec9 (H sj) p (hHcard sj))
            ((μraw idx).down sj)).1 x := hright.symm
    intro idx
    apply monoidHom_ext_of_iSup_eq_top_sec9
      (fun j : Fin q => H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))
      hsup_succ
    intro j x
    have hxmap :
        (x : MF ⧸ H0.subgroupOf MF) ∈ (H j).map action.toMonoidHom := by
      rw [hmap_each j]
      exact x.property
    rcases hxmap with ⟨y, hy, hyx⟩
    let yj : H j := ⟨y, hy⟩
    have hsymm_y :
        action.symm (x : MF ⧸ H0.subgroupOf MF) = (yj : MF ⧸ H0.subgroupOf MF) := by
      rw [← hyx]
      simp [yj]
    have hleft :
        θH (μraw idx) (action.symm (x : MF ⧸ H0.subgroupOf MF)) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 yj := by
      rw [hsymm_y]
      simpa [θH] using
        componentProductLinearCharacter_apply_subgroup_sec9
          p q H hHcard hHindep hHsup (μraw idx).down j yj
    have hright :
        θH (μraw idx) (x : MF ⧸ H0.subgroupOf MF) =
          ((nonprincipalLinearCharacterEquivFin_sec9
              (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
              (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
            ((μraw idx).down (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x := by
      simpa [θH] using
        componentProductLinearCharacter_apply_subgroup_sec9
          p q H hHcard hHindep hHsup (μraw idx).down
          (theorem_9_7_fin_cyclic_succ_sec9 hqpos j) x
    calc
      θH (μraw idx) (action.symm (x : MF ⧸ H0.subgroupOf MF)) =
          ((nonprincipalLinearCharacterEquivFin_sec9 (H j) p (hHcard j))
              ((μraw idx).down j)).1 yj := hleft
      _ = ((nonprincipalLinearCharacterEquivFin_sec9
              (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)) p
              (hHcard (theorem_9_7_fin_cyclic_succ_sec9 hqpos j)))
            ((μraw idx).down
              (theorem_9_7_fin_cyclic_succ_sec9 hqpos j))).1 x :=
          hcomponent_step idx j x yj (by simpa [yj] using hyx)
      _ = θH (μraw idx) (x : MF ⧸ H0.subgroupOf MF) := hright.symm
  dsimp only
  intro hconjHC i h
  have hquot_h :
      e.symm
          (QuotientGroup.mk' (H0C.subgroupOf HC)
            ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩) =
        action.symm (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
    exact quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
      MF H0 HC H0C le_sup_left hH0CinfMF hsup
      (w0 : G) hconjMFpos hconjH0C hconjHC action.symm haction_symm h
  rw [hquot_h]
  have happ := congrArg
    (fun χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ =>
      χ (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h))) (htheta_action i)
  simpa [MonoidHom.comp_apply, HC, H0C, e, θH] using happ

public theorem H0CLinearCandidateXmu_ordered_generator_source_conjugation_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x)) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a) →
      (hBarU : quotientBarUCardinality U C ubar) →
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
        ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          let hDnormal : Dm.Normal := by
            simpa [Dm] using
              (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
          let hHCnormal : HCm.Normal := by
            dsimp [HCm]
            exact theorem_9_8_HC_normal_M_of_case_a_sec9
              M MF U W1 W2 H0 C p q a ubar hcase hBarU
          let source : Section1.ClassFunction HCD :=
            Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))
          ∀ h : HCD,
            source
              ⟨⟨w0M * ((h : Dm) : M) * w0M⁻¹,
                  hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩,
                by
                  change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
                  exact hHCnormal.conj_mem ((h : Dm) : M) h.property w0M⟩ =
              source h := by
  -- conjugation to a rotation of the transported `mu_f` product, and
  -- `cfConjgBigdprod` identifies the rotated component factors.
  classical
  intro hψformula hcase hBarU
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  have hHCleM : HC ≤ M := by
    dsimp [HC]
    exact (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase).trans
      (section12_ambientDerivedSubgroup_le (E := M))
  have hHCnormal : HCm.Normal := by
    dsimp [HCm, HC]
    exact theorem_9_8_HC_normal_M_of_case_a_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  have hconjHC : ∀ h : HC, (w0 : G) * (h : G) * (w0 : G)⁻¹ ∈ HC := by
    intro h
    let hM : M := ⟨(h : G), hHCleM h.property⟩
    let hHCm : HCm := ⟨hM, by
      simp [HCm, HC, hM, Subgroup.mem_subgroupOf]⟩
    have hmem : w0M * hHCm * w0M⁻¹ ∈ HCm :=
      hHCnormal.conj_mem hHCm hHCm.property w0M
    simpa [HCm, HC, hM, hHCm, w0M, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hrot :
      ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
        ∀ h : HC,
          θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC)
                ⟨(w0 : G) * (h : G) * (w0 : G)⁻¹, hconjHC h⟩)) =
            θH (μraw i)
              (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
    simpa [HC, H0C, e, θH] using
      H0CLinearCandidateXmu_ordered_generator_quotient_product_rotation_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hW1M w0 hw0gen hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
        hcase hBarU hconjHC
  dsimp only
  intro i h
  let hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  let hHCnormal' : HCm.Normal := by
    exact hHCnormal
  let hDm : Dm := (h : HCD)
  let hM : M := hDm
  let hHC : HC := ⟨(hM : G), by
    have hhHCm : hM ∈ HCm := h.property
    simpa [HCm, HC, hM, Subgroup.mem_subgroupOf] using hhHCm⟩
  have htargetHC :
      (⟨(w0 : G) * (hHC : G) * (w0 : G)⁻¹, hconjHC hHC⟩ : HC) =
        ⟨((⟨w0M * ((h : Dm) : M) * w0M⁻¹,
            hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩ : Dm) : M),
          by
            change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
            exact hHCnormal'.conj_mem ((h : Dm) : M) h.property w0M⟩ := by
    apply Subtype.ext
    simp [hHC, hM, hDm, w0M, mul_assoc]
  have hrot_i := hrot i hHC
  have hψapp :
      ψHC (μraw i) =
        Section1.quotientCharacterInflation H0C HC (θHC (μraw i)) := by
    simpa [HC, H0C, e, θH, θHC] using congrFun hψformula (μraw i)
  rw [hψapp]
  change
    (θHC (μraw i)
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          (⟨((⟨w0M * ((h : Dm) : M) * w0M⁻¹,
              hDnormal.conj_mem ((h : Dm) : M) (h : Dm).property w0M⟩ : Dm) : M),
            by
              change w0M * ((h : Dm) : M) * w0M⁻¹ ∈ HCm
              exact hHCnormal'.conj_mem ((h : Dm) : M) h.property w0M⟩ : HC)) : ℂ) =
      (θHC (μraw i) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) : ℂ)
  rw [← htargetHC]
  exact congrArg Units.val hrot_i

public theorem H0CLinearCandidateXmu_ordered_generator_inertia_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hW1M : W1 ≤ M)
    (w0 : W1)
    (hw0gen : Subgroup.zpowers w0 = ⊤)
    (hW1normU : W1 ≤ Subgroup.normalizer (U : Set G))
    (hμrawOrderedData :
      H0CLinearCandidateXmuOrderedTransportedRawCoordinateData_sec9
        (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 μraw)
    (hqpos : 0 < q)
    (hsucc :
      ∀ i : Fin q,
        quotientSubgroupConjugateByElement MF H0
          (H i) (H (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)) (w0 : G))
    (χbar : Fin q → (U ⧸ C.subgroupOf U) →*
      Multiplicative (ZMod aρ))
    (hχsep :
      ∀ i, ∀ x y : U ⧸ C.subgroupOf U,
        χbar i x = χbar i y → ρ i x = ρ i y)
    (hχtransition :
      letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
      ∀ x : U,
        ∀ i,
          χbar i (QuotientGroup.mk' (C.subgroupOf U) (w0 • x)) =
            χbar (theorem_9_7_fin_cyclic_succ_sec9 hqpos i)
              (QuotientGroup.mk' (C.subgroupOf U) x)) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
          (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
            let hDnormal : Dm.Normal := by
              simpa [Dm] using
                (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
            letI : Dm.Normal := hDnormal
            Section1.inertiaSubgroup Dm (θ (μorbit i)) := by
  -- transported `mu_f` component product, hence fixes its induced orbit class.
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  have hHCnormal : HCm.Normal := by
    dsimp [HCm]
    exact theorem_9_8_HC_normal_M_of_case_a_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCm.Normal := hHCnormal
  let w0M : M := ⟨(w0 : G), hW1M w0.property⟩
  dsimp only
  intro i
  change Section1.conjugateOnNormal Dm (θ (μorbit i)) w0M = θ (μorbit i)
  have hrel_out :
      MulAction.orbitRel (U ⧸ C.subgroupOf U) κ
        (Quotient.out (μorbit i)) (μraw i) := by
    rw [← Quotient.eq'']
    simp [μorbit, orbit]
  have htheta_out :
      θ (μorbit i) =
        Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := by
    have hθeq :
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let HC : Subgroup G := MF ⊔ C
        let H0C : Subgroup G := H0 ⊔ C
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := HC.subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        letI : HCD.Normal := by
          dsimp [HCD, HCm, Dm]
          exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
            M MF U W1 W2 H0 C p q a ubar hcase hBarU
        let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
          quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
        let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
          fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
        let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
          fun f => (θH f).comp e.symm.toMonoidHom
        let ψHC0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction HC :=
          fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
        let ψ0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction HCm :=
          fun f => Section1.subgroupOfClassFunction (ψHC0 f)
        let θ0 : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
            Section1.ClassFunction Dm :=
          fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ0 f))
        θ0 (Quotient.out (μorbit i)) = θ0 (μraw i) :=
      induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ hρaction hconj
        hH0CinfMF hsup hcase
        (by
          exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
            M MF U W1 W2 H0 C p q a ubar hcase hBarU)
        (Quotient.out (μorbit i)) (μraw i)
        (by simpa [instAction, κ] using hrel_out)
    have hψformula_out : ψHC (Quotient.out (μorbit i)) =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))
          (Quotient.out (μorbit i)) := by
      simpa using congrFun hψformula (Quotient.out (μorbit i))
    have hψformula_app : ψHC (μraw i) =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f)) (μraw i) := by
      simpa using congrFun hψformula (μraw i)
    simpa [κ, Dm, HCm, HCD, instAction, orbit, μorbit, ψ, θ, hψformula_out,
      hψformula_app] using hθeq
  have hsource :
      Section1.conjugateOnNormal Dm
          (Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))) w0M =
        Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := by
    refine conjugateOnNormal_inducedCF_eq_of_subgroupOf_source_conjugation_sec9
      Dm HCm
      (Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))
      (Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))
      w0M ?_
    intro h
    exact H0CLinearCandidateXmu_ordered_generator_source_conjugation_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw hW1M w0
      hw0gen hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
      hψformula hcase hBarU i h
  calc
    Section1.conjugateOnNormal Dm (θ (μorbit i)) w0M =
        Section1.conjugateOnNormal Dm
          (Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction
              (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i))))) w0M := by
          rw [htheta_out]
    _ = Section1.inducedCF HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (T := M) (ψHC (μraw i)))) := hsource
    _ = θ (μorbit i) := htheta_out.symm

public theorem H0CLinearCandidateXmu_transported_W1_generator_inertia_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        ∃ hW1M : W1 ≤ M,
          ∃ w0 : W1,
            Subgroup.zpowers w0 = ⊤ ∧
              let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
              let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
              let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
              let HCD : Subgroup Dm := HCm.subgroupOf Dm
              let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
                rawCoordinateMulAction_sec9 p q H hHcard ρ
              letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
              let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
              let instFintypeι : Fintype ι := Fintype.ofFinite ι
              let instDecidableEqι : DecidableEq ι := Classical.decEq ι
              letI : Fintype ι := instFintypeι
              letI : DecidableEq ι := instDecidableEqι
              let orbit : κ → ι := fun k => Quotient.mk'' k
              let ψ : ι → Section1.ClassFunction HCm :=
                fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
              let θ : ι → Section1.ClassFunction Dm :=
                fun i =>
                  Section1.inducedCF HCD
                    (Section1.subgroupOfClassFunction (ψ i))
              let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
                fun i => orbit (μraw i)
              ∀ i : H0CLinearCandidateXmuRawIndex_sec9 p,
                (⟨(w0 : G), hW1M w0.property⟩ : M) ∈
                  let hDnormal : Dm.Normal := by
                    simpa [Dm] using
                      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
                  letI : Dm.Normal := hDnormal
                  Section1.inertiaSubgroup Dm (θ (μorbit i)) := by
  -- rotates the transported component product and fixes the resulting
  -- induced `mu_f` character.
  classical
  intro hψformula hcase hBarU
  rcases hμrawOrderedActionData with
    ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, χbar,
      hχsep, hχtransition⟩
  refine ⟨W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1, w0,
    hw0gen, ?_⟩
  simpa using
    H0CLinearCandidateXmu_ordered_generator_inertia_bridge_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
      (W1_le_M_of_hypothesis_9_2_sec9 M MF U W1 W2 q hcase.1) w0 hw0gen
      hW1normU hμrawOrderedData hqpos hsucc χbar hχsep hχtransition
      hψformula hcase hBarU

public theorem H0CLinearCandidateXmu_transported_W1_inertia_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (μraw : H0CLinearCandidateXmuRawIndex_sec9 p →
      H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
          fun i => orbit (μraw i)
        H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
          μorbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let hDnormal : Dm.Normal := by
    simpa [Dm] using
      (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  rcases H0CLinearCandidateXmu_transported_W1_generator_inertia_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
      hμrawOrderedActionData
      hψformula hcase hBarU with
    ⟨hW1M, w0, hw0gen, hw0I⟩
  dsimp [H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9]
  intro i
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
    subgroupOf_le_inertiaSubgroup_of_zpowers_generator_mem_sec9
      Dm (θ (μorbit i)) w0 hW1M hw0gen
      (by
        simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ, μorbit] using
          hw0I i)

public theorem H0CLinearCandidateXmu_transported_orbit_W1_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  have horderedXmu_saved := horderedXmu
  rcases horderedXmu_saved with ⟨hW1normU, w0, hw0gen, hqpos, hsucc, χbar,
    hχsep, hχtransition⟩
  rcases H0CLinearCandidateXmuOrderedTransportedRawCoordinate_data_sec9
      (MF := MF) (H0 := H0) (W1 := W1) p q H hHcard w0 hqpos hsucc with
    ⟨μraw, hμrawOrderedData, hμrawData, _hμraw⟩
  refine ⟨μraw, ?_⟩
  have hμrawOrderedActionData :
      H0CLinearCandidateXmuOrderedTransportedRawActionData_sec9
        (MF := MF) (U := U) (W1 := W1) (H0 := H0) (C := C)
        p q aρ H hHcard ρ μraw := by
    exact ⟨hW1normU, w0, hw0gen, hμrawOrderedData, hqpos, hsucc, χbar,
      hχsep, hχtransition⟩
  have hW1Inertia :
      H0CLinearCandidateXmuConstantW1InertiaDataWithRaw_sec9 M W1 p ι
        (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) θ := by
    simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
      H0CLinearCandidateXmu_transported_W1_inertia_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        hψformula hcase hBarU
  have hfinalInjective :
      H0CLinearCandidateXmuFinalInjectiveDataWithRaw_sec9 M p ι
        (fun i : H0CLinearCandidateXmuRawIndex_sec9 p => orbit (μraw i)) θ := by
    simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
      H0CLinearCandidateXmu_transported_final_injective_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup μraw
        hμrawOrderedActionData
        (by simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using hW1Inertia)
        hψformula hcase hBarU
  exact ⟨hfinalInjective, hW1Inertia⟩

public theorem H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
        let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
        let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
        let HCD : Subgroup Dm := HCm.subgroupOf Dm
        let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
        let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
        let instFintypeι : Fintype ι := Fintype.ofFinite ι
        let instDecidableEqι : DecidableEq ι := Classical.decEq ι
        letI : Fintype ι := instFintypeι
        letI : DecidableEq ι := instDecidableEqι
        let orbit : κ → ι := fun k => Quotient.mk'' k
        let ψ : ι → Section1.ClassFunction HCm :=
          fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
        let θ : ι → Section1.ClassFunction Dm :=
          fun i =>
            Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction (ψ i))
        H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ := by
  classical
  intro hψformula hcase hBarU
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  simpa [κ, Dm, HCm, HCD, instAction, orbit, ψ, θ] using
    H0CLinearCandidateXmu_transported_orbit_W1_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU

public theorem H0CLinearCandidateXmu_transported_final_image_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
            rawCoordinateMulAction_sec9 p q H hHcard ρ
          letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
          let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
          let instFintypeι : Fintype ι := Fintype.ofFinite ι
          let instDecidableEqι : DecidableEq ι := Classical.decEq ι
          letI : Fintype ι := instFintypeι
          letI : DecidableEq ι := instDecidableEqι
          let ψ : ι → Section1.ClassFunction HCm :=
            fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
          let θ : ι → Section1.ClassFunction Dm :=
            fun i =>
              Section1.inducedCF HCD
                (Section1.subgroupOfClassFunction (ψ i))
          H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
  classical
  intro hψformula hcase hBarU hSH0C
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let orbit : κ → ι := fun k => Quotient.mk'' k
  have htransport :
      H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ :=
    H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU
  rcases htransport with ⟨μraw, hfinalInjective, hW1Inertia⟩
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  have hcore :
      H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
      M MF U W1 W2 H0 C p q a SH0C μorbit θ hcase hSH0C
      hfinalInertia hfinalInjective
  have hsmu :
      H0CLinearCandidateXmuSmuDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuDataWithRaw_of_coreData_sec9
      M MF H0 C p SH0C ι μorbit θ hcore
  have hsep :
      H0CLinearCandidateXmuFinalSeparationDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ :=
    H0CLinearCandidateXmuFinalSeparationDataWithRaw_of_smuData_sec9
      M MF H0 C p SH0C ι μorbit θ hsmu
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hredCard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  have hconcrete :
      H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_sec9 M MF H0 C p
        SH0C ι μorbit θ :=
    H0CLinearCandidateXmuConcreteFinalImageDataWithRaw_of_final_separation_sec9
      M MF H0 C p SH0C ι μorbit θ hredCard hsep
  exact H0CLinearCandidateXmuFinalImageData_of_concrete_final_image_withRaw_sec9
    M MF H0 C p SH0C ι μorbit θ hconcrete

public theorem H0CLinearCandidateXmu_transported_residual_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  classical
  intro hψformula hcase hBarU hSH0C
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  let orbit : κ → ι := fun k => Quotient.mk'' k
  have htransport :
      H0CLinearCandidateXmuTransportedRawData_sec9 M W1 p κ ι orbit θ :=
    H0CLinearCandidateXmu_transported_raw_data_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ ubar ψHC H hHcard hHnorm hHindep hHsup
      ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
      hψformula hcase hBarU
  rcases htransport with ⟨μraw, hfinalInjective, hW1Inertia⟩
  let μorbit : H0CLinearCandidateXmuRawIndex_sec9 p → ι :=
    fun i => orbit (μraw i)
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : HCD.Normal := hnormalHCD
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let hMFHC : MF ≤ HC := le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψformula' : ψHC = fun f => Section1.quotientCharacterInflation H0C HC (θHC f) := by
    simpa [κ, HC, H0C, hMFHC, e, θH, θHC] using hψformula
  have hψirr : ∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  have hψdeg : ∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ) := by
    intro f
    rw [hψformula']
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  have hψker : ∀ f : κ,
      Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC) := by
    intro f
    rw [hψformula']
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  have hψnonker : ∀ f : κ,
      ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
    intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf, HC]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [hψformula', Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by
            simpa [Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)
  have hθdata_full :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hθclass : ∀ i : ι, Section1.IsClassFunction (θ i) := by
    intro i
    dsimp [θ]
    exact Section1.inducedCF_isClassFunction HCD (Section1.subgroupOfClassFunction (ψ i))
  have hconstFinal :
      H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ :=
    H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_of_W1InertiaData_sec9
      M MF U W1 W2 H0 C p q a μorbit θ hcase hθclass
      (by simpa [μorbit] using hW1Inertia)
  have hfinalInertia :
      H0CLinearCandidateXmuFinalInertiaDataWithRaw_sec9 M MF H0 C p
        ι μorbit θ := by
    dsimp [H0CLinearCandidateXmuConstantFinalInertiaDataWithRaw_sec9] at hconstFinal
    refine ⟨hθinj, ?_, ?_⟩
    · simpa [μorbit, θ, Dm, HCm, HCD] using hconstFinal
    · intro i
      rcases hθdata_full i with ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
      exact ⟨hθirr, hθnotMF, hθker⟩
  have hcore :
      H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9 M MF H0 C p SH0C
        ι μorbit θ :=
    H0CLinearCandidateXmuSmuCoreDataWithRaw_of_finalInertiaData_sec9
      M MF U W1 W2 H0 C p q a SH0C μorbit θ hcase hSH0C
      hfinalInertia hfinalInjective
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hredCard :
      (reducibleCharacterFilter_sec9 M SH0C).card = p - 1 :=
    theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
      M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
      hH0CnormalM hH0CD hH0CinfMF hSH0C
  dsimp [H0CLinearCandidateXmuSmuCoreDataWithRaw_sec9] at hcore
  rcases hcore with ⟨hfinalInj, htop, hred, _himage⟩
  refine ⟨ULift.{u} (H0CLinearCandidateXmuRawIndex_sec9 p), inferInstance,
    Classical.decEq _, ?_⟩
  refine ⟨fun i => θ (μorbit i.down), ?_, ?_, ?_, ?_⟩
  · simp
  · intro i j hij
    apply ULift.ext
    apply hfinalInj
    simpa [Dm] using hij
  · intro i
    rcases hθdata_full (μorbit i.down) with
      ⟨hθirr, hθnotMF, hθker, _hψirr_i, _hψdeg_i⟩
    exact ⟨hθirr, hθnotMF, hθker, by simpa [Dm] using htop i.down,
      by simpa [Dm] using hred i.down⟩
  · intro χ hχred
    let μfinal :
        ULift.{u} (H0CLinearCandidateXmuRawIndex_sec9 p) →
          Section1.ClassFunction M :=
      fun i => Section1.inducedCF Dm (θ (μorbit i.down))
    let Smu : Finset (Section1.ClassFunction M) := Finset.univ.image μfinal
    have hSmuSub : Smu ⊆ reducibleCharacterFilter_sec9 M SH0C := by
      intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨i, _hi, rfl⟩
      simpa [μfinal, Dm] using hred i.down
    have hfinalInjLift : Function.Injective μfinal := by
      intro i j hij
      apply ULift.ext
      apply hfinalInj
      simpa [μfinal, Dm] using hij
    have hSmuCard : Smu.card = p - 1 := by
      rw [Finset.card_image_of_injective _ hfinalInjLift]
      simp
    have hSmuEq : Smu = reducibleCharacterFilter_sec9 M SH0C :=
      Finset.eq_of_subset_of_card_le hSmuSub (by rw [hredCard, hSmuCard])
    have hχSmu : χ ∈ Smu := by
      rw [hSmuEq]
      exact hχred
    rcases Finset.mem_image.mp hχSmu with ⟨i, _hi, hiχ⟩
    exact ⟨i, hiχ.symm⟩

public theorem H0CLinearCandidateXmu_final_subfamily_of_orbit_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ ubar : ℕ)
    (SH0C : Finset (Section1.ClassFunction M))
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G)))
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (_hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hnormalC : (C.subgroupOf U).Normal)
    (ρ : ∀ i, (U ⧸ C.subgroupOf U) →* MulAut (H i))
    (hρcyc : ∀ i, IsCyclic (ρ i).range)
    (hρcard : ∀ i, Nat.card (ρ i).range = aρ)
    (hρaction :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF, ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H i,
              (ρ i x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρker :
      ∀ i, ∀ x : U ⧸ C.subgroupOf U,
        ρ i x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H i) (u : G))
    (horderedXmu : H0COrderedXmuCoordinateData_sec9 MF U W1 H0 C q aρ H ρ)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤) :
    (ψHC =
        (let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
         let HC : Subgroup G := MF ⊔ C
         let H0C : Subgroup G := H0 ⊔ C
         let hMFHC : MF ≤ HC := le_sup_left
         let e : (MF ⧸ H0.subgroupOf MF) ≃*
             (HC ⧸ H0C.subgroupOf HC) :=
           quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
         let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
           fun f =>
             componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
               f.down
         let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
           fun f => (θH f).comp e.symm.toMonoidHom
         fun f => Section1.quotientCharacterInflation H0C HC (θHC f))) →
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C ubar →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          Function.Injective ψHC →
            (∀ f, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) →
              (∀ f, Section1.degree (ψHC f) = (1 : ℂ)) →
                (∀ f, Section1.subgroupInKernel' (ψHC f)
                  ((H0 ⊔ C).subgroupOf (MF ⊔ C))) →
                  (∀ f, ¬ Section1.subgroupInKernel' (ψHC f)
                    (MF.subgroupOf (MF ⊔ C))) →
                      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
                        M MF U H0 C p q ubar ψHC →
                      H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q ubar SH0C := by
  classical
  intro hψformula hcase hBarU hSH0C _hψinj hψirr hψdeg hψker hψnonker _hcoord
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  have hnormalHCD : HCD.Normal := by
    dsimp [HCD, HCm, Dm]
    exact theorem_9_8_HC_normal_ambientDerived_subgroupOf_sec9
      M MF U W1 W2 H0 C p q a ubar hcase hBarU
  letI : (C.subgroupOf U).Normal := hnormalC
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let instAction : MulAction (U ⧸ C.subgroupOf U) κ :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let instFintypeι : Fintype ι := Fintype.ofFinite ι
  let instDecidableEqι : DecidableEq ι := Classical.decEq ι
  letI : Fintype ι := instFintypeι
  letI : DecidableEq ι := instDecidableEqι
  let orbit : κ → ι := fun k => Quotient.mk'' k
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (Quotient.out i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  letI : HCD.Normal := hnormalHCD
  have hstab : ∀ k : κ, MulAction.stabilizer (U ⧸ C.subgroupOf U) k = ⊥ :=
    rawCoordinateMulAction_stabilizer_eq_bot_sec9
      hcase H hHcard hHnorm hHsup ρ hρaction
  have hbarCard : Nat.card (U ⧸ C.subgroupOf U) = ubar := by
    rcases hBarU with ⟨_hC_le_U, _hnormalBarC, hbarCard⟩
    simpa using hbarCard
  have hrawCoord :
      (∀ k : κ,
        Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction
              ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k)) =
          HCD) ∧
        ∀ k l : κ,
          (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) k =
            (fun k => Section1.inducedCF HCD
              (Section1.subgroupOfClassFunction
                ((fun k => Section1.subgroupOfClassFunction (ψHC k)) k))) l ↔
              MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    simpa [instAction, κ, Dm, HCm, HCD] using
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  have hIeq : ∀ i : ι,
      Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) = HCD := by
    intro i
    simpa [ψ, HCm] using hrawCoord.1 (Quotient.out i)
  have hθinj : Function.Injective θ := by
    intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hrawCoord.2]
      simpa [θ, ψ, Dm, HCm, HCD] using hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  have hfiber : ∀ i : ι, Fintype.card {k : κ // orbit k = i} = ubar := by
    intro i
    rw [← hbarCard]
    rw [← Nat.card_eq_fintype_card]
    exact freeAction_orbitQuotient_fiber_natCard_sec9 (A := U ⧸ C.subgroupOf U)
      (κ := κ) hstab i
  have hκcard :
      Fintype.card κ = (p - 1) ^ q :=
    theorem_9_8_Ftheta_raw_choice_card_sec9 p q
  have hcardκ :
      Fintype.card κ = ubar * Fintype.card ι :=
    card_eq_mul_card_of_fiber_card_sec9 orbit ubar hfiber
  have hθcard : ubar * Fintype.card ι = (p - 1) ^ q := by
    rw [← hcardκ]
    exact hκcard
  have hθdata :
      ∀ i : ι,
        Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
          ¬ Section1.subgroupInKernel' (θ i)
            ((MF.subgroupOf M).subgroupOf Dm) ∧
          Section1.subgroupInKernel' (θ i)
            (((H0 ⊔ C).subgroupOf M).subgroupOf Dm) ∧
          Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
          Section1.degree (ψ i) = (1 : ℂ) :=
    H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
      M MF U W1 W2 H0 C p q a (ψHC := ψHC) (ι := ι) Quotient.out
      hcase hψirr hψdeg hψker hψnonker hnormalHCD hIeq
  have hXmu :
      H0CLinearCandidateXmuFinalImageData_sec9 M MF H0 C p SH0C ι θ := by
    exact
      H0CLinearCandidateXmu_transported_final_image_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ ubar SH0C ψHC H hHcard hHnorm hHindep hHsup
        ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup
        hψformula hcase hBarU hSH0C
  dsimp [H0CLinearCandidateXmuFinalImageData_sec9] at hXmu
  rcases hXmu with ⟨Xmu, hXmucard, hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  refine ⟨ι, instFintypeι, instDecidableEqι, θ, ψ, ?_, hθcard, ?_,
    Xmu, hXmucard, hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  · simpa [θ, ψ, Dm, HCm, HCD] using hθinj
  · intro i
    rcases hθdata i with ⟨hθirr, hθnotMF, hθkerH0C, hψirr_i, hψdeg_i⟩
    exact ⟨hθirr, hθnotMF, hθkerH0C, hψirr_i, hψdeg_i, rfl⟩

public theorem theorem_9_8_H0C_linear_candidate_Xmu_final_subfamily_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
            H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q u SH0C := by
  intro hcase hBarU hSH0C hordered
  rcases H0COrderedXmuCoordinateData_of_ordered_sec9 MF U W1 H0 C p q hordered with
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩
  rcases theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hcase with
    ⟨hcomm, hnormalH0C, hH0CinfMF, hsup, ψHC, hψformula, hψinj, hψirr,
      hψdeg, hψker, hψnonker⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  letI : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := hnormalH0C
  have hcore :
      H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
        M MF U H0 C p q ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_concrete_formula_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup hfac hconj
      hnormalC hH0CinfMF hsup ψHC hcase hψformula
  have haction :
      H0CLinearCandidateXthetaThetaCoordinateActionData_sec9
        M MF U H0 C p q u ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_of_core_data_sec9
      M MF U H0 C p q u ψHC hBarU hcore
  have horbitData :
      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9
        M MF U H0 C p q u ψHC :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_orbit_of_action_data_sec9
      M MF U H0 C p q u ψHC haction
  exact H0CLinearCandidateXmu_final_subfamily_of_orbit_data_source_core_sec9
    M MF U W1 W2 H0 C p q a aρ u SH0C ψHC H hHcard hHnorm hHindep hHsup
    hfac hconj hnormalC ρ hρcyc hρcard hρaction hρker horderedXmu hH0CinfMF hsup hψformula
    hcase hBarU hSH0C hψinj hψirr hψdeg hψker hψnonker horbitData

public theorem theorem_9_8_H0C_linear_candidate_Xmu_residual_data_ordered_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q →
            H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  intro hcase hBarU hSH0C hordered
  rcases H0COrderedXmuCoordinateData_of_ordered_sec9 MF U W1 H0 C p q hordered with
    ⟨aρ, hnormalH0, hnormalC, H, hHcard, hHnorm, hHindep, hHsup, _hfac,
      hconj, ρ, hρcyc, hρcard, hρaction, hρker, horderedXmu⟩
  rcases theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hcase with
    ⟨hcomm, hnormalH0C, hH0CinfMF, hsup, ψHC, hψformula, _hψinj, _hψirr,
      _hψdeg, _hψker, _hψnonker⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal := hnormalH0C
  exact H0CLinearCandidateXmu_transported_residual_data_source_core_sec9
    M MF U W1 W2 H0 C p q a aρ u SH0C ψHC H hHcard hHnorm hHindep hHsup
    ρ hρcyc hρcard hρaction hρker hconj horderedXmu hH0CinfMF hsup hψformula
    hcase hBarU hSH0C

public theorem theorem_9_8_H0C_linear_candidate_Xmu_Dmu_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuDmuData_sec9 M MF H0 C p q u SH0C := by
  classical
  intro hcase hBarU hSH0C
  have hordered :
      H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q :=
    theorem_9_7_orderedCaseAComponentTransitionData_of_case_a_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_Xmu_final_subfamily_source_core_sec9
    M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C hordered

public theorem theorem_9_8_H0C_linear_candidate_Xmu_residual_data_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          H0CLinearCandidateXmuResidualData_sec9 M MF H0 C p SH0C := by
  classical
  intro hcase hBarU hSH0C
  have hordered :
      H0COrderedComponentCharacterFamilyData_sec9 MF U W1 H0 C p q :=
    theorem_9_7_orderedCaseAComponentTransitionData_of_case_a_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU
  exact theorem_9_8_H0C_linear_candidate_Xmu_residual_data_ordered_source_core_sec9
    M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C hordered

public theorem theorem_9_8_H0C_linear_candidate_Xmu_Dmu_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          reducibleCharacterFilter_sec9 M SH0C ⊆
              linearHCCharacterFilter_sec9 M MF C SH0C ∧
            ∃ χ : Section1.ClassFunction M,
              χ ∈ SH0C ∧
                Section1.IsIrreducibleCharacterOnGroup χ ∧
                Section1.degree χ = (q * u : ℂ) ∧
                inducedFromLinearCharacterOfHC M MF C χ := by
  classical
  intro hcase hBarU hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_Dmu_data_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨ι, instFintype, instDecidableEq, θ, ψ, hθinj, hθcard, hθdata, Xmu,
      hXmucard, _hXmu_red, hred_sub_Xmu, hXmu_sep⟩
  letI : Fintype ι := instFintype
  letI : DecidableEq ι := instDecidableEq
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  have hHCm_le_Dm : HCm ≤ Dm := by
    have hHC_le_D : MF ⊔ C ≤ ambientDerivedSubgroup M :=
      theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase
    intro x hx
    change ((x : M) : G) ∈ ambientDerivedSubgroup M
    exact hHC_le_D (by simpa [HCm, Subgroup.mem_subgroupOf] using hx)
  have hlinear_induced :
      ∀ i : ι, inducedFromLinearCharacterOfHC M MF C (Section1.inducedCF Dm (θ i)) := by
    intro i
    dsimp [inducedFromLinearCharacterOfHC, inducedFromLinearCharacter]
    refine ⟨ψ i, (hθdata i).2.2.2.1, (hθdata i).2.2.2.2.1, ?_⟩
    calc
      Section1.inducedCF Dm (θ i) =
          Section1.inducedCF Dm
            (Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))) := by
            rw [(hθdata i).2.2.2.2.2]
      _ = Section1.inducedCF HCm (ψ i) := by
            simpa [Dm, HCm, HCD] using
              Section1.inducedCF_trans HCm Dm hHCm_le_Dm (ψ i)
  have hred_linear :
      reducibleCharacterFilter_sec9 M SH0C ⊆
        linearHCCharacterFilter_sec9 M MF C SH0C := by
    intro χ hχred
    rcases hred_sub_Xmu χ hχred with ⟨i, _hiXmu, hχeq⟩
    have hχSH0C : χ ∈ SH0C := by
      have hχpair : χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
        simpa [reducibleCharacterFilter_sec9] using hχred
      exact hχpair.1
    have hlin : inducedFromLinearCharacterOfHC M MF C χ := by
      rw [hχeq]
      exact hlinear_induced i
    exact Finset.mem_filter.mpr ⟨hχSH0C, hlin⟩
  have hnot_all_Xmu : ¬ Finset.univ ⊆ Xmu := by
    intro hall
    have hXmu_eq_univ : Xmu = Finset.univ :=
      Finset.eq_univ_of_forall fun i => hall (by simp)
    have hcard_univ : Fintype.card ι = p - 1 := by
      calc
        Fintype.card ι = (Finset.univ : Finset ι).card := by simp
        _ = Xmu.card := by rw [hXmu_eq_univ]
        _ = p - 1 := hXmucard
    have hcount_eq : ((p - 1) ^ q) / u = p - 1 := by
      have hdiv_eq : Fintype.card ι = ((p - 1) ^ q) / u :=
        card_eq_div_of_left_mul_card_eq_sec9
        (quotientBarUCardinality_pos_sec9 U C u hBarU) hθcard
      exact hdiv_eq.symm.trans hcard_univ
    exact theorem_9_8_H0C_linear_candidate_count_ne_core_sec9
      M MF U W1 W2 H0 C p q a u hcase hBarU hcount_eq
  have hex_not_Xmu : ∃ j : ι, j ∉ Xmu := by
    by_contra hno
    apply hnot_all_Xmu
    intro j _hj
    by_contra hj_not
    exact hno ⟨j, hj_not⟩
  rcases hex_not_Xmu with ⟨j, hj_not_Xmu⟩
  have hχred_not :
      Section1.inducedCF Dm (θ j) ∉ reducibleCharacterFilter_sec9 M SH0C := by
    intro hχred
    rcases hred_sub_Xmu (Section1.inducedCF Dm (θ j)) hχred with ⟨i, hiXmu, hij⟩
    exact hXmu_sep i hiXmu j hj_not_Xmu hij.symm
  have hχSH0C : Section1.inducedCF Dm (θ j) ∈ SH0C := by
    rcases hSH0C with ⟨_hYle, _hMFle, hmem⟩
    rw [hmem]
    exact ⟨θ j, (hθdata j).1, (hθdata j).2.1, (hθdata j).2.2.1, rfl⟩
  have hχirr : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF Dm (θ j)) := by
    by_contra hnot
    exact hχred_not (by
      simp [reducibleCharacterFilter_sec9, hχSH0C, hnot])
  have hχlin : inducedFromLinearCharacterOfHC M MF C (Section1.inducedCF Dm (θ j)) :=
    hlinear_induced j
  have hχdeg : Section1.degree (Section1.inducedCF Dm (θ j)) = (q * u : ℂ) := by
    have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
      HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u
        (case_9_7_a_hypothesis_9_2_sec9 hcase) hBarU
    exact degree_eq_q_mul_u_of_linear_HC_sec9
      M MF C q u (Section1.inducedCF Dm (θ j)) hidx hχlin
  exact ⟨hred_linear, ⟨Section1.inducedCF Dm (θ j), hχSH0C, hχirr, hχdeg, hχlin⟩⟩

public theorem theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          ∃ L : Finset (Section1.ClassFunction M),
            L.card = p - 1 ∧
              L ⊆ SH0C ∧
              (∀ χ : Section1.ClassFunction M, χ ∈ L →
                inducedFromLinearCharacterOfHC M MF C χ) ∧
              reducibleCharacterFilter_sec9 M SH0C ⊆ L ∧
              ∃ χ : Section1.ClassFunction M,
                χ ∈ SH0C ∧
                  Section1.IsIrreducibleCharacterOnGroup χ ∧
                  Section1.degree χ = (q * u : ℂ) ∧
                  inducedFromLinearCharacterOfHC M MF C χ := by
  classical
  intro hcase hBarU hSH0C
  let R : Finset (Section1.ClassFunction M) := reducibleCharacterFilter_sec9 M SH0C
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hC : quotientCentralizerIn MF H0 U C :=
    case_9_7_a_quotientCentralizerIn_sec9 hcase
  have hpprime : Nat.Prime p := case_9_7_a_p_prime_sec9 hcase
  have hpData :
      ∃ hp : Nat.Primes,
        hp.val = p ∧
          hoReductionData M MF U W2 H0 hp ∧
            quotientChiefFactorData_9_6 M MF H0 W1 hp := by
    rcases hcase with
      ⟨_h92, _hH0MF, _hC, _hpprime, _hqprime, hpData, _hrest⟩
    exact hpData
  have hH0CnormalM : ((H0 ⊔ C).subgroupOf M).Normal :=
    theorem_9_H0C_normal_M_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hH0CD : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      h92 hH0MF hC
  have hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0 :=
    theorem_9_H0C_inf_MF_eq_H0_source_core_sec9 M MF U W1 W2 H0 C p q
      h92 hH0MF hC hpprime hpData
  have hRcard : R.card = p - 1 := by
    simpa [R] using
      theorem_9_nb_redM_count_of_normal_le_inter_source_core_sec9
        M MF U W1 W2 H0 (H0 ⊔ C) p q SH0C h92 hH0MF hpprime hpData
        hH0CnormalM hH0CD hH0CinfMF hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_Dmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨hred_linear, hwitness⟩
  have hRsubSH0C : R ⊆ SH0C := by
    intro χ hχR
    have hχ : χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
      simpa [R, reducibleCharacterFilter_sec9] using hχR
    exact hχ.1
  have hRlin :
      ∀ χ : Section1.ClassFunction M, χ ∈ R →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχR
    have hχlinFilter : χ ∈ linearHCCharacterFilter_sec9 M MF C SH0C :=
      hred_linear (by simpa [R] using hχR)
    have hχlin :
        χ ∈ SH0C ∧ inducedFromLinearCharacterOfHC M MF C χ := by
      simpa [linearHCCharacterFilter_sec9] using hχlinFilter
    exact hχlin.2
  exact ⟨R, hRcard, hRsubSH0C, hRlin, by intro χ hχ; simpa [R] using hχ,
    hwitness⟩

public theorem theorem_9_8_H0C_linear_candidate_reducible_subset_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a u : ℕ)
    (SH0C : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
          reducibleCharacterFilter_sec9 M SH0C ⊆
            linearHCCharacterFilter_sec9 M MF C SH0C := by
  classical
  intro hcase hBarU hSH0C
  rcases theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨L, _hLcard, _hLsubSH0C, hLlin, hred_mem_L, _hwitness⟩
  intro χ hχred
  have hχred_pair :
      χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    simpa [reducibleCharacterFilter_sec9] using hχred
  rcases hχred_pair with
    ⟨hχSH0C, hχred'⟩
  have hχL : χ ∈ L := hred_mem_L hχred
  exact Finset.mem_filter.mpr ⟨hχSH0C, hLlin χ hχL⟩


public theorem theorem_9_8_reducible_filter_count_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R0 RC : Finset (Section1.ClassFunction M),
                  R0.card = p - 1 ∧
                    RC.card = p - 1 ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ R0 ↔
                        χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
  intro hcase _hBarU _hUprime hSH0 hSH0C _hSH0U
  rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
  exact theorem_9_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C p q SH0 SH0C h92 hH0MF hC hpprime hpData
      hSH0 hSH0C

public theorem theorem_9_8_reducible_filter_count_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R0 RC : Finset (Section1.ClassFunction M),
                  R0.card = p - 1 ∧
                    RC.card = p - 1 ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ R0 ↔
                        χ ∈ SH0 ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    (∀ χ : Section1.ClassFunction M,
                      χ ∈ RC ↔
                        χ ∈ SH0C ∧ ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ RC →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_filter_count_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem⟩
  have hred_sub_linear :
      reducibleCharacterFilter_sec9 M SH0C ⊆
        linearHCCharacterFilter_sec9 M MF C SH0C :=
    theorem_9_8_H0C_linear_candidate_reducible_subset_source_bridge_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C
  have hRClin :
      ∀ χ : Section1.ClassFunction M, χ ∈ RC →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχRC
    rcases (hRCmem χ).1 hχRC with ⟨hχSH0C, hχred⟩
    have hχredMem : χ ∈ reducibleCharacterFilter_sec9 M SH0C := by
      simp [reducibleCharacterFilter_sec9, hχSH0C, hχred]
    have hχlinMem : χ ∈ linearHCCharacterFilter_sec9 M MF C SH0C :=
      hred_sub_linear hχredMem
    have hmem :
        χ ∈ SH0C ∧ inducedFromLinearCharacterOfHC M MF C χ := by
      simpa [linearHCCharacterFilter_sec9] using hχlinMem
    exact hmem.2
  exact ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem, hRClin⟩

public theorem theorem_9_8_reducible_subfamily_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R : Finset (Section1.ClassFunction M),
                  R.card = p - 1 ∧
                    R ⊆ SH0 ∧
                    (∀ χ : Section1.ClassFunction M, χ ∈ R →
                      ¬ Section1.IsIrreducibleCharacterOnGroup χ) ∧
                    (∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
                      ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R) ∧
                    R ⊆ SH0C ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ R →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_filter_count_linear_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R0, RC, hR0card, hRCcard, hR0mem, hRCmem, hRClin⟩
  have hSH0CsubSH0 : SH0C ⊆ SH0 :=
    kernelInducedFamily_subset_of_le_sec9 M (ambientDerivedSubgroup M) MF
      H0 (H0 ⊔ C) SH0 SH0C le_sup_left hSH0 hSH0C
  have hRCsubR0 : RC ⊆ R0 := by
    intro χ hχRC
    rcases (hRCmem χ).1 hχRC with ⟨hχSH0C, hχred⟩
    exact (hR0mem χ).2 ⟨hSH0CsubSH0 hχSH0C, hχred⟩
  have hRCeqR0 : RC = R0 :=
    Finset.eq_of_subset_of_card_le hRCsubR0 (by rw [hR0card, hRCcard])
  have hR0subSH0 : R0 ⊆ SH0 := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).1
  have hR0nonirr :
      ∀ χ : Section1.ClassFunction M, χ ∈ R0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ := by
    intro χ hχR0
    exact ((hR0mem χ).1 hχR0).2
  have hR0all :
      ∀ χ : Section1.ClassFunction M, χ ∈ SH0 →
        ¬ Section1.IsIrreducibleCharacterOnGroup χ → χ ∈ R0 := by
    intro χ hχSH0 hχred
    exact (hR0mem χ).2 ⟨hχSH0, hχred⟩
  have hR0subSH0C : R0 ⊆ SH0C := by
    intro χ hχR0
    have hχRC : χ ∈ RC := by
      rw [hRCeqR0]
      exact hχR0
    exact ((hRCmem χ).1 hχRC).1
  have hR0lin :
      ∀ χ : Section1.ClassFunction M, χ ∈ R0 →
        inducedFromLinearCharacterOfHC M MF C χ := by
    intro χ hχR0
    have hχRC : χ ∈ RC := by
      rw [hRCeqR0]
      exact hχR0
    exact hRClin χ hχRC
  exact ⟨R0, hR0card, hR0subSH0, hR0nonirr, hR0all, hR0subSH0C, hR0lin⟩

public theorem theorem_9_8_reducible_subfamily_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ R : Finset (Section1.ClassFunction M),
                  R.card = p - 1 ∧
                    reducibleCharacterSubfamilyData M SH0 R (q * u) ∧
                    R ⊆ SH0C ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ R →
                      inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_reducible_subfamily_linear_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨R, hRcard, hRsubSH0, hRnonirr, hRall, hRsubSH0C, hRlin⟩
  have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u hcase.1
      hBarU
  have hRdata : reducibleCharacterSubfamilyData M SH0 R (q * u) := by
    refine ⟨hRsubSH0, ?_, hRall⟩
    intro χ hχR
    have hdeg :
        Section1.degree χ = (q * u : ℂ) :=
      degree_eq_q_mul_u_of_linear_HC_sec9 M MF C q u χ hidx (hRlin χ hχR)
    exact ⟨hRnonirr χ hχR, by simpa [Nat.cast_mul] using hdeg⟩
  exact ⟨R, hRcard, hRdata, hRsubSH0C, hRlin⟩

public theorem theorem_9_8_irreducible_H0C_linear_witness_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ χ : Section1.ClassFunction M,
                  χ ∈ SH0C ∧
                    Section1.IsIrreducibleCharacterOnGroup χ ∧
                    inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_H0C_linear_candidate_Xmu_source_core_sec9
      M MF U W1 W2 H0 C p q a u SH0C hcase hBarU hSH0C with
    ⟨_L, _hLcard, _hLsub, _hLlin, _hred_sub, χ, hχSH0C, hχirr, _hχdeg, hχlin⟩
  exact ⟨χ, hχSH0C, hχirr, hχlin⟩

public theorem theorem_9_8_irreducible_H0C_linear_source_bridge_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0 SH0C SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF H0 SH0 →
            kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ C) SH0C →
              kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
                ∃ χ : Section1.ClassFunction M,
                  χ ∈ SH0C ∧
                    Section1.IsIrreducibleCharacterOnGroup χ ∧
                    Section1.degree χ = (q * u : ℂ) ∧
                    inducedFromLinearCharacterOfHC M MF C χ := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_irreducible_H0C_linear_witness_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨χ, hχSH0C, hχirr, hχlin⟩
  have hidx : Subgroup.index ((MF ⊔ C).subgroupOf M) = q * u :=
    HC_index_eq_q_mul_u_of_hypothesis_9_2_sec9 M MF U W1 W2 C q u hcase.1
      hBarU
  exact ⟨χ, hχSH0C, hχirr,
    degree_eq_q_mul_u_of_linear_HC_sec9 M MF C q u χ hidx hχlin, hχlin⟩


end CFSG.Section9
