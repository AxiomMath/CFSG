module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.CaseA

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

public theorem quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
    {G : Type u} [Group G] [Finite G]
    (MF H0 HC H0C : Subgroup G)
    [(H0.subgroupOf MF).Normal]
    [(H0C.subgroupOf HC).Normal]
    (hMFHC : MF ≤ HC)
    (hH0CinfMF : H0C ⊓ MF = H0)
    (hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤)
    (u : G)
    (hconjMF : ∀ h : MF, u * (h : G) * u⁻¹ ∈ MF)
    (hconjH0C : ∀ h : H0C, u * (h : G) * u⁻¹ ∈ H0C)
    (hconjHC : ∀ h : HC, u * (h : G) * u⁻¹ ∈ HC)
    (β : MulAut (MF ⧸ H0.subgroupOf MF))
    (hβ : ∀ h : MF,
      β (QuotientGroup.mk' (H0.subgroupOf MF) h) =
        QuotientGroup.mk' (H0.subgroupOf MF) ⟨u * (h : G) * u⁻¹, hconjMF h⟩)
    (h : HC) :
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
    e.symm
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩) =
      β (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  classical
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let y : HC ⧸ H0C.subgroupOf HC := QuotientGroup.mk' (H0C.subgroupOf HC) h
  rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) (e.symm y) with
    ⟨m, hm⟩
  have hmy :
      QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) = y := by
    calc
      QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) =
          e (QuotientGroup.mk' (H0.subgroupOf MF) m) := rfl
      _ = y := by rw [hm, MulEquiv.apply_symm_apply]
  have hhm :
      QuotientGroup.mk' (H0C.subgroupOf HC) h =
        QuotientGroup.mk' (H0C.subgroupOf HC) (Subgroup.inclusion hMFHC m) := by
    simpa [y] using hmy.symm
  have hdivH0C : (h / Subgroup.inclusion hMFHC m : HC) ∈ H0C.subgroupOf HC := by
    exact (QuotientGroup.eq_iff_div_mem).1 hhm
  have hdivH0CG : (h : G) * (m : G)⁻¹ ∈ H0C := by
    simpa [Subgroup.mem_subgroupOf, div_eq_mul_inv] using hdivH0C
  let d : H0C := ⟨(h : G) * (m : G)⁻¹, hdivH0CG⟩
  have hconjQuot :
      QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩ =
        QuotientGroup.mk' (H0C.subgroupOf HC)
          (Subgroup.inclusion hMFHC ⟨u * (m : G) * u⁻¹, hconjMF m⟩) := by
    apply (QuotientGroup.eq_iff_div_mem).2
    have hd : u * (d : G) * u⁻¹ ∈ H0C := hconjH0C d
    simpa [Subgroup.mem_subgroupOf, d, div_eq_mul_inv, mul_assoc] using hd
  apply e.injective
  calc
    e (e.symm
        (QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩)) =
        QuotientGroup.mk' (H0C.subgroupOf HC)
          ⟨u * (h : G) * u⁻¹, hconjHC h⟩ := by
          rw [MulEquiv.apply_symm_apply]
    _ = QuotientGroup.mk' (H0C.subgroupOf HC)
          (Subgroup.inclusion hMFHC ⟨u * (m : G) * u⁻¹, hconjMF m⟩) :=
          hconjQuot
    _ = e (QuotientGroup.mk' (H0.subgroupOf MF)
          ⟨u * (m : G) * u⁻¹, hconjMF m⟩) := rfl
    _ = e (β (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h))) := by
          rw [← hβ m, ← hm]

public theorem quotientInfSupEquiv_symm_conj_eq_finiteInternalProductMulAut_symm_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
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
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x) :
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
      finiteInternalProductMulAut_sec9 H
        (by
          intro _i _j _hij y z _hy _hz
          exact mul_comm y z)
        hHindep hHsup (fun i => ρ i x)
    ∃ hconjHC : ∀ h : HC, (u : G) * (h : G) * (u : G)⁻¹ ∈ HC,
      ∀ h : HC,
        e.symm
            (QuotientGroup.mk' (H0C.subgroupOf HC)
              ⟨(u : G) * (h : G) * (u : G)⁻¹, hconjHC h⟩) =
          α.symm (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) h)) := by
  classical
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H
      (by
        intro _i _j _hij y z _hy _hz
        exact mul_comm y z)
      hHindep hHsup (fun i => ρ i x)
  rcases hconj with ⟨hqpos, _hconj⟩
  rcases finiteInternalProductMulAut_symm_eq_quotientConjAction_sec9
      H hHnorm hHindep hHsup ρ hρaction hqpos x u hux with
    ⟨hconjMF, hαsymm⟩
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hDleM : D ≤ M := by
    dsimp [D]
    exact section12_ambientDerivedSubgroup_le (E := M)
  have hUleM : U ≤ M := hUleD.trans hDleM
  have hHCleD : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCleM : HC ≤ M := hHCleD.trans hDleM
  have hH0CleD : H0C ≤ D := by
    dsimp [H0C, D]
    exact theorem_9_H0C_le_ambientDerived_of_source_sec9
      M MF U W1 W2 H0 C q h92
        (case_9_7_a_H0_le_MF_sec9 hcase)
        (case_9_7_a_quotientCentralizerIn_sec9 hcase)
  have hH0CleM : H0C ≤ M := hH0CleD.trans hDleM
  have hH0CnormalM : (H0C.subgroupOf M).Normal := by
    dsimp [H0C]
    rcases hcase with ⟨h92', hH0MF, hCcent, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_normal_M_source_core_sec9
      M MF U W1 W2 H0 C p q h92' hH0MF hCcent hpprime hpData
  have hconjH0C : ∀ h : H0C, (u : G) * (h : G) * (u : G)⁻¹ ∈ H0C := by
    intro h
    let uM : M := ⟨(u : G), hUleM u.property⟩
    let hM : M := ⟨(h : G), hH0CleM h.property⟩
    let hH0CM : H0C.subgroupOf M := ⟨hM, by
      simp [H0C, hM, Subgroup.mem_subgroupOf]⟩
    have hmem :
        uM * hH0CM * uM⁻¹ ∈ H0C.subgroupOf M :=
      hH0CnormalM.conj_mem hH0CM hH0CM.property uM
    simpa [H0C, uM, hM, hH0CM, Subgroup.mem_subgroupOf, mul_assoc] using hmem
  have hconjHC : ∀ h : HC, (u : G) * (h : G) * (u : G)⁻¹ ∈ HC := by
    intro h
    let uM : M := ⟨(u : G), hUleM u.property⟩
    let uD : Dm := ⟨uM, by
      change (u : G) ∈ D
      exact hUleD u.property⟩
    let hM : M := ⟨(h : G), hHCleM h.property⟩
    let hD : Dm := ⟨hM, by
      change (h : G) ∈ D
      exact hHCleD h.property⟩
    let hHCD : HCD := ⟨hD, by
      change (h : G) ∈ HC
      exact h.property⟩
    have hmem : uD * hHCD * uD⁻¹ ∈ HCD :=
      hnormalHCD.conj_mem hHCD hHCD.property uD
    change (u : G) * (h : G) * (u : G)⁻¹ ∈ HC at hmem
    exact hmem
  refine ⟨hconjHC, ?_⟩
  intro h
  exact quotientInfSupEquiv_symm_conj_eq_mulAut_sec9
    MF H0 HC H0C le_sup_left hH0CinfMF hsup
    (u : G) hconjMF hconjH0C hconjHC α.symm hαsymm h

public theorem quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
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
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (x : U ⧸ C.subgroupOf U) (u : U)
    (uD : (ambientDerivedSubgroup M).subgroupOf M)
    (hux : QuotientGroup.mk' (C.subgroupOf U) u = x)
    (huD : ((uD : M) : G) = (u : G))
    (f : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    letI : HCD.Normal := hnormalHCD
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun k => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup k.down
    let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
      fun k => (θH k).comp e.symm.toMonoidHom
    Section1.subgroupOfClassFunction
        (Section1.subgroupOfClassFunction
          (Section1.quotientCharacterInflation H0C HC (θHC (x • f)))) =
      Section1.conjugateOnNormal HCD
        (Section1.subgroupOfClassFunction
          (Section1.subgroupOfClassFunction
            (Section1.quotientCharacterInflation H0C HC (θHC f)))) uD := by
  classical
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun k => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup k.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun k => (θH k).comp e.symm.toMonoidHom
  let α : MulAut (MF ⧸ H0.subgroupOf MF) :=
    finiteInternalProductMulAut_sec9 H
      (by
        intro _i _j _hij y z _hy _hz
        exact mul_comm y z)
      hHindep hHsup (fun i => ρ i x)
  rcases quotientInfSupEquiv_symm_conj_eq_finiteInternalProductMulAut_symm_sec9
      M MF U W1 W2 H0 C p q a H hHnorm hHindep hHsup ρ
      hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u hux with
    ⟨hconjHC, hquot⟩
  have hraw :
      θH (x • f) = (θH f).comp α.symm.toMonoidHom := by
    dsimp [θH, α]
    exact componentProductLinearCharacter_rawCoordinateMulAction_sec9
      p q H hHcard hHindep hHsup ρ x f
  ext h
  let hDm : Dm := (h : HCD)
  let hM : M := hDm
  let hHC : HC := ⟨(hM : G), by
    have hhHCm : hM ∈ HCm := by
      exact h.property
    simpa [HCm, HC, hM, Subgroup.mem_subgroupOf] using hhHCm⟩
  let hConjHCByU : HC :=
    ⟨(u : G) * (hHC : G) * (u : G)⁻¹, hconjHC hHC⟩
  let hConjHCD : HCD :=
    ⟨uD * (h : Dm) * uD⁻¹, hnormalHCD.conj_mem h h.property uD⟩
  let hConjHCm : HCm := ⟨(hConjHCD : Dm), hConjHCD.property⟩
  let hConjHC : HC := ⟨((hConjHCm : M) : G), by
    exact hConjHCm.property⟩
  have hConjHC_mk :
      QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC =
        QuotientGroup.mk' (H0C.subgroupOf HC) hConjHCByU := by
    congr 1
    ext
    simp [hConjHC, hConjHCm, hConjHCD, hConjHCByU, hHC, hDm, hM, huD, mul_assoc]
  have hunit :
      θHC (x • f) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) =
        θHC f (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC) := by
    have happ := congrArg
      (fun χ : (MF ⧸ H0.subgroupOf MF) →* ℂˣ =>
        χ (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC))) hraw
    calc
      θHC (x • f) (QuotientGroup.mk' (H0C.subgroupOf HC) hHC) =
          θH (x • f) (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC)) := by
            rfl
      _ = θH f (α.symm
            (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hHC))) := by
            simpa using happ
      _ = θH f
            (e.symm (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC)) := by
            rw [hConjHC_mk, ← hquot hHC]
      _ = θHC f (QuotientGroup.mk' (H0C.subgroupOf HC) hConjHC) := by
            rfl
  simpa [Section1.subgroupOfClassFunction, Section1.quotientCharacterInflation,
    Section1.conjugateOnNormal, θHC, θH, hHC, hDm, hM, hConjHC, hConjHCm,
    hConjHCD, huD, mul_assoc] using congrArg Units.val hunit

public theorem inducedCF_conjugateOnNormal_sec9
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [hH : H.Normal]
    (theta : Section1.ClassFunction H) (g : G) :
    Section1.inducedCF H (Section1.conjugateOnNormal H theta g) =
      Section1.inducedCF H theta := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  funext y
  let f : G → ℂ := fun z =>
    if hz : z * y * z⁻¹ ∈ H then
      theta ⟨z * y * z⁻¹, hz⟩
    else
      0
  unfold Section1.inducedCF Section1.inducedClassFunction
  have hsum :
      ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            Section1.conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0) =
        ∑ x : G, f (g * x) := by
    refine Finset.sum_congr rfl ?_
    intro x _hx
    have hmem :
        x * y * x⁻¹ ∈ H ↔ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
      constructor
      · intro hxy
        have hgxy : g * (x * y * x⁻¹) * g⁻¹ ∈ H := hH.conj_mem _ hxy g
        simpa [mul_assoc] using hgxy
      · intro hgxy
        have hgxy' : g⁻¹ * (g * x * y * (x⁻¹ * g⁻¹)) * (g⁻¹)⁻¹ ∈ H :=
          hH.conj_mem _ hgxy g⁻¹
        simpa [mul_assoc] using hgxy'
    by_cases hxH : x * y * x⁻¹ ∈ H
    · have hgxH : g * x * y * (x⁻¹ * g⁻¹) ∈ H := hmem.mp hxH
      have hxH' : x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [Section1.conjugateOnNormal, hxH', hgxH', mul_assoc]
    · have hgxH : ¬ g * x * y * (x⁻¹ * g⁻¹) ∈ H := by
        exact fun h => hxH (hmem.mpr h)
      have hxH' : ¬ x * (y * x⁻¹) ∈ H := by
        simpa [mul_assoc] using hxH
      have hgxH' : ¬ g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H := by
        simpa [mul_assoc] using hgxH
      rw [show f (g * x) =
        if h : g * (x * (y * (x⁻¹ * g⁻¹))) ∈ H then
          theta ⟨g * (x * (y * (x⁻¹ * g⁻¹))), h⟩
        else 0 by simp [f, mul_assoc]]
      simp [hxH', hgxH', mul_assoc]
  calc
    (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * y * x⁻¹ ∈ H then
            Section1.conjugateOnNormal H theta g ⟨x * y * x⁻¹, hx⟩
          else
            0)
        =
      (Nat.card H : ℂ)⁻¹ * ∑ x : G, f (g * x) := by
          rw [hsum]
    _ = (Nat.card H : ℂ)⁻¹ * ∑ z : G, f z := by
          congr 1
          simpa using (Equiv.sum_comp (Equiv.mulLeft g) f)
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ z : G,
          (if hz : z * y * z⁻¹ ∈ H then
            theta ⟨z * y * z⁻¹, hz⟩
          else
            0) := by
          rfl


public theorem conjugateOnNormal_inducedCF_eq_of_source_conjugation_sec9
    {G : Type u} [Group G] [Finite G]
    (D : Subgroup G) [hD : D.Normal]
    (H : Subgroup D) [Finite H]
    (θ η : Section1.ClassFunction H) (g : G)
    (hgH : ∀ d : D,
      d ∈ H ↔
        (⟨g * (d : G) * g⁻¹, hD.conj_mem (d : G) d.property g⟩ : D) ∈ H)
    (hθη : ∀ h : H,
      θ ⟨⟨g * ((h : D) : G) * g⁻¹,
          hD.conj_mem ((h : D) : G) (h : D).property g⟩,
        (hgH (h : D)).mp h.property⟩ = η h) :
    Section1.conjugateOnNormal D (Section1.inducedCF H θ) g =
      Section1.inducedCF H η := by
  classical
  letI : Fintype D := Fintype.ofFinite D
  funext y
  let c : D ≃ D :=
    { toFun := fun z =>
        ⟨g * (z : G) * g⁻¹, hD.conj_mem (z : G) z.property g⟩
      invFun := fun z =>
        ⟨g⁻¹ * (z : G) * g, by
          simpa only [inv_inv] using hD.conj_mem (z : G) z.property g⁻¹⟩
      left_inv := by
        intro z
        ext
        simp [mul_assoc]
      right_inv := by
        intro z
        ext
        simp [mul_assoc] }
  let gy : D := ⟨g * (y : G) * g⁻¹, hD.conj_mem (y : G) y.property g⟩
  let F : D → ℂ := fun x =>
    if hx : x * gy * x⁻¹ ∈ H then θ ⟨x * gy * x⁻¹, hx⟩ else 0
  let R : D → ℂ := fun z =>
    if hz : z * y * z⁻¹ ∈ H then η ⟨z * y * z⁻¹, hz⟩ else 0
  unfold Section1.conjugateOnNormal Section1.inducedCF Section1.inducedClassFunction
  have hsum : (∑ x : D, F x) = ∑ z : D, R z := by
    calc
      (∑ x : D, F x) = ∑ z : D, F (c z) := by
        simpa using (Equiv.sum_comp c F).symm
      _ = ∑ z : D, R z := by
        refine Finset.sum_congr rfl ?_
        intro z _hzmem
        have harg : c z * gy * (c z)⁻¹ =
            (⟨g * (((z * y * z⁻¹ : D) : G)) * g⁻¹,
              hD.conj_mem (((z * y * z⁻¹ : D) : G))
                (z * y * z⁻¹ : D).property g⟩ : D) := by
          ext
          simp [c, gy, mul_assoc]
        by_cases hzH : z * y * z⁻¹ ∈ H
        · have hcgH : c z * gy * (c z)⁻¹ ∈ H := by
            simpa [harg] using (hgH (z * y * z⁻¹)).mp hzH
          have hθ := hθη ⟨z * y * z⁻¹, hzH⟩
          simp [F, R, hzH, hcgH]
          simpa [harg] using hθ
        · have hcgH : ¬ c z * gy * (c z)⁻¹ ∈ H := by
            intro hbad
            exact hzH ((hgH (z * y * z⁻¹)).mpr (by
              simpa [harg] using hbad))
          simp [F, R, hzH, hcgH]
  simpa [gy, F, R] using hsum

public theorem
    conjugateOnNormal_inducedCF_eq_of_subgroupOf_source_conjugation_sec9
    {G : Type u} [Group G] [Finite G]
    (D K : Subgroup G) [hD : D.Normal] [hK : K.Normal]
    [Finite (K.subgroupOf D)]
    (θ η : Section1.ClassFunction (K.subgroupOf D)) (g : G)
    (hθη : ∀ h : K.subgroupOf D,
      θ ⟨⟨g * ((h : D) : G) * g⁻¹,
          hD.conj_mem ((h : D) : G) (h : D).property g⟩,
        by
          change g * ((h : D) : G) * g⁻¹ ∈ K
          exact hK.conj_mem ((h : D) : G) h.property g⟩ = η h) :
    Section1.conjugateOnNormal D
        (Section1.inducedCF (K.subgroupOf D) θ) g =
      Section1.inducedCF (K.subgroupOf D) η := by
  classical
  refine conjugateOnNormal_inducedCF_eq_of_source_conjugation_sec9
    D (K.subgroupOf D) θ η g ?_ ?_
  · intro d
    constructor
    · intro hd
      change g * (d : G) * g⁻¹ ∈ K
      exact hK.conj_mem (d : G) hd g
    · intro hd
      have hback :
          g⁻¹ * (g * (d : G) * g⁻¹) * (g⁻¹)⁻¹ ∈ K :=
        hK.conj_mem (g * (d : G) * g⁻¹)
          (by simpa [Subgroup.mem_subgroupOf] using hd) g⁻¹
      change (d : G) ∈ K
      simpa [mul_assoc] using hback
  · intro h
    exact hθη h

public theorem induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
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
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal)
    (k l : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q)
    (hrel :
      let instAction : MulAction (U ⧸ C.subgroupOf U)
          (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
        rawCoordinateMulAction_sec9 p q H hHcard ρ
      letI : MulAction (U ⧸ C.subgroupOf U)
          (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
      MulAction.orbitRel (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) k l) :
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    let HC : Subgroup G := MF ⊔ C
    let H0C : Subgroup G := H0 ⊔ C
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    letI : HCD.Normal := hnormalHCD
    let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
      quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
    let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
      fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
    let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
      fun f => (θH f).comp e.symm.toMonoidHom
    let ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction HC :=
      fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
    let ψ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction HCm :=
      fun f => Section1.subgroupOfClassFunction (ψHC f)
    let θ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
        Section1.ClassFunction Dm :=
      fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ f))
    θ k = θ l := by
  classical
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  let ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction HC :=
    fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
  let ψ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction HCm :=
    fun f => Section1.subgroupOfClassFunction (ψHC f)
  let θ : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction Dm :=
    fun f => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ f))
  have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hDhall, _hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  rw [MulAction.orbitRel_apply] at hrel
  rcases MulAction.mem_orbit_iff.mp hrel with ⟨x, hx⟩
  obtain ⟨u, hux⟩ := QuotientGroup.mk'_surjective (C.subgroupOf U) x
  let uM : M := ⟨(u : G), (hUleD.trans section12_ambientDerivedSubgroup_le) u.property⟩
  let uD : Dm := ⟨uM, by
    simpa [D, Dm, uM, Subgroup.mem_subgroupOf] using hUleD u.property⟩
  have huD : ((uD : M) : G) = (u : G) := rfl
  have hψconj :
      Section1.subgroupOfClassFunction
          (Section1.subgroupOfClassFunction (ψHC k)) =
      Section1.conjugateOnNormal HCD
          (Section1.subgroupOfClassFunction
            (Section1.subgroupOfClassFunction (ψHC l))) uD := by
    rw [← hx]
    simpa [instAction, HC, H0C, D, Dm, HCm, HCD, e, θH, θHC, ψHC, ψ] using
      quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
        hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u uD hux huD l
  have hθHCD :
      θ k = θ l := by
    dsimp [θ, ψ]
    rw [hψconj]
    exact inducedCF_conjugateOnNormal_sec9 HCD
      (Section1.subgroupOfClassFunction (Section1.subgroupOfClassFunction (ψHC l))) uD
  simpa [instAction, HC, H0C, D, Dm, HCm, HCD, e, θH, θHC, ψHC, ψ, θ] using
    hθHCD

public theorem rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        ∀ k l : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
            Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC l)) →
          k = l := by
  classical
  intro hcase hψformula k l
  dsimp only
  intro hres
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let D : Subgroup G := ambientDerivedSubgroup M
  let Dm : Subgroup M := D.subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hHCleD : HC ≤ D := by
    dsimp [HC, D]
    exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  have hHCleM : HC ≤ M :=
    hHCleD.trans (section12_ambientDerivedSubgroup_le (E := M))
  have hHCm_le_Dm : HCm ≤ Dm := by
    intro x hx
    change ((x : M) : G) ∈ D
    exact hHCleD (by simpa [HCm, HC, Subgroup.mem_subgroupOf] using hx)
  have hres' :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
        Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC l)) := by
    simpa [D, Dm, HCm] using hres
  have hψM :
      Section1.subgroupOfClassFunction (T := M) (ψHC k) =
        Section1.subgroupOfClassFunction (T := M) (ψHC l) :=
    subgroupOfClassFunction_injective_sec9 (G := M) (H := HCm) (T := Dm)
      hHCm_le_Dm hres'
  have hψ :
      ψHC k = ψHC l :=
    subgroupOfClassFunction_injective_sec9 (G := G) (H := HC) (T := M)
      hHCleM hψM
  rw [hψformula] at hψ
  have hθHC : θHC k = θHC l :=
    Section1.quotientCharacterInflation_injective H0C HC hψ
  have hθH : θH k = θH l := by
    ext x
    have hval := congrArg
      (fun χ : (HC ⧸ H0C.subgroupOf HC) →* ℂˣ => χ (e x)) hθHC
    simpa [θHC] using congrArg Units.val hval
  have hdown :
      k.down = l.down :=
    componentProductLinearCharacter_injective_sec9
      p q H hHcard hHindep hHsup (by simpa [θH] using hθH)
  rcases k with ⟨kdown⟩
  rcases l with ⟨ldown⟩
  dsimp at hdown
  cases hdown
  rfl

public theorem subgroupOfClassFunction_isClassFunction_sec9
    {G : Type u} [Group G] {H T : Subgroup G}
    {θ : Section1.ClassFunction H}
    (hθ : Section1.IsClassFunction θ) :
    Section1.IsClassFunction (Section1.subgroupOfClassFunction (T := T) θ) := by
  intro x g
  unfold Section1.subgroupOfClassFunction
  let xH : H := ⟨(x : T), x.property⟩
  let gH : H := ⟨(g : T), g.property⟩
  let lhsH : H :=
    ⟨((x * g * x⁻¹ : H.subgroupOf T) : T),
      (x * g * x⁻¹ : H.subgroupOf T).property⟩
  change θ lhsH = θ gH
  have hlhs : lhsH = xH * gH * xH⁻¹ := by
    apply Subtype.ext
    rfl
  rw [hlhs]
  exact hθ xH gH

public theorem conjugateOnNormal_mul_left_of_mem_sec9
    {G : Type u} [Group G] {H : Subgroup G} [H.Normal]
    (θ : Section1.ClassFunction H)
    (hθ : Section1.IsClassFunction θ)
    {k w : G} (hk : k ∈ H) :
    Section1.conjugateOnNormal H θ (k * w) =
      Section1.conjugateOnNormal H θ w := by
  ext h
  let y : H := ⟨w * (h : G) * w⁻¹, (inferInstance : H.Normal).conj_mem h h.property w⟩
  let z : H := ⟨(k * w) * (h : G) * (k * w)⁻¹,
    (inferInstance : H.Normal).conj_mem h h.property (k * w)⟩
  have hz : z = ⟨k, hk⟩ * y * (⟨k, hk⟩ : H)⁻¹ := by
    apply Subtype.ext
    simp [z, y, mul_assoc]
  have hclass := hθ ⟨k, hk⟩ y
  change θ z = θ y
  rw [hz]
  exact hclass

public theorem rawCoordinateMulAction_eq_self_of_conjugateOnNormal_fixed_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    [hnormalC : (C.subgroupOf U).Normal]
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
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          ∀ (x : U ⧸ C.subgroupOf U) (u : U)
            (uD : (ambientDerivedSubgroup M).subgroupOf M),
            QuotientGroup.mk' (C.subgroupOf U) u = x →
              ((uD : M) : G) = (u : G) →
                ∀ k : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q,
                  Section1.conjugateOnNormal
                      ((((MF ⊔ C).subgroupOf M).subgroupOf
                        ((ambientDerivedSubgroup M).subgroupOf M)))
                      (Section1.subgroupOfClassFunction
                        (Section1.subgroupOfClassFunction (ψHC k))) uD =
                    Section1.subgroupOfClassFunction
                      (Section1.subgroupOfClassFunction (ψHC k)) →
                  letI : MulAction (U ⧸ C.subgroupOf U)
                      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
                    rawCoordinateMulAction_sec9 p q H hHcard ρ
                  x • k = k := by
  classical
  intro hcase hψformula hnormalHCD x u uD hux huD k hfix
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := HC.subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C le_sup_left hH0CinfMF hsup
  let θH : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  have hψconj :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC (x • k))) =
        Section1.conjugateOnNormal HCD
          (Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC k))) uD := by
    rw [hψformula]
    simpa [instAction, HC, H0C, Dm, HCm, HCD, e, θH, θHC] using
      quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
        M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
        hρaction hconj hH0CinfMF hsup hcase hnormalHCD x u uD hux huD k
  have hres :
      Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC (x • k))) =
        Section1.subgroupOfClassFunction (T := Dm)
          (Section1.subgroupOfClassFunction (T := M) (ψHC k)) := by
    exact hψconj.trans (by simpa [HC, Dm, HCm, HCD] using hfix)
  simpa [instAction, HC, H0C, Dm, HCm, HCD] using
    rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
      M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hH0CinfMF hsup
      ψHC hcase hψformula (x • k) k hres

public theorem induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    {φ θ : Section1.ClassFunction H}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ)
    (hInd : Section1.inducedCF H φ = Section1.inducedCF H θ) :
    ∃ i : Section1.conjugateOrbitIndex H θ,
      φ = Section1.conjugateOrbitConj H θ i := by
  classical
  rcases hφ with ⟨nφ, φRep, hφirr, hφeq⟩
  rcases hθ with ⟨nθ, θRep, hθirr, hθeq⟩
  subst φ
  subst θ
  exact Section1.proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
    H φRep θRep hφirr hθirr hInd


public theorem theorem_9_8_H0C_linear_candidate_Xtheta_thetaHC_concrete_fields_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      ∃ hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF),
        letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
        let HC : Subgroup G := MF ⊔ C
        let H0C : Subgroup G := H0 ⊔ C
        ∃ hnormalH0C : (H0C.subgroupOf HC).Normal,
          letI : (H0C.subgroupOf HC).Normal := hnormalH0C
          ∃ hH0CinfMF : H0C ⊓ MF = H0,
            ∃ hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤,
              let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
              let hMFHC : MF ≤ HC := le_sup_left
              let e : (MF ⧸ H0.subgroupOf MF) ≃*
                  (HC ⧸ H0C.subgroupOf HC) :=
                quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
              let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
                fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup
                  f.down
              let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
                fun f => (θH f).comp e.symm.toMonoidHom
              ∃ ψHC : κ → Section1.ClassFunction HC,
                ψHC =
                    (fun f => Section1.quotientCharacterInflation H0C HC (θHC f)) ∧
                  Function.Injective ψHC ∧
                  (∀ f : κ, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) ∧
                  (∀ f : κ, Section1.degree (ψHC f) = (1 : ℂ)) ∧
                  (∀ f : κ, Section1.subgroupInKernel' (ψHC f) (H0C.subgroupOf HC)) ∧
                  ∀ f : κ, ¬ Section1.subgroupInKernel' (ψHC f) (MF.subgroupOf HC) := by
  classical
  intro hcase
  have hquotElem : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := by
    rcases case_9_7_a_quotient_isElementaryAbelian_sec9 hcase with
      ⟨_hnormalH0', hElem⟩
    exact hElem
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hquotElem
  let hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := inferInstance
  letI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := hcomm
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let HC : Subgroup G := MF ⊔ C
  let H0C : Subgroup G := H0 ⊔ C
  have hH0CnormalHC : (H0C.subgroupOf HC).Normal := by
    dsimp [H0C, HC]
    exact theorem_9_8_H0C_normal_HC_of_case_a_sec9
      M MF U W1 W2 H0 C p q a hcase
  letI : (H0C.subgroupOf HC).Normal := hH0CnormalHC
  have hH0CinfMF : H0C ⊓ MF = H0 := by
    dsimp [H0C]
    rcases hcase with ⟨h92, hH0MF, hC, hpprime, _hqprime, hpData, _hrest⟩
    exact theorem_9_H0C_inf_MF_eq_H0_source_core_sec9
      M MF U W1 W2 H0 C p q h92 hH0MF hC hpprime hpData
  have hMFHC : MF ≤ HC := by
    dsimp [HC]
    exact le_sup_left
  have hsup : H0C.subgroupOf HC ⊔ MF.subgroupOf HC = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := H0C) (A' := MF) (B := HC)]
    · apply Subgroup.subgroupOf_eq_top.2
      dsimp [H0C, HC]
      exact sup_le
        (show MF ≤ (H0 ⊔ C) ⊔ MF from le_sup_right)
        (show C ≤ (H0 ⊔ C) ⊔ MF from le_sup_right.trans le_sup_left)
    · dsimp [H0C, HC]
      exact sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
    · dsimp [HC]
      exact le_sup_left
  let e : (MF ⧸ H0.subgroupOf MF) ≃*
      (HC ⧸ H0C.subgroupOf HC) :=
    quotientInfSupEquiv_sec9 MF H0 HC H0C hMFHC hH0CinfMF hsup
  let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
    fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
  let θHC : κ → (HC ⧸ H0C.subgroupOf HC) →* ℂˣ :=
    fun f => (θH f).comp e.symm.toMonoidHom
  let ψHC : κ → Section1.ClassFunction HC :=
    fun f => Section1.quotientCharacterInflation H0C HC (θHC f)
  have hqpos : 0 < q := (case_9_7_a_q_prime_sec9 hcase).pos
  have hθHinj : Function.Injective θH := by
    intro f g hfg
    have hdown :
        f.down = g.down :=
      componentProductLinearCharacter_injective_sec9 p q H hHcard hHindep hHsup hfg
    cases f
    cases g
    simp at hdown
    cases hdown
    rfl
  have hθHne : ∀ f : κ, θH f ≠ 1 := by
    intro f
    exact componentProductLinearCharacter_ne_one_sec9 p q H hHcard hHindep hHsup
      f.down ⟨0, hqpos⟩
  refine ⟨hcomm, hH0CnormalHC, hH0CinfMF, hsup, ψHC, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro f g hfg
    apply hθHinj
    have hθHC :
        θHC f = θHC g :=
      Section1.quotientCharacterInflation_injective H0C HC hfg
    ext x
    have hval := congrArg (fun χ : (HC ⧸ H0C.subgroupOf HC) →* ℂˣ =>
      χ (e x)) hθHC
    exact congrArg Units.val (by simpa [θHC] using hval)
  · intro f
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      H0C HC (θHC f)
  · intro f
    exact Section1.quotientCharacterInflation_degree H0C HC (θHC f)
  · intro f
    exact Section1.subgroupInKernel'_quotientCharacterInflation H0C HC (θHC f)
  · intro f hkerMF
    exact hθHne f <| by
      ext x
      have hxker : ψHC f (Subgroup.inclusion hMFHC x) =
          Section1.degree (ψHC f) := by
        exact hkerMF ⟨Subgroup.inclusion hMFHC x, by
          simp [Subgroup.mem_subgroupOf]⟩
      have hqval : θH f x = 1 := by
        have hxval := hxker
        rw [Section1.quotientCharacterInflation_degree] at hxval
        have hxval' :
            ((θHC f) (QuotientGroup.mk' (H0C.subgroupOf HC)
                (Subgroup.inclusion hMFHC x)) : ℂˣ) = (1 : ℂˣ) := by
          exact Units.ext (by simpa [ψHC, Section1.quotientCharacterInflation] using hxval)
        have heq : QuotientGroup.mk' (H0C.subgroupOf HC)
              (Subgroup.inclusion hMFHC x) = e x := rfl
        have hunit : (θHC f) (e x) = 1 := by
          simpa [heq] using hxval'
        have hunit' : θH f x = 1 := by
          simpa [θHC] using hunit
        exact hunit'
      exact congrArg Units.val (by simpa using hqval)


public theorem H0CLinearCandidateXtheta_theta_orbit_entry_data_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a : ℕ)
    {ψHC : ULift.{u, 0} (Fin q → Fin (p - 1)) →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (rep : ι → ULift.{u, 0} (Fin q → Fin (p - 1))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      (∀ f, Section1.IsIrreducibleCharacterOnGroup (ψHC f)) →
        (∀ f, Section1.degree (ψHC f) = (1 : ℂ)) →
          (∀ f, Section1.subgroupInKernel' (ψHC f)
            ((H0 ⊔ C).subgroupOf (MF ⊔ C))) →
          (∀ f, ¬ Section1.subgroupInKernel' (ψHC f)
            (MF.subgroupOf (MF ⊔ C))) →
            let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
            let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
            let HCD : Subgroup Dm := HCm.subgroupOf Dm
            let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
            let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
            ∀ hnormalHCD : HCD.Normal,
              letI : HCD.Normal := hnormalHCD
              let ψ : ι → Section1.ClassFunction HCm :=
                fun i => Section1.subgroupOfClassFunction (ψHC (rep i))
              let θ : ι → Section1.ClassFunction Dm :=
                fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
              (∀ i : ι,
                Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ i)) =
                  HCD) →
                ∀ i : ι,
                  Section1.IsIrreducibleCharacterOnGroup (θ i) ∧
                    ¬ Section1.subgroupInKernel' (θ i) MFD ∧
                    Section1.subgroupInKernel' (θ i) H0CD ∧
                    Section1.IsIrreducibleCharacterOnGroup (ψ i) ∧
                    Section1.degree (ψ i) = (1 : ℂ) := by
  classical
  intro hcase hψirr hψdeg hψkerH0C hψnotMF
  dsimp only
  intro hnormalHCD hIeq i
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let H0CD : Subgroup Dm := ((H0 ⊔ C).subgroupOf M).subgroupOf Dm
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let ψ : ι → Section1.ClassFunction HCm :=
    fun i => Section1.subgroupOfClassFunction (ψHC (rep i))
  let θ : ι → Section1.ClassFunction Dm :=
    fun i => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ i))
  letI : HCD.Normal := hnormalHCD
  have hHC_le_D : MF ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_8_HC_le_ambientDerived_of_case_a_sec9 M MF U W1 W2 H0 C p q a hcase
  have hH0C_le_HC : H0 ⊔ C ≤ MF ⊔ C :=
    sup_le_sup (case_9_7_a_H0_le_MF_sec9 hcase) le_rfl
  have hMF_le_HC : MF ≤ MF ⊔ C := le_sup_left
  have hH0C_le_D : H0 ⊔ C ≤ ambientDerivedSubgroup M :=
    theorem_9_H0C_le_ambientDerived_of_source_sec9 M MF U W1 W2 H0 C q
      (case_9_7_a_hypothesis_9_2_sec9 hcase)
      (case_9_7_a_H0_le_MF_sec9 hcase)
      (case_9_7_a_quotientCentralizerIn_sec9 hcase)
  have hH0C_le_M : H0 ⊔ C ≤ M :=
    hH0C_le_D.trans (section12_ambientDerivedSubgroup_le (E := M))
  have hMF_le_M : MF ≤ M := case_9_7_a_MF_le_M_sec9 hcase
  have hMF_le_D : MF ≤ ambientDerivedSubgroup M :=
    hMF_le_HC.trans hHC_le_D
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
      (case_9_7_a_hypothesis_9_2_sec9 hcase)
      (case_9_7_a_H0_le_MF_sec9 hcase)
      (case_9_7_a_quotientCentralizerIn_sec9 hcase)
      (case_9_7_a_p_prime_sec9 hcase)
      hpData
  letI : ((H0 ⊔ C).subgroupOf M).Normal := hH0CnormalM
  have hH0CDnormal : H0CD.Normal := by
    dsimp [H0CD, Dm]
    exact Section1.subgroupOf_normal_of_normal ((H0 ⊔ C).subgroupOf M)
      ((ambientDerivedSubgroup M).subgroupOf M)
  letI : H0CD.Normal := hH0CDnormal
  have hMFDnormal : MFD.Normal := by
    simpa [MFD, Dm] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hH0CD_le_HCD : H0CD ≤ HCD := by
    intro x hx
    have hxH0C : ((x : Dm) : M) ∈ (H0 ⊔ C).subgroupOf M := by
      simpa [H0CD, Subgroup.mem_subgroupOf] using hx
    have hxH0CG : (((x : Dm) : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hxH0C
    have hxHCG : (((x : Dm) : M) : G) ∈ MF ⊔ C :=
      hH0C_le_HC hxH0CG
    simpa [HCD, HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hMFD_le_HCD : MFD ≤ HCD := by
    intro x hx
    have hxMF : ((x : Dm) : M) ∈ MF.subgroupOf M := by
      simpa [MFD, Subgroup.mem_subgroupOf] using hx
    have hxMFG : (((x : Dm) : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hxMF
    have hxHCG : (((x : Dm) : M) : G) ∈ MF ⊔ C := hMF_le_HC hxMFG
    simpa [HCD, HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hH0CM_le_HCm : (H0 ⊔ C).subgroupOf M ≤ HCm := by
    intro x hx
    have hxH0CG : ((x : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxHCG : ((x : M) : G) ∈ MF ⊔ C := hH0C_le_HC hxH0CG
    simpa [HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hH0CM_le_Dm : (H0 ⊔ C).subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0CG : ((x : M) : G) ∈ H0 ⊔ C := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M := hH0C_le_D hxH0CG
    simpa [Dm, Subgroup.mem_subgroupOf] using hxD
  have hMFM_le_HCm : MF.subgroupOf M ≤ HCm := by
    intro x hx
    have hxMFG : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxHCG : ((x : M) : G) ∈ MF ⊔ C := hMF_le_HC hxMFG
    simpa [HCm, Subgroup.mem_subgroupOf] using hxHCG
  have hMFM_le_Dm : MF.subgroupOf M ≤ Dm := by
    intro x hx
    have hxMFG : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxD : ((x : M) : G) ∈ ambientDerivedSubgroup M := hMF_le_D hxMFG
    simpa [Dm, Subgroup.mem_subgroupOf] using hxD
  have hψi_irr : Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    dsimp [ψ, HCm]
    exact isIrreducible_subgroupOfClassFunction_sec9
      (show MF ⊔ C ≤ M from
        (theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
          M MF U W1 W2 H0 C p q a hcase).trans
          (section12_ambientDerivedSubgroup_le (E := M)))
      (hψirr (rep i))
  have hψiD_irr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.subgroupOfClassFunction (T := Dm) (ψ i)) := by
    dsimp [ψ, HCm, HCD, Dm]
    exact isIrreducible_subgroupOfClassFunction_sec9 (T := Dm)
      (show (MF ⊔ C).subgroupOf M ≤ (ambientDerivedSubgroup M).subgroupOf M from by
        intro x hx
        change ((x : M) : G) ∈ ambientDerivedSubgroup M
        exact hHC_le_D (by simpa [Subgroup.mem_subgroupOf] using hx))
      hψi_irr
  have hθirr : Section1.IsIrreducibleCharacterOnGroup (θ i) := by
    dsimp [θ]
    exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 HCD hψiD_irr (by
      simpa [ψ, θ, HCD, HCm, Dm] using hIeq i)
  have hψdeg : Section1.degree (ψ i) = (1 : ℂ) := by
    dsimp [ψ]
    rw [Section1.degree_subgroupOfClassFunction]
    exact hψdeg (rep i)
  have hθkerH0C : Section1.subgroupInKernel' (θ i) H0CD := by
    have hψiKerH0CM :
        Section1.subgroupInKernel' (ψ i)
          (((H0 ⊔ C).subgroupOf M).subgroupOf HCm) := by
      dsimp [ψ, HCm]
      exact subgroupInKernel'_subgroupOfClassFunction_sec9
        hH0C_le_M hH0C_le_HC (hψkerH0C (rep i))
    have hψiDKerH0CD :
        Section1.subgroupInKernel'
          (Section1.subgroupOfClassFunction (ψ i)) (H0CD.subgroupOf HCD) := by
      dsimp [H0CD, HCD, Dm, HCm]
      exact subgroupInKernel'_subgroupOfClassFunction_sec9
        hH0CM_le_Dm hH0CM_le_HCm hψiKerH0CM
    dsimp [θ]
    exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
      HCD H0CD hH0CD_le_HCD hψiD_irr hψiDKerH0CD
  have hθnotMF : ¬ Section1.subgroupInKernel' (θ i) MFD := by
    intro hθkerMF
    have hψiDKerMFD :
        Section1.subgroupInKernel'
          (Section1.subgroupOfClassFunction (ψ i)) (MFD.subgroupOf HCD) := by
      dsimp [θ] at hθkerMF
      exact subgroupInKernel'_of_inducedCF_sec9
        HCD MFD hMFD_le_HCD hψiD_irr hθkerMF
    have hψiKerMFM :
        Section1.subgroupInKernel' (ψ i) ((MF.subgroupOf M).subgroupOf HCm) := by
      dsimp [MFD, HCD, Dm, HCm] at hψiDKerMFD
      exact subgroupInKernel'_of_subgroupOfClassFunction_sec9
        hMFM_le_Dm hMFM_le_HCm hψiDKerMFD
    have hψHCKerMF :
        Section1.subgroupInKernel' (ψHC (rep i)) (MF.subgroupOf (MF ⊔ C)) := by
      dsimp [ψ, HCm] at hψiKerMFM
      exact subgroupInKernel'_of_subgroupOfClassFunction_sec9
        hMF_le_M hMF_le_HC hψiKerMFM
    exact hψnotMF (rep i) hψHCKerMF
  exact ⟨hθirr, hθnotMF, hθkerH0C, hψi_irr, hψdeg⟩


public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_reverse_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
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
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k));
            (∀ k : κ,
              Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
                HCD) ∧
              ∀ k l : κ,
                θ k = θ l →
                  MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
    classical
    intro hcase hψformula
    dsimp only
    intro hnormalHCD
    let instAction : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
      rawCoordinateMulAction_sec9 p q H hHcard ρ
    letI : MulAction (U ⧸ C.subgroupOf U)
        (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
    letI : (((MF ⊔ C).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
    let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
    let D : Subgroup G := ambientDerivedSubgroup M
    let Dm : Subgroup M := D.subgroupOf M
    let HC : Subgroup G := MF ⊔ C
    let HCm : Subgroup M := HC.subgroupOf M
    let HCD : Subgroup Dm := HCm.subgroupOf Dm
    let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
    let UD : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    let ψ : κ → Section1.ClassFunction HCm :=
      fun k => Section1.subgroupOfClassFunction (ψHC k)
    let θ : κ → Section1.ClassFunction Dm :=
      fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
    letI : HCD.Normal := by
      simpa [HC, D, HCm, Dm, HCD] using hnormalHCD
    have h92 := case_9_7_a_hypothesis_9_2_sec9 hcase
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm, D] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    have hsemi :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD UD := by
      simpa [MFD, UD, Dm, D] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q h92 hMFDnormal
    rcases h92.typeP with ⟨_hMFtype, hcommon⟩
    rcases hcommon with
      ⟨_hDhall, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
        _hMFnotcyc, _hsecond, _hfitting, _hfittingDer, _hW2le, _hW2ne,
        _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
    rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
    have hDleM : D ≤ M := by
      dsimp [D]
      exact section12_ambientDerivedSubgroup_le (E := M)
    have hUleM : U ≤ M := hUleD.trans hDleM
    have hC_le_U : C ≤ U :=
      (case_9_7_a_quotientCentralizerIn_sec9 hcase).1
    have hψclass : ∀ k : κ, Section1.IsClassFunction
        (Section1.subgroupOfClassFunction (T := Dm) (ψ k)) := by
      intro k
      dsimp [ψ, HCm, Dm]
      rw [hψformula]
      exact subgroupOfClassFunction_isClassFunction_sec9
        (subgroupOfClassFunction_isClassFunction_sec9
          (Section1.quotientCharacterInflation_isClassFunction (H0 ⊔ C) (MF ⊔ C) _))
    have hinertia : ∀ k : κ,
        Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) = HCD := by
      intro k
      have hHCD_le_I :
          HCD ≤ Section1.inertiaSubgroup HCD
            (Section1.subgroupOfClassFunction (ψ k)) :=
        Section1.proposition_1_7_inertia_contains_H HCD
          (Section1.subgroupOfClassFunction (ψ k)) (hψclass k)
      apply le_antisymm
      · intro g hgI
        rcases hsemi.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
        let x : U ⧸ C.subgroupOf U :=
          QuotientGroup.mk' (C.subgroupOf U)
            ⟨(((u0 : Dm) : M) : G), by
              have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
                simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
              simpa [Subgroup.mem_subgroupOf] using huUM⟩
        let uU : U := ⟨(((u0 : Dm) : M) : G), by
          have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
            simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
          simpa [Subgroup.mem_subgroupOf] using huUM⟩
        have huD : (((u0 : Dm) : M) : G) = (uU : G) := rfl
        have hmHCD : m0 ∈ HCD := by
          have hmMF : ((m0 : Dm) : M) ∈ MF.subgroupOf M := by
            simpa [MFD, Dm, D, Subgroup.mem_subgroupOf] using hm0
          have hmHCG : (((m0 : Dm) : M) : G) ∈ HC := by
            exact (le_sup_left : MF ≤ HC) (by simpa [Subgroup.mem_subgroupOf] using hmMF)
          simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using hmHCG
        have hu_fix :
            Section1.conjugateOnNormal HCD
                (Section1.subgroupOfClassFunction (ψ k)) u0 =
              Section1.subgroupOfClassFunction (ψ k) := by
          have hgfix :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) g =
                Section1.subgroupOfClassFunction (ψ k) := by
            simpa [Section1.inertiaSubgroup] using hgI
          have hmulfix :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) (m0 * u0) =
                Section1.subgroupOfClassFunction (ψ k) := by
            simpa [hg] using hgfix
          have herase :
              Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) (m0 * u0) =
                Section1.conjugateOnNormal HCD
                  (Section1.subgroupOfClassFunction (ψ k)) u0 :=
            conjugateOnNormal_mul_left_of_mem_sec9
              (Section1.subgroupOfClassFunction (ψ k)) (hψclass k) hmHCD
          exact herase.symm.trans hmulfix
        have hxfix : x • k = k := by
          dsimp [x]
          exact rawCoordinateMulAction_eq_self_of_conjugateOnNormal_fixed_sec9
            M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ hρaction
            hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
            (QuotientGroup.mk' (C.subgroupOf U) uU) uU u0 rfl huD k
            (by simpa [ψ, HCD, HCm, Dm, D] using hu_fix)
        have hxstab : x ∈ MulAction.stabilizer (U ⧸ C.subgroupOf U) k := by
          rw [MulAction.mem_stabilizer_iff]
          exact hxfix
        have hxone : x = 1 := by
          have hstab :=
            rawCoordinateMulAction_stabilizer_eq_bot_sec9
              (hcase := hcase) H hHcard hHnorm hHsup ρ hρaction k
          have hxbot : x ∈ (⊥ : Subgroup (U ⧸ C.subgroupOf U)) := by
            simpa [instAction] using (by simpa [hstab] using hxstab)
          exact Subgroup.mem_bot.mp hxbot
        have huC : (uU : G) ∈ C := by
          have huCsub : uU ∈ C.subgroupOf U :=
            (QuotientGroup.eq_one_iff (N := C.subgroupOf U) (x := uU)).1
              (by simpa [x] using hxone)
          simpa [Subgroup.mem_subgroupOf] using huCsub
        have huHCD : u0 ∈ HCD := by
          have huHCG : (((u0 : Dm) : M) : G) ∈ HC := by
            exact (le_sup_right : C ≤ HC) (by simpa [uU] using huC)
          simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using huHCG
        have hgHCD : g ∈ HCD := by
          rw [hg]
          exact HCD.mul_mem hmHCD huHCD
        exact hgHCD
      · exact hHCD_le_I
    refine ⟨hinertia, ?_⟩
    intro k l hθeq
    have hHC_le_D : HC ≤ D := by
      dsimp [HC, D]
      exact theorem_9_8_HC_le_ambientDerived_of_case_a_sec9
        M MF U W1 W2 H0 C p q a hcase
    have hHCm_le_Dm : HCm ≤ Dm := by
      intro x hx
      change ((x : M) : G) ∈ D
      exact hHC_le_D (by simpa [HCm, HC, Subgroup.mem_subgroupOf] using hx)
    have hHC_le_M : HC ≤ M :=
      hHC_le_D.trans hDleM
    have hψD_irr : ∀ r : κ,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.subgroupOfClassFunction (T := Dm) (ψ r)) := by
      intro r
      have hψHC_irr :
          Section1.IsIrreducibleCharacterOnGroup (ψHC r) := by
        rw [hψformula]
        let e : (MF ⧸ H0.subgroupOf MF) ≃* (HC ⧸ (H0 ⊔ C).subgroupOf HC) :=
          quotientInfSupEquiv_sec9 MF H0 HC (H0 ⊔ C) le_sup_left hH0CinfMF hsup
        let θH : κ → (MF ⧸ H0.subgroupOf MF) →* ℂˣ :=
          fun f => componentProductLinearCharacter_sec9 p q H hHcard hHindep hHsup f.down
        let θHC : κ → (HC ⧸ (H0 ⊔ C).subgroupOf HC) →* ℂˣ :=
          fun f => (θH f).comp e.symm.toMonoidHom
        change Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation (H0 ⊔ C) HC (θHC r))
        exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
          (H0 ⊔ C) HC (θHC r)
      have hψM_irr :
          Section1.IsIrreducibleCharacterOnGroup (ψ r) := by
        dsimp [ψ, HCm]
        exact isIrreducible_subgroupOfClassFunction_sec9 (H := HC) (T := M)
          hHC_le_M hψHC_irr
      exact isIrreducible_subgroupOfClassFunction_sec9 (T := Dm)
        hHCm_le_Dm hψM_irr
    have hθeq' :
        Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ k)) =
          Section1.inducedCF HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) := by
      simpa [ψ, θ, HC, HCm, D, Dm, HCD] using hθeq
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        HCD (hψD_irr k) (hψD_irr l) hθeq' with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemi.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
    let x : U ⧸ C.subgroupOf U :=
      QuotientGroup.mk' (C.subgroupOf U)
        ⟨(((u0 : Dm) : M) : G), by
          have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
            simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
          simpa [Subgroup.mem_subgroupOf] using huUM⟩
    let uU : U := ⟨(((u0 : Dm) : M) : G), by
      have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
        simpa [UD, Dm, D, Subgroup.mem_subgroupOf] using hu0
      simpa [Subgroup.mem_subgroupOf] using huUM⟩
    have huD : (((u0 : Dm) : M) : G) = (uU : G) := rfl
    have hmHCD : m0 ∈ HCD := by
      have hmMF : ((m0 : Dm) : M) ∈ MF.subgroupOf M := by
        simpa [MFD, Dm, D, Subgroup.mem_subgroupOf] using hm0
      have hmHCG : (((m0 : Dm) : M) : G) ∈ HC := by
        exact (le_sup_left : MF ≤ HC) (by simpa [Subgroup.mem_subgroupOf] using hmMF)
      simpa [HCD, HCm, HC, Dm, D, Subgroup.mem_subgroupOf] using hmHCG
    have hconjU :
        Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) u0 := by
      have hconjMU :
          Section1.subgroupOfClassFunction (T := Dm) (ψ k) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (m0 * u0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (m0 * u0) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) u0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.subgroupOfClassFunction (T := Dm) (ψ l)) (hψclass l) hmHCD
      exact hconjMU.trans herase
    have hψconj :
        Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC (x • l))) =
          Section1.conjugateOnNormal HCD
            (Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC l))) u0 := by
      rw [hψformula]
      simpa [instAction, x, HC, D, Dm, HCm, HCD] using
        quotientCharacterInflation_rawCoordinateMulAction_eq_conjugateOnNormal_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
          hρaction hconj hH0CinfMF hsup hcase hnormalHCD
          (QuotientGroup.mk' (C.subgroupOf U) uU) uU u0 rfl huD l
    have hres :
        Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
          Section1.subgroupOfClassFunction (T := Dm)
            (Section1.subgroupOfClassFunction (T := M) (ψHC (x • l))) := by
      have hku :
          Section1.subgroupOfClassFunction (T := Dm)
              (Section1.subgroupOfClassFunction (T := M) (ψHC k)) =
            Section1.conjugateOnNormal HCD
              (Section1.subgroupOfClassFunction (T := Dm)
                (Section1.subgroupOfClassFunction (T := M) (ψHC l))) u0 := by
        simpa [ψ, HCm, Dm, HCD] using hconjU
      exact hku.trans hψconj.symm
    have hk_eq_xl : k = x • l := by
      simpa [instAction, x, HC, D, Dm, HCm, HCD] using
        rawCoordinate_eq_of_restricted_quotientCharacterInflation_eq_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHindep hHsup hH0CinfMF hsup
          ψHC hcase hψformula k (x • l) hres
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨x, hk_eq_xl.symm⟩

public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
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
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        ∀ hnormalHCD : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal,
          letI : (((MF ⊔ C).subgroupOf M).subgroupOf
            ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
          let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
          let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
          let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
          let HCD : Subgroup Dm := HCm.subgroupOf Dm
          let ψ : κ → Section1.ClassFunction HCm :=
            fun k => Section1.subgroupOfClassFunction (ψHC k)
          let θ : κ → Section1.ClassFunction Dm :=
            fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
          (∀ k : κ,
            Section1.inertiaSubgroup HCD (Section1.subgroupOfClassFunction (ψ k)) =
              HCD) ∧
            ∀ k l : κ,
              θ k = θ l ↔
                MulAction.orbitRel (U ⧸ C.subgroupOf U) κ k l := by
  classical
  intro hcase hψformula
  dsimp only
  intro hnormalHCD
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  letI : (((MF ⊔ C).subgroupOf M).subgroupOf
      ((ambientDerivedSubgroup M).subgroupOf M)).Normal := hnormalHCD
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  let ψ : κ → Section1.ClassFunction HCm :=
    fun k => Section1.subgroupOfClassFunction (ψHC k)
  let θ : κ → Section1.ClassFunction Dm :=
    fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψ k))
  have hrev :=
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_reverse_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
      hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula hnormalHCD
  refine ⟨?_, ?_⟩
  · exact hrev.1
  · intro k l
    constructor
    · exact hrev.2 k l
    · intro hrel
      rw [hψformula]
      simpa [instAction, κ, Dm, HCm, HCD, ψ, θ] using
        induced_eq_of_rawCoordinateMulAction_orbitRel_sec9
          M MF U W1 W2 H0 C p q a H hHcard hHnorm hHindep hHsup ρ
          hρaction hconj hH0CinfMF hsup hcase hnormalHCD k l hrel

public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_raw_action_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
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
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        let instAction : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
          rawCoordinateMulAction_sec9 p q H hHcard ρ
        letI : MulAction (U ⧸ C.subgroupOf U)
            (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
        H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
          M MF U H0 C p q ψHC := by
  classical
  intro hcase hψformula
  let instAction : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) :=
    rawCoordinateMulAction_sec9 p q H hHcard ρ
  letI : MulAction (U ⧸ C.subgroupOf U)
      (H0CLinearCandidateXthetaRawIndex_sec9.{u} p q) := instAction
  refine ⟨hnormalC, instAction, ?_, ?_⟩
  · exact
      rawCoordinateMulAction_stabilizer_eq_bot_sec9
        hcase H hHcard hHnorm hHsup ρ hρaction
  · exact
      theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_inertia_orbit_source_core_sec9
        M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
        hρaction hρker hconj hH0CinfMF hsup ψHC hcase hψformula

public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_concrete_formula_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C : Subgroup G)
    (p q a aρ : ℕ)
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (hfac : ∀ i, quotientFactorActionCentralizerData MF H0 U C (H i) aρ)
    (hconj : ∃ hqpos : 0 < q,
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i) (w : G))
    (hnormalC : (C.subgroupOf U).Normal)
    [hnormalH0C : ((H0 ⊔ C).subgroupOf (MF ⊔ C)).Normal]
    (hH0CinfMF : (H0 ⊔ C) ⊓ MF = H0)
    (hsup : ((H0 ⊔ C).subgroupOf (MF ⊔ C)) ⊔
      MF.subgroupOf (MF ⊔ C) = ⊤)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
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
        H0CLinearCandidateXthetaThetaCoordinateActionCoreData_sec9
          M MF U H0 C p q ψHC := by
  -- coordinates must be derived from the displayed product-coordinate formula.
  classical
  letI : (C.subgroupOf U).Normal := hnormalC
  choose hnormalC' ρ hρcyc hρcard hρaction hρker using hfac
  exact
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_action_core_of_raw_action_source_core_sec9
      M MF U W1 W2 H0 C p q a aρ H hHcard hHnorm hHindep hHsup ρ hρcyc hρcard
      hρaction hρker hconj hH0CinfMF hsup ψHC


public theorem
    theorem_9_8_H0C_linear_candidate_Xtheta_theta_coordinate_orbit_of_action_data_sec9
    {G : Type u} [Group G] [Finite G]
    (M MF U H0 C : Subgroup G)
    (p q u : ℕ)
    (ψHC : H0CLinearCandidateXthetaRawIndex_sec9.{u} p q →
      Section1.ClassFunction ((MF ⊔ C : Subgroup G))) :
    H0CLinearCandidateXthetaThetaCoordinateActionData_sec9 M MF U H0 C p q u ψHC →
      H0CLinearCandidateXthetaThetaCoordinateOrbitData_sec9 M MF U H0 C p q u ψHC := by
  classical
  intro hactionData
  rcases hactionData with
    ⟨hnormalC, instAction, hstab, hbarCard, hcoord⟩
  refine ⟨hnormalC, instAction, hstab, hbarCard, ?_⟩
  intro hnormalHCD
  letI : (C.subgroupOf U).Normal := hnormalC
  let κ : Type u := H0CLinearCandidateXthetaRawIndex_sec9.{u} p q
  letI : MulAction (U ⧸ C.subgroupOf U) κ := instAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let HCm : Subgroup M := (MF ⊔ C).subgroupOf M
  let HCD : Subgroup Dm := HCm.subgroupOf Dm
  letI : HCD.Normal := hnormalHCD
  let ι : Type u := Quotient (MulAction.orbitRel (U ⧸ C.subgroupOf U) κ)
  let ψRaw : κ → Section1.ClassFunction HCm :=
    fun k => Section1.subgroupOfClassFunction (ψHC k)
  let θRaw : κ → Section1.ClassFunction Dm :=
    fun k => Section1.inducedCF HCD (Section1.subgroupOfClassFunction (ψRaw k))
  rcases hcoord hnormalHCD with ⟨hIeq, hInd_iff⟩
  constructor
  · intro i j hij
    have hout :
        MulAction.orbitRel (U ⧸ C.subgroupOf U) κ (Quotient.out i) (Quotient.out j) := by
      rw [← hInd_iff]
      exact hij
    have hi : Quotient.mk'' (Quotient.out i : κ) = i :=
      Quotient.out_eq' i
    have hj : Quotient.mk'' (Quotient.out j : κ) = j :=
      Quotient.out_eq' j
    exact (hi.symm.trans (Quotient.sound hout)).trans hj
  · intro i
    exact hIeq (Quotient.out i)



end CFSG.Section9
