module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection14.PFsection14_2_Quotient

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 14: (14.2) field-model bridge
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section14

universe u v w

set_option maxHeartbeats 4000000 in
public theorem section14_appendixC_embedding_of_case_b_field_model_source_bridge
    {G : Type u} [Group G] [Finite G]
    {P U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hfieldW2 :
      Section9.quotientFieldSemidirectModelWithPrimeFieldImageData
        P ⊥ U C W1 W2 p q u)
    (hCbot : C = ⊥)
    (hdisjPU : Disjoint P U)
    (hu : u = (p ^ q - 1) / (p - 1)) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ σ : appendixCH p q →* G,
      Function.Injective σ ∧
        Subgroup.map σ (⊤ : Subgroup (appendixCH p q)) = P ⊔ U ∧
        Subgroup.map σ (appendixCPInH p q) = P ∧
        Subgroup.map σ (appendixCUInH p q) = U ∧
        Subgroup.map σ (appendixCP0InH p q) = W2 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  -- Core finite-field conversion for PF `(14.2)(a)`: transport the Section 9
  -- quotient model to the concrete Appendix C `GaloisField p q` semidirect
  -- product, using `C = ⊥`, the norm-one cardinality endpoint, and the
  -- prime-field image clause for `W₂`.
  rcases hfieldW2 with
    ⟨hnormalH0, hnormalC, hW1normU, hCinv, F, fieldInst, fintypeInst, Ustar,
      hFcard, hUstarCard, hUstarCyc, hspan, φH, φU, φW, hactions, hW2⟩
  rcases hactions with ⟨hUaction, hWaction⟩
  letI : (⊥ : Subgroup G).subgroupOf P |>.Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : Subgroup.Normalizes W1 U := ⟨hW1normU⟩
  letI : MulDistribMulAction W1 (U ⧸ C.subgroupOf U) :=
    quotientMulDistribMulAction (A := W1) (G := U) (C.subgroupOf U) hCinv
  letI : Field F := fieldInst
  letI : Fintype F := fintypeInst
  have hFcard_fintype : Fintype.card F = p ^ q := by
    simpa [Nat.card_eq_fintype_card] using hFcard
  haveI : CharP F p := charP_of_card_eq_prime_pow (R := F) hFcard_fintype
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  let eF : F ≃+* appendixCField p q :=
    Classical.choice (section14_finiteField_ringEquiv_appendixC hp hFcard)
  have hUstarCard_appendix :
      Nat.card Ustar = Nat.card (appendixCNormOneUnits p q) := by
    rw [hUstarCard, hu, appendixCNormOneUnits_natCard (p := p) (q := q)]
  let UstarC : Subgroup (appendixCField p q)ˣ :=
    Ustar.map (Units.map eF.toMonoidHom)
  have hUstarC_card : Nat.card UstarC = Nat.card Ustar := by
    exact Subgroup.card_map_of_injective
      (K := Ustar) (f := Units.map eF.toMonoidHom)
      (Units.map_injective eF.injective)
  have hUstarC_eq_norm :
      UstarC = appendixCNormOneUnits p q := by
    apply section14_cyclic_subgroup_eq_of_natCard_eq
    rw [hUstarC_card, hUstarCard_appendix]
  have hbotSubP : (⊥ : Subgroup G).subgroupOf P = ⊥ :=
    section14_subgroupOf_eq_bot_of_eq_bot (C := (⊥ : Subgroup G)) (U := P) rfl
  let ePquot : P ⧸ (⊥ : Subgroup G).subgroupOf P ≃* P :=
    (QuotientGroup.quotientMulEquivOfEq hbotSubP).trans
      (QuotientGroup.quotientBot (G := P))
  let ePfield : appendixCP p q ≃* Multiplicative F :=
    section14_addEquivToMulEquivMultiplicative (appendixCP p q) F eF.symm.toAddEquiv
  let ePmodel : appendixCP p q ≃* P :=
    (ePfield.trans φH.symm).trans ePquot
  have hCsub_bot : C.subgroupOf U = ⊥ :=
    section14_subgroupOf_eq_bot_of_eq_bot (C := C) (U := U) hCbot
  let eUquot : U ⧸ C.subgroupOf U ≃* U :=
    (QuotientGroup.quotientMulEquivOfEq hCsub_bot).trans
      (QuotientGroup.quotientBot (G := U))
  let eUstarC : Ustar ≃* UstarC :=
    section14_subgroupMapMulEquivOfInjective Ustar (Units.map eF.toMonoidHom)
      (Units.map_injective
        (show Function.Injective eF.toMonoidHom from eF.injective))
  let eNormToUstarC : appendixCNormOneUnits p q ≃* UstarC :=
    section14_subgroupCongr hUstarC_eq_norm.symm
  let eNormToUstar : appendixCNormOneUnits p q ≃* Ustar :=
    eNormToUstarC.trans eUstarC.symm
  let eUmodel : appendixCNormOneUnits p q ≃* U :=
    (eNormToUstar.trans φU.symm).trans eUquot
  let eUmodelInv : appendixCNormOneUnits p q ≃* U :=
    (section14_invMulEquivOfComm (appendixCNormOneUnits p q)).trans eUmodel
  let σP : appendixCP p q →* G := P.subtype.comp ePmodel.toMonoidHom
  let σU : appendixCNormOneUnits p q →* G := U.subtype.comp eUmodelInv.toMonoidHom
  have hcompat :
      ∀ g : appendixCNormOneUnits p q,
        σP.comp (MulEquiv.toMonoidHom (appendixCAction p q g)) =
          (MulEquiv.toMonoidHom (MulAut.conj (σU g))).comp σP := by
    intro g
    ext x
    let xP : appendixCP p q := Multiplicative.ofAdd x
    let xQ : U ⧸ C.subgroupOf U := φU.symm (eNormToUstar g)
    let hP : P := ePmodel xP
    rcases hUaction xQ hP with ⟨hconjMF, hact⟩
    let hconjP : P :=
      ⟨((Quotient.out xQ : U) : G)⁻¹ * (hP : G) *
        ((Quotient.out xQ : U) : G), hconjMF hP⟩
    have heNorm_map :
        Units.map eF.toMonoidHom ((eNormToUstar g : Ustar) : Fˣ) =
          (g : (appendixCField p q)ˣ) := by
      have hsub : eUstarC (eNormToUstar g) = eNormToUstarC g := by
        simp [eNormToUstar]
      exact congrArg (fun z : UstarC => (z : (appendixCField p q)ˣ)) hsub
    have hscalar :
        ePfield ((appendixCAction p q g) xP) =
          Multiplicative.ofAdd (((eNormToUstar g : Ustar) : Fˣ) *
            Multiplicative.toAdd (ePfield xP)) := by
      have heNorm_field :
          eF (((eNormToUstar g : Ustar) : Fˣ) : F) =
            ((g : (appendixCField p q)ˣ) : appendixCField p q) := by
        exact congrArg (fun z : (appendixCField p q)ˣ =>
          (z : appendixCField p q)) heNorm_map
      change eF.symm (Multiplicative.toAdd (((appendixCAction p q) g) xP)) =
        ((eNormToUstar g : Ustar) : Fˣ) * Multiplicative.toAdd (ePfield xP)
      rw [appendixCAction_apply_toAdd]
      apply eF.injective
      rw [eF.apply_symm_apply]
      rw [eF.map_mul (((eNormToUstar g : Ustar) : Fˣ) : F)
        (Multiplicative.toAdd (ePfield xP))]
      rw [heNorm_field]
      congr 1
      change Multiplicative.toAdd xP = eF (eF.symm (Multiplicative.toAdd xP))
      exact (eF.apply_symm_apply (Multiplicative.toAdd xP)).symm
    have hUout : eUquot xQ = Quotient.out xQ :=
      section14_quotient_bot_equiv_apply_eq_out hCsub_bot xQ
    have hφH_hP :
        φH ((QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P)) hP) =
          ePfield xP := by
      change φH ((QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P))
        (ePquot (φH.symm (ePfield xP)))) = ePfield xP
      rw [section14_quotient_bot_equiv_mk'_apply hbotSubP]
      simp
    have hscalarAction :
        ePfield ((appendixCAction p q g) xP) =
          Multiplicative.ofAdd (((φU xQ : Ustar) : Fˣ) *
            Multiplicative.toAdd
              (φH ((QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P)) hP))) := by
      rw [hscalar]
      apply congrArg Multiplicative.ofAdd
      congr 1
      · simp [xQ]
      · rw [hφH_hP]
    have hact' :=
      congrArg (fun z : Multiplicative F => ((ePquot (φH.symm z) : P) : G)) hact
    have hactAction :=
      (congrArg (fun z : Multiplicative F => ((ePquot (φH.symm z) : P) : G))
        hscalarAction).trans hact'.symm
    have hconjP_eval :
        ((ePquot (φH.symm
          (φH ((QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P)) hconjP))) :
            P) : G) = (hconjP : G) := by
      have hmk :
          ePquot ((QuotientGroup.mk' ((⊥ : Subgroup G).subgroupOf P)) hconjP) =
            hconjP := by
        simpa [ePquot] using
          (section14_quotient_bot_equiv_mk'_apply_eq
            (A := P) (N := ((⊥ : Subgroup G).subgroupOf P)) hbotSubP hconjP)
      simpa using congrArg (fun z : P => (z : G)) hmk
    have hactAction' := hactAction.trans hconjP_eval
    simpa [σP, σU, ePmodel, eUmodelInv, eUmodel, ePfield, xP, xQ, hP, hconjP,
      section14_addEquivToMulEquivMultiplicative, section14_invMulEquivOfComm,
      MulAut.conj_apply, hUout] using hactAction'
  let σ : appendixCH p q →* G := SemidirectProduct.lift σP σU hcompat
  have hσPimg : Subgroup.map σ (appendixCPInH p q) = P := by
    calc
      Subgroup.map σ (appendixCPInH p q) =
          Subgroup.map σP (⊤ : Subgroup (appendixCP p q)) := by
        simpa [σ, σP, appendixCPInH] using
          (section14_semidirect_lift_map_inl_range
            (N := appendixCP p q) (K := appendixCNormOneUnits p q)
            (H := G) (φ := appendixCAction p q) σP σU hcompat)
      _ = P := by
        simpa [σP] using section14_map_subtype_comp_equiv_top P ePmodel
  have hσUimg : Subgroup.map σ (appendixCUInH p q) = U := by
    calc
      Subgroup.map σ (appendixCUInH p q) =
          Subgroup.map σU (⊤ : Subgroup (appendixCNormOneUnits p q)) := by
        simpa [σ, σU, appendixCUInH] using
          (section14_semidirect_lift_map_inr_range
            (N := appendixCP p q) (K := appendixCNormOneUnits p q)
            (H := G) (φ := appendixCAction p q) σP σU hcompat)
      _ = U := by
        simpa [σU] using section14_map_subtype_comp_equiv_top U eUmodelInv
  refine ⟨σ, ?_, ?_, hσPimg, hσUimg, ?_⟩
  · simpa [σ, σP, σU] using
      (section14_semidirect_lift_injective_of_disjoint_images
        (N := appendixCP p q) (K := appendixCNormOneUnits p q)
        (G := G) (φ := appendixCAction p q)
        (P := P) (U := U) ePmodel eUmodelInv hdisjPU hcompat)
  · rw [← appendixCPInH_sup_appendixCUInH_eq_top (p := p) (q := q),
      Subgroup.map_sup, hσPimg, hσUimg]
  · calc
      Subgroup.map σ (appendixCP0InH p q) =
          Subgroup.map σP (appendixCP0InP p q) := by
        simpa [appendixCP0InH, σ, σP] using
          (section14_semidirect_lift_map_inl_subgroup
            (N := appendixCP p q) (K := appendixCNormOneUnits p q)
            (H := G) (φ := appendixCAction p q) σP σU hcompat
            (appendixCP0InP p q))
      _ = W2 := by
        have hP0model :
            Subgroup.map ePmodel.toMonoidHom (appendixCP0InP p q) =
              W2.subgroupOf P := by
          simpa [ePquot, ePfield, ePmodel] using
            (section14_appendixCP0InP_map_ePmodel_eq_subgroupOf
              (G := G) (F := F) (P := P) (W2 := W2) (p := p) (q := q)
              eF φH hbotSubP hW2)
        simpa [σP] using
          (section14_map_subtype_comp_equiv_eq_of_subgroupOf_eq
            (G := G) (A := appendixCP p q) (P := P) (K := W2)
            hW2.1 ePmodel hP0model)

public theorem section14_theorem_14_2_fieldIso_of_case_b_source_bridge
    {G : Type u} [Group G] [Finite G]
    {Smax P U W1 W2 C : Subgroup G} {p q u : ℕ}
    (hcase : Section13.case_9_7_b_sourceDataForSection13 Smax P U W1 W2 C p q u)
    (hCbot : C = ⊥)
    (hu : u = (p ^ q - 1) / (p - 1)) :
    theorem_14_2_a_fieldIsoData P U W2 p q := by
  have hfieldW2 :
      Section9.quotientFieldSemidirectModelWithPrimeFieldImageData
        P ⊥ U C W1 W2 p q u :=
    Section9.case_9_7_b_fieldSemidirectModelWithPrimeFieldImageData_sec9 hcase
  have _hfield :
      Section9.quotientFieldSemidirectModelData P ⊥ U C W1 p q u :=
    Section9.quotientFieldSemidirectModelData_of_withPrimeFieldImage_sec9 hfieldW2
  have hp : Nat.Prime p :=
    Section9.case_9_7_b_p_prime_sec9 hcase
  have hq : Nat.Prime q :=
    Section9.case_9_7_b_q_prime_sec9 hcase
  have hdisjPU : Disjoint P U := by
    have h92 : Section9.hypothesis_9_2_statement Smax P U W1 W2 q :=
      Section9.case_9_7_b_hypothesis_9_2_sec9 hcase
    rcases h92.typePDefinitionData with
      ⟨_hMF, _hW1cyc, _hW1ne, _hW1hall, _hcompMW1, _hUleD, _hUnil,
        _hW1normU, hcompDU, _hMFnotCyc, _hSecond, _hFitEq, _hFitLeD,
        _hW2le, _hW2cyc, _hW2ne, _hCent, _hHatW⟩
    exact hcompDU.2.2.2
  exact ⟨hp, hq,
    section14_appendixC_embedding_of_case_b_field_model_source_bridge
      hp hq hfieldW2 hCbot hdisjPU hu⟩
end CFSG.Section14
