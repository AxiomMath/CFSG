module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.InitialCanonical

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped IsMulCommutative commutatorElement

namespace CFSG.Section9

universe u v w

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_irr_Xtheta_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (_hρcardBase : Nat.card ρBase.range = a)
    (_hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    let hClamComm : IsMulCommutative Clam :=
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
    let Lam : Type u := Clam →* ℂˣ
    let hf_surj : Function.Surjective f := by
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩
      rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    letI : IsCyclic ρBase.range := hρcycBase
    letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
    let σ : ρBase.range →* MulAut Clam :=
      mulAutHomInvOfCommDomain_sec9
        (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
    let instLamAction : MulAction ρBase.range Lam :=
      linearCharacterMulAction_sec9 σ
    let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
      Subgroup.subtype ρBase.range
    let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p
        (hHcard ⟨0, hqpos⟩) ρRange
    letI : MulAction ρBase.range Lam := instLamAction
    letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    ∀ (B : Subgroup Dm) (hBnormal : B.Normal) (hAnormal : A.Normal),
    ∀ (_hA_le_B : A ≤ B)
      (_hMFD_le_B : MFD ≤ B)
      (hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B))
      (eWBK : ↥(W ⊓ B) ≃* K)
      (_hWBK_compat :
        ∀ x : ↥(W ⊓ B),
          (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))),
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormal
    letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    ∀ (QH1c QH1 QClam QH1CH1 : Subgroup Q),
    ∀ (hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1)
      (hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam)
      (eH1 : QH1 ≃* H ⟨0, hqpos⟩)
      (eClam : QClam ≃* Clam),
    ∀ (_hQH1_apply :
        ∀ (m : MFD.subgroupOf B)
          (hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩),
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1 ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩)
      (_hQH1c_apply :
        ∀ m : MFD.subgroupOf B,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c)
      (_hQClam_apply :
        ∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B))))
      (QMF : Subgroup Q)
      (_hQMF_eq :
        QMF = ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))))
      (_hQMF_split_in_Q : Section2.IsInternalDirectProduct QMF QH1c QH1)
      (_hQH1_le_QMF : QH1 ≤ QMF),
    let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
      semidirectProductOfInternalDirectProductLinearCharacter_sec9
        hsemi hprod
        (((nonprincipalLinearCharacterEquivFin_sec9
              (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
          eH1.toMonoidHom)
        (k.2.comp eClam.toMonoidHom)
    ∀ (_hIeq :
        ∀ k : Fin (p - 1) × Lam,
          Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) = B),
    ∀ (_hθnotMF :
        ∀ k : Fin (p - 1) × Lam,
          ¬ Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD),
    ∀ k : Fin (p - 1) × Lam,
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)))) := by
  classical
  dsimp
  intro B hBnormal hAnormal hA_le_B hMFD_le_B hBsemi eWBK hWBK_compat
    QH1c QH1 QClam QH1CH1 hsemi hprod eH1 eClam hQH1_apply hQH1c_apply
    hQClam_apply QMF hQMF_eq hQMF_split_in_Q hQH1_le_QMF hIeq hθnotMF k
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  have hψirr :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.quotientCharacterInflation A B (ψlin k)) :=
    Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      A B (ψlin k)
  have hinner :
      Section1.IsIrreducibleCharacterOnGroup
        (Section1.inducedCF B
          (Section1.quotientCharacterInflation A B (ψlin k))) :=
    inducedCF_isIrreducible_of_inertia_eq_self_sec9 B hψirr (by
      simpa [ψlin] using hIeq k)
  have hDnormal : Dm.Normal := by
    simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
  letI : Dm.Normal := hDnormal
  have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
    dsimp [Dm]
    exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
      M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
  have hsemiM :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup M) Dm (W1.subgroupOf M) :=
    internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcomp
  refine
    inducedCF_isIrreducible_of_semidirect_no_nontrivial_complement_fixed_sec9
      Dm (W1.subgroupOf M) hsemiM hinner ?_
  intro g hgW1 hg_ne hfix
  have hkerMFD :
      Section1.subgroupInKernel'
        (Section1.inducedCF B
          (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hsourceKerQH1c :
        ∀ b : B,
          QuotientGroup.mk' (A.subgroupOf B) b ∈ QH1c →
            Section1.quotientCharacterInflation A B (ψlin k) b =
              Section1.degree
                (Section1.quotientCharacterInflation A B (ψlin k)) := by
      intro b hb
      let qh : QH1c := ⟨QuotientGroup.mk' (A.subgroupOf B) b, hb⟩
      have hproj :
          internalSemidirectRightProjectionTop_sec9 hsemi
              (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
        simpa [qh] using
          internalSemidirectRightProjectionTop_apply_left_sec9 hsemi qh
      have hψ :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) b) =
              Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam
                (internalSemidirectRightProjectionTop_sec9 hsemi
                  (QuotientGroup.mk' (A.subgroupOf B) b)) := by
                rfl
          _ = Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam 1 := by
                rw [hproj]
          _ = 1 := by simp
      rw [Section1.quotientCharacterInflation_degree]
      simpa [Section1.quotientCharacterInflation, hψ]
    have hkerA :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) A :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B A hA_le_B hψirr
        (Section1.subgroupInKernel'_quotientCharacterInflation A B (ψlin k))
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    let gW1 : W1 := ⟨(g : G), by
      simpa [Subgroup.mem_subgroupOf] using hgW1⟩
    have hgW1_ne : gW1 ≠ 1 := by
      intro hg1
      apply hg_ne
      ext
      exact congrArg (fun x : W1 => (x : G)) hg1
    let gW1inv : W1 := gW1⁻¹
    have hgW1inv_ne : gW1inv ≠ 1 := by
      intro hg1
      exact hgW1_ne (inv_eq_one.mp hg1)
    rcases theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
        H hqpos hHcard hHnorm hHindep hconjBase hcase gW1inv hgW1inv_ne with
      ⟨iMove, hiMove_ne, hbase_to_iMove⟩
    let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
      ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
    rcases hbase_to_iMove with
      ⟨hconjMF_move, actionMove, hactionMove, htargetMove⟩
    have hbase_conj_mem_H1c :
        ∀ m : MF,
          QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H ⟨0, hqpos⟩ →
            QuotientGroup.mk' (H0.subgroupOf MF)
                ⟨(g : G) * (m : G) * (g : G)⁻¹, by
                  simpa [gW1inv, gW1] using hconjMF_move m⟩ ∈ H1cMF := by
      intro m hmBase
      have htarget_mem :
          actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) ∈ H iMove := by
        rw [htargetMove]
        exact ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase, rfl⟩
      have hcoord :
          actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) =
            QuotientGroup.mk' (H0.subgroupOf MF)
              ⟨(g : G) * (m : G) * (g : G)⁻¹, by
                simpa [gW1inv, gW1] using hconjMF_move m⟩ := by
        simpa [gW1inv, gW1] using hactionMove m
      rw [hcoord] at htarget_mem
      exact
        Subgroup.mem_iSup_of_mem iMove
          (Subgroup.mem_iSup_of_mem hiMove_ne htarget_mem)
    let qMFD : MFD →* (MF ⧸ H0.subgroupOf MF) :=
      (QuotientGroup.mk' (H0.subgroupOf MF)).comp
        (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF)
    let MFDH1cSub : Subgroup MFD := H1cMF.comap qMFD
    let MFDH1Sub : Subgroup MFD := (H ⟨0, hqpos⟩).comap qMFD
    let MFDH1c : Subgroup Dm := MFDH1cSub.map MFD.subtype
    let MFDH1 : Subgroup Dm := MFDH1Sub.map MFD.subtype
    have hMFleD : MF ≤ ambientDerivedSubgroup M :=
      MF_le_ambientDerived_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
    have hDleM : ambientDerivedSubgroup M ≤ M :=
      section12_ambientDerivedSubgroup_le (E := M)
    have hqMFD_surj : Function.Surjective qMFD := by
      intro x
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨mMF, rfl⟩
      let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
      let mD : Dm := ⟨mM, by
        simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
      let mMFD : MFD := ⟨mD, by
        change (mD : M) ∈ MF.subgroupOf M
        simp [mD, mM, Subgroup.mem_subgroupOf]⟩
      refine ⟨mMFD, ?_⟩
      rfl
    have hMF_Hsplit :
        Section2.IsInternalDirectProduct
          (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
      simpa [H1cMF] using
        theorem_9_8_iSup_split_base_internalDirectProduct_sec9
          H ⟨0, hqpos⟩ hHindep hHsup
    have hMF_Hsplit_sup : H1cMF ⊔ H ⟨0, hqpos⟩ = ⊤ := by
      apply top_unique
      intro x _hx
      rcases hMF_Hsplit.mul_surjective x (by trivial) with
        ⟨h1c, hh1c, h1, hh1, hx⟩
      rw [hx]
      exact (H1cMF ⊔ H ⟨0, hqpos⟩).mul_mem
        (Subgroup.mem_sup_left hh1c) (Subgroup.mem_sup_right hh1)
    have hMFD_coord_sup : MFDH1cSub ⊔ MFDH1Sub = ⊤ := by
      have hle_range_H1c : H1cMF ≤ qMFD.range := by
        rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
        exact le_top
      have hle_range_H1 : H ⟨0, hqpos⟩ ≤ qMFD.range := by
        rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
        exact le_top
      calc
        MFDH1cSub ⊔ MFDH1Sub =
            (H1cMF ⊔ H ⟨0, hqpos⟩).comap qMFD := by
              simpa [MFDH1cSub, MFDH1Sub] using
                Subgroup.comap_sup_eq_of_le_range qMFD hle_range_H1c hle_range_H1
        _ = ⊤ := by
              rw [hMF_Hsplit_sup]
              rfl
    have hMFD_map_top : (⊤ : Subgroup MFD).map MFD.subtype = MFD := by
      ext x
      constructor
      · intro hx
        rcases hx with ⟨y, _hy, hyx⟩
        rw [← hyx]
        exact y.property
      · intro hx
        exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hMFDH_join : MFDH1c ⊔ MFDH1 = MFD := by
      calc
        MFDH1c ⊔ MFDH1 =
            (MFDH1cSub ⊔ MFDH1Sub).map MFD.subtype := by
              rw [Subgroup.map_sup]
        _ = (⊤ : Subgroup MFD).map MFD.subtype := by rw [hMFD_coord_sup]
        _ = MFD := hMFD_map_top
    have hH1cMF_norm_U : quotientSubgroupNormalizedBy MF H0 U H1cMF := by
      intro aU
      rcases hHnorm ⟨0, hqpos⟩ aU with ⟨hconjMF, action, haction, _hmapBase⟩
      refine ⟨hconjMF, action, haction, ?_⟩
      have hmap_each :
          ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
        intro i
        rcases hHnorm i aU with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
        have haction_eq : action_i = action := by
          ext x
          rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
          calc
            action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF_i h⟩ := haction_i h
            _ = QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF h⟩ := by
                  congr 1
            _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
        simpa [haction_eq] using hmap_i.symm
      have hmap_sup : H1cMF.map action.toMonoidHom = H1cMF := by
        simp_rw [H1cMF, Subgroup.map_iSup, hmap_each]
      exact hmap_sup.symm
    have hsourceKerMFDH1c :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFDH1c.subgroupOf B) := by
      intro a
      have haMFDH1c : ((a : B) : Dm) ∈ MFDH1c := by
        exact Subgroup.mem_subgroupOf.mp a.property
      rcases haMFDH1c with ⟨y, hyH1c, hy_eq⟩
      have haMFD : ((a : B) : Dm) ∈ MFD := by
        rw [← hy_eq]
        exact y.property
      let mSub : MFD.subgroupOf B := ⟨a, by
        simpa [Subgroup.mem_subgroupOf] using haMFD⟩
      have hy_mSub :
          y = (Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub := by
        apply Subtype.ext
        simpa [mSub, Subgroup.subgroupOfEquivOfLe] using hy_eq
      have hmH1c :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
            H1cMF := by
        have hycoord : qMFD y ∈ H1cMF := by
          simpa [MFDH1cSub] using hyH1c
        simpa [qMFD, hy_mSub]
          using hycoord
      have hmQH1c :
          QuotientGroup.mk' (A.subgroupOf B) mSub ∈ QH1c :=
        hQH1c_apply mSub hmH1c
      simpa [mSub] using hsourceKerQH1c a hmQH1c
    have hMFDH1c_le_MFD : MFDH1c ≤ MFD := by
      intro x hx
      rcases hx with ⟨y, _hy, hyx⟩
      rw [← hyx]
      exact y.property
    have hMFDH1c_le_B : MFDH1c ≤ B :=
      hMFDH1c_le_MFD.trans hMFD_le_B
    have hMFDH1c_normal : MFDH1c.Normal := by
      refine Subgroup.Normal.mk ?_
      intro n hn x
      rcases hn with ⟨n0, hn0H1c, hn0_eq⟩
      have hnMFD : n ∈ MFD := by
        rw [← hn0_eq]
        exact n0.property
      let conjMFD : MFD := ⟨x * n * x⁻¹, hMFDnormal.conj_mem n hnMFD x⟩
      refine ⟨conjMFD, ?_, rfl⟩
      rcases hsemiTop.mul_surjective x (by trivial) with ⟨m, hm, w, hw, hxmw⟩
      let mMFD : MFD := ⟨m, hm⟩
      let wU : U := ⟨(((w : Dm) : M) : G), by
        have hwUM : ((w : Dm) : M) ∈ U.subgroupOf M := by
          simpa [W, Dm, Subgroup.mem_subgroupOf] using hw
        simpa [Subgroup.mem_subgroupOf] using hwUM⟩
      let wConjMFD : MFD :=
        ⟨w * n * w⁻¹, hsemiTop.right_normalizes_left w hw n hnMFD⟩
      have hq_wConj_mem : qMFD wConjMFD ∈ H1cMF := by
        rcases hH1cMF_norm_U (wU⁻¹) with
          ⟨hconjMF, action, haction, hmap⟩
        have hmem_action : action (qMFD n0) ∈ H1cMF := by
          rw [hmap]
          exact Subgroup.mem_map_of_mem action.toMonoidHom (by
            simpa [MFDH1cSub] using hn0H1c)
        have hcoord : action (qMFD n0) = qMFD wConjMFD := by
          let nMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF n0
          have hact := haction nMF
          have hrhs :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                    hconjMF nMF⟩ : MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF wConjMFD) := by
            congr 1
            apply Subtype.ext
            simpa [theorem_9_8_MFDSubgroupOf_to_MF_sec9, nMF, wConjMFD, wU,
              hn0_eq, mul_assoc]
          calc
            action (qMFD n0) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                    hconjMF nMF⟩ : MF) := by
                  simpa [qMFD, nMF] using hact
            _ = qMFD wConjMFD := by
                  simpa [qMFD] using hrhs
        rwa [hcoord] at hmem_action
      have hH1c_normal : H1cMF.Normal :=
        by
          refine Subgroup.Normal.mk ?_
          intro n hn g
          have h : g * n * g⁻¹ = n := by
            simp [mul_assoc, mul_comm]
          simpa [h] using hn
      have hconj_eq :
          conjMFD = mMFD * wConjMFD * mMFD⁻¹ := by
        apply Subtype.ext
        simp [conjMFD, mMFD, wConjMFD, hxmw, mul_assoc]
      rw [hconj_eq]
      change qMFD (mMFD * wConjMFD * mMFD⁻¹) ∈ H1cMF
      simpa [map_mul, map_inv, mul_assoc] using
        hH1c_normal.conj_mem (qMFD wConjMFD) hq_wConj_mem (qMFD mMFD)
    letI : MFDH1c.Normal := hMFDH1c_normal
    have hkerMFDH1c :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1c :=
      subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
        B MFDH1c hMFDH1c_le_B hψirr hsourceKerMFDH1c
    have hkerMFDH1 :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1 := by
      intro z
      rcases z.property with ⟨z0, hz0H1, hz0_eq⟩
      let zD : Dm := MFD.subtype z0
      let zMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF z0
      have hz0Base :
          QuotientGroup.mk' (H0.subgroupOf MF) zMF ∈ H ⟨0, hqpos⟩ := by
        simpa [MFDH1Sub, qMFD, zMF] using hz0H1
      let zConjD : Dm :=
        ⟨(g : M) * (zD : M) * (g : M)⁻¹,
          hDnormal.conj_mem (zD : M) zD.property g⟩
      have hzConjMFD : zConjD ∈ MFD := by
        change (zConjD : M) ∈ MF.subgroupOf M
        have hzMFconj := hconjMF_move zMF
        simpa [zConjD, zD, zMF, gW1inv, gW1,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9,
          Subgroup.mem_subgroupOf, mul_assoc] using hzMFconj
      let zConjMFD : MFD := ⟨zConjD, hzConjMFD⟩
      have hzConjH1cSub : zConjMFD ∈ MFDH1cSub := by
        have hzcoord := hbase_conj_mem_H1c zMF hz0Base
        simpa [MFDH1cSub, qMFD, zConjMFD, zConjD, zD, zMF,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9, mul_assoc] using hzcoord
      have hzConjH1c : zConjD ∈ MFDH1c :=
        ⟨zConjMFD, hzConjH1cSub, rfl⟩
      have hker_conj :=
        hkerMFDH1c ⟨zConjD, hzConjH1c⟩
      have hfix_eval := congrFun hfix (z : Dm)
      have hX_conj_eq :
          Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) zConjD =
            Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) (z : Dm) := by
        simpa [Section1.conjugateOnNormal, zConjD, zD, hz0_eq, ψlin] using hfix_eval
      exact hX_conj_eq.symm.trans hker_conj
    have hkerJoin :
        Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)))
          (MFDH1c ⊔ MFDH1) :=
      subgroupInKernel'_sup_of_irreducible_sec9 hinner hkerMFDH1c hkerMFDH1
    rw [← hMFDH_join]
    exact hkerJoin
  exact False.elim (hθnotMF k (by
    simpa [A, MFD, ψlin] using hkerMFD))

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_inj_Xtheta_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (_hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (_hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    let f : U →* ρBase.range :=
      ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
    let K : Subgroup U := f.ker
    let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
      theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
        U Uprime hUprimeEq
    let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
    letI : Hsub.Normal := hUprimeNormal.subgroupOf K
    let Clam : Type u := K ⧸ Hsub
    letI : Group Clam := inferInstance
    let hClamComm : IsMulCommutative Clam :=
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
    let Lam : Type u := Clam →* ℂˣ
    let hf_surj : Function.Surjective f := by
      intro y
      rcases y with ⟨y, hy⟩
      rcases hy with ⟨x, rfl⟩
      rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
      exact ⟨u, rfl⟩
    letI : IsCyclic ρBase.range := hρcycBase
    letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
    let σ : ρBase.range →* MulAut Clam :=
      mulAutHomInvOfCommDomain_sec9
        (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
    let instLamAction : MulAction ρBase.range Lam :=
      linearCharacterMulAction_sec9 σ
    let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
      Subgroup.subtype ρBase.range
    let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
      nonprincipalLinearCharacterIndexMulAction_sec9 p
        (hHcard ⟨0, hqpos⟩) ρRange
    letI : MulAction ρBase.range Lam := instLamAction
    letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    ∀ (B : Subgroup Dm) (hBnormal : B.Normal) (hAnormal : A.Normal),
    ∀ (_hMFD_le_B : MFD ≤ B)
      (hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B))
      (eWBK : ↥(W ⊓ B) ≃* K)
      (_hWBK_compat :
        ∀ x : ↥(W ⊓ B),
          (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))),
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormal
    letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    ∀ (QH1c QH1 QClam QH1CH1 : Subgroup Q),
    ∀ (hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1)
      (hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam)
      (eH1 : QH1 ≃* H ⟨0, hqpos⟩)
      (eClam : QClam ≃* Clam),
    let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
      semidirectProductOfInternalDirectProductLinearCharacter_sec9
        hsemi hprod
        (((nonprincipalLinearCharacterEquivFin_sec9
              (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
          eH1.toMonoidHom)
        (k.2.comp eClam.toMonoidHom)
    ∀ (_hQH1_apply :
        ∀ (m : MFD.subgroupOf B)
          (hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩),
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1 ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩)
      (_hQH1c_apply :
        ∀ m : MFD.subgroupOf B,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c)
      (_hQClam_apply :
        ∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B)))),
    ∀ (_hIeq :
        ∀ k : Fin (p - 1) × Lam,
          Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) = B)
      (_hθnotMF :
        ∀ k : Fin (p - 1) × Lam,
          ¬ Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD)
      (_hψlin_injective : Function.Injective ψlin)
      (_hpairStabilizer :
        ∀ k : Fin (p - 1) × Lam,
          MulAction.stabilizer ρBase.range k = ⊥),
    ∀ k l : Fin (p - 1) × Lam,
      Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) =
        Section1.inducedCF Dm
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l))) →
      MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l := by
  classical
  dsimp
  intro B hBnormal hAnormal hMFD_le_B hBsemi eWBK hWBK_compat QH1c QH1 QClam
    QH1CH1 hsemi hprod eH1 eClam hQH1_apply hQH1c_apply hQClam_apply hIeq
    hθnotMF hψlin_injective hpairStabilizer
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let Lam : Type u := Clam →* ℂˣ
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  haveI : IsCyclic ρBase.range := hρcycBase
  haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let ψlin : Fin (p - 1) × Lam → (B ⧸ A.subgroupOf B) →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  have hψirr :
      ∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) := by
    intro k
    exact Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
      A B (ψlin k)
  have hinner_irr :
      ∀ k : Fin (p - 1) × Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) := by
    intro k
    exact inducedCF_isIrreducible_of_inertia_eq_self_sec9 B (hψirr k) (by
      simpa [ψlin] using hIeq k)
  have houter_to_inner :
      ∀ k l : Fin (p - 1) × Lam,
        Section1.inducedCF Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) =
          Section1.inducedCF Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) →
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) := by
    have hDnormal : Dm.Normal := by
      simpa [Dm] using (section12_normalIn_ambientDerivedSubgroup (G := G) (E := M)).2
    letI : Dm.Normal := hDnormal
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    have hcomp : Dm.IsComplement' (W1.subgroupOf M) := by
      dsimp [Dm]
      exact ambientDerived_W1_isComplement'_subgroupOf_M_of_hypothesis_9_2_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
    have hsemiM :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup M) Dm (W1.subgroupOf M) :=
      internalSemidirectProduct_top_of_normal_isComplement'_sec9 hcomp
    have hinner_class :
        ∀ r : Fin (p - 1) × Lam,
          Section1.IsClassFunction
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin r))) := by
      intro r
      exact Section1.inducedCF_isClassFunction B
        (Section1.quotientCharacterInflation A B (ψlin r))
    intro k l hInd
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        Dm (hinner_irr k) (hinner_irr l) hInd with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemiM.mul_surjective g (by trivial) with ⟨d0, hd0, w0, hw0, hg⟩
    have hconjW :
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) w0 := by
      have hconjMW :
          Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k)) =
            Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) (d0 * w0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) (d0 * w0) =
            Section1.conjugateOnNormal Dm
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin l))) w0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l))) (hinner_class l) hd0
      exact hconjMW.trans herase
    have hw0_eq : w0 = 1 := by
      by_contra hw0_ne
      have hkerMFD :
          Section1.subgroupInKernel'
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
        have hsourceKerQH1c :
            ∀ r : Fin (p - 1) × Lam,
              ∀ b : B,
                QuotientGroup.mk' (A.subgroupOf B) b ∈ QH1c →
                  Section1.quotientCharacterInflation A B (ψlin r) b =
                    Section1.degree
                      (Section1.quotientCharacterInflation A B (ψlin r)) := by
          intro r b hb
          let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
            ((nonprincipalLinearCharacterEquivFin_sec9
                (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) r.1).1
          let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
          let ηQClam : QClam →* ℂˣ := r.2.comp eClam.toMonoidHom
          let qh : QH1c := ⟨QuotientGroup.mk' (A.subgroupOf B) b, hb⟩
          have hproj :
              internalSemidirectRightProjectionTop_sec9 hsemi
                  (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
            simpa [qh] using
              internalSemidirectRightProjectionTop_apply_left_sec9 hsemi qh
          have hψ :
              ψlin r (QuotientGroup.mk' (A.subgroupOf B) b) = 1 := by
            calc
              ψlin r (QuotientGroup.mk' (A.subgroupOf B) b) =
                  Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam
                    (internalSemidirectRightProjectionTop_sec9 hsemi
                      (QuotientGroup.mk' (A.subgroupOf B) b)) := by
                    rfl
              _ = Section3.internalDirectProductLinearCharacter hprod χQH1 ηQClam 1 := by
                    rw [hproj]
              _ = 1 := by simp
          rw [Section1.quotientCharacterInflation_degree]
          simpa [Section1.quotientCharacterInflation, hψ]
        let w0W1 : W1 := ⟨(w0 : G), by
          simpa [Subgroup.mem_subgroupOf] using hw0⟩
        have hw0W1_ne : w0W1 ≠ 1 := by
          intro hw1
          apply hw0_ne
          ext
          exact congrArg (fun x : W1 => (x : G)) hw1
        let w0W1inv : W1 := w0W1⁻¹
        have hw0W1inv_ne : w0W1inv ≠ 1 := by
          intro hw1
          exact hw0W1_ne (inv_eq_one.mp hw1)
        rcases theorem_9_8_weak_orbit_nonidentity_moves_base_sec9
            H hqpos hHcard hHnorm hHindep hconjBase hcase w0W1inv hw0W1inv_ne with
          ⟨iMove, hiMove_ne, hbase_to_iMove⟩
        let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
          ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
        rcases hbase_to_iMove with
          ⟨hconjMF_move, actionMove, hactionMove, htargetMove⟩
        have hbase_conj_mem_H1c :
            ∀ m : MF,
              QuotientGroup.mk' (H0.subgroupOf MF) m ∈ H ⟨0, hqpos⟩ →
                QuotientGroup.mk' (H0.subgroupOf MF)
                    ⟨(w0 : G) * (m : G) * (w0 : G)⁻¹, by
                      simpa [w0W1inv, w0W1] using hconjMF_move m⟩ ∈ H1cMF := by
          intro m hmBase
          have htarget_mem :
              actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) ∈ H iMove := by
            rw [htargetMove]
            exact ⟨QuotientGroup.mk' (H0.subgroupOf MF) m, hmBase, rfl⟩
          have hcoord :
              actionMove (QuotientGroup.mk' (H0.subgroupOf MF) m) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(w0 : G) * (m : G) * (w0 : G)⁻¹, by
                    simpa [w0W1inv, w0W1] using hconjMF_move m⟩ := by
            simpa [w0W1inv, w0W1] using hactionMove m
          rw [hcoord] at htarget_mem
          exact
            Subgroup.mem_iSup_of_mem iMove
              (Subgroup.mem_iSup_of_mem hiMove_ne htarget_mem)
        let qMFD : MFD →* (MF ⧸ H0.subgroupOf MF) :=
          (QuotientGroup.mk' (H0.subgroupOf MF)).comp
            (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF)
        let MFDH1cSub : Subgroup MFD := H1cMF.comap qMFD
        let MFDH1Sub : Subgroup MFD := (H ⟨0, hqpos⟩).comap qMFD
        let MFDH1c : Subgroup Dm := MFDH1cSub.map MFD.subtype
        let MFDH1 : Subgroup Dm := MFDH1Sub.map MFD.subtype
        have hMFleD : MF ≤ ambientDerivedSubgroup M :=
          MF_le_ambientDerived_of_hypothesis_9_2_sec9
            M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
        have hDleM : ambientDerivedSubgroup M ≤ M :=
          section12_ambientDerivedSubgroup_le (E := M)
        have hqMFD_surj : Function.Surjective qMFD := by
          intro x
          rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨mMF, rfl⟩
          let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
          let mD : Dm := ⟨mM, by
            simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
          let mMFD : MFD := ⟨mD, by
            change (mD : M) ∈ MF.subgroupOf M
            simp [mD, mM, Subgroup.mem_subgroupOf]⟩
          exact ⟨mMFD, rfl⟩
        have hMF_Hsplit :
            Section2.IsInternalDirectProduct
              (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
          simpa [H1cMF] using
            theorem_9_8_iSup_split_base_internalDirectProduct_sec9
              H ⟨0, hqpos⟩ hHindep hHsup
        have hMF_Hsplit_sup : H1cMF ⊔ H ⟨0, hqpos⟩ = ⊤ := by
          apply top_unique
          intro x _hx
          rcases hMF_Hsplit.mul_surjective x (by trivial) with ⟨h1c, hh1c, h1, hh1, hx⟩
          rw [hx]
          exact (H1cMF ⊔ H ⟨0, hqpos⟩).mul_mem
            (Subgroup.mem_sup_left hh1c) (Subgroup.mem_sup_right hh1)
        have hMFD_coord_sup : MFDH1cSub ⊔ MFDH1Sub = ⊤ := by
          have hle_range_H1c : H1cMF ≤ qMFD.range := by
            rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
            exact le_top
          have hle_range_H1 : H ⟨0, hqpos⟩ ≤ qMFD.range := by
            rw [MonoidHom.range_eq_top.mpr hqMFD_surj]
            exact le_top
          calc
            MFDH1cSub ⊔ MFDH1Sub =
                (H1cMF ⊔ H ⟨0, hqpos⟩).comap qMFD := by
                  simpa [MFDH1cSub, MFDH1Sub] using
                    Subgroup.comap_sup_eq_of_le_range qMFD hle_range_H1c hle_range_H1
            _ = ⊤ := by
                  rw [hMF_Hsplit_sup]
                  rfl
        have hMFD_map_top : (⊤ : Subgroup MFD).map MFD.subtype = MFD := by
          ext x
          constructor
          · intro hx
            rcases hx with ⟨y, _hy, hyx⟩
            rw [← hyx]
            exact y.property
          · intro hx
            exact ⟨⟨x, hx⟩, trivial, rfl⟩
        have hMFDH_join : MFDH1c ⊔ MFDH1 = MFD := by
          calc
            MFDH1c ⊔ MFDH1 =
                (MFDH1cSub ⊔ MFDH1Sub).map MFD.subtype := by
                  rw [Subgroup.map_sup]
            _ = (⊤ : Subgroup MFD).map MFD.subtype := by rw [hMFD_coord_sup]
            _ = MFD := hMFD_map_top
        have hH1cMF_norm_U : quotientSubgroupNormalizedBy MF H0 U H1cMF := by
          intro aU
          rcases hHnorm ⟨0, hqpos⟩ aU with ⟨hconjMF, action, haction, _hmapBase⟩
          refine ⟨hconjMF, action, haction, ?_⟩
          have hmap_each :
              ∀ i : Fin q, (H i).map action.toMonoidHom = H i := by
            intro i
            rcases hHnorm i aU with ⟨hconjMF_i, action_i, haction_i, hmap_i⟩
            have haction_eq : action_i = action := by
              ext x
              rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF) x with ⟨h, rfl⟩
              calc
                action_i (QuotientGroup.mk' (H0.subgroupOf MF) h) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF_i h⟩ := haction_i h
                _ = QuotientGroup.mk' (H0.subgroupOf MF)
                      ⟨(aU : G)⁻¹ * (h : G) * (aU : G), hconjMF h⟩ := by
                      congr 1
                _ = action (QuotientGroup.mk' (H0.subgroupOf MF) h) := (haction h).symm
            simpa [haction_eq] using hmap_i.symm
          have hmap_sup : H1cMF.map action.toMonoidHom = H1cMF := by
            simp_rw [H1cMF, Subgroup.map_iSup, hmap_each]
          exact hmap_sup.symm
        have hMFDH1c_le_MFD : MFDH1c ≤ MFD := by
          intro x hx
          rcases hx with ⟨y, _hy, hyx⟩
          rw [← hyx]
          exact y.property
        have hMFDH1c_le_B : MFDH1c ≤ B :=
          hMFDH1c_le_MFD.trans hMFD_le_B
        have hMFDH1c_normal : MFDH1c.Normal := by
          refine Subgroup.Normal.mk ?_
          intro n hn x
          rcases hn with ⟨n0, hn0H1c, hn0_eq⟩
          have hnMFD : n ∈ MFD := by
            rw [← hn0_eq]
            exact n0.property
          let conjMFD : MFD := ⟨x * n * x⁻¹, hMFDnormal.conj_mem n hnMFD x⟩
          refine ⟨conjMFD, ?_, rfl⟩
          rcases hsemiTop.mul_surjective x (by trivial) with ⟨m, hm, w, hw, hxmw⟩
          let mMFD : MFD := ⟨m, hm⟩
          let wU : U := ⟨(((w : Dm) : M) : G), by
            have hwUM : ((w : Dm) : M) ∈ U.subgroupOf M := by
              simpa [W, Dm, Subgroup.mem_subgroupOf] using hw
            simpa [Subgroup.mem_subgroupOf] using hwUM⟩
          let wConjMFD : MFD :=
            ⟨w * n * w⁻¹, hsemiTop.right_normalizes_left w hw n hnMFD⟩
          have hq_wConj_mem : qMFD wConjMFD ∈ H1cMF := by
            rcases hH1cMF_norm_U (wU⁻¹) with
              ⟨hconjMF, action, haction, hmap⟩
            have hmem_action : action (qMFD n0) ∈ H1cMF := by
              rw [hmap]
              exact Subgroup.mem_map_of_mem action.toMonoidHom (by
                simpa [MFDH1cSub] using hn0H1c)
            have hcoord : action (qMFD n0) = qMFD wConjMFD := by
              let nMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF n0
              have hact := haction nMF
              have hrhs :
                  QuotientGroup.mk' (H0.subgroupOf MF)
                      (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                        hconjMF nMF⟩ : MF) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF wConjMFD) := by
                congr 1
                apply Subtype.ext
                simpa [theorem_9_8_MFDSubgroupOf_to_MF_sec9, nMF, wConjMFD, wU,
                  hn0_eq, mul_assoc]
              calc
                action (qMFD n0) =
                    QuotientGroup.mk' (H0.subgroupOf MF)
                      (⟨(((wU⁻¹ : U) : G))⁻¹ * (nMF : G) * ((wU⁻¹ : U) : G),
                        hconjMF nMF⟩ : MF) := by
                      simpa [qMFD, nMF] using hact
                _ = qMFD wConjMFD := by
                      simpa [qMFD] using hrhs
            rwa [hcoord] at hmem_action
          have hH1c_normal : H1cMF.Normal := by
            refine Subgroup.Normal.mk ?_
            intro n hn g
            have h : g * n * g⁻¹ = n := by
              simp [mul_assoc, mul_comm]
            simpa [h] using hn
          have hconj_eq :
              conjMFD = mMFD * wConjMFD * mMFD⁻¹ := by
            apply Subtype.ext
            simp [conjMFD, mMFD, wConjMFD, hxmw, mul_assoc]
          rw [hconj_eq]
          change qMFD (mMFD * wConjMFD * mMFD⁻¹) ∈ H1cMF
          simpa [map_mul, map_inv, mul_assoc] using
            hH1c_normal.conj_mem (qMFD wConjMFD) hq_wConj_mem (qMFD mMFD)
        letI : MFDH1c.Normal := hMFDH1c_normal
        have hsourceKerMFDH1c :
            ∀ r : Fin (p - 1) × Lam,
              Section1.subgroupInKernel'
                (Section1.quotientCharacterInflation A B (ψlin r))
                (MFDH1c.subgroupOf B) := by
          intro r a
          have haMFDH1c : ((a : B) : Dm) ∈ MFDH1c := by
            exact Subgroup.mem_subgroupOf.mp a.property
          rcases haMFDH1c with ⟨y, hyH1c, hy_eq⟩
          have haMFD : ((a : B) : Dm) ∈ MFD := by
            rw [← hy_eq]
            exact y.property
          let mSub : MFD.subgroupOf B := ⟨a, by
            simpa [Subgroup.mem_subgroupOf] using haMFD⟩
          have hy_mSub :
              y = (Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub := by
            apply Subtype.ext
            simpa [mSub, Subgroup.subgroupOfEquivOfLe] using hy_eq
          have hmH1c :
              QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
                H1cMF := by
            have hycoord : qMFD y ∈ H1cMF := by
              simpa [MFDH1cSub] using hyH1c
            simpa [qMFD, hy_mSub] using hycoord
          have hmQH1c :
              QuotientGroup.mk' (A.subgroupOf B) mSub ∈ QH1c :=
            hQH1c_apply mSub hmH1c
          simpa [mSub] using hsourceKerQH1c r a hmQH1c
        have hkerMFDH1c :
            ∀ r : Fin (p - 1) × Lam,
              Section1.subgroupInKernel'
                (Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin r))) MFDH1c := by
          intro r
          exact subgroupInKernel'_inducedCF_of_subgroupInKernel'_sec9
            B MFDH1c hMFDH1c_le_B (hψirr r) (hsourceKerMFDH1c r)
        have hkerMFDH1 :
            Section1.subgroupInKernel'
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin k))) MFDH1 := by
          intro z
          rcases z.property with ⟨z0, hz0H1, hz0_eq⟩
          let zD : Dm := MFD.subtype z0
          let zMF : MF := theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF z0
          have hz0Base :
              QuotientGroup.mk' (H0.subgroupOf MF) zMF ∈ H ⟨0, hqpos⟩ := by
            simpa [MFDH1Sub, qMFD, zMF] using hz0H1
          let zConjD : Dm :=
            ⟨(w0 : M) * (zD : M) * (w0 : M)⁻¹,
              hDnormal.conj_mem (zD : M) zD.property w0⟩
          have hzConjMFD : zConjD ∈ MFD := by
            change (zConjD : M) ∈ MF.subgroupOf M
            have hzMFconj := hconjMF_move zMF
            simpa [zConjD, zD, zMF, w0W1inv, w0W1,
              theorem_9_8_MFDSubgroupOf_to_MF_sec9,
              Subgroup.mem_subgroupOf, mul_assoc] using hzMFconj
          let zConjMFD : MFD := ⟨zConjD, hzConjMFD⟩
          have hzConjH1cSub : zConjMFD ∈ MFDH1cSub := by
            have hzcoord := hbase_conj_mem_H1c zMF hz0Base
            simpa [MFDH1cSub, qMFD, zConjMFD, zConjD, zD, zMF,
              theorem_9_8_MFDSubgroupOf_to_MF_sec9, mul_assoc] using hzcoord
          have hzConjH1c : zConjD ∈ MFDH1c :=
            ⟨zConjMFD, hzConjH1cSub, rfl⟩
          have hker_conj :=
            hkerMFDH1c l ⟨zConjD, hzConjH1c⟩
          have hdegree_lk :
              Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin l))) =
                Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin k))) := by
            have hdegree_kl :
                Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin k))) =
                  Section1.degree
                    (Section1.inducedCF B
                      (Section1.quotientCharacterInflation A B (ψlin l))) := by
              have hdegree_conj :
                  Section1.degree
                      (Section1.conjugateOnNormal Dm
                        (Section1.inducedCF B
                          (Section1.quotientCharacterInflation A B (ψlin l))) w0) =
                    Section1.degree
                      (Section1.inducedCF B
                        (Section1.quotientCharacterInflation A B (ψlin l))) := by
                unfold Section1.degree Section1.conjugateOnNormal
                exact congrArg
                  (Section1.inducedCF B
                    (Section1.quotientCharacterInflation A B (ψlin l)))
                  (Subtype.ext (by simp))
              exact (congrArg Section1.degree hconjW).trans hdegree_conj
            exact hdegree_kl.symm
          have hconj_eval := congrFun hconjW (z : Dm)
          have hX_conj_eq :
              Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin k)) (z : Dm) =
                Section1.inducedCF B
                  (Section1.quotientCharacterInflation A B (ψlin l)) zConjD := by
            simpa [Section1.conjugateOnNormal, zConjD, zD, hz0_eq] using hconj_eval
          exact (hX_conj_eq.trans hker_conj).trans hdegree_lk
        have hkerJoin :
            Section1.subgroupInKernel'
              (Section1.inducedCF B
                (Section1.quotientCharacterInflation A B (ψlin k)))
              (MFDH1c ⊔ MFDH1) :=
          subgroupInKernel'_sup_of_irreducible_sec9 (hinner_irr k)
            (hkerMFDH1c k) hkerMFDH1
        rw [← hMFDH_join]
        exact hkerJoin
      exact False.elim (hθnotMF k (by
        simpa [MFD, A, ψlin] using hkerMFD))
    have hconjW_one :
        Section1.conjugateOnNormal Dm
            (Section1.inducedCF B
              (Section1.quotientCharacterInflation A B (ψlin l))) w0 =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) := by
      funext x
      simp [hw0_eq, Section1.conjugateOnNormal]
    exact hconjW.trans hconjW_one
  have hinner_orbit :
      ∀ k l : Fin (p - 1) × Lam,
        Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k)) =
          Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin l)) →
        MulAction.orbitRel ρBase.range (Fin (p - 1) × Lam) k l := by
    have hMFDnormal : MFD.Normal := by
      simpa [MFD, Dm] using
        theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
          M MF U W1 W2 H0 C p q a hcase
    letI : MFD.Normal := hMFDnormal
    have hsemiTop :
        Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
      simpa [MFD, W, Dm] using
        theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
    have hsource_class :
        ∀ r : Fin (p - 1) × Lam,
          Section1.IsClassFunction
            (Section1.quotientCharacterInflation A B (ψlin r)) := by
      intro r
      exact Section1.quotientCharacterInflation_isClassFunction A B (ψlin r)
    have hfirst_of_conj :
        ∀ (k l : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
          (((u0 : Dm) : M) : G) = (uU : G) →
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 →
          k.1 = (f uU • l).1 := by
      intro k l u0 uU hu0 hconj
      change k.1 = f uU • l.1
      let χbaseK : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
      let χbaseL : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
      let χbaseAction : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) (f uU • l.1)).1
      have hχbase_action :
          χbaseAction = χbaseL.comp (ρRange (f uU)).symm.toMonoidHom := by
        simpa [χbaseL, χbaseAction, ρRange, instFirstAction] using
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange (f uU) l.1
      have hχ : χbaseK = χbaseAction := by
        ext x
        have hMFleD : MF ≤ ambientDerivedSubgroup M :=
          MF_le_ambientDerived_of_hypothesis_9_2_sec9
            M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
        have hDleM : ambientDerivedSubgroup M ≤ M :=
          section12_ambientDerivedSubgroup_le (E := M)
        rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
            (x : MF ⧸ H0.subgroupOf MF) with
          ⟨mMF, hmMFx⟩
        let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
        let mD : Dm := ⟨mM, by
          simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
        have hmD_MFD : mD ∈ MFD := by
          change (mD : M) ∈ MF.subgroupOf M
          simp [mD, mM, Subgroup.mem_subgroupOf]
        let mB : B := ⟨mD, hMFD_le_B hmD_MFD⟩
        have hmB_MFDsub : mB ∈ MFD.subgroupOf B := by
          simpa [MFD, Subgroup.mem_subgroupOf, mB] using hmD_MFD
        let mSub : MFD.subgroupOf B := ⟨mB, hmB_MFDsub⟩
        have hmRaw_eq :
            theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub) =
              mMF := by
          apply Subtype.ext
          rfl
        have hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
              H ⟨0, hqpos⟩ := by
          rw [hmRaw_eq, hmMFx]
          exact x.property
        rcases hQH1_apply mSub hmH1 with ⟨hmQH1, hcoord⟩
        let y : QH1 := ⟨QuotientGroup.mk' (A.subgroupOf B) mB, hmQH1⟩
        have hcoord_x : eH1 y = x := by
          calc
            eH1 y =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)),
                  hmH1⟩ := by
                    simpa [y, mSub] using hcoord
            _ = x := by
                    apply Subtype.ext
                    simpa [hmRaw_eq] using hmMFx
        have hk_eval :
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) = χbaseK x := by
          have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
            (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
              hsemi hprod
              (χbaseK.comp eH1.toMonoidHom)
              (k.2.comp eClam.toMonoidHom))
          calc
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
                (χbaseK.comp eH1.toMonoidHom) y := by
                  simpa [ψlin, χbaseK, y] using hcomp
            _ = χbaseK x := by
                  simp [MonoidHom.comp_apply, hcoord_x]
        have hu0W : u0 ∈ W := by
          change ((u0 : Dm) : M) ∈ U.subgroupOf M
          simp [Subgroup.mem_subgroupOf, hu0]
        have hconjMFD : Section2.conjBy u0 mD ∈ MFD :=
          hsemiTop.right_normalizes_left u0 hu0W mD hmD_MFD
        let mConjB : B := ⟨Section2.conjBy u0 mD, hMFD_le_B hconjMFD⟩
        have hmConjB_MFDsub : mConjB ∈ MFD.subgroupOf B := by
          simpa [MFD, Subgroup.mem_subgroupOf, mConjB] using hconjMFD
        let mConjSub : MFD.subgroupOf B := ⟨mConjB, hmConjB_MFDsub⟩
        rcases hρactionBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹))
            (uU⁻¹) rfl with
          ⟨hconjMF, haction⟩
        let xFromM : H ⟨0, hqpos⟩ :=
          ⟨QuotientGroup.mk' (H0.subgroupOf MF) mMF, by
            rw [hmMFx]
            exact x.property⟩
        have hxFromM : xFromM = x := by
          apply Subtype.ext
          exact hmMFx
        let conjMF : MF :=
          ⟨((uU : G) * (mMF : G) * (uU : G)⁻¹), by
            simpa using hconjMF mMF⟩
        have hsymm_apply :
            ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) =
              (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) := by
          simp [ρRange, f]
        have hact_x :
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
          have hact := haction mMF xFromM.property
          have hact' :
              (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) xFromM :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
            simpa [xFromM, conjMF, mul_assoc] using hact
          simpa [hxFromM] using hact'
        have hmConjRaw_eq :
            theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub) =
              conjMF := by
          apply Subtype.ext
          simp [mConjSub, mConjB, mD, mM, conjMF, Section2.conjBy,
            theorem_9_8_MFDSubgroupOf_to_MF_sec9, hu0, mul_assoc]
        have hconjCoord :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
              ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) := by
          calc
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
                QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
                  rw [hmConjRaw_eq]
            _ = (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                  MF ⧸ H0.subgroupOf MF) := hact_x.symm
            _ = ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) :=
                  hsymm_apply.symm
        have hmConjH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) ∈
              H ⟨0, hqpos⟩ := by
          rw [hconjCoord]
          exact ((ρRange (f uU)).symm x).property
        rcases hQH1_apply mConjSub hmConjH1 with
          ⟨hmConjQH1, hcoordConj⟩
        let yConj : QH1 :=
          ⟨QuotientGroup.mk' (A.subgroupOf B) mConjB, hmConjQH1⟩
        have hcoordConj_x : eH1 yConj = (ρRange (f uU)).symm x := by
          calc
            eH1 yConj =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)),
                  hmConjH1⟩ := by
                    simpa [yConj, mConjSub] using hcoordConj
            _ = (ρRange (f uU)).symm x := by
                    apply Subtype.ext
                    exact hconjCoord
        have hl_eval :
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
              χbaseAction x := by
          have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ yConj)
            (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
              hsemi hprod
              (χbaseL.comp eH1.toMonoidHom)
              (l.2.comp eClam.toMonoidHom))
          have hχapply := congrArg (fun φ : H ⟨0, hqpos⟩ →* ℂˣ => φ x)
            hχbase_action
          calc
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
                (χbaseL.comp eH1.toMonoidHom) yConj := by
                  simpa [ψlin, χbaseL, yConj] using hcomp
            _ = χbaseL ((ρRange (f uU)).symm x) := by
                  simp [MonoidHom.comp_apply, hcoordConj_x]
            _ = χbaseAction x := by
                  simpa [MonoidHom.comp_apply] using hχapply.symm
        have hconj_units :
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
              ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) := by
          apply Units.ext
          have hconj_val := congrFun hconj mB
          change
            ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) : ℂˣ) : ℂ) =
              ((ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) : ℂˣ) : ℂ)
          simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
            mConjB, mB, mD, Section2.conjBy, mul_assoc] using hconj_val
        exact congrArg Units.val (by
          calc
            (χbaseK x : ℂˣ) = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) :=
              hk_eval.symm
            _ = ψlin l (QuotientGroup.mk' (A.subgroupOf B) mConjB) := hconj_units
            _ = χbaseAction x := hl_eval)
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      apply e.injective
      apply Subtype.ext
      exact hχ
    have hlam_of_conj :
        ∀ (k l : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
          (((u0 : Dm) : M) : G) = (uU : G) →
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 →
          k.2 = (f uU • l).2 := by
      intro k l u0 uU hu0 hconj
      have hClamComm : IsMulCommutative Clam :=
        theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
          U C Uprime ρBase hUprimeEq
      have hf_surj : Function.Surjective f := by
        intro y
        rcases y with ⟨y, hy⟩
        rcases hy with ⟨x, rfl⟩
        rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
        exact ⟨u, rfl⟩
      haveI : IsCyclic ρBase.range := hρcycBase
      haveI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
      let σ0 : ρBase.range →* MulAut Clam :=
        kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
          simpa [Clam, Hsub, K, f] using hClamComm) hf_surj
      have hLamAction :
          f uU • l.2 = l.2.comp (σ0 (f uU)).toMonoidHom := by
        have hspec :=
          linearCharacterMulAction_spec_sec9
            (mulAutHomInvOfCommDomain_sec9 σ0) (f uU) l.2
        simpa [σ0, linearCharacterMulAction_sec9, mulAutHomInvOfCommDomain_sec9,
          Clam, Hsub, K, f] using hspec
      change k.2 = f uU • l.2
      rw [hLamAction]
      ext xK
      let wWB : ↥(W ⊓ B) := eWBK.symm xK
      let wB : B := ⟨(wWB : Dm), wWB.property.2⟩
      have hwB_mem : wB ∈ (W ⊓ B).subgroupOf B := by
        exact (Subgroup.mem_subgroupOf (H := W ⊓ B) (K := B)).mpr (by
          simp [wB])
      let wSub : (W ⊓ B).subgroupOf B := ⟨wB, hwB_mem⟩
      rcases hQClam_apply wSub with ⟨hwQClam, hwCoord⟩
      let y : QClam :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) wB, by
          simpa [wSub] using hwQClam⟩
      have hwSub_eq :
          (⟨((wSub : B) : Dm), by
              simpa [W, Subgroup.mem_subgroupOf] using wSub.property⟩ :
            ↥(W ⊓ B)) = wWB := by
        ext
        rfl
      have hy_coord :
          eClam y = QuotientGroup.mk' Hsub xK := by
        calc
          eClam y =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((wSub : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using wSub.property⟩ :
                    ↥(W ⊓ B))) := by
              simpa [y, wSub] using hwCoord
          _ = QuotientGroup.mk' Hsub xK := by
              simp [hwSub_eq, wWB]
      let χk : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
      let χl : H ⟨0, hqpos⟩ →* ℂˣ :=
        ((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
      have hk_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
            k.2 (QuotientGroup.mk' Hsub xK) := by
        have hcomp := congrArg (fun φ : QClam →* ℂˣ => φ y)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
            hsemi hprod
            (χk.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
              (k.2.comp eClam.toMonoidHom) y := by
                simpa [ψlin, χk, y] using hcomp
          _ = k.2 (QuotientGroup.mk' Hsub xK) := by
                simp [MonoidHom.comp_apply, hy_coord]
      have hu0W : u0 ∈ W := by
        change ((u0 : Dm) : M) ∈ U.subgroupOf M
        simp [Subgroup.mem_subgroupOf, hu0]
      let wConjB : B :=
        ⟨u0 * (wB : Dm) * u0⁻¹,
          hBnormal.conj_mem (wB : Dm) wB.property u0⟩
      have hwConjW : (wConjB : Dm) ∈ W := by
        have hwW : (wB : Dm) ∈ W := by
          simpa [wB] using wWB.property.1
        simpa [wConjB, mul_assoc] using
          W.mul_mem (W.mul_mem hu0W hwW) (W.inv_mem hu0W)
      let wConjWB : ↥(W ⊓ B) := ⟨(wConjB : Dm), ⟨hwConjW, wConjB.property⟩⟩
      have hwConjB_mem : wConjB ∈ (W ⊓ B).subgroupOf B := by
        simpa [wConjWB, Subgroup.mem_subgroupOf]
      let wConjSub : (W ⊓ B).subgroupOf B := ⟨wConjB, hwConjB_mem⟩
      rcases hQClam_apply wConjSub with ⟨hwConjQClam, hwConjCoord⟩
      let yConj : QClam :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) wConjB, by
          simpa [wConjSub] using hwConjQClam⟩
      have hwConjSub_eq :
          (⟨((wConjSub : B) : Dm), by
              simpa [W, Subgroup.mem_subgroupOf] using wConjSub.property⟩ :
            ↥(W ⊓ B)) = wConjWB := by
        ext
        rfl
      let xConjK : K :=
        ⟨uU * (xK : U) * uU⁻¹,
          (inferInstance : K.Normal).conj_mem (xK : U) xK.property uU⟩
      have hxK_compat :
          (((xK : K) : U) : G) = (((wWB : ↥(W ⊓ B)) : Dm) : M) := by
        simpa [wWB] using hWBK_compat wWB
      have hwConj_compat :
          ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) =
            (uU : G) * (((xK : K) : U) : G) * (uU : G)⁻¹ := by
        calc
          ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) =
              (((u0 : Dm) : M) : G) * ((((wWB : ↥(W ⊓ B)) : Dm) : M) : G) *
                (((u0 : Dm) : M) : G)⁻¹ := by
                simp [wConjWB, wConjB, wB, mul_assoc]
          _ = (uU : G) * (((xK : K) : U) : G) * (uU : G)⁻¹ := by
                simp [hu0, hxK_compat, mul_assoc]
      have heWBK_conj :
          eWBK wConjWB = xConjK := by
        apply Subtype.ext
        apply Subtype.ext
        calc
          (((eWBK wConjWB : K) : U) : G) =
              ((((wConjWB : ↥(W ⊓ B)) : Dm) : M) : G) := hWBK_compat wConjWB
          _ = (((xConjK : K) : U) : G) := by
                simpa [xConjK] using hwConj_compat
      have hσ0_apply :
          σ0 (f uU) (QuotientGroup.mk' Hsub xK) =
            QuotientGroup.mk' Hsub xConjK := by
        simpa [σ0, Clam, Hsub, K, f, xConjK] using
          kernelQuotientConjHomOfSurjective_apply_mk_sec9
            f (Uprime.subgroupOf U)
            (by simpa [Clam, Hsub, K, f] using hClamComm) hf_surj uU xK
      have hyConj_coord :
          eClam yConj = σ0 (f uU) (QuotientGroup.mk' Hsub xK) := by
        calc
          eClam yConj =
              QuotientGroup.mk' Hsub
                (eWBK
                  (⟨((wConjSub : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using wConjSub.property⟩ :
                    ↥(W ⊓ B))) := by
              simpa [yConj, wConjSub] using hwConjCoord
          _ = QuotientGroup.mk' Hsub (eWBK wConjWB) := by
              rw [hwConjSub_eq]
          _ = QuotientGroup.mk' Hsub xConjK := by
              rw [heWBK_conj]
          _ = σ0 (f uU) (QuotientGroup.mk' Hsub xK) := hσ0_apply.symm
      have hl_eval :
          ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) =
            l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := by
        have hcomp := congrArg (fun φ : QClam →* ℂˣ => φ yConj)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
            hsemi hprod
            (χl.comp eH1.toMonoidHom)
            (l.2.comp eClam.toMonoidHom))
        calc
          ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) =
              (l.2.comp eClam.toMonoidHom) yConj := by
                simpa [ψlin, χl, yConj] using hcomp
          _ = l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := by
                simp [MonoidHom.comp_apply, hyConj_coord]
      have hconj_units :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) =
            ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) := by
        apply Units.ext
        have hconj_val := congrFun hconj wB
        change
          ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) : ℂˣ) : ℂ) =
            ((ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) : ℂˣ) : ℂ)
        simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
          wConjB, wB, mul_assoc] using hconj_val
      exact congrArg Units.val (by
        calc
          k.2 (QuotientGroup.mk' Hsub xK) =
              ψlin k (QuotientGroup.mk' (A.subgroupOf B) wB) := hk_eval.symm
          _ = ψlin l (QuotientGroup.mk' (A.subgroupOf B) wConjB) := hconj_units
          _ = l.2 (σ0 (f uU) (QuotientGroup.mk' Hsub xK)) := hl_eval)
    intro k l hθeq
    rcases induced_eq_imp_conjugateOrbitConj_of_irreducible_sec9
        B (hψirr k) (hψirr l) hθeq with ⟨i, hi⟩
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    have hconjG :
        Section1.quotientCharacterInflation A B (ψlin k) =
          Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin l)) g := by
      simpa [Section1.conjugateOrbitConj] using hi
    rcases hsemiTop.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
    have hmB : m0 ∈ B := hMFD_le_B hm0
    have hconjU :
        Section1.quotientCharacterInflation A B (ψlin k) =
          Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin l)) u0 := by
      have hconjMU :
          Section1.quotientCharacterInflation A B (ψlin k) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) (m0 * u0) := by
        simpa [hg] using hconjG
      have herase :
          Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) (m0 * u0) =
            Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin l)) u0 :=
        conjugateOnNormal_mul_left_of_mem_sec9
          (Section1.quotientCharacterInflation A B (ψlin l)) (hsource_class l) hmB
      exact hconjMU.trans herase
    let uU : U := ⟨(((u0 : Dm) : M) : G), by
      have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
        simpa [W, Dm, Subgroup.mem_subgroupOf] using hu0
      simpa [Subgroup.mem_subgroupOf] using huUM⟩
    have hpair : k = f uU • l := by
      exact Prod.ext
        (hfirst_of_conj k l u0 uU rfl hconjU)
        (hlam_of_conj k l u0 uU rfl hconjU)
    rw [MulAction.orbitRel_apply]
    exact MulAction.mem_orbit_iff.mpr ⟨f uU, hpair.symm⟩
  intro k l hInd
  exact hinner_orbit k l (houter_to_inner k l (by simpa [Dm, A, ψlin] using hInd))


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq →
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  intro hstructure
  classical
  dsimp
    [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_data_sec9]
    at hstructure
  dsimp
    [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  let hClamComm : IsMulCommutative Clam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
      U C Uprime ρBase hUprimeEq
  let Lam : Type u := Clam →* ℂˣ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
    Subgroup.subtype ρBase.range
  let instFirstAction : MulAction ρBase.range (Fin (p - 1)) :=
    nonprincipalLinearCharacterIndexMulAction_sec9 p
      (hHcard ⟨0, hqpos⟩) ρRange
  letI : MulAction ρBase.range Lam := instLamAction
  letI : MulAction ρBase.range (Fin (p - 1)) := instFirstAction
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  rcases hstructure with
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex, hMFD_le_B,
      hBsemi, eWBK, hWBK_compat,
      QMF, QH1c, QH1, QClam, QH1CH1, hsemi, hprod, eH1, eClam,
      hQH1_apply, hQH1c_apply, hQClam_apply, hQMF_eq, hQMF_split_in_Q,
      hQH1_le_QMF⟩
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormal
  letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let ψlin : Fin (p - 1) × Lam → Q →* ℂˣ := fun k =>
    semidirectProductOfInternalDirectProductLinearCharacter_sec9
      hsemi hprod
      (((nonprincipalLinearCharacterEquivFin_sec9
            (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1.comp
        eH1.toMonoidHom)
      (k.2.comp eClam.toMonoidHom)
  have hpairStabilizer :
      ∀ k : Fin (p - 1) × Lam,
        MulAction.stabilizer ρBase.range k = ⊥ := by
    intro k
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_bot]
      rw [MulAction.mem_stabilizer_iff] at hx
      have hfirst : x • k.1 = k.1 := congrArg Prod.fst hx
      let ρRange : ρBase.range →* MulAut (H ⟨0, hqpos⟩) :=
        Subgroup.subtype ρBase.range
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      have hcharfixed :
          nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e k.1) =
            e k.1 := by
        apply Subtype.ext
        have hspec :=
          nonprincipalLinearCharacterIndexMulAction_spec_sec9
            p (hHcard ⟨0, hqpos⟩) ρRange x k.1
        have hleft : (e (x • k.1)).1 = (e k.1).1 :=
          congrArg Subtype.val (congrArg e hfirst)
        exact hspec.symm.trans hleft
      have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
        mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
          (hHcard ⟨0, hqpos⟩) (case_9_7_a_p_prime_sec9 hcase)
          (ρRange x) (e k.1) hcharfixed
      exact Subtype.ext hxval
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [MulAction.mem_stabilizer_iff]
      simp [hx]
  have hψlin_injective : Function.Injective ψlin := by
    intro k l hkl
    let χk : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χl : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) l.1).1
    let ηk : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    let ηl : QClam →* ℂˣ := l.2.comp eClam.toMonoidHom
    have hχ : χk = χl := by
      ext x
      let y : QH1 := eH1.symm x
      have hleft_k := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod (χk.comp eH1.toMonoidHom) ηk)
      have hleft_l := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod (χl.comp eH1.toMonoidHom) ηl)
      have hval := congrArg (fun φ : Q →* ℂˣ => φ (y : Q)) hkl
      change ((χk x : ℂˣ) : ℂ) = ((χl x : ℂˣ) : ℂ)
      calc
        ((χk x : ℂˣ) : ℂ) = (((ψlin k) (y : Q) : ℂˣ) : ℂ) := by
          simpa [ψlin, χk, ηk, y] using congrArg Units.val hleft_k.symm
        _ = (((ψlin l) (y : Q) : ℂˣ) : ℂ) := congrArg Units.val hval
        _ = ((χl x : ℂˣ) : ℂ) := by
          simpa [ψlin, χl, ηl, y] using congrArg Units.val hleft_l
    have hfst : k.1 = l.1 := by
      let e := nonprincipalLinearCharacterEquivFin_sec9
        (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
      apply e.injective
      apply Subtype.ext
      exact hχ
    have hη : k.2 = l.2 := by
      ext x
      let y : QClam := eClam.symm x
      have hright_k := congrArg (fun φ : QClam →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
          hsemi hprod (χk.comp eH1.toMonoidHom) ηk)
      have hright_l := congrArg (fun φ : QClam →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_right_sec9
          hsemi hprod (χl.comp eH1.toMonoidHom) ηl)
      have hval := congrArg (fun φ : Q →* ℂˣ => φ (y : Q)) hkl
      change ((k.2 x : ℂˣ) : ℂ) = ((l.2 x : ℂˣ) : ℂ)
      calc
        ((k.2 x : ℂˣ) : ℂ) = (((ψlin k) (y : Q) : ℂˣ) : ℂ) := by
          simpa [ψlin, χk, ηk, y] using congrArg Units.val hright_k.symm
        _ = (((ψlin l) (y : Q) : ℂˣ) : ℂ) := congrArg Units.val hval
        _ = ((l.2 x : ℂˣ) : ℂ) := by
          simpa [ψlin, χl, ηl, y] using congrArg Units.val hright_l
    exact Prod.ext hfst hη
  have hMFDnormal : MFD.Normal := by
    simpa [MFD, Dm] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hsemiTop :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
    simpa [MFD, W, Dm] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase) hMFDnormal
  have hfirst_free :
      ∀ (x : ρBase.range) (i : Fin (p - 1)), x • i = i → x = 1 := by
    intro x i hfirst
    let e := nonprincipalLinearCharacterEquivFin_sec9
      (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
    have hcharfixed :
        nonprincipalLinearCharacterDualEquiv_sec9 (ρRange x) (e i) = e i := by
      apply Subtype.ext
      have hspec :=
        nonprincipalLinearCharacterIndexMulAction_spec_sec9
          p (hHcard ⟨0, hqpos⟩) ρRange x i
      have hleft : (e (x • i)).1 = (e i).1 :=
        congrArg Subtype.val (congrArg e hfirst)
      exact hspec.symm.trans hleft
    have hxval : (x : MulAut (H ⟨0, hqpos⟩)) = 1 :=
      mulAut_eq_one_of_nonprincipalLinearCharacterDualEquiv_eq_self_sec9
        (hHcard ⟨0, hqpos⟩) (case_9_7_a_p_prime_sec9 hcase)
        (ρRange x) (e i) hcharfixed
    exact Subtype.ext hxval
  have hψlin_first_fixed_of_conjugate :
      ∀ (k : Fin (p - 1) × Lam) (u0 : Dm) (uU : U),
        (((u0 : Dm) : M) : G) = (uU : G) →
        Section1.conjugateOnNormal B
            (Section1.quotientCharacterInflation A B (ψlin k)) u0 =
          Section1.quotientCharacterInflation A B (ψlin k) →
        f uU • k.1 = k.1 := by
    intro k u0 uU hu0 hfix
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χbase' : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) (f uU • k.1)).1
    have hχbase_action :
        χbase' = χbase.comp (ρRange (f uU)).symm.toMonoidHom := by
      simpa [χbase, χbase', ρRange, instFirstAction] using
        nonprincipalLinearCharacterIndexMulAction_spec_sec9
          p (hHcard ⟨0, hqpos⟩) ρRange (f uU) k.1
    have hχ : χbase' = χbase := by
      ext x
      have hMFleD : MF ≤ ambientDerivedSubgroup M :=
        MF_le_ambientDerived_of_hypothesis_9_2_sec9
          M MF U W1 W2 q (case_9_7_a_hypothesis_9_2_sec9 hcase)
      have hDleM : ambientDerivedSubgroup M ≤ M :=
        section12_ambientDerivedSubgroup_le (E := M)
      rcases QuotientGroup.mk'_surjective (H0.subgroupOf MF)
          (x : MF ⧸ H0.subgroupOf MF) with
        ⟨mMF, hmMFx⟩
      let mM : M := ⟨(mMF : G), hDleM (hMFleD mMF.property)⟩
      let mD : Dm := ⟨mM, by
        simpa [Dm, Subgroup.mem_subgroupOf, mM] using hMFleD mMF.property⟩
      have hmD_MFD : mD ∈ MFD := by
        change (mD : M) ∈ MF.subgroupOf M
        simp [mD, mM, Subgroup.mem_subgroupOf]
      let mB : B := ⟨mD, hMFD_le_B hmD_MFD⟩
      have hmB_MFDsub : mB ∈ MFD.subgroupOf B := by
        simpa [MFD, Subgroup.mem_subgroupOf, mB] using hmD_MFD
      let mSub : MFD.subgroupOf B := ⟨mB, hmB_MFDsub⟩
      have hmRaw_eq :
          theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
              ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub) =
            mMF := by
        apply Subtype.ext
        rfl
      have hmH1 :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)) ∈
            H ⟨0, hqpos⟩ := by
        rw [hmRaw_eq, hmMFx]
        exact x.property
      rcases hQH1_apply mSub hmH1 with ⟨hmQH1, hcoord⟩
      let y : QH1 := ⟨QuotientGroup.mk' (A.subgroupOf B) mB, hmQH1⟩
      have hcoord_x : eH1 y = x := by
        calc
          eH1 y =
              ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mSub)),
                hmH1⟩ := by
                  simpa [y, mSub] using hcoord
          _ = x := by
                  apply Subtype.ext
                  simpa [hmRaw_eq] using hmMFx
      have hright_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) = χbase x := by
        have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
            hsemi hprod
            (χbase.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) =
              (χbase.comp eH1.toMonoidHom) y := by
                simpa [ψlin, χbase, y] using hcomp
          _ = χbase x := by
                simp [MonoidHom.comp_apply, hcoord_x]
      have hu0W : u0 ∈ W := by
        change ((u0 : Dm) : M) ∈ U.subgroupOf M
        simp [Subgroup.mem_subgroupOf, hu0]
      have hconjMFD : Section2.conjBy u0 mD ∈ MFD :=
        hsemiTop.right_normalizes_left u0 hu0W mD hmD_MFD
      let mConjB : B := ⟨Section2.conjBy u0 mD, hMFD_le_B hconjMFD⟩
      have hmConjB_MFDsub : mConjB ∈ MFD.subgroupOf B := by
        simpa [MFD, Subgroup.mem_subgroupOf, mConjB] using hconjMFD
      let mConjSub : MFD.subgroupOf B := ⟨mConjB, hmConjB_MFDsub⟩
      rcases hρactionBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹))
          (uU⁻¹) rfl with
        ⟨hconjMF, haction⟩
      let xFromM : H ⟨0, hqpos⟩ :=
        ⟨QuotientGroup.mk' (H0.subgroupOf MF) mMF, by
          rw [hmMFx]
          exact x.property⟩
      have hxFromM : xFromM = x := by
        apply Subtype.ext
        exact hmMFx
      let conjMF : MF :=
        ⟨((uU : G) * (mMF : G) * (uU : G)⁻¹), by
          simpa using hconjMF mMF⟩
      have hsymm_apply :
          ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) =
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
              MF ⧸ H0.subgroupOf MF) := by
        simp [ρRange, f]
      have hact_x :
          (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
              MF ⧸ H0.subgroupOf MF) =
            QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
        have hact := haction mMF xFromM.property
        have hact' :
            (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) xFromM :
                MF ⧸ H0.subgroupOf MF) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
          simpa [xFromM, conjMF, mul_assoc] using hact
        simpa [hxFromM] using hact'
      have hmConjRaw_eq :
          theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
              ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub) =
            conjMF := by
        apply Subtype.ext
        simp [mConjSub, mConjB, mD, mM, conjMF, Section2.conjBy,
          theorem_9_8_MFDSubgroupOf_to_MF_sec9, hu0, mul_assoc]
      have hconjCoord :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
            ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) := by
        calc
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) =
              QuotientGroup.mk' (H0.subgroupOf MF) conjMF := by
                rw [hmConjRaw_eq]
          _ = (ρBase (QuotientGroup.mk' (C.subgroupOf U) (uU⁻¹)) x :
                MF ⧸ H0.subgroupOf MF) := hact_x.symm
          _ = ((ρRange (f uU)).symm x : MF ⧸ H0.subgroupOf MF) :=
                hsymm_apply.symm
      have hmConjH1 :
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)) ∈
            H ⟨0, hqpos⟩ := by
        rw [hconjCoord]
        exact ((ρRange (f uU)).symm x).property
      rcases hQH1_apply mConjSub hmConjH1 with
        ⟨hmConjQH1, hcoordConj⟩
      let yConj : QH1 :=
        ⟨QuotientGroup.mk' (A.subgroupOf B) mConjB, hmConjQH1⟩
      have hcoordConj_x : eH1 yConj = (ρRange (f uU)).symm x := by
        calc
          eH1 yConj =
              ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                  (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                    ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) mConjSub)),
                hmConjH1⟩ := by
                  simpa [yConj, mConjSub] using hcoordConj
          _ = (ρRange (f uU)).symm x := by
                  apply Subtype.ext
                  exact hconjCoord
      have hleft_eval :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) = χbase' x := by
        have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ yConj)
          (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
            hsemi hprod
            (χbase.comp eH1.toMonoidHom)
            (k.2.comp eClam.toMonoidHom))
        have hχapply := congrArg (fun φ : H ⟨0, hqpos⟩ →* ℂˣ => φ x)
          hχbase_action
        calc
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
              (χbase.comp eH1.toMonoidHom) yConj := by
                simpa [ψlin, χbase, yConj] using hcomp
          _ = χbase ((ρRange (f uU)).symm x) := by
                simp [MonoidHom.comp_apply, hcoordConj_x]
          _ = χbase' x := by
                simpa [MonoidHom.comp_apply] using hχapply.symm
      have hfix_units :
          ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) =
            ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) := by
        apply Units.ext
        have hfix_val := congrFun hfix mB
        change
          ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) : ℂˣ) : ℂ) =
            ((ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) : ℂˣ) : ℂ)
        simpa [Section1.conjugateOnNormal, Section1.quotientCharacterInflation,
          mConjB, mB, mD, Section2.conjBy, mul_assoc] using hfix_val
      exact congrArg Units.val (by
        calc
          (χbase' x : ℂˣ) = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mConjB) :=
            hleft_eval.symm
          _ = ψlin k (QuotientGroup.mk' (A.subgroupOf B) mB) := hfix_units
          _ = χbase x := hright_eval)
    let e := nonprincipalLinearCharacterEquivFin_sec9
      (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)
    apply e.injective
    apply Subtype.ext
    exact hχ
  have hIeq :
      ∀ k : Fin (p - 1) × Lam,
        Section1.inertiaSubgroup B
          (Section1.quotientCharacterInflation A B (ψlin k)) = B := by
    intro k
    have hI_le_B :
        Section1.inertiaSubgroup B
            (Section1.quotientCharacterInflation A B (ψlin k)) ≤ B := by
      intro g hgI
      rcases hsemiTop.mul_surjective g (by trivial) with ⟨m0, hm0, u0, hu0, hg⟩
      have hmB : m0 ∈ B := hMFD_le_B hm0
      let uU : U := ⟨(((u0 : Dm) : M) : G), by
        have huUM : ((u0 : Dm) : M) ∈ U.subgroupOf M := by
          simpa [W, Dm, Subgroup.mem_subgroupOf] using hu0
        simpa [Subgroup.mem_subgroupOf] using huUM⟩
      have hu_fix :
          Section1.conjugateOnNormal B
              (Section1.quotientCharacterInflation A B (ψlin k)) u0 =
            Section1.quotientCharacterInflation A B (ψlin k) := by
        have hgfix :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) g =
              Section1.quotientCharacterInflation A B (ψlin k) := by
          simpa [Section1.inertiaSubgroup] using hgI
        have hmulfix :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) (m0 * u0) =
              Section1.quotientCharacterInflation A B (ψlin k) := by
          simpa [hg] using hgfix
        have herase :
            Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) (m0 * u0) =
              Section1.conjugateOnNormal B
                (Section1.quotientCharacterInflation A B (ψlin k)) u0 :=
          conjugateOnNormal_mul_left_of_mem_sec9
            (Section1.quotientCharacterInflation A B (ψlin k))
            (Section1.quotientCharacterInflation_isClassFunction A B (ψlin k)) hmB
        exact herase.symm.trans hmulfix
      have hxone : f uU = 1 := by
        exact hfirst_free (f uU) k.1
          (hψlin_first_fixed_of_conjugate k u0 uU (by rfl) hu_fix)
      have huK : uU ∈ K := by
        simpa [K, MonoidHom.mem_ker] using hxone
      let uK : K := ⟨uU, huK⟩
      let WB : Subgroup Dm := W ⊓ B
      let wB : WB := eWBK.symm uK
      have hwG :
          ((((wB : WB) : Dm) : M) : G) = (uU : G) := by
        have hcompat := hWBK_compat wB
        have hval : (((eWBK wB : K) : U) : G) = (uU : G) := by
          simp [wB, uK]
        exact hcompat.symm.trans hval
      have hu0_eq_wB : u0 = (wB : Dm) := by
        apply Subtype.ext
        apply Subtype.ext
        simpa [uU] using hwG.symm
      have huB : u0 ∈ B := by
        rw [hu0_eq_wB]
        exact wB.property.2
      rw [hg]
      exact B.mul_mem hmB huB
    refine le_antisymm hI_le_B ?_
    exact Section1.proposition_1_7_inertia_contains_H (H := B)
      (theta := Section1.quotientCharacterInflation A B (ψlin k))
      (hclass := Section1.quotientCharacterInflation_isClassFunction A B (ψlin k))
  have hθnotMF :
      ∀ k : Fin (p - 1) × Lam,
        ¬ Section1.subgroupInKernel'
          (Section1.inducedCF B
            (Section1.quotientCharacterInflation A B (ψlin k))) MFD := by
    intro k hkerMFD
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hψirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) :=
      Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        A B (ψlin k)
    have hsrcKer :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFD.subgroupOf B) :=
      subgroupInKernel'_of_inducedCF_sec9 B MFD hMFD_le_B hψirr hkerMFD
    have hχbase_ne : χbase ≠ 1 := by
      simpa [χbase] using
        ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).2
    apply hχbase_ne
    ext x
    let y : QH1 := eH1.symm x
    have hyQMF : (y : Q) ∈ QMF :=
      hQH1_le_QMF y.property
    have hyQMF' :
        (y : Q) ∈
          ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) := by
      simpa [hQMF_eq] using hyQMF
    rcases hyQMF' with ⟨m, hmMFD, hmy⟩
    have hmker := hsrcKer ⟨m, hmMFD⟩
    have hψm : ((ψlin k) (QuotientGroup.mk' (A.subgroupOf B) m) : ℂ) = 1 := by
      rw [Section1.quotientCharacterInflation_degree] at hmker
      simpa [Section1.quotientCharacterInflation] using hmker
    have hψy : ((ψlin k) (y : Q) : ℂ) = 1 := by
      simpa [hmy] using hψm
    have hrestrict :
        ψlin k (y : Q) = χQH1 y := by
      have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod χQH1 ηQClam)
      simpa [ψlin, χQH1, ηQClam, χbase] using hcomp
    have hyval : ((χQH1 y) : ℂ) = 1 := by
      simpa [hrestrict] using hψy
    simpa [χQH1, y] using hyval
  refine
    ⟨B, hBnormal, hAnormal, hA_le_B, hBindex,
      QH1c, QH1, QClam, QH1CH1, hsemi, hprod, eH1, eClam, ?_, ?_, ?_, ?_⟩
  · exact hIeq
  · intro k hkerMFD
    let χbase : H ⟨0, hqpos⟩ →* ℂˣ :=
      ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).1
    let χQH1 : QH1 →* ℂˣ := χbase.comp eH1.toMonoidHom
    let ηQClam : QClam →* ℂˣ := k.2.comp eClam.toMonoidHom
    have hψirr :
        Section1.IsIrreducibleCharacterOnGroup
          (Section1.quotientCharacterInflation A B (ψlin k)) :=
      Section1.quotientCharacterInflation_isIrreducibleCharacterOnGroup
        A B (ψlin k)
    have hsrcKer :
        Section1.subgroupInKernel'
          (Section1.quotientCharacterInflation A B (ψlin k))
          (MFD.subgroupOf B) :=
      subgroupInKernel'_of_inducedCF_sec9 B MFD hMFD_le_B hψirr hkerMFD
    have hχbase_ne : χbase ≠ 1 := by
      simpa [χbase] using
        ((nonprincipalLinearCharacterEquivFin_sec9
          (H ⟨0, hqpos⟩) p (hHcard ⟨0, hqpos⟩)) k.1).2
    apply hχbase_ne
    ext x
    let y : QH1 := eH1.symm x
    have hyQMF : (y : Q) ∈ QMF :=
      hQH1_le_QMF y.property
    have hyQMF' :
        (y : Q) ∈
          ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) := by
      simpa [hQMF_eq] using hyQMF
    rcases hyQMF' with ⟨m, hmMFD, hmy⟩
    have hmker := hsrcKer ⟨m, hmMFD⟩
    have hψm : ((ψlin k) (QuotientGroup.mk' (A.subgroupOf B) m) : ℂ) = 1 := by
      rw [Section1.quotientCharacterInflation_degree] at hmker
      simpa [Section1.quotientCharacterInflation] using hmker
    have hψy : ((ψlin k) (y : Q) : ℂ) = 1 := by
      simpa [hmy] using hψm
    have hrestrict :
        ψlin k (y : Q) = χQH1 y := by
      have hcomp := congrArg (fun φ : QH1 →* ℂˣ => φ y)
        (semidirectProductOfInternalDirectProductLinearCharacter_comp_left_sec9
          hsemi hprod χQH1 ηQClam)
      simpa [ψlin, χQH1, ηQClam, χbase] using hcomp
    have hyval : ((χQH1 y) : ℂ) = 1 := by
      simpa [hrestrict] using hψy
    simpa [χQH1, y] using hyval
  ·
    intro k
    exact
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_irr_Xtheta_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        (H0 := H0) (C := C) (Uprime := Uprime)
        (p := p) (q := q) (a := a) (u := u)
        (H := H) (hqpos := hqpos) (hHcard := hHcard)
        (hHnorm := hHnorm) (hHindep := hHindep) (hHsup := hHsup)
        (ρBase := ρBase) (hρcycBase := hρcycBase)
        (_hρcardBase := hρcardBase) (_hρactionBase := hρactionBase)
        (_hρkerBase := hρkerBase) (hconjBase := hconjBase)
        (hcase := hcase) (_hBarU := hBarU) (hUprimeEq := hUprimeEq)
        (B := B) (hBnormal := hBnormal) (hAnormal := hAnormal)
        (_hA_le_B := hA_le_B) (_hMFD_le_B := hMFD_le_B) (hBsemi := hBsemi)
        (eWBK := eWBK) (_hWBK_compat := hWBK_compat)
        (QH1c := QH1c) (QH1 := QH1) (QClam := QClam)
        (QH1CH1 := QH1CH1) (hsemi := hsemi) (hprod := hprod)
        (eH1 := eH1) (eClam := eClam)
        (_hQH1_apply := hQH1_apply) (_hQH1c_apply := hQH1c_apply)
        (_hQClam_apply := hQClam_apply)
        (QMF := QMF) (_hQMF_eq := hQMF_eq)
        (_hQMF_split_in_Q := hQMF_split_in_Q) (_hQH1_le_QMF := hQH1_le_QMF)
        (_hIeq := hIeq) (_hθnotMF := hθnotMF) k
  ·
    intro k l hInd
    exact
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_inj_Xtheta_core_sec9
        (M := M) (MF := MF) (U := U) (W1 := W1) (W2 := W2)
        (H0 := H0) (C := C) (Uprime := Uprime)
        (p := p) (q := q) (a := a) (u := u)
        (H := H) (hqpos := hqpos) (hHcard := hHcard)
        (hHnorm := hHnorm) (hHindep := hHindep) (hHsup := hHsup)
        (ρBase := ρBase) (hρcycBase := hρcycBase)
        (_hρcardBase := hρcardBase) (hρactionBase := hρactionBase)
        (_hρkerBase := hρkerBase) (hconjBase := hconjBase)
        (hcase := hcase) (_hBarU := hBarU) (hUprimeEq := hUprimeEq)
        (B := B) (hBnormal := hBnormal) (hAnormal := hAnormal)
        (_hMFD_le_B := hMFD_le_B) (hBsemi := hBsemi)
        (eWBK := eWBK) (_hWBK_compat := hWBK_compat)
        (QH1c := QH1c) (QH1 := QH1) (QClam := QClam)
          (QH1CH1 := QH1CH1) (hsemi := hsemi) (hprod := hprod)
          (eH1 := eH1) (eClam := eClam)
          (_hQH1_apply := hQH1_apply) (_hQH1c_apply := hQH1c_apply)
          (_hQClam_apply := hQClam_apply) (_hIeq := hIeq)
          (_hθnotMF := hθnotMF)
          (_hψlin_injective := hψlin_injective)
        (_hpairStabilizer := hpairStabilizer) k l hInd

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_character_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_data_of_semidirect_product_formula_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_formula_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_data_of_quotient_linear_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_quotient_linear_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype) :
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  exact
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_of_semidirect_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq
      (theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq)

set_option maxHeartbeats 800000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (hρcycBase : IsCyclic ρBase.range)
    (hρcardBase : Nat.card ρBase.range = a)
    (hρactionBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
          ∃ hconjMF : ∀ h : MF, (u : G)⁻¹ * (h : G) * (u : G) ∈ MF,
            ∀ h : MF,
            ∀ hhQ : QuotientGroup.mk' (H0.subgroupOf MF) h ∈ H ⟨0, hqpos⟩,
              (ρBase x ⟨QuotientGroup.mk' (H0.subgroupOf MF) h, hhQ⟩ :
                  MF ⧸ H0.subgroupOf MF) =
                QuotientGroup.mk' (H0.subgroupOf MF)
                  ⟨(u : G)⁻¹ * (h : G) * (u : G), hconjMF h⟩)
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        ∀ hUprimeEq : Uprime = (_root_.commutator U).map U.subtype,
          theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9
            M MF U H0 C Uprime p q a H hqpos hHcard ρBase hUprimeEq := by
  -- the base `U -> rhoBase.range` action, quotiented by `U'`.
  -- `def_Itheta` for this concrete quotient.
  intro hcase hBarU hUprimeEq
  classical
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_data_sec9]
  let f : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  let K : Subgroup U := f.ker
  let hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  let Clam : Type u := K ⧸ Hsub
  letI : Group Clam := inferInstance
  letI : Fintype Clam := Fintype.ofFinite Clam
  letI : DecidableEq Clam := Classical.decEq Clam
  letI : Finite Clam := Finite.of_fintype Clam
  have hClamComm : IsMulCommutative Clam := by
    simpa [Clam, Hsub, K, f] using
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_comm_sec9
        U C Uprime ρBase hUprimeEq
  letI : IsMulCommutative Clam := hClamComm
  letI : CommGroup Clam := IsMulCommutative.instCommGroup
  haveI : HasEnoughRootsOfUnity ℂ (Monoid.exponent Clam) :=
    Section1.complex_hasEnoughRootsOfUnity (Monoid.exponent Clam)
  let Lam : Type u := Clam →* ℂˣ
  let instFintypeLam : Fintype Lam := Fintype.ofFinite Lam
  let instDecidableEqLam : DecidableEq Lam := Classical.decEq Lam
  letI : Fintype Lam := instFintypeLam
  letI : DecidableEq Lam := instDecidableEqLam
  let lam : Lam → Clam →* ℂˣ := fun χ => χ
  have hlaminj : Function.Injective lam := by
    intro χ η hχη
    exact hχη
  have hLamClamcard : Fintype.card Lam = Fintype.card Clam := by
    change Fintype.card (Clam →* ℂˣ) = Fintype.card Clam
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity Clam ℂ
  have hlamdata :
      ∀ j : Lam,
        Section1.IsIrreducibleCharacterOnGroup
          (fun x : Clam => (lam j x : ℂ)) ∧
        Section1.degree (fun x : Clam => (lam j x : ℂ)) = 1 := by
    intro χ
    constructor
    · change Section1.IsIrreducibleCharacterOnGroup
        (Section1.characterInflationByHom (MonoidHom.id Clam) χ)
      exact Section1.characterInflationByHom_isIrreducibleCharacterOnGroup
        (MonoidHom.id Clam) χ
    · simpa [lam] using Section1.linearCharacter_degree χ
  have hf_surj : Function.Surjective f := by
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u, rfl⟩
    exact ⟨u, rfl⟩
  letI : IsCyclic ρBase.range := hρcycBase
  letI : IsMulCommutative ρBase.range := IsCyclic.isMulCommutative
  let σ : ρBase.range →* MulAut Clam :=
    mulAutHomInvOfCommDomain_sec9
      (kernelQuotientConjHomOfSurjective_sec9 f (Uprime.subgroupOf U) (by
        simpa [Clam, Hsub, K, f] using hClamComm) hf_surj)
  let instLamAction : MulAction ρBase.range Lam :=
    linearCharacterMulAction_sec9 σ
  have htail :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9
        M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq
  dsimp [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_tail_data_sec9]
    at htail
  exact ⟨Lam, instFintypeLam, instDecidableEqLam, lam, hlaminj, hLamClamcard,
    hlamdata, instLamAction, by
      simpa [f, K, Hsub, Clam, Lam, σ, instLamAction] using htail⟩

public theorem theorem_9_8_initial_constituent_Mtheta_free_action_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
            M MF U H0 Uprime p a := by
  -- `[set~ 0] × Iirr Clam`, its order is `a`, and quotienting gives the
  -- induced `M'` constituents of degree `a`.
  intro hcase hBarU hUprime
  haveI : NeZero a :=
    ⟨Nat.ne_of_gt
      (case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase)⟩
  rcases case_9_7_a_component_decomposition_sec9 hcase with
    ⟨hnormalH0, H, hHcard, hHnorm, hHindep, hHsup, hfac, hconj⟩
  rcases hconj with ⟨hqpos, hconjBase⟩
  rcases hfac ⟨0, hqpos⟩ with
    ⟨hnormalC, ρBase, hρcycBase, hρcardBase, hρactionBase, hρkerBase⟩
  rcases case_9_7_a_quotient_isElementaryAbelian_sec9 hcase with
    ⟨_hnormalH0_case, hquotElem⟩
  letI : (H0.subgroupOf MF).Normal := hnormalH0
  letI : (C.subgroupOf U).Normal := hnormalC
  letI : IsElementaryAbelian p (MF ⧸ H0.subgroupOf MF) := hquotElem
  haveI : IsMulCommutative (MF ⧸ H0.subgroupOf MF) := inferInstance
  have hclam :=
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprime
  have hindex :=
    theorem_9_8_initial_constituent_Mtheta_clam_index_action_data_of_clam_kernel_quotient_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hρcardBase
      hUprime hclam
  have hrawTheta :=
    theorem_9_8_initial_constituent_Mtheta_clam_raw_theta_data_of_clam_index_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase
      (case_9_7_a_p_prime_sec9 hcase) hindex
  have hparam :=
    theorem_9_8_initial_constituent_Mtheta_clam_parameter_data_of_clam_raw_theta_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hrawTheta
  have hrange :=
    theorem_9_8_initial_constituent_Mtheta_base_range_action_data_of_clam_parameter_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hparam
  have habstract :=
    theorem_9_8_initial_constituent_Mtheta_abstract_cyclic_action_data_of_base_range_action_data_sec9
      M MF U H0 C Uprime p q a H hqpos ρBase hρcycBase hρcardBase hrange
  have hcyclic :=
    theorem_9_8_initial_constituent_Mtheta_cyclic_action_data_of_abstract_cyclic_action_data_sec9
      M MF U H0 Uprime p a habstract
  exact theorem_9_8_initial_constituent_Mtheta_free_action_data_of_cyclic_action_data_sec9
    M MF U H0 Uprime p a hcyclic

public theorem theorem_9_8_initial_degree_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
            (theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U).card ≥
              ((p - 1) / a) * (Nat.card U / (a * Nat.card Uprime)) := by
  -- `S(H0U')`.  The witness-level theorem below only unpacks this count
  -- through `kernelInducedFamily`.
  intro hcase hBarU hUprime hSH0U
  have hfree :
      theorem_9_8_initial_constituent_Mtheta_free_action_data_sec9
        M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_free_action_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u hcase hBarU hUprime
  have hraw :
      theorem_9_8_initial_constituent_Mtheta_raw_product_data_sec9
        M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_raw_product_data_of_free_action_data_sec9
      M MF U H0 Uprime p a hfree
  have hmtheta :
      theorem_9_8_initial_constituent_Mtheta_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_Mtheta_data_of_raw_product_data_sec9
      M MF U H0 Uprime p a hraw
  have horbit :
      theorem_9_8_initial_constituent_orbit_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_orbit_data_of_Mtheta_data_sec9
      M MF U H0 Uprime p a (case_9_7_a_index_dvd_p_minus_one_sec9 hcase) hmtheta
  have hfamily :
      theorem_9_8_initial_constituent_family_data_sec9 M MF U H0 Uprime p a :=
    theorem_9_8_initial_constituent_family_data_of_orbit_data_sec9
      M MF U H0 Uprime p a
      (case_9_7_a_index_a_pos_sec9 M MF U W1 W2 H0 C p q a hcase)
      horbit
  exact theorem_9_8_initial_degree_count_of_constituent_family_data_sec9
    M MF U W1 W2 H0 Uprime p q a SH0U
    (case_9_7_a_hypothesis_9_2_sec9 hcase) hSH0U hfamily

public theorem theorem_9_8_initial_constituent_witness_count_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ)
    (SH0U : Finset (Section1.ClassFunction M)) :
    case_9_7_a_data M MF U W1 W2 H0 C p q a →
      quotientBarUCardinality U C u →
        Uprime = (_root_.commutator U).map U.subtype →
          kernelInducedFamily M (ambientDerivedSubgroup M) MF (H0 ⊔ Uprime) SH0U →
            ∃ I : Finset (Section1.ClassFunction M),
              I ⊆ SH0U ∧
                I.card ≥ ((p - 1) / a) *
                  (Nat.card U / (a * Nat.card Uprime)) ∧
                ∀ χ : Section1.ClassFunction M, χ ∈ I →
                  Section1.IsIrreducibleCharacterOnGroup χ ∧
                    ∃ θ : Section1.ClassFunction
                        ((ambientDerivedSubgroup M).subgroupOf M),
                      Section1.IsIrreducibleCharacterOnGroup θ ∧
                        ¬ Section1.subgroupInKernel' θ
                          ((MF.subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        Section1.subgroupInKernel' θ
                          (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                            ((ambientDerivedSubgroup M).subgroupOf M)) ∧
                        χ = Section1.inducedCF
                          ((ambientDerivedSubgroup M).subgroupOf M) θ ∧
                        Section1.degree θ = (a : ℂ) := by
  intro hcase hBarU hUprime hSH0U
  classical
  let I : Finset (Section1.ClassFunction M) :=
    theorem_9_8_initial_degree_subfamily_sec9 M q a SH0U
  have hIcard :
      I.card ≥ ((p - 1) / a) *
        (Nat.card U / (a * Nat.card Uprime)) := by
    simpa [I] using
      theorem_9_8_initial_degree_count_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u SH0U hcase hBarU hUprime hSH0U
  have hDindex :
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q hcase.1
  refine ⟨I, ?_, hIcard, ?_⟩
  · intro χ hχI
    have hχdata :
        χ ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            Section1.degree χ = (q * a : ℂ) := by
      simpa [I, theorem_9_8_initial_degree_subfamily_sec9] using hχI
    exact hχdata.1
  · intro χ hχI
    have hχdata :
        χ ∈ SH0U ∧
          Section1.IsIrreducibleCharacterOnGroup χ ∧
            Section1.degree χ = (q * a : ℂ) := by
      simpa [I, theorem_9_8_initial_degree_subfamily_sec9] using hχI
    rcases hχdata with ⟨hχSH0U, hχirr, hχdegree⟩
    rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
    rcases (hmem χ).mp hχSH0U with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
    refine ⟨hχirr, θ, hθirr, hθnot, hθker, hχeq, ?_⟩
    have hq_ne : (q : ℂ) ≠ 0 := by
      exact_mod_cast (case_9_7_a_q_prime_sec9 hcase).ne_zero
    have hmul :
        (q : ℂ) * Section1.degree θ = (q : ℂ) * (a : ℂ) := by
      calc
        (q : ℂ) * Section1.degree θ =
            Section1.degree
              (Section1.inducedCF ((ambientDerivedSubgroup M).subgroupOf M) θ) := by
          rw [Section1.degree_inducedClassFunction, hDindex]
        _ = Section1.degree χ := by
          rw [← hχeq]
        _ = (q * a : ℂ) := hχdegree
        _ = (q : ℂ) * (a : ℂ) := by
          norm_num [Nat.cast_mul]
    exact mul_left_cancel₀ hq_ne hmul


public theorem theorem_9_8_initial_constituent_degree_count_source_bridge_sec9
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
                ∃ I : Finset (Section1.ClassFunction M),
                  I ⊆ SH0U ∧
                    I.card ≥ ((p - 1) / a) *
                      (Nat.card U / (a * Nat.card Uprime)) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ I →
                      Section1.IsIrreducibleCharacterOnGroup χ ∧
                        ∀ θ : Section1.ClassFunction
                            ((ambientDerivedSubgroup M).subgroupOf M),
                          Section1.IsIrreducibleCharacterOnGroup θ →
                            ¬ Section1.subgroupInKernel' θ
                              ((MF.subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) →
                            Section1.subgroupInKernel' θ
                              (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
                                ((ambientDerivedSubgroup M).subgroupOf M)) →
                            χ = Section1.inducedCF
                              ((ambientDerivedSubgroup M).subgroupOf M) θ →
                              Section1.degree θ = (a : ℂ) := by
  intro hcase hBarU hUprime _hSH0 _hSH0C hSH0U
  rcases theorem_9_8_initial_constituent_witness_count_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0U hcase hBarU hUprime hSH0U with
    ⟨I, hIsub, hIcard, hIwitness⟩
  refine ⟨I, hIsub, hIcard, ?_⟩
  intro χ hχI
  rcases hIwitness χ hχI with
    ⟨hχirr, θ0, hθ0irr, hθ0not, hθ0ker, hχeq0, hθ0deg⟩
  refine ⟨hχirr, ?_⟩
  intro θ _hθirr _hθnot _hθker hχeq
  let D : Subgroup G := ambientDerivedSubgroup M
  have hIndEq :
      Section1.inducedCF (D.subgroupOf M) θ =
        Section1.inducedCF (D.subgroupOf M) θ0 :=
    hχeq.symm.trans hχeq0
  have hdegIndEq :
      Section1.degree (Section1.inducedCF (D.subgroupOf M) θ) =
        Section1.degree (Section1.inducedCF (D.subgroupOf M) θ0) :=
    congrArg Section1.degree hIndEq
  have hidx_ne : (Subgroup.index (D.subgroupOf M) : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.index_ne_zero_of_finite (H := D.subgroupOf M))
  have hmul :
      (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ =
        (Subgroup.index (D.subgroupOf M) : ℂ) * (a : ℂ) := by
    calc
      (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ =
          Section1.degree (Section1.inducedCF (D.subgroupOf M) θ) := by
            rw [Section1.degree_inducedClassFunction]
      _ = Section1.degree (Section1.inducedCF (D.subgroupOf M) θ0) := hdegIndEq
      _ = (Subgroup.index (D.subgroupOf M) : ℂ) * Section1.degree θ0 := by
            rw [Section1.degree_inducedClassFunction]
      _ = (Subgroup.index (D.subgroupOf M) : ℂ) * (a : ℂ) := by
            rw [hθ0deg]
  exact mul_left_cancel₀ hidx_ne hmul

public theorem theorem_9_8_initial_degree_count_source_bridge_sec9
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
                ∃ I : Finset (Section1.ClassFunction M),
                  I ⊆ SH0U ∧
                    I.card ≥ ((p - 1) / a) *
                      (Nat.card U / (a * Nat.card Uprime)) ∧
                    ∀ χ : Section1.ClassFunction M, χ ∈ I →
                      Section1.IsIrreducibleCharacterOnGroup χ ∧
                        Section1.degree χ = (q * a : ℂ) := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_initial_constituent_degree_count_source_bridge_sec9
      M MF U W1 W2 H0 C Uprime p q a u SH0 SH0C SH0U hcase hBarU
      hUprime hSH0 hSH0C hSH0U with
    ⟨I, hIsub, hIcard, hIdegree⟩
  have hDindex :
      Subgroup.index ((ambientDerivedSubgroup M).subgroupOf M) = q :=
    ambientDerived_subgroupOf_index_eq_q_of_hypothesis_9_2_sec9
      M MF U W1 W2 q hcase.1
  refine ⟨I, hIsub, hIcard, ?_⟩
  intro χ hχI
  rcases hIdegree χ hχI with ⟨hχirr, hθdegree⟩
  have hχSH0U : χ ∈ SH0U := hIsub hχI
  rcases hSH0U with ⟨_hYle, _hMFle, hmem⟩
  rcases (hmem χ).mp hχSH0U with ⟨θ, hθirr, hθnot, hθker, hχeq⟩
  have hθdeg : Section1.degree θ = (a : ℂ) :=
    hθdegree θ hθirr hθnot hθker hχeq
  have hχdeg : Section1.degree χ = (q * a : ℂ) := by
    rw [hχeq, Section1.degree_inducedClassFunction, hθdeg, hDindex]
  exact ⟨hχirr, hχdeg⟩

public theorem theorem_9_8_source_core_sec9
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
                  case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  rcases theorem_9_8_degree_divisibility_source_bridge_sec9 M MF U W1 W2 H0 C
      Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
      hSH0U with
    ⟨hdegreeDiv, hunderlyingDiv⟩
  exact
    ⟨hdegreeDiv,
      hunderlyingDiv,
      hBarU,
      theorem_9_8_reducible_subfamily_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U,
      theorem_9_8_irreducible_H0C_linear_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U,
      theorem_9_8_initial_degree_count_source_bridge_sec9 M MF U W1 W2 H0 C
        Uprime p q a u SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C
        hSH0U⟩

public theorem theorem_9_8
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
            (∀ χ : Section1.ClassFunction M, χ ∈ SH0 → characterDegreeDivisibleBy a χ) ∧
            case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U := by
  intro hcase hBarU hUprime hSH0 hSH0C hSH0U
  have hchar :
      case_9_7_a_characterData M MF U H0 C Uprime p q a u SH0 SH0C SH0U :=
    theorem_9_8_source_core_sec9 M MF U W1 W2 H0 C Uprime p q a u
      SH0 SH0C SH0U hcase hBarU hUprime hSH0 hSH0C hSH0U
  exact ⟨hchar.1, hchar⟩

end CFSG.Section9
