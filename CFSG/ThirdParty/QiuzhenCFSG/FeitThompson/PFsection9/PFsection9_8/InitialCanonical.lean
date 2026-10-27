module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection9.PFsection9_8.InitialData

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
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_decomposition_source_core_sec9
    {G : Type u} [Group G] [Finite G] [IsMinCE G]
    (M MF U W1 W2 H0 C Uprime : Subgroup G)
    (p q a u : ℕ) [NeZero a]
    [hnormalH0 : (H0.subgroupOf MF).Normal]
    [hcomm : IsMulCommutative (MF ⧸ H0.subgroupOf MF)]
    [hnormalC : (C.subgroupOf U).Normal]
    (H : Fin q → Subgroup (MF ⧸ H0.subgroupOf MF))
    (hqpos : 0 < q)
    (_hHcard : ∀ i, Nat.card (H i) = p)
    (hHnorm : ∀ i, quotientSubgroupNormalizedBy MF H0 U (H i))
    (hHindep : iSupIndep H)
    (hHsup : iSup H = ⊤)
    (ρBase : (U ⧸ C.subgroupOf U) →* MulAut (H ⟨0, hqpos⟩))
    (_hρcycBase : IsCyclic ρBase.range)
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
    (hρkerBase :
      ∀ x : U ⧸ C.subgroupOf U,
        ρBase x = 1 ↔
          ∀ u : U, QuotientGroup.mk' (C.subgroupOf U) u = x →
            quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) (u : G))
    (_hconjBase :
      ∀ i : Fin q,
        ∃ w : W1,
          quotientSubgroupConjugateByElement MF H0 (H ⟨0, hqpos⟩) (H i)
            (w : G))
    (hcase : case_9_7_a_data M MF U W1 W2 H0 C p q a)
    (_hBarU : quotientBarUCardinality U C u)
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (hBnormal : B.Normal)
    (hBsemi :
      Section2.IsInternalSemidirectProduct B
        ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M))
        (((U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ⊓ B))
    (hWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K)
    (hWBK_compat :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ∀ x : ↥(W ⊓ B),
        (((hWBK x : K) : U) : G) =
          ((((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G)))
    (hWBKquot :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
        M MF U H0 C Uprime q H hqpos ρBase hUprimeEq B hWBK)
    (_hA_le_B :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)) ≤ B)
    (_hBindex : Subgroup.index B = a)
    (hAnormal :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)).Normal) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
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
    let hAnormalA : A.Normal := by simpa [Dm, A] using hAnormal
    letI : B.Normal := hBnormal
    letI : A.Normal := hAnormalA
    letI : (A.subgroupOf B).Normal := hAnormalA.subgroupOf B
    let Q : Type u := B ⧸ A.subgroupOf B
    letI : Group Q := inferInstance
    let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
    let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
    let MFDsubB : Subgroup B := MFD.subgroupOf B
    ∃ QH1c : Subgroup Q,
    ∃ QH1 : Subgroup Q,
    ∃ QClam : Subgroup Q,
    ∃ QH1CH1 : Subgroup Q,
    ∃ _hsemi : Section2.IsInternalSemidirectProduct
        (⊤ : Subgroup Q) QH1c QH1CH1,
        ∃ _hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
        ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
        ∃ eClam : QClam ≃* Clam,
        (∀ m : MFDsubB,
          ∀ hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩,
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1
                  ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                    (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                      ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                  hmH1⟩) ∧
        (∀ m : MFDsubB,
          QuotientGroup.mk' (H0.subgroupOf MF)
              (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
            (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
          QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
        (∀ w : (W ⊓ B).subgroupOf B,
          ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
            eClam
                ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
              QuotientGroup.mk' Hsub
                (hWBK
                  (⟨((w : B) : Dm), by
                    simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                    ↥(W ⊓ B)))) ∧
        ∃ QMF : Subgroup Q,
          QMF =
              ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
          Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
          QH1 ≤ QMF := by
  -- `H1c ><| H1CH1` and `H1 \x Clam` quotient product decompositions.
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
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
  have hAnormalA : A.Normal := by
    simpa [Dm, A] using hAnormal
  letI : B.Normal := hBnormal
  letI : A.Normal := hAnormalA
  letI : (A.subgroupOf B).Normal := hAnormalA.subgroupOf B
  let Q : Type u := B ⧸ A.subgroupOf B
  letI : Group Q := inferInstance
  let qB : B →* Q := QuotientGroup.mk' (A.subgroupOf B)
  let WB : Subgroup Dm := W ⊓ B
  let WBsubB : Subgroup B := WB.subgroupOf B
  let H0D : Subgroup Dm := (H0.subgroupOf M).subgroupOf Dm
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup WB := UprimeD.subgroupOf WB
  let WBHsub : Subgroup WB := Hsub.comap hWBK.toMonoidHom
  have hWBK_compat' :
      ∀ x : WB,
        (((hWBK x : K) : U) : G) = ((((x : WB) : Dm) : M) : G) := by
    simpa [Dm, W, f, K, WB] using hWBK_compat
  have hWB_centralizes_base :
      ∀ x : WB,
        quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩)
          ((((x : WB) : Dm) : M) : G) := by
    intro x
    let uK : K := hWBK x
    have hρ :
        ρBase (QuotientGroup.mk' (C.subgroupOf U) (uK : U)) = 1 := by
      have huK : f (uK : U) = 1 := uK.property
      simpa [f] using congrArg (fun y : ρBase.range => (y : MulAut (H ⟨0, hqpos⟩))) huK
    have hcent :
        quotientSubgroupCentralizedByElement MF H0 (H ⟨0, hqpos⟩) ((uK : U) : G) :=
      (hρkerBase (QuotientGroup.mk' (C.subgroupOf U) (uK : U))).mp hρ (uK : U) rfl
    simpa [uK, hWBK_compat' x] using hcent
  have hWBKquot' :
      ∃ eWBHsub : (WB ⧸ WBHsub) ≃* Clam,
        WBUprime = WBHsub ∧
          ∀ x : WB,
            eWBHsub (QuotientGroup.mk' WBHsub x) =
              QuotientGroup.mk' Hsub (hWBK x) := by
    dsimp
      [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9]
      at hWBKquot
    simpa [Dm, W, f, K, Hsub, Clam, WB, UprimeD, WBUprime, WBHsub]
      using hWBKquot
  rcases hWBKquot' with ⟨eWBHsub, hWBUprime_eq, hWBHsub_apply⟩
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨_hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hH0M : H0 ≤ M := (hH0MF.trans hMFleD).trans
    (section12_ambientDerivedSubgroup_le (E := M))
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprimeM : Uprime ≤ M := (hUprimeU.trans hUleD).trans
    (section12_ambientDerivedSubgroup_le (E := M))
  have hH0subD : H0.subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0 : ((x : M) : G) ∈ H0 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hMFleD (hH0MF hxH0)
  have hUprimeSubD : Uprime.subgroupOf M ≤ Dm := by
    intro x hx
    have hxUprime : ((x : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hUleD (hUprimeU hxUprime)
  have hA_sup :
      A = H0D ⊔ UprimeD := by
    dsimp [A, H0D, UprimeD, Dm]
    rw [Subgroup.subgroupOf_sup (A := H0) (A' := Uprime) (B := M)
      hH0M hUprimeM]
    exact Subgroup.subgroupOf_sup (A := H0.subgroupOf M)
      (A' := Uprime.subgroupOf M) (B := Dm) hH0subD hUprimeSubD
  have hH0D_le_MFD : H0D ≤ ((MF.subgroupOf M).subgroupOf Dm) := by
    intro x hx
    have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
      simpa [H0D, Subgroup.mem_subgroupOf] using hx
    exact hH0MF hxH0
  have hH0Dnormal : H0D.Normal := by
    simpa [H0D] using
      (case_9_7_a_H0_normal_M_sec9 hcase).subgroupOf Dm
  have hUprimeD_le_W : UprimeD ≤ W := by
    intro x hx
    have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
      simpa [UprimeD, Subgroup.mem_subgroupOf] using hx
    exact hUprimeU hxUprime
  have hUprimeD_le_B : UprimeD ≤ B := by
    intro x hx
    have hxA : (x : Dm) ∈ A := by
      rw [hA_sup]
      exact Subgroup.mem_sup_right hx
    exact _hA_le_B hxA
  have hUprimeD_le_WB : UprimeD ≤ WB := by
    intro x hx
    exact ⟨hUprimeD_le_W hx, hUprimeD_le_B hx⟩
  have hA_of_WB_le_UprimeD :
      ∀ x : WB, ((x : Dm) ∈ A) → (x : Dm) ∈ UprimeD := by
    intro x hxA
    letI : H0D.Normal := hH0Dnormal
    exact
      theorem_9_8_mem_right_of_mem_sup_inf_and_left_inf_eq_bot_sec9
        H0D UprimeD W B ((MF.subgroupOf M).subgroupOf Dm)
        hH0D_le_MFD hUprimeD_le_W hUprimeD_le_B hBsemi.inf_eq_bot x
        (by simpa [hA_sup] using hxA)
  have hWBUprimeNormal : WBUprime.Normal := by
    rw [hWBUprime_eq]
    exact (hUprimeNormal.subgroupOf K).comap hWBK.toMonoidHom
  letI : WBUprime.Normal := hWBUprimeNormal
  let QClam : Subgroup Q := WBsubB.map qB
  let eWBsub : WBsubB ≃* WB := Subgroup.subgroupOfEquivOfLe inf_le_right
  let Nsub : Subgroup WBsubB := (A.subgroupOf B).subgroupOf WBsubB
  have hNsubNormal : Nsub.Normal := by
    exact (hAnormalA.subgroupOf B).subgroupOf WBsubB
  letI : Nsub.Normal := hNsubNormal
  have hNmap : Nsub.map eWBsub.toMonoidHom = WBUprime := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyN, hyx⟩
      have hyA : ((y : WBsubB) : B) ∈ A.subgroupOf B := by
        simpa [Nsub, Subgroup.mem_subgroupOf] using hyN
      have hyA_Dm : (((y : WBsubB) : B) : Dm) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hyA
      have hxA : (x : Dm) ∈ A := by
        have hval := congrArg (fun z : WB => (z : Dm)) hyx
        have hyA_image : ((eWBsub y : WB) : Dm) ∈ A := by
          simpa [eWBsub, Subgroup.subgroupOfEquivOfLe] using hyA_Dm
        have hval' : ((eWBsub y : WB) : Dm) = (x : Dm) := by
          simpa using hval
        rw [hval'] at hyA_image
        exact hyA_image
      exact hA_of_WB_le_UprimeD x hxA
    · intro hx
      let yB : B := ⟨(x : Dm), x.property.2⟩
      have hyWBsub : yB ∈ WBsubB := by
        simpa [WBsubB, WB, Subgroup.mem_subgroupOf, yB] using x.property.1
      let y : WBsubB := ⟨yB, hyWBsub⟩
      refine ⟨y, ?_, ?_⟩
      · have hxA : (x : Dm) ∈ A := by
          rw [hA_sup]
          exact Subgroup.mem_sup_right hx
        change (y : B) ∈ A.subgroupOf B
        simpa [Subgroup.mem_subgroupOf, y, yB] using hxA
      · apply Subtype.ext
        rfl
  let eWBUprime : (WB ⧸ WBUprime) ≃* Clam :=
    (QuotientGroup.quotientMulEquivOfEq hWBUprime_eq).trans eWBHsub
  let eQuot : (WBsubB ⧸ Nsub) ≃* (WB ⧸ WBUprime) :=
    QuotientGroup.congr Nsub WBUprime eWBsub hNmap
  let hQClam_equiv : QClam ≃* Clam :=
    (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B)).symm.trans
      (eQuot.trans eWBUprime)
  have hQClam_equiv_apply_mk :
      ∀ w : WBsubB,
        hQClam_equiv ⟨qB w, ⟨w, w.property, rfl⟩⟩ =
          QuotientGroup.mk' Hsub
            (hWBK
              (⟨((w : B) : Dm), by
                simpa [WBsubB, WB, Subgroup.mem_subgroupOf] using w.property⟩ : WB)) := by
    intro w
    let wWB : WB :=
      ⟨((w : B) : Dm), by
        simpa [WBsubB, WB, Subgroup.mem_subgroupOf] using w.property⟩
    have hRange :
        (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B))
            (QuotientGroup.mk' Nsub w) =
          ⟨qB w, ⟨w, w.property, rfl⟩⟩ := by
      apply Subtype.ext
      change
        ((quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B))
            (QuotientGroup.mk' ((A.subgroupOf B).subgroupOf WBsubB) w) :
          B ⧸ A.subgroupOf B) =
            QuotientGroup.mk' (A.subgroupOf B) (w : B)
      exact quotientSubgroupRangeEquiv_apply_mk WBsubB (A.subgroupOf B) w
    have hRange_symm :
        (quotientSubgroupRangeEquiv WBsubB (A.subgroupOf B)).symm
            ⟨qB w, ⟨w, w.property, rfl⟩⟩ =
          QuotientGroup.mk' Nsub w := by
      rw [← hRange]
      simp
    have heWBsub :
        (Subgroup.subgroupOfEquivOfLe inf_le_right : WBsubB ≃* WB) w = wWB := by
      apply Subtype.ext
      rfl
    rw [← hRange]
    simp only [hQClam_equiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change eWBUprime (eQuot (QuotientGroup.mk' Nsub w)) =
      QuotientGroup.mk' Hsub (hWBK wWB)
    rw [show eQuot (QuotientGroup.mk' Nsub w) =
      QuotientGroup.mk' WBUprime (eWBsub w) by
        exact QuotientGroup.congr_mk' Nsub WBUprime eWBsub hNmap w]
    simp only [eWBUprime, MulEquiv.trans_apply,
      QuotientGroup.quotientMulEquivOfEq_mk]
    simpa [heWBsub, eWBsub] using hWBHsub_apply wWB
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let MFDsubB : Subgroup B := MFD.subgroupOf B
  let QMF : Subgroup Q := MFDsubB.map qB
  have hMFDsubD : MF.subgroupOf M ≤ Dm := by
    intro x hx
    have hxMF : ((x : M) : G) ∈ MF := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact hMFleD hxMF
  let eMFD : MFD ≃* MF :=
    (Subgroup.subgroupOfEquivOfLe (H := MF.subgroupOf M) (K := Dm) hMFDsubD).trans
      (Subgroup.subgroupOfEquivOfLe (H := MF) (K := M)
        (hMFleD.trans (section12_ambientDerivedSubgroup_le (E := M))))
  have hH0D_le_MFD : H0D ≤ MFD := by
    intro x hx
    have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
      simpa [H0D, Subgroup.mem_subgroupOf] using hx
    exact hH0MF hxH0
  let H0DsubMFD : Subgroup MFD := H0D.subgroupOf MFD
  haveI : H0DsubMFD.Normal := hH0Dnormal.subgroupOf MFD
  have hMFD_kernel_map : H0DsubMFD.map (eMFD : MFD →* MF) = H0.subgroupOf MF := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hyx⟩
      have hyH0D : (y : Dm) ∈ H0D := by
        simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hy
      have hyH0 : (((y : Dm) : M) : G) ∈ H0 := by
        simpa [H0D, Subgroup.mem_subgroupOf] using hyH0D
      have hval : ((eMFD y : MF) : G) = ((y : Dm) : G) := by
        rfl
      have hxval : (x : G) = ((y : Dm) : G) := by
        rw [← hval]
        exact congrArg (fun z : MF => (z : G)) hyx.symm
      simpa [Subgroup.mem_subgroupOf, hxval] using hyH0
    · intro hx
      let yM : M := ⟨(x : G),
        (hMFleD.trans (section12_ambientDerivedSubgroup_le (E := M))) x.property⟩
      have hyDmem : yM ∈ Dm := hMFDsubD (by
        simp [Subgroup.mem_subgroupOf, yM])
      let yD : Dm := ⟨yM, hyDmem⟩
      have hyMFDmem : yD ∈ MFD := by
        simp [MFD, Subgroup.mem_subgroupOf, yD, yM]
      let y : MFD := ⟨yD, hyMFDmem⟩
      refine ⟨y, ?_, ?_⟩
      · have hxH0 : (x : G) ∈ H0 := by
          simpa [Subgroup.mem_subgroupOf] using hx
        change (y : Dm) ∈ H0D
        simpa [H0D, Subgroup.mem_subgroupOf, y, yD, yM] using hxH0
      · apply Subtype.ext
        rfl
  let NMFsub : Subgroup MFDsubB := (A.subgroupOf B).subgroupOf MFDsubB
  have hNMFsubNormal : NMFsub.Normal := by
    exact (hAnormalA.subgroupOf B).subgroupOf MFDsubB
  letI : NMFsub.Normal := hNMFsubNormal
  let eMFDsub : MFDsubB ≃* MFD := Subgroup.subgroupOfEquivOfLe hBsemi.left_le
  have hNMF_map : NMFsub.map (eMFDsub : MFDsubB →* MFD) = H0DsubMFD := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyN, hyx⟩
      have hyA : ((y : MFDsubB) : B) ∈ A.subgroupOf B := by
        simpa [NMFsub, Subgroup.mem_subgroupOf] using hyN
      have hyA_Dm : (((y : MFDsubB) : B) : Dm) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hyA
      have hxA : (x : Dm) ∈ A := by
        have hval := congrArg (fun z : MFD => (z : Dm)) hyx
        have hyA_image : ((eMFDsub y : MFD) : Dm) ∈ A := by
          simpa [eMFDsub, Subgroup.subgroupOfEquivOfLe] using hyA_Dm
        have hval' : ((eMFDsub y : MFD) : Dm) = (x : Dm) := by
          simpa using hval
        rw [hval'] at hyA_image
        exact hyA_image
      have hxH0D : (x : Dm) ∈ H0D := by
        letI : H0D.Normal := hH0Dnormal
        exact
          theorem_9_8_mem_left_of_mem_sup_and_left_inf_right_eq_bot_sec9
            H0D UprimeD MFD WB hH0D_le_MFD hUprimeD_le_WB
            hBsemi.inf_eq_bot x (by simpa [hA_sup] using hxA)
      simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hxH0D
    · intro hx
      let yB : B := ⟨(x : Dm), hBsemi.left_le x.property⟩
      have hyMFDsub : yB ∈ MFDsubB := by
        simp [MFDsubB, MFD, Subgroup.mem_subgroupOf, yB]
      let y : MFDsubB := ⟨yB, hyMFDsub⟩
      refine ⟨y, ?_, ?_⟩
      · have hxH0D : (x : Dm) ∈ H0D := by
          simpa [H0DsubMFD, Subgroup.mem_subgroupOf] using hx
        have hxA : (x : Dm) ∈ A := by
          rw [hA_sup]
          exact Subgroup.mem_sup_left hxH0D
        change (y : B) ∈ A.subgroupOf B
        simpa [Subgroup.mem_subgroupOf, y, yB] using hxA
      · apply Subtype.ext
        rfl
  let eMFDquot : (MFD ⧸ H0DsubMFD) ≃* (MF ⧸ H0.subgroupOf MF) :=
    QuotientGroup.congr H0DsubMFD (H0.subgroupOf MF) eMFD hMFD_kernel_map
  let eQuot : (MFDsubB ⧸ NMFsub) ≃* (MFD ⧸ H0DsubMFD) :=
    QuotientGroup.congr NMFsub H0DsubMFD eMFDsub hNMF_map
  let eRangeMFD : (MFDsubB ⧸ NMFsub) ≃* QMF :=
    quotientSubgroupRangeEquiv MFDsubB (A.subgroupOf B)
  let hQMF_equiv : QMF ≃* (MF ⧸ H0.subgroupOf MF) :=
    eRangeMFD.symm.trans (eQuot.trans eMFDquot)
  let QH1sub : Subgroup QMF := (H ⟨0, hqpos⟩).comap hQMF_equiv.toMonoidHom
  let QH1 : Subgroup Q := QH1sub.map QMF.subtype
  let hQH1sub_equiv : QH1sub ≃* H ⟨0, hqpos⟩ := by
    let φ : QH1sub →* H ⟨0, hqpos⟩ :=
      { toFun := fun x => ⟨hQMF_equiv (x : QMF), x.property⟩
        map_one' := by
          ext
          simp
        map_mul' := by
          intro x y
          ext
          simp }
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply hQMF_equiv.injective
      exact congrArg (fun z : H ⟨0, hqpos⟩ => (z : MF ⧸ H0.subgroupOf MF)) hxy
    have hφ_surj : Function.Surjective φ := by
      intro x
      let yQMF : QMF := hQMF_equiv.symm (x : MF ⧸ H0.subgroupOf MF)
      have hyQH1 : yQMF ∈ QH1sub := by
        change hQMF_equiv yQMF ∈ H ⟨0, hqpos⟩
        simp [yQMF]
      refine ⟨⟨yQMF, hyQH1⟩, ?_⟩
      ext
      change hQMF_equiv yQMF = (x : MF ⧸ H0.subgroupOf MF)
      simp [yQMF]
    exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let hQH1_range_equiv : QH1sub ≃* QH1 := by
    let φ : QH1sub →* QH1 :=
      { toFun := fun x => ⟨((x : QH1sub) : QMF), ⟨(x : QH1sub), x.property, rfl⟩⟩
        map_one' := by
          ext
          rfl
        map_mul' := by
          intro x y
          ext
          rfl }
    have hφ_inj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : QH1 => (z : Q)) hxy
    have hφ_surj : Function.Surjective φ := by
      intro x
      rcases x.property with ⟨y, hy, hyx⟩
      refine ⟨⟨y, hy⟩, ?_⟩
      apply Subtype.ext
      exact hyx
    exact MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let hQH1_equiv : QH1 ≃* H ⟨0, hqpos⟩ :=
    hQH1_range_equiv.symm.trans hQH1sub_equiv
  let H1cMF : Subgroup (MF ⧸ H0.subgroupOf MF) :=
    ⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i
  have hMF_Hsplit :
      Section2.IsInternalDirectProduct
        (⊤ : Subgroup (MF ⧸ H0.subgroupOf MF)) H1cMF (H ⟨0, hqpos⟩) := by
    simpa [H1cMF] using
      theorem_9_8_iSup_split_base_internalDirectProduct_sec9
        H ⟨0, hqpos⟩ hHindep hHsup
  let QH1csub : Subgroup QMF := H1cMF.comap hQMF_equiv.toMonoidHom
  have hQMF_split :
      Section2.IsInternalDirectProduct (⊤ : Subgroup QMF) QH1csub QH1sub := by
    simpa [QH1csub, QH1sub] using
      internalDirectProduct_comap_mulEquiv_top_sec9 hQMF_equiv hMF_Hsplit
  let QH1c : Subgroup Q := QH1csub.map QMF.subtype
  have hQMF_split_in_Q :
      Section2.IsInternalDirectProduct QMF QH1c QH1 := by
    simpa [QH1c, QH1] using
      internalDirectProduct_map_subtype_top_sec9 hQMF_split
  have hQMF_equiv_apply_mk :
      ∀ m : MFDsubB,
        hQMF_equiv ⟨qB m, ⟨m, m.property, rfl⟩⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) := by
    intro m
    have hRange :
        eRangeMFD (QuotientGroup.mk' NMFsub m) =
          ⟨qB m, ⟨m, m.property, rfl⟩⟩ := by
      apply Subtype.ext
      change
        ((quotientSubgroupRangeEquiv MFDsubB (A.subgroupOf B))
            (QuotientGroup.mk' ((A.subgroupOf B).subgroupOf MFDsubB) m) :
          B ⧸ A.subgroupOf B) =
            QuotientGroup.mk' (A.subgroupOf B) (m : B)
      exact quotientSubgroupRangeEquiv_apply_mk MFDsubB (A.subgroupOf B) m
    have hRange_symm :
        eRangeMFD.symm ⟨qB m, ⟨m, m.property, rfl⟩⟩ =
          QuotientGroup.mk' NMFsub m := by
      rw [← hRange]
      simp
    rw [← hRange]
    simp only [hQMF_equiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    change eMFDquot (eQuot (QuotientGroup.mk' NMFsub m)) =
      QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m))
    dsimp [eQuot, eMFDquot]
  have hQH1_equiv_apply_mk :
      ∀ (m : MFDsubB)
        (hmH1 :
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
            H ⟨0, hqpos⟩),
        ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
          hQH1_equiv ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
            ⟨QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)),
              hmH1⟩ := by
    intro m hmH1
    let qm : QMF := ⟨qB m, ⟨m, m.property, rfl⟩⟩
    have hqmH1sub : qm ∈ QH1sub := by
      change hQMF_equiv qm ∈ H ⟨0, hqpos⟩
      simpa [qm, hQMF_equiv_apply_mk m] using hmH1
    let ysub : QH1sub := ⟨qm, hqmH1sub⟩
    have hQH1_image_val :
        ((hQH1_range_equiv ysub : QH1) : Q) =
          QuotientGroup.mk' (A.subgroupOf B) m := by
      simp [hQH1_range_equiv, ysub, qm, qB]
      rfl
    let hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1 := by
      simp [← hQH1_image_val]
    refine ⟨hmQH1, ?_⟩
    have hQH1_image :
        (⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ : QH1) =
          hQH1_range_equiv ysub := by
      apply Subtype.ext
      exact hQH1_image_val.symm
    calc
      hQH1_equiv ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
          hQH1_equiv (hQH1_range_equiv ysub) := by
        rw [hQH1_image]
      _ =
          hQH1sub_equiv ysub := by
        simp [hQH1_equiv]
      _ = ⟨QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)),
            hmH1⟩ := by
        apply Subtype.ext
        change hQMF_equiv ⟨qB m, ⟨m, m.property, rfl⟩⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m))
        exact hQMF_equiv_apply_mk m
  have hQH1c_apply_mk :
      ∀ (m : MFDsubB)
        (hmH1c :
          QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈ H1cMF),
        QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c := by
    intro m hmH1c
    let qm : QMF := ⟨qB m, ⟨m, m.property, rfl⟩⟩
    have hqmH1csub : qm ∈ QH1csub := by
      change hQMF_equiv qm ∈ H1cMF
      simpa [qm, hQMF_equiv_apply_mk m] using hmH1c
    change qB m ∈ QH1c
    exact ⟨qm, hqmH1csub, rfl⟩
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
  let QH1CH1 : Subgroup Q := QH1 ⊔ QClam
  have hQH1_QClam_commute :
      ∀ h ∈ QH1, ∀ k ∈ QClam, h * k = k * h := by
    intro h hh k hk
    rcases hh with ⟨y, hyQH1sub, hyh⟩
    rcases y.property with ⟨m, hmMFDsub, hmy⟩
    rcases hk with ⟨w, hwWBsub, hwk⟩
    let mSub : MFDsubB := ⟨m, hmMFDsub⟩
    let mMF : MF := eMFD (eMFDsub mSub)
    have hmHbase :
        QuotientGroup.mk' (H0.subgroupOf MF) mMF ∈ H ⟨0, hqpos⟩ := by
      have hybase : hQMF_equiv y ∈ H ⟨0, hqpos⟩ := by
        simpa [QH1sub] using hyQH1sub
      have hy_eq :
          y = ⟨qB mSub, ⟨mSub, mSub.property, rfl⟩⟩ := by
        apply Subtype.ext
        simpa [mSub] using hmy.symm
      rw [hy_eq] at hybase
      simpa [mMF, hQMF_equiv_apply_mk mSub] using hybase
    have hmMFD : (m : Dm) ∈ MFD := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
    have hwWB : (w : Dm) ∈ WB := by
      simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
    let wWB : WB := ⟨(w : Dm), hwWB⟩
    rcases hWB_centralizes_base wWB with ⟨hconjMF, action, haction, hfix⟩
    have hfix_mk :
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
                ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ =
          QuotientGroup.mk' (H0.subgroupOf MF) mMF := by
      calc
        QuotientGroup.mk' (H0.subgroupOf MF)
            ⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
                ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ =
            action (QuotientGroup.mk' (H0.subgroupOf MF) mMF) := by
              exact (haction mMF).symm
        _ = QuotientGroup.mk' (H0.subgroupOf MF) mMF :=
              hfix (QuotientGroup.mk' (H0.subgroupOf MF) mMF) hmHbase
    have hdeltaH0 :
        (⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
            ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ / mMF : MF) ∈
          H0.subgroupOf MF :=
      QuotientGroup.eq_iff_div_mem.mp hfix_mk
    have hconjMFD :
        (w : Dm)⁻¹ * (m : Dm) * (w : Dm) ∈ MFD := by
      simpa [Section2.conjBy, mul_assoc] using
        hBsemi.right_normalizes_left ((w : Dm)⁻¹) (WB.inv_mem hwWB)
          (m : Dm) hmMFD
    let conjB : B :=
      ⟨(w : Dm)⁻¹ * (m : Dm) * (w : Dm), hBsemi.left_le hconjMFD⟩
    have hdeltaH0D : ((conjB / m : B) : Dm) ∈ H0D := by
      have hdeltaH0G :
          (((⟨((((wWB : WB) : Dm) : M) : G)⁻¹ * (mMF : G) *
              ((((wWB : WB) : Dm) : M) : G), hconjMF mMF⟩ / mMF : MF) : G)) ∈
            H0 := by
        simpa [Subgroup.mem_subgroupOf] using hdeltaH0
      simpa [H0D, Subgroup.mem_subgroupOf, conjB, mMF, mSub, wWB, eMFD,
        eMFDsub, Subgroup.subgroupOfEquivOfLe, div_eq_mul_inv, mul_assoc] using hdeltaH0G
    have hconj_eq_m : qB conjB = qB m := by
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hdeltaA : ((conjB / m : B) : Dm) ∈ A := by
        rw [hA_sup]
        exact Subgroup.mem_sup_left hdeltaH0D
      simpa [Subgroup.mem_subgroupOf] using hdeltaA
    have hconjB_eq : conjB = w⁻¹ * m * w := by
      apply Subtype.ext
      rfl
    have hconjQ :
        (qB w)⁻¹ * qB m * qB w = qB m := by
      calc
        (qB w)⁻¹ * qB m * qB w = qB (w⁻¹ * m * w) := by
          simp [map_mul, map_inv, mul_assoc]
        _ = qB conjB := by rw [← hconjB_eq]
        _ = qB m := hconj_eq_m
    have hcomm_mw : qB m * qB w = qB w * qB m := by
      have hleft := congrArg (fun z : Q => qB w * z) hconjQ
      simpa [mul_assoc] using hleft
    rw [← hyh, ← hwk]
    change (y : Q) * qB w = qB w * (y : Q)
    rw [← hmy]
    exact hcomm_mw
  have hQMF_inf_QClam : QMF ⊓ QClam = ⊥ := by
    apply le_antisymm
    · intro x hx
      rcases hx.1 with ⟨m, hmMFDsub, hmx⟩
      rcases hx.2 with ⟨w, hwWBsub, hwx⟩
      have hmwA_B : m / w ∈ A.subgroupOf B := by
        exact QuotientGroup.eq_iff_div_mem.mp (hmx.trans hwx.symm)
      letI : H0D.Normal := hH0Dnormal
      have hmwA_D : ((m / w : B) : Dm) ∈ A := by
        simpa [Subgroup.mem_subgroupOf] using hmwA_B
      have hmwSup : ((m / w : B) : Dm) ∈ H0D ⊔ UprimeD := by
        simpa [hA_sup] using hmwA_D
      rcases (Subgroup.mem_sup_of_normal_left
          (s := H0D) (t := UprimeD) (x := ((m / w : B) : Dm))).1
          hmwSup with
        ⟨h0, hh0, u0, hu0, hprod0⟩
      have hmMFD : (m : Dm) ∈ MFD := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
      have hwWB : (w : Dm) ∈ WB := by
        simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
      have hmul :
          (m : Dm) * (w : Dm)⁻¹ = h0 * u0 := by
        simpa [div_eq_mul_inv] using hprod0.symm
      have huniq :=
        internalSemidirectProduct_mul_unique_sec9 hBsemi
          hmMFD (hH0D_le_MFD hh0) (WB.inv_mem hwWB) (hUprimeD_le_WB hu0) hmul
      have hmA_D : (m : Dm) ∈ A := by
        rw [huniq.1]
        rw [hA_sup]
        exact Subgroup.mem_sup_left hh0
      have hmA_B' : m ∈ A.subgroupOf B := by
        simpa [Subgroup.mem_subgroupOf] using hmA_D
      have hq_m_one : qB m = 1 :=
        (QuotientGroup.eq_one_iff (N := A.subgroupOf B) (x := m)).2 hmA_B'
      have hx_one : x = 1 := by
        rw [← hmx, hq_m_one]
      simp [hx_one]
    · exact bot_le
  have hQH1_le_QMF : QH1 ≤ QMF := by
    intro x hx
    rcases hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQH1_inf_QClam : QH1 ⊓ QClam = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxQMFClam : x ∈ QMF ⊓ QClam :=
        ⟨hQH1_le_QMF hx.1, hx.2⟩
      simpa [hQMF_inf_QClam] using hxQMFClam
    · exact bot_le
  have hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam := by
    simpa [QH1CH1] using
      internalDirectProduct_sup_of_commute_inf_eq_bot_sec9
        QH1 QClam hQH1_QClam_commute hQH1_inf_QClam
  have hsemiQMF :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Q) QMF QClam := by
    refine
      { left_le := ?_
        right_le := ?_
        right_normalizes_left := ?_
        inf_eq_bot := hQMF_inf_QClam
        mul_surjective := ?_ }
    · intro x _hx
      trivial
    · intro x _hx
      trivial
    · intro k hk h hh
      rcases hk with ⟨w, hwWBsub, hwk⟩
      rcases hh with ⟨m, hmMFDsub, hmh⟩
      have hmMFD : (m : Dm) ∈ MFD := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
      have hwWB : (w : Dm) ∈ WB := by
        simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
      have hconjMFD : Section2.conjBy (w : Dm) (m : Dm) ∈ MFD := by
        exact hBsemi.right_normalizes_left (w : Dm) hwWB (m : Dm) hmMFD
      let conjB : B := ⟨Section2.conjBy (w : Dm) (m : Dm), hBsemi.left_le hconjMFD⟩
      have hconjB_MFDsub : conjB ∈ MFDsubB := by
        simpa [MFDsubB, Subgroup.mem_subgroupOf, conjB] using hconjMFD
      refine ⟨conjB, hconjB_MFDsub, ?_⟩
      rw [← hwk, ← hmh]
      have hconjB_eq : conjB = w * m * w⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hconjB_eq]
      simp [Section2.conjBy, map_mul, map_inv, mul_assoc]
    · intro c _hc
      rcases QuotientGroup.mk'_surjective (A.subgroupOf B) c with ⟨b, rfl⟩
      rcases hBsemi.mul_surjective (b : Dm) b.property with
        ⟨m, hmMFD, w, hwWB, hbw⟩
      let mB : B := ⟨m, hBsemi.left_le hmMFD⟩
      let wB : B := ⟨w, hwWB.2⟩
      have hmB_MFDsub : mB ∈ MFDsubB := by
        change (m : Dm) ∈ MFD
        exact hmMFD
      have hwB_WBsub : wB ∈ WBsubB := by
        change (w : Dm) ∈ WB
        exact hwWB
      refine ⟨qB mB, ⟨mB, hmB_MFDsub, rfl⟩,
        qB wB, ⟨wB, hwB_WBsub, rfl⟩, ?_⟩
      have hb_eq : b = mB * wB := by
        apply Subtype.ext
        exact hbw
      rw [hb_eq]
      exact qB.map_mul mB wB
  have hQClam_normalizes_QH1c :
      ∀ k ∈ QClam, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
    intro k hk h hh
    rcases hk with ⟨w, hwWBsub, hwk⟩
    rcases hh with ⟨y, hyQH1csub, hyh⟩
    rcases y.property with ⟨m, hmMFDsub, hmy⟩
    let mSub : MFDsubB := ⟨m, hmMFDsub⟩
    let mMF : MF := eMFD (eMFDsub mSub)
    have hmH1c :
        QuotientGroup.mk' (H0.subgroupOf MF) mMF ∈ H1cMF := by
      have hybase : hQMF_equiv y ∈ H1cMF := by
        simpa [QH1csub] using hyQH1csub
      have hy_eq :
          y = ⟨qB mSub, ⟨mSub, mSub.property, rfl⟩⟩ := by
        apply Subtype.ext
        simpa [mSub] using hmy.symm
      rw [hy_eq] at hybase
      simpa [mMF, hQMF_equiv_apply_mk mSub] using hybase
    have hmMFD : (m : Dm) ∈ MFD := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf] using hmMFDsub
    have hwWB : (w : Dm) ∈ WB := by
      simpa [WBsubB, Subgroup.mem_subgroupOf] using hwWBsub
    let wWB : WB := ⟨(w : Dm), hwWB⟩
    let uK : K := hWBK wWB
    rcases hH1cMF_norm_U ((uK : U)⁻¹) with
      ⟨hconjMF, action, haction, hmap⟩
    have hmem_action :
        action (QuotientGroup.mk' (H0.subgroupOf MF) mMF) ∈ H1cMF := by
      rw [hmap]
      exact Subgroup.mem_map_of_mem action.toMonoidHom hmH1c
    let conjMF : MF :=
      ⟨(((uK : K) : U) : G) * (mMF : G) * (((uK : K) : U) : G)⁻¹,
        by simpa using hconjMF mMF⟩
    have hmem_conj :
        QuotientGroup.mk' (H0.subgroupOf MF) conjMF ∈ H1cMF := by
      rw [haction mMF] at hmem_action
      simpa [conjMF, mul_assoc] using hmem_action
    have hconjMFD : Section2.conjBy (w : Dm) (m : Dm) ∈ MFD := by
      exact hBsemi.right_normalizes_left (w : Dm) hwWB (m : Dm) hmMFD
    let conjB : B :=
      ⟨Section2.conjBy (w : Dm) (m : Dm), hBsemi.left_le hconjMFD⟩
    have hconjB_MFDsub : conjB ∈ MFDsubB := by
      simpa [MFDsubB, Subgroup.mem_subgroupOf, conjB] using hconjMFD
    let conjSub : MFDsubB := ⟨conjB, hconjB_MFDsub⟩
    let yConj : QMF := ⟨qB conjSub, ⟨conjSub, conjSub.property, rfl⟩⟩
    have hconjMF_eq : eMFD (eMFDsub conjSub) = conjMF := by
      apply Subtype.ext
      have hu_eq :
          (((uK : K) : U) : G) = ((((wWB : WB) : Dm) : M) : G) := by
        simpa [uK] using hWBK_compat' wWB
      simp [conjSub, conjB, conjMF, mSub, mMF, wWB, hu_eq, eMFD, eMFDsub,
        Subgroup.subgroupOfEquivOfLe, Section2.conjBy, mul_assoc]
    have hyConj_QH1csub : yConj ∈ QH1csub := by
      change hQMF_equiv yConj ∈ H1cMF
      rw [hQMF_equiv_apply_mk conjSub, hconjMF_eq]
      exact hmem_conj
    refine ⟨yConj, hyConj_QH1csub, ?_⟩
    have hconjQ :
        qB conjB = Section2.conjBy (qB w) (qB m) := by
      have hconjB_eq : conjB = w * m * w⁻¹ := by
        apply Subtype.ext
        rfl
      rw [hconjB_eq]
      simp [Section2.conjBy, map_mul, map_inv, mul_assoc]
    rw [← hwk, ← hyh]
    change qB conjB = Section2.conjBy (qB w) (y : Q)
    rw [← hmy]
    exact hconjQ
  have hsemiQ :
      Section2.IsInternalSemidirectProduct (⊤ : Subgroup Q) QH1c QH1CH1 := by
    -- Associativity of the canonical quotient semidirect product:
    -- `Q = (QH1c × QH1) ⋊ QClam = QH1c ⋊ (QH1 × QClam)`.
    have hQH1c_le_QMF : QH1c ≤ QMF := by
      intro x hx
      rcases hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQH1_normalizes_QH1c :
        ∀ k ∈ QH1, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
      intro k hk h hh
      have hconj_eq : Section2.conjBy k h = h := by
        calc
          Section2.conjBy k h = k * h * k⁻¹ := rfl
          _ = h * k * k⁻¹ := by
            rw [(hQMF_split_in_Q.commute h hh k hk).symm]
          _ = h := by simp [mul_assoc]
      simpa [hconj_eq] using hh
    have hQH1CH1_normalizes_QH1c :
        ∀ k ∈ QH1CH1, ∀ h ∈ QH1c, Section2.conjBy k h ∈ QH1c := by
      intro k hk h hh
      rcases hprod.mul_surjective k hk with ⟨q1, hq1, qc, hqc, hkprod⟩
      have hqc_h : Section2.conjBy qc h ∈ QH1c :=
        hQClam_normalizes_QH1c qc hqc h hh
      have hq1_norm :
          Section2.conjBy q1 (Section2.conjBy qc h) ∈ QH1c :=
        hQH1_normalizes_QH1c q1 hq1 (Section2.conjBy qc h) hqc_h
      have hconj_eq :
          Section2.conjBy k h =
            Section2.conjBy q1 (Section2.conjBy qc h) := by
        rw [hkprod]
        simp [Section2.conjBy, mul_assoc]
      simpa [hconj_eq] using hq1_norm
    have hQH1c_inf_QH1CH1 : QH1c ⊓ QH1CH1 = ⊥ := by
      apply le_antisymm
      · intro x hx
        rcases hprod.mul_surjective x hx.2 with ⟨q1, hq1, qc, hqc, hxprod⟩
        have hxQMF : x ∈ QMF := hQH1c_le_QMF hx.1
        have hq1QMF : q1 ∈ QMF := hQH1_le_QMF hq1
        have hqcQMF : qc ∈ QMF := by
          have hqc_eq : qc = q1⁻¹ * x := by
            rw [hxprod]
            simp
          rw [hqc_eq]
          exact QMF.mul_mem (QMF.inv_mem hq1QMF) hxQMF
        have hqcInf : qc ∈ QMF ⊓ QClam := ⟨hqcQMF, hqc⟩
        have hqc_one : qc = 1 := by
          have hbot : qc ∈ (⊥ : Subgroup Q) := by
            simpa [hQMF_inf_QClam] using hqcInf
          simpa using hbot
        have hx_eq_q1 : x = q1 := by
          rw [hxprod, hqc_one]
          simp
        have hxQH1 : x ∈ QH1 := by
          simpa [hx_eq_q1] using hq1
        have hxInf : x ∈ QH1c ⊓ QH1 := ⟨hx.1, hxQH1⟩
        have hxBot : x ∈ (⊥ : Subgroup Q) := by
          simpa [hQMF_split_in_Q.inf_eq_bot] using hxInf
        simpa using hxBot
      · exact bot_le
    refine
      { left_le := ?_
        right_le := ?_
        right_normalizes_left := hQH1CH1_normalizes_QH1c
        inf_eq_bot := hQH1c_inf_QH1CH1
        mul_surjective := ?_ }
    · intro x _hx
      trivial
    · intro x _hx
      trivial
    · intro c _hc
      rcases hsemiQMF.mul_surjective c (by trivial) with
        ⟨qmf, hqmf, qc, hqc, hcprod⟩
      rcases hQMF_split_in_Q.mul_surjective qmf hqmf with
        ⟨qh1c, hqh1c, qh1, hqh1, hqmfprod⟩
      have hright : qh1 * qc ∈ QH1CH1 := by
        change qh1 * qc ∈ QH1 ⊔ QClam
        have hqh1_sup : qh1 ∈ QH1 ⊔ QClam :=
          (le_sup_left : QH1 ≤ QH1 ⊔ QClam) hqh1
        have hqc_sup : qc ∈ QH1 ⊔ QClam :=
          (le_sup_right : QClam ≤ QH1 ⊔ QClam) hqc
        exact (QH1 ⊔ QClam).mul_mem hqh1_sup hqc_sup
      refine ⟨qh1c, hqh1c, qh1 * qc, hright, ?_⟩
      rw [hcprod, hqmfprod]
      simp [mul_assoc]
  exact
    ⟨QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, hQH1_equiv, hQClam_equiv,
      (fun m hmH1 => by
        have hmRaw_eq :
            eMFD (eMFDsub m) =
              theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m) := by
          ext
          rfl
        have hmH1' :
            QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
              H ⟨0, hqpos⟩ := by
          simpa [hmRaw_eq] using hmH1
        rcases hQH1_equiv_apply_mk m hmH1' with ⟨hmQH1, hmQH1_apply⟩
        refine ⟨hmQH1, ?_⟩
        simpa [hmRaw_eq] using hmQH1_apply),
      (fun m hmH1c => by
        have hmRaw_eq :
            eMFD (eMFDsub m) =
              theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m) := by
          ext
          rfl
        have hmH1c' :
            QuotientGroup.mk' (H0.subgroupOf MF) (eMFD (eMFDsub m)) ∈
              H1cMF := by
          simpa [H1cMF, hmRaw_eq] using hmH1c
        simpa using hQH1c_apply_mk m hmH1c'),
      (fun w => by
        let hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam := by
          exact ⟨w, w.property, rfl⟩
        refine ⟨hwQClam, ?_⟩
        exact hQClam_equiv_apply_mk w),
    QMF, rfl, hQMF_split_in_Q, hQH1_le_QMF⟩

set_option maxHeartbeats 2000000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_product_source_core_sec9
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
    (hUprimeEq : Uprime = (_root_.commutator U).map U.subtype)
    (B : Subgroup ((ambientDerivedSubgroup M).subgroupOf M))
    (hBnormal : B.Normal)
    (hBsemi :
      Section2.IsInternalSemidirectProduct B
        ((MF.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M))
        (((U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)) ⊓ B))
    (hWBK :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ↥(W ⊓ B) ≃* K)
    (hWBK_compat :
      let W : Subgroup ((ambientDerivedSubgroup M).subgroupOf M) :=
        (U.subgroupOf M).subgroupOf ((ambientDerivedSubgroup M).subgroupOf M)
      let f : U →* ρBase.range :=
        ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
      let K : Subgroup U := f.ker
      ∀ x : ↥(W ⊓ B),
        (((hWBK x : K) : U) : G) =
          ((((x : (ambientDerivedSubgroup M).subgroupOf M) : M) : G)))
    (hWBKquot :
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9
        M MF U H0 C Uprime q H hqpos ρBase hUprimeEq B hWBK)
    (_hA_le_B :
      (((H0 ⊔ Uprime).subgroupOf M).subgroupOf
        ((ambientDerivedSubgroup M).subgroupOf M)) ≤ B)
    (_hBindex : Subgroup.index B = a) :
    let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
    let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
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
    ∃ hAnormal : A.Normal,
      letI : B.Normal := hBnormal
      letI : A.Normal := hAnormal
      letI : (A.subgroupOf B).Normal := hAnormal.subgroupOf B
      let Q : Type u := B ⧸ A.subgroupOf B
      letI : Group Q := inferInstance
      let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
      let MFD : Subgroup Dm := ((MF.subgroupOf M).subgroupOf Dm)
      let MFDsubB : Subgroup B := MFD.subgroupOf B
      ∃ QH1c : Subgroup Q,
      ∃ QH1 : Subgroup Q,
      ∃ QClam : Subgroup Q,
      ∃ QH1CH1 : Subgroup Q,
      ∃ _hsemi : Section2.IsInternalSemidirectProduct
          (⊤ : Subgroup Q) QH1c QH1CH1,
      ∃ _hprod : Section2.IsInternalDirectProduct QH1CH1 QH1 QClam,
      ∃ eH1 : QH1 ≃* H ⟨0, hqpos⟩,
      ∃ eClam : QClam ≃* Clam,
        (∀ m : MFDsubB,
          ∀ hmH1 :
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              H ⟨0, hqpos⟩,
            ∃ hmQH1 : QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1,
              eH1
                  ⟨QuotientGroup.mk' (A.subgroupOf B) m, hmQH1⟩ =
                  ⟨QuotientGroup.mk' (H0.subgroupOf MF)
                      (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                        ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)),
                    hmH1⟩) ∧
          (∀ m : MFDsubB,
            QuotientGroup.mk' (H0.subgroupOf MF)
                (theorem_9_8_MFDSubgroupOf_to_MF_sec9 M MF
                  ((Subgroup.subgroupOfEquivOfLe hBsemi.left_le) m)) ∈
              (⨆ i, ⨆ _ : i ≠ ⟨0, hqpos⟩, H i) →
            QuotientGroup.mk' (A.subgroupOf B) m ∈ QH1c) ∧
          (∀ w : (W ⊓ B).subgroupOf B,
            ∃ hwQClam : QuotientGroup.mk' (A.subgroupOf B) w ∈ QClam,
              eClam
                  ⟨QuotientGroup.mk' (A.subgroupOf B) w, hwQClam⟩ =
                QuotientGroup.mk' Hsub
                  (hWBK
                    (⟨((w : B) : Dm), by
                      simpa [W, Subgroup.mem_subgroupOf] using w.property⟩ :
                      ↥(W ⊓ B)))) ∧
            ∃ QMF : Subgroup Q,
              QMF =
                  ((MFD.subgroupOf B).map (QuotientGroup.mk' (A.subgroupOf B))) ∧
              Section2.IsInternalDirectProduct QMF QH1c QH1 ∧
              QH1 ≤ QMF := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  have hAnormal : A.Normal := by
    simpa [Dm, A] using
      theorem_9_8_H0Uprime_normal_ambientDerived_subgroupOf_sec9
        M MF U W1 W2 H0 C Uprime p q a hcase hUprimeEq
  exact ⟨hAnormal,
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_decomposition_source_core_sec9
      M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
      ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
      hUprimeEq B hBnormal hBsemi hWBK hWBK_compat hWBKquot _hA_le_B _hBindex
      hAnormal⟩

set_option maxHeartbeats 800000 in
public theorem
    theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_semidirect_product_structure_source_core_sec9
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
      M MF U H0 C Uprime p q a H hqpos hHcard ρBase hρcycBase hUprimeEq := by
  classical
  let Dm : Subgroup M := (ambientDerivedSubgroup M).subgroupOf M
  let MFD : Subgroup Dm := (MF.subgroupOf M).subgroupOf Dm
  let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
  let fU : U →* ρBase.range :=
    ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
  have h92 : hypothesis_9_2_statement M MF U W1 W2 q :=
    case_9_7_a_hypothesis_9_2_sec9 hcase
  rcases h92.typeP with ⟨_hMFtype, hcommon⟩
  rcases hcommon with
    ⟨hhallD, hMFleD, hcompD, _hnil, _hW1norm, _hW1cyc, _hW1card,
      _hMFnotcyc, _hsecond, _hfitting, _hFittingDer, _hW2le, _hW2ne,
      _hW2cyc, _hcentralizer, _hhat, _hprimeCentralizer, _hW2der⟩
  rcases hhallD with ⟨hDleM, _hDHall⟩
  rcases hcompD with ⟨_hMFleD', hUleD, _hD_eq, _hMFUdisj⟩
  have hMFDnormal : MFD.Normal := by
    simpa [Dm, MFD] using
      theorem_9_8_MF_subgroupOf_ambientDerived_normal_sec9
        M MF U W1 W2 H0 C p q a hcase
  letI : MFD.Normal := hMFDnormal
  have hsemi : Section2.IsInternalSemidirectProduct (⊤ : Subgroup Dm) MFD W := by
    simpa [Dm, MFD, W] using
      theorem_9_8_MF_U_internalSemidirect_ambientDerived_sec9
        M MF U W1 W2 q h92
        (by simpa [Dm, MFD] using hMFDnormal)
  let toU : W →* U := theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9 M U
  let Φ : Dm →* ρBase.range :=
    (fU.comp toU).comp (internalSemidirectRightProjectionTop_sec9 hsemi)
  let B : Subgroup Dm := Φ.ker
  have hBnormal : B.Normal := by
    simpa [B] using MonoidHom.normal_ker Φ
  have hMFleM : MF ≤ M := hMFleD.trans hDleM
  have hUleM : U ≤ M := hUleD.trans hDleM
  have htoU_surj : Function.Surjective toU := by
    intro u0
    let uM : M := ⟨(u0 : G), hUleM u0.property⟩
    let uD : Dm :=
      ⟨uM, by
        simpa [Dm, Subgroup.mem_subgroupOf, uM] using hUleD u0.property⟩
    let uW : W :=
      ⟨uD, by
        change (uD : M) ∈ U.subgroupOf M
        simp [uD, uM, Subgroup.mem_subgroupOf]⟩
    exact ⟨uW, by
      ext
      rfl⟩
  have hΦrange_top : Φ.range = ⊤ := by
    rw [MonoidHom.range_eq_top]
    intro y
    rcases y with ⟨y, hy⟩
    rcases hy with ⟨x, rfl⟩
    rcases QuotientGroup.mk'_surjective (C.subgroupOf U) x with ⟨u0, rfl⟩
    rcases htoU_surj u0 with ⟨w, hw⟩
    refine ⟨(w : Dm), ?_⟩
    ext
    simp [Φ, fU, toU, internalSemidirectRightProjectionTop_apply_right_sec9 hsemi w, hw]
  have hBindex : Subgroup.index B = a := by
    calc
      Subgroup.index B = Nat.card Φ.range := by
        simpa [B] using Subgroup.index_ker Φ
      _ = Nat.card (⊤ : Subgroup ρBase.range) := by rw [hΦrange_top]
      _ = Nat.card ρBase.range := by simp
      _ = a := hρcardBase
  have hMFD_to_B : MFD ≤ B := by
    intro x hx
    change Φ x = 1
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = 1 := by
      simpa using
        internalSemidirectRightProjectionTop_apply_left_sec9 hsemi
          ⟨(x : Dm), hx⟩
    simp [Φ, hproj]
  have hBsemi : Section2.IsInternalSemidirectProduct B MFD (W ⊓ B) := by
    refine
      { left_le := hMFD_to_B
        right_le := inf_le_right
        right_normalizes_left := ?_
        inf_eq_bot := ?_
        mul_surjective := ?_ }
    · intro k hk h hh
      exact hsemi.right_normalizes_left k hk.1 h hh
    · apply le_antisymm
      · intro x hx
        have hxInf : x ∈ MFD ⊓ W := ⟨hx.1, hx.2.1⟩
        have hxBot : x ∈ (⊥ : Subgroup Dm) := by
          simpa [hsemi.inf_eq_bot] using hxInf
        simpa using hxBot
      · exact bot_le
    · intro c hc
      rcases hsemi.mul_surjective c (by trivial) with ⟨m, hm, w, hw, hmw⟩
      have hmB : m ∈ B := hMFD_to_B hm
      have hwB : w ∈ B := by
        have hw_eq : w = m⁻¹ * c := by
          calc
            w = m⁻¹ * (m * w) := by simp
            _ = m⁻¹ * c := by rw [← hmw]
        rw [hw_eq]
        exact B.mul_mem (B.inv_mem hmB) hc
      exact ⟨m, hm, w, ⟨hw, hwB⟩, hmw⟩
  let K : Subgroup U := fU.ker
  let rightToK : ↥(W ⊓ B) →* K :=
    { toFun := fun x => by
        refine ⟨toU ⟨(x : Dm), x.property.1⟩, ?_⟩
        change fU (toU ⟨(x : Dm), x.property.1⟩) = 1
        have hproj :
            internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) =
              (⟨(x : Dm), x.property.1⟩ : W) := by
          simpa using
            internalSemidirectRightProjectionTop_apply_right_sec9 hsemi
              (⟨(x : Dm), x.property.1⟩ : W)
        have hxB : Φ (x : Dm) = 1 := x.property.2
        simpa [Φ, hproj] using hxB
      map_one' := by
        ext
        rfl
      map_mul' := by
        intro x y
        ext
        rfl }
  have hrightToK_inj : Function.Injective rightToK := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : K => ((z : U) : G)) hxy
  have hrightToK_surj : Function.Surjective rightToK := by
    intro k
    let uM : M := ⟨(k : G), hUleM (k : U).property⟩
    let uD : Dm :=
      ⟨uM, by
        simpa [Dm, Subgroup.mem_subgroupOf, uM] using hUleD (k : U).property⟩
    have huW : uD ∈ W := by
      change (uD : M) ∈ U.subgroupOf M
      simp [uD, uM, Subgroup.mem_subgroupOf]
    let uW : W := ⟨uD, huW⟩
    have huB : uD ∈ B := by
      change Φ uD = 1
      have hproj :
          internalSemidirectRightProjectionTop_sec9 hsemi uD = uW := by
        simpa [uW] using internalSemidirectRightProjectionTop_apply_right_sec9 hsemi uW
      have hto : toU uW = (k : U) := by
        ext
        rfl
      calc
        Φ uD = fU (toU uW) := by simp [Φ, hproj]
        _ = fU (k : U) := by rw [hto]
        _ = 1 := k.property
    let x : ↥(W ⊓ B) := ⟨uD, ⟨huW, huB⟩⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    rfl
  let eWBK : ↥(W ⊓ B) ≃* K :=
    MulEquiv.ofBijective rightToK ⟨hrightToK_inj, hrightToK_surj⟩
  have hWBK_compat :
      (let W : Subgroup Dm := (U.subgroupOf M).subgroupOf Dm
       let f : U →* ρBase.range :=
          ρBase.rangeRestrict.comp (QuotientGroup.mk' (C.subgroupOf U))
       let K : Subgroup U := f.ker
       ∀ x : ↥(W ⊓ B),
        (((eWBK x : K) : U) : G) = ((((x : Dm) : M) : G))) := by
    dsimp
    intro x
    change (((rightToK x : K) : U) : G) = ((((x : Dm) : M) : G))
    simp [rightToK, toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9]
  have hH0MF : H0 ≤ MF := case_9_7_a_H0_le_MF_sec9 hcase
  have hUprimeU : Uprime ≤ U := by
    rw [hUprimeEq, Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le_self U
  have hUprimeNormal : (Uprime.subgroupOf U).Normal :=
    theorem_9_8_initial_constituent_Mtheta_uprime_subgroupOf_normal_sec9
      U Uprime hUprimeEq
  have hH0leM : H0 ≤ M := hH0MF.trans hMFleM
  have hUprimeleM : Uprime ≤ M := hUprimeU.trans hUleM
  have hH0subD : H0.subgroupOf M ≤ Dm := by
    intro x hx
    have hxH0 : ((x : M) : G) ∈ H0 := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact (hH0MF.trans hMFleD) hxH0
  have hUprimeSubD : Uprime.subgroupOf M ≤ Dm := by
    intro x hx
    have hxUprime : ((x : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    exact (hUprimeU.trans hUleD) hxUprime
  have hUprime_le_fUker : Uprime.subgroupOf U ≤ fU.ker := by
    simpa [fU] using
      theorem_9_8_initial_constituent_Mtheta_baseActionKernel_uprime_le_sec9
        U C Uprime ρBase hρcycBase hUprimeEq
  let Hsub : Subgroup K := (Uprime.subgroupOf U).subgroupOf K
  let UprimeD : Subgroup Dm := (Uprime.subgroupOf M).subgroupOf Dm
  let WBUprime : Subgroup ↥(W ⊓ B) := UprimeD.subgroupOf (W ⊓ B)
  have hWBUprime_eq_comap : WBUprime = Hsub.comap eWBK.toMonoidHom := by
    ext x
    constructor
    · intro hxWBU
      have hxUprimeD : (x : Dm) ∈ UprimeD := by
        simpa [WBUprime, Subgroup.mem_subgroupOf] using hxWBU
      have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
        simpa [UprimeD, Subgroup.mem_subgroupOf] using hxUprimeD
      change ((eWBK x : K) : U) ∈ Uprime.subgroupOf U
      change ((rightToK x : K) : U) ∈ Uprime.subgroupOf U
      change ((toU ⟨(x : Dm), x.property.1⟩ : U) : G) ∈ Uprime
      simpa [toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hxUprime
    · intro hk
      change ((eWBK x : K) : U) ∈ Uprime.subgroupOf U at hk
      change ((rightToK x : K) : U) ∈ Uprime.subgroupOf U at hk
      change ((toU ⟨(x : Dm), x.property.1⟩ : U) : G) ∈ Uprime at hk
      have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
        simpa [toU, theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hk
      simpa [WBUprime, UprimeD, Subgroup.mem_subgroupOf] using hxUprime
  let WBHsub : Subgroup ↥(W ⊓ B) := Hsub.comap eWBK.toMonoidHom
  have hWBHsub_map : WBHsub.map eWBK.toMonoidHom = Hsub := by
    exact Subgroup.map_comap_eq_self_of_surjective eWBK.surjective Hsub
  letI : Hsub.Normal := hUprimeNormal.subgroupOf K
  letI : WBHsub.Normal := (hUprimeNormal.subgroupOf K).comap eWBK.toMonoidHom
  let hWBHsubQuot : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub) := by
    exact QuotientGroup.congr WBHsub Hsub eWBK hWBHsub_map
  have hWBHsubQuot_apply :
      ∀ x : ↥(W ⊓ B),
        hWBHsubQuot (QuotientGroup.mk' WBHsub x) =
          QuotientGroup.mk' Hsub (eWBK x) := by
    intro x
    exact QuotientGroup.congr_mk' WBHsub Hsub eWBK hWBHsub_map x
  have hWBKquot :
      ∃ eWBHsub : (↥(W ⊓ B) ⧸ WBHsub) ≃* (K ⧸ Hsub),
        WBUprime = WBHsub ∧
          ∀ x : ↥(W ⊓ B),
            eWBHsub (QuotientGroup.mk' WBHsub x) =
              QuotientGroup.mk' Hsub (eWBK x) :=
    ⟨hWBHsubQuot, hWBUprime_eq_comap, hWBHsubQuot_apply⟩
  have hH0_to_B : (H0.subgroupOf M).subgroupOf Dm ≤ B := by
    intro x hx
    change Φ x = 1
    have hxMFD : (x : Dm) ∈ MFD := by
      have hxH0 : (((x : Dm) : M) : G) ∈ H0 := by
        simpa [Subgroup.mem_subgroupOf] using hx
      exact hH0MF hxH0
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = 1 := by
      simpa using
        internalSemidirectRightProjectionTop_apply_left_sec9 hsemi
          ⟨(x : Dm), hxMFD⟩
    simp [Φ, hproj]
  have hUprime_to_B : (Uprime.subgroupOf M).subgroupOf Dm ≤ B := by
    intro x hx
    change Φ x = 1
    have hxUprime : (((x : Dm) : M) : G) ∈ Uprime := by
      simpa [Subgroup.mem_subgroupOf] using hx
    have hxW : (x : Dm) ∈ W := by
      exact hUprimeU hxUprime
    let w : W := ⟨(x : Dm), hxW⟩
    have hproj :
        internalSemidirectRightProjectionTop_sec9 hsemi (x : Dm) = w := by
      simpa [w] using internalSemidirectRightProjectionTop_apply_right_sec9 hsemi w
    have htoU_Uprime : toU w ∈ Uprime.subgroupOf U := by
      change ((toU w : U) : G) ∈ Uprime
      simpa [toU, w,
        theorem_9_8_ambientDerived_U_subgroupOf_to_U_sec9] using hxUprime
    have hfU : fU (toU w) = 1 := hUprime_le_fUker htoU_Uprime
    calc
      Φ x = fU (toU w) := by simp [Φ, hproj]
      _ = 1 := hfU
  let A : Subgroup Dm := (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm)
  have hA_le_B : A ≤ B := by
    change (((H0 ⊔ Uprime).subgroupOf M).subgroupOf Dm) ≤ B
    rw [Subgroup.subgroupOf_sup (A := H0) (A' := Uprime) (B := M)
      hH0leM hUprimeleM]
    rw [Subgroup.subgroupOf_sup (A := H0.subgroupOf M)
      (A' := Uprime.subgroupOf M) (B := Dm) hH0subD hUprimeSubD]
    exact sup_le hH0_to_B hUprime_to_B
  rcases
      theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_canonical_quotient_product_source_core_sec9
        M MF U W1 W2 H0 C Uprime p q a u H hqpos hHcard hHnorm hHindep hHsup
        ρBase hρcycBase hρcardBase hρactionBase hρkerBase hconjBase hcase hBarU
        hUprimeEq B hBnormal (by simpa [MFD, W, B] using hBsemi)
        (by simpa [W, fU, K] using eWBK)
        (by simpa [W, fU, K] using hWBK_compat)
        (by
          dsimp
            [theorem_9_8_initial_constituent_Mtheta_clam_kernel_quotient_theta_right_factor_quotient_bridge_data_sec9]
          simpa [W, fU, K, Hsub, UprimeD, WBUprime, WBHsub] using hWBKquot)
        (by simpa [A] using hA_le_B) hBindex with
      ⟨hAnormal, QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, eH1, eClam,
        hQH1_apply, hQH1c_apply, hQClam_apply, QMF, hQMF_eq, hQMF_split_in_Q,
        hQH1_le_QMF⟩
  exact
    ⟨B, hBnormal, hAnormal, by simpa [A] using hA_le_B, hBindex,
      by simpa [MFD] using hMFD_to_B,
      by simpa [MFD, W, B] using hBsemi,
      by simpa [W, fU, K] using eWBK,
      by simpa [W, fU, K] using hWBK_compat,
      QMF, QH1c, QH1, QClam, QH1CH1, hsemiQ, hprod, eH1, eClam,
      hQH1_apply, hQH1c_apply, hQClam_apply, hQMF_eq, hQMF_split_in_Q,
      hQH1_le_QMF⟩


end CFSG.Section9
