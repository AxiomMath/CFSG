module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4IDMain
public import CFSG.Quasithin.Vol2.Ch11SecSZK
public import CFSG.Quasithin.Vol2.Ch1EightFourMain
public import CFSG.Quasithin.Vol2.Ch1Sec3L42Cases
public import CFSG.Quasithin.Vol2.Ch11SecE42S1a
public import CFSG.Quasithin.EmptyFaithful.S14620G
public import CFSG.Open.StatedZModTwo

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.QuasithinUnique

theorem isPSL_four_two_of_nonempty {X : Type} [Group X]
    (h : Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))) : IsPSL 4 2 1 X := by
  obtain ⟨e⟩ := h
  let eS : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* CFSG.Open.StatedSL 4 (ZMod 2) :=
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).trans
      (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 4 (ZMod 2)).symm)
  exact CFSG.Open.StatedAPI.statedClassicalModel_psl_of_mulEquiv_statedSL_zmod_two (by norm_num)
    (e.trans eS)

theorem trichotomy_of_a312 {G : Type} [Group G] [Finite G] {H S B L : Subgroup G}
    (h312 : CFSG.Quasithin.A312Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hS : IsSylowTwoOf S H)
    (hBH : B ≤ H) (hB : B ∈ CFSG.Quasithin.lFamily S) (hL : L ∈ CFSG.Quasithin.cComp H)
    (hBL : B ≤ L) :
    CFSG.Quasithin.modO2Image H B = CFSG.Quasithin.modO2Image H L ∨
      CFSG.Quasithin.A312Case (CFSG.Quasithin.modO2Image H B) (CFSG.Quasithin.modO2Image H L) ∨
      CFSG.Quasithin.A312Nonquasi (CFSG.Quasithin.modO2Image H B)
        (CFSG.Quasithin.modO2Image H L) := by
  have hSbar := CFSG.Quasithin.isSylowTwoOf_top_map_of_surjective
    (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hS) (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    (QuotientGroup.mk'_surjective _)
  obtain ⟨L', -, -, huniq, hlist⟩ :=
    h312 _ hSbar _ (CFSG.Quasithin.modO2Image_mem_lFamily hS hBH hB)
  have hBLbar : CFSG.Quasithin.modO2Image H B ≤ CFSG.Quasithin.modO2Image H L :=
    Subgroup.map_mono (fun x hx => hBL hx)
  have heq : CFSG.Quasithin.modO2Image H L = L' :=
    huniq _ (CFSG.Quasithin.modO2Image_mem_cComp hL) hBLbar
  rw [heq]
  exact hlist

theorem lemma12_9_4Overgroup_of
    (h37 : CFSG.Quasithin.A37ForSQTK) (h128 : CFSG.Quasithin.Lemma128One)
    (h312 : CFSG.Quasithin.A312ForSQTK) : Lemma12_9_4Overgroup := by
  intro G _ _ T L V hcx K hKf hK4
  have hyp := hcx.hyp.hyp
  obtain ⟨Kp, hKKp, hmax, hfKp⟩ := CFSG.Quasithin.Vol2.Ch11.SecS.exists_maximalFaithful_ge
    hyp.qtke hyp.simple hyp.nonabelian h37 h128 hyp.sylow hKf
  have hLc : Kp ∈ CFSG.Quasithin.cComp (Kp ⊔ T) := hfKp.1.2.1
  have hT : IsSylowTwoOf T (Kp ⊔ T) := ⟨le_sup_right, hfKp.1.1, hfKp.1.2.2.1⟩
  have hBH : K ≤ Kp ⊔ T := hKKp.trans le_sup_left
  have hB : K ∈ CFSG.Quasithin.lFamily T := hKf.1.2.1
  have hG' := CFSG.Quasithin.sqtkHyp_quotient_of_pCoreOf_ne_bot hyp.qtke hyp.simple
    hyp.nonabelian hfKp.1.2.2.2
  haveI : Group.IsPerfect ↥K := CFSG.Quasithin.A36A.isPerfect_of_mem_cComp hKf.1.2.1
  have hBLs : CFSG.Quasithin.modO2Image (Kp ⊔ T) K ≤ CFSG.Quasithin.modO2Image (Kp ⊔ T) Kp :=
    Subgroup.map_mono fun x hx => hKKp hx
  have h4 : IsPSL 4 2 1 (CFSG.Quasithin.ModO2 (CFSG.Quasithin.modO2Image (Kp ⊔ T) K)) := by
    obtain ⟨e₁⟩ := CFSG.Quasithin.Vol2.Ch11.SecE.nonempty_modO2_modO2Image_equiv hBH
    obtain ⟨e₂⟩ := hK4
    exact isPSL_four_two_of_nonempty ⟨e₁.trans e₂⟩
  have hperf : Group.IsPerfect ↥(CFSG.Quasithin.modO2Image (Kp ⊔ T) K) := by
    let σ : ↥K →* ↥(CFSG.Quasithin.modO2Image (Kp ⊔ T) K) :=
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T))).subgroupMap (K.subgroupOf (Kp ⊔ T))).comp
        (Subgroup.subgroupOfEquivOfLe hBH).symm.toMonoidHom
    have hσs : Function.Surjective σ :=
      (MonoidHom.subgroupMap_surjective _ _).comp
        (Subgroup.subgroupOfEquivOfLe hBH).symm.surjective
    exact Group.IsPerfect.ofSurjective (f := σ) hσs
  rcases trichotomy_of_a312 (h312 _ hG') hT hBH hB hLc hKKp with heq | hA | hN
  ·
    exact ⟨Kp, hKKp, hmax, hfKp,
      Or.inl (CFSG.Quasithin.Ch1Four.eq_of_modO2Image_eq hKf.1 hfKp.1 hKKp heq).symm⟩
  ·
    obtain ⟨eL⟩ := CFSG.Quasithin.modO2_mulEquiv hLc
    rcases CFSG.Quasithin.L139L42.cases_of_psl42 h4 hA with ⟨h5, -⟩ | ⟨-, hM⟩ | hJ
    · obtain ⟨e5⟩ := CFSG.Quasithin.nonempty_mulEquiv_sl_of_isPSL h5
      exact ⟨Kp, hKKp, hmax, hfKp, Or.inr (Or.inl ⟨eL.trans e5⟩)⟩
    · obtain ⟨eM⟩ := hM
      exact ⟨Kp, hKKp, hmax, hfKp, Or.inr (Or.inr (Or.inl ⟨eL.trans eM⟩))⟩
    · obtain ⟨eJ⟩ := hJ
      exact ⟨Kp, hKKp, hmax, hfKp, Or.inr (Or.inr (Or.inr ⟨eL.trans eJ⟩))⟩
  ·
    exact (CFSG.Quasithin.L139L42.false_of_nonquasi_psl42 hBLs hperf h4 hN).elim

end CFSG.Quasithin.H13.C1294
