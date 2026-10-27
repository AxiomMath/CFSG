module

public import CFSG.Monster.B.GSide.EdgeData
import all CFSG.Fischer.F4

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Fischer CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam CFSG.Monster.B.TwoA.Unitary
  CFSG.Blueprint.Chevalley Module Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar bar_bar bar_zero bar_eq_zero_iff IsFrame herm
  exists_SU_lines_of_frame isIsometry_of_mem det_of_mem)
open CFSG.Monster.B.Classical.UnitaryPanels (exists_eq_span_singleton_of_finrank_eq_one)

theorem natCard_Qam_three :
    Nat.card (Qam 3) = Nat.card Bam * 5 := by
  let i₃ : Fin Tag.F4.rank := ⟨3, by decide⟩
  have h1 := natCard_eq_mul_ncard_image (Bam_le_resGroup {i₃})
  rw [← residue_chamberOf_one (X := chamberCS) mem_residue_chamberCS_iff, chamberCS_ncard_panel,
    natCard_resGroup] at h1
  have e : ({i₃} : Set (Fin Tag.F4.rank)) =
      {k : Fin Tag.F4.rank | (k : ℕ) = ((3 : Fin 4) : ℕ)} := by
    ext k
    simp only [Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact Fin.ext_iff
  rw [e, parJ_eq_Qam] at h1
  exact h1

theorem relIndex_Bam_Qam_three :
    Bam.relIndex (Qam 3) = 5 := by
  have h := Bam.relIndex_mul_card (Qam 3)
  rw [inf_eq_left.2 (Bam_le_Qam 3), natCard_Qam_three, mul_comm] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem Qam_three_le_of_mem
    {X : Subgroup Dfull} (hB : Bam ≤ X) {q : Dfull} (hq : q ∈ Qam 3)
    (hqB : q ∉ Bam) (hqX : q ∈ X) : Qam 3 ≤ X := by
  have h := Subgroup.relIndex_mul_relIndex Bam (X ⊓ Qam 3) (Qam 3) (le_inf hB (Bam_le_Qam 3))
    inf_le_right
  rw [relIndex_Bam_Qam_three] at h
  have hne : Bam.relIndex (X ⊓ Qam 3) ≠ 1 := fun h1 =>
    hqB (Subgroup.relIndex_eq_one.1 h1 ⟨hqX, hq⟩)
  have h5 : Bam.relIndex (X ⊓ Qam 3) = 5 :=
    ((Nat.dvd_prime (by norm_num)).1 (Dvd.intro _ h)).resolve_left hne
  rw [h5] at h
  have h1 : (X ⊓ Qam 3).relIndex (Qam 3) = 1 := by omega
  exact (Subgroup.relIndex_eq_one.1 h1).trans inf_le_left

theorem Pc_zero_le_of_Qam_three
    {X : Subgroup Dfull} (hK : Pc 0 ⊓ Pc 3 ≤ X) (hQ : Qam 3 ≤ X) :
    Pc 0 ≤ X := by
  rw [Pc_eq_iSup_Qam 0]
  refine iSup₂_le fun j hj => ?_
  by_cases h3 : j = 3
  · rw [h3]
    exact hQ
  · exact (le_inf (Qam_le_Pc (Ne.symm hj)) (Qam_le_Pc (Ne.symm h3))).trans hK

theorem Pc_zero_inf_Pc_three :
    Pc 0 ⊓ Pc 3 = parJ (pairOff 0 3) :=
  Pc_inf_Pc_eq (X := chamberCS) chamberCS_hpanel chamberCS_hres2 chamberCS_hres3
    chamberCS_encard_panel mem_residue_chamberCS_iff Pc_eq_iSup_Qam 0 3 (by decide)

theorem hU_eq_zero_of_mem_span {x y s t : V6} (hxy : hU x y = 0)
    (hs : s ∈ Submodule.span F4 {x}) (ht : t ∈ Submodule.span F4 {y}) : hU s t = 0 := by
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hs
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 ht
  rw [hU_smul_left, hU_smul_right, hxy, mul_zero, mul_zero]

theorem uIso_one_span {x : V6} (hx0 : x ≠ 0) (hx : hU x x = 0) :
    UIso 1 (Submodule.span F4 {x}) :=
  ⟨finrank_span_singleton hx0, fun _ hs _ ht => hU_eq_zero_of_mem_span hx hs ht⟩

theorem span_singleton_ne_of_apply {x y : V6} {j : Fin 6} (hx : x j = 0) (hy : y j ≠ 0) :
    Submodule.span F4 {y} ≠ Submodule.span F4 {x} := fun h => by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self y)
  apply hy
  rw [← hc, Pi.smul_apply, hx, smul_zero]

theorem uIso_two_sup {R₁ R₂ : Submodule F4 V6} (h₁ : UIso 1 R₁) (h₂ : UIso 1 R₂)
    (hne : R₁ ≠ R₂) (horth : ∀ s ∈ R₁, ∀ t ∈ R₂, hU s t = 0) : UIso 2 (R₁ ⊔ R₂) := by
  refine ⟨?_, fun s hs t ht => ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq R₁ R₂
    have hle := Submodule.finrank_mono (inf_le_left : R₁ ⊓ R₂ ≤ R₁)
    have hinf : finrank F4 ↥(R₁ ⊓ R₂) = 0 := by
      by_contra h0
      have e₁ : finrank F4 ↥(R₁ ⊓ R₂) = finrank F4 R₁ := by rw [h₁.1] at hle ⊢; omega
      have e₂ : finrank F4 ↥(R₁ ⊓ R₂) = finrank F4 R₂ := by rw [h₂.1, ← h₁.1]; exact e₁
      exact hne ((Submodule.eq_of_le_of_finrank_eq inf_le_left e₁).symm.trans
        (Submodule.eq_of_le_of_finrank_eq inf_le_right e₂))
    rw [hinf, h₁.1, h₂.1] at h
    omega
  · obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
    obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.1 ht
    have e : hU z y' = 0 := by rw [hU_swap y' z, horth y' hy' z hz, bar_zero]
    rw [hU_add_left, hU_add_right, hU_add_right, h₁.2 y hy y' hy', horth y hy z' hz', e,
      h₂.2 z hz z' hz', add_zero, add_zero]

theorem Pc_zero_le_of_collinear
    {X : Subgroup Dfull} (hK : Pc 0 ⊓ Pc 3 ≤ X) {a : Pc 0}
    (haX : (a : Dfull) ∈ X) (hne : actP1 a Rsp ≠ Rsp) {L : Submodule F4 V6} (hL : UIso 2 L)
    (hRL : Rsp ≤ L) (haL : actP1 a Rsp ≤ L) : Pc 0 ≤ X := by
  have mem3 : ∀ x : Pc 0, actP1 x Rsp = Rsp → (x : Dfull) ∈ Pc 0 ⊓ Pc 3 := fun x hx =>
    ⟨x.2, Subgroup.mem_subgroupOf.1 ((actP1_Rsp_iff x).1 hx)⟩
  obtain ⟨-, T', -, hT', -, hLT⟩ := exists_flag_of_two hL
  obtain ⟨g, hgR, hgH, -⟩ := exists_actP1_flag uIso_Rsp hL hT' hRL hLT
  have hR'H : actP1 g⁻¹ (actP1 a Rsp) ≤ Hsp := by
    have h1 := actP1_mono haL g⁻¹
    rwa [← hgH, actP1_inv_actP1] at h1
  obtain ⟨h, hhR, hhH, hhT⟩ := exists_actP1_flag ((uIso_Rsp.actP1 a).actP1 g⁻¹) uIso_Hsp
    uIso_Tsp hR'H Hsp_le_Tsp
  have hhQ : (h : Dfull) ∈ Qam 3 := by
    refine mem_Qam_iff.2 fun k hk => ?_
    fin_cases k
    · exact h.2
    · exact Subgroup.mem_subgroupOf.1 ((actP1_Tsp_iff h).1 hhT)
    · exact Subgroup.mem_subgroupOf.1 ((actP1_Hsp_iff h).1 hhH)
    · exact absurd rfl hk
  have hhB : (h : Dfull) ∉ Bam := fun hB => by
    have h3 : actP1 h Rsp = Rsp :=
      (actP1_Rsp_iff h).2 (Subgroup.mem_subgroupOf.2 (Bam_le_Pc 3 hB))
    have h4 := congrArg (actP1 g) (h3.symm.trans hhR)
    rw [← actP1_mul, mul_inv_cancel, actP1_one, hgR] at h4
    exact hne h4.symm
  have hk : actP1 ((g * h)⁻¹ * a) Rsp = Rsp := by
    rw [actP1_mul, _root_.mul_inv_rev, actP1_mul, ← hhR, actP1_inv_actP1]
  have hhX : (h : Dfull) ∈ X := by
    have e : h = g⁻¹ * a * ((g * h)⁻¹ * a)⁻¹ := by group
    have h5 := X.mul_mem (X.mul_mem (X.inv_mem (hK (mem3 g hgR))) haX)
      (X.inv_mem (hK (mem3 _ hk)))
    rw [e]
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h5
  exact Pc_zero_le_of_Qam_three hK
    (Qam_three_le_of_mem ((le_inf (Bam_le_Pc 0) (Bam_le_Pc 3)).trans hK) hhQ hhB hhX)

theorem exists_SUh_hyperbolic {v w : V6} (hv : hU v v = 0) (hw : hU w w = 0)
    (hvw : hU v w = 1) :
    ∃ g : SUh,
      (∃ c : F4, c ≠ 0 ∧ e6 2 ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = c • v) ∧
        ∃ d : F4, d ≠ 0 ∧ e6 5 ᵥ* ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) = d • w := by
  have h1 : herm (swV v) (swV v) = 0 := by rw [herm_swV]; exact hv
  have h2 : herm (swV w) (swV w) = 0 := by rw [herm_swV]; exact hw
  have h3 : herm (swV v) (swV w) = 1 := by rw [herm_swV]; exact hvw
  obtain ⟨e, he, e0, e5⟩ :=
    CFSG.Monster.B.Classical.UnitarySix.exists_frame_of_hyperbolic h1 h2 h3
  have he' : IsFrame fun i => e (![2, 1, 0, 5, 4, 3] i) := isFrame_comp he _ (by decide)
  obtain ⟨g, hg⟩ := exists_SU_lines_of_frame he'
  set G : Matrix (Fin 6) (Fin 6) F4 := ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)
  have hdet : (rowConj G).det = 1 := by rw [det_rowConj]; exact det_of_mem g
  have hA : GeneralLinearGroup.mkOfDetNeZero (rowConj G) (by rw [hdet]; exact one_ne_zero) ∈
      SUh := by
    refine ⟨hdet, fun s t => ?_⟩
    change hU (s ᵥ* rowConj G) (t ᵥ* rowConj G) = hU s t
    rw [vecMul_rowConj, vecMul_rowConj, hU_swV, isIsometry_of_mem g, herm_swV]
  refine ⟨⟨_, hA⟩, ?_, ?_⟩
  · obtain ⟨c, hc0, hc⟩ := hg 2
    refine ⟨c, hc0, ?_⟩
    change e6 2 ᵥ* rowConj G = c • v
    rw [vecMul_rowConj, show swV (e6 2) = Pi.single 2 1 by decide +kernel, hc]
    change c • swV (e 0) = c • v
    rw [e0, swV_swV]
  · obtain ⟨d, hd0, hd⟩ := hg 3
    refine ⟨d, hd0, ?_⟩
    change e6 5 ᵥ* rowConj G = d • w
    rw [vecMul_rowConj, show swV (e6 5) = Pi.single 3 1 by decide +kernel, hd]
    change d • swV (e 5) = d • w
    rw [e5, swV_swV]

theorem exists_actP1_hyperbolic
    {r : V6} (hr : hU r r = 0) (h2r : hU (e6 2) r ≠ 0) :
    ∃ g : Pc 0, actP1 g Rsp = Rsp ∧
      actP1 g (Submodule.span F4 {e6 5}) = Submodule.span F4 {r} := by
  set c : F4 := bar (hU (e6 2) r)⁻¹ with hc
  have hc0 : c ≠ 0 := fun h => inv_ne_zero h2r (bar_eq_zero_iff.1 h)
  have hvw : hU (e6 2) (c • r) = 1 := by
    rw [hU_smul_right, hc, bar_bar, inv_mul_cancel₀ h2r]
  have hw : hU (c • r) (c • r) = 0 := by
    rw [hU_smul_left, hU_smul_right, hr, mul_zero, mul_zero]
  obtain ⟨g', ⟨c₁, hc₁, h₁⟩, d, hd, h₂⟩ :=
    exists_SUh_hyperbolic (by decide +kernel : hU (e6 2) (e6 2) = 0) hw hvw
  obtain ⟨g, hg⟩ := exists_actP1_eq (suElt g')
  refine ⟨g, ?_, ?_⟩
  · rw [hg, Rsp, sigmaAct_suElt_span, Set.image_singleton, h₁, span_smul_one hc₁]
  · rw [hg, sigmaAct_suElt_span, Set.image_singleton, h₂, span_smul_one hd, span_smul_one hc0]

@[expose] def shiftMat : Matrix (Fin 6) (Fin 6) F4 := 1 + Matrix.single 4 2 1 + Matrix.single 5 1 1

theorem shiftMat_det : shiftMat.det = 1 := by decide +kernel

theorem shiftMat_gram : shiftMat * hGram * (barM shiftMat)ᵀ = hGram := by decide +kernel

@[expose] def shiftSU : SUh :=
  ⟨GeneralLinearGroup.mkOfDetNeZero shiftMat (by rw [shiftMat_det]; exact one_ne_zero),
    mem_SUh_iff_gram.2 ⟨shiftMat_det, shiftMat_gram⟩⟩

theorem e6_two_vecMul_shiftMat : e6 2 ᵥ* shiftMat = e6 2 := by decide +kernel

theorem e6_five_vecMul_shiftMat : e6 5 ᵥ* shiftMat = e6 5 + e6 1 := by decide +kernel

theorem exists_actP1_shift :
    ∃ g : Pc 0, actP1 g Rsp = Rsp ∧
      actP1 g (Submodule.span F4 {e6 5}) = Submodule.span F4 {e6 5 + e6 1} := by
  obtain ⟨g, hg⟩ := exists_actP1_eq (suElt shiftSU)
  refine ⟨g, ?_, ?_⟩
  · rw [hg, Rsp, sigmaAct_suElt_span, Set.image_singleton]
    exact congrArg (fun x => Submodule.span F4 {x}) e6_two_vecMul_shiftMat
  · rw [hg, sigmaAct_suElt_span, Set.image_singleton]
    exact congrArg (fun x => Submodule.span F4 {x}) e6_five_vecMul_shiftMat

theorem Pc_zero_le_of_not_mem_Pc_three
    {X : Subgroup Dfull} (hK : Pc 0 ⊓ Pc 3 ≤ X) {a : Dfull}
    (ha : a ∈ Pc 0) (ha3 : a ∉ Pc 3) (haX : a ∈ X) : Pc 0 ≤ X := by
  set a' : Pc 0 := ⟨a, ha⟩ with ha'
  have hmem : ∀ x : Pc 0, actP1 x Rsp = Rsp → (x : Dfull) ∈ X := fun x hx =>
    hK ⟨x.2, Subgroup.mem_subgroupOf.1 ((actP1_Rsp_iff x).1 hx)⟩
  have hne : actP1 a' Rsp ≠ Rsp := fun h =>
    ha3 (Subgroup.mem_subgroupOf.1 ((actP1_Rsp_iff a').1 h))
  have hR' := uIso_Rsp.actP1 a'
  obtain ⟨r, -, hRr⟩ := exists_eq_span_singleton_of_finrank_eq_one hR'.1
  have hr : r ∈ actP1 a' Rsp := by
    rw [hRr]
    exact Submodule.mem_span_singleton_self r
  have hrr : hU r r = 0 := hR'.2 r hr r hr
  by_cases h2 : hU (e6 2) r = 0
  ·
    refine Pc_zero_le_of_collinear hK haX hne
      (uIso_two_sup uIso_Rsp hR' hne.symm fun s hs t ht => ?_) le_sup_left le_sup_right
    rw [hRr] at ht
    exact hU_eq_zero_of_mem_span h2 hs ht
  ·
    obtain ⟨g, hgR, hg5⟩ := exists_actP1_hyperbolic hrr h2
    obtain ⟨k, hkR, hk5⟩ := exists_actP1_shift
    set x : Pc 0 := g⁻¹ * a' with hx
    have hxX : (x : Dfull) ∈ X := X.mul_mem (X.inv_mem (hmem g hgR)) haX
    have hx5 : actP1 x Rsp = Submodule.span F4 {e6 5} := by
      rw [hx, actP1_mul, hRr, ← hg5, actP1_inv_actP1]
    have hbX : ((x⁻¹ * k * x : Pc 0) : Dfull) ∈ X :=
      X.mul_mem (X.mul_mem (X.inv_mem hxX) (hmem k hkR)) hxX
    have hbR : actP1 (x⁻¹ * k * x) Rsp = actP1 x⁻¹ (Submodule.span F4 {e6 5 + e6 1}) := by
      rw [actP1_mul, actP1_mul, hx5, hk5]
    have hx5' : actP1 x⁻¹ (Submodule.span F4 {e6 5}) = Rsp := by
      rw [← hx5, actP1_inv_actP1]
    have hL : UIso 2 (Submodule.span F4 {e6 5} ⊔ Submodule.span F4 {e6 1}) :=
      uIso_two_sup (uIso_one_span (e6_ne_zero 5) (by decide +kernel))
        (uIso_one_span (e6_ne_zero 1) (by decide +kernel))
        (span_singleton_ne_of_apply (j := 5) (by decide +kernel) (by decide +kernel))
        fun s hs t ht => hU_eq_zero_of_mem_span (by decide +kernel) hs ht
    have hle : Submodule.span F4 {e6 5 + e6 1} ≤
        Submodule.span F4 {e6 5} ⊔ Submodule.span F4 {e6 1} :=
      (Submodule.span_singleton_le_iff_mem _ _).2
        (Submodule.add_mem_sup (Submodule.mem_span_singleton_self _)
          (Submodule.mem_span_singleton_self _))
    refine Pc_zero_le_of_collinear hK hbX ?_ (hL.actP1 x⁻¹) ?_ ?_
    · rw [hbR]
      intro h
      have h' := congrArg (actP1 x) h
      rw [← actP1_mul, mul_inv_cancel, actP1_one, hx5] at h'
      exact span_singleton_ne_of_apply (j := 1) (by decide +kernel) (by decide +kernel) h'
    · rw [← hx5']
      exact actP1_mono le_sup_left x⁻¹
    · rw [hbR]
      exact actP1_mono hle x⁻¹

theorem parJ_sup_zpowers_eq_Pc_zero
    {a : Dfull} (ha : a ∈ Pc 0) (ha3 : a ∉ Pc 3) :
    parJ (pairOff 0 3) ⊔ Subgroup.zpowers a = Pc 0 := by
  rw [← Pc_zero_inf_Pc_three]
  exact le_antisymm (sup_le inf_le_left ((Subgroup.zpowers_le).2 ha))
    (Pc_zero_le_of_not_mem_Pc_three le_sup_left ha ha3
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))

theorem cEdgeFix_le_of_not_mem_Pc_three
    {X : Subgroup Shat}
    (hK : ∀ g ∈ cEdgeFix, (g : Dfull) ∈ Pc 3 → g ∈ X) {a : Shat} (ha : a ∈ cEdgeFix)
    (ha3 : (a : Dfull) ∉ Pc 3) (haX : a ∈ X) : cEdgeFix ≤ X := by
  have h := Pc_zero_le_of_not_mem_Pc_three (X := X.map Shat.subtype)
    (fun d hd => ⟨⟨d, Pc_le_Shat 0 hd.1⟩, hK _ (mem_cEdgeFix_iff.2 hd.1) hd.2, rfl⟩)
    (mem_cEdgeFix_iff.1 ha) ha3 ⟨a, haX, rfl⟩
  intro g hg
  obtain ⟨y, hy, hyg⟩ := h (mem_cEdgeFix_iff.1 hg)
  rwa [Subtype.ext hyg] at hy

theorem not_mem_Pc_three_of_cvMul_not_mem_cSigma
    {a : Shat} {v : CVert} (hv : v ∈ cSigma 1)
    (hva : cvMul v a ∉ cSigma 1) : (a : Dfull) ∉ Pc 3 := by
  intro h3
  rw [Pc_three] at h3
  obtain ⟨x, hx, rfl⟩ := hv
  refine hva ⟨x * a, Sp8.Xgrp.mul_mem hx h3.1, ?_⟩
  rw [cvMul_cvOf, mul_one, mul_one]

theorem cEdgeFix_le_of_cvMul_not_mem_cSigma
    {X : Subgroup Shat}
    (hK : ∀ g ∈ cEdgeFix, (g : Dfull) ∈ Pc 3 → g ∈ X) {a : Shat} (ha : a ∈ cEdgeFix)
    (haX : a ∈ X) {v : CVert} (hv : v ∈ cSigma 1) (hva : cvMul v a ∉ cSigma 1) :
    cEdgeFix ≤ X :=
  cEdgeFix_le_of_not_mem_Pc_three hK ha (not_mem_Pc_three_of_cvMul_not_mem_cSigma hv hva) haX

end CFSG.Monster.B.GSide
