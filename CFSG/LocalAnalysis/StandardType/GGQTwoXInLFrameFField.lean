module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAmbDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGK0MarkedArithmetic
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5L2Rank

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev ggQTwoTCJProp (lab : LargeEvenLabel) : LargeEvenRawCont :=
  fun R _ I _ => ∀ (L' : Type) [Group L'] [Finite L'],
    ∀ (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
      commutator L' = ⊤ → ∀ e : MulAut L', e ^ 3 = 1 →
        (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
            ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
              GGHasLabel labJ (J ⧸ Subgroup.center J)

private theorem label_iso_n_eq_or_exc {labJ labL : LargeEvenLabel}
    (hiso : GGLabelIso labJ labL) (hL1 : labL.n = 1) (_hJ1 : 1 ≤ labJ.n) :
    labJ.n = labL.n ∨ (labJ = ⟨.A, 1, 2⟩ ∧ labL = ⟨.twD, 2, 1⟩) := by
  unfold GGLabelIso at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · exact Or.inl (by rw [h])
  · exact Or.inl h.2.2.2
  · exact Or.inl (congrArg LargeEvenLabel.n h.2).symm
  · exact Or.inl (congrArg LargeEvenLabel.n h.2).symm
  · exact Or.inl (congrArg LargeEvenLabel.n h.2).symm
  · exact Or.inl (congrArg LargeEvenLabel.n h.2).symm
  · exfalso
    have hLn : labL.n = 2 * labJ.n := congrArg LargeEvenLabel.n h.2
    omega
  · refine Or.inr ⟨?_, ?_⟩
    · calc labJ = ⟨.A, 1, 2 * labL.n⟩ := h.2
        _ = ⟨.A, 1, 2⟩ := by rw [hL1]
    · calc labL = ⟨.twD, 2, labL.n⟩ := h.1
        _ = ⟨.twD, 2, 1⟩ := by rw [hL1]

private theorem innerDiagQTwo_data {G : Type} [Group G] {L : Subgroup G} {Bs : Subgroup G}
    (h : GGInnerDiagOnLabel GGLabQTwo 3 Bs L) :
    ∃ labL : LargeEvenLabel, LargeEvenInLambda2 labL ∧ labL.n = 1 ∧
      GGHasLabel labL (↥L ⧸ Subgroup.center ↥L) ∧
      Bs ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, labL, hlabL, hrawL⟩ := h
  obtain ⟨R, _, I, F, _, _, θ, hq, hBsN, _⟩ :=
    CFSG.StandardType.largeEvenRawDatum_exists hrawL
  refine ⟨labL, hlabL, ?_, ?_, hBsN⟩
  · have hn : labL.n < 2 := by simpa [GGLabQTwo] using hq
    have h1 : 1 ≤ labL.n := hlabL.1
    omega
  · refine CFSG.StandardType.largeEvenRawDatum_mono ?_ hrawL
    rintro R _ I F ⟨-, -, θ, -, -, -⟩
    exact ⟨θ⟩

private theorem not_label_A12_of_config
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hq : CFSG.Assembly.IsQuasisimple ↥L)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hhas : GGHasLabel (⟨.A, 1, 2⟩ : LargeEvenLabel)
      (↥L ⧸ Subgroup.center ↥L)) : False := by
  obtain ⟨-, hna⟩ := ggQuasisimple_centerQuot hq
  have hΛ : LargeEvenInLambda2 (⟨.A, 1, 2⟩ : LargeEvenLabel) := by
    norm_num [LargeEvenInLambda2]
  have hm := CFSG.StandardType.GGK0MarkedArithmetic.markedModel_of_label
    (X := ↥L ⧸ Subgroup.center ↥L) hΛ hna hhas
  have hmodel : CFSG.Blueprint.LieModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 2 := by
    simpa [MarkedModel, markTag, markRank, markChar, markDeg] using hm
  let ψ : ↥Bs →* MulAut (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom ↥L).comp
      (L.normalizerMonoidHom.comp (Subgroup.inclusion hBsN))
  have hker_le : ψ.ker ≤ (Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    refine ⟨b.2, ?_⟩
    change (b : G) ∈ Subgroup.centralizer (L : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hb' : CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient
        (L.normalizerMonoidHom ((Subgroup.inclusion hBsN) b)) = 1 := by
      simpa [ψ, CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom] using hb
    have hφ1 : L.normalizerMonoidHom ((Subgroup.inclusion hBsN) b) = 1 :=
      @CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_eq_one_imp ↥L _
        ⟨hq.1⟩ _ hb'
    have h2 := congrArg (fun f : MulAut ↥L => ((f ⟨l, hl⟩ : ↥L) : G)) hφ1
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply] at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  have hker_card : Nat.card ψ.ker ≤ 3 := by
    have h1 := Subgroup.card_le_of_le hker_le
    have h2 : Nat.card ↥((Bs ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Bs) =
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h2, hcfg.card_bstar_inf_centralizer_L] at h1
    exact h1
  have hcardB : Nat.card ↥Bs = Nat.card ψ.ker * Nat.card ψ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv,
      mul_comm, Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker]
  obtain ⟨-, hBsElem, -, -, hBcard⟩ := hcfg.tableB_facts
  have hrange_card : 27 ≤ Nat.card ψ.range := by
    by_contra h
    have hr : Nat.card ψ.range ≤ 26 := by omega
    have hmul : Nat.card ψ.ker * Nat.card ψ.range ≤ 3 * 26 := Nat.mul_le_mul hker_card hr
    omega
  have hψrange : IsElemAbelian 3 ψ.range := by
    have h := (hBsElem.subgroupOf Bs).map ψ
    rw [Subgroup.subgroupOf_self] at h
    rwa [MonoidHom.range_eq_map]
  have h9 := TableCRes.elemAbelian3_card_le_nine_of_aut_psl2
    (by norm_num : 2 ≤ 2) hmodel ψ.range hψrange
  omega

private theorem exists_labJ_of_tcj
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {R : Type} [groupR : Group R] {I : Set (MulAut R)} {lab : LargeEvenLabel}
    {θ : ↥(ggG0 3 B x L D J) ⧸ Subgroup.center ↥(ggG0 3 B x L D J) ≃* R}
    (hcfg : GGConfig 3 B Bs x L D J)
    (hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)))
    (hperf : commutator ↥(ggG0 3 B x L D J) = ⊤)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G))
    (hdiag : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ
      (fun l l' : ↥(ggG0 3 B x L D J) => (l' : G) = b⁻¹ * l * b) φ)
    (hP : ∀ (L' : Type) [Group L'] [Finite L'],
      ∀ (ψ : L' →* R), Function.Surjective ψ → ψ.ker ≤ Subgroup.center L' →
        commutator L' = ⊤ → ∀ e : MulAut L', e ^ 3 = 1 →
          (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
            ∀ J : Subgroup L', IsComponentOf J (ggFixSub e) →
              ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
                GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ lab.n ∣ labJ.n ∧
      GGHasLabel labJ (↥L ⧸ Subgroup.center ↥L) := by
  let G0 := ggG0 3 B x L D J
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hxN : x ∈ Subgroup.normalizer (G0 : Set G) := hBsN hxBs
  let e : MulAut ↥G0 := G0.normalizerMonoidHom ⟨x, hxN⟩
  let ψ : ↥G0 →* R :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥G0))
  have hψsurj : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker ≤ Subgroup.center ↥G0 := by
    intro l hl
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    exact (QuotientGroup.eq_one_iff l).mp (θ.injective (h0.trans (map_one θ).symm))
  have hepow : e ^ 3 = 1 := by
    have hdvd : orderOf e ∣ orderOf x := by
      have h := orderOf_map_dvd G0.normalizerMonoidHom
        (⟨x, hxN⟩ : ↥(Subgroup.normalizer (G0 : Set G)))
      rwa [Subgroup.orderOf_mk] at h
    exact (orderOf_dvd_iff_pow_eq_one).mp (by simpa [hcfg.orderOf_x] using hdvd)
  have hLle : L ≤ G0 := le_ggG0_left 3 B x L D J
  have hJinf : IsComponentOf L (G0 ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hcomp.of_le_of_le (le_inf hLle hcomp.1) inf_le_right
  have hJfix : IsComponentOf (L.subgroupOf G0) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hJinf
  have hφe : ∃ φ ∈ I, ∀ l : ↥G0, φ (ψ l) = ψ (e l) := by
    obtain ⟨φ, hφI, hφ⟩ := hdiag x⁻¹ (Subgroup.inv_mem Bs hxBs)
    refine ⟨φ, hφI, fun l => ?_⟩
    have hrel : ((e l : ↥G0) : G) = (x⁻¹)⁻¹ * (l : G) * x⁻¹ := by
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      simp
    exact hφ l (e l) hrel
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    hP ↥G0 ψ hψsurj hψker hperf e hepow hφe (L.subgroupOf G0) hJfix
  exact ⟨labJ, hlabJ, hdvd, ggHasLabel_of_mulEquiv
    (QuotientGroup.congr (Subgroup.center ↥(L.subgroupOf G0)) (Subgroup.center ↥L)
      (Subgroup.subgroupOfEquivOfLe hLle) (Subgroup.map_center_eq _)) hhasJ⟩

theorem ggQTwoXInL_ambient_field
    (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hA : GGQTwoXInLAmbOn (fun t => t = .B ∨ t = .C ∨ t = .D ∨ t = .twD) Bs
      (ggG0 3 B x L D J)) :
    CFSG.Assembly.LargeEvenMarking ↥(ggG0 3 B x L D J) (fun lab _ _ I _ θ =>
      (lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD) ∧ lab.n = 1 ∧
        ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  obtain ⟨hperfG0, lab, hlab, hrawA⟩ := hA
  obtain ⟨_, _, _, _, _, _, _, htag₀, -, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawA
  have hd : ¬ CFSG.LocalAnalysis.GLTheoremA.MI.DerivedLab lab := by
    intro h
    rcases htag₀ with h' | h' | h' | h' <;>
      (rcases h with h'' | h'' <;> rw [h'] at h'' <;> cases h'')
  have hTCJlegacy : LargeEvenLabelAll lab (ggQTwoTCJProp lab) :=
    hTCJ 3 (by norm_num : Nat.Prime 3) (by norm_num : (3 : ℕ) ≠ 2) lab hlab
  have hPcanon : CFSG.LocalAnalysis.GLTheoremA.MI.CAll lab (ggQTwoTCJProp lab) :=
    (CFSG.LocalAnalysis.GLTheoremA.MI.canonAll_iff_legacyAll hlab hd _).mpr hTCJlegacy
  obtain ⟨R, instR, I, F, hQAP⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists (hPcanon _ hrawA)
  obtain ⟨-, -, θ, -, hBsN, hdiag⟩ := hQAP.1
  obtain hP := hQAP.2
  obtain ⟨labJ, hlabJ, hdvd, hhasJ⟩ :=
    @exists_labJ_of_tcj G (inferInstance : Group G) (inferInstance : Finite G)
      B Bs x L D J R instR I lab θ hcfg hcomp hperfG0 hBsN hdiag hP
  obtain ⟨labL, hlabL, hL1, hhasL, hBsNL⟩ := innerDiagQTwo_data hS.2.1
  have hiso : GGLabelIso labJ labL :=
    hRig labJ labL (↥L ⧸ Subgroup.center ↥L) hlabJ hlabL hhasJ hhasL
  have hlabn : lab.n = 1 := by
    rcases label_iso_n_eq_or_exc hiso hL1 hlabJ.1 with hEq | hexc
    · have hdvd1 : lab.n ∣ 1 := by simpa [hEq, hL1] using hdvd
      exact Nat.dvd_one.mp hdvd1
    · exfalso
      exact not_label_A12_of_config hcfg hcomp.2.2 hBsNL (hexc.1 ▸ hhasJ)
  refine ⟨hperfG0, lab, hlab, ?_⟩
  refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hrawA
  rintro R _ I F ⟨hs, hna, θ, htag, hBsN, hdiag⟩
  exact ⟨hs, hna, θ, htag, hlabn, hdiag⟩

end CFSG.StandardType

end
