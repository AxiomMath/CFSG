module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRowR3Defs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrRowR3
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeNbrSCFourData
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint TableB

theorem ggRowR3_innerDiagOnLab (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {Bs K : Subgroup G} (hInn : GGInnerDiagOn Bs K)
    (hlab : GGHasLabel ⟨.twE6, 0, 1⟩ (↥K ⧸ Subgroup.center ↥K)) :
    Bs ≤ Subgroup.normalizer (K : Set G) ∧
      GGInnerDiagOnLab (fun p lab => GGTwE6BadLabel p lab ∧ GGLabQTwo p lab) 3 Bs K := by
  have hΛ : LargeEvenInLambda2 ⟨.twE6, 0, 1⟩ := ⟨le_refl 1, rfl⟩
  have hB := ggInnerDiagOn_relabel hRig hInn hΛ hlab
  have hbad : GGTwE6BadLabel 3 ⟨.twE6, 0, 1⟩ := by
    unfold GGTwE6BadLabel; decide
  have hq2 : GGLabQTwo 3 ⟨.twE6, 0, 1⟩ := by
    unfold GGLabQTwo; decide
  have hsplit : LargeEvenSplit 3 ⟨.twE6, 0, 1⟩ := by
    unfold LargeEvenSplit LargeEvenUntwisted; decide
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hInn
    exact hP.1
  · refine largeEvenMarking_mono (fun lab' R _ I F θ hP => ?_) hB
    obtain ⟨rfl, hN, hφ⟩ := hP
    exact ⟨⟨hbad, hq2⟩, hsplit, hN, hφ⟩

theorem ggTwE6BigSetting_of_nbr {G : Type} [Group G] [Finite G] (hL : GGLBalanceInput)
    (hPJ : GGStdSubPrimeInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) {I : Set (MulAut R)}
    (h3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    ∃ _ : J ≤ K, GGTwE6BigSetting I (ggQuotHom θ) (ggGamma K hN).range
      (ggGamma K hN ⟨x, hcfg.tableB_facts.2.2.1⟩) (J.subgroupOf K) := by
  classical
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian 3 (ggGamma K hN).range := isElemAbelian_range hBc hBp (ggGamma K hN)
  obtain ⟨hJK, hJ1⟩ := isComponentOf_comap_ggFix_ggGamma_x hL hPJ hcfg hnb hN hxBs
  refine ⟨hJK, ?_⟩
  unfold GGTwE6BigSetting
  refine ⟨hA, ?_, h5, ⟨⟨x, hxBs⟩, rfl⟩, ?_, hJ1⟩
  · rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta K θ hN b, ggBeta_mem K θ hN h3 b, fun l => ggBeta_ggQuotHom K hN θ b l⟩
  · intro h1
    rw [ggGamma_eq_one_iff] at h1
    exact not_mem_centralizer_of_nbr hnb h1

theorem ggTwE6BigLabel_labelIso_n {a b : LargeEvenLabel} (ha : GGTwE6BigLabel a)
    (hab : GGLabelIso a b) : b.n = 1 := by
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hab with h | h | h | h | h | h | h | h <;>
    (try subst h) <;> simp_all

theorem ggRowR3_false_of_marking (hRig : GGLabelRigidInput) {G : Type} [Group G] {J K : Subgroup G}
    (hJK : J ≤ K)
    (hM : LargeEvenMarking ↥(J.subgroupOf K) fun lab' _ _ _ _ _ => GGTwE6BigLabel lab')
    {labJ : LargeEvenLabel} (hΛ : LargeEvenInLambda2 labJ) (h2 : 2 ≤ labJ.n)
    (hhas : GGHasLabel labJ (↥J ⧸ Subgroup.center ↥J)) : False := by
  obtain ⟨lab5, hΛ5, hhas5, -, -, -, -, -, hbig5⟩ := largeEvenMarking_exists_hasLabel hM
  have hhas5' : GGHasLabel lab5 (↥J ⧸ Subgroup.center ↥J) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK)
      (Subgroup.map_center_eq _)) hhas5
  have hiso : GGLabelIso lab5 labJ :=
    hRig lab5 labJ (↥J ⧸ Subgroup.center ↥J) hΛ5 hΛ hhas5' hhas
  have hn1 : labJ.n = 1 := ggTwE6BigLabel_labelIso_n hbig5 hiso
  omega

theorem ggCorFiveTwentyInputNbrRowR3_of_big (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hL : GGLBalanceInput) (hPJ : GGStdSubPrimeInput) (hBig : GGTwE6BigLabelsKnown) :
    GGCorFiveTwentyInputNbrRowR3 := by
  intro G _ _ p B Bs x L D J hH hq hN hR hF
  obtain ⟨y, K, hnb, hK⟩ : ∃ (y : G) (K : Subgroup G), GGNbr p B x D J y K ∧
      ¬ GGInnerDiagOnLabel GGLabNbrOk p Bs K := by
    by_contra hc
    exact hN fun y K hnb => by_contra fun hK => hc ⟨y, K, hnb, hK⟩
  obtain ⟨hp3, hlabK⟩ := hF y K hnb hK
  subst hp3
  exfalso
  have hcfg := hH.1
  obtain ⟨hNK, hInnK⟩ := ggRowR3_innerDiagOnLab hRig (hH.2.2.1.2 y K hnb) hlabK
  have h5 := hR y K hnb hInnK hNK
  obtain ⟨labL, labJ, _, hq4, _, hJΛ, hdvd, hhasJ⟩ := ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hq hnb
  have hJ2 : 2 ≤ labJ.n := le_trans hq4 (Nat.le_of_dvd (by have := hJΛ.1; omega) hdvd)
  obtain ⟨hK0, lab, hlab, hraw⟩ := hInnK
  obtain ⟨_, _, _, _, _, _, θ₀, hP₀⟩ := largeEvenRawDatum_exists hraw
  have hn1 : lab.n = 1 := by
    have h1 := hlab.1
    have h2 := hP₀.1.2
    simp only [GGLabQTwo] at h2
    omega
  have hAll := hBig lab hlab hP₀.1.1.1 hn1
  obtain ⟨R, _, I, F, ⟨⟨hs, hna, θ, hP⟩, hAll'⟩⟩ := largeEvenRawDatum_exists (hAll _ hraw)
  obtain ⟨hJK, hset⟩ := ggTwE6BigSetting_of_nbr hL hPJ hcfg hnb hNK h5 θ hP.2.2.2
  have hM := hAll' hs hna K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hK0
    (ggGamma K hNK).range (ggGamma K hNK ⟨x, hcfg.tableB_facts.2.2.1⟩) (J.subgroupOf K) hset
  exact ggRowR3_false_of_marking hRig hJK hM hJΛ hJ2 hhasJ

end CFSG.StandardType

end
