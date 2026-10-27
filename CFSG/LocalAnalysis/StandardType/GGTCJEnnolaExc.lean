module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivExc
public import CFSG.LocalAnalysis.StandardType.GGTCJEnnolaDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdxEnnolaTrans
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdxEnnola
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonTriLHolds
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private theorem ennolaExc_p_dvd {p : ℕ} {lab : GLALabel} (hrow : ggRowP_Ennola p lab) :
    p ∣ 2 ^ lab.n + 1 := by
  rcases hrow with h | ⟨-, -, h⟩
  · exact CFSG.StandardType.ggRowP_E.dvd h
  · exact h

private theorem ennolaExc_tag_of_fam_row {p : ℕ} {lab : GLALabel} (hFam : FamExc lab)
    (hrow : ggRowP_Ennola p lab) :
    lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6 := by
  obtain ⟨tg, r, n⟩ := lab
  simp only [FamExc] at hFam
  rcases hFam with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]
  · exfalso
    simp_all [ggRowP_Ennola, ggRowP_E, ggRowP_ESU, ggRowP_EOmP, ggRowP_EOmM, ggRowP_ETwE6,
      ggRowP_EE7, ggRowP_EE8, ggRowP_NF4]

private theorem ennolaExc_canonLabel_eq_of_component_top (hRig : GGLabelRigidInput) {S : Type}
    [Group S] [Finite S] [IsSimpleGroup S] {labK labJ : GLALabel} {J : Subgroup S}
    (hK : HasLabel S (fun l : GLALabel => l = labK))
    (hJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJp : CFSG.Open.IsComponentOf J (⊤ : Subgroup S)) :
    canonLabel labK = canonLabel labJ := by
  have hnt : Nontrivial ↥J := by
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJp.2.2.2
    exact Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center ↥J))
  have hne : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp hnt
  have htop : J = ⊤ := by
    haveI : IsSimpleGroup ↥(⊤ : Subgroup S) := Subgroup.topEquiv.isSimpleGroup
    exact CFSG.LocalAnalysis.GLTheoremA.AltDown.eq_of_isSubnormal_of_isSimpleGroup hJp.2.1 hne
  have e : ↥J ≃* S := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hJ' : HasLabel S (fun l : GLALabel => l = labJ) :=
    (hasLabel_congr e (fun l : GLALabel => l = labJ)).1 hJ
  exact Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hK hJ'

private theorem ennolaExc_index
    {lab : GLALabel}
    (ht : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .twE6)
    {R : Type} [Group R] (hM : MarkedModel lab R) :
    ∃ d : TauCeti.ValidLieTypeIndex, KD264Lie.isExcEnnolaIdx d.1 ∧ d.1.characteristic = 2 ∧
      KD264Lie.fieldSize d.1 = 2 ^ lab.n ∧
      Nonempty (R ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨tg, r, nn⟩ := lab
  dsimp only at ht ⊢
  rcases ht with rfl | rfl | rfl | rfl
  ·
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    have hmem : (.F4 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
      simp [CFSG.Blueprint.chevalleyExceptionalTags]
    have hce := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hM hmem
    obtain ⟨hadm, hm⟩ := hce
    have hf : 0 < nn := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, nn, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ nn := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.F4 q).Valid := by simp
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := hB.f4 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.F4 q, hv⟩, Or.inl ⟨q, rfl⟩, by simp [q],
      by simp [KD264Lie.fieldSize, q, TauCeti.PrimePower.card_def], ⟨e.trans b⟩⟩
  ·
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    have hmem : (.E7 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
      simp [CFSG.Blueprint.chevalleyExceptionalTags]
    have hce := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hM hmem
    obtain ⟨hadm, hm⟩ := hce
    have hf : 0 < nn := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, nn, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ nn := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.E7 q).Valid := by simp
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := hB.e7 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E7 q, hv⟩, Or.inr (Or.inl ⟨q, rfl⟩), by simp [q],
      by simp [KD264Lie.fieldSize, q, TauCeti.PrimePower.card_def], ⟨e.trans b⟩⟩
  ·
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    have hmem : (.E8 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
      simp [CFSG.Blueprint.chevalleyExceptionalTags]
    have hce := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hM hmem
    obtain ⟨hadm, hm⟩ := hce
    have hf : 0 < nn := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, nn, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ nn := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.E8 q).Valid := by simp
    obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := hB.e8 q hv K (by rw [hK, hq])
    exact ⟨⟨TauCeti.LieTypeIndex.E8 q, hv⟩, Or.inr (Or.inr (Or.inl ⟨q, rfl⟩)), by simp [q],
      by simp [KD264Lie.fieldSize, q, TauCeti.PrimePower.card_def], ⟨e.trans b⟩⟩
  ·
    simp only [MarkedModel, markTag, markRank, markChar, markDeg] at hM
    have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
    have hmem : (.twistedE6 : StatedLieTag) ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
      simp [CFSG.Blueprint.chevalleyExceptionalTags]
    have hce := CFSG.Blueprint.LieModel.chevalleyExceptionalModel hM hmem
    obtain ⟨hadm, hm⟩ := hce
    have hf : 0 < nn := hadm.2.1
    let q : TauCeti.PrimePower := ⟨2, nn, Nat.prime_two, hf⟩
    have hq : q.card = 2 ^ nn := TauCeti.PrimePower.card_def q
    have hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid := by simp
    obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hm
    obtain ⟨b⟩ := hB.twistedE6 q hv K (by rw [hK, hq]) σ (fun x => by rw [hq]; exact hσ x)
    exact ⟨⟨TauCeti.LieTypeIndex.twistedE6 q, hv⟩,
      Or.inr (Or.inr (Or.inr ⟨q, rfl⟩)), by simp [q],
      by simp [KD264Lie.fieldSize, q, TauCeti.PrimePower.card_def], ⟨e.trans b⟩⟩

theorem innDiagAllEnnolaExc_of_inputs
    (hRig : GGLabelRigidInput) (hIdx : KD264Lie.LieCompIdxEnnola KD264Lie.isExcEnnolaIdx) :
    InnDiagAllEnnolaOn FamExc := by
  intro S _ _ p α J labK labJ hFam hp hp2 hrow hcen hin hαp hlabJ hJ
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup α) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hK : HasLabel S (fun l : GLALabel => l = labK) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlamK := lambda2_of_hasLabel hK
  have hKn : (canonLabel labK).n = labK.n :=
    canonLabel_n_eq_self hlamK fun h => by simp [FamExc, h] at hFam
  have ht := ennolaExc_tag_of_fam_row hFam hrow
  have hq := hasLabel_isQuasisimple hK
  haveI := hq.2
  haveI hS : IsSimpleGroup S := (CanonInn.quotCenterEquivOfBot hcen).symm.isSimpleGroup
  by_cases hα1 : α = 1
  · subst hα1
    have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
      ext x
      simp [mem_fixSubgroup]
    rw [hfix] at hJ'
    have heq := ennolaExc_canonLabel_eq_of_component_top hRig hK hlabJ hJ'
    exact ⟨1, ⟨0, by norm_num⟩, by simp [heq]⟩
  · have ht5 : labK.tag = .F4 ∨ labK.tag = .E6 ∨ labK.tag = .E7 ∨ labK.tag = .E8 ∨
        labK.tag = .twE6 := by
      rcases ht with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
    have hαD : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S :=
      CFSG.LocalAnalysis.GLTheoremA.CanonTriL.mem_innAutDerived_of_innDiagKind_exc hcen ht5 hin
    have hM : MarkedModel labK (S ⧸ Subgroup.center S) := markedModel_of_hasLabel hK
    obtain ⟨d, hexc, hdchar, hdfs, ⟨e⟩⟩ := ennolaExc_index ht hM
    have hdvd : p ∣ KD264Lie.fieldSize d.1 + 1 := by
      rw [hdfs]
      exact ennolaExc_p_dvd hrow
    have hc := hIdx d p hp hp2 hdvd hexc
    have hedge : S ≃* (TauCeti.CFSGIndex.lie d).Group :=
      (CanonInn.quotCenterEquivOfBot hcen).symm.trans e
    have hcS : KD264Lie.CompIdxEnnolaAt p d.1 S :=
      KD264Lie.compIdxEnnolaAt_of_mulEquiv hedge.symm hc
    obtain ⟨i, ⟨φ⟩, j, hj, hidx⟩ := hcS α hαD hαp hα1 J hJ'
    obtain ⟨k, hk, hk'⟩ :=
      canonLabel_n_odd_of_idxOver hRig hlabJ hdchar hdfs φ hj hidx
    exact ⟨k, hk, by rw [hKn]; exact hk'⟩

theorem innDiagAllEnnolaExc
    (hIdx : KD264Lie.LieCompIdxEnnola KD264Lie.isExcEnnolaIdx) :
    InnDiagAllEnnolaOn FamExc :=
  innDiagAllEnnolaExc_of_inputs CFSG.StandardType.ggLabelRigidInput_holds hIdx

end CFSG.StandardType.TCJ

end
