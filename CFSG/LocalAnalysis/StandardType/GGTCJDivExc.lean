module

public import CFSG.LocalAnalysis.StandardType.GGTCJDivDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInputs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompIdx
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompIdx
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcompInn
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge

public section

namespace CFSG.StandardType.TCJ

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.Y10F
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup LieSemisimpleCent)

theorem tcjExc_exists_compIdx_of_component {S : Type} [Group S] [Finite S]
    (hS : IsSimpleGroup S) {d : TauCeti.ValidLieTypeIndex}
    (e : S ≃* (TauCeti.CFSGIndex.lie d).Group) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpc : p ≠ d.1.characteristic) (hI : KD264Lie.CompIdxAt p d.1 (TauCeti.CFSGIndex.lie d).Group)
    {β : MulAut S} (hβ : β ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived S)
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1) {J : Subgroup S}
    (hJ : CFSG.Open.IsComponentOf J (fixSubgroup β)) :
    ∃ i : TauCeti.CFSGIndex, Nonempty (↥J ⧸ Subgroup.center ↥J ≃* i.Group) ∧
      KD264Lie.compRelC d.1 i :=
  KD264Lie.compIdxAt_of_mulEquiv e.symm hI β hβ hβp hβ1 J hJ

theorem tcjExc_canon_n_dvd_of_component_top (hRig : GGLabelRigidInput) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] {labK labJ : GLALabel} {J : Subgroup S}
    (hK : HasLabel S (fun l : GLALabel => l = labK))
    (hJ : HasLabel ↥J (fun l : GLALabel => l = labJ))
    (hJp : CFSG.Open.IsComponentOf J (⊤ : Subgroup S)) :
    (canonLabel labK).n ∣ (canonLabel labJ).n := by
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
  rw [Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hK hJ']

theorem tcjExc_innDiagAllExc_of_inputs
    (hRig : GGLabelRigidInput) (hRest : GGInndiagCommRestInput)
    (hIdx : KD264Lie.LieCompIdx fun _ => True) (hL : LieSemisimpleCent) : InnDiagAllOn FamExc := by
  intro S _ _ p α J labK labJ hFam hp hp2 hcen hin hαp hlabJ hJ
  have hJ' : CFSG.Open.IsComponentOf J (fixSubgroup α) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ
  have hK : HasLabel S (fun l : GLALabel => l = labK) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hlamK := lambda2_of_hasLabel hK
  have hKn : (canonLabel labK).n = labK.n :=
    canonLabel_n_eq_self hlamK fun h => by simp [FamExc, h] at hFam
  rcases Nat.lt_or_ge labK.n 2 with hn1 | hn2
  · rw [hKn, show labK.n = 1 by have := hlamK.1; omega]
    exact one_dvd _
  have hq := hasLabel_isQuasisimple hK
  haveI := hq.2
  have hS : IsSimpleGroup S := (CanonInn.quotCenterEquivOfBot hcen).symm.isSimpleGroup
  by_cases hα1 : α = 1
  · subst hα1
    have hfix : fixSubgroup (1 : MulAut S) = ⊤ := by
      ext x
      simp [mem_fixSubgroup]
    rw [hfix] at hJ'
    exact tcjExc_canon_n_dvd_of_component_top hRig hK hlabJ hJ'
  have hαD := mem_innAutDerived_of_innDiagKind hRest hcen hn2 hin
  have hc := markChar_eq_two_of_two_le hlamK hn2
  have hLM : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) (markTag labK) (markRank labK) 2
      (markDeg labK) := by
    have h := markedModel_of_hasLabel hK
    unfold CFSG.StandardType.MarkedModel at h
    rwa [hc] at h
  rcases exists_index_or_small_of_lieModel_two hLM with ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
  ·
    have hpc : p ≠ d.1.characteristic := by
      rw [hd2]
      exact hp2
    obtain ⟨i, ⟨φ⟩, hrel⟩ := tcjExc_exists_compIdx_of_component hS
      ((CanonInn.quotCenterEquivOfBot hcen).symm.trans e) hp hp2 hpc
      (hIdx d p hp hp2 hpc trivial) hαD hαp hα1 hJ'
    exact dvd_canonLabel_n_of_compRelC hRig hlabJ hd2
      (two_pow_canonLabel_n_of_lie hRig hK d hd2 e).symm φ hrel
  ·
    exfalso
    have hfix : fixSubgroup α ≠ ⊤ := by
      intro h
      apply hα1
      ext s
      have hs : s ∈ fixSubgroup α := by
        rw [h]
        exact Subgroup.mem_top s
      exact mem_fixSubgroup.1 hs
    have hlt : Nat.card ↥J < 60 := by
      rw [← h60, ← Nat.card_congr (CanonInn.quotCenterEquivOfBot hcen).symm.toEquiv]
      calc Nat.card ↥J ≤ Nat.card ↥(fixSubgroup α) := Subgroup.card_le_of_le hJ'.1
        _ < Nat.card ↥(⊤ : Subgroup S) := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hfix)
        _ = Nat.card S := Subgroup.card_top
    haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    haveI : Nontrivial ↥J := by
      haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJ'.2.2.2
      exact Function.Surjective.nontrivial (QuotientGroup.mk_surjective (s := Subgroup.center ↥J))
    have hperf : commutator ↥J = ⊤ := hJ'.2.2.1
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J).ne hperf
  ·
    exfalso
    have h1' : (canonLabel labK).n = 1 := (canonLabel_n_eq_markDeg hlamK hc).trans h1
    have hdvd := n_dvd_canonLabel_n hlamK
    rw [h1'] at hdvd
    have := Nat.le_of_dvd one_pos hdvd
    omega

theorem innDiagAllExc :
    InnDiagAllOn FamExc :=
  tcjExc_innDiagAllExc_of_inputs CFSG.StandardType.ggLabelRigidInput_holds
    CFSG.StandardType.ggInndiagCommRestInput_holds KD264Lie.lieCompIdx_all
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent

end CFSG.StandardType.TCJ

end
