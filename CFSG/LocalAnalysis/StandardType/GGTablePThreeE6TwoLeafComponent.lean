module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCompLabCat
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import Certificates.Certificate707002
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafModel

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6TwoLeaf_model
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (F : LargeEvenLieTag → Prop) (hFF : ∀ t, F t → t = .E6 ∨ t = .twE6)
    (hD : DatumOn F X A δ J)
    (hn : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2)) :
    ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F' : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R),
      F lab.tag ∧ lab.n = 1 ∧ MarkedModel lab R ∧
      CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n ∧
      ggInducedAut θ δ ∈ I ∧ GGInndiagCommEq R I F' := by
  obtain ⟨hK, huniq, _hcard, hmark⟩ := hD
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  have hδ3 : δ ^ 3 = 1 := hAe.2 δ hδA
  have hdat : GGTorsionDatum (fun lab => F lab.tag) 3 δ J := by
    refine ⟨Nat.prime_three, by norm_num, hδ3, hδ1, hcomp, ?_⟩
    refine largeEvenMarking_mono
      (P := fun lab _ _ I _ θ => F lab.tag ∧ (LargeEvenSplit 3 lab ∧ GGInducedInn A θ I)) ?_ hmark
    intro lab R _ I F' θ h
    exact ⟨h.1, h.2.2 δ hδA⟩
  obtain ⟨hp, hp2, hδp, hδ1', hcomp', hmark'⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark'
  have hF : F lab.tag :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F' h => h.2.2.elim fun _ hh => hh.1) hraw)
  have htag : lab.tag = .E6 ∨ lab.tag = .twE6 := hFF lab.tag hF
  have hrawMM : LargeEvenRawDatumLegacy lab
      (fun R _ I _ => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, F lab.tag ∧ ggInducedAut θ δ ∈ I) ∧
          MarkedModel lab R) :=
    largeEvenRawDatum_markedModel hlab (fun R _ I F' h => h.2.1) hraw
  have hinndiag : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq) := by
    rcases htag with h | h
    · exact largeEvenLabelAll_inndiagComm_E6 h
    · exact largeEvenLabelAll_inndiagComm_twE6 hlab h
  have hraw' := hinndiag _ hrawMM
  obtain ⟨R, _, I, F', ⟨⟨hs, hna, θ, _, hδI⟩, hm⟩, hGuard⟩ := largeEvenRawDatum_exists hraw'
  have hEq : GGInndiagCommEq R I F' := hGuard hs hna
  have hn1 : lab.n = 1 := by
    obtain ⟨-, lab1, hlab1, hraw1⟩ := hn
    have hHas1 : GGHasLabel lab1 (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F' h => ⟨h.2.2.choose⟩) hraw1
    have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F' h => ⟨h.2.2.choose⟩) hraw
    have hn1' : lab1.n < 2 :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F' h => h.2.2.elim fun _ hh => hh) hraw1)
    have hle1 : 1 ≤ lab1.n := hlab1.1
    have heq1 : lab1.n = 1 := by omega
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso lab lab1 := hrigid lab lab1 _ hlab hlab1 hHas hHas1
    have heq : lab = lab1 := eq_of_ggLabelIso_of_e6Tag hIso htag
    rw [heq]
    exact heq1
  have ht_mem : markTag lab ∈ CFSG.Blueprint.chevalleyExceptionalTags := by
    rcases htag with h | h <;>
      simp [markTag, CFSG.Blueprint.chevalleyExceptionalTags, h]
  have hchev : CFSG.Blueprint.ChevalleyExceptionalModel R (markTag lab) 2 lab.n := by
    have hm0 : CFSG.Blueprint.LieModel R (markTag lab) (markRank lab) (markChar lab)
        (markDeg lab) := hm
    have h := hm0.chevalleyExceptionalModel ht_mem
    have hchar : markChar lab = 2 := by rcases htag with h | h <;> simp [markChar, h]
    have hdeg : markDeg lab = lab.n := by rcases htag with h | h <;> simp [markDeg, h]
    rw [hchar, hdeg] at h
    exact h
  exact ⟨lab, R, _, I, F', θ, hF, hn1, hm, hchev, hδI, hEq⟩

theorem e6TwoLeaf_component
    {X : Type} [Group X] [Finite X] {δ : MulAut X} {J : Subgroup X}
    {R : Type} [Group R] {I F : Set (MulAut R)}
    (θ : X ⧸ Subgroup.center X ≃* R)
    (hXc : commutator X = ⊤) (hδ3 : δ ^ 3 = 1) (hδ1 : δ ≠ 1)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup δ))
    (huniq : ∀ Q : Subgroup X, IsComponentOf Q (ggAutFixedSubgroup δ) → Q = J)
    (hδI : ggInducedAut θ δ ∈ I) (hEq : GGInndiagCommEq R I F)
    (d : TauCeti.ValidLieTypeIndex) (hdchar : d.1.characteristic = 2)
    (hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2)
    (hd : (∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∨
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q)
    (e : R ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
      GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧
      ((∃ q : TauCeti.PrimePower, d.1 = .E6 q) →
        E6TwoCompLabelW lab' ∧ (lab' = ⟨.A, 2, 2⟩ → Subgroup.center J ≠ ⊥)) ∧
      (¬ (∃ q : TauCeti.PrimePower, d.1 = .E6 q) → E6TwoCompLabelT lab') := by
  let δbar : MulAut R := ggInducedAut θ δ
  have hδbar1 : δbar ≠ 1 := by
    intro h
    apply hδ1
    exact ggInducedAut_injective_of_perfect hXc θ (h.trans (map_one _).symm)
  have hδbarp : δbar ^ 3 = 1 := by
    dsimp [δbar]
    rw [← map_pow, hδ3, map_one]
  have hβ : δbar ∈ CFSG.ComponentClassification.OuterAutomorphisms.innAutDerived R := by
    have hmem : δbar ∈ ggInndiag R I := Subgroup.mem_sup_right (Subgroup.subset_closure hδI)
    have hmem2 : δbar ∈ ggInndiagComm R := by rw [← hEq]; exact hmem
    rwa [ggInndiagComm_eq_innAutDerived] at hmem2
  let g : X →* R :=
    (θ : X ⧸ Subgroup.center X →* R).comp (QuotientGroup.mk' (Subgroup.center X))
  let Jbar : Subgroup R := J.map g
  have hJbar : IsComponentOf Jbar (ggAutFixedSubgroup δbar) := by
    dsimp [Jbar, g, δbar]
    exact ggTorsion_isComponentOf_image θ hcomp
  have hC : CFSG.Open.IsComponentOf Jbar
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
        ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact isComponentOf_iff_open.mp hJbar
  have huniqJbar : ∀ K : Subgroup R,
      CFSG.Open.IsComponentOf K (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar) →
        K = Jbar := by
    intro K hK
    have hK' : IsComponentOf K (ggAutFixedSubgroup δbar) := by
      have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δbar =
          ggAutFixedSubgroup δbar := Subgroup.ext fun _ => Iff.rfl
      exact isComponentOf_iff_open.mpr (by simpa [hfix] using hK)
    obtain ⟨K0, hK0, hK0map⟩ := exists_component_of_induced hXc θ δ hK'
    have hK0J : K0 = J := huniq K0 hK0
    calc K = K0.map g := hK0map.symm
      _ = J.map g := by rw [hK0J]
      _ = Jbar := rfl
  have hIcomp : CompLabE6TwoAt (∃ q : TauCeti.PrimePower, d.1 = .E6 q)
      (TauCeti.CFSGIndex.lie d).Group :=
    compLabE6Two_cat d hdchar hd hdfield
  have hIcomp' : CompLabE6TwoAt (∃ q : TauCeti.PrimePower, d.1 = .E6 q) R :=
    e6TwoLeaf_compLabE6TwoAt_of_mulEquiv e.symm hIcomp
  obtain ⟨lab', hlab', hhas_bar, hcomp_pair⟩ :=
    hIcomp' δbar hβ hδbarp hδbar1 Jbar hC huniqJbar
  obtain ⟨eJ⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  have hhas : GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) := by
    unfold GGHasLabel at hhas_bar ⊢
    refine largeEvenRawDatum_mono (fun R' _ I' F' ⟨ψ⟩ => ?_) hhas_bar
    exact ⟨eJ.trans ψ⟩
  refine ⟨lab', hlab', hhas, ?_, hcomp_pair.2⟩
  intro huntw
  obtain ⟨hW, hcent_bar⟩ := hcomp_pair.1 huntw
  refine ⟨hW, fun hA => ?_⟩
  intro hbot
  refine hcent_bar hA ?_
  let fJ : ↥J →* ↥Jbar := g.subgroupMap J
  have hfJ : Function.Surjective fJ := g.subgroupMap_surjective J
  have hkerJ : fJ.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx2 : g (x : X) = 1 := by
      change ((g.subgroupMap J) x : R) = 1
      rw [hx]
      rfl
    have hxZ : (x : X) ∈ Subgroup.center X := by
      have h1 : (θ : X ⧸ Subgroup.center X →* R)
          (QuotientGroup.mk' (Subgroup.center X) (x : X)) = 1 := by
        simpa [g] using hx2
      have h2 : QuotientGroup.mk' (Subgroup.center X) (x : X) = 1 :=
        θ.injective (by simpa using h1)
      exact (QuotientGroup.eq_one_iff (x : X)).mp h2
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxZ (y : X))
  have hcomap := e6TwoLeaf_comap_center_eq_center_of_perfect fJ hfJ hkerJ hcomp.2.2.1
  rw [hbot] at hcomap
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  obtain ⟨x, rfl⟩ := hfJ y
  have hx : x ∈ (Subgroup.center ↥Jbar).comap fJ := Subgroup.mem_comap.mpr hy
  rw [hcomap] at hx
  simp only [Subgroup.mem_bot] at hx
  rw [hx, map_one]

theorem e6TwoLeaf_label_W
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .E6) X A δ J)
    (hn : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2)) :
    ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
      GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧ E6TwoCompLabelW lab' ∧
      (lab' = ⟨.A, 2, 2⟩ → Subgroup.center J ≠ ⊥) := by
  obtain ⟨lab, R, hR, I, F', θ, hE6, hn1, _hm, hchev, hδI, hEq⟩ :=
    e6TwoLeaf_model (fun t => t = .E6) (fun _ ht => Or.inl ht) hD hn
  have hchevE6 : CFSG.Blueprint.ChevalleyExceptionalModel R .E6 2 lab.n :=
    e6TwoLeaf_chevE6 hchev hE6
  obtain ⟨d, hdchar, hk, huntw, he⟩ := e6TwoLeaf_index_E6 (p := 2) (f := lab.n) hchevE6
  obtain ⟨e⟩ := he
  have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
    rw [hk, hn1, pow_one]
  obtain ⟨hK, huniq, _hcard, hmarkD⟩ := hD
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  have hδ3 : δ ^ 3 = 1 := hAe.2 δ hδA
  have hXc : commutator X = ⊤ := hmarkD.1
  have hd : (∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∨
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q := Or.inl huntw
  obtain ⟨lab', hlab', hhas, hpairW, _⟩ :=
    e6TwoLeaf_component θ hXc hδ3 hδ1 hcomp huniq hδI hEq d hdchar hdfield hd e
  exact ⟨lab', hlab', hhas, (hpairW huntw).1, (hpairW huntw).2⟩

theorem e6TwoLeaf_label_T
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .twE6) X A δ J)
    (hn : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2)) :
    ∃ lab' : LargeEvenLabel, LargeEvenInLambda2 lab' ∧
      GGHasLabel lab' (↥J ⧸ Subgroup.center ↥J) ∧ E6TwoCompLabelT lab' := by
  obtain ⟨lab, R, hR, I, F', θ, hTw, hn1, _hm, hchev, hδI, hEq⟩ :=
    e6TwoLeaf_model (fun t => t = .twE6) (fun _ ht => Or.inr ht) hD hn
  have hchevTw : CFSG.Blueprint.ChevalleyExceptionalModel R .twistedE6 2 lab.n :=
    e6TwoLeaf_chevTwE6 hchev hTw
  obtain ⟨d, hdchar, hk, huntw, he⟩ := e6TwoLeaf_index_twE6 (p := 2) (f := lab.n) hchevTw
  obtain ⟨e⟩ := he
  have hdfield : CFSG.LocalAnalysis.GLTheoremA.KD264Lie.fieldSize d.1 = 2 := by
    rw [hk, hn1, pow_one]
  have hnotE6 : ¬ (∃ q : TauCeti.PrimePower, d.1 = .E6 q) := by
    rintro ⟨q1, hq1⟩
    obtain ⟨q2, hq2⟩ := huntw
    rw [hq1] at hq2
    cases hq2
  obtain ⟨hK, huniq, _hcard, hmarkD⟩ := hD
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  have hδ3 : δ ^ 3 = 1 := hAe.2 δ hδA
  have hXc : commutator X = ⊤ := hmarkD.1
  have hd : (∃ q : TauCeti.PrimePower, d.1 = .E6 q) ∨
      ∃ q : TauCeti.PrimePower, d.1 = .twistedE6 q := Or.inr huntw
  obtain ⟨lab', hlab', hhas, _, hpairT⟩ :=
    e6TwoLeaf_component θ hXc hδ3 hδ1 hcomp huniq hδI hEq d hdchar hdfield hd e
  exact ⟨lab', hlab', hhas, hpairT hnotE6⟩

end CFSG.StandardType.TablePThreeKG

end
