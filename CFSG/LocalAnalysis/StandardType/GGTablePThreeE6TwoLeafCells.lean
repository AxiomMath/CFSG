module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6Narrow
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLow2Z
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoCompLabCat
import CFSG.LocalAnalysis.StandardType.KGCoverLift
import CFSG.LocalAnalysis.StandardType.GGTCJDivLin
public import Certificates.Certificate707002
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6TwoLeafComponent

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem e6TwoLeaf_center_of_tableZ
    {X : Type} [Group X] [Finite X] {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hZ : TwE6A2CentreInputTwo)
    (hD : DatumOn (fun t => t = .twE6) X A δ J)
    (hn : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2))
    (hJmark : LargeEvenMarking J (fun lab _ _ _ _ _ =>
      lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3)) :
    Subgroup.center J = ⊥ := by
  obtain ⟨hK, huniq, _hcard, hmark⟩ := hD
  obtain ⟨haut, _hker⟩ := hK
  obtain ⟨hAe, hδA, hδ1, hcomp, _hnorm⟩ := haut
  have hδmem : δ ∈ A := hδA
  have hδ3 : δ ^ 3 = 1 := hAe.2 δ hδA
  have hXc : commutator X = ⊤ := hmark.1
  obtain ⟨-, labD, hlabD, hrawD⟩ := hmark
  have htagD : labD.tag = .twE6 :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hrawD)
  have hn1D : labD.n = 1 := by
    obtain ⟨-, lab1, hlab1, hraw1⟩ := hn
    have hHas1 : GGHasLabel lab1 (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw1
    have hHas : GGHasLabel labD (X ⧸ Subgroup.center X) :=
      largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hrawD
    have hn1' : lab1.n < 2 :=
      e6TwoLeaf_rawDatum_elim_const'
        (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hraw1)
    have hle1 : 1 ≤ lab1.n := hlab1.1
    have heq1 : lab1.n = 1 := by omega
    have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
    have hIso : GGLabelIso labD lab1 := hrigid labD lab1 _ hlabD hlab1 hHas hHas1
    have heq : labD = lab1 := eq_of_ggLabelIso_of_e6Tag hIso (Or.inr htagD)
    rw [heq]
    exact heq1
  have hZlabD : LargeEvenLabelAll labD (TwE6A2CentreCont labD.n) :=
    hZ labD hlabD htagD hn1D
  have hrawD2 : LargeEvenRawDatum labD
      (fun R _ I F => (IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : X ⧸ Subgroup.center X ≃* R, (labD.tag = .twE6) ∧
          (LargeEvenSplit 3 labD ∧ GGInducedInn A θ I)) ∧ TwE6A2CentreCont labD.n R I F) :=
    hZlabD _ hrawD
  obtain ⟨R, _, I, F, hQ2⟩ := largeEvenRawDatum_exists hrawD2
  have hQ2a : IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R, (labD.tag = .twE6) ∧
        (LargeEvenSplit 3 labD ∧ GGInducedInn A θ I) := hQ2.1
  have hTw : TwE6A2CentreCont labD.n R I F := hQ2.2
  obtain ⟨hsR, hnaR, hRest⟩ := hQ2a
  obtain ⟨θ, hLD⟩ := hRest
  obtain ⟨hfinC, hCperf, θC, κ, lift, hκsurj, hκker, hκmk, hκlift, hkg⟩ :=
    CFSG.StandardType.KGUniv.exists_universal_cover_lift hXc θ
  haveI : Finite (CFSG.RankThree.PerfectCover.HopfCover R) := hfinC
  have hα3 : (lift δ) ^ 3 = 1 := by
    simpa using congrArg lift hδ3
  have hαne : lift δ ≠ 1 := by
    intro h1
    apply hδ1
    ext y
    obtain ⟨x, rfl⟩ := hκsurj y
    have h := hκlift δ x
    rw [h1] at h
    simpa using h.symm
  have hαI : ggInducedAut θC (lift δ) ∈ I := by
    change kgInducedAut θC (lift δ) ∈ I
    rw [hkg]
    change ggInducedAut θ δ ∈ I
    exact hLD.2.2 δ hδmem
  have hJcompA : CFSG.Assembly.IsComponentOf J
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup δ =
        ggAutFixedSubgroup δ := Subgroup.ext fun _ => Iff.rfl
    rw [hfix]
    exact hcomp
  obtain ⟨Jt, hJtcomp, hJtmap⟩ :=
    CFSG.StandardType.TCJ.tcjLin_component_lift κ hκsurj hκker (lift δ) δ
      (fun x => hκlift δ x) hJcompA
  have hJtcomp' : CFSG.Assembly.IsComponentOf Jt (ggAutFixedSubgroup (lift δ)) := by
    have hfix : CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (lift δ) =
        ggAutFixedSubgroup (lift δ) := Subgroup.ext fun _ => Iff.rfl
    rw [hfix] at hJtcomp
    exact hJtcomp
  let f : ↥Jt →* ↥J :=
    (MulEquiv.subgroupCongr hJtmap).toMonoidHom.comp (κ.subgroupMap Jt)
  have hf : Function.Surjective f :=
    (MulEquiv.subgroupCongr hJtmap).surjective.comp (κ.subgroupMap_surjective Jt)
  have hkerf : f.ker ≤ Subgroup.center ↥Jt := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : (MulEquiv.subgroupCongr hJtmap) (κ.subgroupMap Jt x) =
        (MulEquiv.subgroupCongr hJtmap) 1 := by simpa [f] using hx
    have hx1 : κ.subgroupMap Jt x = 1 := (MulEquiv.subgroupCongr hJtmap).injective hx'
    have hx2 : κ (x : CFSG.RankThree.PerfectCover.HopfCover R) = 1 := by
      simpa using congrArg Subtype.val hx1
    have hxcent : (x : CFSG.RankThree.PerfectCover.HopfCover R) ∈
        Subgroup.center (CFSG.RankThree.PerfectCover.HopfCover R) :=
      hκker (MonoidHom.mem_ker.mpr hx2)
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxcent
      (y : CFSG.RankThree.PerfectCover.HopfCover R))
  let g : ↥Jt →* ↥J ⧸ Subgroup.center ↥J :=
    (QuotientGroup.mk' (Subgroup.center ↥J)).comp f
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).comp hf
  have hgker : Subgroup.center ↥Jt = g.ker := by
    rw [← e6TwoLeaf_comap_center_eq_center_of_perfect f hf hkerf hJtcomp'.2.2.1]
    ext x
    rw [Subgroup.mem_comap, MonoidHom.mem_ker]
    change f x ∈ Subgroup.center ↥J ↔
      QuotientGroup.mk' (Subgroup.center ↥J) (f x) = 1
    exact (QuotientGroup.eq_one_iff (f x)).symm
  let e : ↥Jt ⧸ Subgroup.center ↥Jt ≃* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.liftEquiv (Subgroup.center ↥Jt) hg hgker
  obtain ⟨-, labc, hlabc, hrawc⟩ := hJmark
  have hpropc : labc.tag = .twA ∧ labc.rank = 2 ∧ labc.n = 3 :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh) hrawc)
  have hmJt : LargeEvenMarking ↥Jt
      (fun lab _ _ _ _ _ => lab.tag = .twA ∧ lab.rank = 2 ∧ lab.n = 3 * labD.n) := by
    refine ⟨hJtcomp'.2.2.1, labc, hlabc, ?_⟩
    refine largeEvenRawDatum_mono (fun R _ I F h => ⟨h.1, h.2.1, ?_⟩) hrawc
    obtain ⟨θc, hθc⟩ := h.2.2
    exact ⟨e.trans θc, hpropc.1, hpropc.2.1, by rw [hpropc.2.2, hn1D, mul_one]⟩
  have hcenterJt : Subgroup.center ↥Jt = ⊥ :=
    hTw θC (lift δ) hα3 hαne hαI Jt hJtcomp' hmJt
  have hcomap := e6TwoLeaf_comap_center_eq_center_of_perfect f hf hkerf hJtcomp'.2.2.1
  have hmap := congrArg (Subgroup.map f) hcomap
  rw [Subgroup.map_comap_eq_self_of_surjective hf, hcenterJt, Subgroup.map_bot] at hmap
  exact hmap

theorem e6TwoLeaf_A2_rigid {labJ lab' : LargeEvenLabel}
    (h : GGLabelIso labJ lab') (hJ : GGLabelA2 labJ) : labJ = lab' := by
  obtain ⟨t, l, n⟩ := labJ
  obtain ⟨t', l', n'⟩ := lab'
  have hJ' : l = 2 ∧ (t = .A ∨ t = .twA) := by
    have h1 : l = 2 := hJ.1
    have h2 : t = .A ∨ t = .twA := by
      rcases hJ.2.2 with ⟨ht, -⟩ | ⟨ht, -⟩
      · exact Or.inl ht
      · exact Or.inr ht
    exact ⟨h1, h2⟩
  rcases h with h | h | h | h | h | h | h | h
  · exact h
  · rcases h with ⟨h1, -, -, -⟩
    rcases hJ'.2 with ht | ht <;> rcases h1 with hb | hb <;> simp_all
  · rcases h with ⟨h1, -⟩
    have ht : t = .D := congrArg LargeEvenLabel.tag h1
    rcases hJ'.2 with h2 | h2 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have hl : l = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hJ'.2 with h2 | h2 <;> simp_all
  · rcases h with ⟨h1, -⟩
    have hl : l = 3 := congrArg LargeEvenLabel.rank h1
    omega
  · rcases h with ⟨h1, -⟩
    have ht : t = .twD := congrArg LargeEvenLabel.tag h1
    rcases hJ'.2 with h2 | h2 <;> simp_all
  · rcases h with ⟨-, h1⟩
    have hl : l = 1 := congrArg LargeEvenLabel.rank h1
    omega

theorem e6TwoLeaf_W_of_A2 {lab' : LargeEvenLabel}
    (hW : E6TwoCompLabelW lab') (hJ : GGLabelA2 lab') :
    lab' = ⟨.A, 2, 2⟩ := by
  unfold E6TwoCompLabelW at hW
  rcases hW with h | h | h
  · rw [h] at hJ
    obtain ⟨hr, -, -⟩ := hJ
    simp at hr
  · rw [h] at hJ
    obtain ⟨-, -, hd⟩ := hJ
    rcases hd with ⟨ht, -⟩ | ⟨ht, -⟩ <;> simp at ht
  · exact h

theorem e6TwoLeaf_false_W_of_D4 {labJ lab' : LargeEvenLabel}
    (hIso : GGLabelIso labJ lab') (hJ : labJ.tag = .D ∧ labJ.rank = 4)
    (hW : E6TwoCompLabelW lab') : False := by
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h] at hW
    unfold E6TwoCompLabelW at hW
    rcases hW with h1 | h1 | h1 <;> rw [h1] at hJ <;> simp at hJ
  · rcases h with ⟨h1, -, -, -⟩
    rcases h1 with hb | hb <;> rw [hJ.1] at hb <;> simp at hb
  · have hl : labJ.rank = 3 := congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : labJ.tag = .A := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .twA := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .A := congrArg LargeEvenLabel.tag h.2
    rw [hJ.1] at ht; simp at ht

theorem e6TwoLeaf_false_W_of_triD4 {labJ lab' : LargeEvenLabel}
    (hIso : GGLabelIso labJ lab') (hJ : labJ.tag = .triD4)
    (hW : E6TwoCompLabelW lab') : False := by
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h] at hW
    unfold E6TwoCompLabelW at hW
    rcases hW with h1 | h1 | h1 <;> rw [h1] at hJ <;> simp at hJ
  · rcases h with ⟨h1, -, -, -⟩
    rcases h1 with hb | hb <;> rw [hJ] at hb <;> simp at hb
  · have ht : labJ.tag = .D := congrArg LargeEvenLabel.tag h.1
    rw [hJ] at ht; simp at ht
  · have ht : labJ.tag = .A := congrArg LargeEvenLabel.tag h.1
    rw [hJ] at ht; simp at ht
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ] at ht; simp at ht
  · have ht : labJ.tag = .twA := congrArg LargeEvenLabel.tag h.1
    rw [hJ] at ht; simp at ht
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ] at ht; simp at ht
  · have ht : labJ.tag = .A := congrArg LargeEvenLabel.tag h.2
    rw [hJ] at ht; simp at ht

theorem e6TwoLeaf_false_W_of_A1 {labA lab' : LargeEvenLabel}
    (hIso : GGLabelIso labA lab') (hAt : labA.tag = .A) (hAr : labA.rank = 1)
    (hW : E6TwoCompLabelW lab') : False := by
  have hWf : (lab'.tag = .A ∧ (lab'.rank = 5 ∨ lab'.rank = 2)) ∨
      (lab'.tag = .twD ∧ lab'.rank = 4) := by
    unfold E6TwoCompLabelW at hW
    rcases hW with h | h | h
    · subst h; exact Or.inl ⟨rfl, Or.inl rfl⟩
    · subst h; exact Or.inr ⟨rfl, rfl⟩
    · subst h; exact Or.inl ⟨rfl, Or.inr rfl⟩
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h] at hWf
    rcases hWf with ⟨ht, hr⟩ | ⟨ht, hr⟩
    · rcases hr with hr | hr <;> omega
    · rw [hAt] at ht; simp at ht
  · rcases h.1 with hb | hb <;> rw [hAt] at hb <;> simp at hb
  · have ht : labA.tag = .D := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have hr : labA.rank = 3 := congrArg LargeEvenLabel.rank h.1
    rw [hAr] at hr
    simp at hr
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twA := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · rcases hWf with ⟨ht, hr⟩ | ⟨ht, hr⟩
    · rw [h.1] at ht; simp at ht
    · rw [h.1] at hr; simp at hr

theorem e6TwoLeaf_false_W_of_twA2 {labJ lab' : LargeEvenLabel}
    (hIso : GGLabelIso labJ lab') (hJ : labJ.tag = .twA ∧ labJ.rank = 2)
    (hW : E6TwoCompLabelW lab') : False := by
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [← h] at hW
    unfold E6TwoCompLabelW at hW
    rcases hW with h1 | h1 | h1 <;> rw [h1] at hJ <;> simp at hJ
  · rcases h with ⟨h1, -, -, -⟩
    rcases h1 with hb | hb <;> rw [hJ.1] at hb <;> simp at hb
  · have ht : labJ.tag = .D := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .A := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have hr : labJ.rank = 3 := congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hJ.1] at ht; simp at ht
  · have hr : labJ.rank = 1 := congrArg LargeEvenLabel.rank h.2
    omega

theorem e6TwoLeaf_false_T_of_A1 {labA lab' : LargeEvenLabel}
    (hIso : GGLabelIso labA lab') (hAt : labA.tag = .A) (hAr : labA.rank = 1)
    (hT : E6TwoCompLabelT lab') : False := by
  have hTf : lab'.tag ≠ .A := by
    unfold E6TwoCompLabelT at hT
    rintro ht
    rcases hT with h | h | h | h | h | h | h <;> rw [h] at ht <;> simp at ht
  have hTf2 : ¬ (lab'.tag = .twD ∧ lab'.rank = 2) := by
    unfold E6TwoCompLabelT at hT
    rintro ⟨ht, hr⟩
    rcases hT with h | h | h | h | h | h | h <;> rw [h] at ht hr <;> simp at ht hr
  rcases hIso with h | h | h | h | h | h | h | h
  · rw [h] at hAt; exact hTf hAt
  · rcases h.1 with hb | hb <;> rw [hAt] at hb <;> simp at hb
  · have ht : labA.tag = .D := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have hr : labA.rank = 3 := congrArg LargeEvenLabel.rank h.1
    omega
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twA := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · have ht : labA.tag = .twD := congrArg LargeEvenLabel.tag h.1
    rw [hAt] at ht; simp at ht
  · exact hTf2 ⟨congrArg LargeEvenLabel.tag h.1, congrArg LargeEvenLabel.rank h.1⟩

theorem e6TwoLeaf_eq_twA2_of_T {lab' : LargeEvenLabel}
    (hT : E6TwoCompLabelT lab') (ht : lab'.tag = .twA ∧ lab'.rank = 2) :
    lab' = ⟨.twA, 2, 3⟩ := by
  unfold E6TwoCompLabelT at hT
  rcases hT with h | h | h | h | h | h | h
  · rw [h] at ht; simp at ht
  · rw [h] at ht; simp at ht
  · rw [h] at ht; simp at ht
  · rw [h] at ht; simp at ht
  · rw [h] at ht; simp at ht
  · exact h
  · rw [h] at ht; simp at ht

theorem e6TwoLeaf_marking_E6_deg {X : Type} [Group X] {A : Subgroup (MulAut X)}
    {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .twE6) X A δ J) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .E6 → 2 ≤ lab.n) := by
  refine largeEvenMarking_mono (fun lab R _ I F θ h hE6 => ?_) hD.2.2.2
  rw [h.1] at hE6
  exact absurd hE6 (by decide)

theorem e6TwoLeaf_marking_tag
    {X : Type} [Group X] (hX : commutator X = ⊤)
    {A : Subgroup (MulAut X)} {δ : MulAut X} {J : Subgroup X}
    (hD : DatumOn (fun t => t = .twE6) X A δ J) :
    GGMarkingAll (K := X) (fun lab _ _ _ _ _ => LargeEvenSplit 3 lab → lab.tag = .twE6) := by
  obtain ⟨-, lab0, hlab0, hraw0⟩ := hD.2.2.2
  have htag0 : lab0.tag = .twE6 :=
    e6TwoLeaf_rawDatum_elim_const'
      (largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim fun _ hh => hh.1) hraw0)
  have hHas0 : GGHasLabel lab0 (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw0
  have hrigid : GGLabelRigidInput := ggLabelRigidInput_holds
  intro P hP
  obtain ⟨-, lab, hlab, hraw⟩ := hP
  have hHas : GGHasLabel lab (X ⧸ Subgroup.center X) :=
    largeEvenRawDatum_mono (fun R _ I F h => ⟨h.2.2.choose⟩) hraw
  have hEq : lab0 = lab :=
    eq_of_ggLabelIso_of_e6Tag (hrigid lab0 lab _ hlab0 hlab hHas0 hHas) (Or.inr htag0)
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hPθ⟩
  exact ⟨hs, hna, θ, hPθ, fun _ => by rw [← hEq]; exact htag0⟩

end CFSG.StandardType.TablePThreeKG

end
