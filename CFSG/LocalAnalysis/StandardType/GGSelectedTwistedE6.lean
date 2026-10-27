module

public import CFSG.LieType.Steinberg.Minuscule.ChevExtras
public import CFSG.LieType.Steinberg.TwistedE6.Local
public import CFSG.Timmesfeld.LieEmbed.FieldEmbed
public import CFSG.LocalAnalysis.StandardType.GGSelectedF2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2ShortF4IsoLen
public import CFSG.LieType.CurtisTits.TwistedE6
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageBasic
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.LocalAnalysis.StandardType.GGReverseMarking
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagPowers
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6TwRankOne
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NLift
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.StandardType.GGNbrLSideTransport
public import CFSG.LocalAnalysis.StandardType.GGInducedCentralizerComponents
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixETwisted
public import CFSG.LocalAnalysis.StandardType.GGSixRCKU33Transport

public section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Exceptional CFSG.StandardType.RankOneXfer
  CFSG.Timmesfeld.LieEmbed

lemma sl2_map_upper {F K : Type*} [Field F] [Field K] (e : F →+* K) (c : F) :
    Matrix.SpecialLinearGroup.map e (sl2Upper c) = sl2Upper (e c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_sl2Upper]

lemma sl2_map_lower {F K : Type*} [Field F] [Field K] (e : F →+* K) (c : F) :
    Matrix.SpecialLinearGroup.map e (sl2Lower c) = sl2Lower (e c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.map_apply_coe, coe_sl2Lower]

theorem exists_sl2Hom_fixed {F K : Type*} [Field F] [Field K]
    (theta : K →+* K) (e : F →+* K) (he : ∀ c, theta (e c) = e c)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) F →* fixedGroup K theta,
      Function.Injective phi ∧
        (∀ c, (phi (sl2Upper c) : e6Data_valid.minGroup K) =
          e6Data_valid.xm K (Pi.single i 1) (e c)) ∧
        ∀ c, (phi (sl2Lower c) : e6Data_valid.minGroup K) =
          e6Data_valid.xm K (-Pi.single i 1) (e c) := by
  obtain ⟨phi, hinj, hupper, hlower⟩ := e6Data_valid.exists_sl2Hom K i
  let Phi := phi.comp (Matrix.SpecialLinearGroup.map e)
  have hfixed : ∀ M, Phi M ∈ fixedGroup K theta := by
    have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
        (fixedGroup K theta).comap Phi := by
      rw [← closure_sl2Upper_sl2Lower_eq_top]
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · change Phi (sl2Upper c) ∈ fixedGroup K theta
        rw [mem_fixedGroup]
        change sigma K theta (phi (Matrix.SpecialLinearGroup.map e (sl2Upper c))) =
          phi (Matrix.SpecialLinearGroup.map e (sl2Upper c))
        rw [sl2_map_upper, hupper, sigma_xm_single, hi, he]
      · change Phi (sl2Lower c) ∈ fixedGroup K theta
        rw [mem_fixedGroup]
        change sigma K theta (phi (Matrix.SpecialLinearGroup.map e (sl2Lower c))) =
          phi (Matrix.SpecialLinearGroup.map e (sl2Lower c))
        rw [sl2_map_lower, hlower, sigma_xm_neg_single, hi, he]
    exact fun M => hle (Subgroup.mem_top M)
  refine ⟨Phi.codRestrict _ hfixed, ?_, ?_, ?_⟩
  · intro M N h
    apply Matrix.SpecialLinearGroup.ext
    intro a b
    apply e.injective
    have hMN := hinj (congrArg Subtype.val h)
    exact congrArg (fun P : Matrix.SpecialLinearGroup (Fin 2) K =>
      (P : Matrix (Fin 2) (Fin 2) K) a b) hMN
  · intro c
    change phi (Matrix.SpecialLinearGroup.map e (sl2Upper c)) = _
    rw [sl2_map_upper, hupper]
  · intro c
    change phi (Matrix.SpecialLinearGroup.map e (sl2Lower c)) = _
    rw [sl2_map_lower, hlower]

theorem map_sl2UpperUniSub_eq_twistedRootGroup {F K : Type*} [Field F] [Field K]
    (theta : K →+* K) (e : F →+* K) (he : ∀ c, theta (e c) = e c)
    (hfixed : ∀ c, theta c = c → ∃ a, e a = c)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i)
    (phi : Matrix.SpecialLinearGroup (Fin 2) F →* fixedGroup K theta)
    (hupper : ∀ c, (phi (sl2Upper c) : e6Data_valid.minGroup K) =
      e6Data_valid.xm K (Pi.single i 1) (e c)) :
    (sl2UpperUniSub F).map phi = twistedRootGroup K theta (proj (Pi.single i 1)) := by
  have hroot : IsRoot .E6 (Pi.single i 1) := isRoot_single _ _
  have hrho : rho (Pi.single i 1) = Pi.single i 1 := by rw [rho_single, hi]
  apply le_antisymm
  · rintro _ ⟨M, ⟨c, rfl⟩, rfl⟩
    exact (mem_twistedRootGroup_iff_of_fixed theta hroot rfl hrho _).mpr
      ⟨e c, he c, hupper c⟩
  · intro g hg
    obtain ⟨c, hc, hgc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed theta hroot rfl hrho g).mp hg
    obtain ⟨a, rfl⟩ := hfixed c hc
    exact Subgroup.mem_map.mpr ⟨sl2Upper a, ⟨a, rfl⟩,
      Subtype.ext ((hupper a).trans hgc.symm)⟩

theorem exists_sl2Hom_fixed_root_pair {F K : Type*} [Field F] [Field K]
    (theta : K →+* K) (e : F →+* K) (he : ∀ c, theta (e c) = e c)
    (hfixed : ∀ c, theta c = c → ∃ a, e a = c)
    (i : Fin (Tag.rank .E6)) (hi : rhoPerm i = i) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) F →* fixedGroup K theta,
      Function.Injective phi ∧ (sl2UpperUniSub F).map phi =
        twistedRootGroup K theta (proj (Pi.single i 1)) ∧
      phi.range = twistedRootGroup K theta (proj (Pi.single i 1)) ⊔
        twistedRootGroup K theta (-proj (Pi.single i 1)) := by
  obtain ⟨phi, hinj, hupper, hlower⟩ := exists_sl2Hom_fixed theta e he i hi
  have hroot : IsRoot .E6 (Pi.single i 1) := isRoot_single _ _
  have hrho : rho (Pi.single i 1) = Pi.single i 1 := by rw [rho_single, hi]
  have hneg : IsRoot .E6 (-Pi.single i 1) := isRoot_neg_single _ _
  have hrhoneg : rho (-Pi.single i 1) = -Pi.single i 1 := by rw [rho_neg_single, hi]
  have hU : (sl2UpperUniSub F).map phi =
      twistedRootGroup K theta (proj (Pi.single i 1)) :=
    map_sl2UpperUniSub_eq_twistedRootGroup theta e he hfixed i hi phi hupper
  have hL : twistedRootGroup K theta (-proj (Pi.single i 1)) ≤ phi.range := by
    intro g hg
    have hg' : g ∈ twistedRootGroup K theta (proj (-Pi.single i 1)) := by
      simpa only [map_neg] using hg
    obtain ⟨c, hc, hgc⟩ :=
      (mem_twistedRootGroup_iff_of_fixed theta hneg rfl hrhoneg g).mp hg'
    obtain ⟨a, rfl⟩ := hfixed c hc
    exact ⟨sl2Lower a, Subtype.ext ((hlower a).trans hgc.symm)⟩
  have hle : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) ≤
      (twistedRootGroup K theta (proj (Pi.single i 1)) ⊔
        twistedRootGroup K theta (-proj (Pi.single i 1))).comap phi := by
    rw [← closure_sl2Upper_sl2Lower_eq_top, Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · apply Subgroup.mem_comap.mpr
      refine Subgroup.mem_sup_left ?_
      rw [← hU]
      exact Subgroup.mem_map.mpr ⟨sl2Upper c, ⟨c, rfl⟩, rfl⟩
    · apply Subgroup.mem_comap.mpr
      refine Subgroup.mem_sup_right ?_
      have hmem := (mem_twistedRootGroup_iff_of_fixed theta hneg rfl hrhoneg
        (phi (sl2Lower c))).mpr ⟨e c, he c, hlower c⟩
      simpa only [map_neg] using hmem
  refine ⟨phi, hinj, hU, le_antisymm ?_ (sup_le ?_ hL)⟩
  · rintro _ ⟨A, rfl⟩
    exact hle (Subgroup.mem_top A)
  · intro g hg
    rw [← hU] at hg
    obtain ⟨A, _, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨A, rfl⟩

theorem exists_sl2Hom_twistedE6_long_pair (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    ∃ phi : Matrix.SpecialLinearGroup (Fin 2) (GaloisField p f) →* twistedE6Group p f,
      Function.Injective phi ∧ (sl2UpperUniSub (GaloisField p f)).map phi =
        (twistedE6Datum p f).rootGroup (Pi.single (1 : Fin 4) 1) ∧
      phi.range = (twistedE6Datum p f).rootGroup (Pi.single (1 : Fin 4) 1) ⊔
        (twistedE6Datum p f).rootGroup (-Pi.single (1 : Fin 4) 1) := by
  obtain ⟨phi, hinj, hupper, hrange⟩ := exists_sl2Hom_fixed_root_pair (frobQ p f)
    (gfEmbed p f hf).toRingHom (frobQ_gfEmbed p f hf)
    (fun c hc => (frobQ_eq_iff_mem_range p f hf c).mp hc)
    (3 : Fin 6) rfl
  have hp : proj (Pi.single (3 : Fin 6) 1) = Pi.single (1 : Fin 4) 1 := by
    funext j
    fin_cases j <;> rfl
  refine ⟨phi, hinj, ?_, ?_⟩
  · change (sl2UpperUniSub (GaloisField p f)).map phi =
      twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (Pi.single (1 : Fin 4) 1)
    rwa [hp] at hupper
  · change phi.range =
      twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (Pi.single (1 : Fin 4) 1) ⊔
        twistedRootGroup (GaloisField p (2 * f)) (frobQ p f) (-Pi.single (1 : Fin 4) 1)
    rwa [hp] at hrange

end CFSG.LieType.Steinberg.TwistedE6

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.TwistedE6

theorem ggPsiInnerDiag_mem_normalizer_twistedE6 {G : Type} [Group G] [Finite G]
    {G0 : Subgroup G} {f : ℕ} {psi : (ggU .twistedE6 0 f).K →* G} {c : G}
    (hpsi : GGPresentsG0 G0 (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (h : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi c) :
    c ∈ Subgroup.normalizer (G0 : Set G) := by
  have hgen : (⨆ gamma ∈ (ggU .twistedE6 0 f).D.roots,
      (ggU .twistedE6 0 f).D.rootGroup gamma) = ⊤ :=
    iSup_twistedDatum_rootGroup (frobQ 2 f) (frobQ_frobQ 2 f hpsi.1.1.2.1)
  have hc := mem_normalizer_of_ggPsiInnerDiag hgen h
  rwa [hpsi.2.1.1] at hc

theorem ggPsiInnerDiag_zpowers_twistedE6 {G : Type} [Group G] [Finite G]
    {G0 : Subgroup G} {f : ℕ} {psi : (ggU .twistedE6 0 f).K →* G} {x : G}
    (hpsi : GGPresentsG0 G0 (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) :
    ∀ z ∈ Subgroup.zpowers x, GGPsiInnerDiag (ggU .twistedE6 0 f).D psi z := by
  have hxN : x ∈ Subgroup.normalizer (psi.range : Set G) := by
    simpa only [hpsi.2.1.1] using ggPsiInnerDiag_mem_normalizer_twistedE6 hpsi hdiag
  exact hdiag.forall_mem_zpowers hxN

theorem exists_selectedSL2Model_twistedE6_long :
    GGLongRoot (ggU .twistedE6 0 1).D (Pi.single (1 : Fin 4) 1) ∧
    ∃ model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 1).D (GaloisField 2 1)
      (Pi.single (1 : Fin 4) 1), model.phi.range =
        ggRootLevi (ggU .twistedE6 0 1).D (Pi.single (1 : Fin 4) 1) := by
  have hlong : GGLongRoot (ggU .twistedE6 0 1).D (Pi.single (1 : Fin 4) 1) :=
    (LieKnownR2.Short.f4_ggLongRoot_single_iff (GaloisField 2 1)
      ⟨1, by change 1 < Tag.rank .F4; decide⟩).2 le_rfl
  obtain ⟨phi, hinj, hupper, hrange⟩ := exists_sl2Hom_twistedE6_long_pair 2 1 le_rfl
  have hroot : Pi.single (1 : Fin 4) 1 ∈ (ggU .twistedE6 0 1).D.roots := by
    change Pi.single (1 : Fin 4) 1 ∈
      (twistedDatum (GaloisField 2 (2 * 1)) (frobQ 2 1)).roots
    rw [twistedDatum_roots]
    exact isRoot_single _ _
  refine ⟨hlong, SelectedRoot.SelectedSL2Model.ofGF2Upper _ _ hroot phi hinj hupper, ?_⟩
  exact (congrArg MonoidHom.range
    (SelectedRoot.SelectedSL2Model.ofGF2Upper_phi _ _ hroot phi hinj hupper)).trans hrange

theorem exists_selectedSL2Model_twistedE6 :
    Nonempty (SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 1).D (GaloisField 2 1)
      (Pi.single (1 : Fin 4) 1)) := by
  obtain ⟨_, model, _⟩ := exists_selectedSL2Model_twistedE6_long
  exact ⟨model⟩

theorem ggConfig_L_eq_ggG0_of_twistedE6_central {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :
    L = ggG0 3 B x L D J := by
  have hU : CFSG.IsQuasisimple (ggU .twistedE6 0 f).K :=
    CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hpsi.1.1.2.1
  have hG0 : CFSG.Assembly.IsQuasisimple (ggG0 3 B x L D J) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
      hU psi hpsi.2.1.2
    erw [hpsi.2.1.1] at h
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have hL : IsComponentOf L
      (Subgroup.centralizer ({x} : Set G) ⊓ ggG0 3 B x L D J) :=
    ggIsComponentOf_inf_of_le hC.1.2.2.2.2.2.2.1.2.2.2.1 le_sup_left
  have hinf : Subgroup.centralizer ({x} : Set G) ⊓ ggG0 3 B x L D J =
      ggG0 3 B x L D J := by
    apply inf_eq_right.mpr
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcentral g hg)
  rw [hinf] at hL
  exact Line63.H5.eq_of_isComponentOf_of_isQuasisimple hL hG0

theorem ggSecFiveQTwoFieldTwoSelected_twistedE6_of_central {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J)
    (_hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 1).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 1).D .twistedE6 0 1 psi)
    (_hdiag : GGPsiInnerDiag (ggU .twistedE6 0 1).D psi x)
    (hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (psi' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        psi'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ psi'.range = L ∧
        ∃ (gamma : Fin (ggU .twistedE6 0 1).D.rank → ℤ)
          (delta : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 1).D (GaloisField 2 1) gamma)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) delta),
          ∃ u0 : (ggU .twistedE6 0 1).K,
            ((psi.comp (MulAut.conj u0).toMonoidHom).comp model.phi).range =
              (psi'.comp model'.phi).range := by
  have hLG0 := ggConfig_L_eq_ggG0_of_twistedE6_central hC psi hpsi hcentral
  obtain ⟨model⟩ := exists_selectedSL2Model_twistedE6
  refine ⟨.twistedE6, 0, psi, hpsi.1.1, hpsi.1.2, hpsi.2.1.2,
    hpsi.2.1.1.trans hLG0.symm, _, _, model, model, 1, ?_⟩
  have hconj : psi.comp (MulAut.conj (1 : (ggU .twistedE6 0 1).K)).toMonoidHom = psi := by
    ext g
    simp
  rw [hconj]

section FieldReduction

theorem ggInnerDiagOn_zpowers_twistedE6 {G : Type} [Group G] [Finite G]
    {G0 : Subgroup G} {f : ℕ} {psi : (ggU .twistedE6 0 f).K →* G} {x : G}
    (hpsi : GGPresentsG0 G0 (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) :
    GGInnerDiagOn (Subgroup.zpowers x) G0 := by
  have hxN := ggPsiInnerDiag_mem_normalizer_twistedE6 hpsi hdiag
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (G0 : Set G) := by
    rintro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Subgroup.normalizer (G0 : Set G)).zpow_mem hxN n
  have hpowers := ggPsiInnerDiag_zpowers_twistedE6 hpsi hdiag
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ hP => ⟨hN, fun z hz => hP z (hN hz) (hpowers z hz)⟩)
    (ggInnerDiagMarkingAt_twistedE6 G 0 f psi G0 hpsi)

theorem ggPresentsG0_twistedE6_parameters_of_qTwo {G U : Type} [Group G] [Group U]
    {G0 Bs : Subgroup G} {D : UniversalRootDatum U} {n f : ℕ} {psi : U →* G}
    (hpsi : GGPresentsG0 G0 D .twistedE6 n f psi)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs G0) : n = 0 ∧ f = 1 := by
  obtain ⟨_, a, ha, hrawa⟩ := largeEvenMarking_of_lieModel_centerQuot hpsi.2.2.1 hpsi.2.2.2
  obtain ⟨_, b, hb, hrawb⟩ := hq
  have hasA : GGHasLabel a (↥G0 ⧸ Subgroup.center ↥G0) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hrawa
    rintro R _ I F ⟨-, -, theta, -⟩
    exact ⟨theta⟩
  have hasB : GGHasLabel b (↥G0 ⧸ Subgroup.center ↥G0) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hrawb
    rintro R _ I F ⟨-, -, theta, -⟩
    exact ⟨theta⟩
  obtain ⟨R, _, I, F, _, _, theta, htag, hrank, _, hdeg⟩ :=
    largeEvenRawDatum_exists hrawa
  obtain ⟨R', _, I', F', _, _, theta', hqb, _, _⟩ := largeEvenRawDatum_exists hrawb
  have hta : a.tag = .twE6 := by
    cases ht : a.tag <;> simp [markTag, ht] at htag ⊢
    all_goals split_ifs at htag
  have hab : a = b := by
    have hi := ggLabelRigidInput_holds a b (↥G0 ⧸ Subgroup.center ↥G0)
      ha hb hasA hasB
    obtain ⟨t, r, k⟩ := a
    change t = .twE6 at hta
    subst t
    simpa [GGLabelIso] using hi
  have hn : n = 0 := by simpa [markRank, hta] using hrank.symm
  have haf : a.n = f := by simpa [markDeg, hta] using hdeg
  have hf2 : f < 2 := by simpa only [GGLabQTwo, ← hab, haf] using hqb
  have hf : 1 ≤ f := hpsi.1.1.2.1
  exact ⟨hn, by omega⟩

theorem ggSecFiveQTwoFieldTwoSelected_twistedE6_of_central_all_fields
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x)
    (hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (psi' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        psi'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ psi'.range = L ∧
        ∃ (gamma : Fin (ggU .twistedE6 0 f).D.rank → ℤ)
          (delta : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .twistedE6 0 f).D (GaloisField 2 1) gamma)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) delta),
          ∃ u0 : (ggU .twistedE6 0 f).K,
            ((psi.comp (MulAut.conj u0).toMonoidHom).comp model.phi).range =
              (psi'.comp model'.phi).range := by
  have hLG0 := ggConfig_L_eq_ggG0_of_twistedE6_central hC psi hpsi hcentral
  have hq0 := hq
  rw [hLG0] at hq0
  obtain ⟨_, hf⟩ := ggPresentsG0_twistedE6_parameters_of_qTwo hpsi hq0
  subst f
  exact ggSecFiveQTwoFieldTwoSelected_twistedE6_of_central hC hq psi hpsi hdiag hcentral

section ComponentFieldReduction

theorem ggConfig_field_one_of_twistedE6_qTwo {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) : f = 1 := by
  have hcyc := ggInnerDiagOn_zpowers_twistedE6 hpsi hdiag
  have hN := hcyc.le_normalizer
  have hMark : LargeEvenMarking ↥(ggG0 3 B x L D J)
      (fun _ _ _ I _ theta => ∀ z ∈ Subgroup.zpowers x, ∃ phi ∈ I,
        LargeEvenInduces theta (fun l l' => (l' : G) = z⁻¹ * l * z) phi) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hcyc
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  obtain ⟨a, b, ha, hb, hhasb, hdvd, hMa⟩ :=
    RCKC1.exists_labels_dvd_of_innerDiag_component (by norm_num) (by norm_num)
      (Subgroup.mem_zpowers x) hx3 hN hMark hC.isComponentOf_ggG0_inf
  obtain ⟨c, hc, hc1, hcne, -, -, hhasc⟩ := hC.exists_markedModel_and_hasLabel_of_qTwo hq
  have hi := ggLabelRigidInput_holds c b (↥L ⧸ Subgroup.center ↥L) hc hb hhasc hhasb
  have hbn : b.n = 1 := by
    rcases hi.n_cases with h | ⟨ht, hr⟩ | hdouble
    · exact h.symm.trans hc1
    · have hceq : c = ⟨.twD, 2, 1⟩ := by
        cases c
        simp only [LargeEvenLabel.mk.injEq]
        exact ⟨ht, hr, hc1⟩
      exact (hcne hceq).elim
    · have hpositive := hb.1
      omega
  have han : a.n = 1 := Nat.dvd_one.mp (by simpa only [hbn] using hdvd)
  have hqG0 : GGInnerDiagOnLabel GGLabQTwo 3 (Subgroup.zpowers x) (ggG0 3 B x L D J) := by
    refine largeEvenMarking_mono ?_ hMa
    rintro lab R _ I F theta ⟨hlab, hact⟩
    refine ⟨?_, hN, hact⟩
    change lab.n < 2
    rw [hlab, han]
    decide
  exact (ggPresentsG0_twistedE6_parameters_of_qTwo hpsi hqG0).2

theorem GGConfig.exists_marked_source_component_of_twistedE6_qTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) :
    f = 1 ∧ ∃ (lab : LargeEvenLabel) (M : Subgroup (ggU .twistedE6 0 f).K)
      (rho : ↥M →* ↥L) (e : ↥M ⧸ Subgroup.center ↥M ≃* ↥L ⧸ Subgroup.center ↥L),
      LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧ lab.tag ≠ .B2der ∧
      IsComponentOf M ((Subgroup.centralizer {x}).comap psi) ∧ M.map psi = L ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center ↥M ∧
      rho.ker = psi.ker.comap M.subtype ∧ L.subtype.comp rho = psi.comp M.subtype ∧
      (∀ m : ↥M, e (QuotientGroup.mk m) = QuotientGroup.mk (rho m)) ∧
      MarkedModel lab (↥M ⧸ Subgroup.center ↥M) ∧
      MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
  have hf := ggConfig_field_one_of_twistedE6_qTwo hC hq psi hpsi hdiag
  obtain ⟨lab, hlab, hn, htwD, hB2, hmodel, -⟩ :=
    hC.exists_markedModel_and_hasLabel_of_qTwo hq
  have hL : IsComponentOf L (((Subgroup.centralizer {x}).comap psi).map psi) := by
    rw [Subgroup.map_comap_eq, hpsi.2.1.1]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨M, hM0, hmap⟩ := CFSG.LocalAnalysis.GLTheoremA.I142N.exists_component_lift psi
    (fun u hu => hpsi.2.1.2 (MonoidHom.mem_ker.mpr hu))
    (CFSG.Assembly.isComponentOf_iff_open.mp hL)
  have hM : IsComponentOf M ((Subgroup.centralizer {x}).comap psi) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hM0
  let rho : ↥M →* ↥L := (psi.domRestrict M).codRestrict L (fun m => by
    change psi (m : (ggU .twistedE6 0 f).K) ∈ L
    rw [← hmap]
    exact Subgroup.mem_map_of_mem psi m.2)
  have hsurj : Function.Surjective rho := by
    rintro ⟨l, hl⟩
    have hl' : l ∈ M.map psi := by simpa only [hmap] using hl
    obtain ⟨m, hm, he⟩ := Subgroup.mem_map.mp hl'
    exact ⟨⟨m, hm⟩, Subtype.ext he⟩
  have hkerM : rho.ker ≤ Subgroup.center ↥M := by
    intro m hm
    change rho m = 1 at hm
    have hm1 : psi (m : (ggU .twistedE6 0 f).K) = 1 := congrArg Subtype.val hm
    have hz : (m : (ggU .twistedE6 0 f).K) ∈ Subgroup.center (ggU .twistedE6 0 f).K :=
      hpsi.2.1.2 (MonoidHom.mem_ker.mpr hm1)
    rw [Subgroup.mem_center_iff]
    intro m'
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (m' : (ggU .twistedE6 0 f).K))
  have hkerEq : rho.ker = psi.ker.comap M.subtype := by
    ext m
    change rho m = 1 ↔ psi (m : (ggU .twistedE6 0 f).K) = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have heq : L.subtype.comp rho = psi.comp M.subtype := by
    ext m
    rfl
  obtain ⟨e, he⟩ := ggNbrLSide_centralQuot_equiv rho hsurj hkerM hM.2.2.1
  exact ⟨hf, lab, M, rho, e, hlab, hn, htwD, hB2, hM, hmap, hsurj, hkerM, hkerEq,
    heq, he, MarkedModel.of_mulEquiv e.symm hmodel, hmodel⟩

section NativeComponents

open CFSG.LieType.RootSystem CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.HardMathSupport.Solomon.Coordinator

theorem GGConfig.exists_native_action_of_twistedE6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) :
    ∃ (pi : (ggU .twistedE6 0 f).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))),
      Function.Surjective pi ∧ pi.ker = Subgroup.center (ggU .twistedE6 0 f).K ∧
      (∀ z, ((pi z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (Subtype.val (show twistedE6Group 2 f from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∧
      alpha ∈ LayerSixE.twInndiagAut f ∧ alpha ^ 3 = 1 ∧
      LayerSixE.GGInduces pi psi x alpha ∧
      (alpha = 1 ↔ x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) := by
  have hf : 1 ≤ f := hpsi.1.1.2.1
  obtain ⟨pi, hpi, hpiker, _, hpival⟩ := LayerSixE.exists_model_twistedE6 hf
  have hkpsi : psi.ker ≤ Subgroup.center (ggU .twistedE6 0 f).K := hpsi.2.1.2
  have hkp : psi.ker ≤ pi.ker := hkpsi.trans hpiker.ge
  have hxN : x ∈ Subgroup.normalizer (psi.range : Set G) := by
    simpa only [hpsi.2.1.1] using ggPsiInnerDiag_mem_normalizer_twistedE6 hpsi hdiag
  obtain ⟨alpha, halphaD, hind⟩ :=
    LayerSixE.exists_induces_twistedE6 hf hpival psi hkpsi hkp hxN hdiag
  have hx3 : x ^ 3 = 1 := hC.1.2.2.2.2.2.2.1.1.1.2 x hC.1.2.2.2.2.2.2.1.2.1
  have halpha3 : alpha ^ 3 = 1 := by
    have hp := hind.pow hkp hxN 3
    rw [hx3] at hp
    exact LayerSixE.GGInduces.unique hpi (Subgroup.one_mem _) hp (LayerSixE.GGInduces.one hkp)
  have : Group.IsPerfect (twistedE6Group 2 f) :=
    (CFSG.LieType.CurtisTits.isQuasisimple_twistedE6 2 f hf).1
  have htrivial : alpha = 1 ↔ x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G) := by
    have ht : alpha = 1 ↔ x ∈ Subgroup.centralizer (psi.range : Set G) :=
      hind.eq_one_iff_mem_centralizer hpi hpiker.le hxN
    rw [hpsi.2.1.1] at ht
    exact ht
  exact ⟨pi, alpha, hpi, hpiker, hpival, halphaD, halpha3, hind, htrivial⟩

theorem GGConfig.exists_marked_native_component_of_twistedE6_qTwo
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU .twistedE6 0 f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU .twistedE6 0 f).D .twistedE6 0 f psi)
    (hdiag : GGPsiInnerDiag (ggU .twistedE6 0 f).D psi x) :
    f = 1 ∧ ∃ (pi : (ggU .twistedE6 0 f).K →*
      ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (alpha : MulAut ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)))
      (lab : LargeEvenLabel) (M : Subgroup (ggU .twistedE6 0 f).K)
      (rho : ↥M →* ↥L)
      (eML : ↥M ⧸ Subgroup.center ↥M ≃* ↥L ⧸ Subgroup.center ↥L),
      Function.Surjective pi ∧ pi.ker = Subgroup.center (ggU .twistedE6 0 f).K ∧
      (∀ z, ((pi z : graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) :
        ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))) =
        ((e6IsogenyT (GaloisField 2 (2 * f))
          (Subtype.val (show twistedE6Group 2 f from z)) :
          adjointGroup TwistTag.E6.tag (GaloisField 2 (2 * f))) :
            ModGL TwistTag.E6.tag (GaloisField 2 (2 * f)))) ∧
      alpha ∈ LayerSixE.twInndiagAut f ∧ alpha ^ 3 = 1 ∧
      LayerSixE.GGInduces pi psi x alpha ∧
      (alpha = 1 ↔ x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) ∧
      IsComponentOf M ((Subgroup.centralizer {x}).comap psi) ∧ M.map psi = L ∧
      IsComponentOf (M.map pi) (fixSubgroup alpha) ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center ↥M ∧
      rho.ker = psi.ker.comap M.subtype ∧ L.subtype.comp rho = psi.comp M.subtype ∧
      (∀ m : ↥M, eML (QuotientGroup.mk m) = QuotientGroup.mk (rho m)) ∧
      LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧ lab.tag ≠ .B2der ∧
      MarkedModel lab (↥M ⧸ Subgroup.center ↥M) ∧
      Nonempty (↥M ⧸ Subgroup.center ↥M ≃*
        ↥(M.map pi) ⧸ Subgroup.center ↥(M.map pi)) ∧
      MarkedModel lab (↥(M.map pi) ⧸ Subgroup.center ↥(M.map pi)) ∧
      MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
  obtain ⟨hfield, lab, M, rho, eML, hlab, hn, htwD, hB2, hM, hmap,
    hrho, hrhoker, hrhokerEq, hrhoEq, heML, hmodelM, hmodelL⟩ :=
    hC.exists_marked_source_component_of_twistedE6_qTwo hq psi hpsi hdiag
  obtain ⟨pi, alpha, hpi, hpiker, hpival, halphaD, halpha3, hind, htrivial⟩ :=
    hC.exists_native_action_of_twistedE6 psi hpsi hdiag
  have hxN : x ∈ Subgroup.normalizer (psi.range : Set G) := by
    simpa only [hpsi.2.1.1] using ggPsiInnerDiag_mem_normalizer_twistedE6 hpsi hdiag
  have hnative : IsComponentOf (M.map pi) (fixSubgroup alpha) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr
      (hind.isComponentOf_map_centralizer_comap hpi hpiker.le hxN
        (CFSG.Assembly.isComponentOf_iff_open.mp hM))
  obtain ⟨eMN⟩ := CFSG.LocalAnalysis.GLTheoremA.I141F.nonempty_centerQuot_map
    pi hpiker.le (J := M) ⟨hM.2.2.1⟩
  exact ⟨hfield, pi, alpha, lab, M, rho, eML, hpi, hpiker, hpival, halphaD, halpha3, hind, htrivial,
    hM, hmap, hnative, hrho, hrhoker, hrhokerEq, hrhoEq, heML, hlab, hn, htwD, hB2, hmodelM, ⟨eMN⟩,
    MarkedModel.of_mulEquiv eMN hmodelM, hmodelL⟩

end NativeComponents

end ComponentFieldReduction

end FieldReduction

end CFSG.StandardType
