module

public import CFSG.LocalAnalysis.StandardType.GGSelectedTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMarkingE6
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridgeInner
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple

public section

namespace CFSG.StandardType

namespace FieldTwoExc

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
open CFSG.Open (StatedLieTag)

@[expose] def GGExcFour (t : StatedLieTag) : Prop :=
  t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8

section Cert


theorem iSup_rootGroup_exc {t : StatedLieTag} (ht : GGExcFour t) (n f : ℕ) :
    ⨆ γ ∈ (ggU t n f).D.roots, (ggU t n f).D.rootGroup γ = ⊤ := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact (Adjoint.f4_isCTGroupDatum (GaloisField 2 f)).iSup_eq_top
  · exact (Minuscule.e6Datum_isCTGroupDatum (GaloisField 2 f)).iSup_eq_top
  · exact (Minuscule.e7Datum_isCTGroupDatum (GaloisField 2 f)).iSup_eq_top
  · exact (Adjoint.e8_isCTGroupDatum (GaloisField 2 f)).iSup_eq_top

theorem isQuasisimple_exc {t : StatedLieTag} (ht : GGExcFour t) (n f : ℕ) :
    IsQuasisimple (ggU t n f).K := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact Adjoint.isQuasisimple_f4 (GaloisField 2 f)
  · exact CFSG.LieType.CurtisTits.isQuasisimple_e6 (GaloisField 2 f)
  · exact CFSG.LieType.CurtisTits.isQuasisimple_e7 (GaloisField 2 f)
  · exact Adjoint.isQuasisimple_e8 (GaloisField 2 f)

theorem ggInnerDiagMarkingAt_exc {t : StatedLieTag} (ht : GGExcFour t) :
    GGInnerDiagMarkingAt t := by
  rcases ht with rfl | rfl | rfl | rfl
  · exact ggInnerDiagMarkingAt_of_diagInner (.inr (.inr (.inr (.inl rfl))))
      (ggPsiDiagInnerAt_of_ggInnerTag _ (.inr (.inr (.inr (.inl rfl)))))
  · exact ggInnerDiagMarkingAt_E6
  · exact ggInnerDiagMarkingAt_of_diagInner (.inr (.inr (.inr (.inr (.inl rfl)))))
      (ggPsiDiagInnerAt_of_ggInnerTag _ (.inr (.inr (.inr (.inr (.inl rfl))))))
  · exact ggInnerDiagMarkingAt_of_diagInner (.inr (.inr (.inr (.inr (.inr rfl)))))
      (ggPsiDiagInnerAt_of_ggInnerTag _ (.inr (.inr (.inr (.inr (.inr rfl))))))

theorem exists_selectedSL2Model_E6 :
    ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU .E6 0 1).D (GaloisField 2 1) γ) := by
  obtain ⟨phi, hinj, hupper, -⟩ :=
    Minuscule.e6Data_valid.exists_sl2Hom (GaloisField 2 1) (0 : Fin (Tag.rank .E6))
  have hroot : (Pi.single (0 : Fin (Tag.rank .E6)) 1 : Fin (Tag.rank .E6) → ℤ) ∈
      (Minuscule.e6Datum (GaloisField 2 1)).roots :=
    (Minuscule.e6Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E6
      (GaloisField 2 1)).2
      (isRoot_single _ _)
  have hup : (RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map phi =
      (Minuscule.e6Datum (GaloisField 2 1)).rootGroup (Pi.single (0 : Fin (Tag.rank .E6)) 1) := by
    ext g
    constructor
    · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
      exact (Minuscule.e6Data_valid.mem_rootGroup (GaloisField 2 1)).2 ⟨c, (hupper c).symm⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (Minuscule.e6Data_valid.mem_rootGroup (GaloisField 2 1)).1 hg
      exact ⟨sl2Upper c, ⟨c, rfl⟩, hupper c⟩
  exact ⟨_, ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (Minuscule.e6Datum (GaloisField 2 1)) _
    hroot phi hinj hup⟩⟩

theorem exists_selectedSL2Model_E7 :
    ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU .E7 0 1).D (GaloisField 2 1) γ) := by
  obtain ⟨phi, hinj, hupper, -⟩ :=
    Minuscule.e7Data_valid.exists_sl2Hom (GaloisField 2 1) (0 : Fin (Tag.rank .E7))
  have hroot : (Pi.single (0 : Fin (Tag.rank .E7)) 1 : Fin (Tag.rank .E7) → ℤ) ∈
      (Minuscule.e7Datum (GaloisField 2 1)).roots :=
    (Minuscule.e7Data_valid.mem_minDatum_roots Minuscule.isFiniteType_cartan_E7
      (GaloisField 2 1)).2
      (isRoot_single _ _)
  have hup : (RankOneXfer.sl2UpperUniSub (GaloisField 2 1)).map phi =
      (Minuscule.e7Datum (GaloisField 2 1)).rootGroup (Pi.single (0 : Fin (Tag.rank .E7)) 1) := by
    ext g
    constructor
    · rintro ⟨A, ⟨c, rfl⟩, rfl⟩
      exact (Minuscule.e7Data_valid.mem_rootGroup (GaloisField 2 1)).2 ⟨c, (hupper c).symm⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (Minuscule.e7Data_valid.mem_rootGroup (GaloisField 2 1)).1 hg
      exact ⟨sl2Upper c, ⟨c, rfl⟩, hupper c⟩
  exact ⟨_, ⟨SelectedRoot.SelectedSL2Model.ofGF2Upper (Minuscule.e7Datum (GaloisField 2 1)) _
    hroot phi hinj hup⟩⟩

variable {G : Type} [Group G] [Finite G]

theorem ggPsiInnerDiag_mem_normalizer_exc {t : StatedLieTag} (ht : GGExcFour t)
    {G0 : Subgroup G} {n f : ℕ} {psi : (ggU t n f).K →* G} {c : G}
    (hpsi : GGPresentsG0 G0 (ggU t n f).D t n f psi)
    (h : GGPsiInnerDiag (ggU t n f).D psi c) :
    c ∈ Subgroup.normalizer (G0 : Set G) := by
  have hc := mem_normalizer_of_ggPsiInnerDiag (iSup_rootGroup_exc ht n f) h
  rwa [hpsi.2.1.1] at hc

theorem ggInnerDiagOn_zpowers_exc {t : StatedLieTag} (ht : GGExcFour t)
    {G0 : Subgroup G} {n f : ℕ} {psi : (ggU t n f).K →* G} {x : G}
    (hpsi : GGPresentsG0 G0 (ggU t n f).D t n f psi)
    (hdiag : GGPsiInnerDiag (ggU t n f).D psi x) :
    GGInnerDiagOn (Subgroup.zpowers x) G0 := by
  have hxN := ggPsiInnerDiag_mem_normalizer_exc ht hpsi hdiag
  have hN : Subgroup.zpowers x ≤ Subgroup.normalizer (G0 : Set G) := by
    rintro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Subgroup.normalizer (G0 : Set G)).zpow_mem hxN k
  have hxN' : x ∈ Subgroup.normalizer (psi.range : Set G) := by
    simpa only [hpsi.2.1.1] using hxN
  have hpowers := hdiag.forall_mem_zpowers hxN'
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ hP => ⟨hN, fun z hz => hP z (hN hz) (hpowers z hz)⟩)
    (ggInnerDiagMarkingAt_exc ht G n f psi G0 hpsi)

omit [Finite G] in
theorem ggPresentsG0_exc_parameters_of_qTwo {t : StatedLieTag} (ht : GGExcFour t) {U : Type}
    [Group U] {G0 Bs : Subgroup G} {D : UniversalRootDatum U} {n f : ℕ} {psi : U →* G}
    (hpsi : GGPresentsG0 G0 D t n f psi) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs G0) :
    f = 1 := by
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
  obtain ⟨R, _, I, F, _, _, theta, htag, -, _, hdeg⟩ := largeEvenRawDatum_exists hrawa
  obtain ⟨R', _, I', F', _, _, theta', hqb, _, _⟩ := largeEvenRawDatum_exists hrawb
  have hi := ggLabelRigidInput_holds a b (↥G0 ⧸ Subgroup.center ↥G0) ha hb hasA hasB
  obtain ⟨ta, ra, ka⟩ := a
  have hab : (⟨ta, ra, ka⟩ : LargeEvenLabel) = b := by
    rcases ht with rfl | rfl | rfl | rfl <;>
    · cases ta <;> simp [markTag] at htag
      all_goals first
        | simpa [GGLabelIso] using hi
        | (split_ifs at htag)
  have haf : ka = f := by
    rcases ht with rfl | rfl | rfl | rfl <;>
    · cases ta <;> simp [markTag] at htag
      all_goals first
        | simpa [markDeg] using hdeg
        | (split_ifs at htag)
  have hf2 : f < 2 := by simpa only [GGLabQTwo, ← hab, haf] using hqb
  have hf : 1 ≤ f := hpsi.1.1.2.1
  omega

section ComponentFieldReduction

theorem ggConfig_field_one_of_exc_qTwo {t : StatedLieTag} (ht : GGExcFour t)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU t n f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f psi)
    (hdiag : GGPsiInnerDiag (ggU t n f).D psi x) : f = 1 := by
  have hcyc := ggInnerDiagOn_zpowers_exc ht hpsi hdiag
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
    rcases hi.n_cases with h | ⟨ht', hr⟩ | hdouble
    · exact h.symm.trans hc1
    · have hceq : c = ⟨.twD, 2, 1⟩ := by
        cases c
        simp only [LargeEvenLabel.mk.injEq]
        exact ⟨ht', hr, hc1⟩
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
  exact ggPresentsG0_exc_parameters_of_qTwo ht hpsi hqG0

theorem GGConfig.exists_marked_source_component_of_exc_qTwo {t : StatedLieTag}
    (ht : GGExcFour t) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU t n f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f psi)
    (hdiag : GGPsiInnerDiag (ggU t n f).D psi x) :
    f = 1 ∧ ∃ (lab : LargeEvenLabel) (M : Subgroup (ggU t n f).K)
      (rho : ↥M →* ↥L) (e : ↥M ⧸ Subgroup.center ↥M ≃* ↥L ⧸ Subgroup.center ↥L),
      LargeEvenInLambda2 lab ∧ lab.n = 1 ∧ lab ≠ ⟨.twD, 2, 1⟩ ∧ lab.tag ≠ .B2der ∧
      IsComponentOf M ((Subgroup.centralizer {x}).comap psi) ∧ M.map psi = L ∧
      Function.Surjective rho ∧ rho.ker ≤ Subgroup.center ↥M ∧
      rho.ker = psi.ker.comap M.subtype ∧ L.subtype.comp rho = psi.comp M.subtype ∧
      (∀ m : ↥M, e (QuotientGroup.mk m) = QuotientGroup.mk (rho m)) ∧
      MarkedModel lab (↥M ⧸ Subgroup.center ↥M) ∧
      MarkedModel lab (↥L ⧸ Subgroup.center ↥L) := by
  have hf := ggConfig_field_one_of_exc_qTwo ht hC hq psi hpsi hdiag
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
    change psi (m : (ggU t n f).K) ∈ L
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
    have hm1 : psi (m : (ggU t n f).K) = 1 := congrArg Subtype.val hm
    have hz : (m : (ggU t n f).K) ∈ Subgroup.center (ggU t n f).K :=
      hpsi.2.1.2 (MonoidHom.mem_ker.mpr hm1)
    rw [Subgroup.mem_center_iff]
    intro m'
    exact Subtype.ext (Subgroup.mem_center_iff.mp hz (m' : (ggU t n f).K))
  have hkerEq : rho.ker = psi.ker.comap M.subtype := by
    ext m
    change rho m = 1 ↔ psi (m : (ggU t n f).K) = 1
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have heq : L.subtype.comp rho = psi.comp M.subtype := by
    ext m
    rfl
  obtain ⟨e, he⟩ := ggNbrLSide_centralQuot_equiv rho hsurj hkerM hM.2.2.1
  exact ⟨hf, lab, M, rho, e, hlab, hn, htwD, hB2, hM, hmap, hsurj, hkerM, hkerEq,
    heq, he, MarkedModel.of_mulEquiv e.symm hmodel, hmodel⟩

end ComponentFieldReduction

theorem eq_ggG0_of_isComponentOf_of_exc_central {t : StatedLieTag} (ht : GGExcFour t) {p : ℕ}
    {B : Subgroup G} {x z : G} {L D J X : Subgroup G} {n f : ℕ} (psi : (ggU t n f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f psi)
    (hX : IsComponentOf X (ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G)))
    (hcentral : z ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    X = ggG0 p B x L D J := by
  have hG0 : CFSG.Assembly.IsQuasisimple (ggG0 p B x L D J) := by
    have h := CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_range_of_ker_le_center
      (isQuasisimple_exc ht n f) psi hpsi.2.1.2
    erw [hpsi.2.1.1] at h
    exact ⟨h.1.commutator_eq_top, h.2.1⟩
  have hinf : ggG0 p B x L D J ⊓ Subgroup.centralizer ({z} : Set G) = ggG0 p B x L D J := by
    apply inf_eq_left.mpr
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hcentral g hg)
  rw [hinf] at hX
  exact Line63.H5.eq_of_isComponentOf_of_isQuasisimple hX hG0

theorem ggConfig_L_eq_ggG0_of_exc_central {t : StatedLieTag} (ht : GGExcFour t) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hC : GGConfig p B Bs x L D J) (psi : (ggU t n f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f psi)
    (hcentral : x ∈ Subgroup.centralizer (ggG0 p B x L D J : Set G)) :
    L = ggG0 p B x L D J := by
  have hL : IsComponentOf L
      (Subgroup.centralizer ({x} : Set G) ⊓ ggG0 p B x L D J) :=
    ggIsComponentOf_inf_of_le hC.1.2.2.2.2.2.2.1.2.2.2.1 le_sup_left
  rw [inf_comm] at hL
  exact eq_ggG0_of_isComponentOf_of_exc_central ht psi hpsi hL hcentral

theorem ggSecFiveQTwoFieldTwoSelected_exc_of_central {t : StatedLieTag} (ht : GGExcFour t)
    (hsel : ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU t 0 1).D (GaloisField 2 1) γ))
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    (hC : GGConfig 3 B Bs x L D J) (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (psi : (ggU t n f).K →* G)
    (hpsi : GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f psi)
    (hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)) :
    ∃ (t' : StatedLieTag) (n' : ℕ) (psi' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        psi'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ psi'.range = L ∧
        ∃ (gamma : Fin (ggU t n f).D.rank → ℤ) (delta : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) gamma)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) delta),
          ∃ u0 : (ggU t n f).K,
            ((psi.comp (MulAut.conj u0).toMonoidHom).comp model.phi).range =
              (psi'.comp model'.phi).range := by
  have hLG0 := ggConfig_L_eq_ggG0_of_exc_central ht hC psi hpsi hcentral
  have hq0 := hq
  rw [hLG0] at hq0
  have hf := ggPresentsG0_exc_parameters_of_qTwo ht hpsi hq0
  subst hf
  have hn : n = 0 := by
    have hadm := hpsi.1.1
    rcases ht with rfl | rfl | rfl | rfl <;> exact hadm.2.2
  subst hn
  obtain ⟨γ, ⟨model⟩⟩ := hsel
  refine ⟨t, 0, psi, hpsi.1.1, hpsi.1.2, hpsi.2.1.2, hpsi.2.1.1.trans hLG0.symm, _, _, model,
    model, 1, ?_⟩
  have hconj : psi.comp (MulAut.conj (1 : (ggU t 0 1).K)).toMonoidHom = psi := by
    ext g
    simp
  rw [hconj]

theorem ggSecFiveQTwoFieldTwoSelectedAt_exc_of_noncentral {t : StatedLieTag} (ht : GGExcFour t)
    (hsel : ∃ γ, Nonempty (SelectedRoot.SelectedSL2Model (ggU t 0 1).D (GaloisField 2 1) γ))
    (hnc : ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
      GGConfig 3 B Bs x L D J → GGInnerDiagOnLabel GGLabQTwo 3 Bs L →
        ∀ (n f : ℕ) (ψ : (ggU t n f).K →* G),
          GGPresentsG0 (ggG0 3 B x L D J) (ggU t n f).D t n f ψ →
            GGPsiInnerDiag (ggU t n f).D ψ x →
              x ∉ Subgroup.centralizer (ggG0 3 B x L D J : Set G) →
                ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
                  StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
                    ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
                    ∃ (γ : Fin (ggU t n f).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
                      (model : SelectedRoot.SelectedSL2Model (ggU t n f).D (GaloisField 2 1) γ)
                      (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
                      ∃ u₀ : (ggU t n f).K,
                        ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
                          (ψ'.comp model'.phi).range) :
    GGSecFiveQTwoFieldTwoSelectedAt t := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  by_cases hcentral : x ∈ Subgroup.centralizer (ggG0 3 B x L D J : Set G)
  · exact ggSecFiveQTwoFieldTwoSelected_exc_of_central ht hsel hC hq ψ hpres hcentral
  · exact hnc G B Bs x L D J hC hq n f ψ hpres hdiag hcentral

end Cert

end FieldTwoExc

end CFSG.StandardType

end
