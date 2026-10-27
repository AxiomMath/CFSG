module

public import CFSG.LocalAnalysis.StandardType.GGQTwoCavSetup
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBRMarkedCharTwoCover
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenKernel

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.GroupTheory.FixedCentralQuotientFamily
  CFSG.ComponentClassification.CatalogueBFixedCentralQuotient

variable {G : Type} [Group G] {L D : Subgroup G}
  (hDL : D ≤ Subgroup.normalizer (L : Set G)) {R : Type} [Group R]
  (θ : L ⧸ Subgroup.center L ≃* R)

theorem quotientCentralizer_map :
    (QTwoCentralizer.quotientCentralizer L D hDL).map θ.toMonoidHom =
      (⨅ d : D, ggFix (ggBeta L θ hDL d)) := by
  ext y
  rw [Subgroup.mem_iInf]
  constructor
  · rintro ⟨q, hq, rfl⟩ d
    have hfix := Subgroup.mem_iInf.mp hq d
    change ggBeta L θ hDL d (θ q) = θ q
    induction q using QuotientGroup.induction_on with
    | H l =>
      have hfix' : ((QTwoCentralizer.action L D hDL d) l : L ⧸ Subgroup.center L) =
          (l : L ⧸ Subgroup.center L) := hfix
      rw [ggBeta_eq, ggLAut_apply]
      exact congrArg θ hfix'
  · intro h
    refine ⟨θ.symm y, ?_, θ.apply_symm_apply y⟩
    apply Subgroup.mem_iInf.mpr
    intro d
    change (onQuotient (Subgroup.center L) (QTwoCentralizer.action L D hDL d)
      (QTwoCentralizer.centerInvariant L D hDL d)) (θ.symm y) = θ.symm y
    apply θ.injective
    have hcompat : ∀ q : L ⧸ Subgroup.center L,
        θ (onQuotient (Subgroup.center L) (QTwoCentralizer.action L D hDL d)
          (QTwoCentralizer.centerInvariant L D hDL d) q) = ggBeta L θ hDL d (θ q) := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H l =>
        change θ (((QTwoCentralizer.action L D hDL d) l : L) : L ⧸ Subgroup.center L) =
          ggLAut L θ ⟨d, hDL d.property⟩ (θ (l : L ⧸ Subgroup.center L))
        rw [ggLAut_apply]
        rfl
    rw [hcompat, θ.apply_symm_apply]
    exact h d

@[expose] def markedComponent (J : Subgroup G) : Subgroup R :=
  (QTwoCentralizer.componentImage L D hDL J).map
    (θ.toMonoidHom.comp (QTwoCentralizer.quotientCentralizer L D hDL).subtype)

theorem markedComponent_eq_map_ggQuotHom {J : Subgroup G}
    (hJ : J ≤ L ⊓ Subgroup.centralizer (D : Set G)) :
    markedComponent hDL θ J = (J.subgroupOf L).map (ggQuotHom θ) := by
  let H : Subgroup L := QTwoCentralizer.centralizerPreimage L D hDL
  have hPH : J.subgroupOf L ≤ H := by
    intro j hj
    exact QTwoCentralizer.centralizer_le_preimage L D hDL (hJ hj).2
  have hproj :
      (θ.toMonoidHom.comp (QTwoCentralizer.quotientCentralizer L D hDL).subtype).comp
        (QTwoCentralizer.projection L D hDL) = (ggQuotHom θ).comp H.subtype := by
    ext j
    rfl
  unfold markedComponent QTwoCentralizer.componentImage
  rw [Subgroup.map_map, hproj, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hPH]

theorem isComponentOf_markedComponent {J : Subgroup G}
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf (markedComponent hDL θ J) (⨅ d : D, ggFix (ggBeta L θ hDL d)) := by
  let f : QTwoCentralizer.quotientCentralizer L D hDL →* R :=
    θ.toMonoidHom.comp (QTwoCentralizer.quotientCentralizer L D hDL).subtype
  have hf : Function.Injective f := θ.injective.comp Subtype.val_injective
  have hcomp := isComponentOf_map_of_injective f hf
    (QTwoCentralizer.isComponentOf_componentImage L D hDL hJ)
  have htop : (⊤ : Subgroup (QTwoCentralizer.quotientCentralizer L D hDL)).map f =
      (QTwoCentralizer.quotientCentralizer L D hDL).map θ.toMonoidHom := by
    rw [Subgroup.map_top, MonoidHom.range_comp, Subgroup.range_subtype]
  rwa [htop, quotientCentralizer_map hDL θ] at hcomp

theorem isComponentOf_quotient_image {J : Subgroup G}
    (hJ : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G))) :
    IsComponentOf ((J.subgroupOf L).map (ggQuotHom θ))
      (⨅ d : D, ggFix (ggBeta L θ hDL d)) := by
  rw [← markedComponent_eq_map_ggQuotHom hDL θ hJ.1]
  exact isComponentOf_markedComponent hDL θ hJ

end CFSG.StandardType.QTwoCav

namespace CFSG.StandardType.QTwoCav

open CFSG.LocalAnalysis.GorensteinLyons

variable {G : Type} [Group G] {L Bs J : Subgroup G}
  {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)

theorem markingAutHom_injective (hL : commutator L = ⊤) :
    Function.Injective (gl2MarkingAutHom θ) := by
  intro a b hab
  apply TypeA.mulAut_eq_of_forall (ggQuotHom θ) (ker_ggQuotHom θ).le hL
  intro l
  have h := congrArg (fun φ : MulAut R => φ (ggQuotHom θ l)) hab
  simpa only [gl2MarkingAutHom_apply, ggQuotHom_apply, gl2MarkingAut_apply_mk] using h

theorem markingAutHom_comp_gamma (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (gl2MarkingAutHom θ).comp (ggGamma L hN) = ggBeta L θ hN := by
  ext b r
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective θ r
  rw [MonoidHom.comp_apply, gl2MarkingAutHom_apply, ggQuotHom_apply,
    gl2MarkingAut_apply_mk]
  exact (ggBeta_ggQuotHom L hN θ b l).symm

theorem beta_trans {R' : Type} [Group R'] (e : R ≃* R')
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    (MulAut.congr e).toMonoidHom.comp (ggBeta L θ hN) =
      ggBeta L (θ.trans e) hN := by
  ext b r
  obtain ⟨l, rfl⟩ := ggQuotHom_surjective (θ.trans e) r
  change MulAut.congr e (ggBeta L θ hN b) (e (ggQuotHom θ l)) =
    ggBeta L (θ.trans e) hN b (ggQuotHom (θ.trans e) l)
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, e.symm_apply_apply]
  rw [ggBeta_ggQuotHom, ggBeta_ggQuotHom]
  rfl

theorem markingAutHom_map_inner_j :
    ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L)).map (gl2MarkingAutHom θ) =
      ((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro j
  exact gl2MarkingAut_conj θ j

theorem card_automizer_quotient_image_eq (hL : commutator L = ⊤)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggAutomizer
      (((J.subgroupOf L).map (ggQuotHom θ)).map (MulAut.conj : R →* MulAut R))
      (ggBeta L θ hN).range) =
        Nat.card (ggAutomizer
          ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
          (ggGamma L hN).range) := by
  have hmap : (ggGamma L hN).range.map (gl2MarkingAutHom θ) =
      (ggBeta L θ hN).range := by
    rw [← MonoidHom.range_comp, markingAutHom_comp_gamma θ hN]
  rw [← markingAutHom_map_inner_j θ]
  rw [F4AutWeyl.ggAutomizer_map_eq (markingAutHom_injective θ hL) _ _ hmap,
    Subgroup.card_map_of_injective (MulAut.congr _).injective]

variable [Finite G] {p : ℕ} {B D : Subgroup G} {x : G}

theorem beta_d_card (hp : p.Prime) (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card (ggBeta L θ (d_le_normalizer hS hN)).range = p := by
  have hmap : (ggGamma L (d_le_normalizer hS hN)).range.map (gl2MarkingAutHom θ) =
      (ggBeta L θ (d_le_normalizer hS hN)).range := by
    rw [← MonoidHom.range_comp, markingAutHom_comp_gamma θ]
  rw [← hmap, Subgroup.card_map_of_injective (markingAutHom_injective θ hS.2.1.1)]
  exact gamma_d_card hp hS hN

theorem exists_beta_d_generator (hp : p.Prime) (hS : GGQTwoSetting p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ d : D, ggBeta L θ (d_le_normalizer hS hN) d ≠ 1 ∧
      Subgroup.zpowers (ggBeta L θ (d_le_normalizer hS hN) d) =
        (ggBeta L θ (d_le_normalizer hS hN)).range ∧
      (⨅ e : D, ggFix (ggBeta L θ (d_le_normalizer hS hN) e)) =
        ggFix (ggBeta L θ (d_le_normalizer hS hN) d) := by
  letI : Fact p.Prime := ⟨hp⟩
  let f := ggBeta L θ (d_le_normalizer hS hN)
  have hcard : Nat.card f.range = p := beta_d_card θ hp hS hN
  letI : Finite f.range := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := f.range) p
    (by rw [hcard])
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha
    exact hp.ne_one ha.symm
  obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp a.property
  have hgen : Subgroup.zpowers (f d) = f.range := by
    have h := congrArg (fun A : Subgroup f.range => A.map f.range.subtype)
      (zpowers_eq_top_of_prime_card hcard ha1)
    rw [MonoidHom.map_zpowers, Subgroup.map_top, Subgroup.range_subtype] at h
    change Subgroup.zpowers (a : MulAut R) = f.range at h
    exact hd ▸ h
  have hd1 : f d ≠ 1 := by
    intro h
    apply ha1
    apply Subtype.ext
    exact hd.symm.trans h
  refine ⟨d, hd1, hgen, le_antisymm ?_ ?_⟩
  · exact iInf_le (fun e : D => ggFix (f e)) d
  · intro r hr
    apply Subgroup.mem_iInf.mpr
    intro e
    have hstab : f.range ≤ MulAction.stabilizer (MulAut R) r := by
      rw [← hgen]
      apply Subgroup.zpowers_le.mpr
      change f d r = r
      exact hr
    exact hstab ⟨e, rfl⟩

end CFSG.StandardType.QTwoCav

end
