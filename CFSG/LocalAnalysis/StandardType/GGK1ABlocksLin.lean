module

public import CFSG.LocalAnalysis.StandardType.GGK1ADefs
public import CFSG.RankThree.SteinbergR3ECALinearPrimaryBlocks
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LocalAnalysis.StandardType.GGK1CBlFF
public import CFSG.LocalAnalysis.StandardType.GGK1CBlIdx
public import CFSG.Assembly.Subnormal
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCUnitary
open CFSG.RankThree.CALinearPrimary
open CFSG.ComponentClassification

private noncomputable def ggK1Abl_x {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    LinearMap.GeneralLinearGroup K (Fin N → K) :=
  Matrix.GeneralLinearGroup.toLin xhat.1

private theorem ggK1Abl_x_coe {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) = ggK1A_glEnd xhat.1 := rfl

private theorem ggK1Abl_det {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    LinearMap.det ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) = 1 := by
  have hdet : ((xhat.1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K).det = 1 := by
    have h : (Matrix.GeneralLinearGroup.det xhat.1 : Kˣ) = 1 := xhat.2
    have h2 := congrArg Units.val h
    simpa using h2
  change LinearMap.det (Matrix.toLin' ((xhat.1 : GL (Fin N) K) : Matrix (Fin N) (Fin N) K)) = 1
  rw [LinearMap.det_toLin', hdet]

private noncomputable def ggK1Abl_slEquivG (N : ℕ) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin N) K ≃* ↥(LargeEvenSLGroup (Fin N) K) :=
  (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL N K).trans
    (MulEquiv.subgroupCongr (by
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]; rfl))

private theorem ggK1Abl_slEquivG_apply {N : ℕ} {K : Type} [Field K]
    (a : Matrix.SpecialLinearGroup (Fin N) K) :
    ((ggK1Abl_slEquivG N K a : ↥(LargeEvenSLGroup (Fin N) K)) : GL (Fin N) K) =
      Matrix.SpecialLinearGroup.toGL a := by
  rw [ggK1Abl_slEquivG, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
  rfl

private noncomputable def ggK1Abl_iota (N : ℕ) (K : Type) [Field K] :
    ↥(LargeEvenSLGroup (Fin N) K) →* LinearMap.GeneralLinearGroup K (Fin N → K) :=
  (Matrix.GeneralLinearGroup.toLin :
    GL (Fin N) K ≃* LinearMap.GeneralLinearGroup K (Fin N → K)).toMonoidHom.comp
      (LargeEvenSLGroup (Fin N) K).subtype

private theorem ggK1Abl_iota_x {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    ggK1Abl_iota N K xhat = ggK1Abl_x xhat := rfl

private theorem ggK1Abl_iota_slEquivG (N : ℕ) (K : Type) [Field K] :
    (ggK1Abl_iota N K).comp (ggK1Abl_slEquivG N K).toMonoidHom = slGL N K := by
  apply MonoidHom.ext
  intro a
  change Matrix.GeneralLinearGroup.toLin
    (((ggK1Abl_slEquivG N K) a : ↥(LargeEvenSLGroup (Fin N) K)) : GL (Fin N) K) =
      slGL N K a
  rw [ggK1Abl_slEquivG_apply]
  rfl

private theorem ggK1Abl_iota_slEquivG_apply {N : ℕ} {K : Type} [Field K]
    (a : Matrix.SpecialLinearGroup (Fin N) K) :
    ggK1Abl_iota N K (ggK1Abl_slEquivG N K a) = slGL N K a := by
  have h := DFunLike.congr_fun (ggK1Abl_iota_slEquivG N K) a
  simpa using h

private theorem ggK1Abl_iota_injective (N : ℕ) (K : Type) [Field K] :
    Function.Injective (ggK1Abl_iota N K) :=
  Matrix.GeneralLinearGroup.toLin.injective.comp Subtype.val_injective

private noncomputable def ggK1Abl_F {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (h : K[X]) :
    Subgroup (Matrix.SpecialLinearGroup (Fin N) K) :=
  (linearSpecialBlock (ggK1Abl_x xhat) h).comap (slGL N K)

private noncomputable def ggK1Abl_A {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (h : K[X]) :
    Subgroup ↥(LargeEvenSLGroup (Fin N) K) :=
  (ggK1Abl_F xhat h).map (ggK1Abl_slEquivG N K).toMonoidHom

private noncomputable def ggK1Abl_kind {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (h : K[X]) : ggK1ACo_Kind :=
  .sl (primaryMultiplicity (ggK1A_glEnd xhat.1) h) h.natDegree

private theorem ggK1Abl_F_map_slGL {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    (ggK1Abl_F xhat h).map (slGL N K) = linearSpecialBlock (ggK1Abl_x xhat) h := by
  have hle : linearSpecialBlock (ggK1Abl_x xhat) h ≤ (slGL N K).range := fun g hg =>
    mem_range_slGL (det_eq_one_of_mem_linearSpecialBlock (x := ggK1Abl_x xhat) hsq hh hg)
  rw [ggK1Abl_F, Subgroup.map_comap_eq, inf_eq_right.mpr hle]

private theorem ggK1Abl_A_map_iota {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    (ggK1Abl_A xhat h).map (ggK1Abl_iota N K) =
      linearSpecialBlock (ggK1Abl_x xhat) h := by
  rw [ggK1Abl_A, Subgroup.map_map, ggK1Abl_iota_slEquivG, ggK1Abl_F_map_slGL xhat hsq hh]

private theorem ggK1Abl_A_le_centralizer {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (h : K[X]) :
    ggK1Abl_A xhat h ≤ Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSLGroup (Fin N) K)) := by
  intro g hg
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hsC : slGL N K s ∈ gl_centralizer (ggK1Abl_x xhat) :=
    linearSpecialBlock_le_centralizer _ _ hs
  have hcommU : (slGL N K s) * (ggK1Abl_x xhat) = (ggK1Abl_x xhat) * (slGL N K s) :=
    (Subgroup.mem_centralizer_singleton_iff).mp hsC
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.toLin.injective
  change ggK1Abl_iota N K (ggK1Abl_slEquivG N K s * xhat) =
    ggK1Abl_iota N K (xhat * ggK1Abl_slEquivG N K s)
  rw [map_mul, map_mul, ggK1Abl_iota_slEquivG_apply, ggK1Abl_iota_x]
  exact hcommU

private theorem ggK1Abl_linearSpecialBlock_commute {N : ℕ} {K : Type} [Field K]
    {x : LinearMap.GeneralLinearGroup K (Fin N → K)}
    (hsq : Squarefree (minpoly K ((x : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    {h h' : K[X]} (hh : h ∈ primaryFactors ((x : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)))
    (hh' : h' ∈ primaryFactors ((x : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) (hne : h ≠ h') :
    ∀ a ∈ linearSpecialBlock x h, ∀ b ∈ linearSpecialBlock x h', Commute a b := by
  intro a ha b hb
  have haC : a ∈ gl_centralizer x := linearSpecialBlock_le_centralizer x h ha
  have hbC : b ∈ gl_centralizer x := linearSpecialBlock_le_centralizer x h' hb
  have hat := (mem_linearSpecialBlock.mp ha).2.1
  have hbt := (mem_linearSpecialBlock.mp hb).2.1
  rw [Commute]
  apply Units.ext
  apply ext_primaryComponent hsq
  intro c hc v hv
  change (a : Module.End K (Fin N → K)) ((b : Module.End K (Fin N → K)) v) =
    (b : Module.End K (Fin N → K)) ((a : Module.End K (Fin N → K)) v)
  by_cases hch : c = h
  · have hnh' : c ≠ h' := fun e => hne (hch.symm.trans e)
    rw [hbt c hc hnh' v hv,
      hbt c hc hnh' ((a : Module.End K (Fin N → K)) v)
        (apply_mem_primaryComponent (mem_gl_centralizer.mp haC) hv)]
  · by_cases hch' : c = h'
    · have hnh : c ≠ h := fun e => hne (e.symm.trans hch')
      rw [hat c hc hnh v hv,
        hat c hc hnh ((b : Module.End K (Fin N → K)) v)
          (apply_mem_primaryComponent (mem_gl_centralizer.mp hbC) hv)]
    · rw [hat c hc hch v hv, hbt c hc hch' v hv, hat c hc hch v hv]

private theorem ggK1Abl_comm {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h h' : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)))
    (hh' : h' ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) (hne : h ≠ h') :
    ∀ a ∈ ggK1Abl_A xhat h, ∀ b ∈ ggK1Abl_A xhat h', Commute a b := by
  intro a ha b hb
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hb
  have hs' : slGL N K s ∈ linearSpecialBlock (ggK1Abl_x xhat) h := hs
  have ht' : slGL N K t ∈ linearSpecialBlock (ggK1Abl_x xhat) h' := ht
  have hcommL := ggK1Abl_linearSpecialBlock_commute (x := ggK1Abl_x xhat) hsq hh hh' hne
    (slGL N K s) hs' (slGL N K t) ht'
  have hcommSL : Commute s t := by
    rw [Commute] at hcommL ⊢
    apply slGL_injective
    rw [map_mul, map_mul]
    exact hcommL
  exact hcommSL.map (ggK1Abl_slEquivG N K).toMonoidHom


private noncomputable def ggK1Abl_blockEquiv {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    ↥(linearSpecialBlock (ggK1Abl_x xhat) h) ≃*
      Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) h)) (AdjoinRoot h) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  let b : Module.Basis
      (Fin (primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) h)) (AdjoinRoot h)
      (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(linearSpecialBlock (ggK1Abl_x xhat) h) ≃*
      _root_.SpecialLinearGroup (AdjoinRoot h)
        (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) h) :=
    MulEquiv.ofBijective (linearSpecialBlockRestrict (ggK1Abl_x xhat) h)
      ⟨linearSpecialBlockRestrict_injective hsq, linearSpecialBlockRestrict_surjective hsq hh⟩
  exact e₁.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm

private theorem ggK1Abl_A_equiv_SL {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    Nonempty (↥(ggK1Abl_A xhat h) ≃*
      Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (ggK1A_glEnd xhat.1) h)) (AdjoinRoot h)) := by
  have hmap : (ggK1Abl_F xhat h).map (slGL N K) = linearSpecialBlock (ggK1Abl_x xhat) h :=
    ggK1Abl_F_map_slGL xhat hsq hh
  have e1 : ↥(ggK1Abl_A xhat h) ≃* ↥(ggK1Abl_F xhat h) :=
    (Subgroup.equivMapOfInjective (ggK1Abl_F xhat h) (ggK1Abl_slEquivG N K).toMonoidHom
      (ggK1Abl_slEquivG N K).injective).symm
  have e2 : ↥(ggK1Abl_F xhat h) ≃* ↥(linearSpecialBlock (ggK1Abl_x xhat) h) :=
    (Subgroup.equivMapOfInjective (ggK1Abl_F xhat h) (slGL N K) slGL_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have e3 := ggK1Abl_blockEquiv xhat hsq hh
  exact ⟨e1.trans (e2.trans e3)⟩

private theorem ggK1Abl_A_equiv_linSpecial {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    Nonempty (↥(ggK1Abl_A xhat h) ≃* ↥(linearSpecialBlock (ggK1Abl_x xhat) h)) := by
  have hmap : (ggK1Abl_F xhat h).map (slGL N K) = linearSpecialBlock (ggK1Abl_x xhat) h :=
    ggK1Abl_F_map_slGL xhat hsq hh
  have e1 : ↥(ggK1Abl_A xhat h) ≃* ↥(ggK1Abl_F xhat h) :=
    (Subgroup.equivMapOfInjective (ggK1Abl_F xhat h) (ggK1Abl_slEquivG N K).toMonoidHom
      (ggK1Abl_slEquivG N K).injective).symm
  have e2 : ↥(ggK1Abl_F xhat h) ≃* ↥(linearSpecialBlock (ggK1Abl_x xhat) h) :=
    (Subgroup.equivMapOfInjective (ggK1Abl_F xhat h) (slGL N K) slGL_injective).trans
      (MulEquiv.subgroupCongr hmap)
  exact ⟨e1.trans e2⟩

private theorem ggK1Abl_A_model {N nf : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) (hK : Nat.card K = 2 ^ nf) :
    ggK1ACo_Kind.Model nf K (ggK1Abl_kind xhat h) (ggK1Abl_A xhat h) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype (AdjoinRoot h) := Fintype.ofFinite (AdjoinRoot h)
  obtain ⟨e⟩ := ggK1Abl_A_equiv_SL xhat hsq hh
  refine ⟨AdjoinRoot h, inferInstance, inferInstance, ?_, ⟨?iso⟩⟩
  · rw [← Nat.card_eq_fintype_card,
      CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK]
  · exact e

private def ggK1Abl_good {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (h : K[X]) : Prop :=
  3 ≤ primaryMultiplicity (ggK1A_glEnd xhat.1) h ∨
    (2 ≤ primaryMultiplicity (ggK1A_glEnd xhat.1) h ∧ 4 ≤ Nat.card (AdjoinRoot h))

private theorem ggK1Abl_SL_solvable_of_not_good {E : Type} [Field E] [Finite E] {m : ℕ}
    (hm : 1 ≤ m) (hbad : ¬ (3 ≤ m ∨ (2 ≤ m ∧ 4 ≤ Nat.card E))) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin m) E) := by
  have hmle : m ≤ 2 := by omega
  interval_cases m
  · have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 1) E) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_one_solvable E
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 1) E →* _))
      Matrix.SpecialLinearGroup.toGL_injective
  · have hcard : Nat.card E = 2 ∨ Nat.card E = 3 := by
      have h2 : 1 < Nat.card E := Finite.one_lt_card
      omega
    have : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) E) :=
      CFSG.ComponentClassification.CatalogueBGeneralLinear.generalLinear_two_small_solvable E hcard
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Matrix.SpecialLinearGroup.toGL : Matrix.SpecialLinearGroup (Fin 2) E →* _))
      Matrix.SpecialLinearGroup.toGL_injective

private theorem ggK1Abl_not_isQuasisimple_of_isSolvable {G : Type} [Group G] {A : Subgroup G}
    (h : Group.IsSolvable ↥A) : ¬ CFSG.IsQuasisimple ↥A := by
  haveI := h
  intro hq
  haveI : Group.IsPerfect ↥A := hq.1
  haveI : Nontrivial ↥A := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact Group.IsPerfect.not_isSolvable ↥A inferInstance

private theorem ggK1Abl_linearSpecialBlock_isQuasisimple_iff {N : ℕ} {K : Type} [Field K]
    [Finite K] (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    CFSG.IsQuasisimple ↥(linearSpecialBlock (ggK1Abl_x xhat) h) ↔ ggK1Abl_good xhat h := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  constructor
  · intro hq
    by_contra hbad
    have hm : 1 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
        (Fin N → K)) : Module.End K (Fin N → K)) h := by
      haveI : Nontrivial (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
          (Fin N → K)) : Module.End K (Fin N → K)) h) :=
        Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
      exact Module.finrank_pos
    have hbad' : ¬ (3 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
        (Fin N → K)) : Module.End K (Fin N → K)) h ∨
        (2 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) h ∧ 4 ≤ Nat.card (AdjoinRoot h))) := hbad
    have hsolvSL := ggK1Abl_SL_solvable_of_not_good (E := AdjoinRoot h) hm hbad'
    haveI := hsolvSL
    have hsolv : Group.IsSolvable ↥(linearSpecialBlock (ggK1Abl_x xhat) h) :=
      Group.isSolvable_of_surjective
        (f := (ggK1Abl_blockEquiv xhat hsq hh).symm.toMonoidHom)
        (by simpa using (ggK1Abl_blockEquiv xhat hsq hh).symm.surjective)
    exact ggK1Abl_not_isQuasisimple_of_isSolvable hsolv hq
  · intro hgood
    have hgood' : 3 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
        (Fin N → K)) : Module.End K (Fin N → K)) h ∨
        (2 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) h ∧ 4 ≤ Nat.card (AdjoinRoot h)) := hgood
    exact isQuasisimple_linearSpecialBlock hsq hh hgood'

private theorem ggK1Abl_A_isQuasisimple_iff {N : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    CFSG.IsQuasisimple ↥(ggK1Abl_A xhat h) ↔ ggK1Abl_good xhat h := by
  obtain ⟨e⟩ := ggK1Abl_A_equiv_linSpecial xhat hsq hh
  constructor
  · intro hq
    exact (ggK1Abl_linearSpecialBlock_isQuasisimple_iff xhat hsq hh).mp
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq)
  · intro hg
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      ((ggK1Abl_linearSpecialBlock_isQuasisimple_iff xhat hsq hh).mpr hg)

private theorem ggK1Abl_orbit_sl_qs {nf m e : ℕ} (hm : 1 ≤ m) (he : 1 ≤ e) (hnf : 1 ≤ nf) :
    (ggK1ACo_kindOrbit nf (.sl m e)).qs = true ↔ (3 ≤ m ∨ (m = 2 ∧ 2 ≤ e * nf)) := by
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · subst hm1
    simp [ggK1ACo_kindOrbit]
  · have horb : ggK1ACo_kindOrbit nf (.sl m e) = ggMultBlockA (m - 1) (e * nf) 1 := by
      cases m with
      | zero => omega
      | succ m' => cases m' with
        | zero => omega
        | succ m' => rfl
    rw [horb, ggMultBlockA, if_pos rfl, decide_eq_true_eq]
    have hep : 1 ≤ e * nf := by
      have := Nat.mul_pos (by omega : 0 < e) (by omega : 0 < nf)
      omega
    omega

private theorem ggK1Abl_four_le_card_adjoinRoot_iff {nf e : ℕ} {K : Type} [Field K] [Finite K]
    {h : K[X]} [Fact (Irreducible h)] (he : 1 ≤ e) (hnf : 1 ≤ nf)
    (hK : Nat.card K = 2 ^ nf) (hdeg : h.natDegree = e) :
    4 ≤ Nat.card (AdjoinRoot h) ↔ 2 ≤ e * nf := by
  rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK, hdeg]
  rw [← pow_mul, Nat.mul_comm nf e]
  constructor
  · intro h4
    by_contra hlt
    push Not at hlt
    have hle : e * nf ≤ 1 := by omega
    have h2 : 2 ^ (e * nf) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    rw [pow_one] at h2
    omega
  · intro h2
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (e * nf) := Nat.pow_le_pow_right (by norm_num) h2

private theorem ggK1Abl_good_iff_orbit_qs {N nf : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1)))
    (hh : h ∈ primaryFactors (ggK1A_glEnd xhat.1)) :
    ggK1Abl_good xhat h ↔ (ggK1ACo_kindOrbit nf (ggK1Abl_kind xhat h)).qs = true := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm : 1 ≤ primaryMultiplicity (ggK1A_glEnd xhat.1) h := by
    haveI : Nontrivial (primaryComponent (ggK1A_glEnd xhat.1) h) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
    exact Module.finrank_pos
  have he : 1 ≤ h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  unfold ggK1Abl_kind
  rw [ggK1Abl_orbit_sl_qs hm he hnf]
  unfold ggK1Abl_good
  rw [ggK1Abl_four_le_card_adjoinRoot_iff (e := h.natDegree) he hnf hK rfl]
  constructor
  · rintro (h3 | ⟨h2, hge⟩)
    · exact Or.inl h3
    · rcases eq_or_lt_of_le h2 with h2' | h2'
      · exact Or.inr ⟨h2'.symm, hge⟩
      · exact Or.inl (by omega)
  · rintro (h3 | ⟨h2, hge⟩)
    · exact Or.inl h3
    · exact Or.inr ⟨by omega, hge⟩

private theorem ggK1Abl_ringChar_two {nf : ℕ} {K : Type} [Field K] [Finite K]
    (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf) : ringChar K = 2 := by
  haveI : Fintype K := Fintype.ofFinite K
  rw [FiniteField.even_card_iff_char_two]
  rw [← Nat.card_eq_fintype_card, hK]
  exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega : nf ≠ 0))

private theorem ggK1Abl_hsq {p N nf : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) :
    Squarefree (minpoly K (ggK1A_glEnd xhat.1)) := by
  have hchar : ringChar K = 2 := ggK1Abl_ringChar_two hnf hK
  have hpk : (p : K) ≠ 0 := by
    intro h0
    have hpdiv : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
    have hprime := CharP.prime_ringChar (R := K)
    have hring : ringChar K = p := (Nat.prime_dvd_prime_iff_eq hprime hp).mp hpdiv
    exact hp2 (hchar ▸ hring).symm
  have hval : xhat.1 ^ p = 1 := by
    have := congrArg Subtype.val hxp
    simpa using this
  refine squarefree_minpoly_of_aeval_eq_zero (p := X ^ p - C 1)
    (Polynomial.separable_X_pow_sub_C (1 : K) hpk one_ne_zero).squarefree ?_
  have hx : (ggK1A_glEnd xhat.1) ^ p = 1 := by
    rw [show ggK1A_glEnd xhat.1 =
      Matrix.toLin' (xhat.1 : Matrix (Fin N) (Fin N) K) from rfl,
      ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hval]
    exact Matrix.toLin'_one
  rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hx, sub_self]

private theorem ggK1Abl_fixSub_conj_eq_centralizer {X : Type*} [Group X] (x : X) :
    ggFixSub (MulAut.conj x) = Subgroup.centralizer ({x} : Set X) := by
  ext g
  rw [mem_ggFixSub, MulAut.conj_apply, mul_inv_eq_iff_eq_mul,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

private theorem ggK1Abl_conj_mem_A {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)))
    {c : ↥(LargeEvenSLGroup (Fin N) K)}
    (hc : c ∈ Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSLGroup (Fin N) K)))
    {g : ↥(LargeEvenSLGroup (Fin N) K)} (hg : g ∈ ggK1Abl_A xhat h) :
    c * g * c⁻¹ ∈ ggK1Abl_A xhat h := by
  have hcx : c * xhat = xhat * c := (Subgroup.mem_centralizer_singleton_iff).mp hc
  have hcomm : ggK1Abl_iota N K c * ggK1Abl_x xhat =
      ggK1Abl_x xhat * ggK1Abl_iota N K c := by
    have h := congrArg (ggK1Abl_iota N K) hcx
    simpa only [map_mul, ggK1Abl_iota_x] using h
  have hcC : ggK1Abl_iota N K c ∈ gl_centralizer (ggK1Abl_x xhat) :=
    (Subgroup.mem_centralizer_singleton_iff).mpr hcomm
  have hgL : ggK1Abl_iota N K g ∈ linearSpecialBlock (ggK1Abl_x xhat) h := by
    rw [← ggK1Abl_A_map_iota xhat hsq hh]
    exact Subgroup.mem_map_of_mem _ hg
  have hconj : ggK1Abl_iota N K c * ggK1Abl_iota N K g * (ggK1Abl_iota N K c)⁻¹ ∈
      linearSpecialBlock (ggK1Abl_x xhat) h :=
    conj_mem_linearSpecialBlock hcC hgL
  have hconj' : ggK1Abl_iota N K (c * g * c⁻¹) ∈
      (ggK1Abl_A xhat h).map (ggK1Abl_iota N K) := by
    rw [ggK1Abl_A_map_iota xhat hsq hh]
    simpa only [map_mul, map_inv] using hconj
  obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hconj'
  rwa [ggK1Abl_iota_injective N K hyeq] at hy

private theorem ggK1Abl_A_component {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (hh : h ∈ primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)))
    (hq : CFSG.IsQuasisimple ↥(ggK1Abl_A xhat h)) :
    CFSG.Assembly.IsComponentOf (ggK1Abl_A xhat h) (ggFixSub (MulAut.conj xhat)) := by
  have hle : ggK1Abl_A xhat h ≤ Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSLGroup (Fin N) K)) :=
    ggK1Abl_A_le_centralizer xhat h
  have hq' : CFSG.Assembly.IsQuasisimple ↥(ggK1Abl_A xhat h) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
  refine ⟨?_, ?_, hq'⟩
  · rw [ggK1Abl_fixSub_conj_eq_centralizer]; exact hle
  · rw [ggK1Abl_fixSub_conj_eq_centralizer]
    refine CFSG.Assembly.IsSubnormal.step hle ?_ (CFSG.Assembly.IsSubnormal.refl _)
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ggK1Abl_conj_mem_A xhat hsq hh g.2 hn

private theorem ggK1Abl_hasOrbit_sl_iff (m e : ℕ) :
    (ggK1ACo_Kind.hasOrbit (.sl m e)) = true ↔ m ≠ 1 := by
  cases m with
  | zero => simp [ggK1ACo_Kind.hasOrbit]
  | succ m =>
    cases m with
    | zero => simp [ggK1ACo_Kind.hasOrbit]
    | succ m => simp [ggK1ACo_Kind.hasOrbit]

private theorem ggK1Abl_hsolv {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) {h : K[X]}
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1)))
    (hh : h ∈ primaryFactors (ggK1A_glEnd xhat.1)) :
    (ggK1ACo_Kind.hasOrbit (ggK1Abl_kind xhat h)) = true →
    (ggK1ACo_kindOrbit nf (ggK1Abl_kind xhat h)).qs = false →
    ∃ t ∈ ggK1Abl_A xhat h, t ^ p = 1 ∧
      ∃ a ∈ ggK1Abl_A xhat h, a * t ≠ t * a := by
  intro hhas hqs
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm1 : 1 ≤ primaryMultiplicity (ggK1A_glEnd xhat.1) h := by
    haveI : Nontrivial (primaryComponent (ggK1A_glEnd xhat.1) h) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hh)
    exact Module.finrank_pos
  have hmne : primaryMultiplicity (ggK1A_glEnd xhat.1) h ≠ 1 :=
    (ggK1Abl_hasOrbit_sl_iff _ _).mp (by simpa only [ggK1Abl_kind] using hhas)
  have hm2 : 2 ≤ primaryMultiplicity (ggK1A_glEnd xhat.1) h := by omega
  have hnotgood : ¬ ggK1Abl_good xhat h := by
    intro hg
    have := (ggK1Abl_good_iff_orbit_qs hnf hK xhat hsq hh).mp hg
    rw [this] at hqs
    exact Bool.noConfusion hqs
  have hm2eq : primaryMultiplicity (ggK1A_glEnd xhat.1) h = 2 := by
    unfold ggK1Abl_good at hnotgood
    omega
  have hcard_le : Nat.card (AdjoinRoot h) ≤ 3 := by
    unfold ggK1Abl_good at hnotgood
    omega
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have he1 : h.natDegree = 1 := by
    by_contra hne
    have he2 : 2 ≤ h.natDegree := by
      have := (Fact.out : Irreducible h).natDegree_pos
      omega
    have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK]
      have hbase : 2 ≤ 2 ^ nf := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) hnf
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ (2 ^ nf) ^ 2 := Nat.pow_le_pow_left hbase 2
        _ ≤ (2 ^ nf) ^ h.natDegree := Nat.pow_le_pow_right (by positivity) he2
    omega
  have hnf1 : nf = 1 := by
    by_contra hne
    have h2n : 2 ≤ nf := by omega
    have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
      rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK, he1, pow_one]
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ nf := Nat.pow_le_pow_right (by norm_num) h2n
    omega
  have hcard_eq : Nat.card (AdjoinRoot h) = 2 := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hK, he1, hnf1]
    norm_num
  have hp3 : p = 3 := by
    rcases hdvd with hd | hd
    · rw [hnf1] at hd
      exact absurd (Nat.dvd_one.mp (by simpa using hd)) hp.ne_one
    · rw [hnf1] at hd
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (by simpa using hd)
  let E := AdjoinRoot h
  haveI : Fintype E := Fintype.ofFinite E
  have hEcard : Fintype.card E = 2 := by
    rw [← Nat.card_eq_fintype_card, hcard_eq]
  haveI : CharP E 2 :=
    charP_of_card_eq_prime_pow (R := E) (p := 2) (f := 1) (by simpa using hEcard)
  have hdet_t : (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) E).det = 1 := by
    rw [Matrix.det_fin_two]
    show (0 : E) * 1 - 1 * 1 = 1
    rw [zero_mul, one_mul, zero_sub, CharTwo.neg_eq]
  have hdet_a : (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) E).det = 1 := by
    rw [Matrix.det_fin_two]
    show (0 : E) * 0 - 1 * 1 = 1
    rw [zero_mul, one_mul, zero_sub, CharTwo.neg_eq]
  let t : Matrix.SpecialLinearGroup (Fin 2) E := ⟨!![0,1;1,1], hdet_t⟩
  let a : Matrix.SpecialLinearGroup (Fin 2) E := ⟨!![0,1;1,0], hdet_a⟩
  have ht3 : t ^ 3 = 1 := by
    apply Subtype.ext
    change (t : Matrix (Fin 2) (Fin 2) E) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [t, Matrix.mul_apply, Fin.sum_univ_two, pow_succ, Matrix.one_apply,
        CharTwo.add_self_eq_zero]
  have hat_ne : a * t ≠ t * a := by
    intro hcon
    have h01 := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) E =>
      ((x : Matrix (Fin 2) (Fin 2) E) 0 1)) hcon
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at h01
    change (((a : Matrix (Fin 2) (Fin 2) E) * (t : Matrix (Fin 2) (Fin 2) E)) 0 1) =
      (((t : Matrix (Fin 2) (Fin 2) E) * (a : Matrix (Fin 2) (Fin 2) E)) 0 1) at h01
    simp [a, t, Matrix.mul_apply, Fin.sum_univ_two] at h01
  obtain ⟨e⟩ := ggK1Abl_A_equiv_SL xhat hsq hh
  rw [hm2eq] at e
  refine ⟨e.symm t, (e.symm t).2, ?_, e.symm a, (e.symm a).2, ?_⟩
  · rw [← Subgroup.coe_pow, hp3, ← map_pow, ht3, map_one]
    rfl
  · intro hcon
    apply hat_ne
    have hcon' : (e.symm a : ↥(ggK1Abl_A xhat h)) * (e.symm t) =
        (e.symm t) * (e.symm a) := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul] using hcon
    have h2 := congrArg e hcon'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

private theorem ggK1Abl_aeval_X_pow_sub_one {p N : ℕ} {K : Type} [Field K]
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) :
    aeval (ggK1A_glEnd xhat.1) (X ^ p - C (1 : K)) = 0 := by
  have hval : xhat.1 ^ p = 1 := by
    have := congrArg Subtype.val hxp
    simpa using this
  have hx : (ggK1A_glEnd xhat.1) ^ p = 1 := by
    rw [show ggK1A_glEnd xhat.1 =
      Matrix.toLin' (xhat.1 : Matrix (Fin N) (Fin N) K) from rfl,
      ← Matrix.toLin'_pow, ← Units.val_pow_eq_pow_val, hval]
    exact Matrix.toLin'_one
  rw [map_sub, map_pow, aeval_X, aeval_C, map_one, hx, sub_self]

private theorem ggK1Abl_orderOf_eq_ggMultOrd {p nf : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) :
    orderOf (((2 ^ nf : ℕ) : ZMod p)) = ggMultOrd p nf := by
  unfold ggMultOrd
  by_cases h1 : p ∣ 2 ^ nf - 1
  · rw [if_pos h1]
    have h0 : ((2 ^ nf - 1 : ℕ) : ZMod p) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ nf - 1)).mpr h1
    have hcast : ((2 ^ nf : ℕ) : ZMod p) = 1 := by
      have h1le : 1 ≤ 2 ^ nf := Nat.one_le_two_pow
      rw [Nat.cast_sub h1le, Nat.cast_one, sub_eq_zero] at h0
      exact h0
    exact orderOf_eq_one_iff.mpr hcast
  · rw [if_neg h1]
    rcases hdvd with h | h
    · exact absurd h h1
    · rw [if_pos h]
      have h0 : ((2 ^ nf + 1 : ℕ) : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p (2 ^ nf + 1)).mpr h
      have hcast : ((2 ^ nf : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_add, Nat.cast_one] at h0
        exact eq_neg_of_add_eq_zero_left h0
      haveI : Fact (1 < p) := ⟨hp.one_lt⟩
      haveI : Nontrivial (ZMod p) := ZMod.nontrivial p
      rw [hcast, orderOf_neg_one]
      have hchar : ringChar (ZMod p) = p := ZMod.ringChar_zmod_n p
      rw [hchar, if_neg hp2]

private theorem ggK1Abl_natDegree_eq_ggMultOrd {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (hxp : xhat ^ p = 1)
    {h : K[X]} (hh : h ∈ primaryFactors (ggK1A_glEnd xhat.1)) (hne : h ≠ X - 1) :
    h.natDegree = ggMultOrd p nf := by
  haveI : Fintype K := Fintype.ofFinite K
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hdvdh : h ∣ X ^ p - 1 := by
    refine (mem_primaryFactors.mp hh).2.2.trans ?_
    exact minpoly.dvd K _ (ggK1Abl_aeval_X_pow_sub_one hxp)
  have hpchar : p ≠ ringChar K := by rw [ggK1Abl_ringChar_two hnf hK]; exact hp2
  have hdeg := ggK1CBl_ff_degree hp hpchar hirr hmon hdvdh hne
  rw [hdeg]
  have hcard : Fintype.card K = 2 ^ nf := by rw [← Nat.card_eq_fintype_card, hK]
  rw [hcard]
  exact ggK1Abl_orderOf_eq_ggMultOrd hp hp2 hdvd

private theorem ggK1Abl_primaryMultiplicity_X_sub_C {K V : Type} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (x : Module.End K V) (μ : K) :
    primaryMultiplicity x (X - C μ) = Module.finrank K (primaryComponent x (X - C μ)) := by
  haveI : Fact (Irreducible (X - C μ : K[X])) := ⟨irreducible_X_sub_C μ⟩
  have h := finrank_primaryComponent x (X - C μ)
  rw [natDegree_X_sub_C, one_mul] at h
  exact h.symm

private theorem ggK1Abl_X_sub_one_not_mem_mult {N : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K))
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1)))
    (hmem : (X - 1) ∉ primaryFactors (ggK1A_glEnd xhat.1)) :
    primaryMultiplicity (ggK1A_glEnd xhat.1) (X - 1) = 0 := by
  haveI : Fact (Irreducible (X - 1 : K[X])) :=
    ⟨show Irreducible (X - 1 : K[X]) from irreducible_X_sub_C (1 : K)⟩
  have hcop : IsCoprime (X - 1 : K[X]) (minpoly K (ggK1A_glEnd xhat.1)) := by
    rw [← prod_primaryFactors hsq]
    refine IsCoprime.prod_right fun h hh => ?_
    change IsCoprime (X - C (1 : K)) h
    rw [Irreducible.coprime_iff_not_dvd (irreducible_X_sub_C (1 : K))]
    intro hdvd
    have hne : h ≠ X - 1 := fun he => hmem (he ▸ hh)
    exact hne (eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_X_sub_C 1)
      (((irreducible_X_sub_C (1 : K)).associated_of_dvd
        (irreducible_of_mem_primaryFactors hh) hdvd).symm))
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : aeval (ggK1A_glEnd xhat.1) u * aeval (ggK1A_glEnd xhat.1) (X - 1 : K[X]) = 1 := by
    have := congrArg (aeval (ggK1A_glEnd xhat.1)) huv
    rw [map_add, map_mul, map_mul, minpoly.aeval, mul_zero, add_zero] at this
    simpa only [map_one] using this
  have hinj : Function.Injective (aeval (ggK1A_glEnd xhat.1) (X - 1 : K[X])) := by
    intro a b hab
    have h2 : a - b = 0 := by
      have h3 : aeval (ggK1A_glEnd xhat.1) u
          (aeval (ggK1A_glEnd xhat.1) (X - 1 : K[X]) (a - b)) = a - b := by
        rw [← Module.End.mul_apply, h1, Module.End.one_apply]
      rw [map_sub, hab, sub_self, map_zero] at h3
      exact h3.symm
    exact sub_eq_zero.mp h2
  have hker : primaryComponent (ggK1A_glEnd xhat.1) (X - 1) = ⊥ := by
    change LinearMap.ker (aeval (ggK1A_glEnd xhat.1) (X - 1 : K[X])) = ⊥
    rw [LinearMap.ker_eq_bot]
    exact hinj
  haveI : Subsingleton ↥(primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) :=
    ⟨fun a b => Subtype.ext (by
      have ha : (a : Fin N → K) = 0 := by
        simpa using (show (a : Fin N → K) ∈ (⊥ : Submodule K (Fin N → K)) from hker ▸ a.2)
      have hb : (b : Fin N → K) = 0 := by
        simpa using (show (b : Fin N → K) ∈ (⊥ : Submodule K (Fin N → K)) from hker ▸ b.2)
      rw [ha, hb])⟩
  exact Module.finrank_zero_of_subsingleton

private theorem ggK1Abl_X_sub_one_mem_iff {N : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K))
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1))) :
    (X - 1 : K[X]) ∈ primaryFactors (ggK1A_glEnd xhat.1) ↔
      0 < primaryMultiplicity (ggK1A_glEnd xhat.1) (X - 1) := by
  haveI : Fact (Irreducible (X - 1 : K[X])) :=
    ⟨show Irreducible (X - 1 : K[X]) from irreducible_X_sub_C (1 : K)⟩
  constructor
  · intro hmem
    haveI : Nontrivial (primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) :=
      Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq hmem)
    exact Module.finrank_pos
  · intro hpos
    by_contra hmem
    have := ggK1Abl_X_sub_one_not_mem_mult xhat hsq hmem
    omega

private theorem ggK1Abl_filter_cons (m : List ℕ) :
    Multiset.ofList (m.filter (fun x => decide (x ≠ 0))) =
      (if m.getD 0 0 ≠ 0 then ({m.getD 0 0} : Multiset ℕ) else 0) +
        Multiset.ofList (m.tail.filter (fun x => decide (x ≠ 0))) := by
  cases m with
  | nil => simp
  | cons a t =>
    rw [List.filter_cons]
    by_cases ha : a = 0
    · simp [ha, List.getD]
    · simp [ha, List.getD]

private theorem ggK1Abl_expected_trivial {p nf : ℕ} {m : List ℕ} (hd : ggMultOrd p nf = 1)
    (hlen : m.length = p) :
    ggK1ACo_expectedKinds p nf false m =
      Multiset.ofList ((m.filter (fun x => decide (x ≠ 0))).map
        (fun x => ggK1ACo_Kind.sl x 1)) := by
  have hlist : ((List.range p).filter (fun j => decide (0 < m.getD j 0))).map
      (fun j => ggK1ACo_Kind.sl (m.getD j 0) 1) =
      (m.filter (fun x => decide (x ≠ 0))).map (fun x => ggK1ACo_Kind.sl x 1) := by
    rw [← hlen]
    rw [ggK1CBl_filter_map_getD m 0 (fun x => decide (x ≠ 0))
      (fun x => ggK1ACo_Kind.sl x 1)]
    congr 1
    apply List.filter_congr
    intro k _
    simp [Nat.pos_iff_ne_zero]
  unfold ggK1ACo_expectedKinds ggK1ACo_expectedKindList
  simp only [hd, if_true, if_false, Bool.false_eq_true, false_and, true_and, or_false]
  rw [hlist]

private noncomputable def ggK1Abl_blockDet {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K))
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (b : primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))) :
    ↥(gl_centralizer (ggK1Abl_x xhat)) →* (AdjoinRoot (b : K[X]))ˣ :=
  let e2 : LinearMap.GeneralLinearGroup (AdjoinRoot (b : K[X]))
      (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
        Module.End K (Fin N → K)) (b : K[X])) →* (AdjoinRoot (b : K[X]))ˣ :=
    { toFun := fun u => (LinearMap.GeneralLinearGroup.toLinearEquiv u).det
      map_one' := by
        show (LinearMap.GeneralLinearGroup.toLinearEquiv (1 : LinearMap.GeneralLinearGroup
          (AdjoinRoot (b : K[X])) (primaryComponent ((ggK1Abl_x xhat :
            LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
              (b : K[X])))).det = 1
        rw [show LinearMap.GeneralLinearGroup.toLinearEquiv (1 : LinearMap.GeneralLinearGroup
          (AdjoinRoot (b : K[X])) (primaryComponent ((ggK1Abl_x xhat :
            LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K))
              (b : K[X]))) = 1 from rfl]
        exact map_one _
      map_mul' := by
        intro x y
        show (LinearMap.GeneralLinearGroup.toLinearEquiv (x * y)).det =
          (LinearMap.GeneralLinearGroup.toLinearEquiv x).det *
            (LinearMap.GeneralLinearGroup.toLinearEquiv y).det
        rw [LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
        exact map_mul _ _ _ }
  e2.comp ((Pi.evalMonoidHom _ b).comp (glCentralizerEquivPi hsq).toMonoidHom)

private theorem ggK1Abl_range_slGL_normal (N : ℕ) (K : Type) [Field K] :
    ((slGL N K).range).Normal where
  conj_mem g hg c := by
    obtain ⟨a, rfl⟩ := hg
    apply mem_range_slGL
    change LinearMap.det ((c * slGL N K a * c⁻¹ :
      LinearMap.GeneralLinearGroup K (Fin N → K)) : Module.End K (Fin N → K)) = 1
    have ha : LinearMap.det (slGL N K a : Module.End K (Fin N → K)) = 1 := by
      change LinearMap.det (Matrix.toLin' (a : Matrix (Fin N) (Fin N) K)) = 1
      rw [LinearMap.det_toLin']
      exact a.2
    have hc : LinearMap.det (c : Module.End K (Fin N → K)) *
        LinearMap.det ((c⁻¹ : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K)) = 1 := by
      have h2 : LinearMap.det (((c * c⁻¹ : LinearMap.GeneralLinearGroup K (Fin N → K)) :
          Module.End K (Fin N → K))) = LinearMap.det ((1 : LinearMap.GeneralLinearGroup K
            (Fin N → K)) : Module.End K (Fin N → K)) := by
        rw [mul_inv_cancel]
      rw [Units.val_mul, map_mul, Units.val_one, map_one] at h2
      exact h2
    rw [Units.val_mul, Units.val_mul, map_mul, map_mul, ha, mul_one]
    exact hc

private theorem ggK1Abl_iota_centralizer {N : ℕ} {K : Type} [Field K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    (Subgroup.centralizer ({xhat} : Set ↥(LargeEvenSLGroup (Fin N) K))).map (ggK1Abl_iota N K) =
      gl_centralizer (ggK1Abl_x xhat) ⊓ (slGL N K).range := by
  ext y
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgx : g * xhat = xhat * g := (Subgroup.mem_centralizer_singleton_iff).mp hg
    have hcomm : ggK1Abl_iota N K g * ggK1Abl_x xhat =
        ggK1Abl_x xhat * ggK1Abl_iota N K g := by
      have h := congrArg (ggK1Abl_iota N K) hgx
      simpa only [map_mul, ggK1Abl_iota_x] using h
    refine ⟨(Subgroup.mem_centralizer_singleton_iff).mpr hcomm, ?_⟩
    exact mem_range_slGL (by
      change LinearMap.det (Matrix.toLin' ((g.1 : GL (Fin N) K) :
        Matrix (Fin N) (Fin N) K)) = 1
      rw [LinearMap.det_toLin']
      have h : (Matrix.GeneralLinearGroup.det g.1 : Kˣ) = 1 := g.2
      have h2 := congrArg Units.val h
      simpa using h2)
  · rintro ⟨hyC, hyR⟩
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hyR
    refine ⟨ggK1Abl_slEquivG N K a, ?_, ggK1Abl_iota_slEquivG_apply a⟩
    refine (Subgroup.mem_centralizer_singleton_iff).mpr ?_
    apply ggK1Abl_iota_injective N K
    rw [map_mul, map_mul, ggK1Abl_iota_slEquivG_apply, ggK1Abl_iota_x]
    exact (Subgroup.mem_centralizer_singleton_iff).mp hyC

private theorem ggK1Abl_hom_eq_one_of_perfect {G A : Type} [Group G] [Group A]
    [IsMulCommutative A] (φ : G →* A) (hperf : commutator G = ⊤) : φ = 1 := by
  have hker : commutator G ≤ φ.ker := Abelianization.commutator_subset_ker φ
  rw [hperf] at hker
  exact MonoidHom.ext fun g => MonoidHom.mem_ker.mp (hker (Subgroup.mem_top g))

private theorem ggK1Abl_primaryMultiplicity_X_sub_one {N : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) :
    primaryMultiplicity (ggK1A_glEnd xhat.1) (X - 1) =
      Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) := by
  exact ggK1Abl_primaryMultiplicity_X_sub_C (ggK1A_glEnd xhat.1) (1 : K)

private theorem ggK1Abl_range_filter_sl (m : List ℕ) (e : ℕ) :
    ((List.range (e + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).map
      (fun j => ggK1ACo_Kind.sl (m.getD j 0) 2) =
    (((List.range e).map (fun j => m.getD (j + 1) 0)).filter (fun x => decide (x ≠ 0))).map
      (fun x => ggK1ACo_Kind.sl x 2) := by
  rw [List.range_succ_eq_map, List.filter_cons]
  have h0 : ¬ (((fun j => decide (1 ≤ j ∧ 0 < m.getD j 0)) 0) = true) := by simp
  rw [if_neg h0]
  rw [ggK1CBl_map_filter_eq]
  conv_rhs => rw [ggK1CBl_map_filter_eq]
  rw [List.map_map, List.map_map]
  congr 1
  apply List.filter_congr
  intro k _
  simp only [Function.comp_apply, Nat.succ_eq_add_one]
  rw [decide_eq_decide]
  omega

private theorem ggK1Abl_expected_nontrivial {p nf : ℕ} {m : List ℕ}
    (hd : ggMultOrd p nf = 2) :
    ggK1ACo_expectedKinds p nf false m =
      (if 0 < m.headD 0 then ({ggK1ACo_Kind.sl (m.headD 0) 1} : Multiset ggK1ACo_Kind)
        else 0) +
      Multiset.ofList (((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).map
          (fun j => ggK1ACo_Kind.sl (m.getD j 0) 2)) := by
  have hlist : ggK1ACo_expectedKindList p nf false m =
      (if 0 < m.headD 0 then [ggK1ACo_Kind.sl (m.headD 0) 1] else []) ++
      ((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).map
          (fun j => ggK1ACo_Kind.sl (m.getD j 0) 2) := by
    unfold ggK1ACo_expectedKindList
    rw [if_neg (by rw [hd]; decide)]
    simp only [Bool.false_eq_true, if_false]
  rw [ggK1ACo_expectedKinds, hlist, ← Multiset.coe_add]
  congr 1
  by_cases h0 : 0 < m.headD 0
  · rw [if_pos h0, if_pos h0]; rfl
  · rw [if_neg h0, if_neg h0]; rfl

private theorem ggK1Abl_multOrd_eq_one_or_two {p nf : ℕ}
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1) :
    ggMultOrd p nf = 1 ∨ ggMultOrd p nf = 2 := by
  unfold ggMultOrd
  by_cases h1 : p ∣ 2 ^ nf - 1
  · left; rw [if_pos h1]
  · right; rw [if_neg h1]
    rcases hdvd with h | h
    · exact absurd h h1
    · rw [if_pos h]

private theorem ggK1Abl_kind_multiset_d1 {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (hxp : xhat ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1))) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m)
    (hd1 : ggMultOrd p nf = 1) :
    (Finset.univ : Finset {h : K[X] // h ∈ primaryFactors (ggK1A_glEnd xhat.1)}).val.map
      (fun i => ggK1Abl_kind xhat i.1) = ggK1ACo_expectedKinds p nf false m := by
  classical
  have hhead : m.getD 0 0 =
      Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) := by
    rw [hm.head_eq]
  rw [ggK1CBl_univ_map_subtype_val]
  rw [ggK1Abl_expected_trivial hd1 hm.length_eq]
  have hkind : ∀ h ∈ (primaryFactors (ggK1A_glEnd xhat.1)).val,
      ggK1Abl_kind xhat h = ggK1ACo_Kind.sl
        (primaryMultiplicity (ggK1A_glEnd xhat.1) h) 1 := by
    intro h hh
    have hmem : h ∈ primaryFactors (ggK1A_glEnd xhat.1) := Finset.mem_val.mp hh
    rw [ggK1Abl_kind]
    congr 1
    by_cases hx : h = X - 1
    · subst hx; exact natDegree_X_sub_C 1
    · rw [ggK1Abl_natDegree_eq_ggMultOrd hp hp2 hnf hK hdvd xhat hxp hmem hx, hd1]
  rw [Multiset.map_congr rfl hkind]
  rw [show Multiset.map (fun h => ggK1ACo_Kind.sl
        (primaryMultiplicity (ggK1A_glEnd xhat.1) h) 1)
        (primaryFactors (ggK1A_glEnd xhat.1)).val =
      Multiset.map (fun x => ggK1ACo_Kind.sl x 1)
        (Multiset.map (primaryMultiplicity (ggK1A_glEnd xhat.1))
          (primaryFactors (ggK1A_glEnd xhat.1)).val) from by
    rw [Multiset.map_map]
    rfl]
  have hpmult : (primaryFactors (ggK1A_glEnd xhat.1)).val.map
      (primaryMultiplicity (ggK1A_glEnd xhat.1)) =
      Multiset.ofList (m.filter (fun x => decide (x ≠ 0))) := by
    have htail : Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        (ggK1A_selfDualFactors (xhat : GL (Fin N) K)).val.map
          (primaryMultiplicity (ggK1A_glEnd xhat.1)) := by
      rcases hm.blocks_eq with ⟨⟨h2, -⟩, -⟩ | ⟨-, -, htail⟩
      · rw [hd1] at h2; omega
      · exact htail
    have hmemX : (X - 1 : K[X]) ∈ primaryFactors (ggK1A_glEnd xhat.1) ↔ 0 < m.getD 0 0 := by
      rw [hhead, ← ggK1Abl_primaryMultiplicity_X_sub_one xhat]
      exact ggK1Abl_X_sub_one_mem_iff xhat hsq
    have hsplit : (primaryFactors (ggK1A_glEnd xhat.1)).val =
        ((primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h = X - 1)).val +
        ((primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h ≠ X - 1)).val := by
      rw [Finset.filter_val, Finset.filter_val]
      exact (Multiset.filter_add_not (fun h => h = X - 1) _).symm
    have hX1 : ((primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h = X - 1)).val.map
        (primaryMultiplicity (ggK1A_glEnd xhat.1)) =
        if 0 < m.getD 0 0 then {m.getD 0 0} else 0 := by
      by_cases hX : (X - 1 : K[X]) ∈ primaryFactors (ggK1A_glEnd xhat.1)
      · have hpos : 0 < m.getD 0 0 := hmemX.mp hX
        rw [if_pos hpos]
        have hsing :
            (primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h = X - 1) = {X - 1} := by
          refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
          · rw [Finset.mem_filter]; exact ⟨hX, rfl⟩
          · intro h hh
            rw [Finset.mem_filter] at hh
            exact hh.2
        rw [hsing, Finset.singleton_val, Multiset.map_singleton,
          ggK1Abl_primaryMultiplicity_X_sub_one xhat]
        exact congrArg (fun x => ({x} : Multiset ℕ)) hhead.symm
      · have hneg : ¬ 0 < m.getD 0 0 := fun h => hX (hmemX.mpr h)
        rw [if_neg hneg]
        have hempty : (primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h = X - 1) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro h hh heq
          exact hX (heq ▸ hh)
        rw [hempty]; rfl
    have hSDF : ((primaryFactors (ggK1A_glEnd xhat.1)).filter (fun h => h ≠ X - 1)).val.map
        (primaryMultiplicity (ggK1A_glEnd xhat.1)) =
        Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) := by
      rw [htail]; rfl
    rw [hsplit, Multiset.map_add, hX1, hSDF]
    rw [ggK1Abl_filter_cons m]
    by_cases h0 : m.getD 0 0 = 0
    · rw [if_neg (by omega : ¬ 0 < m.getD 0 0),
        if_neg (by omega : ¬ m.getD 0 0 ≠ 0)]
    · rw [if_pos (by omega : 0 < m.getD 0 0),
        if_pos (by omega : m.getD 0 0 ≠ 0)]
  rw [hpmult]
  rw [Multiset.map_coe]

private theorem ggK1Abl_kind_multiset_d2 {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    (xhat : ↥(LargeEvenSLGroup (Fin N) K)) (hxp : xhat ^ p = 1)
    (hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1))) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m)
    (hd2 : ggMultOrd p nf = 2) :
    (Finset.univ : Finset {h : K[X] // h ∈ primaryFactors (ggK1A_glEnd xhat.1)}).val.map
      (fun i => ggK1Abl_kind xhat i.1) = ggK1ACo_expectedKinds p nf false m := by
  classical
  have hhead : m.getD 0 0 =
      Module.finrank K (primaryComponent (ggK1A_glEnd xhat.1) (X - 1)) := by
    rw [hm.head_eq]
  set pf := primaryFactors (ggK1A_glEnd xhat.1) with hpf
  set sdf := ggK1A_selfDualFactors (xhat : GL (Fin N) K) with hsdf
  have hsdf_eq : sdf = pf.filter (fun h => h ≠ X - 1) := by
    rw [hsdf, hpf, ggK1A_selfDualFactors]
  set L : List ℕ := ((List.range ((p - 1) / 2)).map (fun j => m.getD (j + 1) 0)).filter
    (fun x => decide (x ≠ 0)) with hL
  have hbe : Multiset.ofList L = sdf.val.map (primaryMultiplicity (ggK1A_glEnd xhat.1)) := by
    rcases hm.blocks_eq with ⟨⟨h2, -⟩, -, hbe⟩ | ⟨hnot, -, -⟩
    · exact hbe
    · exact absurd ⟨hd2, rfl⟩ hnot
  have hmemX : (X - 1 : K[X]) ∈ pf ↔ 0 < m.getD 0 0 := by
    rw [hhead, ← ggK1Abl_primaryMultiplicity_X_sub_one xhat]
    exact ggK1Abl_X_sub_one_mem_iff xhat hsq
  rw [ggK1CBl_univ_map_subtype_val]
  rw [ggK1Abl_expected_nontrivial hd2]
  have hsplit : pf.val = (pf.filter (fun h => h = X - 1)).val +
      (pf.filter (fun h => h ≠ X - 1)).val := by
    rw [Finset.filter_val, Finset.filter_val]
    exact (Multiset.filter_add_not (fun h => h = X - 1) _).symm
  have hsdfkind : ∀ h ∈ sdf.val, ggK1Abl_kind xhat h =
      ggK1ACo_Kind.sl (primaryMultiplicity (ggK1A_glEnd xhat.1) h) 2 := by
    intro h hh
    have hmem : h ∈ pf := by
      have := Finset.mem_val.mp hh
      rw [hsdf_eq, Finset.mem_filter] at this
      exact this.1
    have hne : h ≠ X - 1 := by
      have := Finset.mem_val.mp hh
      rw [hsdf_eq, Finset.mem_filter] at this
      exact this.2
    rw [ggK1Abl_kind]
    congr 1
    rw [ggK1Abl_natDegree_eq_ggMultOrd hp hp2 hnf hK hdvd xhat hxp hmem hne, hd2]
  have hX1kind : ∀ h ∈ (pf.filter (fun h => h = X - 1)).val, ggK1Abl_kind xhat h =
      ggK1ACo_Kind.sl (primaryMultiplicity (ggK1A_glEnd xhat.1) h) 1 := by
    intro h hh
    have hx : h = X - 1 := (Finset.mem_filter.mp (Finset.mem_val.mp hh)).2
    rw [ggK1Abl_kind, hx]
    congr 1
    exact natDegree_X_sub_C 1
  have hX1 : ((pf.filter (fun h => h = X - 1)).val.map (fun h => ggK1Abl_kind xhat h)) =
      if 0 < m.getD 0 0 then ({ggK1ACo_Kind.sl (m.getD 0 0) 1} : Multiset ggK1ACo_Kind)
        else 0 := by
    by_cases hX : (X - 1 : K[X]) ∈ pf
    · have hpos : 0 < m.getD 0 0 := hmemX.mp hX
      rw [if_pos hpos]
      have hsing : pf.filter (fun h => h = X - 1) = {X - 1} := by
        refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
        · rw [Finset.mem_filter]; exact ⟨hX, rfl⟩
        · intro h hh; exact (Finset.mem_filter.mp hh).2
      rw [hsing, Finset.singleton_val, Multiset.map_singleton]
      congr 1
      rw [hX1kind (X - 1) (by rw [Finset.mem_val, Finset.mem_filter]; exact ⟨hX, rfl⟩),
        ggK1Abl_primaryMultiplicity_X_sub_one xhat]
      exact congrArg (fun x => ggK1ACo_Kind.sl x 1) hhead.symm
    · have hneg : ¬ 0 < m.getD 0 0 := fun h => hX (hmemX.mpr h)
      rw [if_neg hneg]
      have hempty : pf.filter (fun h => h = X - 1) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro h hh heq; exact hX (heq ▸ hh)
      rw [hempty]; rfl
  have hSDF : (sdf.val.map (fun h => ggK1Abl_kind xhat h)) =
      Multiset.ofList (L.map (fun x => ggK1ACo_Kind.sl x 2)) := by
    rw [Multiset.map_congr rfl hsdfkind]
    rw [show Multiset.map (fun h => ggK1ACo_Kind.sl
        (primaryMultiplicity (ggK1A_glEnd xhat.1) h) 2) sdf.val =
        (Multiset.map (primaryMultiplicity (ggK1A_glEnd xhat.1)) sdf.val).map
          (fun x => ggK1ACo_Kind.sl x 2) from by
      rw [Multiset.map_map]; rfl]
    rw [← hbe, Multiset.map_coe]
  have hRHS2 : Multiset.ofList (((List.range ((p - 1) / 2 + 1)).filter
        (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).map
          (fun j => ggK1ACo_Kind.sl (m.getD j 0) 2)) =
      Multiset.ofList (L.map (fun x => ggK1ACo_Kind.sl x 2)) := by
    rw [ggK1Abl_range_filter_sl, hL]
  rw [hsplit, Multiset.map_add]
  rw [show (pf.filter (fun h => h ≠ X - 1)) = sdf from hsdf_eq.symm]
  rw [hX1, hSDF, hRHS2]
  rw [List.headD_eq_getD]

private theorem ggK1Abl_component_eq_A {N : ℕ} {K : Type} [Field K] [Finite K]
    (xhat : ↥(LargeEvenSLGroup (Fin N) K))
    (hsq : Squarefree (minpoly K ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K))))
    (J : Subgroup ↥(LargeEvenSLGroup (Fin N) K))
    (hJ : CFSG.Assembly.IsComponentOf J (ggFixSub (MulAut.conj xhat))) :
    ∃ h ∈ primaryFactors (ggK1A_glEnd xhat.1), ggK1Abl_A xhat h = J := by
  classical
  let CGL := gl_centralizer (ggK1Abl_x xhat)
  let J' : Subgroup (LinearMap.GeneralLinearGroup K (Fin N → K)) := J.map (ggK1Abl_iota N K)
  have hJ'le : J' ≤ CGL := by
    have h1 : J' ≤ (ggFixSub (MulAut.conj xhat)).map (ggK1Abl_iota N K) :=
      Subgroup.map_mono hJ.1
    rw [ggK1Abl_fixSub_conj_eq_centralizer, ggK1Abl_iota_centralizer] at h1
    exact h1.trans inf_le_left
  have hJ'sub : CFSG.Assembly.IsSubnormal J' CGL := by
    have hmap : CFSG.Assembly.IsSubnormal J'
        ((ggFixSub (MulAut.conj xhat)).map (ggK1Abl_iota N K)) :=
      hJ.2.1.map (ggK1Abl_iota N K)
    rw [ggK1Abl_fixSub_conj_eq_centralizer, ggK1Abl_iota_centralizer] at hmap
    have hnorm : ((CGL ⊓ (slGL N K).range).subgroupOf CGL).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact Subgroup.Normal.subgroupOf (ggK1Abl_range_slGL_normal N K) CGL
    exact hmap.trans (CFSG.Assembly.IsSubnormal.step inf_le_left hnorm
      (CFSG.Assembly.IsSubnormal.refl _))
  have hJ'q : CFSG.Assembly.IsQuasisimple ↥J' :=
    CFSG.Assembly.IsQuasisimple.of_mulEquiv
      (Subgroup.equivMapOfInjective J (ggK1Abl_iota N K) (ggK1Abl_iota_injective N K)).symm hJ.2.2
  have hJ'comp : CFSG.Assembly.IsComponentOf J' CGL := ⟨hJ'le, hJ'sub, hJ'q⟩
  let e := glCentralizerEquivPi hsq
  have hJ'subtop : CFSG.Assembly.IsComponentOf (J'.subgroupOf CGL) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · exact CFSG.Assembly.IsSubnormal.of_mathlib hJ'sub.subgroupOf
    · exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe hJ'le) hJ'q
  have hKcomp : CFSG.Assembly.IsComponentOf ((J'.subgroupOf CGL).map e.toMonoidHom) ⊤ :=
    (CFSG.Assembly.isComponentOf_iff_open).mpr
      ((CFSG.ComponentClassification.LocalComponents.equiv_iff e (J'.subgroupOf CGL)).mpr
        ((CFSG.Assembly.isComponentOf_iff_open).mp hJ'subtop))
  obtain ⟨b₀, hb₀⟩ := CFSG.LieType.SemisimpleCentralizers.Held.exists_factor_of_isComponentOf_top
    (H := fun b : primaryFactors ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
      Module.End K (Fin N → K)) => blockGL (ggK1Abl_x xhat : Module.End K (Fin N → K)) b)
    ((CFSG.Assembly.isComponentOf_iff_open).mp hKcomp)
  have hJ'F : J' ≤ linearSpecialBlock (ggK1Abl_x xhat) b₀ := by
    intro g hg
    rw [mem_linearSpecialBlock]
    have hgCGL : g ∈ CGL := hJ'le hg
    refine ⟨hgCGL, ?_, ?_⟩
    · intro b hb hbne v hv
      have hmem : e ⟨g, hgCGL⟩ ∈ (J'.subgroupOf CGL).map e.toMonoidHom :=
        Subgroup.mem_map_of_mem _ (show (⟨g, hgCGL⟩ : ↥CGL) ∈ J'.subgroupOf CGL from hg)
      have hfac := hb₀ hmem
      have h1 : (e ⟨g, hgCGL⟩) ⟨b, hb⟩ = 1 :=
        (CFSG.LieType.SemisimpleCentralizers.Held.mem_factorSub.mp hfac) ⟨b, hb⟩
          (fun h => hbne (congrArg Subtype.val h))
      rw [← blockApply_glCentralizerEquivPi hsq ⟨g, hgCGL⟩ ⟨b, hb⟩ v hv, h1, blockApply_one]
    · have hperf : commutator ↥J' = ⊤ := hJ'q.1
      have hφ := ggK1Abl_hom_eq_one_of_perfect
        ((ggK1Abl_blockDet xhat hsq b₀).comp (Subgroup.inclusion hJ'le)) hperf
      have h1 : ggK1Abl_blockDet xhat hsq b₀ ⟨g, hgCGL⟩ = 1 := by
        have := congrArg (fun f : ↥J' →* (AdjoinRoot (b₀ : K[X]))ˣ => f ⟨g, hg⟩) hφ
        exact this
      have h2 : LinearMap.det ((LinearMap.GeneralLinearGroup.toLinearEquiv
          (glCentralizerEquivPi hsq ⟨g, hgCGL⟩ b₀)) : Module.End (AdjoinRoot (b₀ : K[X]))
            (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K (Fin N → K)) :
              Module.End K (Fin N → K)) (b₀ : K[X]))) = 1 := by
        rw [← LinearEquiv.coe_det]
        change (↑((ggK1Abl_blockDet xhat hsq b₀) ⟨g, hgCGL⟩) : AdjoinRoot (b₀ : K[X])) = 1
        simpa only [Units.val_one] using
          congrArg (fun x : (AdjoinRoot (b₀ : K[X]))ˣ => (x : AdjoinRoot (b₀ : K[X]))) h1
      exact h2
  have hFq : CFSG.IsQuasisimple ↥(linearSpecialBlock (ggK1Abl_x xhat) b₀) := by
    by_contra hq
    have hnotgood : ¬ ggK1Abl_good xhat b₀ := by
      intro hg
      exact hq ((ggK1Abl_linearSpecialBlock_isQuasisimple_iff xhat hsq b₀.2).mpr hg)
    have hsolv : Group.IsSolvable ↥(linearSpecialBlock (ggK1Abl_x xhat) b₀) := by
      haveI : Fact (Irreducible (b₀ : K[X])) := ⟨irreducible_of_mem_primaryFactors b₀.2⟩
      have hm : 1 ≤ primaryMultiplicity ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
          (Fin N → K)) : Module.End K (Fin N → K)) (b₀ : K[X]) := by
        haveI : Nontrivial (primaryComponent ((ggK1Abl_x xhat : LinearMap.GeneralLinearGroup K
            (Fin N → K)) : Module.End K (Fin N → K)) (b₀ : K[X])) :=
          Submodule.nontrivial_iff_ne_bot.mpr (primaryComponent_ne_bot hsq b₀.2)
        exact Module.finrank_pos
      have hsolvSL := ggK1Abl_SL_solvable_of_not_good (E := AdjoinRoot (b₀ : K[X])) hm
        (by simpa only [ggK1Abl_good, ggK1Abl_x_coe] using hnotgood)
      haveI := hsolvSL
      exact Group.isSolvable_of_surjective
        (f := (ggK1Abl_blockEquiv xhat hsq b₀.2).symm.toMonoidHom)
        (by simpa using (ggK1Abl_blockEquiv xhat hsq b₀.2).symm.surjective)
    have hsolv_sub : Group.IsSolvable ↥(J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.subtype (J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)))
        (Subgroup.subtype_injective _)
    have hqs_sub : CFSG.IsQuasisimple ↥(J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ'F).symm
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJ'q)
    exact ggK1Abl_not_isQuasisimple_of_isSolvable hsolv_sub hqs_sub
  have hJ'eq : J' = linearSpecialBlock (ggK1Abl_x xhat) b₀ := by
    have hcompF : CFSG.Assembly.IsComponentOf J' (linearSpecialBlock (ggK1Abl_x xhat) b₀) :=
      CFSG.Assembly.IsComponentOf.of_le_of_le hJ'comp hJ'F
        (linearSpecialBlock_le_centralizer (ggK1Abl_x xhat) b₀)
    have hsub : (J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)).IsSubnormal :=
      hcompF.2.1.subgroupOf
    have hqF : CFSG.IsQuasisimple ↥(J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ'F).symm
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJ'q)
    have hFq_open : CFSG.Open.IsQuasisimple ↥(linearSpecialBlock (ggK1Abl_x xhat) b₀) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hFq)
    haveI : Group.IsPerfect ↥(J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀)) := hqF.1
    rcases Quasisimple.perfect_subnormal_eq_bot_or_eq_top hFq_open
      (J'.subgroupOf (linearSpecialBlock (ggK1Abl_x xhat) b₀))
      (CFSG.Open.IsSubnormal.of_mathlib hsub) with hbot | htop
    · exfalso
      have hbot' : J' = ⊥ := by
        have hmap := congrArg (Subgroup.map (linearSpecialBlock (ggK1Abl_x xhat) b₀).subtype) hbot
        simpa [Subgroup.map_subgroupOf_eq_of_le hJ'F, Subgroup.map_bot] using hmap
      haveI : Nontrivial ↥J' := CFSG.LocalCores.isQuasisimple_nontrivial
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥J').mp hJ'q)
      have hsub' : Subsingleton ↥J' := by rw [hbot']; infer_instance
      exact (not_subsingleton_iff_nontrivial.mpr inferInstance) hsub'
    · exact le_antisymm hJ'F (Subgroup.subgroupOf_eq_top.mp htop)
  refine ⟨b₀.1, b₀.2, ?_⟩
  have hmap : (ggK1Abl_A xhat b₀.1).map (ggK1Abl_iota N K) = J' := by
    rw [ggK1Abl_A_map_iota xhat hsq b₀.2, hJ'eq]
  exact Subgroup.map_injective (ggK1Abl_iota_injective N K) (by rw [hmap])

theorem ggK1ACo_blocks_exists {p nf N : ℕ} {K : Type} [Field K] [Finite K]
    (hp : p.Prime) (hp2 : p ≠ 2) (hnf : 1 ≤ nf) (hK : Nat.card K = 2 ^ nf)
    (hdvd : p ∣ 2 ^ nf - 1 ∨ p ∣ 2 ^ nf + 1)
    {xhat : ↥(LargeEvenSLGroup (Fin N) K)} (hxp : xhat ^ p = 1) {m : List ℕ}
    (hm : GGK1AMultOf p nf N false K (xhat : GL (Fin N) K) m) :
    Nonempty (ggK1ACo_Blocks p nf false K N ↥(LargeEvenSLGroup (Fin N) K) xhat m) := by
  have hsq : Squarefree (minpoly K (ggK1A_glEnd xhat.1)) :=
    ggK1Abl_hsq hp hp2 hnf hK hxp
  refine ⟨{
    ι := {h : K[X] // h ∈ primaryFactors (ggK1A_glEnd xhat.1)}
    fintype := inferInstance
    A := fun i => ggK1Abl_A xhat i.1
    kind := fun i => ggK1Abl_kind xhat i.1
    hcomm := ?_
    hle := ?_
    kind_multiset := ?_
    hmodel := ?_
    hqsKind := ?_
    hsolv := ?_
    hcomp := ?_
    hfactor := ?_ }⟩
  · intro i j hij a ha b hb
    exact ggK1Abl_comm xhat hsq i.2 j.2 (fun h => hij (Subtype.ext h)) a ha b hb
  · intro i
    exact ggK1Abl_A_le_centralizer xhat i.1
  · rcases ggK1Abl_multOrd_eq_one_or_two hdvd with hd | hd
    · exact ggK1Abl_kind_multiset_d1 hp hp2 hnf hK hdvd xhat hxp hsq hm hd
    · exact ggK1Abl_kind_multiset_d2 hp hp2 hnf hK hdvd xhat hxp hsq hm hd
  · intro i
    exact ggK1Abl_A_model xhat hsq i.2 hK
  · intro i
    exact (ggK1Abl_A_isQuasisimple_iff xhat hsq i.2).trans
      (ggK1Abl_good_iff_orbit_qs hnf hK xhat hsq i.2)
  · intro i hhas hqs
    exact ggK1Abl_hsolv hp hp2 hnf hK hdvd xhat hsq i.2 hhas hqs
  · intro J hJ
    obtain ⟨h, hh, hA⟩ := ggK1Abl_component_eq_A xhat hsq J hJ
    exact ⟨⟨h, hh⟩, hA⟩
  · intro i hq
    exact ggK1Abl_A_component xhat hsq i.2 hq

end CFSG.StandardType

end
