module

public import CFSG.LocalAnalysis.StandardType.GGTBRowCoordFrame
public import CFSG.LocalAnalysis.StandardType.GGF4AutWeylTableB
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4F4
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcWeylNormAdjoint

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem ggF4Row_coxeterLift : CoxeterMatrix.F₄.IsLiftable (fun i => simple .F4 i) :=
  fun i j => by
    rw [FrameRoute.coxeterF4_eq]
    exact (CFSG.LieType.Chevalley.coxeterSystem .F4).simple_mul_simple_pow i j

theorem ggF4Row_coxeterLift_symm :
    (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4)).IsLiftable
      (fun i => CoxeterMatrix.F₄.simple i) :=
  fun i j => by
    rw [← FrameRoute.coxeterF4_eq]
    exact CoxeterMatrix.F₄.toCoxeterSystem.simple_mul_simple_pow i j

noncomputable def ggF4Row_coxeterHom : CoxeterMatrix.F₄.Group →* WeylGroup .F4 :=
  CoxeterMatrix.F₄.toCoxeterSystem.lift ⟨fun i => simple .F4 i, ggF4Row_coxeterLift⟩

noncomputable def ggF4Row_coxeterHomInv : WeylGroup .F4 →* CoxeterMatrix.F₄.Group :=
  (CFSG.LieType.Chevalley.coxeterSystem .F4).lift
    ⟨fun i => CoxeterMatrix.F₄.simple i, ggF4Row_coxeterLift_symm⟩

theorem ggF4Row_coxeterHom_simple (i : Fin 4) :
    ggF4Row_coxeterHom (CoxeterMatrix.F₄.simple i) = simple .F4 i := by
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple CoxeterMatrix.F₄.toCoxeterSystem ggF4Row_coxeterLift i

noncomputable def ggF4Row_coxeterGroupEquiv :
    CoxeterMatrix.F₄.Group ≃* WeylGroup .F4 := by
  have h1 : ggF4Row_coxeterHomInv.comp ggF4Row_coxeterHom = MonoidHom.id _ := by
    refine CoxeterMatrix.F₄.toCoxeterSystem.ext_simple fun i => ?_
    have hψ : ggF4Row_coxeterHom (CoxeterMatrix.F₄.toCoxeterSystem.simple i) = simple .F4 i :=
      CoxeterSystem.lift_apply_simple CoxeterMatrix.F₄.toCoxeterSystem ggF4Row_coxeterLift i
    have hψ' : ggF4Row_coxeterHomInv (simple .F4 i) = CoxeterMatrix.F₄.simple i :=
      CoxeterSystem.lift_apply_simple (CFSG.LieType.Chevalley.coxeterSystem .F4)
        ggF4Row_coxeterLift_symm i
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hψ, hψ', CoxeterMatrix.toCoxeterSystem_simple]
  have h2 : ggF4Row_coxeterHom.comp ggF4Row_coxeterHomInv = MonoidHom.id _ := by
    refine (CFSG.LieType.Chevalley.coxeterSystem .F4).ext_simple fun i => ?_
    have hψ' : ggF4Row_coxeterHomInv (simple .F4 i) = CoxeterMatrix.F₄.simple i :=
      CoxeterSystem.lift_apply_simple (CFSG.LieType.Chevalley.coxeterSystem .F4)
        ggF4Row_coxeterLift_symm i
    have hψ : ggF4Row_coxeterHom (CoxeterMatrix.F₄.simple i) = simple .F4 i :=
      ggF4Row_coxeterHom_simple (Fin.cast (by rfl) i)
    rw [MonoidHom.comp_apply, MonoidHom.id_apply, hψ', hψ]
  exact MulEquiv.ofBijective ggF4Row_coxeterHom
    ⟨fun a b hab => by
      have ha := DFunLike.congr_fun h1 a
      have hb := DFunLike.congr_fun h1 b
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at ha hb
      rw [← ha, hab, hb],
     fun y => by
      have hh := DFunLike.congr_fun h2 y
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply] at hh
      exact ⟨ggF4Row_coxeterHomInv y, hh⟩⟩

theorem ggF4Row_coxeterGroupEquiv_simple (i : Fin Tag.F4.rank) :
    ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple i) = simple .F4 i := by
  change ggF4Row_coxeterHom (CoxeterMatrix.F₄.simple i) = simple .F4 i
  rw [← CoxeterMatrix.toCoxeterSystem_simple]
  exact CoxeterSystem.lift_apply_simple CoxeterMatrix.F₄.toCoxeterSystem
    ggF4Row_coxeterLift i

theorem ggTorusCoordFrame_comp {p : ℕ} {R : Type} [Group R] {k m : ℕ}
    (χ : Multiplicative (Fin m → ZMod p) →* R)
    (γ : Multiplicative (Fin k → ZMod p) ≃* Multiplicative (Fin m → ZMod p))
    {ι : Type} {M : CoxeterMatrix ι} (h : GGTorusCoordFrame p χ M) :
    GGTorusCoordFrame p (χ.comp γ.toMonoidHom) M := by
  obtain ⟨s, hs, e, he⟩ := h
  refine ⟨fun i => (MulAut.congr γ).symm (s i), ?_, ?_⟩
  · intro i
    rw [NbrTableBExc.mem_ggTorusInvolSet_comp_equiv γ χ, MulEquiv.apply_symm_apply]
    exact hs i
  · have hsub : ggTorusInduced (χ.comp γ.toMonoidHom) =
        (ggTorusInduced χ).comap (MulAut.congr γ).toMonoidHom := by
      ext u
      rw [Subgroup.mem_comap]
      exact ExcWeylOuter.mem_ggTorusInduced_comp_equiv γ χ u
    have hmap : (ggTorusInduced (χ.comp γ.toMonoidHom)).map
        (MulAut.congr γ).toMonoidHom = ggTorusInduced χ := by
      rw [hsub, Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr (MulAut.congr γ).surjective, top_inf_eq]
    let Ψ : ↥(ggTorusInduced (χ.comp γ.toMonoidHom)) ≃* ↥(ggTorusInduced χ) :=
      (Subgroup.equivMapOfInjective _ (MulAut.congr γ).toMonoidHom
        (MulAut.congr γ).injective).trans (MulEquiv.subgroupCongr hmap)
    have hΨapply : ∀ x : ↥(ggTorusInduced (χ.comp γ.toMonoidHom)),
        (Ψ x : MulAut (Multiplicative (Fin m → ZMod p))) = MulAut.congr γ x := fun _ => rfl
    have hΨsymm : ∀ y : ↥(ggTorusInduced χ),
        (Ψ.symm y : MulAut (Multiplicative (Fin k → ZMod p))) = (MulAut.congr γ).symm y := by
      intro y
      have h1 : MulAut.congr γ (Ψ.symm y) =
          (y : MulAut (Multiplicative (Fin m → ZMod p))) := by
        rw [← hΨapply (Ψ.symm y), MulEquiv.apply_symm_apply]
      have h2 := congrArg (fun z => (MulAut.congr γ).symm z) h1
      rwa [MulEquiv.symm_apply_apply] at h2
    refine ⟨e.trans Ψ.symm, fun i => ?_⟩
    change (Ψ.symm (e (M.simple i)) : MulAut (Multiplicative (Fin k → ZMod p))) =
      (MulAut.congr γ).symm (s i)
    rw [hΨsymm, he i]

theorem ggTorusCoordFrame_post {p : ℕ} {R R' : Type} [Group R] [Group R'] {k : ℕ}
    (e : R ≃* R') (χ : Multiplicative (Fin k → ZMod p) →* R)
    {ι : Type} {M : CoxeterMatrix ι} (h : GGTorusCoordFrame p χ M) :
    GGTorusCoordFrame p (e.toMonoidHom.comp χ) M := by
  obtain ⟨s, hs, e₀, he₀⟩ := h
  have hind : ggTorusInduced (e.toMonoidHom.comp χ) = ggTorusInduced χ :=
    ggTorusInduced_comp_mulEquiv e χ
  have hinv : NbrTableBExc.ggTorusInvolSet p (e.toMonoidHom.comp χ) =
      NbrTableBExc.ggTorusInvolSet p χ :=
    NbrTableBExc.ggTorusInvolSet_comp_mulEquiv e χ
  refine ⟨s, fun i => ?_, e₀.trans (MulEquiv.subgroupCongr hind).symm, fun i => ?_⟩
  · rw [hinv]; exact hs i
  · rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_symm_apply, he₀ i]

theorem ggMulAut_congr_apply {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (f : MulAut G) (x : H) : MulAut.congr e f x = e (f (e.symm x)) := by
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply]

end CFSG.StandardType

end

