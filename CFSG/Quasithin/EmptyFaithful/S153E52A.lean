module

public import CFSG.Quasithin.Background.G64Statement
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.EmptyFaithful.S153EDefs
public import CFSG.Quasithin.EmptyFaithful.T1531Stage4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section HStar

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem pCoreOf_HStar_eq_bot (cx : Ctx15350 T Mc M V₁ V₂ t) :
    pCoreOf 2 (HStar153 T M V₁ Mc) = ⊥ :=
  Setup.pCoreOf_autOn_eq_bot cx.hF.almostSpecialHyp.G22_four

theorem Mc_le_normalizer_Z (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Mc ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
  cx.hF.H_normalizes_V₁

@[expose] noncomputable def piTilde (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥Mc →* ↥(tildeOf (quasithinOmegaOneCenter T) Mc) :=
  ((secMk (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)) (quasithinOmegaOneCenter T)).comp
    (Subgroup.inclusion (Mc_le_normalizer_Z cx))).codRestrict
      (tildeOf (quasithinOmegaOneCenter T) Mc)
      (fun x => secMk_mem_secImg (x := Subgroup.inclusion (Mc_le_normalizer_Z cx) x) x.2)

theorem piTilde_surjective (cx : Ctx15350 T Mc M V₁ V₂ t) : Function.Surjective (piTilde cx) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := mem_secImg.1 hy
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

omit [Finite G] in
theorem tildeMc_le_normalizer {T M V₁ Mc : Subgroup G} :
    tildeOf (quasithinOmegaOneCenter T) Mc ≤
      Subgroup.normalizer (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc) : Set _) :=
  HypF91.tilde_le_normalizer (hBH := le_rfl)

@[expose] noncomputable def rhoU (cx : Ctx15350 T Mc M V₁ V₂ t) :
    ↥Mc →* MulAut ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc)) :=
  (Setup.rho (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))
    (tildeOf (quasithinOmegaOneCenter T) Mc) tildeMc_le_normalizer).comp (piTilde cx)

theorem range_rhoU (cx : Ctx15350 T Mc M V₁ V₂ t) : (rhoU cx).range = HStar153 T M V₁ Mc := by
  unfold rhoU
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (piTilde_surjective cx), Subgroup.map_top]
  exact Setup.range_rho tildeMc_le_normalizer

theorem isQuotientOfSQTKCat_HStar (cx : Ctx15350 T Mc M V₁ V₂ t) :
    G64.IsQuotientOfSQTKCat ↥(HStar153 T M V₁ Mc) := by
  have := cx.c.hyp.qtfe.simple
  have hP : pCoreOf 2 Mc ≠ ⊥ := (isHTM153_mc cx.c).1.2
  have hMcsq : CFSG.SectionRank.IsSQTKCat ↥Mc :=
    (qtkeCore_of_cat cx.c.hyp.qtfe.nonabelian cx.c.hyp.qtfe.qtke).1 Mc hP
  refine ⟨↥Mc, inferInstance, inferInstance, (rhoU cx).ker, inferInstance, hMcsq, ⟨?_⟩⟩
  exact (MulEquiv.subgroupCongr (range_rhoU cx)).symm.trans
    (QuotientGroup.quotientKerEquivRange (rhoU cx)).symm

theorem isSylowTwoOf_HStar_T (cx : Ctx15350 T Mc M V₁ V₂ t) :
    IsSylowTwoOf (autOn (tildeOf (quasithinOmegaOneCenter T) T)
      (tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) (HStar153 T M V₁ Mc) := by
  have hZT : quasithinOmegaOneCenter T ≤ T := (cx.hF.V₁_le_V).trans cx.hF.V_le_T
  have h1 : IsSylowTwoOf (tildeOf (quasithinOmegaOneCenter T) T)
      (tildeOf (quasithinOmegaOneCenter T) Mc) :=
    isSylowTwoOf_secImg cx.hF.sylow_H (Mc_le_normalizer_Z cx) hZT
  exact Setup.isSylowTwoOf_autOn h1 tildeMc_le_normalizer

theorem rhoU_apply_val (cx : Ctx15350 T Mc M V₁ V₂ t) (k : ↥Mc)
    (w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
    ((rhoU cx k w : ↥(tildeOf (quasithinOmegaOneCenter T) (UH153 T M V₁ Mc))) :
        SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T)) =
      secMk _ _ ⟨(k : G), Mc_le_normalizer_Z cx k.2⟩ *
        (w : SecQuot (Subgroup.normalizer (quasithinOmegaOneCenter T : Set G))
          (quasithinOmegaOneCenter T)) *
        (secMk _ _ ⟨(k : G), Mc_le_normalizer_Z cx k.2⟩)⁻¹ := by
  unfold rhoU
  rw [MonoidHom.comp_apply, Setup.rho_apply_coe]
  rfl

end HStar

end S153E

end CFSG.Quasithin
