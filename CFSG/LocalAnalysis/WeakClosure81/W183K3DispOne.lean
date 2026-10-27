module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3ImgCore
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Shape3
public import CFSG.LocalAnalysis.WeakClosure81.W183K3ShapeSN
public import CFSG.LocalAnalysis.WeakClosure81.W183K3DispAux
public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Base

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open W183K3

variable {G : Type} [Group G] [Finite G]

theorem w183k3_disp_one
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hO : LieOrderFormulasInput) (rows : Br3Rows) (leaves : Br3Leaves)
    {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (x : Ctx188 D V₀ V H i 3)
    (M : ModDataE H (eOmegaZ H D.T)) (hN : calNIn H D.T = {H ⊓ D.M})
    {Kk F : Subgroup ↥(M.img H)} (hker : KStarData Kk F)
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    (hKne : Kk ≠ ⊥) (hOK : OInf H = kerMV V H) {L : Subgroup G}
    (hLc : IsComponentModN (kerMV V H) H L) (hLn : H ≤ Subgroup.normalizer (L : Set G))
    (hLT : L ⊔ D.T = H) (hsh : Shape54 H D.T L)
    (hdyn2 : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsAlt X 6 ∨ IsL3 X 1) →
      ∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t)
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'))
    {g : G} (hgam : Gam183 V H (eOmegaZ H D.T) i g) : False := by
  classical
  have hsh0 := hsh
  have hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => KShapeList X) := by
    have h := hasQuotShape_kshape_of_shape54 hsh0
    rwa [hOK] at h
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, kshape_simple_nonab hO hP⟩
  have hKne' : Kk.map (M.img H).subtype ≠ ⊥ := by
    intro h
    exact hKne ((Subgroup.map_eq_bot_iff_of_injective Kk (M.img H).subtype_injective).mp h)
  obtain ⟨L', hcore, hcent, hshape⟩ := x.br3_oneCore M hker hKk hLc hLn hLT hQ
  have hq : CFSG.Open.IsQuasisimple ↥L' := hcore.quasi
  have hodd : Odd (Nat.card ↥(Subgroup.center ↥L')) :=
    w183k3_odd_center_of_quasiCentre hcore.odd
  have hZne : Nontrivial ↥(Subgroup.center ↥L') :=
    w183k3_nontrivial_center_of_ne_bot (hcent.symm ▸ hKne')
  have hB := x.br2Common M hN
  have hneΓ : (Ctx188.packFamilyU D V H i M).Nonempty :=
    ⟨M.img (vInH V H g), ⟨g, hgam, rfl⟩⟩
  have hall : ∀ A ∈ Ctx188.packFamilyU D V H i M, 2 ≤ mRank A :=
    fun A hA => w183k3_two_le_mRank_of_mem x M hbig hA
  have hA4 : ∃ A ∈ Ctx188.packFamilyU D V H i M, 4 ≤ Nat.card ↥A :=
    ⟨M.img (vInH V H g), ⟨g, hgam, rfl⟩,
      w183k3_four_le_card_of_mem x M hbig ⟨g, hgam, rfl⟩⟩
  unfold Shape54 at hsh
  rw [hOK] at hsh
  rcases hsh with h1 | h2 | ⟨h3shape, hdyn3⟩ | ⟨p, e', hp, hne, hgt, h4⟩ |
    ⟨p, hp, hne, hp5⟩ | ⟨p, hp, hne, h6⟩
  · exact kstar_false_of_L24U34 hGA hq hodd hZne
      (MulEquiv.refl (↥L' ⧸ Subgroup.center ↥L'))
      (hshape (fun X Y _ _ e h =>
        h.imp (CFSG.Blueprint.LieModel.of_mulEquiv e)
          (CFSG.Blueprint.LieModel.of_mulEquiv e)) h1)
  · obtain ⟨t, htT, ht⟩ := hdyn2 h2
    obtain ⟨L'', hOne, hcent'', hshape''⟩ :=
      x.br3_oneComp M hker hKk hLc hLn hLT hQ htT ht
    have hodd'' : Odd (Nat.card ↥(Subgroup.center ↥L'')) :=
      w183k3_odd_center_of_quasiCentre hOne.core.odd
    have hZne'' : Nontrivial ↥(Subgroup.center ↥L'') :=
      w183k3_nontrivial_center_of_ne_bot (hcent''.symm ▸ hKne')
    have hP := hshape'' (fun X Y _ _ e h =>
      h.imp (fun hAlt => ⟨e.symm.trans hAlt.some⟩)
        (CFSG.Blueprint.LieModel.of_mulEquiv e)) h2
    rcases hP with hA6 | hL32
    · exact leaves.one rows hB hOne (Or.inl hA6) hneΓ hall
    · exact kstar_false_of_L32 hGA hOne.core.quasi hodd'' hZne''
        (MulEquiv.refl (↥L'' ⧸ Subgroup.center ↥L'')) hL32
  · obtain ⟨t, htT, ht⟩ := hdyn3
    obtain ⟨L'', hOne, hcent'', hshape''⟩ :=
      x.br3_oneComp M hker hKk hLc hLn hLT hQ htT ht
    have hodd'' : Odd (Nat.card ↥(Subgroup.center ↥L'')) :=
      w183k3_odd_center_of_quasiCentre hOne.core.odd
    have hZne'' : Nontrivial ↥(Subgroup.center ↥L'') :=
      w183k3_nontrivial_center_of_ne_bot (hcent''.symm ▸ hKne')
    have hP := hshape'' (fun X Y _ _ e h =>
      h.imp (CFSG.Blueprint.LieModel.of_mulEquiv e)
        (CFSG.Blueprint.LieModel.of_mulEquiv e)) h3shape
    rcases hP with hL34 | hSp44
    · exact leaves.one rows hB hOne (Or.inr hL34) hneΓ hall
    · exact kstar_false_of_sp44 hGA hOne.core.quasi hodd'' hZne''
        (MulEquiv.refl (↥L'' ⧸ Subgroup.center ↥L'')) hSp44
  · exact kstar_false_of_L2q hGA hq hodd hZne
      (MulEquiv.refl (↥L' ⧸ Subgroup.center ↥L')) hp hne hgt
      (hshape (fun X Y _ _ e h =>
        CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h) h4)
  · rcases hp5 with ⟨h4m, hL3⟩ | ⟨h4m, hU3⟩
    · have hmod := kstar_mod12_of_L3 hGA hq hodd hZne
          (MulEquiv.refl (↥L' ⧸ Subgroup.center ↥L')) hp hne h4m
          (hshape (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) hL3)
      have hp5le : 5 ≤ p := by omega
      exact leaves.coverOne (T := M.img D.T) rows hB.h131 hcore
        ⟨p, hp, hp5le, Or.inl (hshape (fun X Y _ _ e h =>
          CFSG.Blueprint.LieModel.of_mulEquiv e h) hL3)⟩ hA4
    · have hmod := kstar_mod12_of_U3 hGA hq hodd hZne
          (MulEquiv.refl (↥L' ⧸ Subgroup.center ↥L')) hp hne h4m
          (hshape (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) hU3)
      have hp5le : 5 ≤ p := by omega
      exact leaves.coverOne (T := M.img D.T) rows hB.h131 hcore
        ⟨p, hp, hp5le, Or.inr (hshape (fun X Y _ _ e h =>
          CFSG.Blueprint.LieModel.of_mulEquiv e h) hU3)⟩ hA4
  · exact kstar_false_of_psp4 hGA hq hodd hZne
      (MulEquiv.refl (↥L' ⧸ Subgroup.center ↥L')) hp hne
      (hshape (fun X Y _ _ e h => CFSG.Blueprint.LieModel.of_mulEquiv e h) h6)

end CFSG.LocalAnalysis.WeakClosure81

end
