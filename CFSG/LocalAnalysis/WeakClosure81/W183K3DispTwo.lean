module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3Leaves
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Img2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Shape2
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Shape3
public import CFSG.LocalAnalysis.WeakClosure81.W183K3ShapeSN
public import CFSG.LocalAnalysis.WeakClosure81.W183K3DispAux
public import CFSG.LocalAnalysis.WeakClosure81.W183B2ED
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

theorem w183k3_disp_two
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hO : LieOrderFormulasInput) (rows : Br3Rows) (leaves : Br3Leaves)
    {D : Data G} {V₀ V H : Subgroup G} {i : ℕ} (x : Ctx188 D V₀ V H i 3)
    (M : ModDataE H (eOmegaZ H D.T)) (hN : calNIn H D.T = {H ⊓ D.M})
    {Kk F : Subgroup ↥(M.img H)} (hker : KStarData Kk F)
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    (hKne : Kk ≠ ⊥) (hOK : OInf H = kerMV V H) {L : Subgroup G}
    (hLc : IsComponentModN (kerMV V H) H L) (hLT : L ⊔ D.T = H) (hsh : Shape54 H D.T L)
    {t : G} (htT : t ∈ D.T) (hne : conjSubgroup L t ≠ L)
    (hall : ∀ s ∈ D.T, conjSubgroup L s = L ∨ conjSubgroup L s = conjSubgroup L t)
    (hdyn2 : HasQuotShape L (kerMV V H : Set G) (fun X _ => IsAlt X 6 ∨ IsL3 X 1) →
      ∃ t ∈ D.T, ActsOnDynkinMod (kerMV V H) L t)
    (hbig : ∀ g' : G, Gam183 V H (eOmegaZ H D.T) i g' →
      3 ≤ (Subgroup.centralizer (eOmegaZ H D.T : Set G)).relIndex (vInH V H g'))
    {g : G} (hgam : Gam183 V H (eOmegaZ H D.T) i g) : False := by
  classical
  have hLH : L ≤ H := hLc.2.2.1
  have hX : HasQuotShape L (kerMV V H : Set G) (fun X _ => KShapeList X) := by
    have h := hasQuotShape_kshape_of_shape54 hsh
    rwa [hOK] at h
  have hQ : HasQuotShape L (kerMV V H : Set G)
      (fun X _ => IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) := by
    obtain ⟨X, hXg, φ, hs, hk, hP⟩ := hX
    exact ⟨X, hXg, φ, hs, hk, kshape_simple_nonab hO hP⟩
  have hKne' : Kk.map (M.img H).subtype ≠ ⊥ := by
    intro hbot
    exact hKne ((Subgroup.map_eq_bot_iff_of_injective Kk
      (M.img H).subtype_injective).mp hbot)
  obtain ⟨L₁, L₂, htwo, hcent, hshape, hdynimp⟩ :=
    x.br3_twoComp M hker hKk hLc hLT hQ htT hne hall
  have hq := htwo.quasi₁
  have hodd := htwo.odd₁
  have hZne : Nontrivial ↥(Subgroup.center ↥L₁) :=
    w183k3_two_center_nontrivial htwo (hcent.symm ▸ hKne')
  have hB := x.br2Common M hN
  have hneΓ : (Ctx188.packFamilyU D V H i M).Nonempty :=
    ⟨M.img (vInH V H g), ⟨g, hgam, rfl⟩⟩
  have hall' : ∀ A ∈ Ctx188.packFamilyU D V H i M, 2 ≤ mRank A :=
    fun A hA => w183k3_two_le_mRank_of_mem x M hbig hA
  obtain ⟨ED, hED⟩ := x.br2ED M
  unfold Shape54 at hsh
  rw [hOK] at hsh
  rcases hsh with h1 | h2 | ⟨h3, hdyn3⟩ | ⟨p, e', hp, hp2, hgt, h4⟩ |
    ⟨p, hp, hp2, h5⟩ | ⟨p, hp, hp2, h6⟩
  · have hP1 : IsL2 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨
        IsU3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 :=
      hshape (P := fun X _ => IsL2 X 2 ∨ IsU3 X 2)
        (fun X Y _ _ e h => h.elim (fun h2 => Or.inl (LieModel.of_mulEquiv e h2))
          (fun h3 => Or.inr (LieModel.of_mulEquiv e h3))) h1
    exact kstar_false_of_L24U34 hGA hq hodd hZne (MulEquiv.refl _) hP1
  · obtain ⟨t', ht'T, ht'⟩ := hdyn2 h2
    have hτ := hdynimp ht'T ht'
    have hP2 : IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6 ∨
        IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 1 :=
      hshape (P := fun X _ => IsAlt X 6 ∨ IsL3 X 1)
        (fun X Y _ _ e h => h.elim (fun h2 => Or.inl ⟨e.symm.trans h2.some⟩)
          (fun h3 => Or.inr (LieModel.of_mulEquiv e h3))) h2
    rcases hP2 with hA6 | hL31
    · have hZ := kstar_card_center_three hGA hq hodd hZne (MulEquiv.refl _) (Or.inl hA6)
      exact leaves.two rows hB htwo (Or.inl hA6) hZ hτ hneΓ hall' hED
    · exact kstar_false_of_L32 hGA hq hodd hZne (MulEquiv.refl _) hL31
  · obtain ⟨t', ht'T, ht'⟩ := hdyn3
    have hτ := hdynimp ht'T ht'
    have hP3 : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨
        IsSp4 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 :=
      hshape (P := fun X _ => IsL3 X 2 ∨ IsSp4 X 2)
        (fun X Y _ _ e h => h.elim (fun h2 => Or.inl (LieModel.of_mulEquiv e h2))
          (fun h3 => Or.inr (LieModel.of_mulEquiv e h3))) h3
    rcases hP3 with hL32 | hSp
    · have hZ := kstar_card_center_three hGA hq hodd hZne (MulEquiv.refl _) (Or.inr hL32)
      exact leaves.two rows hB htwo (Or.inr hL32) hZ hτ hneΓ hall' hED
    · exact kstar_false_of_sp44 hGA hq hodd hZne (MulEquiv.refl _) hSp
  · have hP4 : CFSG.Quasithin.F6.IsL2 p e' (↥L₁ ⧸ Subgroup.center ↥L₁) :=
      hshape (P := fun X _ => CFSG.Quasithin.F6.IsL2 p e' X)
        (fun X Y _ _ e h => CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h) h4
    exact kstar_false_of_L2q hGA hq hodd hZne (MulEquiv.refl _) hp hp2 hgt hP4
  · rcases h5 with ⟨h4mod, hL3⟩ | ⟨h4mod, hU3⟩
    · have hP5 : LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSL 3 p 1 :=
        hshape (P := fun X _ => LieModel X .PSL 3 p 1)
          (fun X Y _ _ e h => LieModel.of_mulEquiv e h) hL3
      have hp12 := kstar_mod12_of_L3 hGA hq hodd hZne (MulEquiv.refl _) hp hp2 h4mod hP5
      have hp3 : p ≠ 3 := by
        rintro rfl
        norm_num at hp12
      have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
      exact leaves.coverTwo rows hB htwo ⟨p, hp, hp5, Or.inl hP5⟩ hneΓ hall'
    · have hP5 : LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 3 p 1 :=
        hshape (P := fun X _ => LieModel X .PSU 3 p 1)
          (fun X Y _ _ e h => LieModel.of_mulEquiv e h) hU3
      have hp12 := kstar_mod12_of_U3 hGA hq hodd hZne (MulEquiv.refl _) hp hp2 h4mod hP5
      have hp3 : p ≠ 3 := by
        rintro rfl
        norm_num at hp12
      have hp5 : 5 ≤ p := Nat.Prime.five_le_of_ne_two_of_ne_three hp hp2 hp3
      exact leaves.coverTwo rows hB htwo ⟨p, hp, hp5, Or.inr hP5⟩ hneΓ hall'
  · have hP6 : LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSp 2 p 1 :=
      hshape (P := fun X _ => LieModel X .PSp 2 p 1)
        (fun X Y _ _ e h => LieModel.of_mulEquiv e h) h6
    exact kstar_false_of_psp4 hGA hq hodd hZne (MulEquiv.refl _) hp hp2 hP6

end CFSG.LocalAnalysis.WeakClosure81

end
