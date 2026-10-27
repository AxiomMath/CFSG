module

public import CFSG.OddTranspositions.PartFour.Line
public import CFSG.OddTranspositions.SixNineUnconditional
public import CFSG.LieType.SteinbergBRMulEquivCores

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem cimg_mul (a b : G) (S : Set G) : cimg (a * b) S = cimg a (cimg b S) := by
  unfold cimg
  rw [Set.image_image]
  congr 1
  funext x
  group

theorem cimg_one (S : Set G) : cimg 1 S = S := by
  ext x
  simp [cimg]

theorem cimg_inv_cimg (a : G) (S : Set G) : cimg a⁻¹ (cimg a S) = S := by
  rw [← cimg_mul, inv_mul_cancel, cimg_one]

theorem cimg_cimg_inv (a : G) (S : Set G) : cimg a (cimg a⁻¹ S) = S := by
  rw [← cimg_mul, mul_inv_cancel, cimg_one]

theorem cimg_injective (g : G) : Function.Injective (cimg g) := fun S T h => by
  rw [← cimg_inv_cimg g S, h, cimg_inv_cimg]

theorem image_cimg_mul (a b : G) (L : Set (Set G)) :
    (cimg a) '' ((cimg b) '' L) = (cimg (a * b)) '' L := by
  rw [Set.image_image]
  exact Set.image_congr fun S _ => (cimg_mul a b S).symm

theorem image_cimg_inv_cimg (a : G) (L : Set (Set G)) :
    (cimg a⁻¹) '' ((cimg a) '' L) = L := by
  rw [image_cimg_mul, inv_mul_cancel]
  ext T
  simp [cimg]

theorem cimg_eq_self_of_mem_normalizer {α : Set G} {g : G}
    (hg : g ∈ Subgroup.normalizer α) : cimg g α = α := by
  have h := Subgroup.mem_normalizer_iff_conj_image_eq.mp hg
  rw [show (⇑(MulAut.conj g) : G → G) = (fun x => g * x * g⁻¹) by
    funext x; rw [MulAut.conj_apply]] at h
  simpa [cimg] using h

theorem blockClass_eq_of_mem {α β : Set G} (hβ : β ∈ blockClass α) :
    blockClass β = blockClass α :=
  Set.Subset.antisymm
    (fun _ hγ => mem_blockClass_of_mem_blockClass
      (mem_blockClass_of_mem_blockClass hβ (mem_blockClass_self α)) hγ)
    (fun _ hγ => mem_blockClass_of_mem_blockClass hβ hγ)

theorem cimg_mem_blockClass_iff {g : G} {α γ : Set G} :
    cimg g γ ∈ blockClass α ↔ γ ∈ blockClass α := by
  constructor
  · intro h
    exact mem_blockClass_of_mem_blockClass
      (mem_blockClass_of_mem_blockClass h (mem_blockClass_self α))
      (mem_blockClass_comm.mp (mem_blockClass_iff.mpr ⟨g, rfl⟩))
  · intro h
    exact mem_blockClass_of_mem_blockClass
      (mem_blockClass_of_mem_blockClass h (mem_blockClass_self α))
      (mem_blockClass_iff.mpr ⟨g, rfl⟩)

theorem blockClass_cimg (g : G) (α : Set G) : blockClass (cimg g α) = blockClass α :=
  blockClass_eq_of_mem (mem_blockClass_iff.mpr ⟨g, rfl⟩)

theorem perp_cimg_mem (hN : IsNormalSet D) (g : G) {α γ : Set G} :
    cimg g γ ∈ perp D (cimg g α) ↔ γ ∈ perp D α := by
  rw [← perp_conj_image hN g]
  exact Function.Injective.mem_set_image (cimg_injective g)

theorem mem_blockLine_iff {D α β δ : Set G} :
    δ ∈ blockLine D α β ↔
      δ ∈ blockClass α ∧ ∀ γ ∈ perp D α ∩ perp D β, δ ∈ perp D γ := Iff.rfl

theorem cimg_mem_blockLine_iff (hN : IsNormalSet D) (g : G) (α β δ : Set G) :
    cimg g δ ∈ blockLine D (cimg g α) (cimg g β) ↔ δ ∈ blockLine D α β := by
  rw [mem_blockLine_iff, mem_blockLine_iff, blockClass_cimg, cimg_mem_blockClass_iff]
  constructor
  · rintro ⟨hδ, hperp⟩
    refine ⟨hδ, fun γ hγ => ?_⟩
    exact (perp_cimg_mem hN g (α := γ)).mp
      (hperp (cimg g γ) ⟨(perp_cimg_mem hN g (γ := γ)).mpr hγ.1,
        (perp_cimg_mem hN g (γ := γ)).mpr hγ.2⟩)
  · rintro ⟨hδ, hperp⟩
    refine ⟨hδ, fun γ hγ => ?_⟩
    have hγ1 : cimg g⁻¹ γ ∈ perp D α := by
      rw [← perp_cimg_mem hN g (α := α), cimg_cimg_inv]
      exact hγ.1
    have hγ2 : cimg g⁻¹ γ ∈ perp D β := by
      rw [← perp_cimg_mem hN g (α := β), cimg_cimg_inv]
      exact hγ.2
    have h := hperp (cimg g⁻¹ γ) ⟨hγ1, hγ2⟩
    rw [← cimg_cimg_inv g γ]
    exact (perp_cimg_mem hN g (α := cimg g⁻¹ γ) (γ := δ)).mpr h

theorem blockLine_cimg (hN : IsNormalSet D) (g : G) (α β : Set G) :
    blockLine D (cimg g α) (cimg g β) = (cimg g) '' blockLine D α β := by
  ext δ
  constructor
  · intro hδ
    refine ⟨cimg g⁻¹ δ, ?_, cimg_cimg_inv g δ⟩
    have h : cimg g (cimg g⁻¹ δ) ∈ blockLine D (cimg g α) (cimg g β) := by
      rwa [cimg_cimg_inv]
    exact (cimg_mem_blockLine_iff hN g α β (cimg g⁻¹ δ)).mp h
  · rintro ⟨ε, hε, rfl⟩
    exact (cimg_mem_blockLine_iff hN g α β ε).mpr hε

theorem blockLine_comm {α β : Set G} (hβ : β ∈ blockClass α) :
    blockLine D β α = blockLine D α β := by
  ext δ
  rw [mem_blockLine_iff, mem_blockLine_iff, blockClass_eq_of_mem hβ]
  rw [Set.inter_comm (perp D α) (perp D β)]

theorem DalphaStar_cimg (hN : IsNormalSet D) (g : G) (α : Set G) :
    DalphaStar D (cimg g α) = cimg g (DalphaStar D α) := by
  ext x
  rw [mem_DalphaStar_iff, mem_cimg, mem_DalphaStar_iff]
  constructor
  · rintro ⟨β, hβ, hxβ⟩
    have hmem : β ∈ (fun γ => cimg g γ) '' Dalpha D α := by
      rwa [Dalpha_conj_image hN g]
    obtain ⟨β', hβ', rfl⟩ := hmem
    exact ⟨β', hβ', mem_cimg.mp hxβ⟩
  · rintro ⟨β, hβ, hx⟩
    have hmem : cimg g β ∈ Dalpha D (cimg g α) := by
      rw [← Dalpha_conj_image hN g]
      exact ⟨β, hβ, rfl⟩
    exact ⟨cimg g β, hmem, mem_cimg.mpr hx⟩

theorem Halpha_cimg (hN : IsNormalSet D) (g : G) (α : Set G) :
    Halpha D (cimg g α) = (Halpha D α).map (MulAut.conj g).toMonoidHom := by
  change Subgroup.closure (DalphaStar D (cimg g α)) =
    (Subgroup.closure (DalphaStar D α)).map (MulAut.conj g).toMonoidHom
  rw [DalphaStar_cimg hN g α, closure_cimg]

theorem Malpha_cimg (hN : IsNormalSet D) (g : G) (α : Set G) :
    Malpha D (cimg g α) = (Malpha D α).map (MulAut.conj g).toMonoidHom := by
  have hb : Halpha D (cimg g α) = (Halpha D α).map (MulAut.conj g).toMonoidHom :=
    Halpha_cimg hN g α
  let e : (Halpha D α) ≃* (Halpha D (cimg g α)) :=
    ((Halpha D α).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hb.symm)
  have hcomp : (Halpha D (cimg g α)).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (Halpha D α).subtype := by
    ext x
    change ((e x : Halpha D (cimg g α)) : G) = MulAut.conj g ((x : Halpha D α) : G)
    show (((MulEquiv.subgroupCongr hb.symm
      ((Halpha D α).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective x)) : Halpha D (cimg g α)) : G) =
      MulAut.conj g ((x : Halpha D α) : G)
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply (Halpha D α) _ _ x
  rw [show Malpha D (cimg g α) =
      (CFSG.solvableRadical (Halpha D (cimg g α))).map
        (Halpha D (cimg g α)).subtype from rfl,
    show Malpha D α =
      (CFSG.solvableRadical (Halpha D α)).map (Halpha D α).subtype from rfl,
    ← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv e]
  rw [Subgroup.map_map, hcomp]
  exact (Subgroup.map_map (K := CFSG.solvableRadical (Halpha D α))
    (g := (MulAut.conj g).toMonoidHom) (f := (Halpha D α).subtype)).symm

end CFSG.OddTranspositions.PartFour
