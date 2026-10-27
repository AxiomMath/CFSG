module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (I9 Hbar9 BarO3)
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem c8_p0 (D : Data G) {V₀ V K : Subgroup G} {hV : IsElemAbelian 2 V} {v₀ : IntMod V hV}
    (hMs : D.M ≤ stabTil V₀ V)
    (hIm : barSub V₀ V hV (K ⊓ D.M) = ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀))
    (he64 : IsE64L3 ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)))
    (hperf : ⁅ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀),
        ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)⁆ =
      ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)) :
    C8P0 (K ⊓ D.M) (K ⊓ F11.CTilde D.M V₀ V) := by
  have hMn : D.M ≤ normalizer (V : Set G) := hMs.trans (stabTil_le_normalizer V₀ V)
  have hXs : K ⊓ D.M ≤ stabTil V₀ V := inf_le_right.trans hMs
  let φ : ↥(K ⊓ D.M) →* ↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp (Subgroup.inclusion hXs))
      (ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀))
      (fun x => by
        rw [MonoidHom.comp_apply]
        exact hIm ▸ actTil_mem_barSub V₀ V hV x.2 (hXs x.2))
  refine ⟨↥(ptCent (Mbar D.M V₀ V hV) (mkTil V₀ V hV v₀)), inferInstance, φ, ?_, ?_,
    he64, Subgroup.isPerfect_iff.2 hperf⟩
  · rintro ⟨p, hp⟩
    have hp' : p ∈ barSub V₀ V hV (K ⊓ D.M) := hIm.symm ▸ hp
    obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV (K ⊓ D.M) p).1 hp'
    exact ⟨⟨(g : G), hg⟩, Subtype.ext hgφ⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    exact ⟨fun h1 => ⟨x.2.1, x.2.2, hXs x.2, congrArg Subtype.val h1⟩,
      fun h1 => Subtype.ext h1.2.2.2⟩

theorem c8p0_subgroupOf {K Y C : Subgroup G} (hYK : Y ≤ K) (hCY : C ≤ Y) (h : C8P0 Y C) :
    C8P0 (Y.subgroupOf K) (C.subgroupOf K) := by
  obtain ⟨P, inst, φ, hs, hk, he, hp⟩ := h
  let e := Subgroup.subgroupOfEquivOfLe hYK
  refine ⟨P, inst, φ.comp e.toMonoidHom, hs.comp e.surjective, ?_, he, hp⟩
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hk]
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hx
  · intro hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hx

theorem c8k_prod_of_alt {M K : Subgroup G} (h : K = (K ⊓ M) ⊔ I9 K) :
    (K ⊓ M).subgroupOf K ⊔ CFSG.pPrimeCore 3 ↥K = ⊤ := by
  unfold I9 at h
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (inf_le_left : K ⊓ M ≤ K),
    Subgroup.map_top, Subgroup.range_subtype]
  exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
