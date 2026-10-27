module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B3Algebraic
open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.StandardType.F4ExplicitPos.FiniteAction CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.StandardType.F4ExplicitPos.B3Exact CFSG.StandardType.F4ExplicitPos.B3Faithful
  CFSG.StandardType.F4ExplicitPos.B3Unconditional
  C3Range C3Algebraic B2Finite
  CFSG.Timmesfeld.LieEmbed

section B3
variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem map_sigmaΩ_C3Levi :
    (C3Levi Ω).map (sigmaΩF4 Ω) = B3Levi Ω := by
  rw [C3Levi, B3Levi, rootSpan_subgroupOf_eq_closure, rootSpan_subgroupOf_eq_closure,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨γ, hγ, c, hh⟩, rfl⟩
    have hh' : h = ⟨pinnedX .F4 Ω γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hh.symm
    subst hh'
    have hb := (dualRoot_mem_b3LeviRoots_iff hγ.1).2 hγ
    have hsl : γ ∈ F4.shortRoots ∪ F4.longRoots := by
      rw [ReeTag.shortRoots_union_longRoots]; exact hγ.1
    rcases hsl with hs | hl
    · refine ⟨F4.dualRoot γ, hb, c ^ 2, ?_⟩
      exact (congrArg Subtype.val (sigmaΩ_pinnedX_short Ω hs c)).symm
    · refine ⟨F4.dualRoot γ, hb, c, ?_⟩
      exact (congrArg Subtype.val (sigmaΩ_pinnedX_long Ω hl c)).symm
  · rintro ⟨δ, hδ, c, hg⟩
    have hγroot : IsRoot .F4 (F4.dualRoot δ) := ReeTag.isRoot_dualRoot (t := .F4) hδ.1
    have hδγ : F4.dualRoot (F4.dualRoot δ) = δ :=
      ReeTag.dualRoot_dualRoot (t := .F4) hδ.1
    have hγ : F4.dualRoot δ ∈ c3LeviRoots :=
      (dualRoot_mem_b3LeviRoots_iff hγroot).1 (by rw [hδγ]; exact hδ)
    have hsl : F4.dualRoot δ ∈ F4.shortRoots ∪ F4.longRoots := by
      rw [ReeTag.shortRoots_union_longRoots]; exact hγroot
    rcases hsl with hs | hl
    · obtain ⟨d, hd⟩ := exists_sq_eq_charTwo_algebraic Ω c
      refine ⟨⟨pinnedX F4.tag Ω (F4.dualRoot δ) d, pinnedX_mem_adjointGroup _ d⟩,
        ⟨_, hγ, d, rfl⟩, ?_⟩
      have e := sigmaΩ_pinnedX_short Ω hs d
      refine e.trans (Subtype.ext ?_)
      change pinnedX F4.tag Ω (F4.dualRoot (F4.dualRoot δ)) (d ^ 2) = (g : ModGL .F4 Ω)
      rw [hδγ, hd]
      exact hg
    · refine ⟨⟨pinnedX F4.tag Ω (F4.dualRoot δ) c, pinnedX_mem_adjointGroup _ c⟩,
        ⟨_, hγ, c, rfl⟩, ?_⟩
      have e := sigmaΩ_pinnedX_long Ω hl c
      refine e.trans (Subtype.ext ?_)
      change pinnedX F4.tag Ω (F4.dualRoot (F4.dualRoot δ)) c = (g : ModGL .F4 Ω)
      rw [hδγ]
      exact hg

theorem iBΩ_injective :
    Function.Injective (iBΩ Ω) :=
  (sigmaΩ_injective Ω).comp (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_injective Ω)

theorem iBΩ_map_range :
    MonoidHom.range ((adjointGroup .F4 Ω).subtype.comp (iBΩ Ω))
      = rootSpan .F4 Ω b3LeviRoots := by
  have hcomp : (adjointGroup .F4 Ω).subtype.comp (iBΩ Ω)
      = ((adjointGroup .F4 Ω).subtype.comp (sigmaΩF4 Ω)).comp
          (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω) := by
    ext x
    rfl
  rw [hcomp, MonoidHom.range_comp, range_iOmega_eq_C3Levi Ω]
  rw [← Subgroup.map_map, map_sigmaΩ_C3Levi Ω]
  rw [B3Levi, Subgroup.subgroupOf_map_subtype]
  exact inf_of_le_left (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)

theorem iBΩ_x
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : Ω) :
    (iBΩ Ω) (Sp.x 3 Ω γ c) =
      Adjoint.f4Par Ω (F4.dualRoot (c3ToF4 γ))
        (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1) := by
  simp only [ReeTag.tag_F4]
  change (sigmaΩF4 Ω) ((CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω) (Sp.x 3 Ω γ c)) = _
  rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x]
  exact sigmaΩF4_f4Par Ω (isRoot_c3ToF4 hγ) c

theorem iBΩ_x_pinnedX
    {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : Ω) :
    (((iBΩ Ω) (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) : ModGL .F4 Ω) =
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1) := by
  simp only [ReeTag.tag_F4]
  rw [iBΩ_x Ω hγ c,
    CFSG.StandardType.F4ExplicitPos.C3Algebraic.f4Par_coe_eq_pinnedX_alg (K := Ω)
      (ReeTag.isRoot_dualRoot (t := .F4) (isRoot_c3ToF4 hγ)) _,
    pinnedFamilySign_eq_one_charTwo Ω _, one_mul]
  rfl

theorem map_c3RootSubgroup_eq_rootSubgroup_dual
    (ι : StatedSp 3 Ω →* adjointGroup .F4 Ω)
    (hι : ∀ {γ : Fin 3 → ℤ}, γ ∈ roots (isFiniteType_cartanC 3) ∅ → ∀ c,
      ((ι (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) : ModGL .F4 Ω) =
        pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
          (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1))
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := Ω) γ).map
        ((adjointGroup .F4 Ω).subtype.comp ι)
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω (F4.dualRoot (c3ToF4 γ)) := by
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, MonoidHom.map_closure]
  unfold CFSG.Blueprint.Chevalley.rootSubgroup
  congr 1
  rw [← Set.range_comp]
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1, (hι hγ c).symm⟩
  · rintro ⟨d, rfl⟩
    rcases CFSG.StandardType.F4ExplicitPos.B3Exact.Narrow.exponent_F4_eq_one_or_two
      (pinnedData F4.tag (c3ToF4 γ)).1 with h | h
    · exact ⟨d, by
        simpa only [Subgroup.coe_subtype, Function.comp_apply, MonoidHom.comp_apply, h, pow_one]
          using hι hγ d⟩
    · obtain ⟨c, hc⟩ := exists_sq_eq_charTwo_algebraic Ω d
      exact ⟨c, by
        simpa only [Subgroup.coe_subtype, Function.comp_apply, MonoidHom.comp_apply, h, hc]
          using hι hγ c⟩

theorem iBΩ_c3RootSubgroup
    {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := Ω) γ).map
        ((adjointGroup .F4 Ω).subtype.comp (iBΩ Ω))
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω (F4.dualRoot (c3ToF4 γ)) :=
  map_c3RootSubgroup_eq_rootSubgroup_dual Ω (iBΩ Ω)
    (fun hγ c => iBΩ_x_pinnedX Ω hγ c) hγ

end B3

end CFSG.StandardType.F4ExplicitPos.B3Algebraic

end

end
