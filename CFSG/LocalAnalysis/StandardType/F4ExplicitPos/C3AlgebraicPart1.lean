module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart26
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart29

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.C3Algebraic

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Timmesfeld.LieEmbed
  CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange

section Naturality

noncomputable def iOf
    (K : Type) [Field K] [CharP K 2] [Finite K] :
    ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K) :=
  Classical.choose (CFSG.StandardType.F4ExplicitPos.C3Comm.f4C3_exists_pinned_unconditional
    (CFSG.Timmesfeld.Transvection.Pres.spOrder 3 K))

theorem iOf_x
    (K : Type) [Field K] [CharP K 2] [Finite K] (γ : Fin 3 → ℤ) (c : K) :
    iOf K (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c :=
  (Classical.choose_spec (CFSG.StandardType.F4ExplicitPos.C3Comm.f4C3_exists_pinned_unconditional
    (CFSG.Timmesfeld.Transvection.Pres.spOrder 3 K))).2 γ c

theorem iOf_injective
    (K : Type) [Field K] [CharP K 2] [Finite K] :
    Function.Injective (iOf K) :=
  (Classical.choose_spec (CFSG.StandardType.F4ExplicitPos.C3Comm.f4C3_exists_pinned_unconditional
    (CFSG.Timmesfeld.Transvection.Pres.spOrder 3 K))).1

theorem hom_ext_x3 {K H : Type} [Field K] [CharP K 2] [Finite K] [Group H]
    {Ψ Ψ' : ↥(StatedSp 3 K) →* H}
    (h : ∀ γ c, Ψ (Sp.x 3 K γ c) = Ψ' (Sp.x 3 K γ c)) : Ψ = Ψ' := by
  ext g
  change g ∈ MonoidHom.eqLocus Ψ Ψ'
  have hg : g ∈ ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ := by
    rw [CFSG.StandardType.F4ExplicitPos.C3Range.iSup_c3RootSubgroup_eq_top (K := K)]
    exact Subgroup.mem_top g
  have hle : (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ) ≤ MonoidHom.eqLocus Ψ Ψ' :=
    iSup₂_le fun γ _hγ => by
      rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact h γ c
  exact hle hg

theorem iOf_natural
    {K L : Type} [Field K] [CharP K 2] [Finite K]
    [Field L] [CharP L 2] [Finite L] (f : K →+* L) :
    (j (τ := .F4) f).comp (iOf K) = (iOf L).comp (statedSpMap f 3) := by
  apply hom_ext_x3
  intro γ c
  change j f (iOf K (Sp.x 3 K γ c)) = iOf L (statedSpMap f 3 (Sp.x 3 K γ c))
  rw [iOf_x, statedSpMap_x, iOf_x]
  exact map_j_xPar (τ := .F4) f (rootOperatorFamily .F4) (c3ToF4 γ) c

theorem statedSpMap_comp {K L M : Type} [Field K] [Field L] [Field M]
    (g : L →+* M) (f : K →+* L) (n : ℕ) (x : ↥(StatedSp n K)) :
    statedSpMap g n (statedSpMap f n x) = statedSpMap (g.comp f) n x := by
  apply Subtype.ext
  simp only [coe_statedSpMap]
  exact congrArg (fun h : GL (Fin n ⊕ Fin n) K →* GL (Fin n ⊕ Fin n) M => h x)
    (Matrix.GeneralLinearGroup.map_comp (n := Fin n ⊕ Fin n) f g).symm

theorem j_comp
    {R S M : Type} [Field R] [Field S] [Field M] (g : S →+* M) (f : R →+* S) :
    j (τ := .F4) (g.comp f) = (j (τ := .F4) g).comp (j (τ := .F4) f) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  change ((j (τ := .F4) (g.comp f) x : ↥(adjointGroup .F4 M)) : ModGL .F4 M) =
    ((j (τ := .F4) g ((j (τ := .F4) f) x) : ↥(adjointGroup .F4 M)) : ModGL .F4 M)
  rw [j_apply, j_apply, j_apply, bcGL_comp]

end Naturality

section GeneralField

theorem c3RootSubgroup_eq_rootGroup_alg {K : Type} [Field K] {γ : Fin 3 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ =
      (CFSG.LieType.Universal.Symplectic.rootDatum 3 K).rootGroup γ := by
  have hp := Sp.isParametrization (n := 3) (F := K) γ (by rwa [Sp.Φ_roots])
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact (hp.1 _).2 ⟨c, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := (hp.1 g).1 hg
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem iSup_c3RootSubgroup_eq_top_alg (K : Type) [Field K] :
    (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ) = ⊤ := by
  rw [show (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
        CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ)
      = ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
          (CFSG.LieType.Universal.Symplectic.rootDatum 3 K).rootGroup γ from
    iSup_congr fun γ => iSup_congr fun hγ => c3RootSubgroup_eq_rootGroup_alg (K := K) hγ]
  exact (CFSG.LieType.Universal.Symplectic.isCTGroupDatum 3 K).iSup_eq_top

theorem f4Par_coe_eq_pinnedX_alg
    {K : Type} [Field K] [CharP K 2]
    {α : Fin (Tag.rank .F4) → ℤ} (hα : CFSG.Blueprint.Chevalley.IsRoot .F4 α) (c : K) :
    ((Adjoint.f4Par K α c : ↥(adjointGroup .F4 K)) : ModGL .F4 K)
      = pinnedX .F4 K α (((rootOperatorFamily .F4).pinnedFamilySign α : K) * c) := by
  rw [show Adjoint.f4Par K α c = xPar (rootOperatorFamily .F4) α c from rfl,
    xPar, dif_pos hα, RootOperatorFamily.coe_eltElement]
  symm
  rw [(rootOperatorFamily .F4).pinnedX_eq_eltUnit K hα, ← mul_assoc,
    (rootOperatorFamily .F4).pinnedFamilySign_mul_self K α, one_mul]

theorem iota_x_eq_pinnedX_alg
    {K : Type} [Field K] [CharP K 2]
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : K) :
    ((ι (Sp.x 3 K γ c) : ↥(adjointGroup .F4 K)) : ModGL .F4 K)
      = pinnedX .F4 K (c3ToF4 γ)
          (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c) := by
  rw [hι, f4Par_coe_eq_pinnedX_alg (isRoot_c3ToF4 hγ)]

theorem range_iota_x_eq_range_pinnedX_alg
    {K : Type} [Field K] [CharP K 2]
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    Set.range (fun c : K => ((ι (Sp.x 3 K γ c) : ↥(adjointGroup .F4 K)) : ModGL .F4 K))
      = Set.range (pinnedX .F4 K (c3ToF4 γ)) := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c,
      (iota_x_eq_pinnedX_alg ι hι hγ c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c, ?_⟩
    change ((ι (Sp.x 3 K γ (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c)) :
      ↥(adjointGroup .F4 K)) : ModGL .F4 K) = pinnedX .F4 K (c3ToF4 γ) c
    rw [iota_x_eq_pinnedX_alg ι hι hγ (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) *
        c),
      show ((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K)
          * (((rootOperatorFamily .F4).pinnedFamilySign (c3ToF4 γ) : K) * c) = c from by
        rw [← mul_assoc, (rootOperatorFamily .F4).pinnedFamilySign_mul_self K (c3ToF4 γ), one_mul]]

theorem map_c3RootSubgroup_eq_rootSubgroup_alg
    {K : Type} [Field K] [CharP K 2]
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) :
    (CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ).map
        ((adjointGroup .F4 K).subtype.comp ι)
      = CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ) := by
  rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, MonoidHom.map_closure,
    CFSG.Blueprint.Chevalley.rootSubgroup]
  congr 1
  rw [← Set.range_comp]
  exact range_iota_x_eq_range_pinnedX_alg ι hι hγ

theorem range_eq_rootSpan_alg
    {K : Type} [Field K] [CharP K 2]
    (ι : ↥(StatedSp 3 K) →* ↥(adjointGroup .F4 K))
    (hι : ∀ γ c, ι (Sp.x 3 K γ c) = Adjoint.f4Par K (c3ToF4 γ) c) :
    MonoidHom.range ((adjointGroup .F4 K).subtype.comp ι)
      = CFSG.Blueprint.Chevalley.rootSpan .F4 K C3Range.c3RootSet := by
  let f : ↥(StatedSp 3 K) →* ModGL .F4 K := (adjointGroup .F4 K).subtype.comp ι
  have key : MonoidHom.range f
      = ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
          CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ) := by
    rw [MonoidHom.range_eq_map, ← iSup_c3RootSubgroup_eq_top_alg K]
    simp only [Subgroup.map_iSup]
    exact iSup_congr fun γ => iSup_congr fun hγ =>
      map_c3RootSubgroup_eq_rootSubgroup_alg ι hι hγ
  rw [key]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    exact le_iSup₂_of_le (f := fun α (_ : α ∈ CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSet) =>
        CFSG.Blueprint.Chevalley.rootSubgroup .F4 K α) (c3ToF4 γ) ⟨γ, hγ, rfl⟩ le_rfl
  · rw [CFSG.Blueprint.Chevalley.rootSpan]
    refine iSup₂_le fun α hα => ?_
    obtain ⟨γ, hγ, rfl⟩ := hα
    exact le_iSup₂_of_le (f := fun γ (_ : γ ∈ roots (isFiniteType_cartanC 3) ∅) =>
        CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (c3ToF4 γ)) γ hγ le_rfl

end GeneralField

section Graph

abbrev Idx := {k : ℕ // k ≠ 0}

instance : Nonempty Idx := ⟨⟨1, one_ne_zero⟩⟩

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

instance (k : Idx) : Finite (TauCeti.frobeniusFixedSubfield Ω 2 k.1) :=
  TauCeti.finite_frobeniusFixedSubfield Ω 2 k.1 k.2

instance (k : Idx) : CharP (TauCeti.frobeniusFixedSubfield Ω 2 k.1) 2 :=
  Subfield.charP (TauCeti.frobeniusFixedSubfield Ω 2 k.1) 2

noncomputable def incl (k : Idx) : ↥(TauCeti.frobeniusFixedSubfield Ω 2 k.1) →+* Ω :=
    (TauCeti.frobeniusFixedSubfield Ω 2 k.1).subtype

noncomputable def sMap (k : Idx) : ↥(StatedSp 3 (TauCeti.frobeniusFixedSubfield Ω 2 k.1)) →*
    ↥(StatedSp 3 Ω) :=
  statedSpMap (incl Ω k) 3

noncomputable def jMap
    (k : Idx) : ↥(adjointGroup .F4 (TauCeti.frobeniusFixedSubfield Ω 2 k.1)) →* ↥(adjointGroup .F4
        Ω) :=
  j (τ := .F4) (incl Ω k)

end Graph
end CFSG.StandardType.F4ExplicitPos.C3Algebraic
end

end
