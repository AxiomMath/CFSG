module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PinnedBaseChange
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.C3AlgebraicPart2

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.RationalB2

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType
  CFSG.LieType.Chevalley CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.Timmesfeld.LieEmbed CFSG.SeitzReduction.F4Pilot
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.RootBaseChange
  CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  CFSG.HardMathSupport.Timmesfeld.LangTorus

open CFSG.ClassicalInvolution.Models.SymplecticPairs (spEmbed spEmbed_injective)

open CFSG.StandardType.F4ExplicitPos.C3Range (c3RootSubgroup c3RootSubgroup_eq_rootGroup)

open scoped Matrix

section Algebraic

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

noncomputable def c2RootSubgroup {K : Type} [Field K] (v : Fin 2 → ℤ) :
    Subgroup ↥(StatedSp 2 K) :=
  Subgroup.closure (Set.range (Sp.x 2 K v))

theorem c2RootSubgroup_eq_rootGroup_alg {K : Type} [Field K] {v : Fin 2 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    c2RootSubgroup (K := K) v =
      (CFSG.LieType.Universal.Symplectic.rootDatum 2 K).rootGroup v := by
  have hp := Sp.isParametrization (n := 2) (F := K) v (by rwa [Sp.Φ_roots])
  rw [c2RootSubgroup]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact (hp.1 _).2 ⟨c, rfl⟩
  · intro g hg
    obtain ⟨c, rfl⟩ := (hp.1 g).1 hg
    exact Subgroup.subset_closure ⟨c, rfl⟩

theorem iSup_c2RootSubgroup_eq_top_alg (K : Type) [Field K] :
    (⨆ v ∈ roots (isFiniteType_cartanC 2) ∅, c2RootSubgroup (K := K) v) = ⊤ := by
  rw [show (⨆ v ∈ roots (isFiniteType_cartanC 2) ∅, c2RootSubgroup (K := K) v)
      = ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅,
          (CFSG.LieType.Universal.Symplectic.rootDatum 2 K).rootGroup v from
    iSup_congr fun v => iSup_congr fun hv => c2RootSubgroup_eq_rootGroup_alg (K := K) hv]
  exact (CFSG.LieType.Universal.Symplectic.isCTGroupDatum 2 K).iSup_eq_top

theorem hom_ext_x2_alg {K H : Type} [Field K] [CharP K 2] [Group H]
    {Ψ Ψ' : ↥(StatedSp 2 K) →* H}
    (h : ∀ {v : Fin 2 → ℤ}, v ∈ roots (isFiniteType_cartanC 2) ∅ →
      ∀ c, Ψ (Sp.x 2 K v c) = Ψ' (Sp.x 2 K v c)) : Ψ = Ψ' := by
  ext g
  change g ∈ MonoidHom.eqLocus Ψ Ψ'
  have hg : g ∈ ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅, c2RootSubgroup (K := K) v := by
    rw [iSup_c2RootSubgroup_eq_top_alg (K := K)]
    exact Subgroup.mem_top g
  have hle : (⨆ v ∈ roots (isFiniteType_cartanC 2) ∅, c2RootSubgroup (K := K) v) ≤
      MonoidHom.eqLocus Ψ Ψ' :=
    iSup₂_le fun v hv => by
      rw [c2RootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact h (v := v) hv c
  exact hle hg

noncomputable def iOmegaB2 :
    ↥(StatedSp 2 Ω) →* ↥(adjointGroup .F4 Ω) :=
  (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω).comp
    (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2))

theorem iOmegaB2_apply
    (g : ↥(StatedSp 2 Ω)) :
    iOmegaB2 Ω g =
      CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω
        (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2) g) := rfl

theorem iOmegaB2_injective :
    Function.Injective (iOmegaB2 Ω) :=
  (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_injective Ω).comp
    (spEmbed_injective (Fin.succ_injective 2))

theorem iOmegaB2_x
    {v : Fin 2 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) (c : Ω) :
    iOmegaB2 Ω (Sp.x 2 Ω v c) = Adjoint.f4Par Ω (c2ToF4 v) c := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hv
  rw [iOmegaB2_apply, Sp.x_eq hr, spEmbed_elt, ← Sp.x_eq (stdVec_succIdx_eq hr),
    CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega_x, ← c2ToF4_apply]

theorem map_iOmegaB2_rootGroup
    {v : Fin 2 → ℤ}
    (hv : v ∈ roots (isFiniteType_cartanC 2) ∅) :
    ((Symplectic.rootGroup 2 Ω v).map (iOmegaB2 Ω)).map (adjointGroup .F4 Ω).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω (c2ToF4 v) := by
  have hcomp : (adjointGroup .F4 Ω).subtype.comp (iOmegaB2 Ω)
      = ((adjointGroup .F4 Ω).subtype.comp (C3Algebraic.iOmega Ω)).comp
          (spEmbed (Fin.succ : Fin 2 → Fin 3) (Fin.succ_injective 2)) := rfl
  have hroot : Symplectic.rootGroup 3 Ω (shiftC2 v)
      = c3RootSubgroup (K := Ω) (shiftC2 v) :=
    (CFSG.StandardType.F4ExplicitPos.C3Algebraic.c3RootSubgroup_eq_rootGroup_alg (K := Ω)
      (shiftC2_mem_roots hv)).symm
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, map_spEmbed_rootGroup hv, hroot,
    CFSG.StandardType.F4ExplicitPos.C3Algebraic.map_c3RootSubgroup_eq_rootSubgroup_alg
      (CFSG.StandardType.F4ExplicitPos.C3Algebraic.iOmega Ω)
      (fun γ c => C3Algebraic.iOmega_x Ω γ c) (shiftC2_mem_roots hv),
    ← c2ToF4_apply]

theorem range_iOmegaB2 :
    ((iOmegaB2 Ω).range).map (adjointGroup .F4 Ω).subtype
      = rootSpan .F4 Ω b2LeviRoots := by
  have hgen : ((iOmegaB2 Ω).range).map (adjointGroup .F4 Ω).subtype
      = ⨆ v ∈ roots (isFiniteType_cartanC 2) ∅,
          ((Symplectic.rootGroup 2 Ω v).map (iOmegaB2 Ω)).map
            (adjointGroup .F4 Ω).subtype := by
    rw [MonoidHom.range_eq_map, Subgroup.map_map,
      ← (Symplectic.isCTGroupDatum 2 Ω).iSup_eq_top]
    simp only [Subgroup.map_iSup, Subgroup.map_map]
  rw [hgen, rootSpan]
  refine le_antisymm (iSup₂_le fun v hv => ?_) (iSup₂_le fun γ hγ => ?_)
  · rw [map_iOmegaB2_rootGroup (Ω := Ω) (v := v) (hv := hv)]
    exact le_iSup₂ (f := fun γ (_ : γ ∈ b2LeviRoots) =>
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 Ω γ) _ (c2ToF4_mem_b2LeviRoots hv)
  · obtain ⟨v, hv, rfl⟩ := exists_c2ToF4_eq_of_mem_b2LeviRoots hγ
    rw [← map_iOmegaB2_rootGroup (Ω := Ω) (v := v) (hv := hv)]
    exact le_iSup₂ (f := fun v (_ : v ∈ roots (isFiniteType_cartanC 2) ∅) =>
      ((Symplectic.rootGroup 2 Ω v).map (iOmegaB2 Ω)).map
        (adjointGroup .F4 Ω).subtype) v hv

theorem iOmegaB2_natural
    (Fr : Ω →+* Ω) :
    (j (τ := .F4) Fr).comp (iOmegaB2 Ω) = (iOmegaB2 Ω).comp (statedSpMap Fr 2) := by
  apply hom_ext_x2_alg (K := Ω)
  rintro v hv c
  simp only [MonoidHom.comp_apply]
  rw [iOmegaB2_x (Ω := Ω) (v := v) (hv := hv), statedSpMap_x,
    iOmegaB2_x (Ω := Ω) (v := v) (hv := hv)]
  exact map_j_xPar (τ := .F4) Fr (rootOperatorFamily .F4) (c2ToF4 v) c

end Algebraic

section FixedRange

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

noncomputable def conjIMB2
    (n : ModGL .F4 Ω) : ↥(StatedSp 2 Ω) →* ModGL .F4 Ω :=
  (MulAut.conj n).toMonoidHom.comp
    ((adjointGroup .F4 Ω).subtype.comp (iOmegaB2 Ω))

theorem conjIMB2_apply
    (n : ModGL .F4 Ω) (g : ↥(StatedSp 2 Ω)) :
    conjIMB2 Ω n g = n * (iOmegaB2 Ω g : ModGL .F4 Ω) * n⁻¹ := by
  change MulAut.conj n
      ((adjointGroup .F4 Ω).subtype (iOmegaB2 Ω g)) =
    n * (iOmegaB2 Ω g : ModGL .F4 Ω) * n⁻¹
  rw [MulAut.conj_apply]
  rfl

theorem conjIMB2_injective
    (n : ModGL .F4 Ω) :
    Function.Injective (conjIMB2 Ω n) :=
  (MulAut.conj n).injective.comp
    ((adjointGroup .F4 Ω).subtype_injective.comp (iOmegaB2_injective (Ω := Ω)))

end FixedRange
end CFSG.StandardType.F4ExplicitPos.RationalB2
end

end
