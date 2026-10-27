module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3AlgebraicPart3

@[expose] public section

public noncomputable section

namespace CFSG.StandardType.F4ExplicitPos.B3Naturality

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal.Symplectic CFSG.Open CFSG.SeitzReduction.F4Pilot
      CFSG.StandardType.F4ExplicitPos
  CFSG.StandardType.F4ExplicitPos.BaseChange CFSG.StandardType.F4ExplicitPos.PinnedBaseChange
  _root_.CFSG.StandardType.F4ExplicitPos.C3Algebraic CFSG.Timmesfeld.LieEmbed

theorem hom_ext_x3_alg_b3 {K H : Type} [Field K] [CharP K 2] [Group H]
    {Ψ Ψ' : ↥(StatedSp 3 K) →* H}
    (h : ∀ (γ : Fin 3 → ℤ), γ ∈ roots (isFiniteType_cartanC 3) ∅ → ∀ c,
      Ψ (Sp.x 3 K γ c) = Ψ' (Sp.x 3 K γ c)) : Ψ = Ψ' := by
  ext g
  change g ∈ MonoidHom.eqLocus Ψ Ψ'
  have hg : g ∈ ⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ := by
    rw [CFSG.StandardType.F4ExplicitPos.C3Algebraic.iSup_c3RootSubgroup_eq_top_alg (K := K)]
    exact Subgroup.mem_top g
  have hle : (⨆ γ ∈ roots (isFiniteType_cartanC 3) ∅,
      CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup (K := K) γ) ≤ MonoidHom.eqLocus Ψ Ψ' :=
    iSup₂_le fun γ hγ => by
      rw [CFSG.StandardType.F4ExplicitPos.C3Range.c3RootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      exact h γ hγ c
  exact hle hg

variable (Ω : Type) [Field Ω] [CharP Ω 2] [Algebra (ZMod 2) Ω] [Algebra.IsAlgebraic (ZMod 2) Ω]

theorem iBΩ_natural_modGL_apply_root
    (Fr : Ω →+* Ω)
    {γ : Fin 3 → ℤ} (hγ : γ ∈ roots (isFiniteType_cartanC 3) ∅) (c : Ω) :
    bcGL (τ := .F4) Fr
        (((CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω) (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) :
          ModGL .F4 Ω) =
      (((CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω)
          (statedSpMap Fr 3 (Sp.x 3 Ω γ c)) : adjointGroup .F4 Ω) : ModGL .F4 Ω) := by
  have hx : (((B3Algebraic.iBΩ Ω) (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) :
        ModGL .F4 Ω) =
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1) :=
    CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_x_pinnedX Ω hγ c
  have hx' : (((B3Algebraic.iBΩ Ω) (Sp.x 3 Ω γ (Fr c)) : adjointGroup .F4 Ω) :
        ModGL .F4 Ω) =
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        ((Fr c) ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1) :=
    CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ_x_pinnedX Ω hγ (Fr c)
  have hbc : bcGL (τ := .F4) Fr
        (pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
          (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1)) =
      pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
        (Fr (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1)) :=
    CFSG.StandardType.F4ExplicitPos.PinnedBaseChange.bcGL_pinnedX (τ := .F4) (R := Ω) (S := Ω) Fr
      (F4.dualRoot (c3ToF4 γ)) (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1)
  rw [statedSpMap_x]
  calc bcGL (τ := .F4) Fr
        (((CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω) (Sp.x 3 Ω γ c) : adjointGroup .F4 Ω) :
          ModGL .F4 Ω)
      = bcGL (τ := .F4) Fr (pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
          (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1)) := by rw [hx]
    _ = pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
          (Fr (c ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1)) := hbc
    _ = pinnedX .F4 Ω (F4.dualRoot (c3ToF4 γ))
          ((Fr c) ^ F4.exponent (pinnedData F4.tag (c3ToF4 γ)).1) := by
          rw [RingHom.map_pow]
    _ = (((B3Algebraic.iBΩ Ω) (Sp.x 3 Ω γ (Fr c)) : adjointGroup .F4 Ω) :
          ModGL .F4 Ω) := by rw [← hx']

theorem iBΩ_natural
    (Fr : Ω →+* Ω) :
    (j (τ := .F4) Fr).comp (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω) =
      (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω).comp (statedSpMap Fr 3) := by
  apply hom_ext_x3_alg_b3 (K := Ω)
  intro γ hγ c
  refine Subtype.ext ?_
  simp only [MonoidHom.comp_apply]
  rw [j_apply]
  exact iBΩ_natural_modGL_apply_root Ω Fr hγ c

theorem iBΩ_natural_apply
    (Fr : Ω →+* Ω) (g : ↥(StatedSp 3 Ω)) :
    j (τ := .F4) Fr (CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω g) =
      CFSG.StandardType.F4ExplicitPos.B3Algebraic.iBΩ Ω (statedSpMap Fr 3 g) :=
  DFunLike.congr_fun (iBΩ_natural Ω Fr) g

end CFSG.StandardType.F4ExplicitPos.B3Naturality

end

end
