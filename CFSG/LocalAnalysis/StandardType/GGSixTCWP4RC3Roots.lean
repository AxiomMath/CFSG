
module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RC1
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RWeyl
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDual
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RConj
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDualFrob
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFive
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RDefs
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl
public import CFSG.LieType.Steinberg.Adjoint.Pairs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UE8Gen
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UGram

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section RankTwo

private theorem tch_G_bridge {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ)) (hΨ : Ψ.Finite) :
    Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun v i => (v i : ℚ)
  let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := g
      map_add' := by intro a b; funext i; simp [g]
      map_smul' := by intro a b; funext i; simp [g] }
  have hfinj : Function.Injective f := by
    intro a b h
    funext i
    have h' := congrFun h i
    exact Int.cast_injective h'
  have : Module.Finite ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Module.Finite.span_of_finite ℤ (hΨ.image f)
  have hmap : (Submodule.span ℤ Ψ).map f = Submodule.span ℤ (f '' Ψ) := by
    rw [Submodule.map_span]
  have heq : Module.finrank ℤ (Submodule.span ℤ Ψ) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfinj (Submodule.span ℤ Ψ))
  have hM : Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Submodule.finrank_span_eq_finrank_span ℤ ℚ (f '' Ψ)
  have hcomp : compRank Ψ = Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) := by
    rw [compRank]
    rfl
  rw [hcomp, hM]
  exact heq

private theorem tch_G_iform_zero_left {τ : Tag} (x : Fin τ.rank → ℤ) : iform 0 x = 0 := by
  simp [iform]

theorem tc3_compRank_two
    {Ψ : Set (Fin Tag.E8.rank → ℤ)} (hΨ : IsRootComponent Ψ) {a b : Fin Tag.E8.rank → ℤ}
    (ha : a ∈ Ψ) (hb : b ∈ Ψ) (hab : iform a b = -1) : 2 ≤ compRank Ψ := by
  have hfin : Ψ.Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E8).subset fun α hα => hΨ.isRoot α hα
  have haa : iform a a = 2 :=
    iform_self_eq_two_of_mem_e8 a (CFSG.Blueprint.Chevalley.mem_rootFinset.2 (hΨ.isRoot a ha))
  have hbb : iform b b = 2 :=
    iform_self_eq_two_of_mem_e8 b (CFSG.Blueprint.Chevalley.mem_rootFinset.2 (hΨ.isRoot b hb))
  have hba : iform b a = -1 := (CFSG.LieType.Steinberg.Adjoint.iform_comm b a).trans hab
  have hli : LinearIndependent ℤ ![a, b] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : iform (s • a + t • b) a = 0 := by
      rw [hst]
      exact tch_G_iform_zero_left a
    have h2 : iform (s • a + t • b) b = 0 := by
      rw [hst]
      exact tch_G_iform_zero_left b
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left, haa, hba] at h1
    rw [CFSG.LieType.Steinberg.Adjoint.iform_add_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left,
      CFSG.LieType.Steinberg.Adjoint.iform_smul_left, hab, hbb] at h2
    constructor <;> omega
  have : Module.Finite ℤ (Submodule.span ℤ Ψ) := Module.Finite.span_of_finite ℤ hfin
  have hmem : ∀ i : Fin 2, ![a, b] i ∈ Submodule.span ℤ Ψ := by
    intro i
    fin_cases i
    · exact Submodule.subset_span ha
    · exact Submodule.subset_span hb
  let w : Fin 2 → Submodule.span ℤ Ψ := fun i => ⟨![a, b] i, hmem i⟩
  have hw : LinearIndependent ℤ w := by
    apply LinearIndependent.of_comp (Submodule.span ℤ Ψ).subtype
    exact hli
  have hcard := hw.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  rw [← tch_G_bridge (τ := Tag.E8) Ψ hfin]
  exact hcard

end RankTwo

end CFSG.StandardType.TableCRes

end
