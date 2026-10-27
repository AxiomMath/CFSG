module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeEnvelopePieces
import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore
open CFSG.Open (StatedLieTag)

section Torus

variable {τ : Tag}

theorem rckSU3_rootVal_pow
    {z : ModGL τ GGL} (hz : z ∈ torusGroup τ GGL) {p : ℕ} (hzp : z ^ p = 1)
    (γ : Fin τ.rank → ℤ) : rckRootVal z γ ^ p = 1 := by
  change rootChar (rckTorusCoord z) γ ^ p = 1
  exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one (rck_coord_pow hz hzp) γ

theorem rckSU3_rootVal_inv_mul
    {z₁ z₂ : ModGL τ GGL} (h₁ : z₁ ∈ torusGroup τ GGL) (h₂ : z₂ ∈ torusGroup τ GGL)
    (γ : Fin τ.rank → ℤ) :
    rckRootVal (z₁⁻¹ * z₂) γ = (rckRootVal z₁ γ)⁻¹ * rckRootVal z₂ γ := by
  have hmem : z₁⁻¹ * z₂ ∈ torusGroup τ GGL := mul_mem (inv_mem h₁) h₂
  have hcoord : rckTorusCoord (z₁⁻¹ * z₂) =
      (rckTorusCoord z₁)⁻¹ * rckTorusCoord z₂ := by
    apply rootDiagUnit_injective
    rw [rck_rootDiagUnit_coord hmem, rootDiagUnit_mul, ← rootDiagUnit_inv,
      rck_rootDiagUnit_coord h₁, rck_rootDiagUnit_coord h₂]
  change rootChar (rckTorusCoord (z₁⁻¹ * z₂)) γ =
    (rootChar (rckTorusCoord z₁) γ)⁻¹ * rootChar (rckTorusCoord z₂) γ
  rw [hcoord, CFSG.LieType.Chevalley.rootChar_mul_tuple,
    CFSG.LieType.Chevalley.rootChar_inv_apply]

theorem rckSU3_centralizes_rationalComponent
    {p₀ : ℕ} (S : LangSetup τ GGL p₀) (a : Fin τ.rank → GGLˣ)
    (i : KernelComponent (rootCharHom a)) {z : ModGL τ GGL} (hz : z ∈ S.D.torus)
    (h1 : ∀ γ ∈ componentRoots (rootCharHom a) i, rckRootVal z γ = 1)
    {x : ModGL τ GGL} (hx : x ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i) :
    z * x * z⁻¹ = x := by
  have hztg : z ∈ torusGroup τ GGL :=
    (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1 hz).1
  have hcoord : rootDiagUnit τ (rckTorusCoord z) = z := rck_rootDiagUnit_coord hztg
  have hmem : rootDiagUnit τ (rckTorusCoord z) ∈ S.D.torus := by
    rw [hcoord]
    exact hz
  have hsub : rationalRoots S.ρ (rootCharHom a) i ⊆ rootCharKernel (rckTorusCoord z) := by
    rintro γ ⟨k, δ, hδ, rfl⟩
    have hker : ∀ k : ℕ, (S.ρ : (Fin τ.rank → ℤ) → _)^[k] δ ∈
        rootCharKernel (rckTorusCoord z) := by
      intro k
      induction k with
      | zero =>
          have hrδ : IsRoot τ δ := hδ.1.1
          exact ⟨hrδ, h1 δ hδ⟩
      | succ k ih =>
          obtain ⟨ihr, ihc⟩ := ih
          rw [Function.iterate_succ_apply']
          refine ⟨(S.frob.isRoot_iff _).2 ihr, ?_⟩
          rw [S.frob.rootChar_eq (rckTorusCoord z) hmem _ ihr, ihc, one_pow]
    exact hker k
  have hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      toralCentralizer τ GGL (rckTorusCoord z) := by
    rw [rationalComponent]
    exact le_trans (Subgroup.commutator_le_self (rationalSpan S.ρ S.Γ (rootCharHom a) i))
      (le_trans inf_le_left (le_trans (rootSpan_mono hsub)
        (rootSpan_rootCharKernel_le_toralCentralizer (rckTorusCoord z))))
  have hx_comm : rootDiagUnit τ (rckTorusCoord z) * x *
      (rootDiagUnit τ (rckTorusCoord z))⁻¹ = x :=
    (mem_toralCentralizer.1 (hle hx)).2
  rw [hcoord] at hx_comm
  exact hx_comm

end Torus

end CFSG.StandardType.RCKRP

end
