module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotPerfectU

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
  CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

local instance twistedE6PilotPerfectVBasicNeZeroTw : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Data

@[expose] def vFixedRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![0, 0, 1, 1, 1, 0], ![0, 1, 0, 0, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 2, 1, 0],
    ![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 2, 2, 2, 1],
    ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1], ![0, -1, 0, 0, 0, 0]]

@[expose] def vPairRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![0, 0, 0, 1, 1, 0], ![0, 0, 0, 1, 1, 1], ![0, 1, 0, 1, 1, 0], ![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 2, 1]]

@[expose] def vReprRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [twistedE6ClassRootA, twistedE6ClassRootA', twistedE6ClassRootB]

@[expose] def vRootB1 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 1, 1, 0]

@[expose] def vRootB2 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 0, 1, 1, 1, 1]

@[expose] def vRootD1 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 1, 1, 1, 0, 0]

@[expose] def vRootD2 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 0, 0, 1, 1, 0]

@[expose] def vExp1 (α : Fin TwistTag.E6.tag.rank → ℤ) : ℤ := coPair TwistTag.E6.tag 1 α

theorem vFixedRoots_check : ∀ α ∈ vFixedRoots, twistedE6TwoRootB α = true ∧
    permLattice TwistTag.E6.perm α = α ∧ twistedE6ClassCentralB α vReprRoots = true := by
  decide +kernel

theorem vPairRoots_check : ∀ α ∈ vPairRoots, twistedE6TwoRootB α = true ∧
    permLattice TwistTag.E6.perm α ≠ α ∧ twistedE6ClassCentralB α vReprRoots = true ∧
      twistedE6ClassCentralB (permLattice TwistTag.E6.perm α) vReprRoots = true := by
  decide +kernel

@[expose] def vRootS1 : Fin TwistTag.E6.tag.rank → ℤ := ![0, 1, 1, 2, 1, 0]

@[expose] def vRootS2 : Fin TwistTag.E6.tag.rank → ℤ := ![1, 1, 1, 2, 1, 1]

theorem vTorusCheck : (∀ α ∈ vFixedRoots, GoodExp (vExp1 α) ∨ α = vRootS1 ∨ α = vRootS2 ∨
      α = twistedE6ClassRootB) ∧
    (∀ α ∈ vPairRoots, GoodExp (vExp1 α) ∨ α = twistedE6ClassRootA ∨ α = perfRoot011221 ∨
      α = twistedE6ClassRootU) := by
  decide +kernel

theorem vCommutator_check : vRootB1 + vRootB2 = twistedE6ClassRootB ∧ vRootB1 ∈ vFixedRoots ∧
    vRootB2 ∈ vFixedRoots ∧ twistedE6ClassRootB ∈ vFixedRoots ∧ vRootB1 ≠ vRootB2 ∧
    vRootD1 + vRootD2 = twistedE6ClassRootA ∧ vRootD1 ∈ vPairRoots ∧ vRootD2 ∈ vPairRoots ∧
    twistedE6ClassRootA ∈ vPairRoots ∧ vRootD1 ≠ vRootD2 ∧
    twistedE6TwoRootB (vRootD1 + permLattice TwistTag.E6.perm vRootD2) = false ∧
    vRootD1 + permLattice TwistTag.E6.perm vRootD2 ≠ 0 ∧
    twistedE6TwoRootB (permLattice TwistTag.E6.perm (vRootD1 + vRootD2) + vRootD1) = false ∧
    permLattice TwistTag.E6.perm (vRootD1 + vRootD2) + vRootD1 ≠ 0 ∧
    twistedE6TwoRootB (permLattice TwistTag.E6.perm (vRootD1 + vRootD2) + vRootD2) = false ∧
    permLattice TwistTag.E6.perm (vRootD1 + vRootD2) + vRootD2 ≠ 0 ∧
    Pi.single 1 1 = (![0, 1, 0, 0, 0, 0] : Fin TwistTag.E6.tag.rank → ℤ) ∧
    -Pi.single 1 1 = (![0, -1, 0, 0, 0, 0] : Fin TwistTag.E6.tag.rank → ℤ) := by
  decide +kernel

end Data


section Torus

variable {K : Type} [Field K]

theorem pinnedX_eq_rootDiagUnit_conj {α : Fin TwistTag.E6.tag.rank → ℤ}
    (hα : IsRoot TwistTag.E6.tag α) {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : rootChar b α ≠ 1)
    (c : K) :
    pinnedX TwistTag.E6.tag K α c = rootDiagUnit TwistTag.E6.tag b *
        pinnedX TwistTag.E6.tag K α (c * ((rootChar b α : K) - 1)⁻¹) *
          (rootDiagUnit TwistTag.E6.tag b)⁻¹ *
        (pinnedX TwistTag.E6.tag K α (c * ((rootChar b α : K) - 1)⁻¹))⁻¹ := by
  have hχ : (rootChar b α : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hb (Units.ext h)
  rw [rootDiagUnit_conj_pinnedX b hα, pinnedX_neg, ← pinnedX_add]
  congr 1
  field_simp
  ring

theorem twistedE6PairX_eq_rootDiagUnit_conj (σ : K →+* K) {δ : Fin TwistTag.E6.tag.rank → ℤ}
    (hδ : IsRoot TwistTag.E6.tag δ) {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hbδ : rootChar b δ ≠ 1)
    (hbρ : rootChar b (permLattice TwistTag.E6.perm δ) = Units.map σ.toMonoidHom (rootChar b δ))
    (s : K) :
    twistedE6PairX σ δ s = rootDiagUnit TwistTag.E6.tag b *
        twistedE6PairX σ δ (s * ((rootChar b δ : K) - 1)⁻¹) *
      (rootDiagUnit TwistTag.E6.tag b)⁻¹ *
        (twistedE6PairX σ δ (s * ((rootChar b δ : K) - 1)⁻¹))⁻¹ := by
  have hχ : (rootChar b δ : K) - 1 ≠ 0 := sub_ne_zero.2 fun h => hbδ (Units.ext h)
  have hρδ := hδ.permLattice TwistTag.E6.cartan_perm
  generalize ha : s * ((rootChar b δ : K) - 1)⁻¹ = a
  have hsa : (rootChar b δ : K) * a + -a = s := by
    rw [← ha]
    field_simp
    ring
  have hσa : σ ((rootChar b δ : K) * a) + -σ a = σ s := by
    rw [← hsa, map_add, map_neg]
  have hc1 := rootDiagUnit_conj_pinnedX b hδ a
  have hc2 : rootDiagUnit TwistTag.E6.tag b *
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a) *
        (rootDiagUnit TwistTag.E6.tag b)⁻¹ =
      pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)) := by
    rw [rootDiagUnit_conj_pinnedX b hρδ (σ a), hbρ, Units.coe_map, map_mul]
    rfl
  have hcomm := (commute_pinnedX_permLattice_twistedE6 (K := K) hδ (-a) (σ s)).eq
  unfold twistedE6PairX
  calc pinnedX TwistTag.E6.tag K δ s * pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ)
        (σ s)
      = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) * pinnedX TwistTag.E6.tag K δ (-a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s) := by
        rw [← pinnedX_add TwistTag.E6.tag K δ, hsa]
    _ = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ s) *
            pinnedX TwistTag.E6.tag K δ (-a) := by
        rw [mul_assoc, hcomm, ← mul_assoc]
    _ = pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a) *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)) *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (-σ a) *
              pinnedX TwistTag.E6.tag K δ (-a) := by
        rw [mul_assoc (pinnedX TwistTag.E6.tag K δ ((rootChar b δ : K) * a))
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ ((rootChar b δ : K) * a)))
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (-σ a)),
          ← pinnedX_add TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ), hσa]
    _ = (rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag K δ a *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹) *
          (rootDiagUnit TwistTag.E6.tag b *
            pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a) *
              (rootDiagUnit TwistTag.E6.tag b)⁻¹) *
          (pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a))⁻¹ *
            (pinnedX TwistTag.E6.tag K δ a)⁻¹ := by
        rw [hc1, hc2, pinnedX_neg, pinnedX_neg]
    _ = rootDiagUnit TwistTag.E6.tag b * (pinnedX TwistTag.E6.tag K δ a *
          pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a)) *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹ * (pinnedX TwistTag.E6.tag K δ a *
              pinnedX TwistTag.E6.tag K (permLattice TwistTag.E6.perm δ) (σ a))⁻¹ := by
        group

end Torus

end CFSG.SeitzReduction.TwistedE6Pilot
