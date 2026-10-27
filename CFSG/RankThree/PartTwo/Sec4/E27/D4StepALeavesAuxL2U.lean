module

public import CFSG.RankThree.PartTwo.Sec4.E27.D4StepALeavesAuxL1AlgU

public section

namespace CFSG.RankThree.PartTwo.Sec4.E27

open CFSG.RankThree.Classical2 (unitarySet)
open CFSG.OddStandard.GH71.S55 CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartTwo.KFacts

variable {ℓ f : ℕ} [Fact ℓ.Prime] {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω ℓ]

theorem card_subgroup_unitarySet (hf : 1 ≤ f) (U : Subgroup (GL (Fin 3) Ω))
    (hU : (U : Set (GL (Fin 3) Ω)) = unitarySet (ℓ ^ f) 3) :
    Nat.card U = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := by
  classical
  have hF := unitaryFieldData_unitField (Ω := Ω) (ℓ := ℓ) hf
  let φ : unitarySU ℓ f (unitField Ω ℓ f) 3 →* GL (Fin 3) Ω :=
    (unitGLEmb ℓ f Ω).comp (unitarySU ℓ f (unitField Ω ℓ f) 3).subtype
  have hφinj : Function.Injective φ := fun A B h => Subtype.ext (unitGLEmb_injective h)
  have hφrange : ∀ Y : GL (Fin 3) Ω, Y ∈ φ.range ↔ Y ∈ unitarySet (ℓ ^ f) 3 := by
    intro Y
    constructor
    · rintro ⟨B, rfl⟩
      exact unitGLEmb_mem_unitarySet hf B.2
    · intro hY
      obtain ⟨B, hB, hBY⟩ := exists_unitGLEmb_of_mem_unitarySet hf hY
      exact ⟨⟨B, hB⟩, hBY⟩
  have hUφ : U = φ.range := Subgroup.ext fun Y => by
    rw [← SetLike.mem_coe, hU]
    exact (hφrange Y).symm
  rw [hUφ, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv]
  exact card_unitarySU_three hF

end CFSG.RankThree.PartTwo.Sec4.E27
