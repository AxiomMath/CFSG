module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpTorusAutGens
public import CFSG.LocalAnalysis.StandardType.GGQ2SignedPermMem
public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.StandardType CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
  {m : ℕ}

theorem exists_signedPerm_of_mem_torusAut [CharP K 2] (hζ : Function.Injective ζ)
    {X : Subgroup ↥(StatedSp m K)} {φ : PlaneRaw.V m ≃ₗ[ZMod 3] PlaneRaw.V m}
    (hφ : φ ∈ torusAut ζ m X) :
    ∃ (π : Equiv.Perm (Fin m)) (ε : Fin m → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ u i, φ u (π i) = ε i * u i := by
  classical
  rw [torusAut] at hφ
  obtain ⟨y, -, hy⟩ := hφ
  have hg : ∀ f : Fin m → Multiplicative (ZMod 3), ∃ f',
      y * spPlaneTorus m ζ f * y⁻¹ = spPlaneTorus m ζ f' := by
    intro f
    refine ⟨fun i => Multiplicative.ofAdd (φ (fun k => Multiplicative.toAdd (f k)) i), ?_⟩
    simpa [tau] using hy (fun k => Multiplicative.toAdd (f k))
  obtain ⟨π, ε, hε, hφ'⟩ :=
    TorC.exists_signedPerm_of_normalizes (F := K) (p := 3) Nat.prime_three (by norm_num) hζ y hg
  refine ⟨π, ε, hε, fun u i => ?_⟩
  have h1 : y * spPlaneTorus m ζ (fun k => Multiplicative.ofAdd (u k)) * y⁻¹ =
      spPlaneTorus m ζ (fun k => Multiplicative.ofAdd (φ u k)) := by
    simpa [tau] using hy u
  have h2 := hφ' (fun k => Multiplicative.ofAdd (u k))
    (fun k => Multiplicative.ofAdd (φ u k)) h1 i
  simpa using h2

theorem torusAut_subset_signedPermGroup [CharP K 2] (hζ : Function.Injective ζ)
    (X : Subgroup ↥(StatedSp m K)) :
    torusAut ζ m X ⊆ ((PlaneRaw.signedPermGroup m : Subgroup _) : Set _) := by
  intro φ hφ
  obtain ⟨π, ε, hε, h⟩ := exists_signedPerm_of_mem_torusAut (X := X) hζ hφ
  exact PlaneRaw.mem_signedPermGroup_of_apply φ π ε hε h

theorem spAmbientTorusAut_holds : SpAmbientTorusAut := by
  intro K _ _ _ ζ m hK hζ
  exact (torusAut_subset_signedPermGroup hζ ⊤).antisymm
    (signedPermGroup_subset_torusAut_top hK hζ)

end CFSG.StandardType.GGQ2Frame.SpBlocks
