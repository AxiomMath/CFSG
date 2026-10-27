module

public import CFSG.RankThree.PartOne.S15K.PSylowSL
public import CFSG.RankThree.PartOne.KC.LinearCommutantBlocks

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial CFSG.RankThree.PartOne.KCLinComm CFSG.RankThree.PartOne.KCPrimary
open scoped _root_.Classical

variable {K : Type} [Field K] {n : ℕ} {x : Module.End K (Fin n → K)}

theorem psylowSub_blockImage [CharP K 2] {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hsq : Squarefree (minpoly K x)) (c : primaryFactors x) (hmult : ¬ p ∣ mult x c) :
    PSylowSub p (blockImage hsq c) := by
  have : CharP (Efac x c) 2 := charP_of_injective_algebraMap (algebraMap K (Efac x c)).injective 2
  have hζ' : IsPrimitiveRoot (algebraMap K (Efac x c) ζ) p :=
    hζ.map_of_injective (algebraMap K (Efac x c)).injective
  have hSL := psylowSub_specialLinear hp hζ' hmult
  let Θ := (blockTheta hsq).comp (blockEmbed (Efac x) (mult x) c)
  have hΘ : Function.Injective Θ := (blockTheta_injective hsq).comp (blockEmbed_injective c)
  have h1 := hSL.map Θ hΘ
  have heq : (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin (mult x c)) (Efac x c))).map Θ =
      blockImage hsq c := by
    ext g
    rw [mem_blockImage]
    constructor
    · rintro ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, trivial, rfl⟩
  rwa [heq] at h1

end CFSG.RankThree.PartOne.S15K
