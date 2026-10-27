module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixNsOmegaData

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem ggTorusLift_omegaPlusNs [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) (hm : 4 ≤ m) :
    GGTorusLift p 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) := by
  obtain ⟨τ, X, hτH, hτs, hinv, hXH, hX1, hX2, hτX⟩ := exists_omegaPlusNsTorus hp hp2 hpq hK hm
  exact ggTorusLift_of_matrixTorus hp hp2 τ hτH hτs hinv X hXH hX1 hX2 hτX

theorem ggTorusLift_omegaMinusNs [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) (hK : 4 ≤ Nat.card K) (hm : 4 ≤ m) (b c : K) :
    GGTorusLift p 3 (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
  obtain ⟨τ, X, hτH, hτs, hinv, hXH, hX1, hX2, hτX⟩ := exists_omegaPlusNsTorus hp hp2 hpq hK hm
  refine ggTorusLift_of_matrixTorus hp hp2 (blockInl.comp τ)
    (fun f => blockInl_mem_omegaMinus b c (hτH f))
    (fun f hf => hτs f (mem_scalars_of_blockInl hf)) ?_ (blockInl.comp X)
    (fun c' => blockInl_mem_omegaMinus b c (hXH c'))
    (fun h => hX1 (mem_scalars_of_blockInl h)) ?_ ?_
  · intro i j
    obtain ⟨w, hw, hw1, hw2⟩ := hinv i j
    refine ⟨blockInl w, blockInl_mem_omegaMinus b c hw, ?_, fun hji => ?_⟩
    · have h1 : torusBasis (blockInl.comp τ) i = blockInl (torusBasis τ i) := rfl
      rw [h1, ← map_inv blockInl w, ← map_mul, ← map_mul, hw1, map_inv]
    · have h1 : torusBasis (blockInl.comp τ) j = blockInl (torusBasis τ j) := rfl
      rw [h1, ← map_inv blockInl w, ← map_mul, ← map_mul, hw2 hji]
  · intro c'
    rw [MonoidHom.comp_apply, ← map_pow, hX2, map_one]
  · intro f c'
    obtain ⟨c'', hc⟩ := hτX f c'
    refine ⟨c'', ?_⟩
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
      ← map_mul, hc]

end TableBSymp

end CFSG.StandardType

end
