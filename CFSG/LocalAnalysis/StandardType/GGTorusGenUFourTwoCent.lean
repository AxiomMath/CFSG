module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenUFourTwoFrame
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkDiag

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial

private lemma pow_three_eq_one_of_diag_suFourTwo {K : Type} [Field K]
    (h : UnitaryFieldData 2 1 K) {s : ↥(unitarySU 2 1 K 4)} {v : Fin 4 → K}
    (hs : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v) : s ^ 3 = 1 := by
  refine CFSG.StandardType.LineU.pow_eq_one_of_diagSU (n := 1) (d := 4) (p := 3) hs ?_
  intro i
  have hgram := ((mem_unitarySU_iff h).mp s.2).2
  rw [hs, Matrix.diagonal_map (map_zero h.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hgram
  have h1 := congrFun (congrFun hgram i) i
  simp only [Matrix.diagonal_apply_eq] at h1
  rw [UnitaryFieldData.bar_apply] at h1
  norm_num at h1
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
  exact h1

private lemma commute_diag_suFourTwo {K : Type} [Field K] {s s' : ↥(unitarySU 2 1 K 4)}
    {v v' : Fin 4 → K}
    (hs : ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v)
    (hs' : ((s' : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v') :
    s * s' = s' * s := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hs, hs']
  exact (Matrix.commute_diagonal v v').eq

theorem ggTorusCentSC_psuFourTwo {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    GGTorusCentSC 3 (LargeEvenProj (LargeEvenSUGroup (Fin 4) K (2 ^ 1))) := by
  intro E hE h3 hsc c hc hcp
  obtain ⟨φ, hφ, hdiag⟩ := exists_model_diag_psuFourTwo hK hE
  have hpow : ∀ s : ↥(unitarySU 2 1 K 4), (∃ v : Fin 4 → K,
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v) → s ^ 3 = 1 := by
    rintro s ⟨v, hs⟩
    exact pow_three_eq_one_of_diag_suFourTwo hφ.field hs
  have hmem : ∀ s : ↥(unitarySU 2 1 K 4), (∃ v : Fin 4 → K,
      ((s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = diagonal v) → φ s ∈ E := by
    rintro s ⟨v, hs⟩
    refine hsc (φ s) (fun e he => ?_) ?_
    · obtain ⟨s', ⟨v', hs'⟩, rfl⟩ := hdiag e he
      rw [← map_mul, ← map_mul]
      exact congrArg φ (commute_diag_suFourTwo hs hs')
    · rw [← map_pow, hpow s ⟨v, hs⟩, map_one]
  obtain ⟨s₀, ⟨v₀, hs₀⟩, hφs₀⟩ :=
    mem_diagImage_of_commute_pTorsion_coprime hφ Nat.prime_three (by norm_num) (by norm_num) c
      (fun s hs _ => hc (φ s) (hmem s hs))
  have hc3 : c ^ 3 = 1 := by
    rw [← hφs₀, ← map_pow, hpow s₀ ⟨v₀, hs₀⟩, map_one]
  exact hsc c hc hc3

end CFSG.StandardType
