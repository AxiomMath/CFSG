module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuMinimal
public import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.CaseAnalysis
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallL4Label
import CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar.TopRank

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Finset
open CFSG.LieType.SpecialLinear.ExteriorModel
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.HardMathSupport.Meierfrankenfeld.PSUScalar
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
open scoped MonoidAlgebra TensorProduct

theorem w135c2_psu_clauses {m f : ℕ} (hm : 3 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (SU (unitaryInvolution K 2 f) m) W) [ρ.IsIrreducible]
    {ε : Fin f → Finset (Fin m)} (hε : HasUnitaryLabel (by omega : 2 ≤ m) hK ρ ε) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) (SU (unitaryInvolution K 2 f) m))
      ρ.asModule) = 2 ^ s) (hs : 0 < s) (ht : ∃ r, ε r ≠ ∅) :
    f ≤ s * (univ.filter fun r => ε r ≠ ∅).card ∧
      ((univ.filter fun r => ε r ≠ ∅).card ≤ 2 → (∃ r, (ε r).image labelStar ≠ ε r) →
        2 * f ≤ s) ∧
      (∀ y : SU (unitaryInvolution K 2 f) m, y * y = 1 → y ≠ 1 →
        s * movedTop (by omega : 2 ≤ m) ε ≤
          2 * finrank (ZMod 2) (LinearMap.range (ρ y - 1))) ∧
      (∃ (k : Type) (_ : Field k) (_ : CharP k 2),
        Nat.card W = 2 ^ (s * finrank k (BModel k ε))) := by
  classical
  have hn : 0 < m := by omega
  have h0 := w135c2_psu_zero_not_mem_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε
  obtain ⟨k₀, hk₀, φ₀, hpow, -⟩ :=
    w135c2_psu_char_of_hasUnitaryLabel (by omega : 2 ≤ m) hK ρ hε hE
  refine ⟨le_mul_card_of_chiEps_pow hK hn φ₀ h0 ht hs hpow,
    fun hcard hns => two_mul_le_of_chiEps_pow hK hn φ₀ h0 hs hpow hcard hns, ?_, ?_⟩
  · obtain ⟨k, hk, hchar, halg, φ₁, ζ, hζ, y₀, χ, μ, htype, -, -, β, hβ⟩ := hε
    intro y hy hy1
    have hrank := finrank_range_sub_one_eq_mul ρ hE k y
    have hrankβ := finrank_range_sub_one_eq_of_equiv
      (τ := CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ))
      (τ' := suRep φ₁ m ε) β hβ y
    obtain ⟨π, hπ, hπ01, hrankπ⟩ :=
      exists_perm_finrank_range_suRep_sub_one φ₁ (by omega : 2 ≤ m) ε hy hy1
    have htop : movedTop (by omega : 2 ≤ m) ε ≤
        2 * finrank k (LinearMap.range (bRep ε (fun _ => permSL (k := k) π) - 1)) := by
      unfold movedTop
      convert card_moved_top_le (k := k) ε (by omega : 2 ≤ m) π hπ hπ01
    rw [hrankπ, ← hrankβ] at htop
    rw [hrank]
    calc s * movedTop (by omega : 2 ≤ m) ε
        ≤ s * (2 * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) :=
          Nat.mul_le_mul_left s htop
      _ = 2 * (s * finrank k (LinearMap.range
            (CFSG.Theory.Representation.extendScalars k (CFSG.endFieldRep ρ) y - 1))) := by
          ring
  · obtain ⟨k, hk, hchar, halg, φ₁, ζ, hζ, y₀, χ, μ, htype, -, -, β, hβ⟩ := hε
    refine ⟨k, hk, hchar, ?_⟩
    have h1 := card_eq_pow_finrank_extendScalars (ρ := ρ) k
    rw [hE, ← pow_mul, β.finrank_eq] at h1
    exact h1

end CFSG.LocalAnalysis.WeakClosure81
