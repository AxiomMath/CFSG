module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalA
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalAMoves
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalB
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalTorus

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem triD4LineX_moves_line (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3)
    (h3 : 3 ∣ Nat.card k - 1) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x ∈
      Subgroup.center (TriD4LineX k K)) :
    ∀ e ∈ E, e ∉ Subgroup.zpowers z₀ →
      ∃ n : TriD4LineX k K, (∀ e' ∈ E, n * e' * n⁻¹ ∈ E) ∧ n * e * n⁻¹ ∉ Subgroup.zpowers e ∧
        n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ ∈ E := by
  intro e he hez
  obtain ⟨n, hnE, hnmove, hncomm⟩ : ∃ n : TriD4LineX k K, (∀ e' ∈ E, n * e' * n⁻¹ ∈ E) ∧
      (∀ e ∈ E, e ∉ Subgroup.zpowers z₀ → n * e * n⁻¹ ∉ Subgroup.zpowers e) ∧
      n * (x * triD4LineSigma k K σ n * x⁻¹)⁻¹ ∈ E := by
    by_cases hEN : E ≤ triD4LineN0 k K
    · exact triD4LineX_moves_line_of_le_N0 k K σ z₀ hz₀ hzc E hE hEc hzE x hx hx3 hEN
    · exact triD4LineX_moves_line_of_not_le_N0 k K hdeg h3 σ hσ z₀ hz₀ hzc E hE hEc hzE x hx
        hEN
  exact ⟨n, hnE, hnmove e he hez, hncomm⟩

theorem triD4LineX_fix_or_torus (k K : Type) [Field k] [Field K] [Algebra k K]
    [Finite K] (hdeg : Module.finrank k K = 3)
    (h3 : 3 ∣ Nat.card k - 1) (σ : K ≃ₐ[k] K) (hσ : orderOf σ = 3)
    (z₀ : TriD4LineX k K) (hz₀ : orderOf z₀ = 3) (hzc : z₀ ∈ Subgroup.center (TriD4LineX k K))
    (E : Subgroup (TriD4LineX k K)) (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hzE : z₀ ∈ E) (x : TriD4LineX k K) (hx : ∀ e ∈ E, x * triD4LineSigma k K σ e * x⁻¹ = e)
    (hx3 : x * triD4LineSigma k K σ x * triD4LineSigma k K (σ ^ 2) x = 1) :
    (∃ e' ∈ E, ∀ y ∈ triD4LineN0 k K, e' * x * triD4LineSigma k K σ y * x⁻¹ * e'⁻¹ = y) ∨
    ∃ e₁ ∈ E, e₁ ∉ Subgroup.zpowers z₀ ∧ ∃ T : Subgroup (TriD4LineX k K),
      T ≤ Subgroup.centralizer {e₁} ∧
      Nonempty (T ≃* Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1)) ×
        Multiplicative (ZMod (Nat.card k ^ 2 + Nat.card k + 1))) := by
  by_cases hEN : E ≤ triD4LineN0 k K
  · exact Or.inl (triD4LineX_fix_of_le_N0 k K hdeg σ hσ z₀ hz₀ hzc E hE hEc hzE x hx hx3 hEN)
  · right
    obtain ⟨e₁, he₁E, he₁N⟩ := SetLike.not_le_iff_exists.mp hEN
    have hz₀N : z₀ ∈ triD4LineN0 k K := by
      obtain ⟨ζ, -, -, h, hζ⟩ := triD4Line_eq_mk_of_mem_center k K h3 hzc hz₀
      exact (mem_triD4LineN0_iff k K z₀).2 ⟨_, h, hζ⟩
    refine ⟨e₁, he₁E, fun hz => he₁N (Subgroup.zpowers_le.mpr hz₀N hz), ?_⟩
    exact triD4Line_exists_torus k K hdeg e₁ (hE.2 e₁ he₁E) he₁N

end CFSG.StandardType
