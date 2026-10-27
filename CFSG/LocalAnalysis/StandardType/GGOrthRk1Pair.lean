module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs
import CFSG.LocalAnalysis.StandardType.GGOrthRk1PairBlock
import CFSG.GH74.L5U5.IdentUnitary

public section

open Module Multiplicative QuadraticMap Matrix

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ClassicalInvolution.Phan

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem tbjOm_pair_model_le {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r) (hr : 3 ≤ r)
    (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ W : Subgroup (V ≃ₗ[K] V), W ≤ orthDerived Q ⊓ Subgroup.centralizer
        ((Δ.reflFixed i j ⊓ Δ.reflFixed j k : Subgroup (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) ∧
      UnitaryBlockStandardPair K' 2 f W (Δ.rankOne i j) (Δ.rankOne j k) := by
  obtain ⟨θ, hθ, hθΩ, hU, hV, hC⟩ := Δ.exists_pair_blocks hp2 hAΩ hr hpq hfix f hf K' hK' i j k hij hjk
    hik
  refine ⟨θ.range, le_inf hθΩ hC, ?_⟩
  have hker : θ.ker ≤ Subgroup.center (Su K' 2 f 3) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθ]
    exact bot_le
  exact CFSG.GH74.L5U5.unitaryBlockStandardPair_of_blocks hker hU hV

theorem tbjOm_pair_model {Q : QuadraticForm K V} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) {r : ℕ} (Δ : TBJOmData Q p A r) (hr : 3 ≤ r)
    (hpq : p ∣ Nat.card K + 1)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : ℕ) (hf : Nat.card K = 2 ^ f) (K' : Type) [Field K'] [Finite K'] [CharP K' 2]
    (hK' : Nat.card K' = (2 ^ f) ^ 2) (i j k : Fin r) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ W : Subgroup (V ≃ₗ[K] V),
      UnitaryBlockStandardPair K' 2 f W (Δ.rankOne i j) (Δ.rankOne j k) := by
  obtain ⟨W, _, hW⟩ := tbjOm_pair_model_le hp2 hAΩ Δ hr hpq hfix f hf K' hK' i j k hij hjk hik
  exact ⟨W, hW⟩

end OrthTorus

end CFSG.StandardType

end
