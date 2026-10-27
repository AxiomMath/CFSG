module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGTwo
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGDet
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockGSupp

public section

open Module Multiplicative Polynomial

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

theorem TBJOmData.exists_mem_specialBlock_conj (Δ : TBJOmData Q p A r)
    {f₀ : Fin r → Multiplicative (ZMod p)} (hy : OddOrderIsometry Q p (Δ.τ f₀)) {h : K[X]}
    (hh : h ∈ primaryFactors (Δ.τ f₀).toLinearMap) {i k : Fin r}
    (hi : Δ.F.U i ≤ orbitSpace (Δ.τ f₀).toLinearMap h)
    (hk : Δ.F.U k ≤ orbitSpace (Δ.τ f₀).toLinearMap h) {w : V ≃ₗ[K] V} (hw : w ∈ orthDerived Q)
    (hsupp : ∀ v : V, (∀ u ∈ Δ.F.U i, QuadraticMap.polar Q u v = 0) →
      (∀ u ∈ Δ.F.U k, QuadraticMap.polar Q u v = 0) → w v = v)
    (σ : (Fin r → Multiplicative (ZMod p)) → (Fin r → Multiplicative (ZMod p)))
    (hσ : ∀ f, w * Δ.τ f * w⁻¹ = Δ.τ (σ f)) (hσσ : ∀ f, σ (σ f) = f) (hσ₀ : σ f₀ = f₀) :
    ∃ n ∈ specialBlock Q (Δ.τ f₀) h ⊓ orthDerived Q,
      ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (σ f) := by
  haveI : Finite V := Module.finite_of_finite K
  haveI : Finite (V ≃ₗ[K] V) :=
    Finite.of_injective (fun g : V ≃ₗ[K] V => (g : V → V)) DFunLike.coe_injective
  obtain ⟨N, hN, e, hNe⟩ := exists_odd_pow_pow_two_eq_one w
  set n : V ≃ₗ[K] V := w ^ N with hn_def
  have hn_orth : n ∈ orthDerived Q := by
    rw [hn_def]
    exact pow_mem hw N
  have hn_conj : ∀ f, n * Δ.τ f * n⁻¹ = Δ.τ (σ f) := by
    intro f
    rw [hn_def]
    exact pow_odd_conj_eq Δ.τ hσ hσσ hN f
  have hn_comm : n * Δ.τ f₀ = Δ.τ f₀ * n := by
    have h1 : n * Δ.τ f₀ * n⁻¹ = Δ.τ f₀ := by
      rw [hn_conj f₀, hσ₀]
    exact (mul_inv_eq_iff_eq_mul).mp h1
  have hsupp' : ∀ v : V, (∀ u ∈ Δ.F.U i, QuadraticMap.polar Q u v = 0) →
      (∀ u ∈ Δ.F.U k, QuadraticMap.polar Q u v = 0) → n v = v := by
    intro v h₁ h₂
    rw [hn_def]
    have hfixN : ∀ m : ℕ, (w ^ m) v = v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, LinearEquiv.mul_apply, hsupp v h₁ h₂, ih]
    exact hfixN N
  have hfix : ∀ v ∈ othersSpace (Δ.τ f₀).toLinearMap h, n v = v :=
    fixes_othersSpace_of_supported hy hh hi hk hsupp'
  have hn_supp : n ∈ supportedBlock Q (Δ.τ f₀) h :=
    mem_supportedBlock_of_orthDerived hn_orth hn_comm hfix
  have hn_pow : n ^ (2 ^ e) = 1 := by
    rw [hn_def]
    exact hNe
  have hn_special : n ∈ specialBlock Q (Δ.τ f₀) h :=
    mem_specialBlock_of_pow_two_pow (irreducible_of_mem_primaryFactors hh) hn_supp hn_pow
  exact ⟨n, Subgroup.mem_inf.mpr ⟨hn_special, hn_orth⟩, hn_conj⟩

end OrthTorus

end CFSG.StandardType

end
