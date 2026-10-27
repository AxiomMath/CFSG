module

public import CFSG.LocalAnalysis.StandardType.GGRCLatticeTripleTwo
public import CFSG.LocalAnalysis.StandardType.GGLatticeRootsDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggLatCartan_cycle {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {v₀ v₁ v₂ : Fin m → ℤ} (h₀ : GGLatRoot Q v₀) (h₁ : GGLatRoot Q v₁) (h₂ : GGLatRoot Q v₂) :
    ggLatCartan Q v₁ v₀ * ggLatCartan Q v₂ v₁ * ggLatCartan Q v₀ v₂ =
      ggLatCartan Q v₀ v₁ * ggLatCartan Q v₁ v₂ * ggLatCartan Q v₂ v₀ := by
  have hsymm : ∀ v w : Fin m → ℤ, dotProduct v (Q.mulVec w) = dotProduct w (Q.mulVec v) := by
    intro v w
    have h1 : Matrix.vecMul v Q = Q.mulVec v := by
      conv_lhs => rw [← hQ.1]
      exact Matrix.vecMul_transpose Q v
    rw [Matrix.dotProduct_mulVec, h1, dotProduct_comm]
  have e : ∀ v w : Fin m → ℤ, GGLatRoot Q w →
      ggLatCartan Q v w * dotProduct w (Q.mulVec w) = 2 * dotProduct v (Q.mulVec w) := by
    intro v w hw
    unfold ggLatCartan
    exact Int.ediv_mul_cancel (hw.2 v)
  have hpos : ∀ w : Fin m → ℤ, GGLatRoot Q w → 0 < dotProduct w (Q.mulVec w) :=
    fun w hw => hQ.2 w hw.1
  have hne : dotProduct v₀ (Q.mulVec v₀) * dotProduct v₁ (Q.mulVec v₁) *
      dotProduct v₂ (Q.mulVec v₂) ≠ 0 :=
    (mul_pos (mul_pos (hpos v₀ h₀) (hpos v₁ h₁)) (hpos v₂ h₂)).ne'
  apply mul_right_cancel₀ hne
  have e10 := e v₁ v₀ h₀
  have e21 := e v₂ v₁ h₁
  have e02 := e v₀ v₂ h₂
  have e01 := e v₀ v₁ h₁
  have e12 := e v₁ v₂ h₂
  have e20 := e v₂ v₀ h₀
  calc ggLatCartan Q v₁ v₀ * ggLatCartan Q v₂ v₁ * ggLatCartan Q v₀ v₂ *
        (dotProduct v₀ (Q.mulVec v₀) * dotProduct v₁ (Q.mulVec v₁) * dotProduct v₂ (Q.mulVec v₂))
      = (ggLatCartan Q v₁ v₀ * dotProduct v₀ (Q.mulVec v₀)) *
          (ggLatCartan Q v₂ v₁ * dotProduct v₁ (Q.mulVec v₁)) *
          (ggLatCartan Q v₀ v₂ * dotProduct v₂ (Q.mulVec v₂)) := by ring
    _ = (2 * dotProduct v₁ (Q.mulVec v₀)) * (2 * dotProduct v₂ (Q.mulVec v₁)) *
          (2 * dotProduct v₀ (Q.mulVec v₂)) := by rw [e10, e21, e02]
    _ = (2 * dotProduct v₀ (Q.mulVec v₁)) * (2 * dotProduct v₁ (Q.mulVec v₂)) *
          (2 * dotProduct v₂ (Q.mulVec v₀)) := by
        rw [hsymm v₁ v₀, hsymm v₂ v₁, hsymm v₀ v₂]
    _ = (ggLatCartan Q v₀ v₁ * dotProduct v₁ (Q.mulVec v₁)) *
          (ggLatCartan Q v₁ v₂ * dotProduct v₂ (Q.mulVec v₂)) *
          (ggLatCartan Q v₂ v₀ * dotProduct v₀ (Q.mulVec v₀)) := by rw [e01, e12, e20]
    _ = ggLatCartan Q v₀ v₁ * ggLatCartan Q v₁ v₂ * ggLatCartan Q v₂ v₀ *
        (dotProduct v₀ (Q.mulVec v₀) * dotProduct v₁ (Q.mulVec v₁) * dotProduct v₂ (Q.mulVec v₂)) := by
        ring

theorem ggLatticeTriple_cycleBalanced {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {m : ℕ} {Q : Matrix (Fin m) (Fin m) ℤ} (hQ : GGLatForm Q)
    {v : Fin 3 → Fin m → ℤ} (hv : ∀ k, GGLatRoot Q (v k)) {μ : Fin 3 → ZMod p} (hμ : ∀ k, μ k ≠ 0)
    (a : Fin 3 → Module.Dual (ZMod p) V) (hh : Fin 3 → V)
    (hcart : ∀ i k : Fin 3, a i (hh k) * μ k = μ i * (ggLatCartan Q (v k) (v i) : ZMod p)) :
    a 0 (hh 1) * a 1 (hh 2) * a 2 (hh 0) = a 1 (hh 0) * a 2 (hh 1) * a 0 (hh 2) := by
  have hA : ∀ i k : Fin 3, a i (hh k) = μ i * (ggLatCartan Q (v k) (v i) : ZMod p) / μ k :=
    fun i k => eq_div_of_mul_eq (hμ k) (hcart i k)
  have hZ := congrArg (Int.cast : ℤ → ZMod p) (ggLatCartan_cycle hQ (hv 0) (hv 1) (hv 2))
  push_cast at hZ
  rw [hA 0 1, hA 1 2, hA 2 0, hA 1 0, hA 2 1, hA 0 2]
  have h1 : μ 0 * (ggLatCartan Q (v 1) (v 0) : ZMod p) / μ 1 *
      (μ 1 * (ggLatCartan Q (v 2) (v 1) : ZMod p) / μ 2) *
      (μ 2 * (ggLatCartan Q (v 0) (v 2) : ZMod p) / μ 0) =
      (ggLatCartan Q (v 1) (v 0) : ZMod p) * (ggLatCartan Q (v 2) (v 1) : ZMod p) *
        (ggLatCartan Q (v 0) (v 2) : ZMod p) := by
    have := hμ 0; have := hμ 1; have := hμ 2
    field_simp
  have h2 : μ 1 * (ggLatCartan Q (v 0) (v 1) : ZMod p) / μ 0 *
      (μ 2 * (ggLatCartan Q (v 1) (v 2) : ZMod p) / μ 1) *
      (μ 0 * (ggLatCartan Q (v 2) (v 0) : ZMod p) / μ 2) =
      (ggLatCartan Q (v 0) (v 1) : ZMod p) * (ggLatCartan Q (v 1) (v 2) : ZMod p) *
        (ggLatCartan Q (v 2) (v 0) : ZMod p) := by
    have := hμ 0; have := hμ 1; have := hμ 2
    field_simp
  rw [h1, h2]
  exact hZ

theorem ggRC_cycleBalanced_two (hJr : GGForkJr) (hPump : GGForkPumpOr) (hLB : GGLBalanceInput)
    (hSP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b₁ b₂ : Λ}
    {Λa : Type} {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ ⊕ Λa → MulAut ↥Bs} {h : Λ ⊕ Λa → V} {α : Λ ⊕ Λa → Module.Dual (ZMod p) V}
    {j j' : Λ} (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hαj : α (Sum.inl j) (h (Sum.inl j)) = 2) (hαj' : α (Sum.inl j') (h (Sum.inl j')) = 2)
    (hφtop : ∀ o, φ o ∈ ggAutomizer ⊤ Bs)
    (hJL : ∀ j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂}, φ (Sum.inl j) ∈ ggAutomizer L Bs)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j)))
    (hj : j ≠ b₁ ∧ j ≠ b₂) (hj' : j' ≠ b₁ ∧ j' ≠ b₂) {ψ : MulAut ↥Bs}
    (hψ : ψ ∈ Subgroup.closure (Set.range φ)) {ht : V} {αt : Module.Dual (ZMod p) V}
    (hαt : αt ht = 2)
    (htl : ∀ w, ggLin (p := p) ι (ψ * φ (Sum.inl j) * ψ⁻¹) w = w - αt w • ht)
    (hnc : ψ * φ (Sum.inl j) * ψ⁻¹ * φ (Sum.inl j') ≠
      φ (Sum.inl j') * (ψ * φ (Sum.inl j) * ψ⁻¹)) :
    α (Sum.inl j) (h (Sum.inl j')) * α (Sum.inl j') ht * αt (h (Sum.inl j)) =
      α (Sum.inl j') (h (Sum.inl j)) * αt (h (Sum.inl j')) * α (Sum.inl j) ht := by
  obtain ⟨m, Q, v, μ, hQ, hv, hμ, hc⟩ := ggRC_lattice_triple_two hJr hPump hLB hSP hp5 hH hφ hαj
    hαj' hφtop hJL hJ hj hj' hψ hαt htl hnc
  have := ggLatticeTriple_cycleBalanced hQ hv hμ ![α (Sum.inl j), α (Sum.inl j'), αt]
    ![h (Sum.inl j), h (Sum.inl j'), ht] hc
  simpa using this

end CFSG.StandardType

end
