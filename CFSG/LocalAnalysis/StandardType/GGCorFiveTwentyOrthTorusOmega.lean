module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
public import CFSG.LocalAnalysis.StandardType.GGB48OmReduce
public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

open Module Multiplicative QuadraticMap

namespace CFSG.StandardType

namespace OrthTorus

open CFSG.Assembly SpCoord NbrOrth
open CFSG.RankThree.Classical2 (orthDerived)

section Omega

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem exists_torus_orthDerived {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) (E : Subgroup ↥(orthDerived Q))
    (hE : IsElemAbelian p E) (h3 : p ^ 3 ≤ Nat.card E)
    (hsc : ∀ g : ↥(orthDerived Q), (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ (r : ℕ) (τ : (Fin r → Multiplicative (ZMod p)) →* ↥(orthDerived Q)),
      Function.Injective τ ∧ τ.range = E ∧
      (∀ σ : Equiv.Perm (Fin r), ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      (∀ i j : Fin r, i ≠ j → ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      (∀ g : ↥(orthDerived Q), (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin r)) (ε : Fin r → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)) ∧
      ((OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p] ∧ finrank K V = 2 * r) ∨
        (OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p] ∧
          ∀ i : Fin r, ∃ w : ↥(orthDerived Q), ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f))) := by
  have hne : ∃ b ∈ E, b ≠ 1 := by
    by_contra h
    push Not at h
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr fun x hx =>
      h x hx
    rw [hE1, Subgroup.card_bot] at h3
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  exact exists_torus_orthDerived_of_ne hp hp2 hpq hQ hT E hE hne hsc

theorem torusSignedEltSC_orthDerived {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    (hS : ¬ OrdPNsOm.charSum Q ⊤ ≡ 1 [ZMOD p]) : GGTorusSignedEltSC p ↥(orthDerived Q) := by
  intro E hE h3 hsc
  obtain ⟨r, τ, hτinj, hrange, hperm, -, hnorm, hW⟩ :=
    exists_torus_orthDerived hp hp2 hpq hQ hT E hE h3 hsc
  rcases hW with ⟨h1, -⟩ | ⟨-, hsgn⟩
  · exact absurd h1 hS
  · exact ⟨r, τ, hτinj, hrange, hsgn, hperm, hnorm⟩

theorem torusEvenSignedPermEltSC_orthDerived {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0) {n : ℕ}
    (hV : finrank K V = 2 * n) (hS : ¬ OrdPNsOm.charSum Q ⊤ ≡ -1 [ZMOD p]) :
    GGTorusEvenSignedPermEltSC p ↥(orthDerived Q) fun k => k = n := by
  intro E hE h3 hsc
  obtain ⟨r, τ, hτinj, hrange, hperm, hdinv, hnorm, hW⟩ :=
    exists_torus_orthDerived hp hp2 hpq hQ hT E hE h3 hsc
  rcases hW with ⟨-, h2⟩ | ⟨h1, -⟩
  · exact ⟨r, τ, hτinj, hrange, by omega, hdinv, hperm, hnorm⟩
  · exact absurd h1 hS

end Omega

end OrthTorus

end CFSG.StandardType

end
