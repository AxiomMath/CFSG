module

import CFSG.Monster.B.Gen.OrbitChain
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.TwoNodeSmall

private lemma tnc_closure_fix {G V : Type*} [Group G] [MulAction G V] (S : Set G) (v : V)
    (h : ∀ s ∈ S, s • v = v) : ∀ g ∈ Subgroup.closure S, g • v = v := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => exact one_smul G v
  | mul x y _ _ hx hy => rw [mul_smul, hy, hx]
  | inv x _ hx => rw [inv_smul_eq_iff, hx]

theorem card_ge_of_orbit_chain {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    [Finite V] (R : Subgroup (V ≃ₗ[ZMod p] V)) {m : ℕ} (b : Fin m → V)
    (S : Fin m → Set (V ≃ₗ[ZMod p] V)) (O : Fin m → Finset V) (hS : ∀ k, S k ⊆ R)
    (hfix : ∀ k, ∀ s ∈ S k, ∀ j : Fin m, j < k → s (b j) = b j)
    (hO : ∀ k, ∀ v ∈ O k, v ∈ MulAction.orbit (Subgroup.closure (S k)) (b k)) :
    ∏ k, (O k).card ≤ Nat.card R := by
  classical
  haveI hGfin : Finite (V ≃ₗ[ZMod p] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (fun v => congr_fun h v))
  haveI : Finite R :=
    Finite.of_injective (Subtype.val : R → (V ≃ₗ[ZMod p] V)) Subtype.val_injective
  let b' : ℕ → V := fun i => if h : i < m then b ⟨i, h⟩ else 0
  let P' : ℕ → Finset V := fun i => if h : i < m then O ⟨i, h⟩ else ∅
  have hcl : ∀ k, Subgroup.closure (S k) ≤ R := fun k => by
    rw [← Subgroup.closure_eq R]
    exact Subgroup.closure_mono (hS k)
  have hP : ∀ i < m, ∀ q ∈ P' i, ∃ g : R, (∀ k < i, g • b' k = b' k) ∧ g • b' i = q := by
    intro i hi q hq
    have hq' : q ∈ O ⟨i, hi⟩ := by simpa [P', hi] using hq
    obtain ⟨⟨g, hg⟩, hgq⟩ := hO ⟨i, hi⟩ q hq'
    refine ⟨⟨g, hcl _ hg⟩, ?_, ?_⟩
    · intro k hk
      have hkm : k < m := lt_trans hk hi
      have hfixk : ∀ s ∈ S ⟨i, hi⟩, s • b ⟨k, hkm⟩ = b ⟨k, hkm⟩ := fun s hs =>
        hfix ⟨i, hi⟩ s hs ⟨k, hkm⟩ hk
      have := tnc_closure_fix (S ⟨i, hi⟩) (b ⟨k, hkm⟩) hfixk g hg
      simpa [b', hkm] using this
    · simpa [b', hi] using hgq
  have key := CFSG.Monster.B.card_ge_prod_of_chain (G := R) b' P' m hP
  have hprod : ∏ i ∈ Finset.range m, (P' i).card = ∏ k : Fin m, (O k).card := by
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [P', k.isLt]
  rwa [hprod] at key

end CFSG.TwoNodeSmall
