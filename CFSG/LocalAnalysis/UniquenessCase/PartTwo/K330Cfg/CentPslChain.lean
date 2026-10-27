module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.CentCnt
import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

private lemma k330c_mod7_cases {Q : ℕ}
    (hQ : ¬ 7 ∣ Q ∧ ¬ 7 ∣ Q - 1 ∧ ¬ 7 ∣ Q + 1) :
    Q % 7 = 2 ∨ Q % 7 = 3 ∨ Q % 7 = 4 ∨ Q % 7 = 5 := by
  have h0 : Q % 7 ≠ 0 := fun h => hQ.1 (Nat.dvd_iff_mod_eq_zero.mpr h)
  have h1 : Q % 7 ≠ 1 := by
    intro h
    exact hQ.2.1 (by
      refine ⟨Q / 7, ?_⟩
      have hdm : Q / 7 * 7 + Q % 7 = Q := Nat.div_add_mod' Q 7
      omega)
  have h6 : Q % 7 ≠ 6 := by
    intro h
    exact hQ.2.2 (by
      refine ⟨Q / 7 + 1, ?_⟩
      have hdm : Q / 7 * 7 + Q % 7 = Q := Nat.div_add_mod' Q 7
      omega)
  have hlt : Q % 7 < 7 := Nat.mod_lt _ (by norm_num)
  have hcases : Q % 7 = 0 ∨ Q % 7 = 1 ∨ Q % 7 = 2 ∨ Q % 7 = 3 ∨ Q % 7 = 4 ∨
      Q % 7 = 5 ∨ Q % 7 = 6 := by omega
  rcases hcases with h | h | h | h | h | h | h
  · exact absurd h h0
  · exact absurd h h1
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))
  · exact absurd h h6

private lemma k330c_psl_arith {Q n a b u : ℕ}
    (hQ3 : Q % 3 = 2)
    (hQ7 : Q % 7 = 2 ∨ Q % 7 = 3 ∨ Q % 7 = 4 ∨ Q % 7 = 5)
    (hn : n = 4 ∨ n = 5) (ha : a < n) (hb : b < n) (hua : u ≤ a) (hub : u ≤ b)
    (h1 : Q ^ n ≡ Q ^ a [MOD 3]) (h2 : Q ^ n ≡ Q ^ b [MOD 7])
    (h3 : Q ^ a ≡ Q ^ u [MOD 7]) (h4 : Q ^ b ≡ Q ^ u [MOD 3]) :
    n = 5 ∧ u = 0 ∧ b ≠ 0 := by
  have hQ3' : Q ≡ 2 [MOD 3] :=
    (Nat.mod_modEq Q 3).symm.trans (by rw [hQ3])
  have e1 : 2 ^ n ≡ 2 ^ a [MOD 3] := (hQ3'.pow n).symm.trans (h1.trans (hQ3'.pow a))
  have e4 : 2 ^ b ≡ 2 ^ u [MOD 3] := (hQ3'.pow b).symm.trans (h4.trans (hQ3'.pow u))
  have hc : ∃ c : ℕ, (c = 2 ∨ c = 3 ∨ c = 4 ∨ c = 5) ∧ Q ≡ c [MOD 7] := by
    rcases hQ7 with h | h | h | h
    · exact ⟨2, Or.inl rfl, by
        show Q % 7 = 2 % 7
        rw [h]⟩
    · exact ⟨3, Or.inr (Or.inl rfl), by
        show Q % 7 = 3 % 7
        rw [h]⟩
    · exact ⟨4, Or.inr (Or.inr (Or.inl rfl)), by
        show Q % 7 = 4 % 7
        rw [h]⟩
    · exact ⟨5, Or.inr (Or.inr (Or.inr rfl)), by
        show Q % 7 = 5 % 7
        rw [h]⟩
  obtain ⟨c, hcrange, hQ7'⟩ := hc
  have e2 : c ^ n ≡ c ^ b [MOD 7] := (hQ7'.pow n).symm.trans (h2.trans (hQ7'.pow b))
  have e3 : c ^ a ≡ c ^ u [MOD 7] := (hQ7'.pow a).symm.trans (h3.trans (hQ7'.pow u))
  have hu_lt : u < n := lt_of_le_of_lt hua ha
  rcases hn with rfl | rfl <;>
    rcases hcrange with rfl | rfl | rfl | rfl <;>
      (have ha' : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by omega
       have hb' : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by omega
       have hu' : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4 := by omega
       rcases ha' with rfl | rfl | rfl | rfl | rfl <;>
         rcases hb' with rfl | rfl | rfl | rfl | rfl <;>
           rcases hu' with rfl | rfl | rfl | rfl | rfl <;>
             first
               | exact absurd ha (by decide)
               | exact absurd hb (by decide)
               | exact absurd hua (by decide)
               | exact absurd hub (by decide)
               | exact absurd e1 (by decide)
               | exact absurd e2 (by decide)
               | exact absurd e3 (by decide)
               | exact absurd e4 (by decide)
               | decide)

theorem psl_chain {F : Type*} [Field F] [Finite F] {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hn : Module.finrank F V = 4 ∨ Module.finrank F V = 5)
    (hQ3 : Nat.card F % 3 = 2)
    (hQ7 : ¬ 7 ∣ Nat.card F ∧ ¬ 7 ∣ Nat.card F - 1 ∧ ¬ 7 ∣ Nat.card F + 1)
    {x r : V ≃ₗ[F] V} (hxr : x * r = r * x) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hr : r ^ 7 = 1) (hr1 : r ≠ 1) :
    Module.finrank F V = 5 ∧ LinearMap.ker ((r : V →ₗ[F] V) - 1) ≠ ⊥ ∧
      LinearMap.ker ((x : V →ₗ[F] V) - 1) ⊓ LinearMap.ker ((r : V →ₗ[F] V) - 1) = ⊥ := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  set n : ℕ := Module.finrank F V with hnV
  set A : Submodule F V := LinearMap.ker ((x : V →ₗ[F] V) - 1) with hA
  set B : Submodule F V := LinearMap.ker ((r : V →ₗ[F] V) - 1) with hB
  set U : Submodule F V := A ⊓ B with hU
  have hWA : ∀ w ∈ A, r w ∈ A := by
    intro w hw
    rw [hA] at hw ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change x (r w) = r w
    have hxw : x w = w := hw
    have hxr' : x (r w) = r (x w) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f w) hxr
      simpa [LinearEquiv.mul_apply] using h
    rw [hxr', hxw]
  have hWB : ∀ w ∈ B, x w ∈ B := by
    intro w hw
    rw [hB] at hw ⊢
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hw
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    change r (x w) = x w
    have hrw : r w = w := hw
    have hxr' : x (r w) = r (x w) := by
      have h := congrArg (fun f : V ≃ₗ[F] V => f w) hxr
      simpa [LinearEquiv.mul_apply] using h
    rw [← hxr', hrw]
  have hc1 : Nat.card F ^ n ≡ Nat.card F ^ Module.finrank F A [MOD 3] := by
    have h := card_modEq_inf_ker x (show Nat.Prime 3 by decide) hx
      (⊤ : Submodule F V) (fun w _ => Submodule.mem_top)
    rw [top_inf_eq, ← hA] at h
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(⊤ : Submodule F V)),
        Module.natCard_eq_pow_finrank (K := F) (V := ↥A), finrank_top] at h
    rw [← hnV] at h
    exact h
  have hc2 : Nat.card F ^ n ≡ Nat.card F ^ Module.finrank F B [MOD 7] := by
    have h := card_modEq_inf_ker r (show Nat.Prime 7 by decide) hr
      (⊤ : Submodule F V) (fun w _ => Submodule.mem_top)
    rw [top_inf_eq, ← hB] at h
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥(⊤ : Submodule F V)),
        Module.natCard_eq_pow_finrank (K := F) (V := ↥B), finrank_top] at h
    rw [← hnV] at h
    exact h
  have hc3 : Nat.card F ^ Module.finrank F A ≡ Nat.card F ^ Module.finrank F U [MOD 7] := by
    have h := card_modEq_inf_ker r (show Nat.Prime 7 by decide) hr A hWA
    rw [← hB, ← hU] at h
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥A),
        Module.natCard_eq_pow_finrank (K := F) (V := ↥U)] at h
    exact h
  have hc4 : Nat.card F ^ Module.finrank F B ≡ Nat.card F ^ Module.finrank F U [MOD 3] := by
    have h := card_modEq_inf_ker x (show Nat.Prime 3 by decide) hx B hWB
    rw [inf_comm, ← hA, ← hU] at h
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥B),
        Module.natCard_eq_pow_finrank (K := F) (V := ↥U)] at h
    exact h
  have hn' : n = 4 ∨ n = 5 := by rw [hnV]; exact hn
  have ha_lt : Module.finrank F A < n := by
    rw [hnV]
    rcases lt_or_eq_of_le (Submodule.finrank_le A) with hlt | heq
    · exact hlt
    · exfalso
      have hAtop : A = ⊤ := Submodule.eq_top_of_finrank_eq heq
      have hker : LinearMap.ker ((x : V →ₗ[F] V) - 1) = ⊤ := by
        rw [hA] at hAtop
        exact hAtop
      have hx0 : (x : V →ₗ[F] V) = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hker)
      have hxone : x = 1 := by
        ext v
        have hv := congrArg (fun f : V →ₗ[F] V => f v) hx0
        simpa using hv
      exact hx1 hxone
  have hb_lt : Module.finrank F B < n := by
    rw [hnV]
    rcases lt_or_eq_of_le (Submodule.finrank_le B) with hlt | heq
    · exact hlt
    · exfalso
      have hBtop : B = ⊤ := Submodule.eq_top_of_finrank_eq heq
      have hker : LinearMap.ker ((r : V →ₗ[F] V) - 1) = ⊤ := by
        rw [hB] at hBtop
        exact hBtop
      have hr0 : (r : V →ₗ[F] V) = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp hker)
      have hrone : r = 1 := by
        ext v
        have hv := congrArg (fun f : V →ₗ[F] V => f v) hr0
        simpa using hv
      exact hr1 hrone
  have hua : Module.finrank F U ≤ Module.finrank F A := by
    rw [hU]
    exact Submodule.finrank_mono inf_le_left
  have hub : Module.finrank F U ≤ Module.finrank F B := by
    rw [hU]
    exact Submodule.finrank_mono inf_le_right
  have harith := k330c_psl_arith hQ3 (k330c_mod7_cases hQ7) hn' ha_lt hb_lt hua hub
    hc1 hc2 hc3 hc4
  refine ⟨harith.1, ?_, ?_⟩
  · intro hBbot
    exact harith.2.2 (by rw [hBbot, finrank_bot])
  · exact Submodule.finrank_eq_zero.mp harith.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
