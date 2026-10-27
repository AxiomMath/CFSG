module

public import CFSG.Quasithin.EmptyFaithful.S153G93DOm4PC
public import CFSG.Quasithin.EmptyFaithful.S153G93DCases
public import CFSG.Quasithin.EmptyFaithful.S153G93DOm4PB

public section

namespace CFSG.Quasithin.S153G93D.Om4P

open CFSG.Quasithin.H.Om4 CFSG.Quasithin.H

variable {F : Type} [Field F]

theorem card_VM [Finite F] : Nat.card (VM F) = Nat.card F ^ 4 := by
  change Nat.card (Fin 2 → Fin 2 → F) = _
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
    ← pow_mul]

theorem twoOmega_holds : TwoOmega := by
  intro W _ _ K L₁ L₂ S a hctx hmod
  obtain ⟨n, -, F, fF, finF, hFn, π, hπ⟩ := hmod
  obtain ⟨β, hd⟩ := exists_tensorData hπ
  have hπs : Function.Surjective π := hπ.1
  have hcardW : Nat.card W = (2 ^ n) ^ 4 := by
    rw [Nat.card_congr β.toEquiv, card_VM, hFn]
  have hn2 : 2 ≤ n := by
    have h6 := hctx.big
    rw [hcardW, ← pow_mul] at h6
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h6
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hFn])
  have hK4 : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hfac := normalizes_factorL2 hK4 hd hπs hctx.sup hctx.comm hctx.inf
    (isQuasisimple_of_simple_nonabelian hctx.simple₁ hctx.nab₁)
    (isQuasisimple_of_simple_nonabelian hctx.simple₂ hctx.nab₂)
    (ne_bot_of_nonabelian hctx.nab₁) (ne_bot_of_nonabelian hctx.nab₂) hctx.aL₁ hctx.aL₂
  have hL := hL_of_normalizes_factor hd hfac
  have ha2 : a * a = 1 := by rw [← pow_two]; exact hctx.a2
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haN : a ∈ Subgroup.normalizer (K : Set (MulAut W)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hctx.aN k hk, fun hk => ?_⟩
    have h1 := hctx.aN _ hk
    have e : a * (a * k * a⁻¹) * a⁻¹ = k := by
      rw [hainv]
      calc a * (a * k * a) * a = (a * a) * k * (a * a) := by simp only [mul_assoc]
        _ = k := by rw [ha2, one_mul, mul_one]
    rwa [e] at h1
  have hanorm : congrHom β a ∈
      Subgroup.normalizer ((rho (K := F)).range : Set (MulAut (VM F))) := by
    rw [← map_eq_range hπs hd, ← Subgroup.map_equiv_normalizer_eq]
    exact ⟨a, haN, rfl⟩
  obtain ⟨A, B, τ, hform⟩ := form_of_normalizes hK4 hanorm hL
  have h2 : (lr A B * frM τ) * (lr A B * frM τ) = 1 := by
    rw [← hform, ← map_mul, ha2, map_one]
  have h1 : lr A B * frM τ ≠ 1 := by
    rw [← hform]
    intro h
    exact hctx.a1 (congrHom_injective β (h.trans (map_one _).symm))
  have hcard := card_le_commV β hform (not_scalar h2 h1)
  rw [hctx.rk, hFn, ← pow_mul] at hcard
  have h3 : n * 2 ≤ 2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  omega

end CFSG.Quasithin.S153G93D.Om4P
