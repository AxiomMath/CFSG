module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Statements
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open scoped commutatorElement

namespace Item22Res3Proof

theorem le_normalizer_of_conj_mem {H : Type*} [Group H] {X S : Subgroup H}
    (h : ∀ x ∈ X, ∀ y ∈ S, x * y * x⁻¹ ∈ S) : X ≤ Subgroup.normalizer (S : Set H) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h x hx y, fun hy => ?_⟩
  have := h x⁻¹ (X.inv_mem hx) _ hy
  rwa [inv_inv, show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this

theorem commutator_eq_bot_of_isCyclic {G : Type*} [Group G] [Finite G] {C D : Subgroup G}
    [IsCyclic C] (hC : IsPGroup 2 C) (hD : IsPGroup 3 D)
    (hDC : D ≤ Subgroup.normalizer (C : Set G)) : ⁅C, D⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro d hd
  set f : D →* MulAut C := C.normalizerMonoidHom.comp (Subgroup.inclusion hDC) with hf
  obtain ⟨j, hj⟩ := hC.exists_card_eq
  have hAut : IsPGroup 2 (MulAut C) := by
    refine IsPGroup.of_card (n := j - 1) ?_
    rw [Nat.card_congr (IsCyclic.mulAutMulEquiv C).toEquiv, hj, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient]
    rcases j with _ | j
    · simp
    · rw [Nat.totient_prime_pow Nat.prime_two (Nat.succ_pos j)]
      simp
  obtain ⟨k, hk⟩ := hD ⟨d, hd⟩
  obtain ⟨l, hl⟩ := hAut (f ⟨d, hd⟩)
  have h3 : (f ⟨d, hd⟩) ^ 3 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h1 : f ⟨d, hd⟩ = 1 := by
    have hcop : Nat.Coprime (3 ^ k) (2 ^ l) := Nat.Coprime.pow k l (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨h3, hl⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have := congrArg (fun φ : MulAut C => ((φ ⟨x, hx⟩ : C) : G)) h1
  simp only [hf, MonoidHom.coe_comp, Function.comp_apply, MulAut.one_apply] at this
  change d * x * d⁻¹ = x at this
  calc x * d = (d * x * d⁻¹) * d := by rw [this]
    _ = d * x := by group

end Item22Res3Proof

open Item22Res3Proof

end CFSG.RankThree.PartTwo.Sec21
