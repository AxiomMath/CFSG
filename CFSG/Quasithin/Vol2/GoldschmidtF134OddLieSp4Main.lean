module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Transport
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Out
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieSp4Even

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.EmptyFaithfulMultiple
open CFSG.Quasithin.F134.Sp4 CFSG.Quasithin.H13.NQCore.Psp4

theorem psp4Even_simple : Psp4EvenSimple := by
  intro n A _ _ p _ L P T hp5 hL h
  obtain ⟨⟨-, hn1, -, hne⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have hn : 2 ≤ n := by
    by_contra h'
    have : n = 1 := by omega
    subst this
    exact hne rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hp2 : p ≠ 2 := by omega
  have := h.normal
  have hU := h.isSylowTwoOf_inf
  obtain ⟨a, ha, hPa⟩ := h.exists_card
  obtain ⟨hPU, hab, hdvd⟩ := normalizes_of_mulEquiv_odd hK4
    (e.trans (Lin2.Five.projEquiv K).symm) hU h.le hp2 ha hPa h.exp h.mul_inf
  have ha2 : a = 2 := by
    rcases ha with rfl | rfl
    · rfl
    · obtain ⟨x, hx, y, hy, hxy⟩ := h.nonab hPa
      exact absurd (hab x hx y hy) hxy
  subst ha2
  have hZ := Lin2.Five.center_eq_bot_of_equiv e
  obtain ⟨τ, hτn, hτ⟩ := exists_forall_eq_conj_mul_pow_pow hK e
  have hnorm : ∀ s ∈ T ⊓ Subgroup.normalizer (P : Set A),
      s ∈ Subgroup.normalizer ((T ⊓ L : Subgroup A) : Set A) := fun s hs =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs.1,
      (Subgroup.normalizer_eq_top_iff.mpr h.normal).symm ▸ Subgroup.mem_top s⟩
  have hcyc : AutCyclic T P := by
    refine autCyclic_of_forall hτ fun s hs x hsx y hy => ?_
    have hs2 : IsPGroup 2 (Subgroup.zpowers s) :=
      h.sylow.2.1.to_le (Subgroup.zpowers_le.mpr hs.1)
    exact conj_eq_of_conjNormal_eq_conj_odd hZ hU h.le hp2 h.isPGroup hPU hs2 (hnorm s hs) hs.2
      hsx hy
  obtain ⟨c, hc, hgen⟩ := hcyc
  have hev : Even n := by
    refine even_of_pow_centralizes h hPa hab hc hgen fun y hy => ?_
    have hc2 : IsPGroup 2 (Subgroup.zpowers c) :=
      h.sylow.2.1.to_le (Subgroup.zpowers_le.mpr hc.1)
    exact pow_centralizes hZ hU h.le hp2 h.isPGroup hPU hτn hτ hc2 (hnorm c hc) hc.2 hy
  exact ⟨hPa, hev, by rwa [hK] at hdvd, ⟨c, hc, hgen⟩⟩

end CFSG.Quasithin.H13.NQCore
