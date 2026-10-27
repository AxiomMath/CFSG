
module

public import CFSG.Sporadic.Schreier.J4SSylowBase1

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.Schreier.J4SSylowCheck
public import CFSG.Sporadic.Schreier.J4SLocalNodes
public import CFSG.Sporadic.Schreier.J4SNative
public import CFSG.Sporadic.Schreier.J4SCols
public import CFSG.Sporadic.Schreier.J4SOrbits
public meta import CFSG.Sporadic.Schreier.J4SOrbits
public import CFSG.Sporadic.Schreier.J4SSylowData
public meta import CFSG.Sporadic.Schreier.J4SSylowData
public import CFSG.Sporadic.J4.Local

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.Sporadic.J4 CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native

theorem eq_of_actsBy
    {g h : J} (hg : g ∈ K) (hh : h ∈ K) {C : Array ℕ} (h1 : ActsBy g C)
    (h2 : ActsBy h C) : g = h := by
  have e : ρK ⟨g, hg⟩ = ρK ⟨h, hh⟩ := by
    refine MulEquiv.ext fun n => Subtype.ext ?_
    obtain ⟨a, -, ha⟩ := exists_η_eq n.2
    rw [ρK_apply, ρK_apply, ← ha]
    exact (h1 a).trans (h2 a).symm
  exact congrArg Subtype.val (ρK_injective e)

theorem uElt_zero :
    uElt 0 = 1 :=
  eq_of_actsBy (U_le_K (uElt_mem_U 0)) K.one_mem (uElt_acts (by norm_num))
    (elem_zero ▸ actsBy_one)

theorem uElt_mul_kgen
    {e i : ℕ} (he : e < 1024) (hi : i < 4) :
    uElt e * kgen i = uElt (rightEdges[e]!)[i]! := by
  obtain ⟨-, -, -, hedge⟩ := elem_all e he
  obtain ⟨hlt, heq⟩ := hedge i hi
  refine eq_of_actsBy (K.mul_mem (U_le_K (uElt_mem_U e)) (kgen_mem_K i))
    (U_le_K (uElt_mem_U _)) (actsBy_mul (uElt_acts he) (kgen_acts hi)) ?_
  rw [← heq]
  exact uElt_acts hlt

theorem mem_U_iff
    {g : J} : g ∈ U ↔ ∃ e < 1024, uElt e = g := by
  constructor
  · intro hg
    have hg' : g ∈ Submonoid.closure (Set.range fun i : Fin 4 => kgen i) := by
      rw [← Subgroup.closure_toSubmonoid_of_finite]
      exact hg
    clear hg
    induction hg' using Submonoid.closure_induction_right with
    | one => exact ⟨0, by norm_num, uElt_zero⟩
    | mul_right g _ s hs ih =>
      obtain ⟨i, rfl⟩ := hs
      obtain ⟨e, he, rfl⟩ := ih
      beta_reduce
      exact ⟨_, ((elem_all e he).2.2.2 i i.isLt).1, (uElt_mul_kgen he i.isLt).symm⟩
  · rintro ⟨e, -, rfl⟩
    exact uElt_mem_U e

theorem card_U :
    Nat.card U = 1024 := by
  have hf : Function.Injective fun e : Fin 1024 => (⟨uElt e, uElt_mem_U e⟩ : U) := by
    intro e e' h
    have h' := Subtype.ext_iff.1 h
    dsimp only at h'
    exact Fin.ext (uElt_injOn e.isLt e'.isLt h')
  have hs : Function.Surjective fun e : Fin 1024 => (⟨uElt e, uElt_mem_U e⟩ : U) := by
    rintro ⟨g, hg⟩
    obtain ⟨e, he, rfl⟩ := mem_U_iff.1 hg
    exact ⟨⟨e, he⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective _ ⟨hf, hs⟩), Nat.card_fin]

theorem card_S0 :
    Nat.card S0 = 2 ^ 21 := by
  let f : N × U → S0 := fun p => ⟨(p.1 : J) * p.2, S0.mul_mem (N_le_S0 p.1.2) (U_le_S0 p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨n, hn⟩, ⟨u, hu⟩⟩ ⟨⟨n', hn'⟩, ⟨u', hu'⟩⟩ h
      have h' := Subtype.ext_iff.1 h
      dsimp only [f] at h'
      obtain ⟨e1, e2⟩ := mul_unique hn hn' hu hu' h'
      subst e1
      subst e2
      rfl
    · rintro ⟨s, hs⟩
      obtain ⟨n, hn, u, hu, rfl⟩ := exists_mul_of_mem_S0 hs
      exact ⟨(⟨n, hn⟩, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, card_N, card_U]
  norm_num

theorem card_J4J :
    Nat.card J = 86775571046077562880 := card_J j4Facts

theorem factorization_card_J :
    (Nat.card J).factorization 2 = 21 := by
  rw [card_J4J, show (86775571046077562880 : ℕ) = 2 ^ 21 * 41377816699065 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide), add_zero]

@[expose] def S0Sylow :
    Sylow 2 J :=
  Sylow.ofCard S0 (by rw [card_S0, factorization_card_J])

theorem S0Sylow_coe :
    (S0Sylow : Subgroup J) = S0 := Sylow.coe_ofCard _ _

end CFSG.Sporadic.J4Schreier
