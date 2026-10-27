module

public import CFSG.Permutation.FiveTransitive.OyamaMinimalOrbitDescent
public import Mathlib.GroupTheory.GroupAction.Embedding

public section

namespace CFSG

namespace FiveTransitive.SemiregularTupleInvolution

open MulAction OyamaMinimalOrbitDescent

theorem exists_fixed_range
    {G X : Type*} [Group G] [Finite G] [MulAction G X] (k : ℕ)
    (e : Fin k ↪ X) (S : Sylow 2 (stabilizer G e))
    (hS : (S : Subgroup (stabilizer G e)) ≠ ⊥)
    (hfixed : fixedPoints (ambientSylow e S) X = Set.range e)
    (hfree : ∀ q : G, q ∈ ambientSylow e S → q ≠ 1 →
      ∀ x : X, x ∉ Set.range e → q • x ≠ x) :
    ∃ a : G, a ∈ ambientSylow e S ∧ orderOf a = 2 ∧
      fixedBy X a = Set.range e := by
  classical
  let _ : Nontrivial S := (S : Subgroup (stabilizer G e)).nontrivial_iff_ne_bot.mpr hS
  let _ : Fintype S := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := exists_ne (1 : S)
  have hdiv : 2 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card]
    exact (S.isPGroup'.dvd_orderOf hu).trans (orderOf_dvd_natCard u)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card (p := 2) (G := S) hdiv
  let a : G := t.val.val
  have ha : a ∈ ambientSylow e S := ⟨t.val, t.property, rfl⟩
  have horder : orderOf a = 2 :=
    (Subgroup.orderOf_coe t.val).trans ((Subgroup.orderOf_coe t).trans ht)
  have ha1 : a ≠ 1 := by
    intro he
    rw [he, orderOf_one] at horder
    omega
  refine ⟨a, ha, horder, ?_⟩
  ext x
  constructor
  · intro hx
    by_contra hout
    exact hfree a ha ha1 x hout hx
  · intro hx
    have hf : x ∈ fixedPoints (ambientSylow e S) X := by rwa [hfixed]
    exact mem_fixedPoints.mp hf ⟨a, ha⟩

end FiveTransitive.SemiregularTupleInvolution

end CFSG
