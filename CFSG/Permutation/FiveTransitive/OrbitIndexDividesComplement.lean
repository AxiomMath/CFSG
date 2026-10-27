module

public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG

namespace FiveTransitive.OrbitIndexDividesComplement

open MulAction
open scoped BigOperators

theorem quotient_dvd_complement
    (G X : Type*) [Group G] [Finite G] [Finite X] [MulAction G X]
    (u : ℕ) (hu : u ∣ Nat.card G)
    (hstab : ∀ x : X, x ∉ fixedPoints G X → Nat.card (stabilizer G x) ∣ u) :
    Nat.card G / u ∣ Nat.card X - (fixedPoints G X).ncard := by
  classical
  let C : SubMulAction G X :=
    { carrier := (fixedPoints G X)ᶜ
      smul_mem' := by
        intro g x hx hfix
        have he : x = g • x := by
          simpa only [inv_smul_smul] using mem_fixedPoints.mp hfix g⁻¹
        exact hx (he.symm ▸ hfix) }
  have hc : Nat.card G / u ∣ Nat.card C := by
    let _ : Fintype G := Fintype.ofFinite G
    let _ : Fintype C := Fintype.ofFinite C
    let _ : Fintype (Quotient (orbitRel G C)) := Fintype.ofFinite _
    let _ : ∀ x : C, Fintype (stabilizer G x) := fun _ => Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,card_eq_sum_card_group_div_card_stabilizer G C]
    apply Finset.dvd_sum
    intro ω _
    have hd : Nat.card (stabilizer G ω.out) ∣ u := by
      rw [SubMulAction.stabilizer_of_subMul]
      exact hstab ω.out.val ω.out.property
    simpa only [Nat.card_eq_fintype_card] using Nat.div_dvd_div_left hu hd
  change Nat.card G / u ∣ Nat.card ((fixedPoints G X)ᶜ : Set X) at hc
  rwa [Nat.card_coe_set_eq,Set.ncard_compl] at hc

end FiveTransitive.OrbitIndexDividesComplement

end CFSG
