module

public import CFSG.Permutation.FiveTransitive.OrbitComplementCardBound
public import CFSG.Permutation.FiveTransitive.A9TenQuotientArithmetic
public import CFSG.Permutation.FiveTransitive.A9TenQuotientTransitive

public section

namespace CFSG

namespace FiveTransitive.A9TenQuotientNineOrbit
open MulAction

theorem exists_nine_orbit
    {F E : Type*} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E ≤ 10)
    (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F)
    (htau : Function.Surjective tau) : ∃ x : E, Nat.card (orbit B x) = 9 := by
  classical
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]; norm_num [Nat.factorial]
  have hB := Nat.card_le_card_of_surjective tau htau
  rw [hA] at hB
  let _ : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨b,hb⟩ := exists_ne (1 : B)
  obtain ⟨x,hx⟩ : ∃ x : E, (b : Equiv.Perm E) x ≠ x := by
    by_contra! hn
    apply hb
    apply Subtype.ext
    exact Equiv.ext hn
  let _ : Fintype (orbit B x) := Fintype.ofFinite _
  have hne : Nat.card (orbit B x) ≠ 1 := by
    intro he
    have hf : x ∈ fixedPoints B E := mem_fixedPoints_iff_card_orbit_eq_one.mpr
      (by rwa [← Nat.card_eq_fintype_card])
    exact hx (hf b)
  have hpos : 0 < Nat.card (orbit B x) := by
    let _ : Nonempty (orbit B x) := ⟨⟨x,mem_orbit_self x⟩⟩
    exact Nat.card_pos
  have hle : Nat.card (orbit B x) ≤ Nat.card E :=
    Nat.card_le_card_of_injective (fun y : orbit B x => y.val) Subtype.val_injective
  have hnsmall : ¬ Nat.card (orbit B x) ≤ 8 := by
    intro ho
    have hb := OrbitComplementCardBound.card_le_factorials B x
    have hh := A9TenQuotientArithmetic.factorial_product_lt (Nat.card E)
      (Nat.card (orbit B x)) hE (by omega) ho
    omega
  have hc : Nat.card (orbit B x) = 9 ∨ Nat.card (orbit B x) = 10 := by omega
  rcases hc with h9 | h10
  · exact ⟨x,h9⟩
  · have hE10 : Nat.card E = 10 := by omega
    have hall : orbit B x = Set.univ := (Set.eq_univ_iff_ncard _).mpr (by
      rw [← Nat.card_coe_set_eq]
      exact h10.trans hE10.symm)
    let _ : IsPretransitive B E := by
      constructor
      intro y z
      obtain ⟨a,ha⟩ := mem_orbit_iff.mp (hall ▸ Set.mem_univ y)
      obtain ⟨c,hc⟩ := mem_orbit_iff.mp (hall ▸ Set.mem_univ z)
      exact ⟨c * a⁻¹,by rw [mul_smul,← ha,inv_smul_smul,hc]⟩
    exact (A9TenQuotientTransitive.excluded hF hE10 B tau htau).elim

end FiveTransitive.A9TenQuotientNineOrbit

end CFSG
