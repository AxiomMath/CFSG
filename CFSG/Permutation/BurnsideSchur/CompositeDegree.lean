module

public import CFSG.Permutation.BurnsideSchur.SeparatingSubgroup

public section

namespace CFSG

open MulAction
open scoped Pointwise

namespace BurnsideSchur

variable {C : Type*} [AddCommGroup C] [Finite C] {G : Subgroup (Equiv.Perm C)}
  (hG : ∀ c : C, Equiv.addRight c ∈ G)
include hG

private theorem prime_dvd_ncard_nsmul_eq [IsPreprimitive G C] {p : ℕ} (hp : p.Prime)
    (hpC : p ∣ Nat.card C) {S : Set C} (hS : IsStable G S) {c : C} (hc : c ≠ 0) :
    p ∣ {x ∈ S | p • x = c}.ncard := by
  have := Fintype.ofFinite C
  have := Fact.mk hp
  have ha := pow_mem (ofSet_mem_schurRing hG (R := ZMod p) hS) p
  let Y := {y | (ofSet (ZMod p) S ^ p).coeff y ≠ 0}
  have hYp : AddSubgroup.closure Y ≤ (nsmulAddMonoidHom p : C →+ C).range := by
    refine (AddSubgroup.closure_le _).2 fun y hy => ?_
    obtain ⟨x, -, rfl⟩ : {x ∈ S | p • x = y}.Nonempty := by
      refine Set.nonempty_iff_ne_empty.2 fun h => hy ?_
      rw [coeff_ofSet_pow_char, h, Set.ncard_empty, Nat.cast_zero]
    exact ⟨x, rfl⟩
  have hrange : (nsmulAddMonoidHom p : C →+ C).range ≠ ⊤ := by
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' p hpC
    intro h
    have hinj := Finite.injective_iff_surjective.2 (AddMonoidHom.range_eq_top.1 h)
    have hz0 : z = 0 := hinj (by simp [← hz, addOrderOf_nsmul_eq_zero])
    rw [hz0, addOrderOf_zero] at hz
    exact hp.ne_one hz.symm
  have hbot : AddSubgroup.closure Y = ⊥ :=
    ((isStable_setOf_coeff hG ha (· ≠ 0)).closure hG).eq_bot_or_eq_top hG |>.resolve_right
      fun h => hrange (top_le_iff.1 (h ▸ hYp))
  have hcY : c ∉ Y := fun h => hc (by simpa [hbot] using AddSubgroup.subset_closure h)
  rw [← ZMod.natCast_eq_zero_iff, ← coeff_ofSet_pow_char]
  simpa [Y] using hcY

theorem isMultiplyPretransitive_of_not_prime [IsAddCyclic C] [IsPreprimitive G C]
    (hC : ¬ (Nat.card C).Prime) : IsMultiplyPretransitive G C 2 := by
  rw [isMultiplyPretransitive_two_iff hG]
  obtain h1 | h1 := eq_or_ne (Nat.card C) 1
  · have := (Nat.card_eq_one_iff_unique.1 h1).1
    exact fun x hx => absurd (Subsingleton.elim x 0) hx
  have := Fintype.ofFinite C
  obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd h1
  have := Fact.mk hp
  have hpn : p < Nat.card C :=
    (Nat.le_of_dvd Nat.card_pos hpC).lt_of_ne fun h => hC (h ▸ hp)
  let E : AddSubgroup C := (nsmulAddMonoidHom p : C →+ C).ker
  have hE : (E : Set C).ncard ≤ p := by
    classical
    convert IsAddCyclic.card_nsmul_eq_zero_le (α := C) hp.pos
    rw [Set.ncard_eq_toFinset_card', ← Set.filter_mem_univ_eq_toFinset]
    rfl
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hpC
  have hxE : x ∈ E := by simp [E, ← hx, addOrderOf_nsmul_eq_zero]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hp.ne_one (addOrderOf_zero (G := C) ▸ hx).symm
  set T := suborbit G x
  have hout : (T \ E).Nonempty := by
    refine Set.nonempty_iff_ne_empty.2 fun h => ?_
    rw [Set.sdiff_eq_empty] at h
    rcases ((isStable_suborbit x).closure hG).eq_bot_or_eq_top hG with h' | h'
    · exact hx0 (by simpa [h'] using AddSubgroup.subset_closure (mem_suborbit_self (G := G) x))
    · have hEtop : E = ⊤ := top_le_iff.1 (h' ▸ (AddSubgroup.closure_le E).2 h)
      rw [hEtop, AddSubgroup.coe_top, Set.ncard_univ] at hE
      omega
  have hEB : (E : Set C) + (T \ E) ⊆ T \ E := by
    rintro _ ⟨e, he, y, ⟨hyT, hyE⟩, rfl⟩
    have hfiber : {z ∈ T | p • z = p • y} = T ∩ (y +ᵥ (E : Set C)) := by
      ext z
      simp [E, Set.mem_vadd_set_iff_neg_vadd_mem, neg_add_eq_zero, eq_comm]
    have hdvd := prime_dvd_ncard_nsmul_eq hG hp hpC (isStable_suborbit x) (c := p • y)
      (by simpa [E] using hyE)
    rw [hfiber] at hdvd
    have hle : (T ∩ (y +ᵥ (E : Set C))).ncard ≤ (y +ᵥ (E : Set C)).ncard :=
      Set.ncard_le_ncard Set.inter_subset_right
    have hpos : 0 < (T ∩ (y +ᵥ (E : Set C))).ncard :=
      (Set.ncard_pos).2 ⟨y, hyT, 0, E.zero_mem, add_zero y⟩
    have heq : T ∩ (y +ᵥ (E : Set C)) = y +ᵥ (E : Set C) :=
      Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by
        have := Nat.le_of_dvd hpos hdvd
        rw [Set.ncard_vadd_set] at hle ⊢
        omega)
    have hey : e + y ∈ y +ᵥ (E : Set C) := ⟨e, he, add_comm y e⟩
    rw [← heq] at hey
    exact ⟨hey.1, fun h => hyE (by simpa using E.sub_mem h he)⟩
  have hT := suborbit_eq_compl_zero_of_separating hG hx0 ⟨x, mem_suborbit_self x, hxE⟩ hout hEB
  intro y hy
  have hyT : y ∈ suborbit G x := by rw [hT]; exact hy
  exact (suborbit_eq_of_mem hyT).trans hT

end BurnsideSchur

end CFSG
