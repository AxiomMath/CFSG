module

public import CFSG.Permutation.FiveTransitive.Degree79TwoSevenFixity

public section

namespace CFSG

namespace FiveTransitive.Degree79TwoSevenElements
open MulAction SylowFixedActionCore Degree79TwoSevenFixity

theorem exists_three_exterior_zero
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (hthree : ∀ t : Set X, t.ncard = 5 → ¬ 3 ∣ Nat.card (fixingSubgroup P t))
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 7) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 3 ∧
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} = 0 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hN5 := normalizer_five P h5 s hs S
  change Nat.card F = 7 at hF
  obtain ⟨t,_,ht⟩ := Set.exists_subset_card_eq
    (show 4 ≤ (Set.univ : Set F).ncard by rw [Set.ncard_univ,hF]; decide)
  let H := fixingSubgroup N t
  let C : SubMulAction H F := SubMulAction.ofFixingSubgroup N t
  let _ : MulAction H C := SubMulAction.mulAction C
  let _ : Fintype C := Fintype.ofFinite _
  have hC : Nat.card C = 3 := by
    change Nat.card (tᶜ : Set F) = 3
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,hF]
  have hH1 : IsMultiplyPretransitive H C 1 := by
    let _ : IsMultiplyPretransitive N F 5 := hN5
    apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (m := 1) (n := 5) N t
    omega
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive H C 1
    (by rw [← Nat.card_eq_fintype_card,hC]; decide) hH1
  rw [← Nat.card_eq_fintype_card,hC] at hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
    ((by norm_num : 3 ∣ (3 : ℕ).descFactorial 1).trans hd)
  let g : N := u.val
  have hg : orderOf g = 3 := (Subgroup.orderOf_coe u).trans hu
  have hlocal : 4 ≤ Nat.card (Function.fixedPoints (rho g)) := by
    have hsub : t ⊆ Function.fixedPoints (rho g) := by
      intro x hx
      exact (mem_fixingSubgroup_iff N).mp u.property x hx
    have hh := Set.ncard_le_ncard hsub
    rwa [ht,← Nat.card_coe_set_eq] at hh
  have hglobal := fixed_card_lt_five P 3 hthree g.val ((Subgroup.orderOf_coe g).trans hg)
  have hsum := fixed_card_split P s S g
  change Nat.card (Function.fixedPoints (rho g)) +
    Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} =
    Nat.card (Function.fixedPoints g.val.val) at hsum
  exact ⟨g,hg,by omega⟩

theorem exists_five_or_seven_exterior_le_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5)
    (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7)
    (hfree : ∀ t : Set X, t.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P t))
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 7) :
    ∃ g : sylowNormalizer X P s S, orderOf g = p ∧
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} ≤ 2 := by
  classical
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hN5 := normalizer_five P h5 s hs S
  change Nat.card F = 7 at hF
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
    (by rw [← Nat.card_eq_fintype_card,hF]; decide) hN5
  rw [← Nat.card_eq_fintype_card,hF] at hd
  have hpdiv : p ∣ (7 : ℕ).descFactorial 5 := by
    rcases hp with rfl | rfl <;> norm_num [Nat.descFactorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p (hpdiv.trans hd)
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := fixed_card_lt_five P p hfree g.val ((Subgroup.orderOf_coe g).trans hg)
  have hsum := fixed_card_split P s S g
  change Nat.card (Function.fixedPoints (rho g)) +
    Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} =
    Nat.card (Function.fixedPoints g.val.val) at hsum
  have hmlocal := fixed_mod p (rho g) (by rw [← map_pow,hgp,map_one])
  rw [hF] at hmlocal
  have hmglobal := fixed_mod p g.val.val (congrArg (fun z : N => z.val.val) hgp)
  rw [Nat.card_eq_fintype_card (α := X),hcard] at hmglobal
  refine ⟨g,hg,?_⟩
  rcases hp with rfl | rfl <;> omega

end FiveTransitive.Degree79TwoSevenElements

end CFSG
