module

public import CFSG.Permutation.FiveTransitive.Degree80FiveOrder

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoEightLifts
open MulAction FixedNormalizerAction SylowFixedActionCore

private theorem exists_prime_exterior_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (Q : Subgroup P)
    (hF : Nat.card (Fixed (X := X) Q) = 8)
    (hAlt : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (p : ℕ) (hp : p = 5 ∨ p = 7)
    (hglobal_bound : ∀ g : P, orderOf g = p →
      Nat.card (Function.fixedPoints g.val) ≤ if p = 5 then 5 else 3) :
    ∃ g : Normalizer Q, orderOf g = p ∧
      Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} ≤ 2 := by
  classical
  let _ : Fact (Nat.Prime p) := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let N := Normalizer Q
  let F := Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  change alternatingGroup F ≤ rho.range at hAlt
  change Nat.card F = 8 at hF
  have hdiv : p ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (Fact.out : Nat.Prime p)
      (by rcases hp with rfl | rfl <;> decide)
      (by rw [← Nat.card_eq_fintype_card,hF]; omega)).trans (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p
    (hdiv.trans (Subgroup.card_range_dvd rho))
  have hgp : g ^ p = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := hglobal_bound g.val ((Subgroup.orderOf_coe g).trans hg)
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  have hle5 : Nat.card (Function.fixedPoints (rho g)) ≤ 5 := by
    rcases hp with rfl | rfl <;> simp only [ite_true,show ¬(7:ℕ)=5 by decide,ite_false] at hglobal <;> omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ p = 1 := by
    funext x
    change ((rho g) ^ p) x = x
    rw [← map_pow,hgp,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := p) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % p = Fintype.card (Function.fixedPoints (rho g)) % p at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal5 : p = 5 → 3 ≤ Nat.card (Function.fixedPoints (rho g)) := by
    intro hp5
    rw [hp5] at hm
    omega
  have hlocal7 : p = 7 → 1 ≤ Nat.card (Function.fixedPoints (rho g)) := by
    intro hp7
    rw [hp7] at hm
    omega
  let B := {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x}
  let E : Function.fixedPoints (rho g) ⊕ B ≃ Function.fixedPoints g.val.val :=
    { toFun := fun t => match t with
        | Sum.inl x => ⟨x.val.val,congrArg Subtype.val x.property⟩
        | Sum.inr x => ⟨x.val,x.property.2⟩
      invFun := fun x => if hx : x.val ∈ fixedPoints Q X then
        Sum.inl ⟨⟨x.val,hfixeq.symm ▸ hx⟩,Subtype.ext x.property⟩
        else Sum.inr ⟨x.val,hx,x.property⟩
      left_inv := by
        intro t
        cases t with
        | inl x =>
          have hx : x.val.val ∈ fixedPoints Q X := hfixeq ▸ x.val.property
          simp only [hx,↓reduceDIte]
        | inr x =>
          simp only [x.property.1,↓reduceDIte]
          rfl
      right_inv := by
        intro x
        dsimp only
        split_ifs <;> rfl }
  have he := Nat.card_congr E
  rw [Nat.card_sum] at he
  refine ⟨g,hg,?_⟩
  change Nat.card B ≤ 2
  rcases hp with rfl | rfl
  · simp only [ite_true] at hglobal
    have hl := hlocal5 rfl
    omega
  · simp only [show ¬ (7 : ℕ) = 5 by decide,ite_false] at hglobal
    have hl := hlocal7 rfl
    omega

private theorem alternating_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (h5 : IsMultiplyPretransitive P X 5)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 8) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    alternatingGroup (sylowFixedPoints X P s S) ≤
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F
  · rw [← Nat.card_eq_fintype_card]; exact hF.ge.trans' (by decide)
  · rw [← Nat.card_eq_fintype_card,hF]; decide
  · rw [← Nat.card_eq_fintype_card,hF]; decide
  · rw [← Nat.card_eq_fintype_card,hF]; decide
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5 a b ha hb
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,hg⟩

theorem exists_normalizers
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 8) :
    ∃ g5 g7 : sylowNormalizer X P s S,
      g5 ^ 5 = 1 ∧ g7 ^ 7 = 1 ∧
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g5.val • x = x} ≤ 2 ∧
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g7.val • x = x} ≤ 2 := by
  have hAlt := alternating_image P h5 s hs S hF
  obtain ⟨g5,hg5,hfive⟩ := exists_prime_exterior_bound P
    (sylowImage X P s S) hF hAlt 5 (Or.inl rfl) (by
      intro g hg
      have hh := Degree80FiveOrder.fixed_card_cases P hcard h5 hnotAlt g hg
      simp only [ite_true]
      omega)
  obtain ⟨g7,hg7,hseven⟩ := exists_prime_exterior_bound P
    (sylowImage X P s S) hF hAlt 7 (Or.inr rfl) (by
      intro g hg
      simp only [show ¬ (7:ℕ)=5 by decide,ite_false]
      exact (Degree80SevenFree.fixed_card_eq_three P hcard h5 hnotAlt g hg).le)
  exact ⟨g5,g7,hg5 ▸ pow_orderOf_eq_one g5,hg7 ▸ pow_orderOf_eq_one g7,hfive,hseven⟩

end FiveTransitive.Degree80TwoEightLifts

end CFSG
