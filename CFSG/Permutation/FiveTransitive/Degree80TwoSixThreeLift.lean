module

public import CFSG.Permutation.FiveTransitive.Degree80ThreeNoSixFixed

public section

namespace CFSG

namespace FiveTransitive.Degree80TwoSixThreeLift

open MulAction SylowFixedActionCore

theorem exists_three_two_exterior
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hF : Nat.card (sylowFixedPoints X P s S) = 6) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 3 ∧
      Nat.card (Function.fixedPoints
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S) g)) = 3 ∧
      Nat.card {x : X // x ∉ fixedPoints (sylowImage X P s S) X ∧ g.val • x = x} = 2 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  change Nat.card F = 6 at hF
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 : IsMultiplyPretransitive N F 5 :=
    FiveTransitive.isMultiplyPretransitive_of_explicit N F 5
      (sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S)
  obtain ⟨t,_,ht⟩ := Set.exists_subset_card_eq
    (show 3 ≤ (Set.univ : Set F).ncard by rw [Set.ncard_univ,hF]; decide)
  let H := fixingSubgroup N t
  let C : SubMulAction H F := SubMulAction.ofFixingSubgroup N t
  let _ : MulAction H C := SubMulAction.mulAction C
  let _ : Fintype C := Fintype.ofFinite _
  have hC : Nat.card C = 3 := by
    change Nat.card (tᶜ : Set F) = 3
    rw [Nat.card_coe_set_eq,Set.ncard_compl,ht,hF]
  have hH2 : IsMultiplyPretransitive H C 2 := by
    let _ : IsMultiplyPretransitive N F 5 := hN5
    apply SubMulAction.ofFixingSubgroup.isMultiplyPretransitive (m := 2) (n := 5) N t
    omega
  have hd := FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive H C 2
    (by rw [← Nat.card_eq_fintype_card,hC]; decide) hH2
  rw [← Nat.card_eq_fintype_card,hC] at hd
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) 3
    ((by norm_num : 3 ∣ (3 : ℕ).descFactorial 2).trans hd)
  let g : N := u.val
  have hg : orderOf g = 3 := (Subgroup.orderOf_coe u).trans hu
  have htlocal : 3 ≤ Nat.card (Function.fixedPoints (rho g)) := by
    have hsub : t ⊆ Function.fixedPoints (rho g) := by
      intro x hx
      exact (mem_fixingSubgroup_iff N).mp u.property x hx
    have hh := Set.ncard_le_ncard hsub
    rwa [ht,← Nat.card_coe_set_eq] at hh
  have hg5 : g ^ 3 = 1 := hg ▸ pow_orderOf_eq_one g
  have hglobal := Degree80ThreeNoSixFixed.fixed_card_cases P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  have hgloballe : Nat.card (Function.fixedPoints g.val.val) ≤ 5 := by omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 3 = 1 := by
    funext x
    change ((rho g) ^ 3) x = x
    rw [← map_pow,hg5,map_one]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 3) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 3 = Fintype.card (Function.fixedPoints (rho g)) % 3 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hm
  have hlocal : Nat.card (Function.fixedPoints (rho g)) = 3 := by omega
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
  have hB : Nat.card B = 2 := by
    have he := Nat.card_congr E
    rw [Nat.card_sum,hlocal] at he
    omega
  exact ⟨g,hg,hlocal,hB⟩

end FiveTransitive.Degree80TwoSixThreeLift

end CFSG
