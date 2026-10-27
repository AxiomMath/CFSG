module

public import CFSG.Permutation.FiveTransitive.Degree52FiveFixerFactorization
public import CFSG.Permutation.FiveTransitive.SylowTwoFixedDegreeBounded

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoEntrance

open MulAction Subgroup FixedNormalizerAction SylowFixedActionCore

theorem fixed_six_and_image
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) = 6 ∧
      (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hbase := SylowFixedActionPrimeFree.base_card_le_fixed_degree X P s S
  rw [hs] at hbase
  change 5 ≤ Nat.card F at hbase
  have hb := SylowTwoFixedDegreeBounded.fixed_degree_le_eight_or_eq_twelve X P h5 s hs S
  change Nat.card F ≤ 8 ∨ Nat.card F = 12 at hb
  have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 2 = Nat.card F % 2 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hNexp := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hN5 : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hNexp a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  let b : Fin 5 ↪ F := (Fin.castLEEmb hbase).trans (Finite.equivFin F).symm.toEmbedding
  let t : Set F := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive N F t.ncard := by rw [ht]; exact hN5
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hnot12 : Nat.card F ≠ 12 := by
    intro hF
    have hd : 11 ∣ (fixingSubgroup N t).index := by
      rw [hi,ht,hF]
      norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial]
    exact Degree52FiveFixerFactorization.eleven_not_dvd_card P hcard h5 hnotAlt
      ((hd.trans (fixingSubgroup N t).index_dvd_card).trans (Subgroup.card_subgroup_dvd_card N))
  have hnot8 : Nat.card F ≠ 8 := by
    intro hF
    have hd : 5 ∣ (fixingSubgroup N t).index := by
      rw [hi,ht]
      exact dvd_mul_of_dvd_right (by norm_num [Nat.factorial]) _
    obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
      (hd.trans (fixingSubgroup N t).index_dvd_card)
    have hglobal := Degree52FiveFree.fixed_card_eq_two P hcard h5 hnotAlt g.val
      ((Subgroup.orderOf_coe g).trans hg)
    let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
      fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
    have hf : Function.Injective f := by
      intro x y h
      have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
      change x.val.val = y.val.val at hh
      exact Subtype.ext (Subtype.ext hh)
    have hle := Nat.card_le_card_of_injective f hf
    rw [hglobal] at hle
    let a : Function.End F := (rho g).toFun
    have ha : a ^ 5 = 1 := by
      funext x
      change ((rho g) ^ 5) x = x
      rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
      rfl
    have hmod := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
      (by simpa only [pow_one] using ha)
    change Fintype.card F % 5 = Fintype.card (Function.fixedPoints (rho g)) % 5 at hmod
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hF] at hmod
    omega
  have hF : Nat.card F = 6 := by omega
  refine ⟨hF,?_⟩
  apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
  change IsMultiplyPretransitive rho.range F (Nat.card F - 1)
  rw [hF]
  change IsMultiplyPretransitive rho.range F 5
  rw [isMultiplyPretransitive_iff]
  intro a b
  obtain ⟨g,hg⟩ := hN5.exists_smul_eq a b
  exact ⟨⟨rho g,⟨g,rfl⟩⟩,hg⟩

end FiveTransitive.Degree52TwoEntrance

end CFSG
