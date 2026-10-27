module

public import CFSG.Permutation.FiveTransitive.Degree69FiveTwentyFourBound
public import CFSG.Permutation.FiveTransitive.CentralizingFixedPointCongruence
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.FiveGroup625ElevenAutomorphism
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree69FiveTwentyFour

open MulAction Subgroup SylowFixedActionCore

private theorem false_of_centralizing_eleven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (hF : Nat.card (fixedPoints Q X) = 24)
    (g : FixedNormalizerAction.Normalizer Q) (hg : orderOf g = 11)
    (hcomm : ∀ q : Q, g.val * q.val = q.val * g.val) : False := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let F := FixedNormalizerAction.Fixed (X := X) Q
  let _ : Fintype F := Fintype.ofFinite F
  let rho := toPermHom (FixedNormalizerAction.Normalizer Q) F
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hFc : Nat.card F = 24 := by rw [hfixeq]; exact hF
  have hm5 := CentralizingFixedPointCongruence.card_modEq P Q hQ g.val hcomm
  rw [← hfixeq] at hm5
  let e : Function.fixedPoints (rho g) ≃ {x : F // g.val.val x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e] at hm5
  change Nat.card (Function.fixedPoints g.val.val) % 5 =
    Nat.card (Function.fixedPoints (rho g)) % 5 at hm5
  have hl : Nat.card (Function.fixedPoints (rho g)) ≤ 24 := by
    have hb := Nat.card_le_card_of_injective
      (fun x : Function.fixedPoints (rho g) => x.val) Subtype.val_injective
    exact hb.trans hFc.le
  let f : Function.fixedPoints (rho g) → Function.fixedPoints g.val.val :=
    fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg (fun z : Function.fixedPoints g.val.val => z.val) h
    change x.val.val = y.val.val at hh
    exact Subtype.ext (Subtype.ext hh)
  have hle := Nat.card_le_card_of_injective f hf
  have hgperm : orderOf g.val.val = 11 :=
    (Subgroup.orderOf_coe g.val).trans ((Subgroup.orderOf_coe g).trans hg)
  have hne : g.val.val ≠ 1 := by intro he; rw [he,orderOf_one] at hgperm; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt g.val.property hne
  rw [hcard] at hb
  have hglobal : Nat.card (Function.fixedPoints g.val.val) ≤ 34 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard]
    have hs := Finset.card_le_univ g.val.val.support
    rw [hcard] at hs
    omega
  let a : Function.End F := (rho g).toFun
  have ha : a ^ 11 = 1 := by
    funext x
    change ((rho g) ^ 11) x = x
    rw [← map_pow,← hg,pow_orderOf_eq_one,map_one]
    rfl
  have hmF := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 11) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card F % 11 = Fintype.card (Function.fixedPoints (rho g)) % 11 at hmF
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hFc] at hmF
  let b : Function.End X := g.val.val.toFun
  have hb : b ^ 11 = 1 := by
    funext x
    change ((g ^ 11).val.val) x = x
    rw [← hg,pow_orderOf_eq_one]
    rfl
  have hmX := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 11) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card X % 11 = Fintype.card (Function.fixedPoints g.val.val) % 11 at hmX
  rw [hcard,← Nat.card_eq_fintype_card] at hmX
  omega

theorem fixed_ne_twentyFour
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) :
    Nat.card (sylowFixedPoints X P s S) ≠ 24 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro hF
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 24 := by rwa [← hfixeq]
  have hbound := Degree69FiveTwentyFourBound.card_le_one_twenty_five
    P hcard h5 hnotAlt Q hQ hfixed
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
  have hsize : 5 ≤ Nat.card F := by change 5 ≤ Nat.card (sylowFixedPoints X P s S); omega
  let b : Fin 5 ↪ F := (Fin.castLEEmb hsize).trans (Finite.equivFin F).symm.toEmbedding
  let t : Set F := Set.range b
  have ht : t.ncard = 5 := by
    simpa only [Nat.card_fin] using Set.ncard_range_of_injective b.injective
  have htrans : IsMultiplyPretransitive N F t.ncard := by rw [ht]; exact hN5
  have hi := htrans.index_of_fixingSubgroup_eq t
  have hd : 11 ∣ (fixingSubgroup N t).index := by
    rw [hi,ht]
    change 11 ∣ (Nat.card (sylowFixedPoints X P s S)).choose 5 * Nat.factorial 5
    rw [hF]
    norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 11
    (hd.trans (fixingSubgroup N t).index_dvd_card)
  have haut : Q.normalizerMonoidHom g = 1 :=
    FiveGroup625ElevenAutomorphism.eq_one hQ (by omega) _
      (by rw [← map_pow,← hg,pow_orderOf_eq_one,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using
      congrArg (fun a : P => a * g.val) hh
  exact false_of_centralizing_eleven P hcard h5 hnotAlt Q hQ hfixed g hg hcomm

end FiveTransitive.Degree69FiveTwentyFour

end CFSG
