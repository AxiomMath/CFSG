module

public import CFSG.Permutation.FiveTransitive.Degree54SevenBound
public import CFSG.Permutation.FiveTransitive.Degree54SevenElevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree53SevenElevenAut
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore

public section

namespace CFSG

namespace FiveTransitive.Degree54SevenFixedTwelve

open MulAction SylowFixedActionCore

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (sylowFixedPoints X P s S) ≠ 12 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  intro hF
  change Nat.card F = 12 at hF
  have hFfin : Fintype.card F = 12 := by rw [← Nat.card_eq_fintype_card]; exact hF
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQfixed : Nat.card (fixedPoints Q X) = 12 := by rw [← hfixeq]; exact hF
  have hQbound := Degree54SevenBound.card_le_343_of_fixed_twelve P hcard h5 hnotAlt Q hQ hQfixed
  have hexp : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i := by
    intro a b ha hb
    obtain ⟨g,hg⟩ := h5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ X) ⟨b,hb⟩
    exact ⟨g,fun i => DFunLike.congr_fun hg i⟩
  have hN5 := sylowNormalizer_five_transitive_on_fixedPoints X P hexp s hs S
  have hNmt : IsMultiplyPretransitive N F 5 := by
    constructor
    intro a b
    obtain ⟨g,hg⟩ := hN5 a b a.injective b.injective
    exact ⟨g,DFunLike.ext _ _ hg⟩
  obtain ⟨t,_,ht⟩ := Set.exists_subset_card_eq
    (show 5 ≤ (Set.univ : Set F).ncard by simp [Set.ncard_univ,hFfin])
  have hi := IsMultiplyPretransitive.index_of_fixingSubgroup_eq (G := N) t (by rwa [ht])
  rw [hF,ht] at hi
  norm_num [Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial] at hi
  have heleven : 11 ∣ Nat.card N := (show 11 ∣ (fixingSubgroup N t).index by rw [hi]; norm_num).trans
    (fixingSubgroup N t).index_dvd_card
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 11
    heleven
  have hz11 : z ^ 11 = 1 := hz ▸ pow_orderOf_eq_one z
  have haut : Q.normalizerMonoidHom z = 1 :=
    Degree53SevenElevenAut.eq_one Q hQ hQbound _
      (by rw [← map_pow,hz11,map_one])
  have hcomm : ∀ q : Q, z.val * q.val = q.val * z.val := by
    intro q
    have hh : z.val * q.val * z.val⁻¹ = q.val :=
      congrArg Subtype.val (DFunLike.congr_fun haut q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * z.val) hh
  have hQone := Degree54SevenElevenCentralizer.card_eq_one P hcard h5 hnotAlt Q hQ z.val
    ((Subgroup.orderOf_coe z).trans hz) hcomm
  exact hS (hQcard.symm.trans hQone)

end FiveTransitive.Degree54SevenFixedTwelve

end CFSG
