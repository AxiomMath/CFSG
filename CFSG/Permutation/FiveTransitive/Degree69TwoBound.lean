module

public import CFSG.Permutation.FiveTransitive.Degree69TwoNoSixFixed

public section

namespace CFSG

namespace FiveTransitive.Degree69TwoBound
open MulAction Subgroup SylowFixedActionCore

private theorem free_outside_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hcommon : Nat.card (fixedPoints Q X) = 5)
    (q : Q) (x : X) (hx : x ∉ fixedPoints Q X) (hqx : q • x = x) : q = 1 := by
  classical
  let T := stabilizer Q x
  let R := T.map Q.subtype
  have hR : IsPGroup 2 R := (hQ.to_subgroup T).map Q.subtype
  have hsub : insert x (fixedPoints Q X) ⊆ fixedPoints R X := by
    intro y hy r
    obtain ⟨a,ha,har⟩ := r.property
    change Q.subtype a = r.val at har
    rcases Set.mem_insert_iff.mp hy with hy | hy
    · subst y
      change r.val • x = x
      rw [← har]
      exact ha
    · change r.val • y = y
      rw [← har]
      exact hy a
  have hRfixed : 6 ≤ Nat.card (fixedPoints R X) := by
    have hh := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem hx,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,hcommon] at hh
    omega
  have hRbot := Degree69TwoNoSixFixed.eq_bot_of_six_fixed P hcard h5 hnotAlt R hR hRfixed
  have hqR : q.val ∈ R := ⟨q,hqx,rfl⟩
  rw [hRbot,mem_bot] at hqR
  exact Subtype.ext hqR

private theorem sylow_card_dvd_sixtyFour
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S ∣ 64 := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF := (Degree69TwoFixed.fixed_five_and_image P hcard h5 hnotAlt s hs S).1
  have hcommon : Nat.card (fixedPoints Q X) = 5 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hd := FreeComplementCard.card_dvd_complement Q X (fixedPoints Q X)
    (by intro q x hx; rwa [hx q]) (free_outside_five P hcard h5 hnotAlt Q hQ hcommon)
  rw [← Nat.card_coe_set_eq,hcommon,Nat.card_eq_fintype_card (α := X),hcard] at hd
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  rwa [hQcard] at hd

theorem sylow_card_le_sixtyFour
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s)) :
    Nat.card S ≤ 64 := by
  exact Nat.le_of_dvd (by decide) (sylow_card_dvd_sixtyFour P hcard h5 hnotAlt s hs S)

end FiveTransitive.Degree69TwoBound

end CFSG
