module

public import CFSG.Permutation.FiveTransitive.CentralizingSingletonFixed
public import CFSG.Permutation.FiveTransitive.Degree36OrderFiveFixed
public import CFSG.Permutation.FiveTransitive.ThreeGroupTwentySevenNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree36CentralizingFiveFree

open MulAction

theorem centralizes_and_fixed_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q) (hQcard : Nat.card Q ≤ 27)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 5)
    (hlocal : Nat.card {x : fixedPoints Q X // g.val • x.val = x.val} = 1) :
    (∀ q : Q, g.val * q.val = q.val * g.val) ∧
      Nat.card (Function.fixedPoints g.val.val) = 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hg5 : g ^ 5 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have haut : Q.normalizerMonoidHom g = 1 :=
    ThreeGroupTwentySevenNormalizer.aut_eq_one hQ hQcard _ (by rw [← map_pow,hg5,map_one])
  have hcomm (q : Q) : g.val * q.val = q.val * g.val := by
    have hh := congrArg (fun f : MulAut Q => (f q).val) haut
    rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
    exact (mul_inv_eq_iff_eq_mul).mp hh
  have hmod3 := CentralizingFixedPointCongruence.card_modEq P Q hQ g.val hcomm
  change Nat.card (Function.fixedPoints g.val.val) % 3 =
    Nat.card {x : fixedPoints Q X // g.val • x.val = x.val} % 3 at hmod3
  rw [hlocal] at hmod3
  have horder : orderOf g.val = 5 := by simpa only [Subgroup.orderOf_coe] using hg
  have hlt : Nat.card (Function.fixedPoints g.val.val) < 5 := by
    by_contra hn
    have h6 := Degree36OrderFiveFixed.fixed_card_eq_six P hcard h5 hnotAlt g.val horder (by omega)
    rw [h6] at hmod3
    norm_num at hmod3
  let A := Subgroup.zpowers g.val
  have hA : IsPGroup 5 A := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers,horder,pow_one])
  have hmod5 := hA.card_modEq_card_fixedPoints X
  rw [CentralizingSingletonFixed.fixed_zpowers] at hmod5
  change Nat.card X % 5 = Nat.card (Function.fixedPoints g.val.val) % 5 at hmod5
  rw [Nat.card_eq_fintype_card,hcard] at hmod5
  exact ⟨hcomm,by omega⟩

theorem free_outside
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (g : P) (hg : orderOf g = 5) (hgfix : Nat.card (Function.fixedPoints g.val) = 1)
    (hcomm : ∀ r : Q, g * r.val = r.val * g)
    (r : Q) (x : X) (hx : x ∉ fixedPoints Q X) (hrx : r • x = x) : r = 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  by_contra hr
  have hrne : r.val.val ≠ 1 := fun he => hr (Subtype.ext (Subtype.ext he))
  have hbound := HighDegreeManningSupport.degree_le_two_mul_support P (by omega)
    h5 hnotAlt r.val.property hrne
  rw [hcard] at hbound
  have hupper : Nat.card (fixedBy X r) ≤ 18 := by
    change Nat.card (Function.fixedPoints r.val.val) ≤ 18
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,Equiv.Perm.sum_cycleType,hcard]
    omega
  have hsub : insert x (fixedPoints Q X) ⊆ fixedBy X r := by
    intro y hy
    rcases hy with rfl | hy
    · exact hrx
    · exact hy r
  have hlower := Set.ncard_le_ncard hsub
  rw [Set.ncard_insert_of_notMem hx,← Nat.card_coe_set_eq,hQfixed,
    ← Nat.card_coe_set_eq] at hlower
  have hmod3 := (hQ.to_subgroup (Subgroup.zpowers r)).card_modEq_card_fixedPoints X
  rw [CentralizingSingletonFixed.fixed_zpowers] at hmod3
  change Nat.card X % 3 = Nat.card (fixedBy X r) % 3 at hmod3
  rw [Nat.card_eq_fintype_card,hcard] at hmod3
  have hmod5 := CentralizingSingletonFixed.fixed_card_mod_prime P g r.val hg hgfix
    (show Commute r.val g from (hcomm r).symm)
  change Nat.card (fixedBy X r) % 5 = 1 % 5 at hmod5
  omega

end FiveTransitive.Degree36CentralizingFiveFree

end CFSG
