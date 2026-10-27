module

public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamilyFive
public import CFSG.Permutation.FiveTransitive.CoprimeCentralizerOrbit
public import CFSG.Permutation.FiveTransitive.ThirteenGroupSmallFiveAutomorphism
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree52ThirteenCentralizer

open MulAction

private theorem centralizes
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) (hQ : IsPGroup 13 Q) (hQcard : Nat.card Q ≤ 169)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1) :
    g.val ∈ Subgroup.centralizer (Q : Set G) := by
  have ha : Q.normalizerMonoidHom g = 1 :=
    ThirteenGroupSmallFiveAutomorphism.eq_one hQ hQcard _ (by rw [← map_pow,hg,map_one])
  apply Subgroup.mem_centralizer_iff.mpr
  intro q hq
  have hh := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩).val) ha
  rw [Q.normalizerMonoidHom_apply_apply_coe] at hh
  exact ((mul_inv_eq_iff_eq_mul).mp hh).symm

private theorem fixes_outside
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 52) (Q : Subgroup G) (hQ : IsPGroup 13 Q)
    (_hfixed : Nat.card (fixedPoints Q X) ≤ 26)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 5)
    (hc : g.val ∈ Subgroup.centralizer (Q : Set G))
    (x : X) (hx : x ∉ fixedPoints Q X) : g.val • x = x := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 13) := ⟨by decide⟩
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hm : Nat.card (orbit Q x) ≠ 1 := by
    intro hm
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card]))
  have he0 : 0 < e := by
    by_contra hn
    apply hm
    rw [he,show e=0 by omega,pow_zero]
  have hlo : 13 ≤ Nat.card (orbit Q x) := by
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 13) he0
  have hb := NormalizerExteriorOrbitFamily.card_mul_add_fixed_le (X := X) Q _ hm
  rw [hX] at hb
  have hsmall : Nat.card (NormalizerOrbitFamily.Family (X := X) Q (Nat.card (orbit Q x))) ≤ 4 := by
    nlinarith
  have hpres := NormalizerExteriorOrbitFamilyFive.five_fixes_family (X := X) Q _ hsmall g
    (hg ▸ pow_orderOf_eq_one g) ⟨Quotient.mk'' x,by rw [orbitRel.Quotient.orbit_mk]⟩
  have horbit : g.val • x ∈ orbit Q x := Quotient.exact (show
      (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hpres)
  apply CoprimeCentralizerOrbit.fixed_of_mem_orbit Q g.val hc ?_ x horbit
  intro r
  obtain ⟨k,hk⟩ := IsPGroup.iff_orderOf.mp hQ r
  rw [hk,show orderOf g.val = 5 by simpa only [Subgroup.orderOf_coe] using hg]
  exact Nat.Coprime.pow_left k (by decide)

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 13 Q) (hQcard : Nat.card Q ≤ 169)
    (hfixed : Nat.card (fixedPoints Q X) ≤ 26)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 5) : False := by
  have hc := centralizes Q hQ hQcard g (hg ▸ pow_orderOf_eq_one g)
  have hsub : (fixedPoints Q X)ᶜ ⊆ Function.fixedPoints g.val.val := by
    intro x hx
    exact fixes_outside (by rwa [Nat.card_eq_fintype_card]) Q hQ hfixed g hg hc x hx
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := X),hcard] at hle
  have hne : g.val.val ≠ 1 := by
    intro hh
    have hgone : g = 1 := Subtype.ext (Subtype.ext hh)
    rw [hgone,orderOf_one] at hg
    omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
    g.val.property hne
  rw [hcard] at hb
  rw [Nat.card_eq_fintype_card (α := Function.fixedPoints g.val.val),Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard] at hle
  have horder : orderOf g.val.val = 5 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact hg
  obtain ⟨k,hk⟩ := Equiv.Perm.cycleType_prime_order (σ := g.val.val) (by rw [horder]; norm_num)
  have hsum := g.val.val.sum_cycleType
  rw [hk,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,horder] at hsum
  omega

end FiveTransitive.Degree52ThirteenCentralizer

end CFSG
