module

public import CFSG.Permutation.FiveTransitive.SylowFixedActionCore
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction
public import CFSG.Permutation.FiveTransitive.Degree58LargePrimeElevenCentralizer
import CFSG.Permutation.FiveTransitive.Degree67TwoSevenOrbit

public section

namespace CFSG

namespace FiveTransitive.Degree60ElevenDescentCentralizer

open MulAction

private theorem fixes_outside
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 60) (Q : Subgroup G) (hQ : IsPGroup 11 Q)
    (_hfixed : Nat.card (fixedPoints Q X) ≤ 27)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 7)
    (hc : g.val ∈ Subgroup.centralizer (Q : Set G))
    (x : X) (hx : x ∉ fixedPoints Q X) : g.val • x = x := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hm : Nat.card (orbit Q x) ≠ 1 := by
    intro hm
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card]))
  have he0 : 0 < e := by
    by_contra hn
    apply hm
    rw [he,show e=0 by omega,pow_zero]
  have hlo : 11 ≤ Nat.card (orbit Q x) := by
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 11) he0
  have hb := NormalizerExteriorOrbitFamily.card_mul_add_fixed_le (X := X) Q _ hm
  rw [hX] at hb
  have hsmall : Nat.card (NormalizerOrbitFamily.Family (X := X) Q (Nat.card (orbit Q x))) ≤ 6 := by
    nlinarith
  have hpres := FiveTransitive.Degree67TwoSevenOrbit.seven_fixes_family (X := X) Q _ hsmall g
    (hg ▸ pow_orderOf_eq_one g) ⟨Quotient.mk'' x,by rw [orbitRel.Quotient.orbit_mk]⟩
  have horbit : g.val • x ∈ orbit Q x := Quotient.exact (show
      (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hpres)
  apply CoprimeCentralizerOrbit.fixed_of_mem_orbit Q g.val hc ?_ x horbit
  intro r
  obtain ⟨k,hk⟩ := IsPGroup.iff_orderOf.mp hQ r
  rw [hk,show orderOf g.val = 7 by simpa only [Subgroup.orderOf_coe] using hg]
  exact Nat.Coprime.pow_left k (by decide)

private theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q) (hQcard : Nat.card Q ≤ 121)
    (hfixed : Nat.card (fixedPoints Q X) ≤ 27)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 7) : False := by
  have hc := Degree58LargePrimeElevenCentralizer.centralizes Q hQ hQcard g (hg ▸ pow_orderOf_eq_one g)
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
  omega

theorem excluded_of_fixed_sixteen
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 11 Q)
    [Fintype (FixedNormalizerAction.Fixed (X := X) Q)]
    (hfixed : Nat.card (FixedNormalizerAction.Fixed (X := X) Q) = 16)
    (hAlt : alternatingGroup (FixedNormalizerAction.Fixed (X := X) Q) ≤
      FixedNormalizerAction.Image (X := X) Q) : False := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let F := FixedNormalizerAction.Fixed (X := X) Q
  let N := FixedNormalizerAction.Normalizer Q
  let rho := toPermHom N F
  have hfix : Nat.card (fixedPoints Q X) = 16 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hfixed
  have htuple := Degree60LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    15 (by rw [hfix])
  rw [hfix] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he2 : e ≤ 2 := by
    by_contra hn
    have hpow : 11 ^ 3 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 11 (by omega : 3 ≤ e)
    have hc := hpow.trans htuple
    norm_num at hc
  have hQ121 : Nat.card Q ≤ 121 := by
    rw [he]
    exact Nat.pow_le_pow_right (by decide : 0 < 11) he2
  have hseven : 7 ∣ Nat.card rho.range :=
    (SylowFixedActionCore.odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
      (by rw [← Nat.card_eq_fintype_card]; change 7 ≤ Nat.card (FixedNormalizerAction.Fixed (X := X) Q); rw [hfixed]; decide)).trans
      (Subgroup.card_dvd_of_le hAlt)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
    (hseven.trans (Subgroup.card_range_dvd rho))
  exact excluded P hcard h5 hnotAlt Q hQ hQ121 (by rw [hfix]; decide) z hz

end FiveTransitive.Degree60ElevenDescentCentralizer

end CFSG
