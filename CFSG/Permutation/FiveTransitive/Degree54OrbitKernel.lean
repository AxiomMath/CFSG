module

public import CFSG.Permutation.FiveTransitive.CentralizingOrbitExponent
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitConjugacy
public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree54OrbitKernel
open MulAction NormalizerFixedComplement

private theorem pow_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : Nat.card Q = 5)
    (hF : Nat.card (fixedPoints Q X) = 9)
    (g : Normalizer Q) (hc : ∀ q : Q, Commute g.val q.val)
    (horbit : NormalizerOrbitConjugacy.orbitHom (X := X) Q g = 1) : g ^ 5 = 1 := by
  classical
  have hQpow : ∀ q : Q, q ^ 5 = 1 := by intro q; rw [← hQ]; exact pow_card_eq_one'
  have hfixed (x : X) (hx : x ∉ fixedPoints Q X) : (g.val ^ 5) • x = x := by
    apply CentralizingOrbitExponent.pow_smul_eq Q 5 hQpow g.val hc x
    let y : Domain (X := X) Q := ⟨x,hx⟩
    have he := DFunLike.congr_fun horbit (Quotient.mk'' y)
    change (Quotient.mk'' (g • y) : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) =
      Quotient.mk'' y at he
    have ho : g • y ∈ orbit (Inside Q) y := Quotient.exact he
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp ho
    refine ⟨⟨q.val.val,q.property⟩,?_⟩
    exact (congrArg Subtype.val hq).symm
  have hsub : (g.val.val ^ 5).support ⊆ (fixedPoints Q X).toFinite.toFinset := by
    intro x hx
    apply ((fixedPoints Q X).toFinite.mem_toFinset).mpr
    by_contra hn
    exact Equiv.Perm.mem_support.mp hx (hfixed x hn)
  have hsmall : (g.val.val ^ 5).support.card ≤ 9 := by
    have hh := Finset.card_le_card hsub
    rwa [← Set.ncard_eq_toFinset_card, ← Nat.card_coe_set_eq, hF] at hh
  have he : g.val.val ^ 5 = 1 := by
    by_contra hn
    have hb := HighDegreeManningSupport.degree_le_two_mul_support
      P (by omega) h5 hnotAlt (P.pow_mem g.val.property 5) hn
    rw [hcard] at hb
    omega
  exact Subtype.ext (Subtype.ext he)

theorem isPGroup_ker
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : Nat.card Q = 5)
    (hF : Nat.card (fixedPoints Q X) = 9)
    (K : Subgroup (Normalizer Q))
    (hc : ∀ g : K, ∀ q : Q, Commute g.val.val q.val) :
    IsPGroup 5 ((NormalizerOrbitConjugacy.orbitHom (X := X) Q).comp K.subtype).ker := by
  intro g
  refine ⟨1,?_⟩
  rw [pow_one]
  apply Subtype.ext
  apply Subtype.ext
  exact pow_eq_one P hcard h5 hnotAlt Q hQ hF g.val.val (hc g.val) g.property

end FiveTransitive.Degree54OrbitKernel

end CFSG
