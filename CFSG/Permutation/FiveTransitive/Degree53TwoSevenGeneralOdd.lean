module

public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralData
public import CFSG.Permutation.FiveTransitive.Degree53TwoSevenGeneralSupport
public import CFSG.Permutation.FiveTransitive.Degree52TwoOddKernel
public import CFSG.Permutation.FiveTransitive.Degree52TwoOddOrbit

public section

namespace CFSG

namespace FiveTransitive.Degree53TwoSevenGeneralOdd

open MulAction FixedNormalizerAction

private theorem exterior_fixed_mem
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 53) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (x : X) (hsmall : ∀ y : X, y ∉ orbit Q x → Nat.card (orbit Q y) ≤ 2)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hunique : ∀ y z : X, y ∉ fixedPoints Q X → z ∉ fixedPoints Q X →
      g.val • y = y → g.val • z = z → y = z)
    (y : X) (hy : y ∉ fixedPoints Q X) (hgy : g.val • y = y) : y ∈ orbit Q x := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  let O : orbitRel.Quotient Q X := Quotient.mk'' y
  have hne : Nat.card O.orbit ≠ 1 := by
    intro he
    apply hy
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [←Nat.card_eq_fintype_card]
    exact he
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O := by
    change Quotient.mk'' (g.val • y) = Quotient.mk'' y
    rw [hgy]
  have hsixteen : Nat.card (orbit Q y) = 16 :=
    Degree53TwoSevenPreserved.preserved_card_eq_sixteen hX Q hQ g hg hunique O hne hpres
  by_contra hn
  have hh := hsmall y hn
  omega

theorem exists_odd_of_card_thirty_two
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 53)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 2 Q)
    (hF : Nat.card (Fixed (X := X) Q) = 7)
    (him : let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
      alternatingGroup (Fixed (X := X) Q) ≤ Image (X := X) Q)
    (hQcard : Nat.card Q = 32) :
    ∃ z : Q, z.val.val ∉ alternatingGroup X := by
  classical
  obtain ⟨x,hO,himage,_,hsmall⟩ := Degree53TwoSevenGeneralData.exists_orbit_data P hcard h5 hnotAlt Q hQ hF him
  let f := toPermHom Q (orbit Q x)
  have hK : Nat.card f.ker = 2 := by
    have hm := f.ker.card_mul_index
    rw [Subgroup.index_ker] at hm
    change Nat.card f.ker * Nat.card f.range = Nat.card Q at hm
    change Nat.card f.range = 16 at himage
    rw [himage,hQcard] at hm
    omega
  obtain ⟨g,hg,y,hy,hunique⟩ := Degree53TwoSevenGeneralFive.exists_five_unique_exterior P Q hF him
    (Degree53FiveFree.fixed_card_eq_three P hcard h5 hnotAlt)
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hu : ∀ u v : X, u ∉ fixedPoints Q X → v ∉ fixedPoints Q X →
      g.val • u = u → g.val • v = v → u = v := by
    intro u v hu hv hgu hgv
    exact (hunique u ⟨hu,hgu⟩).trans (hunique v ⟨hv,hgv⟩).symm
  have hyO : y ∈ orbit Q x := exterior_fixed_mem
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ x hsmall g hg5 hu y hy.1 hy.2
  obtain ⟨z,hzne,hz2,hzO,hcomm⟩ := Degree52TwoOddKernel.exists_involution Q x hK g
    (Degree52TwoOddOrbit.stable Q x hO hsmall g)
  have hfixed : Nat.card (fixedPoints Q X) = 7 := by
    rw [←FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hfixg : ∀ u : X, g.val • u = u → z • u = u := by
    intro u hgu
    by_cases hf : u ∈ fixedPoints Q X
    · exact hf z
    · have he : u = y := hunique u ⟨hf,hgu⟩
      rw [he]
      exact hzO y hyO
  have hodd := Degree53TwoSevenGeneralSupport.not_mem_alternating P hcard h5 hnotAlt Q hfixed
    x hO z hzne hz2 hzO g.val (congrArg Subtype.val hg5) hcomm hfixg
  exact ⟨z,hodd⟩

end FiveTransitive.Degree53TwoSevenGeneralOdd

end CFSG
