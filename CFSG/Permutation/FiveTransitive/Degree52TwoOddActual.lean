module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOddKernel
public import CFSG.Permutation.FiveTransitive.Degree52TwoOddOrbit
public import CFSG.Permutation.FiveTransitive.Degree52TwoOddSupport
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrderData

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOddActual

open MulAction SylowFixedActionCore

theorem exists_odd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 2 (fixingSubgroup P s))
    (hS : Nat.card S = 32) :
    ∃ z : fixingSubgroup P s, z.val.val ∉ alternatingGroup X := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 2 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = 32 := by
    rw [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective]
    exact hS
  obtain ⟨x,hO,himage,_,hsmall⟩ := Degree52TwoOrderData.exists_orbit_data P hcard h5 hnotAlt s hs S
  let f := toPermHom Q (orbit Q x)
  have hK : Nat.card f.ker = 2 := by
    have hm := f.ker.card_mul_index
    rw [Subgroup.index_ker] at hm
    change Nat.card f.ker * Nat.card f.range = Nat.card Q at hm
    change Nat.card f.range = 16 at himage
    rw [himage,hQcard] at hm
    omega
  obtain ⟨g,hg,y,hy,hunique⟩ := Degree52TwoOrbitFiveLift.exists_five_unique_exterior P hcard h5 hnotAlt s hs S
  have hg5 : g ^ 5 = 1 := hg ▸ pow_orderOf_eq_one g
  have hu : ∀ u v : X, u ∉ fixedPoints Q X → v ∉ fixedPoints Q X →
      g.val • u = u → g.val • v = v → u = v := by
    intro u v hu hv hgu hgv
    exact (hunique u ⟨hu,hgu⟩).trans (hunique v ⟨hv,hgv⟩).symm
  have hyO : y ∈ orbit Q x := Degree52TwoOddOrbit.exterior_fixed_mem
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ x hsmall g hg5 hu y hy.1 hy.2
  obtain ⟨z,hzne,hz2,hzO,hcomm⟩ := Degree52TwoOddKernel.exists_involution Q x hK g
    (Degree52TwoOddOrbit.stable Q x hO hsmall g)
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by
    rw [←FixedNormalizerAction.fixed_eq Q]
    exact (Degree52TwoEntrance.fixed_six_and_image P hcard h5 hnotAlt s hs S).1
  have hfixg : ∀ u : X, g.val • u = u → z • u = u := by
    intro u hgu
    by_cases hf : u ∈ fixedPoints Q X
    · exact hf z
    · have he : u = y := hunique u ⟨hf,hgu⟩
      rw [he]
      exact hzO y hyO
  have hodd := Degree52TwoOddSupport.not_mem_alternating P hcard h5 hnotAlt Q hfixed
    x hO z hzne hz2 hzO g.val (congrArg Subtype.val hg5) hcomm hfixg
  obtain ⟨u,_,huz⟩ := z.property
  refine ⟨u,?_⟩
  change u.val = z.val at huz
  rw [huz]
  exact hodd

end FiveTransitive.Degree52TwoOddActual

end CFSG
