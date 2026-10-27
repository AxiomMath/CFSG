module

public import CFSG.Permutation.FiveTransitive.Degree54FiveCentralizerEntrance
public import CFSG.Permutation.FiveTransitive.Degree54SylowFiveOrder
public import CFSG.Permutation.FiveTransitive.Degree54OrbitKernel
public import CFSG.Permutation.FiveTransitive.Degree54FiveOrbitCount
public import CFSG.Permutation.FiveTransitive.NineAlternatingImageSection

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveFree
open MulAction Subgroup SylowFixedActionCore FixedNormalizerAction

private theorem sylow_card_eq_one
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) : Nat.card S = 1 := by
  classical
  by_contra hS
  let Q := sylowImage X P s S
  let F := Fixed (X := X) Q
  let E := orbitRel.Quotient (NormalizerFixedComplement.Inside Q)
    (NormalizerFixedComplement.Domain (X := X) Q)
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype E := Fintype.ofFinite _
  have hQ : Nat.card Q = 5 := by
    rw [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective]
    exact Degree54SylowFiveOrder.sylow_card P hcard h5 hnotAlt s hs S hS
  obtain ⟨hF,hAlt⟩ := Degree54FiveSylowData.five_fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  change Nat.card F = 9 at hF
  have hfixed : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hE : Nat.card E = 9 := Degree54FiveOrbitCountCore.orbit_card_nine Q hQ
    (by rw [Nat.card_eq_fintype_card,hcard]) hfixed
  obtain ⟨K,rho,hrho,hc,hcompat⟩ :=
    Degree54FiveCentralizerEntrance.exists_subgroup Q hQ hF hAlt
  let sigma : K →* Equiv.Perm E := (NormalizerOrbitConjugacy.orbitHom (X := X) Q).comp K.subtype
  have hk : IsPGroup 5 sigma.ker := Degree54OrbitKernel.isPGroup_ker
    P hcard h5 hnotAlt Q hQ hfixed K hc
  obtain ⟨g,hg,hlocal,horbits⟩ := NineAlternatingImageSection.exists_double_lift
    hF hE rho hrho sigma hk
  have hg2 : g.val ^ 2 = 1 := congrArg Subtype.val (show g ^ 2 = 1 by rw [← hg,pow_orderOf_eq_one])
  rw [hcompat g] at hlocal
  exact Degree54FiveOrbitCount.excluded P hcard h5 hnotAlt Q hQ g.val
    (hc g) hg2 hlocal horbits

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 5 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  let S : Sylow 5 (fixingSubgroup P s) := Sylow.nonempty.some
  have hdiv : 5 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  rw [sylow_card_eq_one P hcard h5 hnotAlt s hs S] at hdiv
  norm_num at hdiv

theorem fixed_card_eq_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (g : P) (hg : orderOf g = 5) : Nat.card (Function.fixedPoints g.val) = 4 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hlt : Nat.card (Function.fixedPoints g.val) < 5 := by
    by_contra hn
    have hsize : 5 ≤ (Function.fixedPoints g.val).ncard := by
      rw [← Nat.card_coe_set_eq]
      omega
    obtain ⟨s,hsub,hs⟩ := Set.exists_subset_card_eq hsize
    let u : fixingSubgroup P s := ⟨g,(mem_fixingSubgroup_iff P).mpr (fun x hx => hsub hx)⟩
    have hu : orderOf u = 5 := (Subgroup.orderOf_coe u).symm.trans hg
    exact not_dvd_five_fixer P hcard h5 hnotAlt s hs
      (hu ▸ orderOf_dvd_natCard u)
  have hgperm : orderOf g.val = 5 := (Subgroup.orderOf_coe g).trans hg
  have hpow : g.val ^ 5 = 1 := by rw [← hgperm,pow_orderOf_eq_one]
  let a : Function.End X := g.val.toFun
  have ha : a ^ 5 = 1 := by
    funext x
    change (g.val ^ 5) x = x
    exact congrArg (fun z : Equiv.Perm X => z x) hpow
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := 5) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card X % 5 = Fintype.card (Function.fixedPoints g.val) % 5 at hm
  rw [hcard,← Nat.card_eq_fintype_card] at hm
  omega

end FiveTransitive.Degree54FiveFree

end CFSG
