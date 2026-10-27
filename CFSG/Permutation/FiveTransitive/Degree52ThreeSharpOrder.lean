module

public import CFSG.Permutation.FiveTransitive.Degree52ThreeStructure
public import CFSG.Permutation.FiveTransitive.Degree52ThreeCommutingFixed
public import CFSG.Permutation.FiveTransitive.Degree52ThreeFinalOrbitCount
public import CFSG.Permutation.FiveTransitive.SmallThreeOrbitExponent

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeSharpOrder

open MulAction SylowFixedActionCore

private theorem card_le_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) : Nat.card S ≤ 3 := by
  classical
  by_cases hS : Nat.card S = 1
  · omega
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  obtain ⟨horbit,hbound⟩ := Degree52ThreeStructure.orbit_card_three_and_bound P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hcount⟩ := Degree52ThreeSevenLift.exists_seven_exterior_fixed_three P hcard h5 hnotAlt
    (Degree52SevenFixedElements.fixed_card_three_or_ten P hcard h5 hnotAlt) s hs S hS
  have hg7 : g ^ 7 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have ha : Q.normalizerMonoidHom g = 1 := Degree43ThreeGroupSmallSevenAut.eq_one Q hQ
    (by rwa [hQcard]) _ (by rw [← map_pow,hg7,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val := congrArg Subtype.val (DFunLike.congr_fun ha q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * g.val) hh
  have hgf := Degree52SevenFixedElements.fixed_card_three_or_ten P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)
  let C := {x : fixedPoints Q X // g.val • x.val = x.val}
  change Nat.card (Function.fixedPoints g.val.val) = Nat.card C + 3 at hcount
  have hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 3 := by
    intro x
    by_cases hx : x ∈ fixedPoints Q X
    · have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hx
      rw [← Nat.card_eq_fintype_card] at h
      omega
    · rw [horbit x hx]
  have hqbound : ∀ q : Q, q ≠ 1 → Nat.card (fixedBy X q) ≤ 10 := by
    intro q hqne
    have hq3 : q ^ 3 = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
      intro y
      simpa only [one_smul] using SmallThreeOrbitExponent.cube_smul_eq hQ hsmall q y
    let L := {x : Function.fixedPoints g.val.val // q.val.val x.val = x.val}
    let i : C → L := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property q⟩
    have hi : Function.Injective i := by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : L => y.val.val) hab
    have hCL := Nat.card_le_card_of_injective i hi
    have hcases := Degree52ThreeCommutingFixed.fixed_card_seven_or_ten P hcard h5 hnotAlt g.val q.val
      (congrArg Subtype.val hg7) (congrArg Subtype.val hq3)
      (fun he => hqne (Subtype.ext he)) hgf
      (by change Nat.card (Function.fixedPoints g.val.val) ≤ Nat.card L + 3; omega)
      (hcomm q).symm
    change Nat.card (Function.fixedPoints q.val.val) ≤ 10
    omega
  let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
  have hF := (Degree52ThreeFixed.three_fixed_card_and_image P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  rw [hfixeq] at hF
  let sf := (fixedPoints Q X).toFinset
  have hsf : sf.card = 7 := by
    rw [Set.toFinset_card,← Nat.card_eq_fintype_card,hF]
  have hb := Degree52ThreeFinalOrbitCount.card_le_three hcard sf hsf
    (fun q y hy => (Set.mem_toFinset.mp hy) q) hsmall hqbound
  rwa [hQcard] at hb

theorem nine_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 9 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro h9
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have h9S := S.pow_dvd_card_of_pow_dvd_card (n := 2) h9
  have hb := card_le_three P hcard h5 hnotAlt s hs S
  have hl := Nat.le_of_dvd (Nat.card_pos (α := S)) h9S
  norm_num at hl
  omega

end FiveTransitive.Degree52ThreeSharpOrder

end CFSG
