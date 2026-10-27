module

public import CFSG.Permutation.FiveTransitive.Degree48ThreeStructure
public import CFSG.Permutation.FiveTransitive.Degree48ThreeElevenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree48ThreeOrder

open MulAction SylowFixedActionCore

private theorem card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) : Nat.card S = 3 := by
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hbound := (Degree48ThreeStructure.orbit_card_three_and_bound P hcard h5 hnotAlt s hs S hS).2
  obtain ⟨g,hg,hgfixed⟩ := Degree48ThreeElevenLift.exists_eleven_fixed_four P hcard h5 hnotAlt s hs S hS
  have hg11 : g ^ 11 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have ha : Q.normalizerMonoidHom g = 1 := ThreeGroupSmallElevenAut.eq_one Q hQ
    (by rwa [hQcard]) _ (by rw [← map_pow,hg11,map_one])
  have hcomm : ∀ q : Q, g.val * q.val = q.val * g.val := by
    intro q
    have hh : g.val * q.val * g.val⁻¹ = q.val := congrArg Subtype.val (DFunLike.congr_fun ha q)
    simpa only [mul_assoc,inv_mul_cancel,mul_one] using congrArg (fun a : P => a * g.val) hh
  have hQthree := Degree48ThreeElevenCentralizer.card_le_three P hcard h5 hnotAlt Q hQ g.val
    ((Subgroup.orderOf_coe g).trans hg) hcomm
  rw [hQcard] at hQthree
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have he1 : e ≤ 1 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 2 ≤ e)
    rw [← he] at hh
    norm_num at hh
    omega
  have hepos : e ≠ 0 := by
    intro he0
    exact hS (by rw [he,he0,pow_zero])
  rw [he,show e = 1 by omega,pow_one]

theorem nine_not_dvd_five_fixer_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 9 ∣ Nat.card (fixingSubgroup P s) := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro h9
  let S : Sylow 3 (fixingSubgroup P s) := Sylow.nonempty.some
  have h9S := S.pow_dvd_card_of_pow_dvd_card (n := 2) h9
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at h9S; norm_num at h9S
  rw [card_eq_three P hcard h5 hnotAlt s hs S hS] at h9S
  norm_num at h9S

end FiveTransitive.Degree48ThreeOrder

end CFSG
