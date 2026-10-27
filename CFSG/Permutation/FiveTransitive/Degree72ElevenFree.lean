module

public import CFSG.Permutation.FiveTransitive.Degree72ThreeFree
public import CFSG.Permutation.FiveTransitive.CyclicElevenCentralizerNine
public import CFSG.Permutation.FiveTransitive.CentralizerFreeExterior

public section

namespace CFSG

namespace FiveTransitive.Degree72ElevenFree
open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 11 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  intro hd
  let S : Sylow 11 (fixingSubgroup P s) := Sylow.nonempty.some
  have hS11 : 11 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 1) hd
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hS11; norm_num at hS11
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hQcard : Nat.card Q = 11 := by
    rw [Subgroup.card_map_of_injective (fixingSubgroup P s).subtype_injective]
    exact Degree72ElevenCyclic.card_eq_eleven P hcard h5 hnotAlt s hs S hS
  have hF : Nat.card F = 6 := Degree72ElevenFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  have hN9 : 9 ∣ Nat.card N := by
    have hj := Degree72ElevenFixed.image_eq_top P hcard h5 hnotAlt s hs S hS
    have hh : 9 ∣ Nat.card (toPermHom N F).range := by
      rw [hj,Subgroup.card_top,Nat.card_perm,hF]
      norm_num [Nat.factorial]
    exact hh.trans (Subgroup.card_range_dvd _)
  let C := centralizer (Q : Set P)
  have hC9 : 9 ∣ Nat.card C := CyclicElevenCentralizerNine.nine_dvd Q hQcard hN9
  let T : Sylow 3 C := Sylow.nonempty.some
  let A : Subgroup P := (T : Subgroup C).map C.subtype
  have hAc : Nat.card A = Nat.card T := Subgroup.card_map_of_injective C.subtype_injective
  have hA9 : 9 ∣ Nat.card A := by
    rw [hAc]
    exact T.pow_dvd_card_of_pow_dvd_card (n := 2) hC9
  have hA : IsPGroup 3 A := T.isPGroup'.map C.subtype
  have hAC : A ≤ C := by rintro a ⟨c,hc,rfl⟩; exact c.property
  have hcomm (a : A) (q : Q) : a.val * q.val = q.val * a.val :=
    (Subgroup.mem_centralizer_iff.mp (hAC a.property) q.val q.property).symm
  have hfix (a : A) (ha : a ≠ 1) : Nat.card (fixedBy X a.val) ≤ 4 := by
    by_contra hn
    have hsize : 5 ≤ (fixedBy X a.val).ncard := by rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨t,ht,htc⟩ := Set.exists_subset_card_eq hsize
    let u : fixingSubgroup P t := ⟨a.val,(mem_fixingSubgroup_iff P).mpr (fun x hx => ht hx)⟩
    obtain ⟨e,he⟩ := IsPGroup.iff_orderOf.mp hA a
    have hepos : 1 ≤ e := by
      by_contra he0
      have h1 : orderOf a = 1 := by rw [he,show e=0 by omega,pow_zero]
      exact ha (orderOf_eq_one_iff.mp h1)
    have ha3 : 3 ∣ orderOf a := by rw [he]; exact dvd_pow_self 3 (by omega)
    have hu : orderOf u = orderOf a := (Subgroup.orderOf_coe u).symm.trans (Subgroup.orderOf_coe a)
    have hu3 : 3 ∣ orderOf u := hu ▸ ha3
    exact Degree72ThreeFree.not_dvd_five_fixer P hcard h5 hnotAlt t htc
      (hu3.trans (orderOf_dvd_natCard u))
  have hQ : IsPGroup 11 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hn : Nat.card X < 11 ^ 2 := by rw [Nat.card_eq_fintype_card,hcard]; decide
  have hdiv := CentralizerFreeExterior.card_dvd_complement Q A 4 hcomm
    (fun x hx => by rw [Degree72LargePrimeOrbitSize.card_eq_prime 11 (by decide) hQ hn x hx]; decide) hfix
  have hf : Nat.card (fixedPoints Q X) = 6 := by rw [← FixedNormalizerAction.fixed_eq Q]; exact hF
  rw [Nat.card_eq_fintype_card (α := X),hcard,hf] at hdiv
  have hfalse : 9 ∣ 66 := hA9.trans hdiv
  norm_num at hfalse

end FiveTransitive.Degree72ElevenFree

end CFSG
