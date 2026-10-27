module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree52SevenTwentyFourCentralizer

open MulAction Subgroup

theorem twenty_three_not_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 52)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (hu : orderOf u = 7) (hfixed : 24 ≤ Nat.card (Function.fixedPoints u.val)) :
    ¬ 23 ∣ Nat.card (Subgroup.centralizer ({u} : Set P)) := by
  classical
  let g : Equiv.Perm X := u.val
  have hg : orderOf g = 7 := (Subgroup.orderOf_coe u).trans hu
  obtain ⟨m,ht⟩ := Equiv.Perm.cycleType_prime_order (σ := g) (by rw [hg]; norm_num)
  have hsum := g.sum_cycleType
  rw [ht,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hg] at hsum
  have hne : g ≠ 1 := by intro he; rw [he,orderOf_one] at hg; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt u.property hne
  rw [hcard] at hb
  rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,u.val.sum_cycleType,hcard] at hfixed
  have hsle := Finset.card_le_univ g.support
  rw [hcard] at hsle
  change (m + 1) * 7 = u.val.support.card at hsum
  change u.val.support.card ≤ 52 at hsle
  have hm : m + 1 = 4 := by omega
  have hsupport : g.support.card = 28 := by change u.val.support.card = 28; omega
  have htype : g.cycleType = Multiset.replicate 4 7 := by rw [ht,hg,hm]
  let C := Subgroup.centralizer ({u} : Set P)
  let f : C →* Equiv.Perm X := P.subtype.comp C.subtype
  let K := Subgroup.centralizer ({g} : Set (Equiv.Perm X))
  have hmem : ∀ c : C, f c ∈ K := by
    intro c
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  let i : C →* K := f.codRestrict K hmem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree28ThirteenCentralizer.centralizerToSupport g).comp i
  let gSupport : Equiv.Perm g.support := g.subtypePerm (fun _ => g.apply_mem_support)
  let L := Subgroup.centralizer ({gSupport} : Set (Equiv.Perm g.support))
  have hsupportMem : ∀ c : C, supportMap c ∈ L := by
    intro c
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change c.val.val (g x.val) = g (c.val.val x.val)
    exact congrArg (fun a : P => a.val x.val)
      (Subgroup.mem_centralizer_singleton_iff.mp c.property)
  let j : C →* L := supportMap.codRestrict L hsupportMem
  have hinj : Function.Injective j := by
    apply (injective_iff_map_eq_one _).mpr
    intro c hc
    have hcs : supportMap c = 1 := congrArg Subtype.val hc
    have hfix : ∀ x ∈ g.support, c.val.val x = x := by
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun hcs (⟨x,hx⟩ : g.support))
    have hsub : c.val.val.support ⊆ g.supportᶜ := by
      intro x hx
      apply Finset.mem_compl.mpr
      exact fun hxg => Equiv.Perm.mem_support.mp hx (hfix x hxg)
    have hsmall : c.val.val.support.card ≤ 24 := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_compl,hcard,hsupport] at hle
      exact hle
    by_contra hne
    have hpermne : c.val.val ≠ 1 := fun he => hne (Subtype.ext (Subtype.ext he))
    have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega)
      h5 hnotAlt c.val.property hpermne
    rw [hcard] at hb
    omega
  have hExtend : Equiv.Perm.ofSubtype gSupport = g :=
    Equiv.Perm.ofSubtype_subtypePerm (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hSupportCycle : gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,hExtend]
  have hL : Nat.card L = 24 * 7 ^ 4 := by
    rw [Equiv.Perm.nat_card_centralizer,hSupportCycle,htype,Fintype.card_coe,hsupport]
    norm_num
  have hd := Subgroup.card_dvd_of_injective j hinj
  intro h23
  have hh := h23.trans hd
  rw [hL] at hh
  norm_num at hh

end FiveTransitive.Degree52SevenTwentyFourCentralizer

end CFSG
