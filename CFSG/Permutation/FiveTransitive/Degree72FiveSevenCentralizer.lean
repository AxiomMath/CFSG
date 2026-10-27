module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree72FiveSevenCentralizer

open MulAction

theorem card_le_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 5 Q)
    (z : P) (hz : orderOf z = 7)
    (hfixed : Nat.card (Function.fixedPoints z.val) = 30)
    (hcomm : ∀ q : Q, z * q.val = q.val * z) : Nat.card Q ≤ 5 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hzperm : orderOf z.val = 7 := (Subgroup.orderOf_coe z).trans hz
  have hzne : z.val ≠ 1 := by intro he; rw [he,orderOf_one] at hzperm; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.property hzne
  rw [hcard] at hb
  have hp : Nat.Prime (orderOf z.val) := by rw [hzperm]; norm_num
  obtain ⟨m,hmcycle⟩ := Equiv.Perm.cycleType_prime_order hp
  have hsum := z.val.sum_cycleType
  rw [hmcycle,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzperm] at hsum
  have hsle := Finset.card_le_univ z.val.support
  rw [hcard] at hsle
  have hsupp : z.val.support.card = 42 := by
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.sum_cycleType,hcard] at hfixed
    omega
  have hmlo : 5 ≤ m := by omega
  have hmhi : m ≤ 5 := by omega
  have hsupport : 42 ≤ z.val.support.card := by omega
  let f : Q →* Equiv.Perm X := P.subtype.comp Q.subtype
  let K := Subgroup.centralizer ({z.val} : Set (Equiv.Perm X))
  have hmem : ∀ q : Q, f q ∈ K := by
    intro q
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (hcomm q).symm
  let i : Q →* K := f.codRestrict K hmem
  let supportMap : Q →* Equiv.Perm z.val.support :=
    (Degree28ThirteenCentralizer.centralizerToSupport z.val).comp i
  let zSupport : Equiv.Perm z.val.support :=
    z.val.subtypePerm (fun _ => z.val.apply_mem_support)
  let L := Subgroup.centralizer ({zSupport} : Set (Equiv.Perm z.val.support))
  have hsupportMem : ∀ q : Q, supportMap q ∈ L := by
    intro q
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change q.val.val (z.val x.val) = z.val (q.val.val x.val)
    exact congrArg (fun a : P => a.val x.val) (hcomm q).symm
  let j : Q →* L := supportMap.codRestrict L hsupportMem
  have hinj : Function.Injective j := by
    apply (injective_iff_map_eq_one _).mpr
    intro q hq
    have hqSupport : supportMap q = 1 := congrArg Subtype.val hq
    have hfix : ∀ x ∈ z.val.support, q.val.val x = x := by
      intro x hx
      exact congrArg Subtype.val (DFunLike.congr_fun hqSupport (⟨x,hx⟩ : z.val.support))
    have hsub : q.val.val.support ⊆ z.val.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      exact fun hz => Equiv.Perm.mem_support.mp hx (hfix x hz)
    have hsmall : q.val.val.support.card ≤ 30 := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_compl,hcard] at hle
      omega
    by_contra hne
    have hpermne : q.val.val ≠ 1 := fun he => hne (Subtype.ext (Subtype.ext he))
    have hbq := HighDegreeManningSupport.degree_le_two_mul_support
      P (by omega) h5 hnotAlt q.val.property hpermne
    rw [hcard] at hbq
    omega
  have hExtend : Equiv.Perm.ofSubtype zSupport = z.val :=
    Equiv.Perm.ofSubtype_subtypePerm (fun _ => z.val.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hSupportCycle : zSupport.cycleType = z.val.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,hExtend]
  have hLnot : ¬ 25 ∣ Nat.card L := by
    rw [Equiv.Perm.nat_card_centralizer,hSupportCycle,hmcycle,hzperm,
      Fintype.card_coe,← hsum]
    interval_cases m
    norm_num
  have hd := Subgroup.card_dvd_of_injective j hinj
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have h25 : 25 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 5 (by omega : 2 ≤ e)
    exact hLnot (h25.trans hd)
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 5) he1).trans (by norm_num)

end FiveTransitive.Degree72FiveSevenCentralizer

end CFSG
