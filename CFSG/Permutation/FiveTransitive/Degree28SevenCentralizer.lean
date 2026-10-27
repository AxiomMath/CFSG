module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport

public section

namespace CFSG

namespace FiveTransitive.Degree28SevenCentralizer

open MulAction

theorem pow_seven_eq_one
    {X : Type} [Fintype X] [DecidableEq X] (hcard : Fintype.card X = 28)
    (g : Equiv.Perm X) (he : ∃ e : ℕ, orderOf g = 7 ^ e) : g ^ 7 = 1 := by
  obtain ⟨e,he⟩ := he
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [← g.lcm_cycleType]
  apply Multiset.lcm_dvd.mpr
  intro d hd
  have hdd := Equiv.Perm.dvd_of_mem_cycleType hd
  rw [he] at hdd
  obtain ⟨k,_,rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).mp hdd
  have hkbound : 7 ^ k ≤ 28 := (Multiset.single_le_sum (fun _ _ => Nat.zero_le _) _ hd).trans (hcard ▸ g.sum_cycleType_le)
  have hk : k ≤ 1 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 7) (by omega : 2 ≤ k)
    norm_num at hp
    omega
  interval_cases k <;> norm_num

theorem card_le_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (z : P) (hz : orderOf z = 7)
    (hcomm : ∀ q : Q, z * q.val = q.val * z)
    (hnofix : ∀ x ∈ fixedPoints Q X, z.val x ≠ x) : Nat.card Q ≤ 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hzperm : orderOf z.val = 7 := (Subgroup.orderOf_coe z).trans hz
  have hzne : z.val ≠ 1 := by intro he; rw [he,orderOf_one] at hzperm; omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.property hzne
  rw [hcard] at hb
  let C : SubMulAction Q X :=
    { carrier := Function.fixedPoints z.val
      smul_mem' := by
        intro q x hx
        change z.val (q.val.val x) = q.val.val x
        have he := congrArg (fun p : P => p.val x) (hcomm q)
        change z.val (q.val.val x) = q.val.val (z.val x) at he
        exact he.trans (congrArg q.val.val hx) }
  have hCempty : IsEmpty (fixedPoints Q C) := ⟨by
    rintro ⟨x,hx⟩
    have hxQ : x.val ∈ fixedPoints Q X := fun q => congrArg Subtype.val (hx q)
    exact hnofix x.val hxQ x.property⟩
  let _ := hCempty
  have hm := hQ.card_modEq_card_fixedPoints C
  rw [Nat.card_eq_zero.mpr (Or.inl hCempty)] at hm
  have hCcard : Nat.card C = 28 - z.val.support.card := by
    change Nat.card (Function.fixedPoints z.val) = _
    rw [Nat.card_eq_fintype_card,Equiv.Perm.card_fixedPoints,z.val.sum_cycleType,hcard]
  have hthree : (28 - z.val.support.card) % 3 = 0 := by
    change Nat.card C % 3 = 0 % 3 at hm
    simpa only [hCcard,Nat.zero_mod] using hm
  have hp : Nat.Prime (orderOf z.val) := by rw [hzperm]; norm_num
  obtain ⟨m,hmcycle⟩ := Equiv.Perm.cycleType_prime_order hp
  have hsum := z.val.sum_cycleType
  rw [hmcycle,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hzperm] at hsum
  have hsle := Finset.card_le_univ z.val.support
  rw [hcard] at hsle
  have hmfour : m + 1 = 4 := by omega
  have hcycle : z.val.cycleType = {7,7,7,7} := by rw [hmcycle,hmfour,hzperm]; rfl
  let f : Q →* Equiv.Perm X := P.subtype.comp Q.subtype
  let K := Subgroup.centralizer ({z.val} : Set (Equiv.Perm X))
  have hmem : ∀ q : Q, f q ∈ K := by
    intro q
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (hcomm q).symm
  let i : Q →* K := f.codRestrict K hmem
  have hinj : Function.Injective i := by
    intro q r he
    have hh : f q = f r := congrArg (fun a : K => (a : Equiv.Perm X)) he
    exact Q.subtype_injective (P.subtype_injective hh)
  have hd := Subgroup.card_dvd_of_injective i hinj
  have hKcard : Nat.card K = 57624 := by
    rw [Equiv.Perm.nat_card_centralizer,hcycle,hcard]
    norm_num
  rw [hKcard] at hd
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have he1 : e ≤ 1 := by
    by_contra hn
    have h9 : 9 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 3 (by omega : 2 ≤ e)
    have hh := h9.trans hd
    norm_num at hh
  rw [he]
  exact (Nat.pow_le_pow_right (by norm_num : 0 < 3) he1).trans (by norm_num)

end FiveTransitive.Degree28SevenCentralizer

end CFSG
