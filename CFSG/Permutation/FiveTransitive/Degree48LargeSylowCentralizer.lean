module

public import CFSG.Permutation.FiveTransitive.Degree48LargeSylowData
public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree48LargeSylowCentralizer

open MulAction Subgroup

private theorem centralizer_card_dvd_power
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 47 ∨ p = 23 ∨ p = 11)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ (48 / p).factorial * p ^ (48 / p) := by
  classical
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl | rfl <;> norm_num⟩
  have hS := Degree48LargeSylowData.sylow_card P hcard h5 hp hfree S
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huP : orderOf u.val = p := (Subgroup.orderOf_coe u).trans (hu.trans hS)
  have htype := Degree48LargeSylowData.element_cycle_type P hcard h5 hp hfree u.val huP
  let C := Subgroup.centralizer (S : Set P)
  let g : Equiv.Perm X := u.val.val
  have hsupport : g.support.card = (48 / p) * p := by
    rw [← g.sum_cycleType,htype,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id]
  let f : C →* Equiv.Perm X := P.subtype.comp C.subtype
  let K := Subgroup.centralizer ({g} : Set (Equiv.Perm X))
  have hmem : ∀ c : C, f c ∈ K := by
    intro c
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val ((c.property u.val u.property).symm)
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
    exact congrArg (fun a : P => a.val x.val) ((c.property u.val u.property).symm)
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
    have hsmall : c.val.val.support.card ≤ 4 := by
      have hle := Finset.card_le_card hsub
      rw [Finset.card_compl,hcard,hsupport] at hle
      rcases hp with rfl | rfl | rfl <;> omega
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
  have hL : Nat.card L = (48 / p).factorial * p ^ (48 / p) := by
    rw [Equiv.Perm.nat_card_centralizer,hSupportCycle,htype,Fintype.card_coe,hsupport]
    rcases hp with rfl | rfl | rfl <;> norm_num
  have hd := Subgroup.card_dvd_of_injective j hinj
  rwa [hL] at hd

theorem remove_prime_powers
    {n p m k : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hm : m ≠ 0)
    (hd : n ∣ p ^ k * m) (hle : n.factorization p ≤ 1) : n ∣ p * m := by
  apply (Nat.factorization_le_iff_dvd hn (mul_ne_zero hp.ne_zero hm)).mp
  intro q
  have hb := ((Nat.factorization_le_iff_dvd hn
    (mul_ne_zero (pow_ne_zero _ hp.ne_zero) hm)).mpr hd) q
  rw [Nat.factorization_mul hp.ne_zero hm,Finsupp.add_apply]
  by_cases hq : q = p
  · subst q
    rw [hp.factorization,Finsupp.single_eq_same]
    omega
  · rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm,Finsupp.add_apply,
      Nat.factorization_pow,Finsupp.smul_apply,hp.factorization,Finsupp.single_apply] at hb
    rw [hp.factorization,Finsupp.single_apply]
    simp only [Ne.symm hq,ite_false,smul_zero,zero_add] at hb ⊢
    exact hb

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 48)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 47 ∨ p = 23 ∨ p = 11)
    (hfree : ∀ s : Set X, s.ncard = 5 → ¬ p ∣ Nat.card (fixingSubgroup P s))
    (S : Sylow p P) : Nat.card (Subgroup.centralizer (S : Set P)) ∣ p * (48 / p).factorial := by
  have hprime : p.Prime := by rcases hp with rfl | rfl | rfl <;> norm_num
  have hbound := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (S : Set P)))) p
  rw [Degree48LargeSylowData.factorization_eq_one P hcard h5 hp hfree] at hbound
  apply remove_prime_powers hprime Nat.card_pos.ne' (Nat.factorial_ne_zero _)
  · rw [mul_comm]
    exact centralizer_card_dvd_power P hcard h5 hnotAlt hp hfree S
  · exact hbound

end FiveTransitive.Degree48LargeSylowCentralizer

end CFSG
