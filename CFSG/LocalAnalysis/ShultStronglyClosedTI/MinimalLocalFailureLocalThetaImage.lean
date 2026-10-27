module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LocalTheta

open scoped commutatorElement IsMulCommutative

universe u v

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem elementary_of_injective {F : Type v} [Group F] {p : ℕ}
    [IsElementaryAbelian p F] (f : G →* F) (hf : Function.Injective f) :
    IsElementaryAbelian p G := by
  have hcomm : IsMulCommutative G := ⟨⟨fun x y => hf (by simp [mul_comm])⟩⟩
  refine { toIsMulCommutative := hcomm, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply hf
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p F) (f x)

omit [Finite G] in
theorem prime_subgroup_eq_bot_of_coprime {p : ℕ} (hp : p.Prime)
    (S : Subgroup G) (hS : IsPGroup p S) (hcoprime : Nat.Coprime p (Nat.card G)) :
    S = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  apply Subgroup.eq_bot_of_card_eq
  exact hS.card_eq_or_dvd.resolve_right (fun h =>
    (hp.coprime_iff_not_dvd.mp hcoprime) (h.trans S.card_subgroup_dvd_card))

omit [Finite G] in
theorem normal_odd_supplement_quotient (I U : Subgroup G) [I.Normal]
    (hUodd : Odd (Nat.card U)) (hgen : I ⊔ U = ⊤) : Odd (Nat.card (G ⧸ I)) := by
  let q := QuotientGroup.mk' I
  let f : U →* G ⧸ I := q.comp U.subtype
  have hsurj : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective I y
    obtain ⟨i, hi, t, ht, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp
      (hgen.symm ▸ Subgroup.mem_top x)
    refine ⟨⟨t, ht⟩, ?_⟩
    change q t = q x
    have hqi : q i = 1 := (QuotientGroup.eq_one_iff i).mpr hi
    rw [← hprod, map_mul, hqi, one_mul]
  exact hUodd.of_dvd_nat (Subgroup.card_dvd_of_surjective hsurj)

theorem normal_elementary_odd_supplement_solvable (I U : Subgroup G)
    [I.Normal] [IsElementaryAbelian 2 I] (hUodd : Odd (Nat.card U))
    (hgen : I ⊔ U = ⊤) : Group.IsSolvable G := by
  let : Group.IsSolvable (G ⧸ I) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (normal_odd_supplement_quotient I U hUodd hgen)
  exact Group.isSolvable_of_subgroup_quotient I

omit [Finite G] in
theorem two_subgroup_le_normal_elementary_factor (I U : Subgroup G)
    [I.Normal] (hUodd : Odd (Nat.card U)) (hgen : I ⊔ U = ⊤)
    (S : Subgroup G) (hS : IsPGroup 2 S) : S ≤ I := by
  let q := QuotientGroup.mk' I
  have hodd := normal_odd_supplement_quotient I U hUodd hgen
  have hzero : S.map q = ⊥ := prime_subgroup_eq_bot_of_coprime Nat.prime_two
    (S.map q) (hS.map q) (Nat.coprime_two_left.mpr hodd)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have hqx : q x ∈ S.map q := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rw [hzero] at hqx
  exact Subgroup.mem_bot.mp hqx

theorem normal_odd_centralizes_elementary (I R : Subgroup G)
    [I.Normal] [R.Normal] [IsElementaryAbelian 2 I]
    (hRodd : Odd (Nat.card R)) : R ≤ Subgroup.centralizer (I : Set G) := by
  intro r hr
  apply Subgroup.mem_centralizer_iff.mpr
  intro i hi
  have hcomm := (Subgroup.commutator_le_inf R I)
    (Subgroup.commutator_mem_commutator hr hi)
  have hone : ⁅r, i⁆ = 1 := square_one_eq_one_of_mem_odd_subgroup R hRodd
    hcomm.1 (elemPow_eq_one_of_isElementaryAbelian _ hcomm.2)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

theorem normal_odd_le_odd_supplement (I U R : Subgroup G)
    [I.Normal] [R.Normal] [IsElementaryAbelian 2 I]
    (hUodd : Odd (Nat.card U)) (hRodd : Odd (Nat.card R))
    (hgen : I ⊔ U = ⊤) : R ≤ U := by
  have hcent := normal_odd_centralizes_elementary I R hRodd
  intro r hr
  obtain ⟨i, hi, t, ht, hprod⟩ := Subgroup.mem_sup_of_normal_left.mp
    (hgen.symm ▸ Subgroup.mem_top r)
  have hri : Commute r i :=
    ((Subgroup.mem_centralizer_iff.mp (hcent hr)) i hi).symm
  have hit : Commute i t := by
    rw [← hprod] at hri
    change i * t * i = i * (i * t) at hri
    exact (mul_left_cancel (by simpa only [mul_assoc] using hri)).symm
  have htodd : Odd (orderOf t) := by
    have hh := hUodd.of_dvd_nat (orderOf_dvd_natCard (⟨t, ht⟩ : U))
    change Odd (orderOf ((⟨t, ht⟩ : U) : G))
    rw [Subgroup.orderOf_coe]
    exact hh
  have hrodd : Odd (orderOf r) := by
    have hh := hRodd.of_dvd_nat (orderOf_dvd_natCard (⟨r, hr⟩ : R))
    change Odd (orderOf ((⟨r, hr⟩ : R) : G))
    rw [Subgroup.orderOf_coe]
    exact hh
  have hi2 : i ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian i hi
  have hicoprime : Nat.Coprime (orderOf i) (orderOf t) :=
    (Nat.coprime_two_left.mpr htodd).coprime_dvd_left (orderOf_dvd_of_pow_eq_one hi2)
  have hiorder : Odd (orderOf i) := hrodd.of_dvd_nat (by
    rw [← hprod, hit.orderOf_mul_eq_mul_orderOf_of_coprime hicoprime]
    exact dvd_mul_right _ _)
  have hi1 : i = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hi2) with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hiorder
      exact False.elim ((by decide : ¬ Odd 2) hiorder)
  rw [← hprod, hi1, one_mul]
  exact ht

theorem odd_kernel_elementary_image_solvable {F : Type v} [Group F] [Finite F]
    (f : G →* F) (hf : Function.Surjective f) (hkernel : Odd (Nat.card f.ker))
    (I U : Subgroup G) [I.Normal] (hUodd : Odd (Nat.card U))
    (hgen : I ⊔ U = ⊤) [IsElementaryAbelian 2 (I.map f)] : Group.IsSolvable G := by
  let : (I.map f).Normal := (inferInstance : I.Normal).map f hf
  have himagegen : I.map f ⊔ U.map f = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, f.range_eq_top_of_surjective hf]
  have hUimageodd : Odd (Nat.card (U.map f)) :=
    hUodd.of_dvd_nat (Subgroup.card_map_dvd U f)
  let : Group.IsSolvable F := normal_elementary_odd_supplement_solvable
    (I.map f) (U.map f) hUimageodd himagegen
  let : Group.IsSolvable f.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hkernel
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f
    (by rw [Subgroup.range_subtype])

omit [Finite G] in
theorem odd_kernel_elementary_image_two_subgroup {F : Type v} [Group F] [Finite F]
    (f : G →* F) (hf : Function.Surjective f) (hkernel : Odd (Nat.card f.ker))
    (I U : Subgroup G) [I.Normal] (hUodd : Odd (Nat.card U))
    (hgen : I ⊔ U = ⊤) [IsElementaryAbelian 2 (I.map f)]
    (S : Subgroup G) (hS : IsPGroup 2 S) : IsElementaryAbelian 2 S := by
  let : (I.map f).Normal := (inferInstance : I.Normal).map f hf
  have himagegen : I.map f ⊔ U.map f = ⊤ := by
    rw [← Subgroup.map_sup, hgen, Subgroup.map_top, f.range_eq_top_of_surjective hf]
  have hUimageodd : Odd (Nat.card (U.map f)) :=
    hUodd.of_dvd_nat (Subgroup.card_map_dvd U f)
  have hSimage : S.map f ≤ I.map f := two_subgroup_le_normal_elementary_factor
    (I.map f) (U.map f) hUimageodd himagegen (S.map f) (hS.map f)
  let g : S →* F := f.comp S.subtype
  have hkerodd : Odd (Nat.card g.ker) :=
    CFSG.ProperTwoGeneratedCore.odd_kernel_subgroup_restriction f hkernel S
  have hker2 : IsPGroup 2 g.ker := hS.to_subgroup g.ker
  have hkerbot : g.ker = ⊥ := g.ker.eq_bot_of_card_eq
    (hker2.card_eq_or_dvd.resolve_right hkerodd.not_two_dvd_nat)
  have hginj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hkerbot
  let e : S →* I.map f := g.codRestrict _ (fun x =>
    hSimage (Subgroup.mem_map.mpr ⟨x.val, x.property, rfl⟩))
  exact elementary_of_injective e (fun a b h => hginj (congrArg Subtype.val h))

end CFSG.ShultStronglyClosedTI.LocalTheta
