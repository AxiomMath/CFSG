module

public import CFSG.Permutation.FiveTransitive.OddFourStabilizerLifts
public import CFSG.Permutation.FiveTransitive.OddIndexTwoConjugacy
public import CFSG.Permutation.FiveTransitive.OddFourCentralizer

public section

namespace CFSG

namespace FiveTransitive.Research.OddFourCorrection

open scoped Pointwise
open Research.OddFourStabilizerLifts
open Research.OddIndexTwoConjugacy
open Research.OddFourCentralizer
open Research.SharpFourDegreeCompletion

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

@[expose] noncomputable def rangeBasePerm (e : Fin 4 ↪ X)
    (sigma : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Set.range e : Set X) :=
  (baseRangeEquiv e).permCongrHom sigma

theorem mem_baseSetwiseStabilizer_of_base_perm
    (e : Fin 4 ↪ X) (z : G) (sigma : Equiv.Perm (Fin 4))
    (hz : ∀ i, z • e i = e (sigma i)) :
    z ∈ baseSetwiseStabilizer (G := G) e := by
  rw [MulAction.mem_stabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    change z • e i ∈ Set.range e
    rw [hz]
    exact ⟨sigma i, rfl⟩
  · rintro _ ⟨i, rfl⟩
    refine ⟨e (sigma⁻¹ i), ⟨sigma⁻¹ i, rfl⟩, ?_⟩
    change z • e (sigma⁻¹ i) = e i
    rw [hz]
    exact congrArg e (sigma.apply_symm_apply i)

theorem baseSetwisePermHom_eq_rangeBasePerm
    (e : Fin 4 ↪ X) (z : G) (sigma : Equiv.Perm (Fin 4))
    (hz : ∀ i, z • e i = e (sigma i)) :
    baseSetwisePermHom (G := G) e
        ⟨z, mem_baseSetwiseStabilizer_of_base_perm e z sigma hz⟩ =
      rangeBasePerm e sigma := by
  apply Equiv.ext
  intro x
  obtain ⟨i, rfl⟩ := (baseRangeEquiv e).surjective x
  apply Subtype.ext
  change z • e i =
    ((rangeBasePerm e sigma (baseRangeEquiv e i) : Set.range e) : X)
  rw [hz]
  simp [rangeBasePerm]
  rw [baseRangeEquiv, Equiv.ofInjective_apply]

private theorem eq_one_of_mem_odd_subgroup_of_sq_eq_one
    (H : Subgroup G) (hodd : Odd (Nat.card H))
    (x : G) (hx : x ∈ H) (hxTwo : x ^ 2 = 1) :
    x = 1 := by
  by_contra hxNe
  have hxOrder : orderOf x = 2 := orderOf_eq_prime hxTwo hxNe
  have hdvd := H.orderOf_dvd_natCard hx
  rw [hxOrder] at hdvd
  exact hodd.not_two_dvd_nat hdvd

theorem sameBaseInvolutionConjugacy_of_odd_pointwiseStabilizer
    (e : Fin 4 ↪ X)
    (hodd : Odd (Nat.card (MulAction.stabilizer G e))) :
    SameBaseInvolutionConjugacy (G := G) e := by
  classical
  intro u v huTwo hvTwo hsame
  by_cases huOne : u = 1
  · subst u
    have hvfix : ∀ i, v • e i = e i := by
      intro i
      simpa using (hsame i).symm
    have hvMem : v ∈ MulAction.stabilizer G e := by
      rw [MulAction.mem_stabilizer_iff]
      apply Function.Embedding.ext
      exact hvfix
    have hvOne := eq_one_of_mem_odd_subgroup_of_sq_eq_one
      (MulAction.stabilizer G e) hodd v hvMem hvTwo
    subst v
    exact ⟨1, (MulAction.stabilizer G e).one_mem, by simp⟩
  have hvOne : v ≠ 1 := by
    intro hv
    subst v
    have hufix : ∀ i, u • e i = e i := by
      intro i
      simpa using hsame i
    have huMem : u ∈ MulAction.stabilizer G e := by
      rw [MulAction.mem_stabilizer_iff]
      apply Function.Embedding.ext
      exact hufix
    exact huOne (eq_one_of_mem_odd_subgroup_of_sq_eq_one
      (MulAction.stabilizer G e) hodd u huMem huTwo)
  let r : G := v * u
  have hrfix : ∀ i, r • e i = e i := by
    intro i
    change (v * u) • e i = e i
    rw [mul_smul, hsame]
    rw [← mul_smul, ← pow_two, hvTwo, one_smul]
  let H : Subgroup G := MulAction.stabilizer G e
  let rH : H := ⟨r, by
    rw [MulAction.mem_stabilizer_iff]
    apply Function.Embedding.ext
    exact hrfix⟩
  have hrOrderOdd : Odd (orderOf rH) := by
    apply Odd.of_dvd_nat hodd
    exact orderOf_dvd_natCard rH
  let Z : Subgroup H := Subgroup.zpowers rH
  let rZ : Z := ⟨rH, Subgroup.mem_zpowers rH⟩
  have hZOdd : Odd (Nat.card Z) := by
    change Odd (Nat.card (Subgroup.zpowers rH))
    rw [Nat.card_zpowers]
    exact hrOrderOdd
  have hcoprime : (Nat.card Z).Coprime 2 :=
    Nat.coprime_two_right.mpr hZOdd
  obtain ⟨kZ, hkZ⟩ :=
    (Nat.Coprime.pow_left_bijective (G := Z) hcoprime).2 rZ
  let kH : H := kZ
  let k : G := kH
  have hkSqH : kH ^ 2 = rH := congrArg Subtype.val hkZ
  have hkSq : k ^ 2 = r := congrArg Subtype.val hkSqH
  obtain ⟨n, hnH⟩ := Subgroup.mem_zpowers_iff.mp kZ.prop
  have hnG : r ^ n = k := congrArg Subtype.val hnH
  have huOrder : orderOf u = 2 := orderOf_eq_prime huTwo huOne
  have hvOrder : orderOf v = 2 := orderOf_eq_prime hvTwo hvOne
  have huInv : u⁻¹ = u := inv_eq_self_of_orderOf_eq_two huOrder
  have hvInv : v⁻¹ = v := inv_eq_self_of_orderOf_eq_two hvOrder
  have huu : u * u = 1 := by simpa [pow_two] using huTwo
  have hur : u * r * u⁻¹ = r⁻¹ := by
    dsimp only [r]
    rw [mul_inv_rev, huInv, hvInv]
    calc
      u * (v * u) * u = u * v * (u * u) := by group
      _ = u * v := by rw [huu, mul_one]
  have huk : u * k * u⁻¹ = k⁻¹ := by
    calc
      u * k * u⁻¹ = u * (r ^ n) * u⁻¹ := by rw [hnG]
      _ = (MulAut.conj u) (r ^ n) := by rw [MulAut.conj_apply]
      _ = ((MulAut.conj u) r) ^ n := map_zpow (MulAut.conj u) r n
      _ = (u * r * u⁻¹) ^ n := by rw [MulAut.conj_apply]
      _ = (r⁻¹) ^ n := by rw [hur]
      _ = (r ^ n)⁻¹ := inv_zpow r n
      _ = k⁻¹ := by rw [hnG]
  have huk' : u * k * u = k⁻¹ := by simpa only [huInv] using huk
  have hukInv : u * k⁻¹ * u = k := by
    have h := congrArg Inv.inv huk'
    have h' : u * (k⁻¹ * u) = k := by
      simpa only [mul_inv_rev, inv_inv, huInv] using h
    exact (mul_assoc u k⁻¹ u).trans h'
  have huKInv : u * k⁻¹ = k * u := by
    calc
      u * k⁻¹ = (u * k⁻¹ * u) * u := by
        rw [mul_assoc, huu, mul_one]
      _ = k * u := by rw [hukInv]
  refine ⟨k, kH.prop, ?_⟩
  calc
    k * u * k⁻¹ = k * (u * k⁻¹) := by rw [mul_assoc]
    _ = k * (k * u) := by rw [huKInv]
    _ = (k ^ 2) * u := by rw [pow_two, mul_assoc]
    _ = r * u := by rw [hkSq]
    _ = (v * u) * u := rfl
    _ = v := by rw [mul_assoc, huu, mul_one]

end FiveTransitive.Research.OddFourCorrection

end CFSG
