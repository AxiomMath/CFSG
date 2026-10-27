module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG

namespace FiveTransitive.Research.OddIndexTwoConjugacy

open scoped Pointwise

theorem eq_one_or_eq_of_natCard_eq_two
    {Q : Type*} [Group Q]
    (hQ : Nat.card Q = 2) (a : Q) (ha : a ≠ 1) (q : Q) :
    q = 1 ∨ q = a := by
  obtain ⟨y, hy, hyuniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
  by_cases hq : q = 1
  · exact Or.inl hq
  · right
    exact (hyuniq q hq).trans (hyuniq a ha).symm

private theorem eq_generator_of_mem_zpowers_of_orderOf_eq_two
    {L : Type*} [Group L] {v x : L}
    (hv : orderOf v = 2)
    (hxmem : x ∈ Subgroup.zpowers v) (hx : x ≠ 1) :
    x = v := by
  let oneZ : Subgroup.zpowers v := ⟨1, (Subgroup.zpowers v).one_mem⟩
  let xZ : Subgroup.zpowers v := ⟨x, hxmem⟩
  let vZ : Subgroup.zpowers v := ⟨v, Subgroup.mem_zpowers v⟩
  have hcard : Nat.card (Subgroup.zpowers v) = 2 := by
    rw [Nat.card_zpowers, hv]
  obtain ⟨y, hy, hyuniq⟩ :=
    (Nat.card_eq_two_iff' oneZ).mp hcard
  have hxZ : xZ ≠ oneZ := by
    intro h
    exact hx (congrArg Subtype.val h)
  have hvne : v ≠ 1 := by
    intro hvone
    rw [hvone, orderOf_one] at hv
    norm_num at hv
  have hvZ : vZ ≠ oneZ := by
    intro h
    exact hvne (congrArg Subtype.val h)
  exact congrArg Subtype.val ((hyuniq xZ hxZ).trans (hyuniq vZ hvZ).symm)

private theorem involutions_conjugate_of_card_eq_two_mul_odd
    {L : Type*} [Group L] [Finite L]
    (m : ℕ) (hcard : Nat.card L = 2 * m) (hm : Odd m)
    {u v : L} (huTwo : u ^ 2 = 1) (hvTwo : v ^ 2 = 1)
    (huNe : u ≠ 1) (hvNe : v ≠ 1) :
    ∃ g : L, g * u * g⁻¹ = v := by
  classical
  let U : Subgroup L := Subgroup.zpowers u
  let V : Subgroup L := Subgroup.zpowers v
  have huOrder : orderOf u = 2 :=
    orderOf_eq_prime huTwo huNe
  have hvOrder : orderOf v = 2 :=
    orderOf_eq_prime hvTwo hvNe
  have hUcard : Nat.card U = 2 := by
    simpa [U] using (Nat.card_zpowers u).trans huOrder
  have hVcard : Nat.card V = 2 := by
    simpa [V] using (Nat.card_zpowers v).trans hvOrder
  have hUindex : U.index = m := by
    have hmul := U.card_mul_index
    rw [hUcard, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
  have hVindex : V.index = m := by
    have hmul := V.card_mul_index
    rw [hVcard, hcard] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) hmul
  have hUP : IsPGroup 2 U :=
    IsPGroup.of_card (n := 1) (by simpa using hUcard)
  have hVP : IsPGroup 2 V :=
    IsPGroup.of_card (n := 1) (by simpa using hVcard)
  have hUnot : ¬ 2 ∣ U.index := by
    rw [hUindex]
    exact hm.not_two_dvd_nat
  have hVnot : ¬ 2 ∣ V.index := by
    rw [hVindex]
    exact hm.not_two_dvd_nat
  let SU : Sylow 2 L := hUP.toSylow hUnot
  let SV : Sylow 2 L := hVP.toSylow hVnot
  letI : Fintype (Sylow 2 L) := Fintype.ofFinite _
  have hpre : MulAction.IsPretransitive L (Sylow 2 L) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq SU SV
  have hsub : MulAut.conj g • U = V := by
    have hcoe := congrArg (fun S : Sylow 2 L => (S : Subgroup L)) hg
    simpa [SU, SV, Sylow.coe_subgroup_smul,
      IsPGroup.toSylow_coe] using hcoe
  have hug : (MulAut.conj g) u ∈ MulAut.conj g • U :=
    Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) U
      (by simpa [U] using Subgroup.mem_zpowers u)
  rw [hsub] at hug
  have hug' : g * u * g⁻¹ ∈ Subgroup.zpowers v := by
    simpa [V] using hug
  have hne : g * u * g⁻¹ ≠ 1 := by
    have h := (MulAut.conj g).injective.ne huNe
    simpa using h
  exact ⟨g,
    eq_generator_of_mem_zpowers_of_orderOf_eq_two hvOrder hug' hne⟩

theorem exists_ker_conjugator_of_odd_kernel_card_two
    {L Q : Type*} [Group L] [Group Q] [Finite L]
    (f : L →* Q) (hf : Function.Surjective f)
    (hodd : Odd (Nat.card f.ker))
    (hQ : Nat.card Q = 2)
    {u v : L} (huTwo : u ^ 2 = 1) (hvTwo : v ^ 2 = 1)
    (huNe : u ≠ 1) (hvNe : v ≠ 1)
    (hfv : f v ≠ 1) :
    ∃ k : L, k ∈ f.ker ∧ k * u * k⁻¹ = v := by
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hf
  have hindex : f.ker.index = 2 := by
    rw [Subgroup.index_ker, hrange]
    simpa using hQ
  have hcard : Nat.card L = 2 * Nat.card f.ker := by
    rw [← f.ker.index_mul_card, hindex]
  obtain ⟨g, hguv⟩ :=
    involutions_conjugate_of_card_eq_two_mul_odd
      (Nat.card f.ker) hcard hodd huTwo hvTwo huNe hvNe
  rcases eq_one_or_eq_of_natCard_eq_two hQ (f v) hfv (f g) with hg | hg
  · exact ⟨g, MonoidHom.mem_ker.mpr hg, hguv⟩
  · refine ⟨v⁻¹ * g, ?_, ?_⟩
    · rw [MonoidHom.mem_ker, map_mul, map_inv, hg]
      simp
    · calc
        (v⁻¹ * g) * u * (v⁻¹ * g)⁻¹ =
            v⁻¹ * (g * u * g⁻¹) * v := by group
        _ = v⁻¹ * v * v := by rw [hguv]
        _ = v := by group

end FiveTransitive.Research.OddIndexTwoConjugacy

end CFSG
