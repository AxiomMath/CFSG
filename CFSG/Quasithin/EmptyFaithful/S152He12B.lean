module

public import CFSG.GroupTheory.FrobeniusNormalComplement
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical

public section

namespace CFSG.Quasithin

namespace He12

open CFSG.SectionRank.Ccomm

theorem eq_one_of_fix_orderThree {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    (α : MulAut Q) (hcop : Nat.Coprime 3 (orderOf α)) (hfix : ∀ x : Q, orderOf x = 3 → α x = x) :
    α = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases subsingleton_or_nontrivial Q with hS | hN
  · ext x
    exact Subsingleton.elim _ _
  · obtain ⟨D, hDc, -, hD3, -, -, hker⟩ := supercritical_witness (p := 3) (by norm_num) hQ
    have := hDc
    have hα : α ∈ (frattiniAction D).ker := by
      rw [mem_ker_frattiniAction]
      intro d
      have hd : α (d : Q) = d := by
        by_cases h1 : (d : Q) = 1
        · rw [h1, map_one]
        · exact hfix _ (orderOf_eq_prime (hD3 d d.2) h1)
      have hd' : MulAut.characteristic D α d = d := Subtype.ext hd
      rw [hd', inv_mul_cancel]
      exact Subgroup.one_mem _
    obtain ⟨n, hn⟩ := hker ⟨α, hα⟩
    have h1 : α ^ 3 ^ n = 1 := congrArg Subtype.val hn
    have h2 : orderOf α ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
    have h3 : Nat.Coprime (orderOf α) (3 ^ n) := (hcop.symm).pow_right n
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h3 h2)

theorem mem_centralizer_of_fix_orderThree {C : Type*} [Group C] {Q : Subgroup C} [Finite Q]
    (hQ : IsPGroup 3 Q) {h : C} (hN : h ∈ Subgroup.normalizer (Q : Set C))
    (hcop : Nat.Coprime 3 (orderOf h))
    (hfix : ∀ x ∈ Q, orderOf x = 3 → h * x * h⁻¹ = x) : h ∈ Subgroup.centralizer (Q : Set C) := by
  set α : MulAut Q := Q.normalizerMonoidHom ⟨h, hN⟩ with hα
  have hcoe : ∀ a : Q, ((α a : Q) : C) = h * a * h⁻¹ := fun a =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Q ⟨h, hN⟩ a
  have hord : orderOf α ∣ orderOf h := by
    have h1 := orderOf_map_dvd Q.normalizerMonoidHom (⟨h, hN⟩ : Subgroup.normalizer (Q : Set C))
    have e : orderOf h = orderOf (⟨h, hN⟩ : Subgroup.normalizer (Q : Set C)) :=
      Subgroup.orderOf_coe ⟨h, hN⟩
    rw [e]
    exact h1
  have hα1 : α = 1 := by
    refine eq_one_of_fix_orderThree hQ α (hcop.coprime_dvd_right hord) fun x hx => ?_
    apply Subtype.ext
    rw [hcoe]
    exact hfix x x.2 ((Subgroup.orderOf_coe x).trans hx)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := hcoe ⟨y, hy⟩
  rw [hα1] at h1
  have h2 : y = h * y * h⁻¹ := by simpa using h1
  calc y * h = (h * y * h⁻¹) * h := by rw [← h2]
    _ = h * y := by group

theorem exists_normal_threeComplement {C : Type*} [Group C] [Finite C]
    (h : ∀ y : C, orderOf y = 3 → y ∈ Subgroup.center C) :
    ∃ N : Subgroup C, CFSG.GroupTheory.IsNormalPComplement 3 N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ((CFSG.GroupTheory.frobenius_normal_p_complement 3).1).2 ?_
  intro Q hQ x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
  obtain ⟨e, b, hb, hgb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg0 3 (by norm_num)
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hord : orderOf (g ^ 3 ^ e) = b := by
    rw [orderOf_pow' _ (pow_ne_zero _ (by norm_num)), hgb, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_cancel_left _ (pow_pos (by norm_num) _)]
  have hcop : Nat.Coprime 3 (orderOf ((g : C) ^ 3 ^ e)) := by
    have e1 : orderOf ((g : C) ^ 3 ^ e) = b := by
      rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]; exact hord
    rw [e1]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hb
  refine mem_centralizer_of_fix_orderThree hQ ?_ ?_ ?_
  · exact ((g ^ 3 ^ e : Subgroup.normalizer (Q : Set C))).2
  · simpa using hcop
  · intro y hy hy3
    have hc := Subgroup.mem_center_iff.mp (h y hy3) ((g : C) ^ 3 ^ e)
    calc (g : C) ^ 3 ^ e * y * ((g : C) ^ 3 ^ e)⁻¹ = (y * (g : C) ^ 3 ^ e) * ((g : C) ^ 3 ^ e)⁻¹ := by
          rw [hc]
      _ = y := by group

end He12

end CFSG.Quasithin
