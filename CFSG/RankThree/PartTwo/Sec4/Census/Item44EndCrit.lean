module

public import CFSG.RankThree.GroupTheory.SteinbergBYSymplecticCritical

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec4.Census

open Subgroup
open scoped commutatorElement

theorem exists_orderOf_eq_two_pow {A : Type*} [Group A] (hA : IsPGroup 2 A) (x : A) :
    ∃ j : ℕ, orderOf x = 2 ^ j := by
  obtain ⟨k, hk⟩ := hA x
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
  exact ⟨j, hj⟩

theorem isCyclic_of_unique_involution {A : Type*} [Group A] [Finite A] [hc : IsMulCommutative A]
    (hA : IsPGroup 2 A) (h : ∀ s t : A, s * s = 1 → t * t = 1 → s ≠ 1 → t ≠ 1 → s = t) :
    IsCyclic A := by
  obtain ⟨a, ha⟩ := Finite.exists_max (orderOf : A → ℕ)
  obtain ⟨i, hi⟩ := exists_orderOf_eq_two_pow hA a
  have key : ∀ n, ∀ b : A, orderOf b = n → b ∈ zpowers a := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro b hb
    by_cases hb1 : b = 1
    · rw [hb1]
      exact one_mem _
    obtain ⟨j, hj⟩ := exists_orderOf_eq_two_pow hA b
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hb1 hj
    have hb2 : orderOf (b ^ 2) = 2 ^ (j - 1) := by
      rw [orderOf_pow' b two_ne_zero, hj, Nat.gcd_eq_right (dvd_pow_self 2 hj0)]
      calc 2 ^ j / 2 = 2 ^ (j - 1) * 2 / 2 := by
            rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)]
        _ = 2 ^ (j - 1) := Nat.mul_div_cancel _ two_pos
    have hlt : orderOf (b ^ 2) < n := by
      rw [hb2, ← hb, hj]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.mp
      (mem_powers_iff_mem_zpowers.mpr (ih _ hlt (b ^ 2) rfl))
    have hba : orderOf b ≤ orderOf a := ha b
    have hm2 : 2 ∣ m := by
      by_contra hodd
      have hm0 : m ≠ 0 := fun h0 => hodd (h0 ▸ dvd_zero 2)
      have hcop : Nat.gcd (orderOf a) m = 1 := by
        rw [hi]
        exact Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
      have h1 : orderOf (a ^ m) = orderOf a := by rw [orderOf_pow' a hm0, hcop, Nat.div_one]
      rw [hm] at h1
      omega
    obtain ⟨l, rfl⟩ := hm2
    set c := b * (a ^ l)⁻¹ with hcdef
    have hcc : c * c = 1 := by
      have hcomm : b * (a ^ l)⁻¹ = (a ^ l)⁻¹ * b := hc.is_comm.comm _ _
      calc c * c = b * b * ((a ^ l)⁻¹ * (a ^ l)⁻¹) := by
            rw [hcdef, mul_assoc, ← mul_assoc (a ^ l)⁻¹, ← hcomm, mul_assoc, mul_assoc]
        _ = 1 := by
            rw [← sq, ← hm, ← mul_inv_rev, ← pow_add, ← two_mul, mul_inv_cancel]
    by_cases hc1 : c = 1
    · have : b = a ^ l := by rwa [hcdef, mul_inv_eq_one] at hc1
      rw [this]
      exact pow_mem (mem_zpowers a) l
    ·
      have hi0 : i ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hi
        have h2 : 2 ≤ orderOf b := by
          rw [hj]
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hj0)
        omega
      set d := a ^ (2 ^ (i - 1)) with hd
      have hd1 : d ≠ 1 := pow_ne_one_of_lt_orderOf (pow_ne_zero _ two_ne_zero) (by
        rw [hi]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega))
      have hdd : d * d = 1 := by
        rw [hd, ← pow_add, ← two_mul, ← pow_succ', Nat.sub_add_cancel
          (Nat.one_le_iff_ne_zero.mpr hi0), ← hi, pow_orderOf_eq_one]
      have hcd := h c d hcc hdd hc1 hd1
      have : b = d * a ^ l := by rw [← hcd, hcdef, inv_mul_cancel_right]
      rw [this]
      exact mul_mem (pow_mem (mem_zpowers a) _) (pow_mem (mem_zpowers a) l)
  exact ⟨a, fun b => mem_zpowers_iff.mp (key _ b rfl)⟩

variable {P : Type*} [Group P]

theorem map_center_top : (center (⊤ : Subgroup P)).map (⊤ : Subgroup P).subtype = center P := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, mem_center_iff] at hy
    rw [mem_center_iff]
    intro g
    exact congrArg Subtype.val (hy ⟨g, mem_top g⟩)
  · intro hx
    refine ⟨⟨x, mem_top x⟩, ?_, rfl⟩
    rw [mem_center_iff] at hx
    rw [SetLike.mem_coe, mem_center_iff]
    intro g
    exact Subtype.ext (hx g)

theorem card_quot_center_top [Finite P] :
    Nat.card ((⊤ : Subgroup P) ⧸ center (⊤ : Subgroup P)) = Nat.card (P ⧸ center P) := by
  have h1 := card_eq_card_quotient_mul_card_subgroup (center (⊤ : Subgroup P))
  have h2 := card_eq_card_quotient_mul_card_subgroup (center P)
  have h3 : Nat.card (center (⊤ : Subgroup P)) = Nat.card (center P) := by
    rw [← map_center_top (P := P), card_map_of_injective (subtype_injective _)]
  rw [card_top, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.symm.trans h2)

theorem structure_of_central [Finite P] [Nontrivial P] (hP : IsPGroup 2 P)
    (hsymp : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → IsCyclic A)
    (hcen : ∀ A : Subgroup P, A.Characteristic → IsMulCommutative A → A ≤ center P) :
    IsCyclic P ∨
      ∃ z ∈ center P, orderOf z = 2 ∧ (∀ x ∈ center P, orderOf x = 2 → x = z) ∧
        (∀ x y : P, ⁅x, y⁆ ∈ zpowers z) ∧
        ∃ E : Subgroup P, E ⊔ center P = ⊤ ∧ E ⊓ center P = zpowers z ∧
          ∃ w : ℕ, 1 ≤ w ∧ Nat.card (P ⧸ center P) = 2 ^ (2 * w) := by
  obtain ⟨⟨D, -, hD⟩, hall⟩ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.symplectic_critical_subgroup_central_product hP hsymp
  obtain ⟨-, -, hZchar, z, -, hz2, -, hzc, hzcu, hcent, E, R, hEZ, -, -, -, -, -, -, hcases, -⟩ :=
    hall D hD
  have hZle := hcen _ hZchar inferInstance
  have hDtop : D = ⊤ := by
    rw [← hcent]
    refine eq_top_iff.mpr fun x _ => mem_centralizer_iff.mpr fun y hy => ?_
    exact (mem_center_iff.mp (hZle hy) x).symm
  subst hDtop
  rcases hcases with ⟨hcyc, -, -⟩ | ⟨w, hw1, -, hcard, -, -, -, -, -, hEZ', -, b, -, -, -, -, hb⟩
  · exact Or.inl ((MulEquiv.isCyclic topEquiv).mp hcyc)
  · refine Or.inr ⟨z, hzc, hz2, hzcu, fun x y => ?_, E, ?_, ?_, w, hw1, ?_⟩
    · have h := hb ⟨x⁻¹, mem_top _⟩ ⟨y⁻¹, mem_top _⟩
      simp only [inv_inv] at h
      rw [commutatorElement_def, h]
      exact pow_mem (mem_zpowers z) _
    · rwa [map_center_top] at hEZ
    · rwa [map_center_top] at hEZ'
    · rw [← card_quot_center_top]
      exact hcard

end CFSG.RankThree.PartTwo.Sec4.Census
