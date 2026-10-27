module

public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.RankThree.PartTwo.Sec16.Res162Five

open Equiv Equiv.Perm

theorem card_centralizer_replicate_two :
    ((Fintype.card (Fin 7) - (Multiset.replicate 1 2).sum).factorial *
        (Multiset.replicate 1 2).prod *
        ∏ n ∈ (Multiset.replicate 1 2).toFinset, ((Multiset.replicate 1 2).count n).factorial =
      240) ∧
    ((Fintype.card (Fin 7) - (Multiset.replicate 2 2).sum).factorial *
        (Multiset.replicate 2 2).prod *
        ∏ n ∈ (Multiset.replicate 2 2).toFinset, ((Multiset.replicate 2 2).count n).factorial =
      48) ∧
    ((Fintype.card (Fin 7) - (Multiset.replicate 3 2).sum).factorial *
        (Multiset.replicate 3 2).prod *
        ∏ n ∈ (Multiset.replicate 3 2).toFinset, ((Multiset.replicate 3 2).count n).factorial =
      48) := by
  decide

theorem not_nine_dvd_card_centralizer {u : Perm (Fin 7)} (hu : orderOf u = 2) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer ({u} : Set (Perm (Fin 7)))) := by
  obtain ⟨n, hn⟩ := cycleType_prime_order (hu ▸ Nat.prime_two)
  rw [hu] at hn
  have hsum := sum_cycleType_le u
  rw [hn, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  rw [nat_card_centralizer, hn]
  have hn2 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hn2 with rfl | rfl | rfl
  · rw [card_centralizer_replicate_two.1]
    norm_num
  · rw [card_centralizer_replicate_two.2.1]
    norm_num
  · rw [card_centralizer_replicate_two.2.2]
    norm_num

theorem eq_one_of_le_centralizer {y : Perm (Fin 7)} {k : ℕ} (hy : y ^ 2 ^ k = 1)
    {E : Subgroup (Perm (Fin 7))} (hE : Nat.card E = 9)
    (hEy : E ≤ Subgroup.centralizer ({y} : Set (Perm (Fin 7)))) : y = 1 := by
  by_contra hy1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers]
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hy)
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact hy1 (orderOf_eq_one_iff.mp (by simpa using hm))
    rw [hm]
    exact dvd_pow_self 2 hm0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : orderOf (z : Perm (Fin 7)) = 2 := by rw [Subgroup.orderOf_coe, hz]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp z.2
  have hEz : E ≤ Subgroup.centralizer ({(z : Perm (Fin 7))} : Set (Perm (Fin 7))) := by
    intro e he
    have hey := hEy he
    rw [Subgroup.mem_centralizer_singleton_iff] at hey ⊢
    have hc : Commute e y := hey
    rw [← hj]
    exact hc.zpow_right j
  have h9 := Subgroup.card_dvd_of_le hEz
  rw [hE] at h9
  exact not_nine_dvd_card_centralizer hz2 h9

theorem le_alternatingGroup_of_le_normalizer {P E : Subgroup (Perm (Fin 7))}
    (hP : IsPGroup 2 P) (hE : Nat.card E = 9)
    (hEP : E ≤ Subgroup.normalizer (P : Set (Perm (Fin 7)))) :
    P ≤ alternatingGroup (Fin 7) := by
  classical
  intro x hx
  by_contra hxA
  have hsx : sign x = -1 := by
    rw [Equiv.Perm.mem_alternatingGroup] at hxA
    rcases Int.units_eq_one_or (sign x) with h | h
    · exact (hxA h).elim
    · exact h
  set X := {y : Perm (Fin 7) // y ∈ P ∧ sign y = -1} with hXdef
  have hconj : ∀ (e : E) (y : X), (e : Perm (Fin 7)) * y.1 * (e : Perm (Fin 7))⁻¹ ∈ P ∧
      sign ((e : Perm (Fin 7)) * y.1 * (e : Perm (Fin 7))⁻¹) = -1 := by
    intro e y
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hEP e.2) y.1).mp y.2.1, ?_⟩
    rw [map_mul, map_mul, map_inv, y.2.2, mul_comm (sign (e : Perm (Fin 7))) (-1), mul_assoc,
      mul_inv_cancel, mul_one]
  let _ : MulAction E X :=
    { smul := fun e y => ⟨(e : Perm (Fin 7)) * y.1 * (e : Perm (Fin 7))⁻¹, hconj e y⟩
      one_smul := fun y => by
        apply Subtype.ext
        change (1 : Perm (Fin 7)) * y.1 * (1 : Perm (Fin 7))⁻¹ = y.1
        group
      mul_smul := fun e f y => by
        apply Subtype.ext
        change ((e : Perm (Fin 7)) * f) * y.1 * ((e : Perm (Fin 7)) * f)⁻¹ =
          (e : Perm (Fin 7)) * ((f : Perm (Fin 7)) * y.1 * (f : Perm (Fin 7))⁻¹) *
            (e : Perm (Fin 7))⁻¹
        group }
  have hA1 : ∀ y : X, x⁻¹ * y.1 ∈ alternatingGroup (Fin 7) := by
    intro y
    rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hsx, y.2.2]
    decide
  have hA2 : ∀ z : (P ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))),
      sign (x * z.1) = -1 := by
    intro z
    have hz := (Subgroup.mem_inf.mp z.2).2
    rw [Equiv.Perm.mem_alternatingGroup] at hz
    rw [map_mul, hsx, hz, mul_one]
  have hcardX : Nat.card X = Nat.card (P ⊓ alternatingGroup (Fin 7) : Subgroup (Perm (Fin 7))) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hx) y.2.1, hA1 y⟩⟩
        invFun := fun z => ⟨x * z.1, mul_mem hx (Subgroup.mem_inf.mp z.2).1, hA2 z⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
  have hX3 : ¬ 3 ∣ Nat.card X := by
    rw [hcardX]
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP.to_le inf_le_left)
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  obtain ⟨y, hyfix⟩ := hE3.nonempty_fixed_point_of_prime_not_dvd_card X hX3
  have hEy : E ≤ Subgroup.centralizer ({y.1} : Set (Perm (Fin 7))) := by
    intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val (hyfix ⟨e, he⟩)
    change e * y.1 * e⁻¹ = y.1 at h
    calc e * y.1 = (e * y.1 * e⁻¹) * e := by group
      _ = y.1 * e := by rw [h]
  obtain ⟨k, hk⟩ := hP ⟨y.1, y.2.1⟩
  have hk' : y.1 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hy1 := eq_one_of_le_centralizer hk' hE hEy
  have hys := y.2.2
  rw [hy1, map_one] at hys
  exact absurd hys (by decide)

end CFSG.RankThree.PartTwo.Sec16.Res162Five
