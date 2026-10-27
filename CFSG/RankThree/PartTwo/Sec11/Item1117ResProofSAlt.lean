module

public import CFSG.RankThree.PartTwo.Sec11.Notation
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1117ResProof

section Group

variable {G : Type*} [Group G]

theorem pow_three_commutator (x g : G) :
    x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ =
      (x ^ 2 * (x * g * x⁻¹ * g⁻¹) * (x ^ 2)⁻¹) * (x * (x * g * x⁻¹ * g⁻¹) * x⁻¹) *
        (x * g * x⁻¹ * g⁻¹) := by
  group

theorem pow_three_commutator_eq {x g a w e₀ : G} {k : ℤ}
    (hxg : x * g * x⁻¹ * g⁻¹ = a ^ k * w) (hxa : x * a * x⁻¹ = e₀ * a)
    (he₀x : Commute e₀ x) (he₀a : Commute e₀ a) (hwx : Commute w x) (hwa : Commute w a)
    (hwe : Commute w e₀) (he₀3 : e₀ ^ 3 = 1) (ha3 : a ^ 3 = 1) :
    x ^ 3 * g * (x ^ 3)⁻¹ * g⁻¹ = w ^ 3 := by
  have hconj : ∀ y : G, Commute y x → x * y * x⁻¹ = y := fun y hy => by
    rw [← hy.eq, mul_inv_cancel_right]
  have h1 : x * (a ^ k * w) * x⁻¹ = e₀ ^ k * (a ^ k * w) := by
    have hak : x * a ^ k * x⁻¹ = (e₀ * a) ^ k := by rw [← hxa, conj_zpow]
    calc x * (a ^ k * w) * x⁻¹ = (x * a ^ k * x⁻¹) * (x * w * x⁻¹) := by group
      _ = (e₀ * a) ^ k * w := by rw [hak, hconj w hwx]
      _ = e₀ ^ k * (a ^ k * w) := by rw [he₀a.mul_zpow, mul_assoc]
  have h2 : x ^ 2 * (a ^ k * w) * (x ^ 2)⁻¹ = e₀ ^ k * (e₀ ^ k * (a ^ k * w)) := by
    calc x ^ 2 * (a ^ k * w) * (x ^ 2)⁻¹ = x * (x * (a ^ k * w) * x⁻¹) * x⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = x * (e₀ ^ k * (a ^ k * w)) * x⁻¹ := by rw [h1]
      _ = (x * e₀ ^ k * x⁻¹) * (x * (a ^ k * w) * x⁻¹) := by group
      _ = e₀ ^ k * (e₀ ^ k * (a ^ k * w)) := by rw [h1, hconj _ (he₀x.zpow_left k)]
  rw [pow_three_commutator, hxg, h1, h2]
  generalize hα : a ^ k * w = α
  have hαe : Commute α (e₀ ^ k) := by
    rw [← hα]
    exact ((he₀a.zpow_zpow k k).symm).mul_left (hwe.zpow_right k)
  have he3 : (e₀ ^ k) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he₀3, one_zpow]
  have hα3 : α ^ 3 = w ^ 3 := by
    rw [← hα, ((hwa.zpow_right k).symm).mul_pow]
    have ha3' : (a ^ k) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha3, one_zpow]
    rw [ha3', one_mul]
  calc e₀ ^ k * (e₀ ^ k * α) * (e₀ ^ k * α) * α
      = e₀ ^ k * e₀ ^ k * (α * e₀ ^ k) * α * α := by group
    _ = e₀ ^ k * e₀ ^ k * (e₀ ^ k * α) * α * α := by rw [hαe.eq]
    _ = (e₀ ^ k * e₀ ^ k * e₀ ^ k) * (α * α * α) := by group
    _ = w ^ 3 := by rw [← pow_three', ← pow_three', he3, hα3, one_mul]

end Group

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem a_not_mem_Y_of_center_eq_bot (h : Sec11Std G A c L a R Y)
    (hZ : Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) = ⊥) : a ∉ Y := by
  intro haY
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYC := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y
  set y : Y := ⟨a, haY⟩ with hy
  have hcen : (y : Y ⧸ aschbacherSolvableCore 3 Y) ∈
      Subgroup.center (Y ⧸ aschbacherSolvableCore 3 Y) := by
    rw [Subgroup.mem_center_iff]
    intro w
    induction w using QuotientGroup.induction_on with
    | H w =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hy]
      exact Subgroup.mem_centralizer_singleton_iff.mp (hYC w.2)
  rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcen
  have h3 := (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).2.2.1
  apply h3
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hord : orderOf a = 3 := orderOf_eq_prime ha3 h.a_ne_one
  have h1 := orderOf_dvd_natCard (⟨y, hcen⟩ : aschbacherSolvableCore 3 Y)
  rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord] at h1

end Data

end Item1117ResProof

end CFSG.RankThree.PartTwo.Sec11
