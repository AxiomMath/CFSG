module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Abelianization.Defs

public section

namespace CFSG.Quasithin.A38c14

open scoped IsMulCommutative

theorem central_mem_commutator_eq_one_of_abelian_sylow {X : Type} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] (P : Sylow p X) (hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) {z : X}
    (hz : z ∈ Subgroup.center X) (hzP : z ∈ P) (hzc : z ∈ commutator X) : z = 1 := by
  classical
  have hcomm : IsMulCommutative (P : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hP a a.2 b b.2)⟩⟩
  let t : X →* (P : Subgroup X) := MonoidHom.transfer (MonoidHom.id (P : Subgroup X))
  have key : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup X) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center X := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← (Subgroup.mem_center_iff.mp hc g₀), ← mul_assoc, inv_mul_cancel, one_mul]
  have h1 : t z = ⟨z ^ (P : Subgroup X).index, MonoidHom.transfer_eq_pow_aux z key⟩ :=
    MonoidHom.transfer_eq_pow _ z key
  have h2 : t z = 1 := MonoidHom.mem_ker.mp (Abelianization.commutator_subset_ker t hzc)
  have h3 : z ^ (P : Subgroup X).index = 1 := by
    have := congrArg Subtype.val (h1.symm.trans h2)
    simpa using this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.2) ⟨z, hzP⟩
  have hk' : orderOf z = p ^ k := by
    have := orderOf_submonoid (⟨z, hzP⟩ : (P : Subgroup X))
    simpa [Subgroup.orderOf_coe] using hk
  have hdvd : p ^ k ∣ (P : Subgroup X).index := hk' ▸ orderOf_dvd_of_pow_eq_one h3
  have hk0 : k = 0 := by
    by_contra hne
    exact P.not_dvd_index ((dvd_pow_self p hne).trans hdvd)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at hk'
  exact hk'

theorem card_sylow_three {X : Type} [Group X] [Finite X] (P : Sylow 3 X) {k m : ℕ}
    (hm : ¬ 3 ∣ m) (hcard : Nat.card X = 3 ^ k * m) : Nat.card P = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, hcard]
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 3)
  rw [Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd hm, add_zero]

theorem mem_sylow_three_of_central {X : Type} [Group X] [Finite X] (P : Sylow 3 X) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) : z ∈ P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hzle : Subgroup.zpowers z ≤ Subgroup.center X := Subgroup.zpowers_le.mpr hz
  have hzN : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hzle
  have hzp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz3]; norm_num)
  exact hzp.le_sylow_of_normal P (Subgroup.mem_zpowers z)

theorem false_of_central_three {B : Type} [Group B] [Finite B] (hB : commutator B = ⊤) {m : ℕ}
    (hm : ¬ 3 ∣ m) (hcard : Nat.card B = 9 * m) {z : B} (hz : z ∈ Subgroup.center B)
    (hz3 : orderOf z = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow 3 B))
  have hP : Nat.card P = 3 ^ 2 := card_sylow_three P hm (by rw [hcard]; norm_num)
  have hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := fun a ha b hb => by
    have := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := (P : Subgroup B)) hP
    simpa using congrArg Subtype.val (mul_comm (⟨a, ha⟩ : (P : Subgroup B)) ⟨b, hb⟩)
  have h1 := central_mem_commutator_eq_one_of_abelian_sylow P hab hz
    (mem_sylow_three_of_central P hz hz3) (by rw [hB]; exact Subgroup.mem_top z)
  rw [h1, orderOf_one] at hz3
  exact absurd hz3 (by norm_num)

theorem false_of_central_three_of_abelian {X : Type} [Group X] [Finite X]
    (hX : commutator X = ⊤) {m : ℕ} (hm : ¬ 3 ∣ m) (hcard : Nat.card X = 27 * m) {z : X}
    (hz : z ∈ Subgroup.center X) (hz3 : orderOf z = 3) {Q : Subgroup X} (hQ : Nat.card Q = 27)
    (hab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) (hzQ : z ∈ Q) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  have hidx : ¬ 3 ∣ Q.index := by
    have h1 := Subgroup.card_mul_index Q
    rw [hQ, hcard] at h1
    have : Q.index = m := by omega
    rw [this]
    exact hm
  let P : Sylow 3 X := hQp.toSylow hidx
  have h1 := central_mem_commutator_eq_one_of_abelian_sylow P
    (fun a ha b hb => hab a ha b hb) hz hzQ (by rw [hX]; exact Subgroup.mem_top z)
  rw [h1, orderOf_one] at hz3
  exact absurd hz3 (by norm_num)

end CFSG.Quasithin.A38c14
