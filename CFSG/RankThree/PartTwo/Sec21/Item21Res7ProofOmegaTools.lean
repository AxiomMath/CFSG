module

import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.Implications
public import CFSG.RankThree.PartTwo.Sec4.Notation
import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_le [Finite G] {Q R : Subgroup G} (hRQ : R ≤ Q) (hR : IsPGroup 3 R) :
    ∃ P : Subgroup G, R ≤ P ∧ CFSG.ABGLocalTools.IsSylowOf 3 P Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR' : IsPGroup 3 (R.subgroupOf Q) := hR.comap_of_injective Q.subtype Q.subtype_injective
  obtain ⟨S, hS⟩ := hR'.exists_le_sylow
  refine ⟨(S : Subgroup Q).map Q.subtype, fun r hr => ?_, ⟨S, rfl⟩⟩
  exact ⟨⟨r, hRQ hr⟩, hS (mem_subgroupOf.mpr hr), rfl⟩

omit [Finite G] in
theorem mul_pow_three_eq_pow_three {y k u : G} (hy3 : y ^ 3 = 1) (hyk : y * k * y⁻¹ = u * k)
    (huy : u * y = y * u) (huk : u * k = k * u) (hu3 : u ^ 3 = 1) : (y * k) ^ 3 = k ^ 3 := by
  have h2 : y * (u * k) * y⁻¹ = u * (u * k) := by
    calc y * (u * k) * y⁻¹ = (y * u * y⁻¹) * (y * k * y⁻¹) := by group
      _ = u * (u * k) := by
        rw [hyk, show y * u * y⁻¹ = u by rw [← huy]; group]
  have hcomm : Commute u k := huk
  calc (y * k) ^ 3 = (y * k * y⁻¹) * (y * (y * k * y⁻¹) * y⁻¹) * (y ^ 3 * k) := by
        rw [pow_three, pow_three]; group
    _ = (u * k) * (u * (u * k)) * k := by rw [hyk, h2, hy3, one_mul]
    _ = u ^ 3 * k ^ 3 := by
      rw [show (u * k) * (u * (u * k)) * k = u * (k * u) * (u * k) * k by group, ← huk]
      rw [show u * (u * k) * (u * k) * k = u * u * (k * u) * k * k by group, ← huk]
      rw [pow_three, pow_three]; group
    _ = k ^ 3 := by rw [hu3, one_mul]

omit [Finite G] in
theorem mul_pow_three_eq_one {a b ℓ : G} (hℓ3 : ℓ ^ 3 = 1) (hℓa : ℓ * a * ℓ⁻¹ = a * b)
    (hℓb : ℓ * b * ℓ⁻¹ = b) (hab : a * b = b * a) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) :
    (a * ℓ) ^ 3 = 1 := by
  have h2 : ℓ * (a * b) * ℓ⁻¹ = a * b * b := by
    calc ℓ * (a * b) * ℓ⁻¹ = (ℓ * a * ℓ⁻¹) * (ℓ * b * ℓ⁻¹) := by group
      _ = a * b * b := by rw [hℓa, hℓb]
  have hc : Commute a b := hab
  calc (a * ℓ) ^ 3 = a * (ℓ * a * ℓ⁻¹) * (ℓ * (ℓ * a * ℓ⁻¹) * ℓ⁻¹) * ℓ ^ 3 := by
        rw [pow_three, pow_three]; group
    _ = a * (a * b) * (a * b * b) := by rw [hℓa, h2, hℓ3, mul_one]
    _ = a ^ 3 * b ^ 3 := by
      rw [show a * (a * b) * (a * b * b) = a * a * (b * a) * b * b by group, ← hab]
      rw [pow_three, pow_three]; group
    _ = 1 := by rw [ha3, hb3, one_mul]

theorem eq_one_of_mem_inf_thetaQuotCentralizer {L : Subgroup G}
    (hZ : center (lBar L) = ⊥) {z : G} (hzL : z ∈ L) (hzC : z ∈ Sec4.thetaQuotCentralizer L)
    {k : ℕ} (hzk : z ^ (3 ^ k) = 1) : z = 1 := by
  obtain ⟨-, hTch, -⟩ := solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  have hzZ : ((⟨z, hzL⟩ : L) : lBar L) ∈ center (lBar L) := by
    rw [mem_center_iff]
    intro q
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective θ q
    obtain ⟨-, hl⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp hzC
    obtain ⟨t, ht, hte⟩ := hl l l.2
    change ((l : lBar L) * ((⟨z, hzL⟩ : L) : lBar L)) = ((⟨z, hzL⟩ : L) : lBar L) * (l : lBar L)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have : (l * ⟨z, hzL⟩)⁻¹ * (⟨z, hzL⟩ * l) = ⟨z, hzL⟩⁻¹ * t * ⟨z, hzL⟩ := by
      apply Subtype.ext
      have hte' : (t : G) = (l : G)⁻¹ * (z * l * z⁻¹) := hte
      simp only [coe_mul, coe_inv, hte']
      group
    rw [this]
    have hθn : θ.Normal := normal_of_characteristic θ
    have := hθn.conj_mem _ ht (⟨z, hzL⟩⁻¹)
    simpa [mul_assoc] using this
  rw [hZ, mem_bot, QuotientGroup.eq_one_iff] at hzZ
  have h1 := orderOf_dvd_natCard (⟨⟨z, hzL⟩, hzZ⟩ : θ)
  have h2 : orderOf (⟨⟨z, hzL⟩, hzZ⟩ : θ) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by simpa using hzk)))
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h2
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact congrArg (fun w : θ => ((w : L) : G)) hj
  · exfalso
    rw [hj] at h1
    exact three_not_dvd_card_aschbacherSolvableCore
      ((dvd_pow_self 3 (Nat.succ_ne_zero j)).trans h1)

end CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof
