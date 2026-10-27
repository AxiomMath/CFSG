module

public import CFSG.RankThree.PartTwo.Sec18.SylowFiveDelta
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace SylowFive

namespace CaseTwo

variable {G : Type} [Group G] {P A B : Subgroup G} {c : G} (hS : CaseTwo P A B c)
include hS

section Abelian

variable (hab : ∀ x ∈ qOf P B, ∀ y ∈ qOf P B, ⁅x, y⁆ ∈ B)
include hab

theorem commutator_mul_left_of {x y z : G} (hx : x ∈ qOf P B) (hy : y ∈ qOf P B)
    (hz : z ∈ qOf P B) : ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hyz := hab y hy z hz
  have e : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
    simp only [commutatorElement_def]; group
  rw [e, hS.commute_of_mem_qOf hx hyz, mul_inv_cancel_right]
  exact hS.comm (hS.le hyz) (hS.le (hab x hx z hz))

theorem commutator_mul_right_of {x y z : G} (hy : y ∈ qOf P B) (hxz : ⁅x, z⁆ ∈ B) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [e, hS.commute_of_mem_qOf hy hxz, mul_inv_cancel_right]

theorem mul_pow_three_of {x y : G} (hx : x ∈ qOf P B) (hy : y ∈ qOf P B) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  set w := ⁅y⁻¹, x⁻¹⁆ with hw
  have hwB : w ∈ B := hab _ ((qOf P B).inv_mem hy) _ ((qOf P B).inv_mem hx)
  have h1 : x⁻¹ * y * x = y * w := by rw [hw, commutatorElement_def]; group
  have hwx : x⁻¹ * w * x = w := by
    rw [mul_assoc, ← hS.commute_of_mem_qOf hx hwB, inv_mul_cancel_left]
  have h2 : x⁻¹ * (y * w) * x = y * w * w := by
    calc x⁻¹ * (y * w) * x = (x⁻¹ * y * x) * (x⁻¹ * w * x) := by group
      _ = y * w * w := by rw [h1, hwx]
  have hwy : w * y = y * w := (hS.commute_of_mem_qOf hy hwB).symm
  have e : (x * y) ^ 3 = x ^ 3 * ((x⁻¹ * (x⁻¹ * y * x) * x) * (x⁻¹ * y * x) * y) := by
    rw [_root_.pow_three, _root_.pow_three]; group
  rw [e, h1, h2]
  have e2 : y * w * w * (y * w) * y = (y * w) ^ 3 := by
    calc y * w * w * (y * w) * y = (y * w) * (w * y) * (w * y) := by simp only [mul_assoc]
      _ = (y * w) ^ 3 := by rw [hwy, _root_.pow_three]; simp only [mul_assoc]
  rw [e2, Commute.mul_pow hwy.symm 3, hS.pow_three_of_mem_plane hwB, mul_one]

@[expose] def cube : qOf P B →* G where
  toFun t := (t : G) ^ 3
  map_one' := by simp
  map_mul' x y := by
    simp only [Subgroup.coe_mul]
    exact hS.mul_pow_three_of hab x.2 y.2

theorem cube_apply (t : qOf P B) : hS.cube hab t = (t : G) ^ 3 := rfl

variable [Finite G]

theorem exists_pow_three_ne_one : ∃ t ∈ qOf P B, t ^ 3 ≠ 1 := by
  by_contra hall
  push Not at hall
  obtain ⟨b₀, b₁, hF⟩ := hS.exists_flag
  obtain ⟨x₁, hx₁, hδ₁⟩ := hS.exists_commutator_eq hF.mem_one
  obtain ⟨x₂, hx₂, hδ₂⟩ := hS.exists_commutator_eq hF.mem_zero
  have he := hab x₁ hx₁ x₂ hx₂
  obtain ⟨α, -, z, hz, hez⟩ :=
    Sec13.exists_pow_mul_of_mem hS.isElemAbelian_plane hF.mem_one (hS.plane_eq_sup hF) he
  obtain ⟨γ, -, n, hn, hzn⟩ := Sec13.exists_pow_mul_of_mem
    (CFSG.Open.isElemAbelian_zpowers (hS.pow_three_of_mem_plane hF.mem_zero))
    (Subgroup.mem_zpowers b₀) (sup_bot_eq _).symm hz
  rw [Subgroup.mem_bot] at hn
  rw [hn, mul_one] at hzn
  rw [hzn] at hez
  have hcQ : c ∈ qOf P B := hS.le_qOf hS.mem
  have hcγ : c ^ γ ∈ qOf P B := (qOf P B).pow_mem hcQ γ
  have hcα : c ^ (2 * α) ∈ qOf P B := (qOf P B).pow_mem hcQ _
  set u := x₁ * c ^ γ with hu
  set v := x₂ * c ^ (2 * α) with hv
  have huQ : u ∈ qOf P B := (qOf P B).mul_mem hx₁ hcγ
  have hvQ : v ∈ qOf P B := (qOf P B).mul_mem hx₂ hcα
  have hb₀B : ∀ k : ℕ, b₀ ^ k ∈ B := fun k => B.pow_mem hF.mem_zero k
  have hb₁B : ∀ k : ℕ, b₁ ^ k ∈ B := fun k => B.pow_mem hF.mem_one k
  have h1 : ⁅x₁, c ^ (2 * α)⁆ = b₁ ^ (2 * α) := by
    rw [← mul_one (c ^ (2 * α)), hS.commutator_pow_mul hx₁ B.one_mem, hδ₁]
  have h2 : ⁅c ^ γ, x₂⁆ = (b₀ ^ γ)⁻¹ := by
    rw [← commutatorElement_inv, ← mul_one (c ^ γ), hS.commutator_pow_mul hx₂ B.one_mem, hδ₂]
  have h3 : ⁅c ^ γ, c ^ (2 * α)⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hS.comm (A.pow_mem hS.mem _) (A.pow_mem hS.mem _)
  have huv : ⁅u, v⁆ = 1 := by
    rw [hu, hS.commutator_mul_left_of hab hx₁ hcγ hvQ, hv,
      hS.commutator_mul_right_of hab hx₂ (hab x₁ hx₁ _ hcα),
      hS.commutator_mul_right_of hab hx₂ (hab _ hcγ _ hcα), hez, h1, h2, h3, mul_one]
    have hc : b₀ ^ γ * b₁ ^ (2 * α) = b₁ ^ (2 * α) * b₀ ^ γ :=
      hS.comm (hS.le (hb₀B γ)) (hS.le (hb₁B _))
    calc b₁ ^ α * b₀ ^ γ * b₁ ^ (2 * α) * (b₀ ^ γ)⁻¹
        = b₁ ^ α * (b₀ ^ γ * b₁ ^ (2 * α)) * (b₀ ^ γ)⁻¹ := by group
      _ = b₁ ^ α * (b₁ ^ (2 * α) * b₀ ^ γ) * (b₀ ^ γ)⁻¹ := by rw [hc]
      _ = (b₁ ^ 3) ^ α := by
        rw [mul_assoc, mul_inv_cancel_right, ← pow_add, ← pow_mul]; congr 1; ring
      _ = 1 := by rw [hS.pow_three_of_mem_plane hF.mem_one, one_pow]
  have huvc : u * v = v * u := commutatorElement_eq_one_iff_mul_comm.mp huv
  have hUV : CFSG.Assembly.IsElemAbelian 3 (Subgroup.zpowers u ⊔ Subgroup.zpowers v) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers (hall u huQ))
      (CFSG.Open.isElemAbelian_zpowers (hall v hvQ)) fun a ha b hb => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        exact (Commute.zpow_zpow huvc i j).eq
  have hUVQ : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ qOf P B :=
    sup_le (Subgroup.zpowers_le.mpr huQ) (Subgroup.zpowers_le.mpr hvQ)
  set E := (Subgroup.zpowers u ⊔ Subgroup.zpowers v) ⊔ B with hE
  have hEel : CFSG.Assembly.IsElemAbelian 3 E :=
    CFSG.Open.IsElemAbelian.sup_of_commute hUV hS.isElemAbelian_plane fun a ha b hb =>
      hS.commute_of_mem_qOf (hUVQ ha) hb
  have hEQ : E ≤ qOf P B := sup_le hUVQ (hS.le.trans hS.le_qOf)
  have hδu : ⁅u, c⁆ = b₁ := by
    rw [hu, hS.commutator_mul hx₁ hcγ.1, hδ₁,
      commutatorElement_eq_one_iff_mul_comm.mpr (hS.comm (A.pow_mem hS.mem _) hS.mem), mul_one]
  have hδv : ⁅v, c⁆ = b₀ := by
    rw [hv, hS.commutator_mul hx₂ hcα.1, hδ₂,
      commutatorElement_eq_one_iff_mul_comm.mpr (hS.comm (A.pow_mem hS.mem _) hS.mem), mul_one]
  have hBD : B ≤ hS.dImage E := by
    refine (hS.plane_eq_sup hF).le.trans (sup_le (Subgroup.zpowers_le.mpr ?_)
      (Subgroup.zpowers_le.mpr ?_))
    · exact hS.mem_dImage.mpr
        ⟨u, Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)), huQ, hδu⟩
    · exact hS.mem_dImage.mpr
        ⟨v, Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)), hvQ, hδv⟩
  have hcard := hS.card_eq_of_le_qOf hEQ
  have h9a : 9 ≤ Nat.card (E ⊓ A : Subgroup G) := by
    rw [← hS.card_plane]
    exact Subgroup.card_le_of_le (le_inf le_sup_right hS.le)
  have h9b : 9 ≤ Nat.card (hS.dImage E) := by
    rw [← hS.card_plane]
    exact Subgroup.card_le_of_le hBD
  have h27 := hS.card_le E (hEQ.trans inf_le_left) hEel
  nlinarith

theorem cube_range_eq : (hS.cube hab).range = B := by
  have hle : (hS.cube hab).range ≤ B := by
    rintro _ ⟨t, rfl⟩
    exact hS.pow_three_mem_plane t.2
  have hne : (hS.cube hab).range ≠ ⊥ := by
    obtain ⟨t, ht, ht3⟩ := hS.exists_pow_three_ne_one hab
    intro h
    have hmem : hS.cube hab ⟨t, ht⟩ ∈ (hS.cube hab).range := ⟨_, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact ht3 hmem
  have hdvd : Nat.card (hS.cube hab).range ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hS.card_plane]
    exact Subgroup.card_dvd_of_le hle
  have hne3 : Nat.card (hS.cube hab).range ≠ 3 := by
    intro h3
    apply hS.not_le_normalizer _ hle h3
    intro g hg
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro y
    constructor
    · rintro ⟨t, rfl⟩
      have hgt : g * (t : G) * g⁻¹ ∈ qOf P B := (hg t).mp t.2
      exact ⟨⟨_, hgt⟩, by rw [hS.cube_apply, conj_pow]; rfl⟩
    · rintro ⟨t, ht⟩
      have hgt : g⁻¹ * (t : G) * g ∈ qOf P B := by
        refine (hg _).mpr ?_
        have e : g * (g⁻¹ * (t : G) * g) * g⁻¹ = t := by group
        rw [e]
        exact t.2
      refine ⟨⟨_, hgt⟩, ?_⟩
      rw [hS.cube_apply] at ht ⊢
      have e : g⁻¹ * (t : G) * g = g⁻¹ * (t : G) * g⁻¹⁻¹ := by rw [inv_inv]
      simp only [e, conj_pow, ht]
      group
  have hcard9 : Nat.card (hS.cube hab).range = 9 := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    interval_cases k
    · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hk')) hne
    · exact absurd (by simpa using hk') hne3
    · simpa using hk'
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard9, hS.card_plane])

theorem exists_pow_three_eq {b : G} (hb : b ∈ B) : ∃ t ∈ qOf P B, t ^ 3 = b := by
  obtain ⟨t, ht⟩ := (hS.cube_range_eq hab).ge hb
  exact ⟨t, t.2, ht⟩

theorem mem_of_pow_three_eq_one {t : G} (ht : t ∈ qOf P B) (h3 : t ^ 3 = 1) : t ∈ A := by
  set K := (hS.cube hab).ker.map (qOf P B).subtype with hK
  have hAK : A ≤ K := fun a ha => ⟨⟨a, hS.le_qOf ha⟩, hS.pow_three ha, rfl⟩
  have hcardK : Nat.card K = 27 := by
    have h := Subgroup.card_ker_mul_card_range (hS.cube hab)
    rw [hS.cube_range_eq hab, hS.card_plane, hS.card_qOf] at h
    rw [hK, Subgroup.card_map_of_injective (qOf P B).subtype_injective]
    omega
  have hKA : K = A := (Subgroup.eq_of_le_of_card_ge hAK (by rw [hcardK, hS.card_eq])).symm
  rw [← hKA]
  exact ⟨⟨t, ht⟩, h3, rfl⟩

end Abelian

end CaseTwo

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
