module

public import CFSG.RankThree.PartTwo.Sec18.SylowFiveDelta
import CFSG.RankThree.PartTwo.Sec18.SylowFiveAbelian
import CFSG.RankThree.PartTwo.Sec18.SylowFiveChar
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace SylowFive

variable {G : Type} [Group G]

theorem mem_of_pow_mem {Z : Subgroup G} {g : G} (h3 : g ^ 3 = 1) {i : ℕ} (hi : i < 3)
    (hi0 : i ≠ 0) (h : g ^ i ∈ Z) : g ∈ Z := by
  interval_cases i
  · exact absurd rfl hi0
  · simpa using h
  · have e : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, h3, one_mul]
    rw [e]
    exact Z.pow_mem h 2

theorem mul_eq_pow_three {q s z : G} (hzs : z * s = s * z) :
    q * s * (z * s) * z * (z * s) = q * s ^ 3 * z ^ 3 := by
  calc q * s * (z * s) * z * (z * s) = q * s * (s * z) * z * (s * z) := by rw [hzs]
    _ = q * s * s * (z * (z * s)) * z := by simp only [mul_assoc]
    _ = q * s * s * (z * (s * z)) * z := by rw [hzs]
    _ = q * s * s * ((z * s) * z) * z := by simp only [mul_assoc]
    _ = q * s * s * ((s * z) * z) * z := by rw [hzs]
    _ = q * s ^ 3 * z ^ 3 := by rw [_root_.pow_three, _root_.pow_three]; simp only [mul_assoc]

theorem conj_pow_three_eq {q u m₁ m₂ m₃ : G} (h1 : q * u * q⁻¹ = m₁ * u)
    (h2 : q * m₁ * q⁻¹ = m₂ * m₁) (h3 : q * m₂ * q⁻¹ = m₃ * m₂) :
    q ^ 3 * u * (q ^ 3)⁻¹ = m₃ * m₂ * (m₂ * m₁) * (m₂ * m₁) * (m₁ * u) := by
  calc q ^ 3 * u * (q ^ 3)⁻¹ = q * (q * (q * u * q⁻¹) * q⁻¹) * q⁻¹ := by
        rw [_root_.pow_three]; group
    _ = q * (q * (m₁ * u) * q⁻¹) * q⁻¹ := by rw [h1]
    _ = q * ((q * m₁ * q⁻¹) * (q * u * q⁻¹)) * q⁻¹ := by group
    _ = q * ((m₂ * m₁) * (m₁ * u)) * q⁻¹ := by rw [h1, h2]
    _ = (q * m₂ * q⁻¹) * (q * m₁ * q⁻¹) * (q * m₁ * q⁻¹) * (q * u * q⁻¹) := by group
    _ = m₃ * m₂ * (m₂ * m₁) * (m₂ * m₁) * (m₁ * u) := by rw [h1, h2, h3]

theorem mul_eq_of_mul_eq {m₁ m₂ m₃ w u : G} (h12 : m₁ * m₂ = w * (m₂ * m₁))
    (hw : m₃ * m₂ * m₂ * w = w * (m₃ * m₂ * m₂)) :
    m₃ * m₂ * (m₂ * m₁) * (m₂ * m₁) * (m₁ * u) = w * m₃ * m₂ ^ 3 * m₁ ^ 3 * u := by
  calc m₃ * m₂ * (m₂ * m₁) * (m₂ * m₁) * (m₁ * u)
      = (m₃ * m₂ * m₂) * (m₁ * m₂) * (m₁ * m₁ * u) := by simp only [mul_assoc]
    _ = (m₃ * m₂ * m₂) * (w * (m₂ * m₁)) * (m₁ * m₁ * u) := by rw [h12]
    _ = ((m₃ * m₂ * m₂) * w) * (m₂ * m₁) * (m₁ * m₁ * u) := by simp only [mul_assoc]
    _ = (w * (m₃ * m₂ * m₂)) * (m₂ * m₁) * (m₁ * m₁ * u) := by rw [hw]
    _ = w * m₃ * m₂ ^ 3 * m₁ ^ 3 * u := by
      rw [_root_.pow_three, _root_.pow_three]; simp only [mul_assoc]

namespace CaseTwo

variable {P A B : Subgroup G} {c : G} (hS : CaseTwo P A B c)
include hS

variable [Finite G]

theorem exists_card_eq {X : Subgroup G} (hX : X ≤ P) : ∃ k : ℕ, Nat.card X = 3 ^ k := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact IsPGroup.iff_card.mp (hS.isPGroup.to_le hX)

theorem three_mul_card_le {X Y : Subgroup G} (hX : X ≤ P) (hYX : Y ≤ X) (hne : Y ≠ X) :
    3 * Nat.card Y ≤ Nat.card X := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq hX
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hYX
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hne (Subgroup.eq_of_le_of_card_ge hYX (by rw [hm, mul_one]))
  have hmdvd : m ∣ 3 ^ k := ⟨Nat.card Y, by rw [← hk, hm, mul_comm]⟩
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hmdvd
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hm1 (pow_zero 3)
  have h3 : 3 ≤ 3 ^ j := by
    calc 3 = 3 ^ 1 := (pow_one 3).symm
      _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.pos_of_ne_zero hj0)
  rw [hm, mul_comm]
  exact Nat.mul_le_mul_left _ h3

theorem three_le_card {X : Subgroup G} (hX : X ≤ P) (hne : X ≠ ⊥) : 3 ≤ Nat.card X := by
  have h := hS.three_mul_card_le hX bot_le (Ne.symm hne)
  rwa [Subgroup.card_bot, mul_one] at h

theorem card_eq_three {X : Subgroup G} (hX : X ≤ P) (h3 : 3 ≤ Nat.card X)
    (h9 : Nat.card X < 9) : Nat.card X = 3 := by
  obtain ⟨k, hk⟩ := hS.exists_card_eq hX
  rw [hk] at h3 h9 ⊢
  have hk2 : k < 2 := by
    by_contra h
    push Not at h
    have h' : 3 ^ 2 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h
    exact absurd h9 (not_lt.mpr (by simpa using h'))
  interval_cases k
  · norm_num at h3
  · norm_num

theorem mem_of_mem_dImage {U : Subgroup G} (hAU : A ≤ U) {x : G} (hx : x ∈ qOf P B)
    (hd : ⁅x, c⁆ ∈ hS.dImage U) : x ∈ U := by
  obtain ⟨y, hyU, hyQ, hy⟩ := hS.mem_dImage.mp hd
  have hyi : y⁻¹ ∈ qOf P B := (qOf P B).inv_mem hyQ
  have h1 : ⁅x * y⁻¹, c⁆ = 1 := by
    rw [hS.commutator_mul hx hyi.1, hS.commutator_inv hyQ, hy, mul_inv_cancel]
  have h2 : x * y⁻¹ ∈ A := (hS.commutator_eq_one_iff ((qOf P B).mul_mem hx hyi)).mp h1
  have e : x = x * y⁻¹ * y := by group
  rw [e]
  exact U.mul_mem (hAU h2) hyU

theorem dImage_le {U V : Subgroup G} (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ V) {a : G}
    (haU : a ∈ U) (haA : a ∈ A) (haB : a ∉ B) : hS.dImage U ≤ V := by
  obtain ⟨i, hi, b, hb, rfl⟩ := Sec13.exists_pow_mul_of_mem hS.isElemAbelian hS.mem hS.eq_sup haA
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact haB (by simpa using hb)
  intro y hy
  obtain ⟨q, hqU, hqQ, rfl⟩ := hS.mem_dImage.mp hy
  have h := hcomm q hqU _ haU
  rw [hS.commutator_pow_mul hqQ hb i] at h
  exact mem_of_pow_mem (hS.pow_three_of_mem_plane (hS.commutator_mem hqQ.1)) hi hi0 h

variable {b₀ b₁ : G}

theorem zpowers_eq (hF : Flag P B b₀ b₁) {z : G} (hz : z ∈ Subgroup.zpowers b₀) (hz1 : z ≠ 1) :
    Subgroup.zpowers z = Subgroup.zpowers b₀ := by
  refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hz) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, hS.orderOf_flag hF,
    orderOf_eq_prime (hS.pow_three_of_mem_plane (hF.zpowers_le hz)) hz1]

theorem commutator_not_mem (hF : Flag P B b₀ b₁) {u q : G} (hu : u ∈ P) (huQ : u ∉ qOf P B)
    (hq : q ∈ qOf P B) (hδq : ⁅q, c⁆ = b₁) : ⁅u, q⁆ ∉ A := by
  intro h
  have h1 := (hS.commutator_eq_one_iff (hS.commutator_mem_qOf_of_mem_qOf hu hq)).mpr h
  rw [hS.commutator_commutator hu hq, hδq] at h1
  exact huQ ((hS.mem_qOf_iff_commutator hF hu).mpr h1)

theorem false_of_dImage_eq (hF : Flag P B b₀ b₁) {U : Subgroup G} (hU : U ≤ P) (hAU : A ≤ U)
    (hD : hS.dImage U = Subgroup.zpowers b₀)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ Subgroup.zpowers b₀)
    (hcube : ∀ x ∈ U, x ^ 3 ∈ Subgroup.zpowers b₀) {u : G} (huU : u ∈ U)
    (huQ : u ∉ qOf P B) : False := by
  have huP : u ∈ P := hU huU
  have hb₁P : b₁ ∈ P := hS.plane_le hF.mem_one
  obtain ⟨q, hqQ, hδq⟩ := hS.exists_commutator_eq hF.mem_one
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = ⁅u, b₁⁆ := ⟨_, rfl⟩
  have hχZ : χ ∈ Subgroup.zpowers b₀ := hχ ▸ hS.commutator_mem_zpowers hF huP hF.mem_one
  have hχ1 : χ ≠ 1 := fun h => huQ ((hS.mem_qOf_iff_commutator hF huP).mpr (hχ ▸ h))
  by_cases hab : ∀ x ∈ qOf P B, ∀ y ∈ qOf P B, ⁅x, y⁆ ∈ B
  ·
    have hqi : q⁻¹ ∈ qOf P B := (qOf P B).inv_mem hqQ
    have huqQ : u * q * u⁻¹ ∈ qOf P B := hS.conj_mem_qOf huP hqQ
    obtain ⟨s, hs⟩ : ∃ s, s = q⁻¹ * (u * q * u⁻¹) := ⟨_, rfl⟩
    have hsQ : s ∈ qOf P B := hs ▸ (qOf P B).mul_mem hqi huqQ
    have hub₁ : u * b₁ * u⁻¹ = χ * b₁ := by
      rw [hχ, commutatorElement_def, inv_mul_cancel_right]
    have hδs : ⁅s, c⁆ = χ := by
      rw [hs, hS.commutator_mul hqi huqQ.1, hS.commutator_inv hqQ, hS.commutator_conj huP hqQ, hδq,
        hub₁, ← hF.commute_of_mem hb₁P hχZ, inv_mul_cancel_left]
    have hsU : s ∈ U := hS.mem_of_mem_dImage hAU hsQ (by rw [hδs, hD]; exact hχZ)
    have hsA : s ∉ A := fun h => hχ1 (hδs ▸ (hS.commutator_eq_one_iff hsQ).mpr h)
    obtain ⟨z, hz⟩ : ∃ z, z = ⁅u, s⁆ := ⟨_, rfl⟩
    have hzZ : z ∈ Subgroup.zpowers b₀ := hz ▸ hcomm u huU s hsU
    have hus : u * s * u⁻¹ = z * s := by rw [hz, commutatorElement_def, inv_mul_cancel_right]
    have huq : u * q * u⁻¹ = q * s := by rw [hs, mul_inv_cancel_left]
    have hzu : u * z * u⁻¹ = z := by rw [hF.commute_of_mem huP hzZ, mul_inv_cancel_right]
    have hzs : z * s = s * z := (hF.commute_of_mem hsQ.1 hzZ).symm
    have e1 : u * (q * s) * u⁻¹ = q * s * (z * s) := by
      calc u * (q * s) * u⁻¹ = (u * q * u⁻¹) * (u * s * u⁻¹) := by group
        _ = q * s * (z * s) := by rw [huq, hus]
    have e2 : u * (q * s * (z * s)) * u⁻¹ = q * s * (z * s) * z * (z * s) := by
      calc u * (q * s * (z * s)) * u⁻¹
          = (u * q * u⁻¹) * (u * s * u⁻¹) * (u * z * u⁻¹) * (u * s * u⁻¹) := by group
        _ = q * s * (z * s) * z * (z * s) := by rw [huq, hus, hzu]
    have e3 : u ^ 3 * q * (u ^ 3)⁻¹ = q * s ^ 3 * z ^ 3 := by
      calc u ^ 3 * q * (u ^ 3)⁻¹ = u * (u * (u * q * u⁻¹) * u⁻¹) * u⁻¹ := by
            rw [_root_.pow_three]; group
        _ = q * s * (z * s) * z * (z * s) := by rw [huq, e1, e2]
        _ = q * s ^ 3 * z ^ 3 := mul_eq_pow_three hzs
    have hu3 : u ^ 3 * q * (u ^ 3)⁻¹ = q := by
      rw [← hS.commute_of_mem_qOf hqQ (hF.zpowers_le (hcube u huU)), mul_inv_cancel_right]
    rw [hu3, hS.pow_three_of_mem_plane (hF.zpowers_le hzZ), mul_one] at e3
    have hs3 : s ^ 3 = 1 := mul_left_cancel (e3.symm.trans (mul_one q).symm)
    exact hsA (hS.mem_of_pow_three_eq_one hab hsQ hs3)
  ·
    push Not at hab
    have huq : ⁅u, q⁆ ∈ qOf P B := hS.commutator_mem_qOf_of_mem_qOf huP hqQ
    obtain ⟨m₁, hm₁⟩ : ∃ m, m = ⁅q, u⁆ := ⟨_, rfl⟩
    have hm₁Q : m₁ ∈ qOf P B := hm₁ ▸ hS.commutator_mem_qOf hF hqQ.1 huP
    have hδm₁ : ⁅m₁, c⁆ = χ⁻¹ := by
      rw [hm₁, ← commutatorElement_inv u q, hS.commutator_inv huq,
        hS.commutator_commutator huP hqQ, hδq, hχ]
    have hχi : χ⁻¹ ∈ Subgroup.zpowers b₀ := (Subgroup.zpowers b₀).inv_mem hχZ
    have hm₁U : m₁ ∈ U := hS.mem_of_mem_dImage hAU hm₁Q (by rw [hδm₁, hD]; exact hχi)
    have hm₁1 : ⁅m₁, c⁆ ≠ 1 := by
      rw [hδm₁]
      exact inv_ne_one.mpr hχ1
    have hb₁m : ⁅q, c⁆ ∉ Subgroup.zpowers ⁅m₁, c⁆ := by
      rw [hδq, hδm₁]
      exact fun h => hF.not_mem (Subgroup.zpowers_le.mpr hχi h)
    obtain ⟨m₂, hm₂⟩ : ∃ m, m = ⁅q, m₁⁆ := ⟨_, rfl⟩
    have hm₂A : m₂ ∈ A :=
      hm₂ ▸ hS.commutator_qOf_le (Subgroup.commutator_mem_commutator hqQ hm₁Q)
    have hm₂B : m₂ ∉ B := hm₂ ▸ hS.commutator_not_mem_plane hab hqQ hm₁Q hm₁1 hb₁m
    obtain ⟨i, hi, b, hb, hm₂eq⟩ :=
      Sec13.exists_pow_mul_of_mem hS.isElemAbelian hS.mem hS.eq_sup hm₂A
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hm₂B (by rw [hm₂eq, pow_zero, one_mul]; exact hb)
    obtain ⟨m₃, hm₃⟩ : ∃ m, m = ⁅q, m₂⁆ := ⟨_, rfl⟩
    have hm₃eq : m₃ = b₁ ^ i := by rw [hm₃, hm₂eq, hS.commutator_pow_mul hqQ hb i, hδq]
    have h1 : q * u * q⁻¹ = m₁ * u := by rw [hm₁, commutatorElement_def, inv_mul_cancel_right]
    have h2 : q * m₁ * q⁻¹ = m₂ * m₁ := by rw [hm₂, commutatorElement_def, inv_mul_cancel_right]
    have h3 : q * m₂ * q⁻¹ = m₃ * m₂ := by rw [hm₃, commutatorElement_def, inv_mul_cancel_right]
    have hq3 : q ^ 3 ∈ B := hS.pow_three_mem_plane hqQ
    have hw₁ : ⁅q ^ 3, u⁆ ∈ Subgroup.zpowers b₀ := by
      rw [← commutatorElement_inv u (q ^ 3)]
      exact (Subgroup.zpowers b₀).inv_mem (hS.commutator_mem_zpowers hF huP hq3)
    have he1 : q ^ 3 * u * (q ^ 3)⁻¹ = ⁅q ^ 3, u⁆ * u := by
      rw [commutatorElement_def, inv_mul_cancel_right]
    obtain ⟨w, hw⟩ : ∃ w, w = ⁅m₁, m₂⁆ := ⟨_, rfl⟩
    have hwZ : w ∈ Subgroup.zpowers b₀ := hw ▸ hcomm m₁ hm₁U m₂ (hAU hm₂A)
    have h12 : m₁ * m₂ = w * (m₂ * m₁) := by rw [hw, commutatorElement_def]; group
    have hm₂P : m₂ ∈ P := hS.le_sylow hm₂A
    have hm₃P : m₃ ∈ P := hm₃eq ▸ P.pow_mem hb₁P i
    have hwc : m₃ * m₂ * m₂ * w = w * (m₃ * m₂ * m₂) :=
      hF.commute_of_mem (P.mul_mem (P.mul_mem hm₃P hm₂P) hm₂P) hwZ
    have heq := (he1.symm.trans (conj_pow_three_eq h1 h2 h3)).trans (mul_eq_of_mul_eq h12 hwc)
    rw [hS.pow_three hm₂A, mul_one] at heq
    have heq' : ⁅q ^ 3, u⁆ = w * m₃ * m₁ ^ 3 := mul_right_cancel heq
    have hm₃Z : m₃ ∈ Subgroup.zpowers b₀ := by
      have e : m₃ = w⁻¹ * ⁅q ^ 3, u⁆ * (m₁ ^ 3)⁻¹ := by rw [heq']; group
      rw [e]
      exact (Subgroup.zpowers b₀).mul_mem ((Subgroup.zpowers b₀).mul_mem
        ((Subgroup.zpowers b₀).inv_mem hwZ) hw₁) ((Subgroup.zpowers b₀).inv_mem (hcube m₁ hm₁U))
    rw [hm₃eq] at hm₃Z
    exact hF.not_mem (mem_of_pow_mem (hS.pow_three_of_mem_plane hF.mem_one) hi hi0 hm₃Z)

theorem card_le_of_section {U V : Subgroup G} (hU : U ≤ P) (hVU : V ≤ U)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ V) (hcube : ∀ x ∈ U, x ^ 3 ∈ V) :
    Nat.card U ≤ 27 * Nat.card V := by
  by_cases hV1 : V = ⊥
  ·
    subst hV1
    have hUel : CFSG.Assembly.IsElemAbelian 3 U :=
      ⟨⟨⟨fun x y => Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp
        (Subgroup.mem_bot.mp (hcomm x x.2 y y.2)))⟩⟩, fun x hx => Subgroup.mem_bot.mp (hcube x hx)⟩
    rw [Subgroup.card_bot, mul_one]
    exact hS.card_le U hU hUel
  have hVP : V ≤ P := hVU.trans hU
  have hv3 : 3 ≤ Nat.card V := hS.three_le_card hVP hV1
  obtain ⟨b₀, b₁, hF⟩ := hS.exists_flag
  have hZ3 : Nat.card (Subgroup.zpowers b₀) = 3 := by rw [Nat.card_zpowers, hS.orderOf_flag hF]
  have hd9 : Nat.card (hS.dImage U) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hS.card_plane]
    exact Subgroup.card_dvd_of_le (hS.dImage_le_plane U)
  have hd9' : Nat.card (hS.dImage U) ≤ 9 := Nat.le_of_dvd (by norm_num) hd9
  have ha27 : Nat.card (U ⊓ A : Subgroup G) ≤ 27 :=
    hS.card_eq ▸ Subgroup.card_le_of_le inf_le_right
  by_cases hUQ : U ≤ qOf P B
  ·
    have hcard := hS.card_eq_of_le_qOf hUQ
    rw [hcard]
    by_cases h1 : ∃ a ∈ U, a ∈ A ∧ a ∉ B
    · obtain ⟨a, haU, haA, haB⟩ := h1
      exact Nat.mul_le_mul ha27 (Subgroup.card_le_of_le (hS.dImage_le hcomm haU haA haB))
    · push Not at h1
      have ha9 : Nat.card (U ⊓ A : Subgroup G) ≤ 9 :=
        hS.card_plane ▸ Subgroup.card_le_of_le fun x hx => h1 x hx.1 hx.2
      calc Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U) ≤ 9 * 9 :=
            Nat.mul_le_mul ha9 hd9'
        _ = 27 * 3 := by norm_num
        _ ≤ 27 * Nat.card V := Nat.mul_le_mul_left _ hv3
  obtain ⟨u, huU, huQ⟩ : ∃ u ∈ U, u ∉ qOf P B := by
    by_contra h
    push Not at h
    exact hUQ h
  have huP : u ∈ P := hU huU
  have hχZ : ⁅u, b₁⁆ ∈ Subgroup.zpowers b₀ := hS.commutator_mem_zpowers hF huP hF.mem_one
  have hχ1 : ⁅u, b₁⁆ ≠ 1 := fun h => huQ ((hS.mem_qOf_iff_commutator hF huP).mpr h)
  have h3 := hS.card_le_three_mul hF hU
  rw [hS.card_inf_qOf U] at h3
  have hVA : b₁ ∈ hS.dImage U → 3 * Nat.card (V ⊓ A : Subgroup G) ≤ Nat.card V := by
    intro hb₁
    obtain ⟨q, hqU, hqQ, hδq⟩ := hS.mem_dImage.mp hb₁
    refine hS.three_mul_card_le hVP inf_le_left fun h => ?_
    have hmem : ⁅u, q⁆ ∈ V ⊓ A := by
      rw [h]
      exact hcomm u huU q hqU
    exact hS.commutator_not_mem hF huP huQ hqQ hδq hmem.2
  by_cases h1 : ∃ a ∈ U, a ∈ A ∧ a ∉ B
  ·
    obtain ⟨a, haU, haA, haB⟩ := h1
    have hDV : hS.dImage U ≤ V := hS.dImage_le hcomm haU haA haB
    have hdv : Nat.card (hS.dImage U) ≤ Nat.card V := Subgroup.card_le_of_le hDV
    by_cases hAU : A ≤ U
    ·
      have hZV : Subgroup.zpowers b₀ ≤ V := by
        rw [← hS.zpowers_eq hF hχZ hχ1]
        exact Subgroup.zpowers_le.mpr (hcomm u huU b₁ (hAU (hS.le hF.mem_one)))
      rw [inf_eq_right.mpr hAU, hS.card_eq] at h3
      suffices hkey : 3 * Nat.card (hS.dImage U) ≤ Nat.card V by
        calc Nat.card U ≤ 3 * (27 * Nat.card (hS.dImage U)) := h3
          _ = 27 * (3 * Nat.card (hS.dImage U)) := by ring
          _ ≤ 27 * Nat.card V := Nat.mul_le_mul_left _ hkey
      obtain ⟨k, hk, hdk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd9
      interval_cases k
      · rw [hdk, pow_zero, mul_one]
        exact hv3
      · rw [hdk, pow_one]
        by_contra hlt
        push Not at hlt
        have hV3 : Nat.card V = 3 := hS.card_eq_three hVP hv3 (by omega)
        have hVZ : V = Subgroup.zpowers b₀ :=
          (Subgroup.eq_of_le_of_card_ge hZV (by rw [hV3, hZ3])).symm
        have hDZ : hS.dImage U = Subgroup.zpowers b₀ :=
          Subgroup.eq_of_le_of_card_ge (hVZ ▸ hDV) (by rw [hZ3, hdk, pow_one])
        subst hVZ
        exact hS.false_of_dImage_eq hF hU hAU hDZ hcomm hcube huU huQ
      · have hDB : hS.dImage U = B :=
          Subgroup.eq_of_le_of_card_ge (hS.dImage_le_plane U) (by rw [hS.card_plane, hdk]; norm_num)
        have h9 : 9 ≤ Nat.card (V ⊓ A : Subgroup G) :=
          hS.card_plane ▸ Subgroup.card_le_of_le (le_inf (hDB ▸ hDV) hS.le)
        have h27 := hVA (by rw [hDB]; exact hF.mem_one)
        rw [hdk]
        norm_num
        omega
    ·
      have ha9 : 3 * Nat.card (U ⊓ A : Subgroup G) ≤ 27 := by
        rw [← hS.card_eq]
        exact hS.three_mul_card_le hS.le_sylow inf_le_right fun h =>
          hAU (by rw [← h]; exact inf_le_left)
      calc Nat.card U ≤ 3 * (Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U)) := h3
        _ = (3 * Nat.card (U ⊓ A : Subgroup G)) * Nat.card (hS.dImage U) := by ring
        _ ≤ 27 * Nat.card (hS.dImage U) := Nat.mul_le_mul_right _ ha9
        _ ≤ 27 * Nat.card V := Nat.mul_le_mul_left _ hdv
  ·
    push Not at h1
    have hUAB : U ⊓ A ≤ B := fun x hx => h1 x hx.1 hx.2
    have ha9 : Nat.card (U ⊓ A : Subgroup G) ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hS.card_plane]
      exact Subgroup.card_dvd_of_le hUAB
    have ha9' : Nat.card (U ⊓ A : Subgroup G) ≤ 9 := Nat.le_of_dvd (by norm_num) ha9
    by_cases hv9 : 9 ≤ Nat.card V
    · calc Nat.card U ≤ 3 * (Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U)) := h3
        _ ≤ 3 * (9 * 9) := Nat.mul_le_mul_left _ (Nat.mul_le_mul ha9' hd9')
        _ = 27 * 9 := by norm_num
        _ ≤ 27 * Nat.card V := Nat.mul_le_mul_left _ hv9
    push Not at hv9
    obtain ⟨i, hi, hai⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp ha9
    obtain ⟨j, hj, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd9
    by_cases hij : i = 2 ∧ j = 2
    ·
      exfalso
      obtain ⟨rfl, rfl⟩ := hij
      have hUA : U ⊓ A = B :=
        Subgroup.eq_of_le_of_card_ge hUAB (by rw [hai, hS.card_plane]; norm_num)
      have hDB : hS.dImage U = B :=
        Subgroup.eq_of_le_of_card_ge (hS.dImage_le_plane U) (by rw [hdj, hS.card_plane]; norm_num)
      have hχV : ⁅u, b₁⁆ ∈ V ⊓ A :=
        ⟨hcomm u huU b₁ (hUA.ge hF.mem_one).1, hS.le (hF.zpowers_le hχZ)⟩
      have h3' : 3 ≤ Nat.card (V ⊓ A : Subgroup G) :=
        hS.three_le_card (inf_le_left.trans hVP) fun h => hχ1 (by
          rw [h] at hχV
          exact Subgroup.mem_bot.mp hχV)
      have h27 := hVA (by rw [hDB]; exact hF.mem_one)
      omega
    · have had : Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U) ≤ 27 := by
        rw [hai, hdj]
        interval_cases i <;> interval_cases j <;> first | exact absurd ⟨rfl, rfl⟩ hij | norm_num
      calc Nat.card U ≤ 3 * (Nat.card (U ⊓ A : Subgroup G) * Nat.card (hS.dImage U)) := h3
        _ ≤ 3 * 27 := Nat.mul_le_mul_left _ had
        _ = 27 * 3 := by norm_num
        _ ≤ 27 * Nat.card V := Nat.mul_le_mul_left _ hv3

theorem sectional : HasSectionalThreeRankThree P := by
  refine ⟨fun U V _ hU hel => ?_, ?_⟩
  · set N := V.subgroupOf U with hN
    have hmem : ∀ g : U, QuotientGroup.mk' N g = 1 → (g : G) ∈ V ⊓ U := by
      intro g hg
      have hgN : g ∈ N := by
        rw [← QuotientGroup.ker_mk' N]
        exact MonoidHom.mem_ker.mpr hg
      exact ⟨Subgroup.mem_subgroupOf.mp hgN, g.2⟩
    have hcomm : ∀ x ∈ U, ∀ y ∈ U, ⁅x, y⁆ ∈ V ⊓ U := by
      intro x hx y hy
      have h := hmem ⁅(⟨x, hx⟩ : U), (⟨y, hy⟩ : U)⁆ (by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hel.toIsMulCommutative.is_comm.comm _ _)
      simpa [commutatorElement_def] using h
    have hcube : ∀ x ∈ U, x ^ 3 ∈ V ⊓ U := by
      intro x hx
      have h3 : ∀ g : U ⧸ N, g ^ 3 = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (hel.exponent_dvd_p)
      have h := hmem ((⟨x, hx⟩ : U) ^ 3) (by rw [map_pow]; exact h3 _)
      simpa using h
    have hle := hS.card_le_of_section hU inf_le_right hcomm hcube
    have hNc : Nat.card N = Nat.card (V ⊓ U : Subgroup G) := by
      rw [hN, ← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective U.subtype_injective]
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hNc] at hle
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
  · refine ⟨A, ⊥, by rw [Subgroup.bot_subgroupOf]; infer_instance, hS.le_sylow, ?_, ?_⟩
    · refine { is_comm := ⟨fun a b => ?_⟩, exponent_dvd_p := ?_ }
      · induction a using QuotientGroup.induction_on with | H x => ?_
        induction b using QuotientGroup.induction_on with | H y => ?_
        exact congrArg (QuotientGroup.mk (s := (⊥ : Subgroup G).subgroupOf A))
          (Subtype.ext (hS.comm x.2 y.2))
      · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => ?_
        induction g using QuotientGroup.induction_on with | H x => ?_
        have hx3 : x ^ 3 = 1 := Subtype.ext (by simpa using hS.pow_three x.2)
        rw [← QuotientGroup.mk_pow, hx3, QuotientGroup.mk_one]
    · have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ((⊥ : Subgroup G).subgroupOf A)
      have h1 : Nat.card ((⊥ : Subgroup G).subgroupOf A) = 1 := by
        rw [Subgroup.bot_subgroupOf, Subgroup.card_bot]
      rw [h1, mul_one, hS.card_eq] at h
      exact h.symm

end CaseTwo

end SylowFive

end CFSG.RankThree.PartTwo.Sec18
