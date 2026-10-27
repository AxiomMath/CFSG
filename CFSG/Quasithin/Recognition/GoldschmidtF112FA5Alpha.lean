module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Sylow5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace FA5

set_option linter.unusedSectionVars false

theorem inv_of_involution_five {H : Type*} [Group H] {ξ σ : H} (hξ5 : ξ ^ 5 = 1) (hξ1 : ξ ≠ 1)
    (hσ : σ * σ = 1) (hmem : σ * ξ * σ⁻¹ ∈ Subgroup.zpowers ξ) (hne : σ * ξ * σ⁻¹ ≠ ξ) :
    σ * ξ * σ⁻¹ = ξ⁻¹ := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ξ = 5 := orderOf_eq_prime hξ5 hξ1
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h2 : ξ ^ (j * j) = ξ ^ (1 : ℤ) := by
    calc ξ ^ (j * j) = (ξ ^ j) ^ j := by rw [← zpow_mul]
      _ = (σ * ξ * σ⁻¹) ^ j := by rw [hj]
      _ = σ * ξ ^ j * σ⁻¹ := by rw [conj_zpow]
      _ = σ * (σ * ξ * σ⁻¹) * σ⁻¹ := by rw [hj]
      _ = (σ * σ) * ξ * (σ * σ)⁻¹ := by group
      _ = ξ ^ (1 : ℤ) := by rw [hσ]; group
  have h3 : j * j ≡ 1 [ZMOD (orderOf ξ : ℤ)] := zpow_eq_zpow_iff_modEq.mp h2
  rw [hord] at h3
  have h4 : (j % 5) * (j % 5) % 5 = 1 := by
    have := h3
    unfold Int.ModEq at this
    rw [Int.mul_emod] at this
    simpa using this
  have h5 : ξ ^ j = ξ ^ (j % 5) := by
    have := zpow_mod_orderOf ξ j
    rw [hord] at this
    simpa using this.symm
  have hr0 : 0 ≤ j % 5 := Int.emod_nonneg _ (by norm_num)
  have hr5 : j % 5 < 5 := Int.emod_lt_of_pos _ (by norm_num)
  have hcases : j % 5 = 1 ∨ j % 5 = 4 := by
    generalize j % 5 = r at *
    interval_cases r <;> omega
  rcases hcases with h | h
  · exfalso
    apply hne
    rw [← hj, h5, h]
    simp
  · rw [← hj, h5, h]
    have : ξ ^ (4 : ℤ) * ξ = 1 := by
      calc ξ ^ (4 : ℤ) * ξ = ξ ^ 5 := by group
        _ = 1 := hξ5
    exact eq_inv_of_mul_eq_one_left this

namespace Frame

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G} (F : Frame L1 L2 S D X)
include F

noncomputable def pi1 (L1 L2 S : Subgroup G) :
    ↥(P1 L1 L2 S) →* oTwoQuot ↥(P1 L1 L2 S) :=
  QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(P1 L1 L2 S))

omit F in
theorem pi1_eq_one_iff (g : ↥(P1 L1 L2 S)) :
    pi1 L1 L2 S g = 1 ↔ (g : G) ∈ Q1 L1 L2 S := by
  show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥(P1 L1 L2 S)) g = 1 ↔ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact F1.mem_pCore_iff_coe g

omit F in
theorem pi1_eq_iff (g h : ↥(P1 L1 L2 S)) :
    pi1 L1 L2 S g = pi1 L1 L2 S h ↔ (g : G)⁻¹ * (h : G) ∈ Q1 L1 L2 S := by
  rw [← inv_mul_eq_one, ← map_inv, ← map_mul, pi1_eq_one_iff]
  rfl

theorem mem_Q1_of_commute {u : ↥(P1 L1 L2 S)} (hu : (u : G) ∈ S)
    (h : ∀ x : ↥(P1 L1 L2 S), (x : G) ∈ X →
      pi1 L1 L2 S u * pi1 L1 L2 S x = pi1 L1 L2 S x * pi1 L1 L2 S u) : (u : G) ∈ Q1 L1 L2 S := by
  refine F.mem_Q1_of_conj_mem hu (fun x hx => ?_)
  have hxP : x ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx
  have hc := h ⟨x, hxP⟩ hx
  have h1 : pi1 L1 L2 S (⟨x, hxP⟩⁻¹ * u * ⟨x, hxP⟩) = pi1 L1 L2 S u := by
    rw [map_mul, map_mul, map_inv, mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h2 := (pi1_eq_iff _ _).mp h1.symm
  have h3 : x⁻¹ * (u : G) * x = (u : G) * ((u : G)⁻¹ * (x⁻¹ * (u : G) * x)) := by group
  rw [h3]
  have h4 : (u : G)⁻¹ * (x⁻¹ * (u : G) * x) ∈ Q1 L1 L2 S := h2
  exact (bigB L1 L2 S).mul_mem (F.mem_B_of_mem_S hu) (F.mem_B_of_mem_S (F.Q1_le_S h4))

theorem inv_of_involution {s : G} (hs : s ∈ S) (hs2 : s * s ∈ Q1 L1 L2 S)
    (hsQ : s ∉ Q1 L1 L2 S) {x : G} (hx : x ∈ X) :
    ∃ q ∈ Q1 L1 L2 S, s * x * s⁻¹ = x⁻¹ * q := by
  obtain ⟨x0, hx0, hx05, hx01, hgen⟩ := F.exists_gen
  have hsP : s ∈ P1 L1 L2 S := F.mem_P1_of_mem_S hs
  have hx0P : x0 ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx0
  set π := pi1 L1 L2 S with hπ
  set s' : ↥(P1 L1 L2 S) := ⟨s, hsP⟩ with hs'
  set x' : ↥(P1 L1 L2 S) := ⟨x0, hx0P⟩ with hx'
  set σ : oTwoQuot ↥(P1 L1 L2 S) := π s' with hσ
  set ξ : oTwoQuot ↥(P1 L1 L2 S) := π x' with hξ
  have hxj : ∀ j : ℤ, x0 ^ j ∈ P1 L1 L2 S := fun j => (P1 L1 L2 S).zpow_mem hx0P j
  have hπx : ∀ j : ℤ, π ⟨x0 ^ j, hxj j⟩ = ξ ^ j := by
    intro j
    rw [hξ, ← map_zpow]
    rfl
  have hξ5 : ξ ^ 5 = 1 := by
    rw [hξ, ← map_pow]
    have : x' ^ 5 = 1 := Subtype.ext (by simpa using hx05)
    rw [this, map_one]
  have hξ1 : ξ ≠ 1 := by
    intro h
    have h2 : x0 ∈ Q1 L1 L2 S := (pi1_eq_one_iff x').mp h
    have h3 : x0 ∈ S := F.Q1_le_S h2
    obtain ⟨k, hk⟩ := F.pair.hyp.hyp.h1.pgroup ⟨x0, h3⟩
    have hk' : x0 ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hg : Nat.gcd (2 ^ k) 5 = 1 := Nat.Coprime.pow_left k (by norm_num)
    have := pow_gcd_eq_one.mpr ⟨hk', hx05⟩
    rw [hg, pow_one] at this
    exact hx01 this
  have hσσ : σ * σ = 1 := by
    rw [hσ, ← map_mul, pi1_eq_one_iff]
    exact hs2
  have hmem : σ * ξ * σ⁻¹ ∈ Subgroup.zpowers ξ := by
    obtain ⟨y, hy, o, ho, hyo⟩ := F.conj_mem_X_mul (F.mem_B_of_mem_S hs) hx0
    obtain ⟨j, hj⟩ := hgen y hy
    have hsxP : s * x0 * s⁻¹ ∈ P1 L1 L2 S :=
      (P1 L1 L2 S).mul_mem ((P1 L1 L2 S).mul_mem hsP hx0P) ((P1 L1 L2 S).inv_mem hsP)
    have h1 : σ * ξ * σ⁻¹ = π ⟨s * x0 * s⁻¹, hsxP⟩ := by
      show σ * ξ * σ⁻¹ = π (s' * x' * s'⁻¹)
      rw [map_mul, map_mul, map_inv]
    have h2 : π ⟨s * x0 * s⁻¹, hsxP⟩ = π ⟨x0 ^ j, hxj j⟩ := by
      rw [pi1_eq_iff]
      show (s * x0 * s⁻¹)⁻¹ * x0 ^ j ∈ Q1 L1 L2 S
      have : (s * x0 * s⁻¹)⁻¹ * x0 ^ j = o⁻¹ := by
        rw [hyo, hj]
        group
      rw [this]
      exact (Q1 L1 L2 S).inv_mem (F.pCore_L1_le_Q1 ho)
    rw [h1, h2, hπx]
    exact Subgroup.zpow_mem_zpowers ξ j
  have hne : σ * ξ * σ⁻¹ ≠ ξ := by
    intro hc
    apply hsQ
    refine F.mem_Q1_of_commute (u := s') hs (fun z hz => ?_)
    obtain ⟨j, hj⟩ := hgen z hz
    have hcomm : Commute σ ξ := mul_inv_eq_iff_eq_mul.mp hc
    have hzj : z = ⟨x0 ^ j, hxj j⟩ := Subtype.ext hj
    rw [hzj, hπx]
    exact hcomm.zpow_right j
  have hinv : σ * ξ * σ⁻¹ = ξ⁻¹ := inv_of_involution_five hξ5 hξ1 hσσ hmem hne
  obtain ⟨j, hj⟩ := hgen x hx
  have hxP : x ∈ P1 L1 L2 S := F.mem_P1_of_mem_X hx
  set xx : ↥(P1 L1 L2 S) := ⟨x, hxP⟩ with hxx
  have hxjP : xx = ⟨x0 ^ j, hxj j⟩ := Subtype.ext hj
  have h1 : π (s' * xx * s'⁻¹) = π xx⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv, hxjP, hπx, ← hσ, ← conj_zpow, hinv, inv_zpow]
  have h2 := (pi1_eq_iff _ _).mp h1
  have h2' : (s * x * s⁻¹)⁻¹ * x⁻¹ ∈ Q1 L1 L2 S := h2
  refine ⟨x * (s * x * s⁻¹), ?_, by group⟩
  have h3 : x * (s * x * s⁻¹) = ((s * x * s⁻¹)⁻¹ * x⁻¹)⁻¹ := by group
  rw [h3]
  exact (Q1 L1 L2 S).inv_mem h2'

theorem mul_inv_mem_Q1 {s t : G} (hs : s ∈ S) (ht : t ∈ S) (hs2 : s * s ∈ Q1 L1 L2 S)
    (ht2 : t * t ∈ Q1 L1 L2 S) (hsQ : s ∉ Q1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) :
    s * t⁻¹ ∈ Q1 L1 L2 S := by
  have hu : s * t⁻¹ ∈ S := S.mul_mem hs (S.inv_mem ht)
  have hsP : s ∈ P1 L1 L2 S := F.mem_P1_of_mem_S hs
  have htP : t ∈ P1 L1 L2 S := F.mem_P1_of_mem_S ht
  set π := pi1 L1 L2 S with hπ
  set s' : ↥(P1 L1 L2 S) := ⟨s, hsP⟩ with hs'
  set t' : ↥(P1 L1 L2 S) := ⟨t, htP⟩ with ht'
  have hτ2 : π t' * π t' = 1 := by
    rw [← map_mul, pi1_eq_one_iff]
    exact ht2
  have hτ : (π t')⁻¹ = π t' := inv_eq_of_mul_eq_one_right hτ2
  refine F.mem_Q1_of_commute (u := s' * t'⁻¹) hu (fun z hz => ?_)
  obtain ⟨q1, hq1, h1⟩ := F.inv_of_involution hs hs2 hsQ hz
  obtain ⟨q2, hq2, h2⟩ := F.inv_of_involution ht ht2 htQ hz
  have hS : π s' * π z * (π s')⁻¹ = (π z)⁻¹ := by
    have e : π s' * π z * (π s')⁻¹ = π (s' * z * s'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [e, ← map_inv, pi1_eq_iff]
    show (s * (z : G) * s⁻¹)⁻¹ * (z : G)⁻¹ ∈ Q1 L1 L2 S
    rw [h1]
    have : ((z : G)⁻¹ * q1)⁻¹ * (z : G)⁻¹ = q1⁻¹ := by group
    rw [this]
    exact (Q1 L1 L2 S).inv_mem hq1
  have hT : π t' * π z * (π t')⁻¹ = (π z)⁻¹ := by
    have e : π t' * π z * (π t')⁻¹ = π (t' * z * t'⁻¹) := by rw [map_mul, map_mul, map_inv]
    rw [e, ← map_inv, pi1_eq_iff]
    show (t * (z : G) * t⁻¹)⁻¹ * (z : G)⁻¹ ∈ Q1 L1 L2 S
    rw [h2]
    have : ((z : G)⁻¹ * q2)⁻¹ * (z : G)⁻¹ = q2⁻¹ := by group
    rw [this]
    exact (Q1 L1 L2 S).inv_mem hq2
  rw [map_mul, map_inv, hτ]
  have key : π s' * π t' * π z * (π s' * π t')⁻¹ = π z := by
    calc π s' * π t' * π z * (π s' * π t')⁻¹
        = π s' * (π t' * π z * (π t')⁻¹) * (π s')⁻¹ := by group
      _ = π s' * (π z)⁻¹ * (π s')⁻¹ := by rw [hT]
      _ = (π s' * π z * (π s')⁻¹)⁻¹ := by group
      _ = π z := by rw [hS, inv_inv]
  exact mul_inv_eq_iff_eq_mul.mp key

theorem relIndex_inf_Q1_le_two {E : Subgroup G} (hE : E ≤ S)
    (hE2 : ∀ e ∈ E, e * e ∈ Q1 L1 L2 S) : (E ⊓ Q1 L1 L2 S).relIndex E ≤ 2 := by
  by_cases hall : ∀ e ∈ E, e ∈ Q1 L1 L2 S
  · have : E ⊓ Q1 L1 L2 S = E := inf_eq_left.mpr hall
    rw [this, Subgroup.relIndex_self]
    norm_num
  · obtain ⟨e, he, heQ⟩ : ∃ e ∈ E, e ∉ Q1 L1 L2 S := by
      by_contra hcon
      exact hall fun e he => by_contra fun h => hcon ⟨e, he, h⟩
    have hidx : ((E ⊓ Q1 L1 L2 S).subgroupOf E).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨⟨e⁻¹, E.inv_mem he⟩, fun b => ?_⟩
      have hbE : (b : G) ∈ E := b.2
      by_cases hbQ : (b : G) ∈ Q1 L1 L2 S
      · right
        refine ⟨⟨hbE, hbQ⟩, fun hba => ?_⟩
        have : (b : G) * e⁻¹ ∈ Q1 L1 L2 S := hba.2
        exact heQ (by simpa using (Q1 L1 L2 S).mul_mem ((Q1 L1 L2 S).inv_mem hbQ) this)
      · left
        refine ⟨?_, fun hb => hbQ hb.2⟩
        have := F.mul_inv_mem_Q1 (hE hbE) (hE he) (hE2 _ hbE) (hE2 _ he) hbQ heQ
        exact ⟨E.mul_mem hbE (E.inv_mem he), this⟩
    exact hidx.le

end Frame

end FA5

end CFSG.Quasithin
