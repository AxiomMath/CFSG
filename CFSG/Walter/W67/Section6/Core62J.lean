module

public import CFSG.Walter.W67.Section6.Core62H

public section

namespace CFSG.Walter.W67.Sec6

variable {G : Type} [Group G] [Finite G]

open BenderSuzuki.External BenderSuzuki.PFchapter1section1

section QuotAct

variable {S Z N : Subgroup G} [hZ : (Z.subgroupOf S).Normal]

omit [Finite G] hZ in
theorem map_conjAut_eq (hNS : N ≤ Subgroup.normalizer (S : Set G))
    (hNZ : N ≤ Subgroup.normalizer (Z : Set G)) (n : N) :
    (Z.subgroupOf S).map (conjAut (hNS n.2) : S →* S) = Z.subgroupOf S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : (y : G) ∈ Z := hy
    change (n : G) * y * (n : G)⁻¹ ∈ Z
    exact (Subgroup.mem_normalizer_iff.mp (hNZ n.2) y).mp hy'
  · intro hx
    have hx' : (x : G) ∈ Z := hx
    refine ⟨(conjAut (hNS n.2)).symm x, ?_, by simp⟩
    change (n : G)⁻¹ * x * n ∈ Z
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hNZ n.2)) x).mp hx'
    simpa using this

@[expose] def quotAct (hNS : N ≤ Subgroup.normalizer (S : Set G))
    (hNZ : N ≤ Subgroup.normalizer (Z : Set G)) : N →* MulAut (S ⧸ Z.subgroupOf S) where
  toFun n := QuotientGroup.congr (Z.subgroupOf S) (Z.subgroupOf S) (conjAut (hNS n.2))
    (map_conjAut_eq hNS hNZ n)
  map_one' := by
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H s =>
      rw [QuotientGroup.congr_mk, MulAut.one_apply]
      congr 1
      exact Subtype.ext (by simp [conjAut])
  map_mul' m n := by
    refine MulEquiv.ext fun v => ?_
    induction v using QuotientGroup.induction_on with
    | H s =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk]
      congr 1
      exact Subtype.ext (by simp [conjAut, mul_assoc])

omit [Finite G] in
theorem quotAct_mk (hNS : N ≤ Subgroup.normalizer (S : Set G))
    (hNZ : N ≤ Subgroup.normalizer (Z : Set G)) (n : N) (s : S) :
    quotAct hNS hNZ n (s : S ⧸ Z.subgroupOf S) =
      ((⟨n * s * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hNS n.2) s).mp s.2⟩ : S) :
        S ⧸ Z.subgroupOf S) := rfl

end QuotAct

omit [Finite G] in
theorem conj_pow_of_commute {a t : G} (hc : Commute (a * t * a⁻¹ * t⁻¹) a) (n : ℕ) :
    a ^ n * t * (a ^ n)⁻¹ * t⁻¹ = (a * t * a⁻¹ * t⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) * t * (a ^ (n + 1))⁻¹ * t⁻¹ =
        a * (a ^ n * t * (a ^ n)⁻¹ * t⁻¹) * a⁻¹ * (a * t * a⁻¹ * t⁻¹) := by
      rw [pow_succ']
      group
    rw [e, ih, ← (hc.pow_left n).eq, mul_inv_cancel_right, pow_succ]

namespace Hyp62

variable {r : ℕ} [Fact r.Prime] {J d x₀ y₀ : G} {P₀ P₁ M M₁ H₃ : Subgroup G}
  (h : Hyp62 r J d x₀ y₀ P₀ P₁ M M₁ H₃)
include h

section CaseCSmall

variable {S : Subgroup G} {w : G} (c : CaseC r J y₀ P₀ P₁ S w)
include c

theorem caseC_w_comm {b : G} (hb : b ∈ P₁) : b * w = w * b :=
  comm_of_inv (h.caseC_J_inv c) b (h.caseC_P₁_le c hb) w (caseC_w_mem c)

theorem caseC_inf_w : P₁ ⊓ Subgroup.zpowers w = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyP, hyw⟩ := Subgroup.mem_inf.mp hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hw1 : w ≠ 1 := fun h1 => c.hwY (h1 ▸ Subgroup.one_mem _)
  have hwo : orderOf w = r := orderOf_eq_prime c.hw.2.1 hw1
  have hyr : y ^ r = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyw
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, c.hw.2.1, one_zpow]
  have hyo : orderOf y = r := orderOf_eq_prime hyr hy1
  have hz := eq_of_le_cyclic (Subgroup.isCyclic_zpowers w) (Subgroup.zpowers_le.mpr hyw) le_rfl
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hyo, hwo])
  have hwP : w ∈ P₁ := (Subgroup.zpowers_le.mpr hyP) (hz ▸ Subgroup.mem_zpowers w)
  exact c.hwY (h.mem_Y_of_pow hwP c.hw.2.1)

theorem caseC_eq_sup (hδ : Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) ≤
    r * Nat.card P₁) : S ⊓ Subgroup.centralizer ({w} : Set G) = P₁ ⊔ Subgroup.zpowers w := by
  have hw1 : w ≠ 1 := fun h1 => c.hwY (h1 ▸ Subgroup.one_mem _)
  have hwo : orderOf w = r := orderOf_eq_prime c.hw.2.1 hw1
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.caseC_w_comm c hb
  have hle : P₁ ⊔ Subgroup.zpowers w ≤ S ⊓ Subgroup.centralizer ({w} : Set G) :=
    sup_le (h.caseC_P₁_le c) (Subgroup.zpowers_le.mpr (caseC_w_mem c))
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_sup_of_inf_eq_bot hwN (h.caseC_inf_w c), Nat.card_zpowers, hwo, mul_comm]
  exact hδ

theorem caseC_isT_x₀ (hδ : Nat.card ↥(S ⊓ Subgroup.centralizer ({w} : Set G)) ≤
    r * Nat.card P₁) : IsT S y₀ r x₀ := by
  have hyC := h.y₀_mem_centralizer c.hS c.hPS c.hJS c.hSP
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hQeq := h.caseC_eq_sup c hδ
  refine ⟨hx₀S, by rw [← h.orderOf_x₀, pow_orderOf_eq_one], fun s hs => ?_⟩
  have hc1 : x₀ * w * x₀⁻¹ * w⁻¹ ∈ Subgroup.zpowers y₀ := c.hw.2.2 x₀ hx₀S
  have hc' : w * x₀ * w⁻¹ * x₀⁻¹ ∈ Subgroup.zpowers y₀ := by
    have e : w * x₀ * w⁻¹ * x₀⁻¹ = (x₀ * w * x₀⁻¹ * w⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hc1
  have hXN : Subgroup.zpowers x₀ ≤
      Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx₀S).trans (h.caseC_normal c)
  obtain ⟨q, hq, x, hx, rfl⟩ := (mem_sup_iff_of_le_normalizer hXN).mp (h.caseC_sup c hs)
  rw [hQeq] at hq
  have hwN : Subgroup.zpowers w ≤ Subgroup.normalizer (P₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact h.caseC_w_comm c hb
  obtain ⟨b, hb, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hwN).mp hq
  obtain ⟨k, rfl⟩ := (isOfFinOrder_of_finite w).mem_powers_iff_mem_zpowers.mpr he
  have hbx : b * x₀ = x₀ * b := Subgroup.mem_centralizer_singleton_iff.mp (h.M_le (h.P₁_le_M hb))
  have hxx : x * x₀ * x⁻¹ = x₀ := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [(Commute.zpow_left (Commute.refl x₀) i).eq, mul_inv_cancel_right]
  have hxb : x₀ * b⁻¹ * x₀⁻¹ = b⁻¹ := by
    calc x₀ * b⁻¹ * x₀⁻¹ = b⁻¹ * (b * x₀) * b⁻¹ * x₀⁻¹ := by group
      _ = b⁻¹ * (x₀ * b) * b⁻¹ * x₀⁻¹ := by rw [hbx]
      _ = b⁻¹ := by group
  have hwk := conj_pow_of_commute (a := w) (t := x₀)
    (IsT.comm_of_mem_zpowers hyC hc' c.hw.1) k
  have hbS : b ∈ S := c.hPS (Subgroup.mem_sup_right hb)
  have hck : (w * x₀ * w⁻¹ * x₀⁻¹) ^ k ∈ Subgroup.zpowers y₀ := Subgroup.pow_mem _ hc' k
  have e : b * w ^ k * x * x₀ * (b * w ^ k * x)⁻¹ * x₀⁻¹ = (w * x₀ * w⁻¹ * x₀⁻¹) ^ k := by
    calc b * w ^ k * x * x₀ * (b * w ^ k * x)⁻¹ * x₀⁻¹
        = b * (w ^ k * (x * x₀ * x⁻¹) * (w ^ k)⁻¹ * x₀⁻¹) * (x₀ * b⁻¹ * x₀⁻¹) := by group
      _ = b * (w * x₀ * w⁻¹ * x₀⁻¹) ^ k * b⁻¹ := by rw [hxx, hwk, hxb]
      _ = (w * x₀ * w⁻¹ * x₀⁻¹) ^ k := by
          rw [← IsT.comm_of_mem_zpowers hyC hck hbS, mul_inv_cancel_right]
  rw [e]
  exact hck

theorem caseC_P₁_comm {b : G} (hb : b ∈ P₁) {s : G} (hs : s ∈ S) : b * s = s * b := by
  have hx₀S : x₀ ∈ S := c.hPS h.x₀_mem_P
  have hXN : Subgroup.zpowers x₀ ≤
      Subgroup.normalizer ((S ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) : Set G) :=
    (Subgroup.zpowers_le.mpr hx₀S).trans (h.caseC_normal c)
  obtain ⟨q, hq, x, hx, rfl⟩ := (mem_sup_iff_of_le_normalizer hXN).mp (h.caseC_sup c hs)
  have hbq : b * q = q * b := comm_of_inv (h.caseC_J_inv c) b (h.caseC_P₁_le c hb) q hq
  have hbx₀ : b * x₀ = x₀ * b := Subgroup.mem_centralizer_singleton_iff.mp (h.M_le (h.P₁_le_M hb))
  have hbx : b * x = x * b := by
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right (show Commute b x₀ from hbx₀) i).eq
  calc b * (q * x) = (b * q) * x := by group
    _ = q * (b * x) := by rw [hbq]; group
    _ = q * x * b := by rw [hbx]; group

theorem caseC_center_le {z : G} (hz : z ∈ S) (hzC : ∀ s ∈ S, z * s = s * z) : z ∈ P₁ := by
  have hzQ : z ∈ S ⊓ Subgroup.centralizer ({w} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr (hzC w c.hw.1)⟩
  exact h.caseC_inf_centralizer c hzQ (hzC x₀ (c.hPS h.x₀_mem_P))

theorem caseC_normalizer_P₁ :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (P₁ : Set G) := by
  intro n hn
  apply JT.mem_normalizer_of_conj_mem
  intro b hb
  have hbS : b ∈ S := c.hPS (Subgroup.mem_sup_right hb)
  refine h.caseC_center_le c ((Subgroup.mem_normalizer_iff.mp hn b).mp hbS) fun s hs => ?_
  have hs' : n⁻¹ * s * n ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) s).mp hs
    simpa using this
  have := h.caseC_P₁_comm c hb hs'
  calc n * b * n⁻¹ * s = n * (b * (n⁻¹ * s * n)) * n⁻¹ := by group
    _ = n * ((n⁻¹ * s * n) * b) * n⁻¹ := by rw [this]
    _ = s * (n * b * n⁻¹) := by group

end CaseCSmall

end Hyp62

end CFSG.Walter.W67.Sec6
