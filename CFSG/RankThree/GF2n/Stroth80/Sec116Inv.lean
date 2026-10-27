module

import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoCenter
import CFSG.RankThree.GF2n.Stroth80.Sec1110TwoFieldLe
import CFSG.RankThree.GF2n.Stroth80.Sec116
import CFSG.ClassicalGroups.Unitary.ThreeEven
import CFSG.RankThree.OddKernel.OddLift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.GF2n.Stroth80.Sec112Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec11BStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] {M Q Z B : Subgroup G}

theorem Ctx.exists_mem_Ebar_inv_conj_of_forall [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) {k : ℕ}
    (hk : Odd k)
    (h : ∀ d : XbarMod M Q Z B, orderOf d = 2 →
      ∃ τ : XbarMod M Q Z B, orderOf τ = k ∧ d⁻¹ * τ * d = τ⁻¹) :
    ∃ d ∈ Ebar M Q Z B, ∃ τ : Mbar M Q, Odd (orderOf τ) ∧ k ∣ orderOf τ ∧
      d⁻¹ * τ * d = τ⁻¹ := by
  obtain ⟨d₀, hd₀⟩ := hc.Ebar_nonempty ha2
  have hdX : d₀ ∈ Xbar M Q Z B := Subgroup.subset_closure hd₀
  have ht : orderOf (⟨d₀, hdX⟩ : ↥(Xbar M Q Z B)) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact Ctx.orderOf_eq_two_of_mem_Ebar hd₀
  obtain ⟨τ₁, hτ₁o, hτ₁⟩ := h _
    (CFSG.RankThree.OddKernel.orderOf_mk_eq_two (Subgroup.center ↥(Xbar M Q Z B))
      hc.odd_card_center_Xbar ht)
  have hodd₁ : Odd (orderOf τ₁) := by
    rw [hτ₁o]
    exact hk
  obtain ⟨τ, hτ, hτodd, hτdvd⟩ :=
    CFSG.ClassicalGroups.Unitary.exists_inv_conj_lift_of_odd_card hc.odd_card_center_Xbar
      (by rw [← ht]; exact pow_orderOf_eq_one _) hτ₁ hodd₁
  refine ⟨d₀, hd₀, (τ : Mbar M Q), ?_, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hτodd
  · rw [Subgroup.orderOf_coe, ← hτ₁o]
    exact hτdvd
  · simpa using congrArg (fun y : ↥(Xbar M Q Z B) => (y : Mbar M Q)) hτ

theorem Ctx.dvd_of_card_Z_eq_two_pow_of_forall [Finite G]
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n x a : ℕ} (hw : Width Q Z n)
    (ha2 : ∃ a ∈ LB M Q B, IsA2 Q Z a) (hx : 1 ≤ x)
    (h : ∀ d : XbarMod M Q Z B, orderOf d = 2 →
      ∃ τ : XbarMod M Q Z B, orderOf τ = 2 ^ x + 1 ∧ d⁻¹ * τ * d = τ⁻¹)
    (ha : Nat.card Z = 2 ^ a) : x ∣ a := by
  obtain ⟨d, hd, τ, hodd, hdvd, hτ⟩ := hc.exists_mem_Ebar_inv_conj_of_forall ha2
    (Even.add_one ((Nat.even_pow' (by omega)).mpr even_two)) h
  have h1 := stroth_11_6 hc hw hd hτ hodd
  rw [ha] at h1
  exact dvd_of_two_pow_add_one_dvd_sq_sub_one hx (hdvd.trans h1)

end CFSG.RankThree.GF2n.Stroth80
