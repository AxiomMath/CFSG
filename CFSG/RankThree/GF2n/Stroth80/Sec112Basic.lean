module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def A2Set (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal] : Set (Mbar M Q) :=
  {τ | ∃ e : M, (e : Mbar M Q) = τ ∧ IsA2 Q Z (e : G)}

theorem Ctx.mk_mem_A2Set [(Q.subgroupOf M).Normal] {a : G} (ha : a ∈ M) (hA : IsA2 Q Z a) :
    (QuotientGroup.mk (⟨a, ha⟩ : ↥M) : Mbar M Q) ∈ A2Set M Q Z :=
  ⟨⟨a, ha⟩, rfl, hA⟩

theorem Ctx.orderOf_eq_two_of_mem_A2Set [(Q.subgroupOf M).Normal] {τ : Mbar M Q}
    (hτ : τ ∈ A2Set M Q Z) : orderOf τ = 2 := by
  obtain ⟨e, rfl, hA⟩ := hτ
  have hne : (QuotientGroup.mk e : Mbar M Q) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    intro h
    exact hA.2.1 (Subgroup.mem_subgroupOf.mp h)
  have hsq : (QuotientGroup.mk e : Mbar M Q) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hA.2.2.1
  exact orderOf_eq_prime hsq hne

theorem Ctx.orderOf_eq_two_of_mem_Ebar [(Q.subgroupOf M).Normal] {τ : Mbar M Q}
    (hτ : τ ∈ Ebar M Q Z B) : orderOf τ = 2 :=
  Ctx.orderOf_eq_two_of_mem_A2Set hτ.1

theorem Ctx.Ebar_nonempty [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B)
    (ha : ∃ a ∈ LB M Q B, IsA2 Q Z a) : (Ebar M Q Z B).Nonempty := by
  obtain ⟨a, haL, hA⟩ := ha
  exact ⟨_, hc.mk_mem_Ebar haL hA⟩

@[expose] def EbarIsXbarClassStatement (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Prop :=
  ∃ e₀ ∈ Ebar M Q Z B, ∀ e : Mbar M Q,
    e ∈ Ebar M Q Z B ↔ ∃ x ∈ Xbar M Q Z B, e = x * e₀ * x⁻¹

@[expose] def EbarSqClosedStatement (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal] : Prop :=
  ∀ e₁ ∈ Ebar M Q Z B, ∀ e₂ ∈ Ebar M Q Z B, orderOf (e₁ * e₂) = 4 →
    (e₁ * e₂) ^ 2 ∈ Ebar M Q Z B

end CFSG.RankThree.GF2n.Stroth80
