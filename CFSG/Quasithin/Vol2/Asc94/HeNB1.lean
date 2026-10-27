module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4Cz

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

structure Sec4SettingNB (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F : Subgroup G) : Prop where
  frame : Frame G A A R g E F
  type : TypeL34 (rankTwoQuot A)
  even : Even (Nat.card (center A))
  top : rankTwoX A ⊔ R = ⊤

structure Sec4QNB (G : Type) [Group G] [Finite G] (A R : Subgroup G) (g : G)
    (E F S₁ Q : Subgroup G) (z : G) : Prop where
  setting : Sec4SettingNB G A R g E F
  sylowN : IsSylowOf 2 S₁ (normalizer ((E ⊔ F : Subgroup G) : Set G))
  sylow : IsSylowOf 2 S₁ ⊤
  le : Q ≤ S₁
  extraspecial : CFSG.IsExtraspecialPGroup 2 Q
  card : Nat.card Q = 2 ^ 7
  order_z : orderOf z = 2
  center_Q : centerIn Q = zpowers z
  center_S₁ : centerIn S₁ = zpowers z
  normE : Q ≤ normalizer (E : Set G)
  normF : Q ≤ normalizer (F : Set G)
  lt : Nat.card Q < Nat.card S₁

namespace Sec4QNB

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {g : G} {E F S₁ Q : Subgroup G}
  {z : G}

theorem le_centralizer (hQ : Sec4QNB G A R g E F S₁ Q z) :
    S₁ ≤ centralizer ({z} : Set G) := by
  intro s hs
  have hz : z ∈ centerIn S₁ := by rw [hQ.center_S₁]; exact mem_zpowers z
  rw [mem_centralizer_singleton_iff]
  exact (mem_centralizer_iff.mp hz.2) s hs

theorem Q_le_centralizer (hQ : Sec4QNB G A R g E F S₁ Q z) : Q ≤ centralizer ({z} : Set G) :=
  hQ.le.trans hQ.le_centralizer

theorem z_ne_one (hQ : Sec4QNB G A R g E F S₁ Q z) : z ≠ 1 := by
  intro h
  have := hQ.order_z
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem commutator_mem (hQ : Sec4QNB G A R g E F S₁ Q z) {q v : G} (hq : q ∈ Q) (hv : v ∈ Q) :
    q * v * q⁻¹ * v⁻¹ ∈ zpowers z := by
  rw [← hQ.center_Q]
  have h1 : (⟨q, hq⟩ : Q) * ⟨v, hv⟩ * (⟨q, hq⟩ : Q)⁻¹ * (⟨v, hv⟩ : Q)⁻¹ ∈ center Q := by
    rw [← hQ.extraspecial.2.1]
    exact commutator_mem_commutator (mem_top _) (mem_top _)
  refine mem_centerIn.mpr
    ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hq hv) (Q.inv_mem hq)) (Q.inv_mem hv), ?_⟩
  rw [mem_centralizer_iff]
  intro w hw
  exact congrArg Subtype.val ((mem_center_iff.mp h1) ⟨w, hw⟩)

end Sec4QNB

end CFSG.ComponentClassification.AS81
