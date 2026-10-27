module

public import CFSG.Quasithin.Background.Harris.R1.QbetaData

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

namespace QD

variable {G : Type*} [Group G] [Finite G] {P S Q W Z M D : Subgroup G} {g y z : G}
variable (h : QD P S Q W Z M D g y z)
include h

theorem card_W_eq_two_mul : Nat.card W = 2 * Nat.card ↥(W ⊓ Q) := by
  obtain ⟨w0, hw0W, hw0Q⟩ := IsConcreteLE.not_le_iff_exists.mp h.vh.wq
  have hw0S : w0 ∈ S := h.vh.ws hw0W
  let H : Subgroup ↥W := (W ⊓ Q).subgroupOf W
  have hidx : H.index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨w0, hw0W⟩, fun b => ?_⟩
    have hbS : (b : G) ∈ S := h.vh.ws b.2
    by_cases hb : (b : G) ∈ Q
    · right
      refine ⟨Subgroup.mem_subgroupOf.mpr ⟨b.2, hb⟩, fun hbw => ?_⟩
      have := (Subgroup.mem_subgroupOf.mp hbw).2
      exact hw0Q (by simpa using Q.mul_mem (Q.inv_mem hb) this)
    · left
      refine ⟨?_, fun hbH => hb (Subgroup.mem_subgroupOf.mp hbH).2⟩
      have hbi : (b : G)⁻¹ ∉ Q := fun hh => hb (by simpa using Q.inv_mem hh)
      have := h.inv_mul_mem_Q (S.inv_mem hbS) hw0S hbi hw0Q
      refine Subgroup.mem_subgroupOf.mpr ⟨W.mul_mem b.2 hw0W, ?_⟩
      simpa using this
  have h1 : H.index * Nat.card H = Nat.card W := Subgroup.index_mul_card H
  have h2 : Nat.card H = Nat.card ↥(W ⊓ Q) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hidx, h2] at h1
  exact h1.symm

theorem card_A' (hW : Nat.card W = 32) : Nat.card ↥(conjSub g W ⊓ Q) = 16 := by
  have h1 := h.card_W_eq_two_mul
  have hA : Nat.card ↥(W ⊓ Q) = 16 := by omega
  have e : conjSub g (W ⊓ Q) = conjSub g W ⊓ Q := by
    rw [conjSub_inf, conjSub_eq_of_mem_normalizer (h.vh.qn h.hg)]
  rw [← e]
  exact (Vert.card_conjSub g _).trans hA

end QD

end CFSG.Quasithin.Background.Harris.R1
