module

public import CFSG.OddTranspositions.PartThree.EightEight.StarBlocks

import CFSG.OddTranspositions.PartThree.EightEight.Seventeen
import CFSG.OddTranspositions.SixNineUnconditional

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem mul_mem_of_commute_of_mem_of_mem (h86 : Lemma8_6) (h87 : Theorem8_7)
    (hC : HypothesisC D) (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {a b : G} (ha : a ∈ ρ) (hb : b ∈ ρ) (hab : a ≠ b)
    (hcomm : Commute a b) : a * b ∈ D := by
  classical
  have hZ : Subgroup.center G = ⊥ := Asc72.eq_bot_of_le_center hrad le_rfl
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨g, hg⟩ := mem_blockClass_iff.mp (mem_blockClass_of_mem_blockClass hρ hβ.1)
  let a' : G := g * a * g⁻¹
  let b' : G := g * b * g⁻¹
  have ha' : a' ∈ β := by rw [hg]; exact ⟨a, ha, rfl⟩
  have hb' : b' ∈ β := by rw [hg]; exact ⟨b, hb, rfl⟩
  have ha'b' : a' ≠ b' := by
    intro h
    apply hab
    calc a = g⁻¹ * a' * g := by simp only [a']; group
      _ = g⁻¹ * b' * g := by rw [h]
      _ = b := by simp only [b']; group
  have hcomm' : Commute a' b' := by
    have h := hcomm.conj g
    simpa only [a', b'] using h
  obtain ⟨γ, hγ, hγβ, hmain⟩ :=
    exists_odd_or_isThirdKind_of_commute_of_mem h86 h87 hC hrad hO4 hF hβ ha' hb' ha'b'
      hcomm'
  obtain ⟨c, hc⟩ := nonempty_of_mem_blockClass hC.isBlock_alpha.nonempty hγ.1
  obtain ⟨htri, hodd | h3⟩ := hmain c hc
  · have hmem : a' * b' ∈ D :=
      IsTriangle.mul_mem_of_odd hC.setup.oddT hC.setup.normal htri hodd
    have hback := hC.setup.conj_mem g⁻¹ hmem
    have heq : g⁻¹ * (a' * b') * g⁻¹⁻¹ = a * b := by
      simp only [a', b']
      group
    rwa [heq] at hback
  · exfalso
    have hcβ : c ∈ β := mem_of_isThirdKind_of_mem hC hZ htri h3 hβ.1 ha' hb'
    have hγβ' : γ = β :=
      eq_of_mem_of_mem_blockClass hC.isBlock_alpha hγ.1 hβ.1 ⟨c, hc, hcβ⟩
    rw [hγβ'] at hγβ
    exact hγβ (mem_perp_iff.mpr (Or.inr rfl))

end CFSG.OddTranspositions.PartThree.EightEight
