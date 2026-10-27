module

public import CFSG.LocalAnalysis.StandardType.GGHalfJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylCentOmega
public import CFSG.LocalAnalysis.StandardType.GGHalfSlOnLevi

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix GGHalf
open scoped commutatorElement

private lemma commutator_mul_mul_of_commute {G : Type*} [Group G] {a b s t : G}
    (has : Commute a s) (hat : Commute a t) (hab : Commute a b)
    (hbs : Commute b s) (hbt : Commute b t) :
    ⁅a * s, b * t⁆ = ⁅s, t⁆ := by
  have h1 : ⁅a * s, b * t⁆ = a * (s * b * t * s⁻¹) * a⁻¹ * (t⁻¹ * b⁻¹) := by
    rw [commutatorElement_def]; group
  have ha' : Commute a (s * b * t * s⁻¹) :=
    ((has.mul_right hab).mul_right hat).mul_right has.inv_right
  have h2 : a * (s * b * t * s⁻¹) * a⁻¹ = s * b * t * s⁻¹ := ha'.mul_inv_cancel
  have h3 : s * b * t * s⁻¹ * (t⁻¹ * b⁻¹) = s * (b * (t * s⁻¹ * t⁻¹) * b⁻¹) := by group
  have hb' : Commute b (t * s⁻¹ * t⁻¹) := (hbt.mul_right hbs.inv_right).mul_right hbt.inv_right
  have h4 : b * (t * s⁻¹ * t⁻¹) * b⁻¹ = t * s⁻¹ * t⁻¹ := hb'.mul_inv_cancel
  rw [h1, h2, h3, h4, commutatorElement_def]
  group

private lemma le_of_perfect_of_commutators {G : Type*} [Group G] {J L : Subgroup G}
    (hJ : commutator ↥J = ⊤) (h : ∀ g ∈ J, ∀ k ∈ J, ⁅g, k⁆ ∈ L) : J ≤ L := by
  have hJJ : ⁅J, J⁆ = J := by
    have h1 := congrArg (Subgroup.map J.subtype) hJ
    rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at h1
    exact h1
  rw [← hJJ]
  exact Subgroup.commutator_le.mpr h

theorem GGHalfJoin.le_range_slLower2Hom_of_perfect_of_commute {m : ℕ}
    {J : Subgroup (SpecialLinearGroup (Fin (m + 1 + 1 + 1)) F2)} (hJ : commutator ↥J = ⊤)
    (hc : ∀ g ∈ J, g * omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ =
      omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩ * g) :
    J ≤ (slLower2Hom m).range := by
  rw [range_slLower2Hom]
  have hS : {i : Fin (m + 1 + 1 + 1) | i ≠ (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).castSucc ∧
      i ≠ (⟨0, Nat.succ_pos _⟩ : Fin (m + 1 + 1)).succ} = {i | 2 ≤ i.val} := by
    ext i
    simp only [Set.mem_setOf_eq, ne_eq, Fin.ext_iff, Fin.val_succ, Fin.coe_castSucc]
    omega
  refine le_of_perfect_of_commutators hJ ?_
  intro g hg k hk
  obtain ⟨a, ha, s, hs, rfl⟩ := mem_centralizer_omegaBlock m ⟨0, Nat.succ_pos _⟩ g (hc g hg)
  obtain ⟨b, hb, t, ht, rfl⟩ := mem_centralizer_omegaBlock m ⟨0, Nat.succ_pos _⟩ k (hc k hk)
  have hωs : Commute (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩) s :=
    commute_omegaBlock_slOn (by simp) hs
  have hωt : Commute (omegaBlock (m + 1 + 1) ⟨0, Nat.succ_pos _⟩) t :=
    commute_omegaBlock_slOn (by simp) ht
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  rw [commutator_mul_mul_of_commute (hωs.zpow_left i) (hωt.zpow_left i)
    ((Commute.refl _).zpow_zpow i j) (hωs.zpow_left j) (hωt.zpow_left j)]
  rw [hS] at hs ht
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hs ht) (inv_mem hs)) (inv_mem ht)

end CFSG.StandardType

end
