module


import CFSG.RankThree.GF2n.Stroth78.Sec3Five
import CFSG.RankThree.GF2n.Stroth78.Sec3Seven
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndCenter
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUEndPlane
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ThreeTranspositions.FischerResidual
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec3Comp
public import CFSG.RankThree.GF2n.Stroth78.Sec3Lbar
public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions CFSG.GroupTheory.ThreeTranspositions
open CFSG.Blueprint.Fischer CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

attribute [local instance] Xsub_normal

namespace Sec4PSUEnd

private theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {Y : Type*} [Group Y] {ρ y : Y}
    (hρ3 : ρ ^ 3 = 1) (hy : y ∈ Subgroup.zpowers ρ) : y = 1 ∨ y = ρ ∨ y = ρ⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h3 : ρ ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hρ3
  have hk : ρ ^ k = ρ ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, h3, one_zpow, one_mul]
  rw [hk]
  obtain ⟨m, hm⟩ : ∃ m, m = k % 3 := ⟨_, rfl⟩
  have h0 : 0 ≤ m := hm ▸ Int.emod_nonneg k (by norm_num)
  have h1 : m < 3 := hm ▸ Int.emod_lt_of_pos k (by norm_num)
  rw [← hm]
  interval_cases m
  · exact Or.inl (zpow_zero ρ)
  · exact Or.inr (Or.inl (zpow_one ρ))
  · refine Or.inr (Or.inr ?_)
    rw [show (2 : ℤ) = 3 - 1 by norm_num, zpow_sub_one, h3, one_mul]

theorem exists_mem_Lbar_mul_inv_eq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a)
    (hpsu : fischerCentralQuotientModel
      (threeResidualClass (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 4 x y)
      (fischerTransvections (fischerHermitianF4 4) fun v => v ≠ 0 ∧ fischerHermitianF4 4 v v = 0))
    (hw : w ≤ 5) {ρ : Hbar z} (hρC : ρ ∈ Subgroup.centralizer (Xsub S a : Set (Hbar z)))
    (hρ1 : ρ ≠ 1) : ∃ l ∈ Lbar S a, l * ρ * l⁻¹ = ρ⁻¹ := by
  obtain ⟨hρ3, hρC'⟩ :=
    orderOf_eq_three_and_zpowers_eq_centralizer_Xsub S h h217 h3 hα hpsu hw hρC hρ1
  have hρpow : ρ ^ 3 = 1 := hρ3 ▸ pow_orderOf_eq_one ρ
  have hCn : (Subgroup.centralizer (Xsub S a : Set (Hbar z))).Normal := inferInstance
  have hLρ : Lbar S a ≤ Subgroup.normalizer (Subgroup.zpowers ρ : Set (Hbar z)) := by
    rw [hρC', Subgroup.normalizer_eq_top_iff.mpr hCn]
    exact le_top
  by_contra hne
  push Not at hne
  have hcomm : ∀ l ∈ Lbar S a, l * ρ = ρ * l := by
    intro l hl
    have hmem : l * ρ * l⁻¹ ∈ Subgroup.zpowers ρ := by
      rw [hρC']
      exact hCn.conj_mem ρ hρC l
    rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers hρpow hmem with h1 | h1 | h1
    · exfalso
      apply hρ1
      calc ρ = l⁻¹ * (l * ρ * l⁻¹) * l := by group
        _ = 1 := by rw [h1]; group
    · exact mul_inv_eq_iff_eq_mul.mp h1
    · exact absurd h1 (hne l hl)
  have hfixa : ∀ l ∈ Lbar S a, rhoLin S l (aVec S h.mem_Q) = aVec S h.mem_Q := fun l hl =>
    rhoLin_apply_eq_of_mem_fixSpaceOf S h.aVec_mem_fixSpaceOf hl
  have hfixy : ∀ l ∈ Lbar S a, ∀ y : Hbar z, l * y = y * l →
      rhoLin S l (rhoLin S y (aVec S h.mem_Q)) = rhoLin S y (aVec S h.mem_Q) := by
    intro l hl y hly
    rw [← LinearEquiv.mul_apply, ← rhoLin_mul, hly, rhoLin_mul, LinearEquiv.mul_apply,
      hfixa l hl]
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀X : α₀ ∈ Xsub S a :=
    subset_Xsub S a (Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1'))
  have hρα : ρ * α₀ = α₀ * ρ := (Subgroup.mem_centralizer_iff.mp hρC α₀ hα₀X).symm
  have hplane := (aVec_add_rhoLin_add_rhoLin_eq_zero S h h217 hρpow hρ1 hLρ hα₀R hα₀1' hρα).2
  apply h.not_forall_Lbar_fix_commSpace (fun β hβ γ hγ => stroth78_35 S h h217 h3 hβ hγ)
    (isA2Hbar_of_mem_Rbar S h.mem_Q h.isConj h.not_mem_ZQ h.mem_Qa h.centerIn_Qa_not_le_Q α₀
      hα₀R hα₀1')
  intro l hl v hv
  have hc : Commute l ρ := hcomm l hl
  rcases hplane v hv with rfl | rfl | rfl | rfl
  · exact map_zero _
  · exact hfixa l hl
  · exact hfixy l hl ρ hc.eq
  · exact hfixy l hl (ρ * ρ) (hc.mul_right hc).eq

end Sec4PSUEnd

end CFSG.RankThree.GF2n.Stroth78
