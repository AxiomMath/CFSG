module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjLinear
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeAct

import CFSG.RankThree.GF2n.Stroth78.Sec3Six

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.RankThree.OrthogonalInvolutions
open CFSG.GroupTheory.ThreeTranspositions

namespace Sec4Five

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_mem_Rbar_fischerLinearModel (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [CommRing 𝕜]
    {M : Subgroup (GL ι 𝕜)} {T : Set (GL ι 𝕜)}
    (hO : CFSG.Open.fischerLinearModel
      (threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))) M T) :
    ∃ α₀ : Hbar z, ∃ hα₀ : α₀ ∈ Rbar S a, α₀ ≠ 1 ∧
      CFSG.Open.fischerLinearModel (threeResidualClass (alphaInX S h hα₀)) M T := by
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀E : α₀ ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1')
  obtain ⟨-, ⟨e, hE⟩, -, -, -⟩ := pair_Xsub S h h217 h3
  have hd : (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ∈
      (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := Tset_subset_Eset S a hα
  have hd₀E : alphaInX S h hα₀R ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := hα₀E
  rw [hE] at hd hd₀E
  have hc : IsConj (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a))
      (alphaInX S h hα₀R) :=
    (isConj_comm.1 hd).trans hd₀E
  exact ⟨α₀, hα₀R, hα₀1', fischerLinearModel_of_isConj hc hO⟩

end Sec4Five

end CFSG.RankThree.GF2n.Stroth78
