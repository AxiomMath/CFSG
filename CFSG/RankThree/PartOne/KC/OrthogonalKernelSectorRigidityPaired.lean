module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockDet
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityDescent
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityTransvection

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Setup

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {x : V ≃ₗ[K] V}
  {r : K[X]}

theorem smul_mem_of_stable {S : Submodule K V} (hS : ∀ v ∈ S, x v ∈ S) (c : AdjoinRoot r)
    (u : primaryComponent x.toLinearMap r) (hu : (u : V) ∈ S) :
    ((c • u : primaryComponent x.toLinearMap r) : V) ∈ S := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  rw [coe_mk_smul_primaryComponent]
  exact aeval_apply_mem_of_forall_mem (f := x.toLinearMap) hS f hu

theorem pair_linearIndependent [Fact (Irreducible r)] {S₁ S₂ : Submodule K V}
    (hS₁ : ∀ v ∈ S₁, x v ∈ S₁) (hS₂ : ∀ v ∈ S₂, x v ∈ S₂) (hdisj : Disjoint S₁ S₂)
    {u w : primaryComponent x.toLinearMap r} (hu : (u : V) ∈ S₁) (hw : (w : V) ∈ S₂)
    (hu0 : u ≠ 0) (hw0 : w ≠ 0) : LinearIndependent (AdjoinRoot r) ![u, w] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1 : ((s • u : primaryComponent x.toLinearMap r) : V) ∈ S₁ :=
    smul_mem_of_stable hS₁ s u hu
  have h2 : ((t • w : primaryComponent x.toLinearMap r) : V) ∈ S₂ :=
    smul_mem_of_stable hS₂ t w hw
  have h3 : s • u = -(t • w) := eq_neg_of_add_eq_zero_left hst
  have h4 : ((s • u : primaryComponent x.toLinearMap r) : V) ∈ S₂ := by
    rw [h3, Submodule.coe_neg]
    exact S₂.neg_mem h2
  have h5 : ((s • u : primaryComponent x.toLinearMap r) : V) = 0 :=
    Submodule.disjoint_def.mp hdisj _ h1 h4
  have h6 : ((t • w : primaryComponent x.toLinearMap r) : V) = 0 := by
    have h7 : ((t • w : primaryComponent x.toLinearMap r) : V) ∈ S₁ := by
      have : t • w = -(s • u) := by rw [h3, neg_neg]
      rw [this, Submodule.coe_neg]
      exact S₁.neg_mem h1
    exact Submodule.disjoint_def.mp hdisj _ h7 h2
  have h8 : s • u = 0 := Subtype.ext h5
  have h9 : t • w = 0 := Subtype.ext h6
  exact ⟨(smul_eq_zero.mp h8).resolve_right hu0, (smul_eq_zero.mp h9).resolve_right hw0⟩

end Setup

section Paired

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem exists_paired_mixing (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hne : r ≠ reciprocalPolynomial r)
    {S₁ S₂ : Submodule K V} (hS₁ : ∀ v ∈ S₁, x v ∈ S₁) (hS₂ : ∀ v ∈ S₂, x v ∈ S₂)
    (hdisj : Disjoint S₁ S₂) (h₁ : S₁ ⊓ primaryComponent x.toLinearMap r ≠ ⊥)
    (h₂ : S₂ ⊓ primaryComponent x.toLinearMap r ≠ ⊥) :
    2 ≤ primaryMultiplicity x.toLinearMap r ∧
      ∃ g ∈ specialBlock Q x r, ∃ v ∈ S₁, ∃ s ∈ S₁, ∃ t ∈ S₂, t ≠ 0 ∧ g v = s + t := by
  have : Fact (Irreducible r) := ⟨irreducible_of_mem_primaryFactors hr⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₁
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h₂
  let u : primaryComponent x.toLinearMap r := ⟨v, hv.2⟩
  let w' : primaryComponent x.toLinearMap r := ⟨w, hw.2⟩
  have hu0 : u ≠ 0 := fun h => hv0 (congrArg Subtype.val h)
  have hw0' : w' ≠ 0 := fun h => hw0 (congrArg Subtype.val h)
  have hind := pair_linearIndependent hS₁ hS₂ hdisj hv.1 hw.1 hu0 hw0'
  refine ⟨by simpa using hind.fintype_card_le_finrank, ?_⟩
  have hnot : u ∉ Submodule.span (AdjoinRoot r) {w'} := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have := (LinearIndependent.pair_iff.mp hind) (-1) c (by
      rw [neg_smul, one_smul, hc, neg_add_cancel])
    exact one_ne_zero (neg_eq_zero.mp this.1)
  obtain ⟨φ, hφu, hφw⟩ := exists_functional_of_not_mem_span hnot
  obtain ⟨g, hg⟩ := hx.blockGL_surjective_paired hr hne (transvectionUnit φ w' hφw)
  refine ⟨g.1, mem_specialBlock.mpr ⟨g.2, ?_⟩, v, hv.1, v, hv.1, w, hw.1, hw0, ?_⟩
  · rw [blockDet_apply, hg]
    exact det_transvectionUnit φ w' hφw
  · have h1 := coe_blockGL (Q := Q) (x := x) r g u
    rw [hg, transvectionUnit_apply, hφu, one_smul] at h1
    exact h1.symm

end Paired

end CFSG.RankThree.PartOne.KCOrthogonal
