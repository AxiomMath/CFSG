module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandTagsExcBasic
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerExcConj

public section

namespace CFSG.StandardType

namespace RootCentQL

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  RootCentExc

section Adjoint


variable {τ : Tag} {K : Type} [Field K]

theorem iff_of_adj (h2 : (2 : K) = 0) (F : RootOperatorFamily τ) {j k : Fin τ.rank}
    (h1 : τ.cartan k j = -1) (h1' : τ.cartan j k = -1) :
    GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) ↔
      GGRootCentQL (xPar F (Pi.single k 1) (1 : K)) := by
  obtain ⟨g, hg⟩ := exists_conj_xPar_single_of_adj h2 F h1 h1'
  constructor
  · intro h
    rw [← hg]
    exact h.conj g
  · intro h
    rw [← hg] at h
    exact h.of_conj

theorem of_mem_rootGroup [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    (hs : ∀ j, GGRootCentQL (xPar F (Pi.single j 1) (1 : K))) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) {z : adjointGroup τ K} (hz : z ∈ rootGroup F K γ) (hz1 : z ≠ 1) :
    GGRootCentQL z := by
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hγ hz hz1
  have h := hs j
  rw [← hg] at h
  exact h.of_conj

theorem exists_single [Finite K] [CharP K 2] (F : RootOperatorFamily τ)
    {θ : Fin τ.rank → ℤ} {i₀ : Fin τ.rank} (hd : HighRootData τ θ i₀)
    (h : GGRootCentQL (xPar F θ (1 : K))) :
    ∃ j, GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) := by
  have hx1 : xPar F θ (1 : K) ≠ 1 := by
    intro h'
    rw [← xPar_zero (F := F) θ] at h'
    exact one_ne_zero (xPar_injective hd.maxHeight.1 h')
  obtain ⟨g, j, hg⟩ := AutSt.exists_conj_xPar_single hd.maxHeight.1
    (xPar_mem hd.maxHeight.1 (1 : K)) hx1
  refine ⟨j, ?_⟩
  rw [← hg]
  exact h.conj g

theorem single_E6 [Finite K] [CharP K 2] (F : RootOperatorFamily .E6)
    (hθ : GGRootCentQL (xPar F e6HighRoot (1 : K))) (j : Fin Tag.E6.rank) :
    GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E6.rank → Prop := fun j => GGRootCentQL (xPar F (Pi.single j 1) (1 : K))
    with hP
  have step : ∀ a b : Fin Tag.E6.rank, Tag.cartan .E6 b a = -1 → Tag.cartan .E6 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj h2 F h h').trans hb
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
        (by decide) Iff.rfl)
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) (step _ ⟨2, by decide⟩ (by decide)
        (by decide) (step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl))
    · exact step _ ⟨4, by decide⟩ (by decide) (by decide) (step _ ⟨3, by decide⟩ (by decide)
        (by decide) (step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩
          (by decide) (by decide) Iff.rfl)))
  obtain ⟨j₁, hj₁⟩ := exists_single (K := K) F highRootData_E6 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem single_E7 [Finite K] [CharP K 2] (F : RootOperatorFamily .E7)
    (hθ : GGRootCentQL (xPar F e7HighRoot (1 : K))) (j : Fin Tag.E7.rank) :
    GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E7.rank → Prop := fun j => GGRootCentQL (xPar F (Pi.single j 1) (1 : K))
    with hP
  have step : ∀ a b : Fin Tag.E7.rank, Tag.cartan .E7 b a = -1 → Tag.cartan .E7 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj h2 F h h').trans hb
  have h3 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : P ⟨4, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : P ⟨5, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  obtain ⟨j₁, hj₁⟩ := exists_single (K := K) F highRootData_E7 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem single_E8 [Finite K] [CharP K 2] (F : RootOperatorFamily .E8)
    (hθ : GGRootCentQL (xPar F e8HighRoot (1 : K))) (j : Fin Tag.E8.rank) :
    GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  set P : Fin Tag.E8.rank → Prop := fun j => GGRootCentQL (xPar F (Pi.single j 1) (1 : K))
    with hP
  have step : ∀ a b : Fin Tag.E8.rank, Tag.cartan .E8 b a = -1 → Tag.cartan .E8 a b = -1 →
      (P b ↔ P ⟨0, by decide⟩) → (P a ↔ P ⟨0, by decide⟩) :=
    fun a b h h' hb => (iff_of_adj h2 F h h').trans hb
  have h3 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    step _ ⟨2, by decide⟩ (by decide) (by decide) (step _ ⟨0, by decide⟩ (by decide)
      (by decide) Iff.rfl)
  have h4 : P ⟨4, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨3, by decide⟩ (by decide) (by decide) h3
  have h5 : P ⟨5, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨4, by decide⟩ (by decide) (by decide) h4
  have h6 : P ⟨6, by decide⟩ ↔ P ⟨0, by decide⟩ := step _ ⟨5, by decide⟩ (by decide) (by decide) h5
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact step _ ⟨3, by decide⟩ (by decide) (by decide) h3
    · exact step _ ⟨0, by decide⟩ (by decide) (by decide) Iff.rfl
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact step _ ⟨6, by decide⟩ (by decide) (by decide) h6
  obtain ⟨j₁, hj₁⟩ := exists_single (K := K) F highRootData_E8 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

theorem single_F4 [Finite K] [CharP K 2] (F : RootOperatorFamily .F4)
    (hθ : GGRootCentQL (xPar F f4HighRoot (1 : K))) (j : Fin Tag.F4.rank) :
    GGRootCentQL (xPar F (Pi.single j 1) (1 : K)) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := (inferInstance : CharP K 2)
  set P : Fin Tag.F4.rank → Prop := fun j => GGRootCentQL (xPar F (Pi.single j 1) (1 : K))
    with hP
  let φ : MulAut (adjointGroup Tag.F4 K) := CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K
  have hφ3 : φ (xElement (τ := Tag.F4) ⟨3, by decide⟩ (1 : K)) =
      xElement (τ := Tag.F4) ⟨0, by decide⟩ 1 := by
    have h := CFSG.LieType.Ree.ReeTag.finiteExceptionalAut_xElement
      (t := CFSG.LieType.Ree.ReeTag.F4) (K := K) ⟨3, by decide⟩ 1
    rw [one_pow, show CFSG.LieType.Ree.ReeTag.F4.perm ⟨3, by decide⟩ = ⟨0, by decide⟩ by
      decide] at h
    exact h
  have h30 : P ⟨3, by decide⟩ ↔ P ⟨0, by decide⟩ := by
    simp only [hP, xPar_single_eq_xElement h2 F]
    constructor
    · intro h
      have h' := h.map φ
      rwa [hφ3] at h'
    · intro h
      have h' := h.map φ.symm
      rwa [← hφ3, MulEquiv.symm_apply_apply] at h'
  have h01 : P ⟨1, by decide⟩ ↔ P ⟨0, by decide⟩ := iff_of_adj h2 F (by decide) (by decide)
  have h20 : P ⟨2, by decide⟩ ↔ P ⟨0, by decide⟩ :=
    (iff_of_adj h2 F (k := ⟨3, by decide⟩) (by decide) (by decide)).trans h30
  have h0 : ∀ j, P j ↔ P ⟨0, by decide⟩ := by
    intro j
    fin_cases j
    · exact Iff.rfl
    · exact h01
    · exact h20
    · exact h30
  obtain ⟨j₁, hj₁⟩ := exists_single (K := K) F highRootData_F4 hθ
  exact (h0 j).2 ((h0 j₁).1 hj₁)

end Adjoint

end RootCentQL

end CFSG.StandardType
