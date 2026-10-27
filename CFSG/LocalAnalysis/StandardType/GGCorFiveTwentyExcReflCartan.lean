module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Irreducible
import TauCeti.LinearAlgebra.RootSystem.FiniteType.TripleEdge

public section

namespace CFSG.StandardType

open TauCeti

section Diagram

variable {B B' : Type*}

theorem diagramGraph_transpose (A : Matrix B B ℤ) :
    diagramGraph A.transpose = diagramGraph A := by
  ext i j
  simp only [diagramGraph_adj, Matrix.transpose_apply]
  tauto

theorem connected_diagramGraph_reindex {A : Matrix B B ℤ} (e : B ≃ B')
    (h : (diagramGraph A).Connected) : (diagramGraph (Matrix.reindex e e A)).Connected := by
  rw [Matrix.reindex_apply, diagramGraph_submatrix e.symm.injective]
  exact (SimpleGraph.Iso.comap e.symm (diagramGraph A)).connected_iff.mpr h

theorem connected_of_ggIntCartan_reindex {n : ℕ} {M₀ : CoxeterMatrix (Fin n)}
    {C₀ : Matrix (Fin n) (Fin n) ℤ} (hC₀ : GGIntCartan M₀ C₀)
    (hconn₀ : (diagramGraph C₀).Connected) (hone : GGAtMostOneMultipleEdge M₀) {Γ : Type*}
    (e : Fin n ≃ Γ) {C : Matrix Γ Γ ℤ} (hC : GGIntCartan (M₀.reindex e) C) :
    (diagramGraph C).Connected := by
  have hr := connected_diagramGraph_reindex e hconn₀
  rcases hC.eq_or_eq_transpose (hC₀.reindex e) (hone.reindex e) with rfl | rfl
  · exact hr
  · rw [diagramGraph_transpose]
    exact hr

end Diagram

theorem connected_diagramGraph_of_ggIsWeylMatrix {Γ : Type} {M : CoxeterMatrix Γ}
    (hM : GGIsWeylMatrixFixed M) {C : Matrix Γ Γ ℤ} (hC : GGIntCartan M C) :
    (diagramGraph C).Connected := by
  rcases hM with ⟨n, e, hn, rfl | ⟨hn, rfl⟩ | ⟨hn, rfl⟩⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩ |
    ⟨e, rfl⟩ | ⟨e, rfl⟩
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .A n) (DynkinType.valid_A.mpr hn)
    simp only [DynkinType.rank_A, DynkinType.cartanMatrix_A] at h
    exact connected_of_ggIntCartan_reindex (ggIntCartan_A n) h (ggAtMostOneMultipleEdge_A n) e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .B n) (DynkinType.valid_B.mpr hn)
    simp only [DynkinType.rank_B, DynkinType.cartanMatrix_B] at h
    exact connected_of_ggIntCartan_reindex (ggIntCartan_B n) h (ggAtMostOneMultipleEdge_B n) e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .D n) (DynkinType.valid_D.mpr hn)
    simp only [DynkinType.rank_D, DynkinType.cartanMatrix_D] at h
    exact connected_of_ggIntCartan_reindex (ggIntCartan_D n) h (ggAtMostOneMultipleEdge_D n) e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .E6) DynkinType.valid_E6
    simp only [DynkinType.rank_E6, DynkinType.cartanMatrix_E6] at h
    exact connected_of_ggIntCartan_reindex ggIntCartan_E₆ h ggAtMostOneMultipleEdge_E₆ e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .E7) DynkinType.valid_E7
    simp only [DynkinType.rank_E7, DynkinType.cartanMatrix_E7] at h
    exact connected_of_ggIntCartan_reindex ggIntCartan_E₇ h ggAtMostOneMultipleEdge_E₇ e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .E8) DynkinType.valid_E8
    simp only [DynkinType.rank_E8, DynkinType.cartanMatrix_E8] at h
    exact connected_of_ggIntCartan_reindex ggIntCartan_E₈ h ggAtMostOneMultipleEdge_E₈ e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .F4) DynkinType.valid_F4
    simp only [DynkinType.rank_F4, DynkinType.cartanMatrix_F4] at h
    exact connected_of_ggIntCartan_reindex ggIntCartan_F₄ h ggAtMostOneMultipleEdge_F₄ e hC
  · have h := DynkinType.connected_diagramGraph_cartanMatrix (t := .G2) DynkinType.valid_G2
    simp only [DynkinType.rank_G2, DynkinType.cartanMatrix_G2] at h
    rw [diagramGraph_transpose] at h
    exact connected_of_ggIntCartan_reindex ggIntCartan_G₂ h ggAtMostOneMultipleEdge_G₂ e hC

theorem mem_of_reachable_of_closed {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {a b : V} (hab : G.Reachable a b) (ha : a ∈ S) :
    b ∈ S := by
  obtain ⟨w⟩ := hab
  induction w with
  | nil => exact ha
  | cons hadj w ih => exact ih (hS _ ha _ hadj)

theorem ggCartan_closed_eq_univ {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Λ : Type} [Fintype Λ]
    {M : CoxeterMatrix Λ} (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h3 : 3 ≤ Fintype.card Λ) {S : Set Λ} (hne : S.Nonempty)
    (hS : ∀ k ∈ S, ∀ j, (C j k : ZMod p) ≠ 0 → j ∈ S) : S = Set.univ := by
  classical
  have hFT : IsFiniteType C := isFiniteType_of_ggIsWeylMatrixFixed (hM : GGIsWeylMatrixFixed M) hC
  have hconn := connected_diagramGraph_of_ggIsWeylMatrix (hM : GGIsWeylMatrixFixed M) hC
  have hent : ∀ j k, j ≠ k → C j k ≠ 0 → C j k = -1 ∨ C j k = -2 := by
    intro j k hjk hne'
    rcases hC.entries hjk with ⟨-, h0, -⟩ | ⟨-, h1, -⟩ | ⟨-, h1 | h1⟩ | ⟨-, h1⟩
    · exact absurd h0 hne'
    · exact Or.inl h1
    · exact Or.inl h1.1
    · exact Or.inr h1.1
    · exfalso
      have hprod : C j k * C k j = 3 := by
        rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
      have := hFT.card_eq_two_of_apply_mul_apply_eq_three hconn.preconnected hprod
      omega
  have hmod : ∀ j k, j ≠ k → C j k ≠ 0 → (C j k : ZMod p) ≠ 0 := by
    intro j k hjk hne'
    rcases hent j k hjk hne' with h | h
    · rw [h]
      simp
    · rw [h]
      have := zmod_two_ne_zero hp2
      simpa using this
  have hadj : ∀ u ∈ S, ∀ v, (diagramGraph C).Adj u v → v ∈ S := by
    intro u hu v huv
    rw [diagramGraph_adj] at huv
    exact hS u hu v (hmod v u (Ne.symm huv.1) huv.2.2)
  obtain ⟨a, ha⟩ := hne
  exact Set.eq_univ_of_forall fun b => mem_of_reachable_of_closed hadj (hconn.preconnected a b) ha

open Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggCartan_functionals_vanish_of_moving_coroots_mem_axis
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h3 : 3 ≤ Fintype.card Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (x : V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hfixed : ∃ i, α i x = 0)
    (haxis : ∀ i, α i x ≠ 0 → h i ∈ Submodule.span (ZMod p) {x}) :
    ∀ i, α i x = 0 := by
  classical
  intro i
  by_contra hi
  let S : Set Λ := {j | α j x ≠ 0}
  have hS : S = Set.univ := ggCartan_closed_eq_univ hp2 hM hC h3
    (Set.nonempty_of_mem hi) (by
      intro k hk j hjk
      change α j x ≠ 0
      intro hj
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (haxis k hk)
      apply hjk
      rw [← hpair, ← hc, map_smul, hj, smul_zero])
  obtain ⟨j, hj⟩ := hfixed
  have hjS : j ∈ S := by rw [hS]; trivial
  exact hjS hj

theorem ggCartan_exists_moving_coroot_outside_axis
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Λ : Type} [Fintype Λ] {M : CoxeterMatrix Λ}
    (hM : GGIsWeylMatrix M) {C : Matrix Λ Λ ℤ} (hC : GGIntCartan M C)
    (h3 : 3 ≤ Fintype.card Λ)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V) (x : V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (hfixed : ∃ i, α i x = 0) (hmoving : ∃ i, α i x ≠ 0) :
    ∃ i, α i x ≠ 0 ∧ h i ∉ Submodule.span (ZMod p) {x} := by
  classical
  by_contra hnone
  have haxis : ∀ i, α i x ≠ 0 → h i ∈ Submodule.span (ZMod p) {x} := by
    intro i hi
    by_contra hout
    exact hnone ⟨i, hi, hout⟩
  obtain ⟨i, hi⟩ := hmoving
  exact hi (ggCartan_functionals_vanish_of_moving_coroots_mem_axis
    hp2 hM hC h3 h α x hpair hfixed haxis i)

end CFSG.StandardType
