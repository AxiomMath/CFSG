module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4ComponentIdent
public import CFSG.LocalAnalysis.StandardType.GGInnerD4Regimes
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.RankThree.PartOne.KC.OrthogonalLocalComponents

public section

namespace CFSG.StandardType.S2MathAs51600DGenFixed

open CFSG CFSG.Assembly
open CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.KCOrthogonal

@[expose] def CentralizerImageRewrite : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2]
    (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V),
    (QuadraticMap.polarBilin Q).Nondegenerate →
    (∃ U : Submodule K V, Module.finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) →
    ∀ (X : Type) [Group X]
      (θ : X ⧸ Subgroup.center X ≃* ProjOrthDerived Q)
      (σ : MulAut X) (x : orthDerived Q),
      MulAut.conj
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x) =
          ggInducedAut θ σ →
      ggAutFixedSubgroup (ggInducedAut θ σ) =
        centralizerImage Q (x : V ≃ₗ[K] V)

theorem centralizerImageRewrite_holds : CentralizerImageRewrite := by
  intro K _ _ _ V _ _ _ Q hQ hT X _ θ σ x hrep
  classical
  obtain ⟨U, hU3, -⟩ := hT
  have hUne : U ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hU3
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  haveI : Nontrivial V := ⟨⟨u, 0, hu0⟩⟩
  have hinj : Function.Injective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) :=
    CFSG.RankThree.PartOne.S15K.mk_injective_orth hQ
  have hsurj : Function.Surjective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) :=
    QuotientGroup.mk'_surjective _
  have hfix : ggAutFixedSubgroup
        (MulAut.conj (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x)) =
      Subgroup.centralizer
        ({QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x} :
          Set (ProjOrthDerived Q)) := by
    ext g
    rw [mem_ggAutFixedSubgroup, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    · intro h
      rw [MulAut.conj_apply, mul_inv_eq_iff_eq_mul]
      exact h.symm
  have hmap : (Subgroup.centralizer ({x} : Set ↥(orthDerived Q))).map
        (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) =
      Subgroup.centralizer
        ({QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)) x} :
          Set (ProjOrthDerived Q)) := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      rw [← map_mul, ← map_mul, hy]
    · intro hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hg
      obtain ⟨y, rfl⟩ := hsurj g
      refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hg
  rw [← hrep, hfix, ← hmap]
  exact CFSG.RankThree.PartOne.map_centralizer_eq_centralizerImage x

end CFSG.StandardType.S2MathAs51600DGenFixed

end
