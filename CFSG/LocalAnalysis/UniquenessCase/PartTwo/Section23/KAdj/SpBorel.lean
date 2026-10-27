module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

import CFSG.LocalAnalysis.UniquenessCase.UC22P22m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open SymplecticFlag (borelSubgroup unipotent)
open SymplecticHigher (flagStabilizer)
open KTabD (lineStab)
open Matrix

private lemma flag_succ_one_eq_span_singleton_C01 (m : ℕ) {K : Type} [Field K] :
    SymplecticFlag.flag (m + 1) K 1
      = Submodule.span K {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} := by
  have hset : (fun j : Fin (m + 1) =>
        (Pi.single (Sum.inl j) (1 : K) : Fin (m + 1) ⊕ Fin (m + 1) → K)) ''
        {j | (j : ℕ) < 1}
      = {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} := by
    ext v
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hjval : (j : ℕ) = 0 := Nat.lt_one_iff.mp hj
      have hj0 : j = 0 := Fin.ext (by simpa using hjval)
      subst hj0
      rfl
    · intro hv
      exact ⟨0, by simp, hv.symm⟩
  rw [SymplecticFlag.flag, ite_eq_left (show 1 ≤ m + 1 by omega), SymplecticFlag.isoFlag,
    hset]

private lemma gl_mulVec_injective_C01 {n : Type} [Fintype n] [DecidableEq n] {K : Type} [Field K]
    (u : GL n K) : Function.Injective (((u : GL n K) : Matrix n n K).mulVec) :=
  Matrix.mulVec_injective_iff_isUnit.mpr ⟨u, rfl⟩

private lemma mem_stabilizer_span_singleton_iff_C01 {r : ℕ} {K : Type} [Field K]
    {A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hA : Function.Injective A.mulVec)
    {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    (Submodule.span K {v}).map (Matrix.mulVecLin A) = Submodule.span K {v} ↔
      ∃ c : K, A *ᵥ v = c • v := by
  rw [Submodule.map_span, Set.image_singleton, Matrix.mulVecLin_apply]
  have hAv : A *ᵥ v ≠ 0 := fun h => hv (hA (by rw [h, Matrix.mulVec_zero]))
  constructor
  · intro h
    have hmem : A *ᵥ v ∈ Submodule.span K {v} := by
      rw [← h]
      exact Submodule.mem_span_singleton_self (A *ᵥ v)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := fun hcz => hAv (by rw [hc, hcz, zero_smul])
    rw [hc]
    exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc0) v

private lemma lineStab_statedSp_succ_eq_flagStabilizer_C01 (m : ℕ) {K : Type} [Field K] :
    lineStab (StatedSp (m + 1) K) (Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K))
      = SymplecticHigher.flagStabilizer (m + 1) K ({1} : Set ℕ) := by
  have hflag : SymplecticFlag.flag (m + 1) K 1
      = Submodule.span K {Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)} :=
    flag_succ_one_eq_span_singleton_C01 (K := K) m
  have hv : (Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K) :
      Fin (m + 1) ⊕ Fin (m + 1) → K) ≠ 0 := by
    intro h
    have h1 : (1 : K) = 0 := by
      simpa using congrFun h (Sum.inl (0 : Fin (m + 1)))
    exact one_ne_zero h1
  have hsingle : SymplecticHigher.flagStabilizer (m + 1) K ({1} : Set ℕ)
      = SymplecticFlag.stabilizer (m + 1) K (SymplecticFlag.flag (m + 1) K 1) := by
    apply le_antisymm
    · intro g hg
      rw [SymplecticHigher.mem_flagStabilizer] at hg
      exact hg 1 (by simp)
    · intro g hg
      rw [SymplecticHigher.mem_flagStabilizer]
      intro i hi
      rw [Set.mem_singleton_iff] at hi
      subst hi
      exact hg
  rw [hsingle, hflag]
  apply le_antisymm
  · intro γ hγ
    rw [KTabD.mem_lineStab] at hγ
    rw [SymplecticFlag.mem_stabilizer]
    rw [mem_stabilizer_span_singleton_iff_C01 (K := K) (A :=
      ((γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (gl_mulVec_injective_C01 (K := K) (γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (v := Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)) hv]
    exact hγ
  · intro γ hγ
    rw [SymplecticFlag.mem_stabilizer] at hγ
    rw [KTabD.mem_lineStab]
    rw [mem_stabilizer_span_singleton_iff_C01 (K := K) (A :=
      ((γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K) :
        Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (gl_mulVec_injective_C01 (K := K) (γ : GL (Fin (m + 1) ⊕ Fin (m + 1)) K))
      (v := Pi.single (Sum.inl (0 : Fin (m + 1))) (1 : K)) hv] at hγ
    exact hγ

theorem lineStab_statedSp_eq_flagStabilizer (m : ℕ) (K : Type) [Field K] :
    lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) = flagStabilizer (m + 2) K {1} :=
  lineStab_statedSp_succ_eq_flagStabilizer_C01 (m + 1) (K := K)

theorem flagStabilizer_inf_eq_borelSubgroup (m : ℕ) (K : Type) [Field K] :
    flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) ⊓ flagStabilizer (m + 2) K {1} =
      borelSubgroup (m + 2) K := by
  ext g
  rw [Subgroup.mem_inf, SymplecticHigher.mem_flagStabilizer,
    SymplecticHigher.mem_flagStabilizer, SymplecticFlag.mem_borelSubgroup]
  constructor
  · rintro ⟨h1, h2⟩ i hi1 hir
    rcases Nat.lt_or_ge i 2 with hi | hi
    · have hi1' : i = 1 := by omega
      subst hi1'
      exact h2 1 (by simp)
    · exact h1 i (Set.mem_Icc.mpr ⟨hi, hir⟩)
  · intro h
    refine ⟨fun i hi => h i (by have := hi.1; omega) hi.2, ?_⟩
    intro i hi
    rw [Set.mem_singleton_iff] at hi
    subst hi
    exact h 1 le_rfl (by omega)

theorem unipotent_le_normalizer_hinf_lineStab (m : ℕ) (K : Type) [Field K] :
    unipotent (m + 2) K ≤ Subgroup.normalizer
      (Hinf (lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1)) :
        Set (StatedSp (m + 2) K)) := by
  intro u hu
  have huB : u ∈ borelSubgroup (m + 2) K := SymplecticFlag.unipotent_le_borelSubgroup hu
  rw [← flagStabilizer_inf_eq_borelSubgroup] at huB
  have huQ : u ∈ lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
    rw [lineStab_statedSp_eq_flagStabilizer]
    exact huB.2
  exact uc22p22m_le_normalizer_Hinf _ huQ

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
