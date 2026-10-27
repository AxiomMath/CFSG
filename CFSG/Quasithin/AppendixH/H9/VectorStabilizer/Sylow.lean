module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem utriGL_le_stabGL (m : ℕ) : utriGL (m + 1) ≤ stabGL m := by
  intro A hA
  have h := (mem_utriGL_iff (n := m + 1)).mp hA
  rw [mem_stabGL_iff, ez, Matrix.mulVec_single_one]
  ext i
  rw [Matrix.col_apply]
  by_cases hi : i = 0
  · subst hi
    simp [h.2]
  · rw [h.1 i 0 (Fin.pos_iff_ne_zero.mpr hi)]
    simp [Pi.single_apply, hi]

theorem T0_inf_stabSub_V1n_eq_centSub (m : ℕ) :
    T0 (m + 1) ⊓ stabSub (V1n (m + 1)) =
      T0 (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) := by
  rw [T0_inf_stabSub_V1n (n := m + 1) (Nat.succ_pos m)]
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · show pairActN (m + 1) A ∈
        (utriGL (m + 1)).map (pairActN (m + 1)) ⊔
          Subgroup.zpowers (pairActN (m + 1) (revGL (m + 1)) * swapN (m + 1))
      exact Subgroup.mem_sup_left (Subgroup.mem_map.mpr ⟨A, hA, rfl⟩)
    · exact (pairActN_mem_centSub_iff A).mpr (utriGL_le_stabGL m hA)
  · intro g hg
    obtain ⟨hgT, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgM : g ∈ Mg (m + 1) := T0_le_Mg (m + 1) hgT
    have hgL : g ∈ Lg (m + 1) := by
      have hmem : g ∈ Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) :=
        ⟨hgM, hgC⟩
      rw [Mg_inf_centSub_eq m] at hmem
      exact hmem.1
    have hmem : g ∈ T0 (m + 1) ⊓ Lg (m + 1) := ⟨hgT, hgL⟩
    rwa [T0_inf_Lg (n := m + 1) (Nat.succ_pos m)] at hmem

theorem isSylowIn_T0_inf_stabSub (m : ℕ) :
    IsSylowIn 2 (T0 (m + 1) ⊓ stabSub (V1n (m + 1)))
      (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) := by
  have hP : T0 (m + 1) ⊓ stabSub (V1n (m + 1)) =
      (utriGL (m + 1)).map (pairActN (m + 1)) :=
    T0_inf_stabSub_V1n (n := m + 1) (Nat.succ_pos m)
  have hH : Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) =
      Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) :=
    Mg_inf_centSub_eq m
  have hPH : (utriGL (m + 1)).map (pairActN (m + 1)) ≤
      Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) := by
    rw [Lg_inf_centSub_eq_map m]
    exact Subgroup.map_mono (utriGL_le_stabGL m)
  unfold IsSylowIn
  rw [hP, hH]
  refine ⟨hPH, ?_, ?_⟩
  · exact (isSylowIn_utriGL (m + 1)).isPGroup.map (pairActN (m + 1))
  · intro h2
    have hCL : Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) ≤ Lg (m + 1) :=
      inf_le_left
    have hmul := Subgroup.relIndex_mul_relIndex
      (H := (utriGL (m + 1)).map (pairActN (m + 1)))
      (K := Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)))
      (L := Lg (m + 1)) hPH hCL
    have hdvd : 2 ∣ ((utriGL (m + 1)).map (pairActN (m + 1))).relIndex (Lg (m + 1)) := by
      rw [← hmul]
      exact Dvd.dvd.mul_right h2 _
    have hrel : ((utriGL (m + 1)).map (pairActN (m + 1))).relIndex (Lg (m + 1)) =
        (utriGL (m + 1)).relIndex ⊤ := by
      rw [show Lg (m + 1) = (pairActN (m + 1)).range from rfl,
        ← Subgroup.map_top (pairActN (m + 1))]
      exact Subgroup.relIndex_map_map_of_injective _ _ (pairActN_injective (n := m + 1))
    rw [hrel] at hdvd
    exact (isSylowIn_utriGL (m + 1)).not_dvd_relIndex hdvd

end CFSG.ASVolI.ChH.VectorStabilizer
