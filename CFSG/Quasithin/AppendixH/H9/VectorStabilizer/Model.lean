module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Block

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

theorem mem_centSub_zpowers_iff {V : Type*} [CommGroup V] {g : MulAut V} {v : V} :
    g ∈ centSub (Subgroup.zpowers v) ↔ g v = v := by
  constructor
  · intro h
    exact (mem_centSub.mp h) v (Subgroup.mem_zpowers v)
  · intro h
    refine mem_centSub.mpr fun u hu => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, h]

theorem ez_ne_zero : ez m ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [ez, Pi.single_eq_same, Pi.zero_apply] at h0
  exact one_ne_zero h0

theorem pairActN_mem_centSub_iff (A : GL (Fin (m + 1)) (ZMod 2)) :
    pairActN (m + 1) A ∈ centSub (Subgroup.zpowers (pairVec (ez m) 0)) ↔ A ∈ stabGL m := by
  have key : (pairActN (m + 1) A (pairVec (ez m) 0) = pairVec (ez m) 0) ↔ A ∈ stabGL m := by
    rw [pairActN_pairVec, Matrix.mulVec_zero, pairVec_inj, mem_stabGL_iff]
    simp
  exact mem_centSub_zpowers_iff.trans key

theorem Lg_inf_centSub_eq_map (m : ℕ) :
    Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) =
      (stabGL m).map (pairActN (m + 1)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
    obtain ⟨A, hA⟩ := mem_Lg_iff.mp hgL
    subst hA
    exact Subgroup.mem_map.mpr ⟨A, (pairActN_mem_centSub_iff A).mp hgC, rfl⟩
  · intro hg
    obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp hg
    subst hAg
    exact Subgroup.mem_inf.mpr ⟨pairActN_mem_Lg A, (pairActN_mem_centSub_iff A).mpr hA⟩

theorem mem_Lg_inf_centSub_iff {g : MulAut (PairN (m + 1))} :
    g ∈ Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) ↔
      ∃ A ∈ stabGL m, pairActN (m + 1) A = g := by
  rw [Lg_inf_centSub_eq_map, Subgroup.mem_map]

theorem Mg_inf_centSub_eq (m : ℕ) :
    Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) =
      Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgM, hgC⟩ := Subgroup.mem_inf.mp hg
    rcases mem_Mg_iff.mp hgM with hgL | ⟨A, hA⟩
    · exact Subgroup.mem_inf.mpr ⟨hgL, hgC⟩
    · exfalso
      have hv : g (pairVec (ez m) 0) = pairVec (ez m) 0 :=
        (mem_centSub.mp hgC) _ (Subgroup.mem_zpowers _)
      rw [hA, MulAut.mul_apply, swapN_pairVec, pairActN_pairVec, Matrix.mulVec_zero] at hv
      exact ez_ne_zero (pairVec_inj.mp hv).1.symm
  · intro g hg
    obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
    exact Subgroup.mem_inf.mpr ⟨Lg_le_Mg hgL, hgC⟩

end CFSG.ASVolI.ChH.VectorStabilizer
