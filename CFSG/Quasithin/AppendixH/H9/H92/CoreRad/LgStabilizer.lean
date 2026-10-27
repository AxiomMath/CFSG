module

public import CFSG.Quasithin.AppendixH.H9.H92.CoreRad.StabMat

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem pairActN_mem_stabSub_iff {n : ℕ} {U : Subgroup (PairN n)} (hU : U ≤ V1n n)
    (B : GL (Fin n) (ZMod 2)) :
    pairActN n B ∈ stabSub U ↔ B ∈ stabMat n (v1Space n U) := by
  constructor
  · intro h x
    have h1 := (mem_stabSub.mp h) (pairVec x 0)
    change pairVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x)
      (((dualGLn n B : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ 0) ∈ U ↔
        pairVec x 0 ∈ U at h1
    rw [Matrix.mulVec_zero] at h1
    exact h1
  · intro h
    refine mem_stabSub.mpr fun u => ?_
    by_cases hu : u ∈ V1n n
    · obtain ⟨a, b, rfl⟩ := pairVec_surj u
      have hb : b = 0 := ofAdd_eq_one.mp (mem_V1n.mp hu)
      subst hb
      change pairVec ((B : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ a)
        (((dualGLn n B : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ 0) ∈ U ↔
          pairVec a 0 ∈ U
      rw [Matrix.mulVec_zero]
      exact h a
    · have h2 : pairActN n B u ∉ V1n n := fun h' =>
        hu ((mem_stabSub.mp (Lg_le_stabSub_V1n (pairActN_mem_Lg B)) u).mp h')
      exact ⟨fun h3 => absurd (hU h3) h2, fun h3 => absurd (hU h3) hu⟩

theorem Lg_inf_stabSub_eq_map_stabMat {n : ℕ} {U : Subgroup (PairN n)} (hU : U ≤ V1n n) :
    Lg n ⊓ stabSub U = (stabMat n (v1Space n U)).map (pairActN n) := by
  ext g
  constructor
  · intro hg
    obtain ⟨A, rfl⟩ := mem_Lg_iff.mp (Subgroup.mem_inf.mp hg).1
    exact ⟨A, (pairActN_mem_stabSub_iff hU A).mp (Subgroup.mem_inf.mp hg).2, rfl⟩
  · rintro ⟨A, hA, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨pairActN_mem_Lg A, (pairActN_mem_stabSub_iff hU A).mpr hA⟩

end CFSG.ASVolI.ChH
