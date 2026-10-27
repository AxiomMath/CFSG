module

public import CFSG.Quasithin.AppendixH.H9.H93.S8Classes
public import CFSG.Quasithin.AppendixH.H9.H93.S8Unique.KleinInvolutions
public import CFSG.Quasithin.AppendixH.H9.H93.S8Unique.OrbitPartition

public section

namespace CFSG.ASVolI.ChH

open Equiv

private theorem kleinInvolution_mem_of_hasOrbitPartition {E : Subgroup (Perm (Fin 8))}
    (hE : IsElemAb2 E) (hc : Nat.card E = 16) {A : Finset (Fin 8)} (hA : HasOrbitPartition E A)
    (i : Fin 3) : kleinInvolution A i ∈ E := by
  rw [mem_e16_iff hE hc]
  intro x
  by_cases hx : x ∈ A
  · rw [hA.orbit_of_mem x hx]
    refine ⟨fun y hy => ?_, Or.inr fun y hy => ?_⟩
    · exact Finset.mem_coe.mpr (kleinInvolution_spec hA.card_eq i (Finset.mem_coe.mp hy)).1
    · exact ⟨(kleinInvolution_spec hA.card_eq i (Finset.mem_coe.mp hy)).2.1,
        (kleinInvolution_spec hA.card_eq i (Finset.mem_coe.mp hy)).2.2⟩
  · rw [hA.orbit_of_notMem x hx]
    refine ⟨fun y hy => ?_, Or.inl fun y hy => ?_⟩
    · have hyA : y ∉ A := Finset.mem_compl.mp (Finset.mem_coe.mp hy)
      rw [kleinInvolution_apply_of_notMem hA.card_eq i hyA]
      exact hy
    · exact kleinInvolution_apply_of_notMem hA.card_eq i
        (Finset.mem_compl.mp (Finset.mem_coe.mp hy))

private theorem eq_one_of_pow_three_eq_one_of_isPGroup_two {P : Subgroup (Perm (Fin 8))}
    (hP : IsPGroup 2 P) {σ : Perm (Fin 8)} (hσ : σ ∈ P) (h3 : σ ^ 3 = 1) : σ = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨σ, hσ⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [hk] at hdvd
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · exact orderOf_eq_one_iff.mp (by simpa using hk)
  · have h23 : 2 ∣ 3 := (dvd_pow_self 2 hk0.ne').trans hdvd
    omega

theorem e16_eq_of_le_twoGroup {E E' P : Subgroup (Perm (Fin 8))} (hE : IsElemAb2 E)
    (hc : Nat.card E = 16) (hE' : IsElemAb2 E') (hc' : Nat.card E' = 16)
    (hEA : E ≤ alternatingGroup (Fin 8)) (hE'A : E' ≤ alternatingGroup (Fin 8))
    (hP : IsPGroup 2 P) (hEP : E ≤ P) (hE'P : E' ≤ P) : E = E' := by
  obtain ⟨A, hA0, hA⟩ := exists_hasOrbitPartition_of_orbitSizesOf_eq
    ((e16_le_alternatingGroup_iff hE hc).mp hEA)
  obtain ⟨B, hB0, hB⟩ := exists_hasOrbitPartition_of_orbitSizesOf_eq
    ((e16_le_alternatingGroup_iff hE' hc').mp hE'A)
  by_cases hAB : A = B
  · subst hAB
    ext σ
    rw [mem_e16_iff hE hc σ, mem_e16_iff hE' hc' σ]
    simp only [hA.orbit_eq hB]
  · exfalso
    obtain ⟨C, hC, i, j, h3, h1⟩ :=
      exists_kleinInvolution_mul_order_three hA.card_eq hB.card_eq hA0 hB0 hAB
    have hmemE : kleinInvolution A i ∈ E := kleinInvolution_mem_of_hasOrbitPartition hE hc hA i
    have hmemE' : kleinInvolution C j ∈ E' := by
      rcases hC with rfl | rfl
      · exact kleinInvolution_mem_of_hasOrbitPartition hE' hc' hB j
      · exact kleinInvolution_mem_of_hasOrbitPartition hE' hc' hB.compl j
    exact h1 (eq_one_of_pow_three_eq_one_of_isPGroup_two hP
      (P.mul_mem (hEP hmemE) (hE'P hmemE')) h3)

end CFSG.ASVolI.ChH
