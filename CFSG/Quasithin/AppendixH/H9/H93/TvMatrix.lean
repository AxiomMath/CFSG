module

public import CFSG.Quasithin.AppendixH.H9.H93.TvMatrix.TvEltCount

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem isTvElt_iff_vec {g : MulAut (PairN 4)} (hg : g ∈ Lg 4) :
    IsTvElt g ↔ ∃ u f : Fin 4 → ZMod 2, u ≠ 0 ∧ f ≠ 0 ∧
      ∀ a : Fin 4 → ZMod 2, g (pairVec a 0) = pairVec (a + (f ⬝ᵥ a) • u) 0 := by
  obtain ⟨A, rfl⟩ := mem_Lg_iff.mp hg
  rw [isTvElt_pairActN_iff]
  constructor
  · rintro ⟨u, f, hu, hf, hA⟩
    refine ⟨u, f, hu, hf, fun a => ?_⟩
    rw [pairActN_pairVec, Matrix.mulVec_zero, hA, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  · rintro ⟨u, f, hu, hf, h⟩
    refine ⟨u, f, hu, hf, Matrix.ext_of_mulVec_single fun i => ?_⟩
    have h2 := h (Pi.single i 1)
    rw [pairActN_pairVec, Matrix.mulVec_zero] at h2
    rw [(pairVec_inj.mp h2).1, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
      op_smul_eq_smul]

theorem exists_isTvElt : ∃ g : MulAut (PairN 4), IsTvElt g := by
  exact ⟨pairActN 4 (transvectionGL ![1, 0, 0, 0] ![0, 0, 1, 0] (by decide)),
    (isTvElt_pairActN_iff _).mpr (isTvMat_transvectionGL (by decide) (by decide) (by decide))⟩

theorem isTvElt_sq {g : MulAut (PairN 4)} (h : IsTvElt g) : g ^ 2 = 1 ∧ g ≠ 1 := by
  obtain ⟨A, rfl⟩ := mem_Lg_iff.mp h.1
  have hA := (isTvElt_pairActN_iff A).mp h
  refine ⟨?_, fun h1 => hA.ne_one (pairActN_injective (h1.trans (map_one _).symm))⟩
  rw [← map_pow, pow_two, hA.mul_self, map_one]

theorem isTvElt_conj_of_mem_Mg {g h : MulAut (PairN 4)} (hg : g ∈ Mg 4) (hh : IsTvElt h) :
    IsTvElt (g * h * g⁻¹) := by
  obtain ⟨A, rfl⟩ := mem_Lg_iff.mp hh.1
  have hA := (isTvElt_pairActN_iff A).mp hh
  rcases mem_Mg_iff.mp hg with hgL | ⟨B, rfl⟩
  · obtain ⟨B, rfl⟩ := mem_Lg_iff.mp hgL
    have e : pairActN 4 B * pairActN 4 A * (pairActN 4 B)⁻¹ = pairActN 4 (B * A * B⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [e]
    exact (isTvElt_pairActN_iff _).mpr (hA.conj B)
  · have e : pairActN 4 B * swapN 4 * pairActN 4 A * (pairActN 4 B * swapN 4)⁻¹ =
        pairActN 4 (B * dualGLn 4 A * B⁻¹) := by
      have hs : swapN 4 * pairActN 4 A * swapN 4 = pairActN 4 (dualGLn 4 A) := by
        rw [swapN_mul_pairActN, mul_assoc, swapN_mul_self, mul_one]
      rw [map_mul, map_mul, map_inv, ← hs, mul_inv_rev, swapN_inv]
      group
    rw [e]
    exact (isTvElt_pairActN_iff _).mpr (hA.dualGLn.conj B)

theorem isTvElt_exists_conj_Lg {h h' : MulAut (PairN 4)} (hh : IsTvElt h) (hh' : IsTvElt h') :
    ∃ l ∈ Lg 4, l * h * l⁻¹ = h' := by
  obtain ⟨A, rfl⟩ := mem_Lg_iff.mp hh.1
  obtain ⟨A', rfl⟩ := mem_Lg_iff.mp hh'.1
  obtain ⟨C, hC⟩ := ((isTvElt_pairActN_iff A).mp hh).exists_conj
    ((isTvElt_pairActN_iff A').mp hh')
  refine ⟨pairActN 4 C, pairActN_mem_Lg C, ?_⟩
  rw [← hC, map_mul, map_mul, map_inv]

theorem ncard_isTvElt_le : Set.ncard {g : MulAut (PairN 4) | IsTvElt g} ≤ 105 := by
  exact ncard_isTvElt_le_105

end CFSG.ASVolI.ChH
