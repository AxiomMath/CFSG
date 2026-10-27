module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningBridge
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningSqZero
public import CFSG.RankThree.PartOne.KC.UnitaryTransvection
public import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotent

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem isPrimeFormGram_one {n : ℕ} : IsPrimeFormGram (1 : GL (Fin n) K) := by
  refine ⟨by simp, fun i j => ?_⟩
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem trvN_mul_self (m : ℕ) (η : K) :
    KCUnitaryTrv.trvN K m η * KCUnitaryTrv.trvN K m η = 0 := by
  have hne : (Fin.last (m + 1) : Fin (m + 2)) ≠ 0 := (KCUnitaryTrv.zero_ne_last (m := m)).symm
  rw [KCUnitaryTrv.trvN, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.single_mul_single_of_ne (1 : K) 0 (Fin.last (m + 1)) 0 hne (1 : K), smul_zero,
    smul_zero]

theorem trvN_one (η : K) :
    KCUnitaryTrv.trvN K 1 η = !![0, 0, η; 0, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KCUnitaryTrv.trvN, Fin.ext_iff]

theorem npc_three_sq_zero (hp3 : 3 < p) {N : Matrix (Fin 3) (Fin 3) K} (hN : N ^ 3 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 3) K) N = -N) (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    NormalPrimeComplementsTrivial p (MulAut.conj (unitaryExp h (le_refl 3) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 3) (Fin 3) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := Matrix.mulVecLin N
  have hNl : ∀ x y, B (Nl x) y = -B x (Nl y) := fun x y => gramForm_one_mulVec_skew h hs x y
  have hNl2 : ∀ x, Nl (Nl x) = 0 := fun x => by
    show N *ᵥ (N *ᵥ x) = 0
    rw [mulVec_mulVec, hN2, zero_mulVec]
  have hNl0 : Nl ≠ 0 := by
    intro h0
    apply hN0
    ext i j
    have := congrFun (LinearMap.congr_fun h0 (Pi.single j 1)) i
    simpa [Nl, mulVec_single_one] using this
  obtain ⟨η, hη, hη0⟩ := KCUnitaryHerm.exists_traceZero h
  obtain ⟨e, g, hee, hgg, heg, hNe, hNg, hWdim, hWsep, hcases⟩ :=
    KCUnitaryHerm.exists_sq_zero_structure hp3 hB hBl hNl hNl2 hNl0 hη hη0
  set W := (Submodule.span K {e, g}).orthogonalBilin B with hW
  have hWd : Module.finrank K W = 1 := by rw [hWdim, Module.finrank_fin_fun]
  have hT : ∀ z ∈ W, Nl z = 0 := by
    rcases hcases with hT | ⟨hfin2, -⟩
    · exact hT
    · omega
  obtain ⟨E, hE⟩ := h.exists_orthonormal_basis (hB.domRestrict W) hWsep
  have hp0 : 0 < Module.finrank K W := by omega
  obtain ⟨z, hzW, hzz⟩ : ∃ z : Fin 3 → K, z ∈ W ∧ B z z = 1 := by
    refine ⟨(E ⟨0, hp0⟩ : Fin 3 → K), (E ⟨0, hp0⟩).2, ?_⟩
    have := hE ⟨0, hp0⟩ ⟨0, hp0⟩
    simpa [LinearMap.domRestrict₁₂_apply] using this
  have hez : B e z = 0 :=
    (Submodule.mem_orthogonalBilin.mp hzW) e (Submodule.subset_span (by simp))
  have hgz : B g z = 0 :=
    (Submodule.mem_orthogonalBilin.mp hzW) g (Submodule.subset_span (by simp))
  have hze : B z e = 0 := by rw [hsymm e z, hez, map_zero]
  have hzg : B z g = 0 := by rw [hsymm g z, hgz, map_zero]
  have hge : B g e = 1 := by rw [hsymm e g, heg, map_one]
  have hNz : N *ᵥ z = 0 := hT z hzW
  have hNe' : N *ᵥ e = 0 := hNe
  have hNg' : N *ᵥ g = η • e := hNg
  refine normalPrimeComplementsTrivial_of_family h (le_refl 3) (by omega) hN hskew
    (C' := KCUnitaryTrv.trvGL K 1) (N' := KCUnitaryTrv.trvN K 1 η) (trvElt 1 h η hη) ?_
    ![e, z, g] ?_ ?_ ?_
  · have h1 := truncExp_of_mul_self_eq_zero (n := 1 + 2) (K := K) (by norm_num)
      (trvN_mul_self (K := K) 1 η)
    rw [coe_trvElt]
    exact h1.symm
  · intro i j
    simp only [← hBdef]
    fin_cases i <;> fin_cases j <;>
      simp [KCUnitaryTrv.trvGram_one, hee, heg, hgg, hez, hgz, hze, hzg, hge, hzz]
  · intro j
    fin_cases j <;> simp [trvN_one, Fin.sum_univ_three, hNe', hNz, hNg']
  · exact fun B hB S hSC hSn hSp =>
      unitary_transvection_centralizer_normal_prime_complements_trivial h hp3 (by norm_num) hη hη0
        B hB S hSC hSn hSp

theorem npc_three (hp3 : 3 < p) {N : Matrix (Fin 3) (Fin 3) K} (hN : N ^ 3 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 3) K) N = -N) (hN0 : N ≠ 0) :
    NormalPrimeComplementsTrivial p (MulAut.conj (unitaryExp h (le_refl 3) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))) := by
  by_cases h2 : N ^ 2 = 0
  · exact npc_three_sq_zero h hp3 hN hskew (by rw [← pow_two]; exact h2) hN0
  · exact fun B hB S hSC hSn hSp =>
      unitary_regular_unipotent_centralizer_normal_prime_complements_trivial h hp3 (le_refl 3)
        (by omega) isPrimeFormGram_one hskew hN h2 B hB S hSC hSn hSp

end CFSG.RankThree.PartOne.KCUnitaryDefining
