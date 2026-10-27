module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningThree
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningThreeOne
public import CFSG.RankThree.PartOne.KC.UnitaryNonregularA
public import CFSG.RankThree.PartOne.KC.UnitaryNonregularB

public section

namespace CFSG.RankThree.PartOne.KCUnitaryDefining

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.GroupTheory

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem trvN_two (η : K) :
    KCUnitaryTrv.trvN K 2 η = !![0, 0, 0, η; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [KCUnitaryTrv.trvN, Fin.ext_iff]

theorem npc_four_sq_zero (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN2 : N * N = 0) (hN0 : N ≠ 0) :
    NormalPrimeComplementsTrivial p (MulAut.conj (unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 4) (Fin 4) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := Matrix.mulVecLin N
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
  have hpe : ∀ z ∈ W, B e z = 0 ∧ B g z = 0 := fun z hz =>
    ⟨(Submodule.mem_orthogonalBilin.mp hz) e (Submodule.subset_span (by simp)),
      (Submodule.mem_orthogonalBilin.mp hz) g (Submodule.subset_span (by simp))⟩
  have hge : B g e = 1 := by rw [hsymm e g, heg, map_one]
  have hNe' : N *ᵥ e = 0 := hNe
  have hNg' : N *ᵥ g = η • e := hNg
  rcases hcases with hT | ⟨-, e', he'W, g', hg'W, hee', hgg', heg', hNe'', hNg''⟩
  ·
    have hWd : Module.finrank K W = 2 := by rw [hWdim, Module.finrank_fin_fun]
    obtain ⟨E, hE⟩ := h.exists_orthonormal_basis (hB.domRestrict W) hWsep
    have hp0 : 0 < Module.finrank K W := by omega
    have hp1 : 1 < Module.finrank K W := by omega
    obtain ⟨z₀, z₁, hz₀W, hz₁W, hn00, hn01, hn10, hn11⟩ : ∃ z₀ z₁ : Fin 4 → K, z₀ ∈ W ∧ z₁ ∈ W ∧
        B z₀ z₀ = 1 ∧ B z₀ z₁ = 0 ∧ B z₁ z₀ = 0 ∧ B z₁ z₁ = 1 := by
      refine ⟨(E ⟨0, hp0⟩ : Fin 4 → K), (E ⟨1, hp1⟩ : Fin 4 → K), (E ⟨0, hp0⟩).2,
        (E ⟨1, hp1⟩).2, ?_, ?_, ?_, ?_⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨0, hp0⟩ ⟨0, hp0⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨0, hp0⟩ ⟨1, hp1⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨1, hp1⟩ ⟨0, hp0⟩
      · simpa [LinearMap.domRestrict₁₂_apply] using hE ⟨1, hp1⟩ ⟨1, hp1⟩
    obtain ⟨hez₀, hgz₀⟩ := hpe z₀ hz₀W
    obtain ⟨hez₁, hgz₁⟩ := hpe z₁ hz₁W
    have hz₀e : B z₀ e = 0 := by rw [hsymm e z₀, hez₀, map_zero]
    have hz₁e : B z₁ e = 0 := by rw [hsymm e z₁, hez₁, map_zero]
    have hz₀g : B z₀ g = 0 := by rw [hsymm g z₀, hgz₀, map_zero]
    have hz₁g : B z₁ g = 0 := by rw [hsymm g z₁, hgz₁, map_zero]
    have hNz₀ : N *ᵥ z₀ = 0 := hT z₀ hz₀W
    have hNz₁ : N *ᵥ z₁ = 0 := hT z₁ hz₁W
    refine normalPrimeComplementsTrivial_of_family h (by norm_num) (by omega) hN hskew
      (C' := KCUnitaryTrv.trvGL K 2) (N' := KCUnitaryTrv.trvN K 2 η) (trvElt 2 h η hη) ?_
      ![e, z₀, z₁, g] ?_ ?_ ?_
    · have h1 := truncExp_of_mul_self_eq_zero (n := 2 + 2) (K := K) (by norm_num)
        (trvN_mul_self (K := K) 2 η)
      rw [coe_trvElt]
      exact h1.symm
    · intro i j
      simp only [← hBdef]
      fin_cases i <;> fin_cases j <;>
        simp [KCUnitaryTrv.trvGram_two, hee, heg, hgg, hez₀, hez₁, hgz₀, hgz₁, hz₀e, hz₁e, hz₀g,
          hz₁g, hge, hn00, hn01, hn10, hn11]
    · intro j
      fin_cases j <;> simp [trvN_two, Fin.sum_univ_four, hNe', hNz₀, hNz₁, hNg']
    · exact fun B hB S hSC hSn hSp =>
        unitary_transvection_centralizer_normal_prime_complements_trivial h hp3 (by norm_num) hη
          hη0 B hB S hSC hSn hSp
  ·
    obtain ⟨hee'e, hge'⟩ := hpe e' he'W
    obtain ⟨heg'e, hgg'e⟩ := hpe g' hg'W
    have he'e : B e' e = 0 := by rw [hsymm e e', hee'e, map_zero]
    have he'g : B e' g = 0 := by rw [hsymm g e', hge', map_zero]
    have hg'e : B g' e = 0 := by rw [hsymm e g', heg'e, map_zero]
    have hg'g : B g' g = 0 := by rw [hsymm g g', hgg'e, map_zero]
    have hg'e' : B g' e' = 1 := by rw [hsymm e' g', heg', map_one]
    have hNe2 : N *ᵥ e' = 0 := hNe''
    have hNg2 : N *ᵥ g' = η • e' := hNg''
    refine normalPrimeComplementsTrivial_of_family h (by norm_num) (by omega) hN hskew
      (C' := KCUnitaryNr.nrGLA K) (N' := nrNilA η) (nrEltA h hp3 hη) rfl
      ![e, e', g, g'] ?_ ?_ ?_
    · intro i j
      simp only [← hBdef]
      fin_cases i <;> fin_cases j <;>
        simp [nrGramA, hee, heg, hgg, hee'e, hge', heg'e, hgg'e, hee', hgg',
          heg', hge, he'e, he'g, hg'e, hg'g, hg'e']
    · intro j
      fin_cases j <;> simp [nrNilA, Fin.sum_univ_four, hNe', hNg', hNe2, hNg2]
    · exact KCUnitaryNr.nrA_normalPrimeComplementsTrivial h hp3 hη hη0

theorem npc_four_three_one (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN3 : N * N * N = 0)
    (hN2 : N * N ≠ 0) :
    NormalPrimeComplementsTrivial p (MulAut.conj (unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) := by
  have hs : (N.map h.bar)ᵀ = -N := by
    rw [← unitaryAdjoint_one h N]
    exact hskew
  set B := gramForm h (1 : Matrix (Fin 4) (Fin 4) K) with hBdef
  have hB : B.IsSymm := gramForm_one_isSymm h
  have hBl : B.SeparatingLeft := gramForm_one_separatingLeft h
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  let Nl : (Fin 4 → K) →ₗ[K] (Fin 4 → K) := Matrix.mulVecLin N
  have hNl : ∀ x y, B (Nl x) y = -B x (Nl y) := fun x y => gramForm_one_mulVec_skew h hs x y
  have hNl3 : ∀ x, Nl (Nl (Nl x)) = 0 := fun x => by
    show N *ᵥ (N *ᵥ (N *ᵥ x)) = 0
    rw [mulVec_mulVec, mulVec_mulVec, hN3, zero_mulVec]
  have hNl2 : ∃ x, Nl (Nl x) ≠ 0 := by
    by_contra hcon
    have hcon' : ∀ x, Nl (Nl x) = 0 := fun x => by
      by_contra hne
      exact hcon ⟨x, hne⟩
    apply hN2
    ext i j
    have h1 : (N * N) *ᵥ (Pi.single j 1 : Fin 4 → K) = 0 := by
      rw [← mulVec_mulVec]
      exact hcon' _
    have := congrFun h1 i
    simpa [mulVec_single_one] using this
  obtain ⟨b₀, b₁, b₂, b₃, g00, g01, g02, g03, g11, g12, g13, g22, g23, g33, hNb0, hNb1, hNb2,
    hNb3⟩ := KCUnitaryHerm.exists_three_one_family hp3 hB hBl (Module.finrank_fin_fun K) hNl hNl3
      hNl2
  have g10 : B b₁ b₀ = 0 := by rw [hsymm b₀ b₁, g01, map_zero]
  have g20 : B b₂ b₀ = 1 := by rw [hsymm b₀ b₂, g02, map_one]
  have g21 : B b₂ b₁ = 0 := by rw [hsymm b₁ b₂, g12, map_zero]
  have g30 : B b₃ b₀ = 0 := by rw [hsymm b₀ b₃, g03, map_zero]
  have g31 : B b₃ b₁ = 0 := by rw [hsymm b₁ b₃, g13, map_zero]
  have g32 : B b₃ b₂ = 0 := by rw [hsymm b₂ b₃, g23, map_zero]
  have hNb0' : N *ᵥ b₀ = 0 := hNb0
  have hNb1' : N *ᵥ b₁ = b₀ := hNb1
  have hNb2' : N *ᵥ b₂ = b₁ := hNb2
  have hNb3' : N *ᵥ b₃ = 0 := hNb3
  refine normalPrimeComplementsTrivial_of_family h (by norm_num) (by omega) hN hskew
    (C' := KCUnitaryNr.nrGLB K) (N' := nrNilB K) (nrEltB h hp3) rfl ![b₀, b₁, b₂, b₃] ?_ ?_ ?_
  · intro i j
    simp only [← hBdef]
    fin_cases i <;> fin_cases j <;>
      simp [nrGramB, g00, g01, g02, g03, g11, g12, g13, g22, g23, g33, g10, g20,
        g21, g30, g31, g32]
  · intro j
    fin_cases j <;> simp [nrNilB, Fin.sum_univ_four, hNb0', hNb1', hNb2', hNb3']
  · exact KCUnitaryNr.nrB_normalPrimeComplementsTrivial h hp3

theorem npc_four (hp3 : 3 < p) {N : Matrix (Fin 4) (Fin 4) K} (hN : N ^ 4 = 0)
    (hskew : unitaryAdjoint h (1 : GL (Fin 4) K) N = -N) (hN0 : N ≠ 0) :
    NormalPrimeComplementsTrivial p (MulAut.conj (unitaryExp h (by norm_num) (by omega) hN hskew :
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))) := by
  have e2 : N ^ 2 = N * N := pow_two N
  have e3 : N ^ 3 = N * N * N := by rw [pow_succ, pow_two]
  by_cases h3 : N ^ 3 = 0
  · by_cases h2 : N ^ 2 = 0
    · exact npc_four_sq_zero h hp3 hN hskew (by rw [← e2]; exact h2) hN0
    · exact npc_four_three_one h hp3 hN hskew (by rw [← e3]; exact h3) (by rw [← e2]; exact h2)
  · exact fun B hB S hSC hSn hSp =>
      unitary_regular_unipotent_centralizer_normal_prime_complements_trivial h hp3 (by norm_num)
        (by omega) isPrimeFormGram_one hskew hN h3 B hB S hSC hSn hSp

end CFSG.RankThree.PartOne.KCUnitaryDefining
