module

public import CFSG.RankThree.PartOne.K159G.PlaneGen
public import CFSG.RankThree.PartOne.S15K.U5Model

public section

namespace CFSG.RankThree.PartOne.K159G

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.KCPrimary Polynomial Matrix
  CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KCUnitaryBlock

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem idSU_le_unitarySU {w : GL (Fin 5) K} (hw : w ∈ idSU h) : w ∈ unitarySU 2 f K 5 := by
  rw [mem_unitarySU_iff h]
  obtain ⟨hu, hdet⟩ := (mem_gramSU_iff_unitary h).1 hw
  refine ⟨hdet, ?_⟩
  have := mem_primeFormUnitary.1 hu
  simpa [idGram] using this

@[expose] noncomputable def eigIdx (d : Fin 5 → Kˣ) (μ : K) : Finset (Fin 5) := by
  classical
  exact Finset.univ.filter fun i => (d i : K) = μ

theorem mem_eigIdx {d : Fin 5 → Kˣ} {μ : K} {i : Fin 5} : i ∈ eigIdx d μ ↔ (d i : K) = μ := by
  classical
  simp [eigIdx]

theorem blockSU_le_planeGen (hq : 4 ≤ 2 ^ f) {d : Fin 5 → Kˣ} {g : ↥(idU h)}
    (hg : (g : GL (Fin 5) K) = diagU d) (a : BlockIdx (toLinU h 5 g)) {μ : K}
    (hax : (a.1 : K[X]) = X - C μ) (hμ : h.bar μ * μ = 1) :
    ∀ w ∈ blockSU h g a, (w : GL (Fin 5) K) ∈ planeGen h (eigIdx d μ) := by
  classical
  intro w hw
  refine mem_planeGen_of_fixOut hq _ (eigIdx d μ) rfl _ (idSU_le_unitarySU h w.2) ?_
  intro i hi
  have hdi : (d i : K) ≠ μ := fun h' => hi (mem_eigIdx.2 h')
  have hw' : idPhi h w ∈ specialBlock (idForm h 5) (toLinU h 5 g) (a.1 : K[X]) := hw
  have hof := specialBlock_le_orbitFactor hw'
  set x : Module.End K (Fin 5 → K) :=
    ((toLinU h 5 g : LinearMap.GeneralLinearGroup K (Fin 5 → K)) : Module.End K (Fin 5 → K)) with hx
  have hxe : x (Pi.single i 1) = (d i : K) • Pi.single i 1 := by
    rw [hx, toLinU_apply_eq, hg, diagU_val]
    ext r
    simp only [Matrix.mulVec_diagonal, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hr : r = i
    · subst hr
      simp
    · simp [hr]
  have hb : (X - C (d i : K) : K[X]) ∈ primaryFactors x := by
    rw [mem_primaryFactors]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [Polynomial.dvd_iff_isRoot]
    refine Module.End.hasEigenvalue_iff_isRoot.1 (Module.End.hasEigenvalue_of_hasEigenvector
      (x := Pi.single i 1) ?_)
    refine Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hxe, ?_⟩
    intro h0
    have := congrFun h0 i
    simp at this
  have hbS : (X - C (d i : K) : K[X]) ∉ ({(a.1 : K[X]), dualPoly h.bar (a.1 : K[X])} : Set K[X]) := by
    intro hmem
    have hne : (X - C (d i : K) : K[X]) ≠ X - C μ := fun h' =>
      hdi (by simpa using congrArg (fun q : K[X] => -q.coeff 0) h')
    rcases hmem with h1 | h1
    · exact hne (h1.trans hax)
    · rw [hax, dualPoly_X_sub_C_eq h hμ] at h1
      exact hne h1
  have hfix := hof.2 _ hb hbS (Pi.single i 1) (mem_primaryComponent_X_sub_C.2 hxe)
  rw [idPhi, MonoidHom.comp_apply, toLinU_apply_eq] at hfix
  exact hfix

end CFSG.RankThree.PartOne.K159G
