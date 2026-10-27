module

public import CFSG.LocalAnalysis.StandardType.GGKG3Defs
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dCheck
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dWeyl
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dProj
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Sylow

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open CFSG.StandardType.GGKG3.K3dCheck
open CFSG.StandardType.GGKG3.K3dWeyl
open CFSG.StandardType.GGKG3.K3dProj

private theorem kg3_weylMat6_w3 :
    ∀ i j : Fin 6, weylMat6 w3 i j = kMw i j := by
  intro i j
  have h2 : weylMatrix w3 = CFSG.RankThree.Lattice.wordMat Tag.E6
      CFSG.LieType.SeitzGeneration.e6ThreeWord :=
    CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylMatrix_wordProd' Tag.E6
      CFSG.LieType.SeitzGeneration.e6ThreeWord
  rw [weylMat6_apply, h2, CFSG.LieType.SeitzGeneration.e6Three_wordMat]
  rfl

private theorem kg3_mv_kMw :
    ∀ x : Fin 6 → ℤ, mv kMw x = (weylMat6 w3).mulVec x := by
  intro x
  funext i
  rw [mv, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_six]
  simp only [kg3_weylMat6_w3]

private theorem kg3_e6RootVec_mem (m : Fin 72) : (e6RootVec m : Fin 6 → ℤ) ∈ k3Roots := by
  change e6RootVec m ∈ (List.range 72).map e6Certificate.root
  exact List.mem_map.mpr ⟨m, List.mem_range.mpr m.2, rfl⟩

private theorem kg3_mem_k3Roots {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) : (γ : Fin 6 → ℤ) ∈ k3Roots := by
  rw [isRoot_iff_exists_e6RootVec] at hγ
  obtain ⟨m, hm⟩ := hγ
  rw [← hm]
  exact kg3_e6RootVec_mem m

private theorem kg3_moved_root (c : WeylGroup .E6)
    (htr : (weylMatrix c).trace = 2) :
    ∃ γ : Fin 6 → ℤ, γ ∈ k3Roots ∧
      (weylMat6 c).mulVec γ ∈ k3Roots ∧ (weylMat6 c).mulVec γ ≠ γ := by
  have hne : weylMat6 c ≠ 1 := by
    intro h
    have htr1 : (weylMat6 c).trace = 6 := by
      rw [h, Matrix.trace_one]
      norm_num
    rw [weylMat6_trace, htr] at htr1
    norm_num at htr1
  have hex : ∃ j : Fin 6, (weylMat6 c).mulVec (Pi.single j 1) ≠ Pi.single j 1 := by
    by_contra h
    push Not at h
    apply hne
    ext i j
    have hj := congrFun (h j) i
    rw [Matrix.mulVec_single_one, Pi.single_apply] at hj
    rw [Matrix.one_apply]
    exact hj
  obtain ⟨j, hj⟩ := hex
  refine ⟨Pi.single j 1, ?_, ?_, hj⟩
  · exact kg3_mem_k3Roots (IsRoot.basis (e6Index j))
  · have hroot : IsRoot Tag.E6 ((weylMat6 c).mulVec (Pi.single j 1) : Fin Tag.E6.rank → ℤ) := by
      have hsm : (weylMat6 c).mulVec ((Pi.single j 1) : Fin Tag.E6.rank → ℤ) =
          c • ((Pi.single j 1) : Fin Tag.E6.rank → ℤ) :=
        weylMat6_mulVec c _
      exact hsm.symm ▸ IsRoot.smul (IsRoot.basis (e6Index j)) c
    exact kg3_mem_k3Roots hroot

private theorem kg3_bad (γ δ : Fin 6 → ℤ)
    (D : ℤ) (N : Fin 6 → Fin 6 → ℤ) (M : Matrix (Fin 6) (Fin 6) ℤ)
    (hkn : kN γ δ = (D, N)) (hDne : D ≠ 0)
    (hM : ∀ i j, D * M i j = N i j)
    (hAdj : ∀ i j, 3 ∣ ((M - 1) * Matrix.of kAdjC) i j) :
    k3dBad γ δ = true := by
  let S : Fin 6 → Fin 6 → ℤ := fun i j =>
      (N i 0 - (if i = 0 then D else 0)) * kAdjC 0 j +
      (N i 1 - (if i = 1 then D else 0)) * kAdjC 1 j +
      (N i 2 - (if i = 2 then D else 0)) * kAdjC 2 j +
      (N i 3 - (if i = 3 then D else 0)) * kAdjC 3 j +
      (N i 4 - (if i = 4 then D else 0)) * kAdjC 4 j +
      (N i 5 - (if i = 5 then D else 0)) * kAdjC 5 j
  have hterm : ∀ (i j : Fin 6) (k : Fin 6),
      D * ((M - 1) i k * kAdjC k j) = (N i k - if i = k then D else 0) * kAdjC k j := by
    intro i j k
    rw [Matrix.sub_apply, Matrix.one_apply]
    calc D * ((M i k - (if i = k then 1 else 0)) * kAdjC k j)
        = (D * M i k - D * (if i = k then 1 else 0)) * kAdjC k j := by ring
      _ = (N i k - (if i = k then D else 0)) * kAdjC k j := by
            rw [hM i k]
            rw [show D * (if i = k then (1:ℤ) else 0) = (if i = k then D else 0) by
              split_ifs <;> simp]
  have hS : ∀ i j : Fin 6, S i j = D * ((M - 1) * Matrix.of kAdjC) i j := by
    intro i j
    change ((N i 0 - (if i = 0 then D else 0)) * kAdjC 0 j +
      (N i 1 - (if i = 1 then D else 0)) * kAdjC 1 j +
      (N i 2 - (if i = 2 then D else 0)) * kAdjC 2 j +
      (N i 3 - (if i = 3 then D else 0)) * kAdjC 3 j +
      (N i 4 - (if i = 4 then D else 0)) * kAdjC 4 j +
      (N i 5 - (if i = 5 then D else 0)) * kAdjC 5 j) = _
    rw [Matrix.mul_apply, Finset.mul_sum, Fin.sum_univ_six]
    rw [← hterm i j 0, ← hterm i j 1, ← hterm i j 2, ← hterm i j 3, ← hterm i j 4,
      ← hterm i j 5]
    rfl
  have hmod : ∀ i j : Fin 6, 3 * D ∣ S i j := by
    intro i j
    rw [hS i j, mul_comm 3 D]
    exact mul_dvd_mul_left D (hAdj i j)
  have hdiv : ∀ i j : Fin 6, D ∣ N i j := by
    intro i j
    exact ⟨M i j, (hM i j).symm⟩
  unfold k3dBad
  rw [hkn]
  simp only [Prod.fst, Prod.snd]
  have h1 : decide (D ≠ 0) = true := decide_eq_true_eq.mpr hDne
  have h2 : (List.finRange 6).all (fun i => (List.finRange 6).all
      (fun j => decide (D ∣ N i j))) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    exact decide_eq_true_eq.mpr (hdiv i j)
  have h3 : (List.finRange 6).all (fun i => (List.finRange 6).all
      (fun j => decide (3 * D ∣ S i j))) = true := by
    rw [List.all_eq_true]
    intro i _
    rw [List.all_eq_true]
    intro j _
    exact decide_eq_true_eq.mpr (hmod i j)
  change (decide (D ≠ 0) && (List.finRange 6).all (fun i => (List.finRange 6).all
      (fun j => decide (D ∣ N i j))) && (List.finRange 6).all (fun i => (List.finRange 6).all
      (fun j => decide (3 * D ∣ S i j)))) = true
  rw [h1, h2, h3]
  rfl

theorem k3d :
    ¬ ∃ c : WeylGroup .E6, c * w3 = w3 * c ∧ c * c = 1 ∧ (weylMatrix c).trace = 2 := by
  rintro ⟨c, hcw, hc2, htr⟩
  have hM2 : weylMat6 c * weylMat6 c = 1 := by
    rw [← weylMat6_mul, hc2, weylMat6_one]
  have hMW : weylMat6 c * weylMat6 w3 = weylMat6 w3 * weylMat6 c := by
    rw [← weylMat6_mul, ← weylMat6_mul, hcw]
  have horth : (weylMat6 c).transpose * Matrix.of kC * weylMat6 c = Matrix.of kC :=
    k3_weylMat6_orth c
  have hMC : (weylMat6 c).transpose * Matrix.of kC = Matrix.of kC * weylMat6 c := by
    calc (weylMat6 c).transpose * Matrix.of kC
        = (weylMat6 c).transpose * Matrix.of kC * (weylMat6 c * weylMat6 c) := by
            rw [hM2, mul_one]
      _ = ((weylMat6 c).transpose * Matrix.of kC * weylMat6 c) * weylMat6 c :=
            (mul_assoc _ _ _).symm
      _ = Matrix.of kC * weylMat6 c := by rw [horth]
  have htr2 : (weylMat6 c).trace = 2 := by
    rw [weylMat6_trace]; exact htr
  obtain ⟨γ, hγmem, hδmem, hne⟩ := kg3_moved_root c htr
  let δ : Fin 6 → ℤ := (weylMat6 c).mulVec γ
  let u : Fin 6 → ℤ := γ - δ
  let v : Fin 6 → ℤ := mv kMw u
  have hγδ : γ ≠ δ := fun h => hne h.symm
  have hMγ : (weylMat6 c).mulVec γ = δ := rfl
  have hMδ : (weylMat6 c).mulVec δ = γ := by
    show (weylMat6 c).mulVec ((weylMat6 c).mulVec γ) = γ
    rw [Matrix.mulVec_mulVec, hM2, Matrix.one_mulVec]
  have hu : (weylMat6 c).mulVec u = -u := by
    ext i
    simp only [u, Matrix.mulVec_sub]
    rw [hMγ, hMδ]
    simp
  have hv : (weylMat6 c).mulVec v = -v := by
    have hvW : v = (weylMat6 w3).mulVec u := kg3_mv_kMw u
    calc (weylMat6 c).mulVec v
        = (weylMat6 c).mulVec ((weylMat6 w3).mulVec u) := by rw [hvW]
      _ = ((weylMat6 c) * (weylMat6 w3)).mulVec u := Matrix.mulVec_mulVec u _ _
      _ = ((weylMat6 w3) * (weylMat6 c)).mulVec u := by rw [hMW]
      _ = (weylMat6 w3).mulVec ((weylMat6 c).mulVec u) := (Matrix.mulVec_mulVec u _ _).symm
      _ = (weylMat6 w3).mulVec (-u) := by rw [hu]
      _ = -((weylMat6 w3).mulVec u) := Matrix.mulVec_neg u _
      _ = -v := by rw [← hvW]
  have hD : (kNuv u v).1 ≠ 0 := by
    have hkn : kN γ δ = kNuv u v := kN_eq_kNuv γ δ
    rw [← hkn]
    exact kN_fst_ne_zero hγmem hδmem hγδ
  have hproj := k3_proj_formula (weylMat6 c) hM2 hMC htr2 u v hu hv hD
  have hkn2 : kN γ δ = ((kNuv u v).1, (kNuv u v).2) := kN_eq_kNuv γ δ
  have hbad := kg3_bad γ δ (kNuv u v).1 (kNuv u v).2 (weylMat6 c)
      hkn2 hD (fun i j => hproj i j) (k3_weylMat6_sub_one_adj c)
  have hfalse := k3dBad_eq_false hγmem hδmem hγδ
  rw [hbad] at hfalse
  nomatch hfalse

end CFSG.StandardType.GGKG3
