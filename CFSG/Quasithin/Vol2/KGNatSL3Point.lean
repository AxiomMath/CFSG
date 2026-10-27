module

public import CFSG.Quasithin.Vol2.KGNatSL3Levi

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)
open CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Core

variable {G G' : Type*} [Group G] [Group G']

theorem derivedSeriesOf_map (φ : G →* G') (X : Subgroup G) (n : ℕ) :
    derivedSeriesOf (X.map φ) n = (derivedSeriesOf X n).map φ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [derivedSeriesOf_succ, derivedSeriesOf_succ, ih, Subgroup.map_commutator]

theorem perfectCore_map (φ : G →* G') (hφ : Function.Injective φ) (X : Subgroup G) :
    perfectCore (X.map φ) = (perfectCore X).map φ := by
  unfold perfectCore
  rw [Subgroup.map_iInf _ hφ]
  exact iInf_congr fun n => derivedSeriesOf_map φ X n

end Core

variable {K : Type} [Field K]

theorem perfectCore_parQ12 [Finite K]
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤) :
    perfectCore (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) K)) =
      parJR K (Fin 1) (Fin 2) := by
  rw [perfectCore_eq_map_perfectResidual, perfectResidual_parQ_eq_parJR hSL,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left parJR_le_parQ]

theorem perfectCore_parQ21 [Finite K]
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤) :
    perfectCore (parQ : Subgroup (Matrix.SpecialLinearGroup (Fin 2 ⊕ Fin 1) K)) =
      parJL K (Fin 2) (Fin 1) := by
  rw [perfectCore_eq_map_perfectResidual, perfectResidual_parQ_eq_parJL hSL,
    Subgroup.subgroupOf_map_subtype, inf_of_le_left parJL_le_parQ]

theorem h12 : (1 : ℕ) + 2 = 3 := rfl

theorem h21 : (2 : ℕ) + 1 = 3 := rfl

theorem reindex12_apply (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) K) (i j : Fin 3) :
    (reindexSL K h12 M : Matrix (Fin 3) (Fin 3) K) i j =
      M.val ((sumEquiv h12).symm i) ((sumEquiv h12).symm j) := by
  rw [reindexSL_val]
  rfl

theorem sumEquiv12_symm : (sumEquiv h12).symm (0 : Fin 3) = Sum.inl 0 ∧
    (sumEquiv h12).symm (1 : Fin 3) = Sum.inr 0 ∧ (sumEquiv h12).symm (2 : Fin 3) = Sum.inr 1 :=
  ⟨rfl, rfl, rfl⟩

theorem mem_parJR12_iff (M : Matrix.SpecialLinearGroup (Fin 1 ⊕ Fin 2) K) :
    M ∈ parJR K (Fin 1) (Fin 2) ↔
      (reindexSL K h12 M : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  obtain ⟨s0, s1, s2⟩ := sumEquiv12_symm
  have hcol : ∀ i : Fin 3, ((reindexSL K h12 M : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) i =
      M.val ((sumEquiv h12).symm i) (Sum.inl 0) := by
    intro i
    rw [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    simp [reindex12_apply, s0]
  rw [mem_parJR, mem_parQ]
  constructor
  · rintro ⟨h21', h11⟩
    funext i
    rw [hcol]
    fin_cases i
    · simpa [s0, Matrix.toBlocks₁₁] using congrFun (congrFun h11 0) 0
    · simpa [s1, Matrix.toBlocks₂₁] using congrFun (congrFun h21' 0) 0
    · simpa [s2, Matrix.toBlocks₂₁] using congrFun (congrFun h21' 1) 0
  · intro hB
    have e0 := congrFun hB 0
    have e1 := congrFun hB 1
    have e2 := congrFun hB 2
    rw [hcol] at e0 e1 e2
    simp only [s0, s1, s2] at e0 e1 e2
    refine ⟨?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j
      · simpa [Matrix.toBlocks₂₁] using e1
      · simpa [Matrix.toBlocks₂₁] using e2
    · ext i j
      fin_cases i
      fin_cases j
      simpa [Matrix.toBlocks₁₁] using e0

theorem mulVec_eq_of_fix_e0 {B : Matrix (Fin 3) (Fin 3) K} (hB : B *ᵥ ![1, 0, 0] = ![1, 0, 0])
    {v : Fin 3 → K} (hv : v ∈ flagSpace 3 K 1) : B *ᵥ v = v := by
  rw [← stdLine_eq_flagSpace] at hv
  have hv' : v = v 0 • ![1, 0, 0] := vec3_eq (by simp) (by simp [hv.1]) (by simp [hv.2])
  rw [hv', Matrix.mulVec_smul, hB]

section Point

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem eq_U1_of_isFlagW [Finite K] (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U) :
    U = hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
  rw [(eq_std_of_stable hS).1 (by rw [hc, pow_one]), stdLine_eq_flagSpace]

theorem eq_U2_of_isFlagW [Finite K] (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) 2 U) :
    U = hf.pre (gmap g (flagSpace 3 K 2)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
  rw [(eq_std_of_stable hS).2.1 hc, stdPlane_eq_flagSpace]

theorem mem_perfectCore_HU1_iff [Finite K]
    (hSL : commutator (Matrix.SpecialLinearGroup (Fin 2) K) = ⊤)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) (g : Matrix.SpecialLinearGroup (Fin 3) K)
    (x : MulAut W) :
    x ∈ perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmap g (flagSpace 3 K 1)).toAddSubgroup)) ↔
      ∃ B : Matrix.SpecialLinearGroup (Fin 3) K,
        (B : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0] = ![1, 0, 0] ∧
          x = ((rho3 π (g * B * g⁻¹) : ↥H) : MulAut W) := by
  rw [← map_parQ_psiPar hf g h12, perfectCore_map _ (psiPar_injective hf g h12),
    perfectCore_parQ12 hSL]
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨reindexSL K h12 M, (mem_parJR12_iff M).mp hM, psiPar_apply π g h12 M⟩
  · rintro ⟨B, hB, rfl⟩
    refine ⟨(reindexSL K h12).symm B, (mem_parJR12_iff _).mpr ?_, ?_⟩
    · rwa [MulEquiv.apply_symm_apply]
    · rw [psiPar_apply, MulEquiv.apply_symm_apply]

end Point

end CFSG.Quasithin.Vol2.KGNat
