module

public import CFSG.Quasithin.Vol2.Ch11SecAKA6
public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4J

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ blkQ_apply blkIdx sigma2 spLevi spMat
  spMat_leviSp_one spLevi_mem_perfectCore spMat_inr_inl_of_mem_Q2_one)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer flag)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq mem_N0_of_entry_eq_one fix_gammaW_one
  mem_pCoreOf_N_iff)

namespace KA

variable {K : Type} [Field K]

theorem spLevi1_mulVec_plane (A : Matrix.SpecialLinearGroup (Fin 2) K)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ spPlane K) :
    mat 2 K (spLevi 1 A) *ᵥ v = vec4
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0 * v (.inl 0) + (A : Matrix (Fin 2) (Fin 2) K) 0 1 *
        v (.inl 1))
      ((A : Matrix (Fin 2) (Fin 2) K) 1 0 * v (.inl 0) + (A : Matrix (Fin 2) (Fin 2) K) 1 1 *
        v (.inl 1)) 0 0 := by
  obtain ⟨h2, h3⟩ := hv
  rw [show mat 2 K (spLevi 1 A) = spMat (spLevi 1 A) from rfl, spMat_leviSp_one]
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, h2, h3, vec4]

variable [Finite K] [CharP K 2]

theorem mem_N0_of_fix (hK4 : ∃ s : Finset K, s.card = 4) {M : StatedSp 2 K}
    (hM : mat 2 K M *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0) : M ∈ perfectCore (Q2 K 0) := by
  have hMQ : M ∈ Q2 K 0 := by
    show M ∈ stabilizer 2 K (flag 2 K 1)
    rw [flag_one_eq]
    refine mem_stabilizer_iff'.mpr fun y => ?_
    have hline : ∀ y : Fin 2 ⊕ Fin 2 → K, y ∈ spLine K → y = y (.inl 0) • vec4 1 0 0 0 :=
      fun y hy => vec4_eq (by simp [vec4]) (by simp [vec4, hy.1]) (by simp [vec4, hy.2.1])
        (by simp [vec4, hy.2.2])
    constructor
    · intro hy
      rw [hline y hy, Matrix.mulVec_smul, hM]
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
    · intro hy
      have h1 : mat 2 K M *ᵥ y = mat 2 K M *ᵥ ((mat 2 K M *ᵥ y) (.inl 0) • vec4 1 0 0 0) := by
        rw [Matrix.mulVec_smul, hM]
        exact hline _ hy
      have h2 := congrArg (fun v => mat 2 K M⁻¹ *ᵥ v) h1
      simp only [mat_inv_mulVec] at h2
      rw [h2]
      exact (spLine K).smul_mem _ vec4_e0_mem_spLine
  refine mem_N0_of_entry_eq_one hK4 hMQ ?_
  rw [spMat_eq_mulVec, single_inl0, hM]
  rfl

theorem pCore1_mulVec (hK4 : ∃ s : Finset K, s.card = 4) {N : StatedSp 2 K}
    (hN : N ∈ pCoreOf 2 (perfectCore (Q2 K 1))) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ spPlane K) :
    mat 2 K N *ᵥ v = v := by
  have hNc : N ∈ perfectCore (Q2 K 1) := Subgroup.map_subtype_le _ hN
  have hNQ : N ∈ Q2 K 1 := perfectCore_le _ hNc
  have hB := (mem_pCoreOf_N_iff hK4 1 hNc).mp hN
  have hblk : ∀ i k : Fin 2, spMat N (sigma2 1 i) (sigma2 1 k) =
      (1 : Matrix (Fin 2) (Fin 2) K) i k := fun i k => by
    have := congrFun₂ hB i k
    rwa [blkQ_apply] at this
  have e00 : spMat N (.inl 0) (.inl 0) = 1 := by simpa [sigma2] using hblk 0 0
  have e01 : spMat N (.inl 0) (.inl 1) = 0 := by simpa [sigma2] using hblk 0 1
  have e10 : spMat N (.inl 1) (.inl 0) = 0 := by simpa [sigma2] using hblk 1 0
  have e11 : spMat N (.inl 1) (.inl 1) = 1 := by simpa [sigma2] using hblk 1 1
  have l00 := spMat_inr_inl_of_mem_Q2_one hNQ 0 0
  have l01 := spMat_inr_inl_of_mem_Q2_one hNQ 0 1
  have l10 := spMat_inr_inl_of_mem_Q2_one hNQ 1 0
  have l11 := spMat_inr_inl_of_mem_Q2_one hNQ 1 1
  obtain ⟨h2, h3⟩ := hv
  simp only [spMat] at e00 e01 e10 e11 l00 l01 l10 l11
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mat_apply, h2, h3,
      e00, e01, e10, e11, l00, l01, l10, l11]

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem fix_of_mulVec_eq [Finite W] (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    {M : StatedSp 2 K} {w : W} (hM : mat 2 K M *ᵥ f w = f w) :
    ((π M : ↥H) : MulAut W) w = w := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  by_cases hw : f w = 0
  · exact hZ _ (π M).2 w ((hf.ker w).mp hw)
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨h, hh⟩ := exists_sp4_lin_eq _ _ he0 hw
  rw [linModelNat_lin] at hh
  change mat 2 K h *ᵥ vec4 1 0 0 0 = f w at hh
  have hN : h⁻¹ * M * h ∈ perfectCore (Q2 K 0) := by
    refine mem_N0_of_fix hK4 ?_
    rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hh, hM, ← hh,
      mat_inv_mulVec]
  have hγ : psiSp π h (h⁻¹ * M * h) ∈
      perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp h (spLine K)).toAddSubgroup)) := by
    rw [show perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp h (spLine K)).toAddSubgroup)) =
      Ch11.SecS.gammaW H (hf.pre (gmapSp h (spLine K)).toAddSubgroup) from rfl,
      gammaW_pre_eq hf h 0 _ flag_one_eq]
    exact ⟨_, hN, rfl⟩
  have hwU : w ∈ hf.pre (gmapSp h (spLine K)).toAddSubgroup := by
    show f w ∈ gmapSp h (spLine K)
    rw [mem_gmapSp, ← hh, mat_inv_mulVec]
    exact vec4_e0_mem_spLine
  have := fix_gammaW_one hf hZ h _ hγ w hwU
  rwa [psiSp_apply, show h * (h⁻¹ * M * h) * h⁻¹ = M by group] at this

end KA

end CFSG.Quasithin.Vol2.KGNat
