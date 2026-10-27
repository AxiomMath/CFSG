module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4I
public import CFSG.Quasithin.Vol2.KGNatSp4Transv
public import CFSG.Quasithin.Vol2.Ch11SecSFactsCartan
public import CFSG.Quasithin.Vol2.KGNatSL3Par
public import CFSG.Quasithin.Vol2.KGNatSp4Levi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Open (pCoreOf)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.Quasithin.Vol2.KGNat (IsCoord linModelNat psiSp psiSp_apply psiSp_injective
  map_stabilizer_eq perfectCore_map flag_one_eq flag_two_eq spLine spPlane gmapSp vec4 vec4_eq
  mem_gmapSp_spLine_iff mat_inv_mulVec fix_of_perfect)

variable {K : Type} [Field K] {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

theorem gammaW_pre_eq (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    (j : Fin 2) (S : Submodule K (Fin 2 ⊕ Fin 2 → K)) (hS : flag 2 K ((j : ℕ) + 1) = S) :
    gammaW H (hf.pre (gmapSp g S).toAddSubgroup) = (perfectCore (Q2 K j)).map (psiSp π g) := by
  rw [gammaW, ← map_stabilizer_eq hf g S, perfectCore_map _ (psiSp_injective hf g), ← hS]
  rfl

variable [Finite K]

theorem mat_e0_of_mem_N0 {M : StatedSp 2 K} (hM : M ∈ perfectCore (Q2 K 0)) :
    mat 2 K M *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
  have hMQ := perfectCore_le _ hM
  have h1 := spMat_inl_zero_eq_one_of_perfectCore hM
  have c1 := spMat_col_zero_of_mem_Q2_zero hMQ (Sum.inl 1) (by simp)
  have c2 := spMat_col_zero_of_mem_Q2_zero hMQ (Sum.inr 0) (by simp)
  have c3 := spMat_col_zero_of_mem_Q2_zero hMQ (Sum.inr 1) (by simp)
  simp only [spMat] at h1 c1 c2 c3
  refine vec4_eq ?_ ?_ ?_ ?_ <;>
    simp [vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mat_apply,
      h1, c1, c2, c3]

theorem act_N0_mod (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K)
    {M : StatedSp 2 K} (hM : M ∈ perfectCore (Q2 K 0)) {u : W}
    (hu : f u ∈ gmapSp g (spLine K)) : f (psiSp π g M u) = f u := by
  obtain ⟨c, hc⟩ := mem_gmapSp_spLine_iff.mp hu
  rw [psiSp_apply, hf.act4, hc, Matrix.mulVec_smul, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mat_inv_mulVec, mat_e0_of_mem_N0 hM]

theorem fix_gammaW_one (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (g : StatedSp 2 K) [Finite (MulAut W)] :
    ∀ γ ∈ gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup),
      ∀ u ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup, γ u = u := by
  refine fix_of_perfect (Z := Z) (perfectCore_perfect _)
    (fun h hh z hz => hZ h (perfectCore_le _ hh).1 z hz) ?_
  intro h hh u hu
  rw [gammaW_pre_eq hf g 0 _ flag_one_eq] at hh
  obtain ⟨M, hM, rfl⟩ := hh
  exact (hf.eq_iff _ _).mp (act_N0_mod hf g hM hu)

variable [CharP K 2]

theorem mem_gammaW_one_of_fix (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {x : MulAut W}
    (hx : x ∈ H) (hxS : x ∈ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))
    (hfix : ∀ u ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup, f (x u) = f u) :
    x ∈ gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup) := by
  rw [gammaW_pre_eq hf g 0 _ flag_one_eq]
  have hxHS : x ∈ H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup) := ⟨hx, hxS⟩
  rw [← map_stabilizer_eq hf g (spLine K)] at hxHS
  obtain ⟨M, hM, rfl⟩ := hxHS
  have hMQ : M ∈ Q2 K 0 := by
    show M ∈ stabilizer 2 K (flag 2 K 1)
    rw [flag_one_eq]
    exact hM
  refine ⟨M, mem_N0_of_entry_eq_one hK4 hMQ ?_, rfl⟩
  obtain ⟨u₀, hu₀⟩ := hf.surj (mat 2 K g *ᵥ vec4 1 0 0 0)
  have hu₀U : u₀ ∈ hf.pre (gmapSp g (spLine K)).toAddSubgroup :=
    hf.mem_pre.mpr (mem_gmapSp_spLine_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩)
  have h1 := hfix u₀ hu₀U
  rw [psiSp_apply, hf.act4, hu₀, map_mul, map_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, mat_inv_mulVec] at h1
  have h2 : mat 2 K M *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
    have := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h1
    rwa [mat_inv_mulVec, mat_inv_mulVec] at this
  have h3 := congrFun h2 (Sum.inl 0)
  simpa [vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, mat_apply]
    using h3

omit [Finite K] [CharP K 2] in
theorem exists_move_gammaW_two (hK4 : ∃ s : Finset K, s.card = 4)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f) (g : StatedSp 2 K) {b : W}
    (hb : f b ∈ gmapSp g (spLine K)) (hbZ : b ∉ Z) :
    ∃ γ ∈ gammaW H (hf.pre (gmapSp g (spPlane K)).toAddSubgroup), γ b ≠ b := by
  obtain ⟨c, hc⟩ := mem_gmapSp_spLine_iff.mp hb
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hc
    exact hbZ ((hf.ker b).mp hc)
  let A : SpecialLinearGroup (Fin 2) K := ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨psiSp π g (spLevi 1 A), ?_, fun h => ?_⟩
  · rw [gammaW_pre_eq hf g 1 _ flag_two_eq]
    exact ⟨_, spLevi_mem_perfectCore hK4 1 A, rfl⟩
  · have h1 := congrArg f h
    rw [psiSp_apply, hf.act4, hc, Matrix.mulVec_smul, map_mul, map_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, mat_inv_mulVec] at h1
    have h2 : mat 2 K (spLevi 1 A) *ᵥ vec4 1 0 0 0 = vec4 1 0 0 0 := by
      have h3 := smul_right_injective _ hc0 h1
      have := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h3
      rwa [mat_inv_mulVec, mat_inv_mulVec] at this
    have h4 := congrFun h2 (Sum.inl 1)
    rw [show mat 2 K (spLevi 1 A) = spMat (spLevi 1 A) from rfl, spMat_leviSp_one] at h4
    simp [vec4, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two, A] at h4

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
