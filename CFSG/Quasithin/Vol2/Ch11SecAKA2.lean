module

public import CFSG.Quasithin.Vol2.Ch11SecAKA1
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15b
public import CFSG.Quasithin.Vol2.Ch11SecQ9aCartE

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.QuasithinUnique.Vol2Native.A312L (blkQ blkQ_apply blkIdx sigma2)
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (gammaW_pre_eq usp_le_perfectCore mem_pCoreOf_N_iff)

namespace KA

variable {K : Type} [Field K]

theorem blkQ0_qSp (x y : K) (h : qSp x y 0 ∈ Q2 K 0) : blkQ 0 ⟨qSp x y 0, h⟩ = 1 := by
  rw [blkQ_apply]
  change blkIdx (sigma2 0) (mat 2 K (qSp x y 0)) = 1
  rw [mat_qSp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, qMat, symm3]

theorem blkQ0_nSp (r : K) (h : nSp r ∈ Q2 K 0) : blkQ 0 ⟨nSp r, h⟩ = 1 := by
  rw [blkQ_apply]
  change blkIdx (sigma2 0) (mat 2 K (lSp K (uGL r))) = 1
  rw [mat_lSp]
  ext i k
  fin_cases i <;> fin_cases k <;> simp [blkIdx, sigma2, uGL]

variable [Finite K] [CharP K 2]

theorem nSp_mem_pCoreOf (hK4 : ∃ s : Finset K, s.card = 4) (r : K) :
    nSp r ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
  (mem_pCoreOf_N_iff hK4 0 (usp_le_perfectCore hK4 (nSp_mem_Usp r))).mpr (blkQ0_nSp r _)

theorem qSp_mem_pCoreOf (hK4 : ∃ s : Finset K, s.card = 4) (x y : K) :
    qSp x y 0 ∈ pCoreOf 2 (perfectCore (Q2 K 0)) :=
  (mem_pCoreOf_N_iff hK4 0 (usp_le_perfectCore hK4 (qSp_mem_Usp x y 0))).mpr (blkQ0_qSp x y _)

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSp 2 K) →* ↥H} {f : W → (Fin 2 ⊕ Fin 2 → K)}

omit [CharP K 2] in
theorem exists_pCore_of_mem (hf : IsCoord (linModelNat (StatedSp 2 K)) H Z π f)
    [Finite (MulAut W)] (g : StatedSp 2 K) {M : StatedSp 2 K}
    (hM : M ∈ pCoreOf 2 (perfectCore (Q2 K 0))) :
    ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))),
      y ∈ CFSG.pCore 2
        ↥(perfectCore (H ⊓ Ch11.SecA.stabW (hf.pre (gmapSp g (spLine K)).toAddSubgroup))) ∧
      (y : MulAut W) = psiSp π g M := by
  have h1 : psiSp π g M ∈ pCoreOf 2
      (Ch11.SecS.gammaW H (hf.pre (gmapSp g (spLine K)).toAddSubgroup)) := by
    rw [gammaW_pre_eq hf g 0 _ flag_one_eq,
      Ch11.SecS.C11P9A.pCoreOf_map_of_injective _ (psiSp_injective hf g)]
    exact ⟨M, hM, rfl⟩
  obtain ⟨y, hy, hyM⟩ := h1
  exact ⟨y, by exact hy, hyM⟩

end KA

theorem factRadicalFixedSp4_holds : Ch11.SecA.FactRadicalFixedSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨f, hf, g, -, rfl⟩ := KA.exists_point_coords hn hK hW hπ hP hU
  intro w hw
  have hfix : ∀ M ∈ pCoreOf 2 (perfectCore (Q2 K 0)),
      mat 2 K M *ᵥ (mat 2 K g⁻¹ *ᵥ f w) = mat 2 K g⁻¹ *ᵥ f w := by
    intro M hM
    obtain ⟨y, hy, hyM⟩ := KA.exists_pCore_of_mem hf g hM
    have h1 := (hf.eq_iff _ _).mpr (hw y hy)
    rw [hyM, psiSp_apply, hf.act4, map_mul, map_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec] at h1
    have h2 := congrArg (fun v => mat 2 K g⁻¹ *ᵥ v) h1
    simpa only [mat_inv_mulVec] using h2
  have h1 := hfix _ (KA.nSp_mem_pCoreOf hK4 1)
  have h2 := hfix _ (KA.qSp_mem_pCoreOf hK4 0 1)
  show f w ∈ gmapSp g (spLine K)
  rw [mem_gmapSp, mem_spLine]
  generalize mat 2 K g⁻¹ *ᵥ f w = v at h1 h2
  rw [nSp_mulVec] at h1
  rw [qSp_mulVec] at h2
  have a1 := congrFun h1 (.inl 0)
  have a2 := congrFun h1 (.inr 1)
  have a3 := congrFun h2 (.inl 0)
  simp [vec4] at a1 a2 a3
  exact ⟨a1, a2, a3⟩

end CFSG.Quasithin.Vol2.KGNat
