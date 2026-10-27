module

public import CFSG.RankThree.PartOne.U5K.Kf.Sylow
public import CFSG.RankThree.PartOne.U5K.Kf.Long
public import CFSG.RankThree.PartOne.U5K.Kf.Diag
public import CFSG.RankThree.PartOne.U5K.Hyp.Parabolic

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG CFSG.RankThree.PartOne CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.U5K.Hyp

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

theorem exists_long_of_central (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) (hq : 3 ≤ 2 ^ f)
    {T : Subgroup (MulAut (hypPSU hK 2 1))} (hT2 : IsPGroup 2 T) (hTU : T ⊓ Pi hK = Uh hK)
    {y : MulAut (hypPSU hK 2 1)} (hyT : y ∈ T) (hyc : ∀ t ∈ T, t * y = y * t) :
    ∃ (s : hypSU hK 2 1) (c : K), mat s = oddUni hK 0 !![c, 0; 0, 0] ∧ y = innM hK s := by
  have hS : pushingUpS T = Sh hK := pushingUpS_eq_Sh hZ hq hT2 hTU
  have hyS : y ∈ pushingUpS T := by
    refine ⟨hyT, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    obtain ⟨t, -, rfl⟩ := hw
    exact hyc t.1 t.2
  rw [hS] at hyS
  obtain ⟨s, hs, rfl⟩ := hyS
  have hUT : Uh hK ≤ T := by rw [← hTU]; exact inf_le_left
  have hcomm : ∀ u ∈ hypUnitriangular hK 2 1, s * u = u * s := by
    intro u hu
    apply innM_injOn hZ (mul_mem (Ssub_le_Usub hs) hu) (mul_mem hu (Ssub_le_Usub hs))
    rw [map_mul, map_mul]
    exact (hyc _ (hUT ⟨u, hu, rfl⟩)).symm
  obtain ⟨c, hc⟩ := central_Usub_long hs hcomm
  exact ⟨s, c, hc, rfl⟩

theorem exists_T_hyp (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) (hq : 3 ≤ 2 ^ f)
    {H Ab B : Subgroup (MulAut (hypPSU hK 2 1))} (hH : Pi hK ≤ H)
    (hAb : ∀ ρ ∈ Ab, ∃ x : Gam hK, Phi hK x = ρ ∧ x.1.right = 1 ∧ ∃ α : K,
      (∀ r : HypIndex 2 1, lmat x r (Sum.inl 0) = if r = Sum.inl 0 then α else 0) ∧
      hK.bar α * α = 1 ∧
      ((lmat x).map hK.bar)ᵀ * hypGram 2 1 K * lmat x = hypGram 2 1 K)
    (hB : ∀ ρ ∈ B, ∃ x : Gam hK, Phi hK x = ρ ∧ x.1.right = 1 ∧
      ∃ (A : Matrix (Fin 2) (Fin 2) K) (d : K), IsUnit A.det ∧ hK.bar d * d = 1 ∧
        lmat x = oddDiag hK A d) :
    ∃ T : Subgroup (MulAut (hypPSU hK 2 1)), IsSylowOf 2 T H ∧
      Ab ≤ Subgroup.centralizer (omegaOneCenterIn T : Set (MulAut (hypPSU hK 2 1))) ∧
      B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (hypPSU hK 2 1))) := by
  obtain ⟨T, hT, hTU⟩ := exists_sylow_Uh hZ hH
  have hT2 : IsPGroup 2 T := hT.2.1
  have hS : pushingUpS T = Sh hK := pushingUpS_eq_Sh hZ hq hT2 hTU
  refine ⟨T, hT, fun ρ hρ => ?_, fun ρ hρ => ?_⟩
  · obtain ⟨x, rfl, hx, α, hcol, hα, hg⟩ := hAb ρ hρ
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyW : y ∈ Subgroup.centralizer ({Phi hK x} : Set (MulAut (hypPSU hK 2 1))) := by
      refine (Subgroup.closure_le _).2 (fun z hz => ?_) hy
      obtain ⟨hzZ, -⟩ := hz
      obtain ⟨zc, hzc, rfl⟩ := hzZ
      have hzc' := Subgroup.mem_center_iff.1 hzc
      obtain ⟨s, c, hs, hzs⟩ := exists_long_of_central hZ hq hT2 hTU zc.2
        (fun t ht => congrArg Subtype.val (hzc' ⟨t, ht⟩))
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hact := act_eq_of_long x hx hcol hα hg hs
      have h5 := Phi_mul_innM_mul_inv x s
      rw [hact, mul_inv_eq_iff_eq_mul] at h5
      have hzs' : T.subtype zc = innM hK s := hzs
      rw [hzs']
      exact h5.symm
    exact Subgroup.mem_centralizer_singleton_iff.1 hyW
  · obtain ⟨x, rfl, hx, A, d, hA, hd, hl⟩ := hB ρ hρ
    rw [hS]
    exact Phi_mem_normalizer_Sh x hx hA hd hl

end CFSG.RankThree.PartOne.U5K.Kf
