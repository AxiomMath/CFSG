module

public import CFSG.CGT.Harada80.Orbits

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s16t3_statedOmega_trans_of_elementary {K : Type} [Field K] {ι : Type}
    [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀)
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    {x y : ι → K} {e : (ι → K) ≃ₗ[K] (ι → K)}
    (he : e ∈ CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q) (hex : e x = y) :
    ∃ g ∈ StatedOmega Q₀, ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x = y := by
  refine ⟨(CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm e, ?_, ?_⟩
  · rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_map_elementaryGroup (ι := ι) (K := K)
      hQ hE]
    exact Subgroup.mem_map_of_mem _ he
  · rw [← CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply
        ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).symm e) x,
      MulEquiv.apply_symm_apply, hex]

theorem s16t3_statedOmega_trans {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2)
    {ι : Type} [Fintype ι] [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hd : 4 ≤ Module.finrank K (ι → K))
    (hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ =
      CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q)
    {x y : ι → K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : Q₀ x = Q₀ y) :
    ∃ g ∈ StatedOmega Q₀, ((g : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K).mulVec x = y := by
  haveI : CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 K :=
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.of_natCard_eq_two hK
  have hxyQ : Q x = Q y := by
    rw [← hQ] at hxy
    exact hxy
  rcases CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2.eq_zero_or_one (Q x)
    with hQx | hQx
  · have hQy : Q y = 0 := by rw [hxyQ] at hQx; exact hQx
    obtain ⟨e, he, hex⟩ :=
      CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.exists_mem_elementaryGroup_apply_eq_f2
        hnd hd hx hy hQx hQy
    exact s16t3_statedOmega_trans_of_elementary hQ hE he hex
  · have hQy : Q y = 1 := by rw [hxyQ] at hQx; exact hQx
    obtain ⟨e, he, hex⟩ :=
      CFSG.CGT.Harada80.exists_mem_elementaryGroup_apply_eq_of_map_eq_one hnd hd hQx hQy
    exact s16t3_statedOmega_trans_of_elementary hQ hE he hex

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
