module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3_POmegaMinus_dualPairOne
    (n f : ℕ) (hf : 1 ≤ f) (hn : 4 ≤ n)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .POmegaMinus n f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
                (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e) :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
                (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e) :
          Subgroup (ggU .POmegaMinus n f).K)⁆) :
    RCKSpinSiegelModel
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) J' := by
  classical
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  obtain ⟨r, ι, β₀, -, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig,
    _hsig'⟩ :=
    exists_blockModel_dualPair_POmegaMinus_explicit n f hf S hSU hS hodd he hn hpair hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hnorm : RCKNormalizedModel .PSL (r + 1) f :=
    ⟨Or.inl rfl, rckRP_admissible_PSL_of_quasisimple_range (G := ↥(spinGroup Q)) hf ι hq⟩
  exact ⟨.PSL, r + 1, f, ι, β₀, hnorm, Or.inl rfl, ggLongRoot_mem_roots hlong, hlong,
    hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩

end CFSG.StandardType.RCKRP
