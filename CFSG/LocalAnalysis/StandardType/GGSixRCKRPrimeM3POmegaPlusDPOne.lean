module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3_POmegaPlus_dualPairOne
    (k f : ℕ) (hf : 1 ≤ f) (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    {J' : Subgroup (ggU .POmegaPlus (k + 3) f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e) :
          Subgroup (ggU .POmegaPlus (k + 3) f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e) :
          Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆) :
    RCKSpinSiegelModel (Spin.quadPlus (k + 3) (GaloisField 2 f)) J' := by
  classical
  let Q := Spin.quadPlus (k + 3) (GaloisField 2 f)
  obtain ⟨r, ι, β₀, -, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig,
    _hsig'⟩ :=
    exists_blockModel_dualPair_POmegaPlus_explicit k f hf S hSU hS hodd he hpair hdeg hJe
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  have hnorm : RCKNormalizedModel .PSL (r + 1) f :=
    ⟨Or.inl rfl, rckRP_admissible_PSL_of_quasisimple_range (G := ↥(spinGroup Q)) hf ι hq⟩
  exact ⟨.PSL, r + 1, f, ι, β₀, hnorm, Or.inl rfl, ggLongRoot_mem_roots hlong, hlong,
    hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩

end CFSG.StandardType.RCKRP
