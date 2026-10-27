module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSpinFlagDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoSpSu
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeSmall

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckM3_POmegaMinus_selfDualTwo
    (n f : ℕ) (hn : 4 ≤ n)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
      (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
      (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {J' : Subgroup (ggU .POmegaMinus n f).K}
    (hJe : IsComponentOf J'
      ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
          Subgroup (ggU .POmegaMinus n f).K),
        (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f)
          (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)) S e :
          Subgroup (ggU .POmegaMinus n f).K)⁆) :
    RCKSpinSiegelModel
      (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2) J' := by
  classical
  let Q := Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2
  obtain ⟨r, ι, β₀, -, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig, -⟩ :=
    exists_blockModel_selfDualTwo_POmegaMinus_explicit n f S hSU hS hodd he hn hadj hdeg₁
      hdeg₂ hJe
  have hg1 : 1 ≤ max f 1 := le_max_right f 1
  have hq : CFSG.Assembly.IsQuasisimple ↥ι.range := by
    rw [hrange]
    exact hJe.2.2
  rcases rckRP_admissible_PSU_of_quasisimple_range (G := ↥(spinGroup Q)) hg1 ι hq with
    hadm | ⟨rfl, h2⟩
  · exact ⟨.PSU, r, max f 1, ι, β₀, ⟨Or.inr (Or.inl rfl), hadm⟩, Or.inr (Or.inl rfl),
      ggLongRoot_mem_roots hlong, hlong, hrange, hcent, a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig⟩
  ·
    obtain ⟨eU, hec⟩ := irgIsoCompat_su_two (g := max f 1) h2
    obtain ⟨γ, ι', hgood, hrange', hcent', hroot, -⟩ :=
      exists_model_of_irgIsoCompat (t' := .PSU) (m := 2) (g' := max f 1)
        (t := .PSL) (n := 2) (g := max f 1) (L := ↥(spinGroup Q)) (e := eU) hec ι hcent hlong
    have hγlong : GGLongRoot (ggU .PSL 2 (max f 1)).D γ := by
      rcases hgood.2 with h | h
      · exact h
      · rcases h.1 with ⟨h', -⟩ | h' <;> cases h'
    have hnorm : RCKNormalizedModel .PSL 2 (max f 1) :=
      ⟨Or.inl rfl, rckRP_admissible_PSL_of_quasisimple_range (G := ↥(spinGroup Q)) hg1 ι'
        (by rw [hrange']; exact hq)⟩
    have hsig' : (((ggU .PSL 2 (max f 1)).D.rootGroup γ).map ι').map (Spin.spinAction Q) =
        siegelGroup Q a₁ a₂ := by
      rw [hroot]
      exact hsig
    exact ⟨.PSL, 2, max f 1, ι', γ, hnorm, Or.inl rfl, hgood.1, hγlong, hrange'.trans hrange,
      hcent', a₁, a₂, b₁, b₂, hQ, hb1, hb2, hb12, hsig'⟩

end CFSG.StandardType.RCKRP
