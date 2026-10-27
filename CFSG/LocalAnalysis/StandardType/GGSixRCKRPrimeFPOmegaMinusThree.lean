module

public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPOmegaMinusLow
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeFPSU

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckClassicalModelIDAt_PSU_of_omegaMinus_three
    {X : Type} [Group X] {g : ℕ} (hg : 1 ≤ g) {K B : Subgroup X}
    (φ : (ggU .POmegaMinus 3 g).K →* X) (hφr : φ.range = K)
    (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaMinus 3 g).K)
    (hdiag : ∀ b ∈ B, GGPsiInnerDiag (ggU .POmegaMinus 3 g).D φ b) :
    RCKClassicalModelIDAt .PSU K B := by
  obtain ⟨e, -⟩ := irgIsoCompat_omegaMinus_three hg
  refine ⟨4, g, φ.comp e.symm.toMonoidHom, hg, ?_, ?_, ?_⟩
  · rw [← hφr]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, rfl⟩
    · rintro ⟨y, rfl⟩
      refine ⟨e y, ?_⟩
      show φ (e.symm (e y)) = φ y
      rw [MulEquiv.symm_apply_apply]
  · intro x hx
    have hx' : φ (e.symm x) = 1 := hx
    have hc : e.symm x ∈ Subgroup.center (ggU .POmegaMinus 3 g).K :=
      hφk (MonoidHom.mem_ker.mpr hx')
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    have h := congrArg e (hc (e.symm y))
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h
    exact h
  · intro b hb
    obtain ⟨g₁, hg₁, hcent⟩ :=
      CFSG.StandardType.PsiDiag.SpinM.exists_mem_centralizer_three (K := GaloisField 2 g)
        (minusCoeffs_irr 2 g) φ hφk (hdiag b hb)
    refine ⟨g₁, ?_, fun γ _ => ⟨1, Subgroup.one_mem _, fun z _ => ?_⟩⟩
    · obtain ⟨y, hy⟩ := hg₁
      refine ⟨e y, ?_⟩
      exact (congrArg φ (MulEquiv.symm_apply_apply e y)).trans hy
    · have hz : (φ.comp e.symm.toMonoidHom) z ∈ (φ.range : Set X) := ⟨e.symm z, rfl⟩
      have h1 := (Subgroup.mem_centralizer_iff.mp hcent) _ hz
      simp only [one_mul, inv_one, mul_one]
      rw [mul_assoc, h1, inv_mul_cancel_left]

theorem rckLemmaFAtPOmegaMinusThree_of_PSU
    (hPSU : RCKLemmaFAt .PSU) : RCKLemmaFAtPOmegaMinusThree := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hA6 hRJ hRmJ hroot
  obtain ⟨g, φ, hg, hφr, hφk, hdiag⟩ := hmodel
  exact hPSU X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
    (rckClassicalModelIDAt_PSU_of_omegaMinus_three hg φ hφr hφk hdiag) hodd hcomp hA6 hRJ hRmJ
    hroot

theorem rckLemmaFIIAtPOmegaMinusThree_of_PSU
    (hPSU : RCKLemmaFIIAt .PSU) : RCKLemmaFIIAtPOmegaMinusThree := by
  intro X _ _ p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank hmodel hodd hcomp hrow hA6 hRJ hRmJ hroot
    hR2
  obtain ⟨g, φ, hg, hφr, hφk, hdiag⟩ := hmodel
  exact hPSU X p K J R Rm B d hp hp2 hBab hdB hBK hBJ hrank
    (rckClassicalModelIDAt_PSU_of_omegaMinus_three hg φ hφr hφk hdiag) hodd hcomp hrow hA6 hRJ hRmJ
    hroot hR2

theorem rckLemmaFAt_POmegaMinus_holds
    (hIRG : RCKIntrinsicRoot) : RCKLemmaFAt .POmegaMinus :=
  rckLemmaFAt_POmegaMinus_of_three hIRG
    (rckLemmaFAtPOmegaMinusThree_of_PSU (rckLemmaFAt_PSU hIRG))

theorem rckLemmaFIIAt_POmegaMinus_of_PSU
    (hIRG : RCKIntrinsicRoot) (hPSU : RCKLemmaFIIAt .PSU) : RCKLemmaFIIAt .POmegaMinus :=
  rckLemmaFIIAt_POmegaMinus_of_three hIRG (rckLemmaFIIAtPOmegaMinusThree_of_PSU hPSU)

end CFSG.StandardType.RCKRP
