module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceSix
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSpinMinus
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionTwistedE6
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional

public section

namespace CFSG.StandardType

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

section

@[expose] def GGRootSylowCentralTag (t : StatedLieTag) : Prop :=
  ∀ n f : ℕ, StatedLieAdmissible t n 2 f → GGRootSylowCentral (ggU t n f).D t

theorem ggRootInvolutionCentralInput_of_tags (h : ∀ t, GGRootSylowCentralTag t) :
    GGRootInvolutionCentralInput := by
  intro G _ _ t n f ψ hadm _ G₀ hG₀ r hr
  exact ggRootInvolution_central_of_sylowCentral (h t n f hadm) ψ G₀ hG₀ hr

theorem ggRootSylowCentralTag_PSL : GGRootSylowCentralTag .PSL := by
  intro n f hadm
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact GGRootSL.ggRootSylowCentral_specialLinear (m := m) (F := GaloisField 2 f) .PSL

theorem ggRootSylowCentralTag_of_placeholder (t : StatedLieTag)
    (ht : t = .G2 ∨ t = .trialityD4 ∨ t = .twistedB2 ∨ t = .twistedG2 ∨ t = .twistedF4 ∨
      t = .Tits) : GGRootSylowCentralTag t := by
  intro n f _
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact GGRootSL.ggRootSylowCentral_specialLinear (m := 0) (F := ZMod 2) _

theorem ggRootSylowCentralTag_PSp : GGRootSylowCentralTag .PSp := fun _ f hadm =>
  GGRootSp.ggRootSylowCentral_symplectic (F := GaloisField 2 f) hadm.2.2.1 .PSp

theorem ggRootSylowCentralTag_POmegaMinus : GGRootSylowCentralTag .POmegaMinus :=
  fun _ f hadm => ggRootSylowCentral_spinMinus (K := GaloisField 2 f) (minusCoeffs_irr 2 f) hadm.2.2

theorem ggRootSylowCentralTag_twistedE6 : GGRootSylowCentralTag .twistedE6 := fun _ f hadm =>
  ggRootSylowCentral_twistedE6 (k := GaloisField 2 (2 * f))
    (CFSG.LieType.Steinberg.Exceptional.frobQ 2 f)
    (CFSG.LieType.Steinberg.Exceptional.frobQ_frobQ 2 f hadm.2.1)

theorem ggRootSylowCentralTag_E6 : GGRootSylowCentralTag .E6 := fun _ f _ =>
  ggRootSylowCentral_e6 (k := GaloisField 2 f) .E6

theorem ggRootSylowCentralTag_E7 : GGRootSylowCentralTag .E7 := fun _ f _ =>
  ggRootSylowCentral_e7 (k := GaloisField 2 f) .E7

theorem ggRootSylowCentralTag_POmegaOdd : GGRootSylowCentralTag .POmegaOdd :=
  fun _ _ hadm => absurd rfl hadm.2.2.2

theorem ggRootInvolutionCentralInput_of_remaining (hPSU : GGRootSylowCentralTag .PSU)
    (hPlus : GGRootSylowCentralTag .POmegaPlus) (hF4 : GGRootSylowCentralTag .F4)
    (hE8 : GGRootSylowCentralTag .E8) : GGRootInvolutionCentralInput := by
  refine ggRootInvolutionCentralInput_of_tags fun t => ?_
  cases t with
  | PSL => exact ggRootSylowCentralTag_PSL
  | PSU => exact hPSU
  | PSp => exact ggRootSylowCentralTag_PSp
  | POmegaOdd => exact ggRootSylowCentralTag_POmegaOdd
  | POmegaPlus => exact hPlus
  | POmegaMinus => exact ggRootSylowCentralTag_POmegaMinus
  | F4 => exact hF4
  | E6 => exact ggRootSylowCentralTag_E6
  | E7 => exact ggRootSylowCentralTag_E7
  | E8 => exact hE8
  | twistedE6 => exact ggRootSylowCentralTag_twistedE6
  | G2 => exact ggRootSylowCentralTag_of_placeholder _ (Or.inl rfl)
  | trialityD4 => exact ggRootSylowCentralTag_of_placeholder _ (Or.inr (Or.inl rfl))
  | twistedB2 => exact ggRootSylowCentralTag_of_placeholder _ (Or.inr (Or.inr (Or.inl rfl)))
  | twistedG2 =>
    exact ggRootSylowCentralTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  | twistedF4 =>
    exact ggRootSylowCentralTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | Tits =>
    exact ggRootSylowCentralTag_of_placeholder _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

end

section Adjoint

theorem ggRootSylowCentralTag_E8 : GGRootSylowCentralTag .E8 := fun _ f _ =>
  ggRootSylowCentral_e8 (k := GaloisField 2 f) .E8

theorem ggRootInvolutionCentralInput_of_remaining' (hPSU : GGRootSylowCentralTag .PSU)
    (hPlus : GGRootSylowCentralTag .POmegaPlus) (hF4 : GGRootSylowCentralTag .F4) :
    GGRootInvolutionCentralInput :=
  ggRootInvolutionCentralInput_of_remaining hPSU hPlus hF4 ggRootSylowCentralTag_E8

end Adjoint

end CFSG.StandardType
