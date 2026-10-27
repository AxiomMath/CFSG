module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RKernel
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RTuple
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RFlag
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RRows

open CFSG.Assembly (LargeEvenLabel LargeEvenLieTag LargeEvenSplit LargeEvenHalfSplit
  LargeEvenUntwisted LargeEvenInLambda2)
open CFSG.StandardType (GGLabelIso)

public section

namespace CFSG.StandardType.TableCRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus

section C1

variable {ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ)}

theorem tcrAllowedC1_one_three (dJ dx : TcrCData) : tcrAllowedC1 1 3 dJ dx = false := by
  simp [tcrAllowedC1]

theorem tcC1_row_of_allowed {ΨJ Ψx : Set (Fin Tag.E6.rank → ℤ)} {dJ dx : TcrCData}
    (hJ : TcDataOK ρ ΨJ dJ) (hx : TcDataOK ρ Ψx dx) (h : tcrAllowedC1 1 1 dJ dx = true) :
    TcC1Row ρ ΨJ Ψx := by
  obtain ⟨hJe, hJr, hJN, hJk⟩ := hJ
  obtain ⟨hXe, hXr, hXN, hXk⟩ := hx
  unfold tcrAllowedC1 at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, if_true, Bool.true_and,
    Int.reduceBEq, Nat.reduceBEq] at h
  have key : ∀ (Ψ : Set (Fin Tag.E6.rank → ℤ)) (d : TcrCData) (k : TcrKind),
      tcrKindOfK (twistKindOf ρ Ψ) ∈ d.ks → d.ks = [k] → tcrKindOfK (twistKindOf ρ Ψ) = k := by
    intro Ψ d k h1 h2
    rw [h2] at h1
    simpa using h1
  have hin : ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), tcrKindOfK (twistKindOf ρ Ψ) = .inner →
      twistKindOf ρ Ψ = .inner := by
    intro Ψ h
    cases hk : twistKindOf ρ Ψ <;> simp_all [tcrKindOfK]
  have h2D : ∀ Ψ : Set (Fin Tag.E6.rank → ℤ), tcrKindOfK (twistKindOf ρ Ψ) = .twoD →
      twistKindOf ρ Ψ = .twoD := by
    intro Ψ h
    cases hk : twistKindOf ρ Ψ <;> simp_all [tcrKindOfK]
  rcases h with ⟨⟨⟨⟨ar, aN⟩, ae⟩, aks⟩, (⟨⟨⟨br, bN⟩, be⟩, bks⟩ | ⟨⟨⟨br, bN⟩, be⟩, bks⟩) |
      ⟨⟨⟨br, bN⟩, be⟩, bks⟩⟩ | ⟨⟨⟨⟨⟨⟨⟨ar, aN⟩, ae⟩, aks⟩, br⟩, bN⟩, be⟩, bks⟩
  · left
    exact ⟨by omega, by omega, by omega, hin _ (key _ _ _ hJk aks),
      Or.inl ⟨by omega, by omega, by omega, hin _ (key _ _ _ hXk bks)⟩⟩
  · left
    exact ⟨by omega, by omega, by omega, hin _ (key _ _ _ hJk aks),
      Or.inr (Or.inl ⟨by omega, by omega, by omega, h2D _ (key _ _ _ hXk bks)⟩)⟩
  · left
    exact ⟨by omega, by omega, by omega, hin _ (key _ _ _ hJk aks),
      Or.inr (Or.inr ⟨by omega, by omega, by omega, hin _ (key _ _ _ hXk bks)⟩)⟩
  · right
    exact ⟨by omega, by omega, by omega, hin _ (key _ _ _ hJk aks), by omega, by omega,
      by omega, hin _ (key _ _ _ hXk bks)⟩

end C1

end CFSG.StandardType.TableCRes

end
