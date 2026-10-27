module

public import CFSG.Timmesfeld.RankTwo.Levi
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.LieType.CurtisTits.Spin
public import CFSG.LieType.Universal.Unitary.Extras
public import CFSG.LieType.Steinberg.TwistedE6.Datum
public import CFSG.LieType.Steinberg.TwistedE6.Generation
public import CFSG.LieType.Steinberg.Exceptional.Fields

public section

namespace CFSG.Timmesfeld

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg

theorem leviConePresented_specialLinear (m : ℕ) (F : Type) [Field F] :
    LeviConePresented (SpecialLinear.rootDatum m F) :=
  leviConePresented_of (SpecialLinear.isCTGroupDatum m F) (SpecialLinear.steinbergExtras m F)

theorem leviConePresented_symplectic (n : ℕ) (F : Type) [Field F] :
    LeviConePresented (Symplectic.rootDatum n F) :=
  leviConePresented_of (Symplectic.isCTGroupDatum n F) (Symplectic.steinbergExtras n F)

theorem leviConePresented_spinPlus {n : ℕ} (F : Type) [Field F] (hn : 3 ≤ n) :
    LeviConePresented (Spin.plusDatum n F hn) :=
  leviConePresented_of (Spin.plusDatum_isCTGroupDatum hn (Spin.plusDatum_iSup_eq_top n F hn))
    (Spin.plusDatum_steinbergExtras hn)

theorem leviConePresented_spinOdd {n : ℕ} {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (hn : 3 ≤ n) : LeviConePresented (Spin.oddDatum n F) :=
  leviConePresented_of (Spin.oddDatum_isCTGroupDatum n F (Spin.oddDatum_iSup_eq_top n F h2 hn))
    (Spin.oddDatum_steinbergExtras h2)

theorem leviConePresented_spinMinus {n : ℕ} {F : Type} [Field F] [Finite F] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hn : 4 ≤ n) :
    LeviConePresented (Spin.Twisted.minusDatum n hirr) :=
  leviConePresented_of (Spin.Twisted.minusDatum_isCTGroupDatum n hirr hn)
    (Spin.Twisted.minusDatum_steinbergExtras n hirr)

theorem leviConePresented_unitary {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]
    [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    LeviConePresented (Unitary.rootDatum hF n) := by
  obtain ⟨ζ, hζ⟩ := Unitary.exists_traceZero_ne_zero hF
  exact leviConePresented_of (Unitary.isCTGroupDatum hF n hn ζ hζ)
    (Unitary.steinbergExtras hF n hn ζ hζ)

theorem leviConePresented_e6 (k : Type*) [Field k] : LeviConePresented (Minuscule.e6Datum k) :=
  leviConePresented_of (Minuscule.e6Datum_isCTGroupDatum k) (Minuscule.e6Datum_steinbergExtras k)

theorem leviConePresented_e7 (k : Type*) [Field k] : LeviConePresented (Minuscule.e7Datum k) :=
  leviConePresented_of (Minuscule.e7Datum_isCTGroupDatum k) (Minuscule.e7Datum_steinbergExtras k)

theorem leviConePresented_e8 (K : Type) [Field K] : LeviConePresented (Adjoint.e8Datum K) :=
  leviConePresented_of (Adjoint.e8_isCTGroupDatum K) (Adjoint.e8_steinbergExtras K)

theorem leviConePresented_f4 (K : Type) [Field K] : LeviConePresented (Adjoint.f4Datum K) :=
  leviConePresented_of (Adjoint.f4_isCTGroupDatum K) (Adjoint.f4_steinbergExtras K)

theorem leviConePresented_g2 (K : Type) [Field K] : LeviConePresented (Adjoint.g2Datum K) :=
  leviConePresented_of (Adjoint.g2_isCTGroupDatum K) (Adjoint.g2_steinbergExtras K)

theorem leviConePresented_twistedE6Datum {k : Type*} [Field k] (θ : k →+* k)
    (hθ : ∀ c, θ (θ c) = c) : LeviConePresented (TwistedE6.twistedDatum k θ) :=
  leviConePresented_of
    (TwistedE6.twistedDatum_isCTGroupDatum θ hθ (TwistedE6.iSup_twistedDatum_rootGroup θ hθ))
    (TwistedE6.twistedDatum_steinbergExtras θ hθ)

theorem leviConePresented_twistedE6 (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    LeviConePresented (Exceptional.twistedE6Datum p f) :=
  leviConePresented_twistedE6Datum (Exceptional.frobQ p f) (Exceptional.frobQ_frobQ p f hf)

theorem leviConePresented_twistedD4 {K : Type} [Field K] (σ : K →+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) : LeviConePresented (TwistedD4.twistedDatum σ) :=
  leviConePresented_of (TwistedD4.twistedDatum_isCTGroupDatum σ hσ)
    (TwistedD4.twistedDatum_steinbergExtras σ hσ)

end CFSG.Timmesfeld
