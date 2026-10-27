module

public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.Quasithin.Background.F7TwoInvSQTKFam

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Blueprint

@[expose] def InvAutGenCarrier (s : TauCeti.SporadicName) : Prop :=
  ∀ φ : MulAut (NativeSporadic.Carrier s), φ * φ = 1 → φ ≠ 1 →
    InvAutGen (NativeSporadic.Carrier s) φ

theorem invAutGenFamSporadic_of_carriers
    (h : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J1 ∨ s = .J2 ∨ s = .J4 ∨
        s = .HS ∨ s = .He ∨ s = .Ru) → InvAutGenCarrier s) :
    InvAutGenFamSporadic := by
  intro s hs S _ _ ⟨e⟩ φ hφ2 hφ1
  exact invAutGen_of_mulEquiv_forall e (h s hs) φ hφ2 hφ1

theorem invAutGenFamSporadic_of_eleven
    (hM11 : InvAutGenCarrier .M11) (hM12 : InvAutGenCarrier .M12) (hM22 : InvAutGenCarrier .M22)
    (hM23 : InvAutGenCarrier .M23) (hM24 : InvAutGenCarrier .M24) (hJ1 : InvAutGenCarrier .J1)
    (hJ2 : InvAutGenCarrier .J2) (hJ4 : InvAutGenCarrier .J4) (hHS : InvAutGenCarrier .HS)
    (hHe : InvAutGenCarrier .He) (hRu : InvAutGenCarrier .Ru) : InvAutGenFamSporadic :=
  invAutGenFamSporadic_of_carriers fun s hs => by
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      assumption

end CFSG.Quasithin.F7Two
