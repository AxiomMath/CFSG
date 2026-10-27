module

public import Certificates.Certificate705101

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

@[expose] def l4Mat14 (s : Fin 6) : Matrix (Fin 14) (Fin 14) (ZMod 2) :=
  refMat 14 ((classRefRows14[0]!)[s.val]!)

@[expose] def l4Mat20 (r : Fin 2) (s : Fin 6) : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  refMat 20 ((classRefRows20[r.val]!)[s.val]!)

theorem classify_fourteen {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 14)
    {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) :
    ∃ e : V ≃ₗ[ZMod 2] (Fin 14 → ZMod 2),
      ∀ (s : Fin 6) (v : V), e (ρ (genN s.val) v) = l4Mat14 s *ᵥ e v :=
  Certificates.certificate705101.1 V hV ρ hirr

theorem classify_twenty {V : Type} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V] (hV : finrank (ZMod 2) V = 20)
    {ρ : SL4 →* (V ≃ₗ[ZMod 2] V)} (hirr : IsIrredGen ρ) :
    ∃ r : Fin 2, ∃ e : V ≃ₗ[ZMod 2] (Fin 20 → ZMod 2),
      ∀ (s : Fin 6) (v : V), e (ρ (genN s.val) v) = l4Mat20 r s *ᵥ e v :=
  Certificates.certificate705101.2 V hV ρ hirr

end CFSG.LocalAnalysis.WeakClosure81
