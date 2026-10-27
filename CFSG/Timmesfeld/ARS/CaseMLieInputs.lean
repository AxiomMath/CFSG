module

public import CFSG.Timmesfeld.ARS.CaseMLevi

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Timmesfeld Matrix

namespace CaseM

@[expose] def c3PosRoots : Set (Fin 4 → ℤ) :=
  {![0, 1, 0, 0], ![0, 0, 1, 0], ![0, 0, 0, 1], ![0, 1, 1, 0], ![0, 1, 2, 0], ![0, 0, 1, 1]}

@[expose] def c3PairRoots : Set (Fin 4 → ℤ) := c3PosRoots ∪ (fun γ => -γ) '' c3PosRoots

@[expose] def c3Coords (γ : Fin 4 → ℤ) : Fin 3 → ℤ := ![γ 3, γ 2, γ 1]

@[expose] def F4C3LeviInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∃ ι : ↥(StatedSp 3 (GaloisField 2 f)) →*
      ↥(Chevalley.adjointGroup .F4 (GaloisField 2 f)), Function.Injective ι ∧
    ∀ γ ∈ c3PairRoots, ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup γ : Set _) =
      ι '' ((Symplectic.rootDatum 3 (GaloisField 2 f)).rootGroup (c3Coords γ) : Set _)

@[expose] def TwistedE6C3LeviInput : Prop :=
  ∀ (f : ℕ) (hf : 1 ≤ f), ∃ ι : ↥(Unitary.SU (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) 6) →*
      Exceptional.twistedE6Group 2 f, ι.ker ≤ Subgroup.center _ ∧
    ∀ γ ∈ c3PairRoots, ((Exceptional.twistedE6Datum 2 f).rootGroup γ : Set _) =
      ι '' ((Unitary.rootDatum (card_galoisField_two_mul hf) 6).rootGroup (c3Coords γ) : Set _)

@[expose] def F4EdgeLeviInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∃ l : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →*
      ↥(Chevalley.adjointGroup .F4 (GaloisField 2 f)), Function.Injective l ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup ![1, 0, 0, 0] : Set _) =
      Set.range (fun c => l (tv 0 1 c)) ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup (-![1, 0, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 1 0 c)) ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup ![0, 1, 0, 0] : Set _) =
      Set.range (fun c => l (tv 1 2 c)) ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup (-![0, 1, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 2 1 c)) ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup ![1, 1, 0, 0] : Set _) =
      Set.range (fun c => l (tv 0 2 c)) ∧
    ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup (-![1, 1, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 2 0 c)) ∧
    ∀ j : Fin 4, (j = 2 ∨ j = 3) → ∃ m : SpecialLinearGroup (Fin 2) (GaloisField 2 f) ×
        SpecialLinearGroup (Fin 2) (GaloisField 2 f) →*
          ↥(Chevalley.adjointGroup .F4 (GaloisField 2 f)), Function.Injective m ∧
      ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup (Pi.single j 1) : Set _) =
        Set.range (fun c => m (1, tv 0 1 c)) ∧
      ((Adjoint.f4Datum (GaloisField 2 f)).rootGroup (-Pi.single j 1) : Set _) =
        Set.range (fun c => m (1, tv 1 0 c)) ∧
      ∀ c, m (tv 0 1 c, 1) = l (tv 0 1 c) ∧ m (tv 1 0 c, 1) = l (tv 1 0 c)

@[expose] def TwistedE6EdgeLeviInput : Prop :=
  ∀ f : ℕ, 1 ≤ f → ∃ l : SpecialLinearGroup (Fin 3) (GaloisField 2 f) →*
      Exceptional.twistedE6Group 2 f, Function.Injective l ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup ![1, 0, 0, 0] : Set _) =
      Set.range (fun c => l (tv 0 1 c)) ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup (-![1, 0, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 1 0 c)) ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup ![0, 1, 0, 0] : Set _) =
      Set.range (fun c => l (tv 1 2 c)) ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup (-![0, 1, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 2 1 c)) ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup ![1, 1, 0, 0] : Set _) =
      Set.range (fun c => l (tv 0 2 c)) ∧
    ((Exceptional.twistedE6Datum 2 f).rootGroup (-![1, 1, 0, 0]) : Set _) =
      Set.range (fun c => l (tv 2 0 c)) ∧
    ∀ j : Fin 4, (j = 2 ∨ j = 3) → ∃ m : SpecialLinearGroup (Fin 2) (GaloisField 2 f) ×
        SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)) →* Exceptional.twistedE6Group 2 f,
      Function.Injective m ∧
      ((Exceptional.twistedE6Datum 2 f).rootGroup (Pi.single j 1) : Set _) =
        Set.range (fun c => m (1, tv 0 1 c)) ∧
      ((Exceptional.twistedE6Datum 2 f).rootGroup (-Pi.single j 1) : Set _) =
        Set.range (fun c => m (1, tv 1 0 c)) ∧
      ∀ c, m (tv 0 1 c, 1) = l (tv 0 1 c) ∧ m (tv 1 0 c, 1) = l (tv 1 0 c)

end CaseM

end CFSG.Timmesfeld.ARS
