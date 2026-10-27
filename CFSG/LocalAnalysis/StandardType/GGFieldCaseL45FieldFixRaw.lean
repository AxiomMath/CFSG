module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45FieldFixTorsion (p : ℕ) (R : Type) [Group R] (I F : Set (MulAut R)) : Prop :=
  ∀ (K : Type) [Group K] [Finite K] (θ : K ⧸ Subgroup.center K ≃* R), commutator K = ⊤ →
    ∀ ψ : MulAut K, ψ ^ p = 1 →
    (∃ f ∈ F, ∃ u ∈ I, orderOf f = p ∧
      LargeEvenInduces θ (fun k k' => k' = ψ k) (u * f * u⁻¹)) →
    ∀ Q : Subgroup K, IsComponentOf Q (ggAutFixedSubgroup ψ) →
      LargeEvenMarking Q fun lab' _ _ _ _ _ => GGL45TorsionTag lab'

theorem ggL45FieldFixKGRaw_of_torsion {p : ℕ} {lab : LargeEvenLabel} (hA : ¬ GGLabelA2 lab)
    {R : Type} [Group R] {I F : Set (MulAut R)} (h : GGL45FieldFixTorsion p R I F) :
    GGL45FieldFixKGRaw p lab R I F :=
  ⟨fun hA2 => absurd hA2 hA, fun K _ _ θ hK ψ hψ hind Q hQ =>
    ⟨fun _ => h K θ hK ψ hψ hind Q hQ, fun hA2 => absurd hA2 hA⟩⟩

theorem ggL45FieldFixKGRaw_of_vac {p : ℕ} {lab : LargeEvenLabel} (hA : GGLabelA2 lab → p ≠ 3)
    (hT : ¬ GGL45TorsionTag lab) {R : Type} [Group R] (I F : Set (MulAut R)) :
    GGL45FieldFixKGRaw p lab R I F :=
  ⟨fun hA2 hp3 => absurd hp3 (hA hA2), fun K _ _ θ hK ψ hψ hind Q hQ =>
    ⟨fun ht => absurd ht hT, fun hA2 hp3 => absurd hp3 (hA hA2)⟩⟩

theorem ggL45FieldFixLabelAll_of_vac {p : ℕ} {lab : LargeEvenLabel}
    (hA : GGLabelA2 lab → p ≠ 3) (hT : ¬ GGL45TorsionTag lab) :
    LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab) := fun Q hQ =>
  largeEvenRawDatum_mono (fun _ _ I F hq => ⟨hq, ggL45FieldFixKGRaw_of_vac hA hT I F⟩) hQ

theorem ggL45FieldFixLabelAll_of_torsion {p : ℕ} {lab : LargeEvenLabel} (hA : ¬ GGLabelA2 lab)
    (h : LargeEvenLabelAll lab fun R _ I F => GGL45FieldFixTorsion p R I F) :
    LargeEvenLabelAll lab (GGL45FieldFixKGRaw p lab) :=
  h.mono fun _ _ _ _ hT => ggL45FieldFixKGRaw_of_torsion hA hT

end CFSG.StandardType
