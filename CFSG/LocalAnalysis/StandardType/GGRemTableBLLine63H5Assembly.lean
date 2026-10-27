module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Setup
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Marking
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5StepOneMarking

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly
  CFSG.StandardType

theorem prime_eq_three_of_innerDiagOnLab {G : Type} [Group G] {p : ℕ} {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLab GGUnitDvd63Label p Bs L) : p = 3 := by
  have h : LargeEvenMarking L fun _ _ _ _ _ _ => p = 3 :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1.2.2) hM
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hp3⟩ := largeEvenRawDatum_exists hraw
  exact hp3

@[expose] def Line63StepOneQ2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → Nat.card Bs < 3 ^ 5 →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 → commutator L = ⊤ →
    ∀ θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (unitarySU 2 1 K 6),
      Bs ≤ Subgroup.normalizer (L : Set G) →
      (∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 1 K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ 1)),
        LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) →
      ∀ z ∈ L, (∀ l ∈ L, z * l = l * z) → z ^ 3 = 1 → z = 1

end CFSG.StandardType.Line63.H5

end
