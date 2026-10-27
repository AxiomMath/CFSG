module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoRankOneDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeDefs
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace S2MathAs3_1615

open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalGroups.UnitaryFlag

noncomputable section

@[expose] def KD2NarrowAt (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a →
      lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∧
        ¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹

@[expose] def KD2Narrow : Prop :=
  ∀ lab, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ => KD2NarrowAt lab R I)

@[expose] def KD2NarrowOriginalAt (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a →
      (∃ m : ℕ, 1 ≤ m ∧ 3 = 3 * m ∧
        ((lab = (⟨.A, 2 * 3 - 1, m⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ m - 1) ∨
          (lab = (⟨.twA, 2 * 3 - 1, m⟩ : LargeEvenLabel) ∧ 3 ∣ 2 ^ m + 1))) ∧
        ¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹

theorem KD2Narrow_iff_originalSlice : KD2Narrow ↔ (∀ lab, LargeEvenInLambda2 lab → LargeEvenLabelAll
    lab (fun R _ I _ => KD2NarrowOriginalAt lab R I)) := by
  constructor
  · intro hN lab hlab
    have h' : LargeEvenLabelAll lab (fun R _ I _ => KD2NarrowAt lab R I) := hN lab hlab
    refine LargeEvenLabelAll.mono (fun R _ I _ hN => ?_) h'
    intro L' _ _ ψ hsurj hker hcomm e J a hsetup
    obtain ⟨hlab, hnon⟩ := hN L' ψ hsurj hker hcomm e J a hsetup
    refine ⟨⟨1, le_rfl, rfl, Or.inr ⟨?_, ?_⟩⟩, hnon⟩
    · exact hlab
    · norm_num
  · intro hS lab hlab
    have h' : LargeEvenLabelAll lab (fun R _ I _ => KD2NarrowOriginalAt lab R I) := hS lab hlab
    refine LargeEvenLabelAll.mono (fun R _ I _ hS => ?_) h'
    intro L' _ _ ψ hsurj hker hcomm e J a hsetup
    obtain ⟨⟨m, -, h3m, hshape⟩, hnon⟩ := hS L' ψ hsurj hker hcomm e J a hsetup
    have hm : m = 1 := by omega
    subst hm
    rw [show (2 * 3 - 1 : ℕ) = 5 from rfl] at hshape
    rcases hshape with ⟨hA, hdvd⟩ | ⟨htwA, hdvd⟩
    · exfalso
      norm_num at hdvd
    · exact ⟨htwA, hnon⟩

@[expose] def NonsplitUnitaryModel {R : Type} [Group R] {L' : Type} [Group L']
    (ψ : L' →* R) (e : MulAut L') (I : Set (MulAut R)) : Prop :=
  ∃ (k : Type) (_ : Field k) (_ : Finite k) (h : UnitaryFieldData 2 1 k)
    (theta : R ≃* LargeEvenProj (unitarySU 2 1 k 6))
    (alpha : MulAut (LargeEvenProj (unitarySU 2 1 k 6))),
    (∀ l : L', alpha (theta (ψ l)) = theta (ψ (e l))) ∧
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.FieldType h alpha ∧
    (∀ φ ∈ I, ∃ beta ∈ InndiagSU.inndiagU (d := 6) h (by norm_num),
      ∀ r : R, beta (theta r) = theta (φ r))

@[expose] def StrongKD2At (lab : LargeEvenLabel) (R : Type) [Group R]
    (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ (e : MulAut L') (J : Subgroup L') (a : MulAut L'),
      GGRankOneSetup I ψ 3 e J 3 a →
      (lab = (⟨.twA, 5, 1⟩ : LargeEvenLabel) ∧
        ¬ ∃ r : R, ∀ l : L', ψ (e l) = r * ψ l * r⁻¹) ∧
      NonsplitUnitaryModel ψ e I

@[expose] def StrongKD2 : Prop :=
  ∀ lab, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (fun R _ I _ => StrongKD2At lab R I)

theorem KD2Narrow_of_strong (h : StrongKD2) : KD2Narrow := by
  intro lab hlab
  have h' : LargeEvenLabelAll lab (fun R _ I _ => StrongKD2At lab R I) := h lab hlab
  exact LargeEvenLabelAll.mono
    (fun R _ I _ hs => fun L' _ _ ψ hsurj hker hcomm e J a hsetup =>
      (hs L' ψ hsurj hker hcomm e J a hsetup).1)
    h'

end

end S2MathAs3_1615

end
