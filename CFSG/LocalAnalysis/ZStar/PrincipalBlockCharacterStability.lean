module

public import CFSG.LocalAnalysis.ZStar.AbstractStepV
public import CFSG.LocalAnalysis.ZStar.ComponentIntegralLattice
public import CFSG.LocalAnalysis.ZStar.IntegralTraceBridge

public section

namespace CFSG

namespace ZStar.PrincipalBlockCharacterStability

open ZStar.AbstractStepV
open ZStar.ComponentIntegralLattice
open ZStar.IntegralTraceBridge
open ZStar.PadicBlockField
open ZStar.TwoAdicWedderburn
open ZStar.WedderburnBlock

noncomputable section

universe u v

variable {G : Type u} [Group G] [Fintype G]

attribute [local instance 2000] CommRing.toCommSemiring

structure ComponentIntegralSpectralDatum
    (D : Decomposition G) (i : Fin D.blockCount) (w v : G) where
  P : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) ℤ_[2]
  Q : Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) ℤ_[2]
  sectorCount : ℕ
  E : Fin sectorCount →
    Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) ℤ_[2]
  c : Fin sectorCount → TwoAdicComplex
  P_involution : P * P = 1
  E_idempotent : ∀ s, E s * E s = E s
  E_commutes_P : ∀ s, E s * P = P * E s
  modular_exact : ∀ s,
    (Matrix.toLin' (P.map (PadicInt.toZModPow 1) - 1)).ker ⊓
        (Matrix.toLin' ((E s).map (PadicInt.toZModPow 1))).range ≤
      (Matrix.toLin' (P.map (PadicInt.toZModPow 1) - 1)).range
  spectral_decomposition :
    P.map padicIntToComplex * (Q.map padicIntToComplex - 1) =
      ∑ s, c s • ((E s).map padicIntToComplex * P.map padicIntToComplex)
  realizes_w :
    P.map padicIntToComplex =
      D.equiv (MonoidAlgebra.single w 1) i
  realizes_v :
    Q.map padicIntToComplex =
      D.equiv (MonoidAlgebra.single v 1) i

private theorem toZModPow_one_surjective :
    Function.Surjective (PadicInt.toZModPow 1 : ℤ_[2] →+* ZMod 2) :=
  ZMod.ringHom_surjective _

private theorem padicIntToComplex_injective :
    Function.Injective padicIntToComplex := by
  intro x y hxy
  apply PadicInt.ext
  apply (algebraMap ℚ_[2] TwoAdicComplex).injective
  exact hxy

private theorem componentCharacter_mul_eq_of_integralSpectralDatum
    (D : Decomposition G) (i : Fin D.blockCount) (w v : G)
    (d : ComponentIntegralSpectralDatum D i w v) :
    (componentRepresentation D i).character (w * v) =
      (componentRepresentation D i).character w := by
  have htrace :
      (d.P.map padicIntToComplex * d.Q.map padicIntToComplex).trace =
        (d.P.map padicIntToComplex).trace := by
    exact trace_mul_eq_trace_of_exact_projector_decomposition
      (R := ℤ_[2]) (k := ZMod 2) (K := TwoAdicComplex)
      (n := Fin (D.blockSize i)) (I := Fin d.sectorCount)
      (q := PadicInt.toZModPow 1) (hq := toZModPow_one_surjective)
      (j := padicIntToComplex) (hj := padicIntToComplex_injective)
      (P := d.P) (Q := d.Q) (E := d.E) (c := d.c)
      (hP := d.P_involution) (hE := d.E_idempotent)
      (hEP := d.E_commutes_P) (hexact := d.modular_exact)
      (hdecomp := d.spectral_decomposition)
  have hcomponent_mul :
      D.equiv (MonoidAlgebra.single (w * v) 1) i =
        D.equiv (MonoidAlgebra.single w 1) i *
          D.equiv (MonoidAlgebra.single v 1) i := by
    calc
      D.equiv (MonoidAlgebra.single (w * v) 1) i =
          D.equiv
            (MonoidAlgebra.single w 1 * MonoidAlgebra.single v 1) i := by
        simp
      _ = D.equiv (MonoidAlgebra.single w 1) i *
          D.equiv (MonoidAlgebra.single v 1) i := by
        rw [map_mul]
        rfl
  calc
    (componentRepresentation D i).character (w * v) =
        Matrix.trace (D.equiv (MonoidAlgebra.single (w * v) 1) i) :=
      componentCharacter_eq_matrixTrace D i (w * v)
    _ = Matrix.trace
        (D.equiv (MonoidAlgebra.single w 1) i *
          D.equiv (MonoidAlgebra.single v 1) i) := by
      rw [hcomponent_mul]
    _ = Matrix.trace
        (d.P.map padicIntToComplex * d.Q.map padicIntToComplex) := by
      rw [d.realizes_w, d.realizes_v]
    _ = Matrix.trace (d.P.map padicIntToComplex) := htrace
    _ = Matrix.trace (D.equiv (MonoidAlgebra.single w 1) i) := by
      rw [d.realizes_w]
    _ = (componentRepresentation D i).character w :=
      (componentCharacter_eq_matrixTrace D i w).symm

structure ComponentOrbitLatticeSpectralDatum
    (D : Decomposition G) (i : Fin D.blockCount) (w v : G)
    {k : Type v} [Field k] [CharP k 2] (q : O2 →+* k) where
  sectorCount : ℕ
  E : Fin sectorCount →
    Matrix (Fin (D.blockSize i)) (Fin (D.blockSize i)) O2
  c : Fin sectorCount → TwoAdicComplex
  E_idempotent : ∀ s, E s * E s = E s
  E_commutes_P : ∀ s,
    E s * componentIntegralMatrix D i w =
      componentIntegralMatrix D i w * E s
  modular_exact : ∀ s,
    (Matrix.toLin'
        ((componentIntegralMatrix D i w).map q - 1)).ker ⊓
        (Matrix.toLin' ((E s).map q)).range ≤
      (Matrix.toLin'
        ((componentIntegralMatrix D i w).map q - 1)).range
  spectral_decomposition :
    (componentIntegralMatrix D i w).map
          (algebraMap O2 TwoAdicComplex) *
        ((componentIntegralMatrix D i v).map
          (algebraMap O2 TwoAdicComplex) - 1) =
      ∑ s, c s •
        ((E s).map (algebraMap O2 TwoAdicComplex) *
          (componentIntegralMatrix D i w).map
            (algebraMap O2 TwoAdicComplex))

private theorem componentCharacter_eq_componentIntegralMatrix_trace
    (D : Decomposition G) (i : Fin D.blockCount) (g : G) :
    (componentRepresentation D i).character g =
      Matrix.trace ((componentIntegralMatrix D i g).map
        (algebraMap O2 TwoAdicComplex)) := by
  change LinearMap.trace TwoAdicComplex
      (Fin (D.blockSize i) → TwoAdicComplex) (componentRepresentation D i g) = _
  rw [componentIntegralMatrix_map_algebraMap]
  exact LinearMap.trace_eq_matrix_trace
    TwoAdicComplex (componentFieldBasis D i) (componentRepresentation D i g)

private theorem componentCharacter_mul_eq_of_orbitLatticeSpectralDatum
    (D : Decomposition G) (i : Fin D.blockCount) (w v : G)
    (hw2 : w * w = 1)
    {k : Type v} [Field k] [CharP k 2]
    (q : O2 →+* k) (hq : Function.Surjective q)
    (d : ComponentOrbitLatticeSpectralDatum D i w v q) :
    (componentRepresentation D i).character (w * v) =
      (componentRepresentation D i).character w := by
  have htrace :
      ((componentIntegralMatrix D i w).map
            (algebraMap O2 TwoAdicComplex) *
          (componentIntegralMatrix D i v).map
            (algebraMap O2 TwoAdicComplex)).trace =
        ((componentIntegralMatrix D i w).map
          (algebraMap O2 TwoAdicComplex)).trace := by
    exact trace_mul_eq_trace_of_exact_projector_decomposition
      (R := O2) (k := k) (K := TwoAdicComplex)
      (n := Fin (D.blockSize i)) (I := Fin d.sectorCount)
      (q := q) (hq := hq)
      (j := algebraMap O2 TwoAdicComplex)
      (hj := algebraMap_O2_TwoAdicComplex_injective)
      (P := componentIntegralMatrix D i w)
      (Q := componentIntegralMatrix D i v)
      (E := d.E) (c := d.c)
      (hP := componentIntegralMatrix_sq_of_sq_one D i w hw2)
      (hE := d.E_idempotent) (hEP := d.E_commutes_P)
      (hexact := d.modular_exact)
      (hdecomp := d.spectral_decomposition)
  calc
    (componentRepresentation D i).character (w * v) =
        Matrix.trace ((componentIntegralMatrix D i (w * v)).map
          (algebraMap O2 TwoAdicComplex)) :=
      componentCharacter_eq_componentIntegralMatrix_trace D i (w * v)
    _ = Matrix.trace
        (((componentIntegralMatrix D i w).map
            (algebraMap O2 TwoAdicComplex)) *
          ((componentIntegralMatrix D i v).map
            (algebraMap O2 TwoAdicComplex))) := by
      rw [componentIntegralMatrix_mul, Matrix.map_mul]
    _ = Matrix.trace ((componentIntegralMatrix D i w).map
          (algebraMap O2 TwoAdicComplex)) := htrace
    _ = (componentRepresentation D i).character w :=
      (componentCharacter_eq_componentIntegralMatrix_trace D i w).symm

def SelectedComponentSpectralDataAvailable (D : Decomposition G) : Prop :=
  ∀ (i : Fin D.blockCount),
    i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)) →
    ∀ (w : G), w ≠ 1 → w * w = 1 →
    ∀ (H : Subgroup G), H = Subgroup.centralizer ({w} : Set G) →
    ∀ (N : Subgroup H), N.Normal → Odd (Nat.card N) →
    ∀ (v : H), v ∈ N →
      Nonempty (ComponentIntegralSpectralDatum D i w (v : G))

@[expose] def SelectedComponentOrbitLatticeSpectralDataAvailable
    (D : Decomposition G) {k : Type v} [Field k] [CharP k 2]
    (q : O2 →+* k) : Prop :=
  ∀ (i : Fin D.blockCount),
    i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G)) →
    ∀ (w : G), w ≠ 1 → w * w = 1 →
    ∀ (H : Subgroup G), H = Subgroup.centralizer ({w} : Set G) →
    ∀ (N : Subgroup H), N.Normal → Odd (Nat.card N) →
    ∀ (v : H), v ∈ N →
      Nonempty (ComponentOrbitLatticeSpectralDatum D i w (v : G) q)

theorem selected_componentCharacter_centralizerOddCoreStable
    (D : Decomposition G)
    (hdata : SelectedComponentSpectralDataAvailable D)
    (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G))) :
    CentralizerOddCoreStable (componentRepresentation D i).character := by
  intro w hwne hw2 H hH N hNnormal hNodd v hv
  obtain ⟨d⟩ := hdata i hi w hwne hw2 H hH N hNnormal hNodd v hv
  exact componentCharacter_mul_eq_of_integralSpectralDatum
    D i w (v : G) d

theorem selected_componentCharacter_centralizerOddCoreStable_of_orbitLattice
    (D : Decomposition G)
    {k : Type v} [Field k] [CharP k 2]
    (q : O2 →+* k) (hq : Function.Surjective q)
    (hdata : SelectedComponentOrbitLatticeSpectralDataAvailable D q)
    (i : Fin D.blockCount)
    (hi : i ∈ selectedIndices D.equiv (principalBlockTwoAdic (G := G))) :
    CentralizerOddCoreStable (componentRepresentation D i).character := by
  intro w hwne hw2 H hH N hNnormal hNodd v hv
  obtain ⟨d⟩ := hdata i hi w hwne hw2 H hH N hNnormal hNodd v hv
  exact componentCharacter_mul_eq_of_orbitLatticeSpectralDatum
    D i w (v : G) hw2 q hq d

end

end ZStar.PrincipalBlockCharacterStability

end CFSG
