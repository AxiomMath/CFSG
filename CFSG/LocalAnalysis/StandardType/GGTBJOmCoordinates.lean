module

public import CFSG.LocalAnalysis.StandardType.GGTBJOmPlaneIsometries
public import CFSG.LocalAnalysis.StandardType.GGTBJOmBlockZ
public import CFSG.LocalAnalysis.StandardType.GGTBJOmTauOm
public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations
public import CFSG.Mathlib.LinearAlgebra.QuadraticForm.OrthogonalSum
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Projection
public import CFSG.LieType.SeitzGeneration.OrthNonsplitDims
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

open Module Multiplicative QuadraticMap Polynomial
open CFSG.RankThree.PartOne.KCOrthogonal

namespace CFSG.StandardType

namespace OrthTorus

open SpCoord
open CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
open CFSG.GroupTheory.WeirSylow
open CFSG.RankThree.Classical2 (orthDerived)

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p r : ℕ} {A : Subgroup (V ≃ₗ[K] V)}

@[expose] def TBJOmData.originalActive (Δ : TBJOmData Q p A r) : Submodule K V :=
  ⨆ i, Δ.F.U i

@[expose] def TBJOmData.originalAnchor (Δ : TBJOmData Q p A r) : Submodule K V :=
  polarPerp Q (Δ.originalActive)

@[expose] noncomputable def TBJOmData.originalSumMap (Δ : TBJOmData Q p A r) :
    (Π₀ i : Fin r, Δ.F.U i) →ₗ[K] V :=
  DFinsupp.lsum ℕ fun i => (Δ.F.U i).subtype

theorem TBJOmData.originalSumMap_injective (Δ : TBJOmData Q p A r) :
    Function.Injective (Δ.originalSumMap) :=
  iSupIndep.dfinsupp_lsum_injective Δ.F.iSupIndep_pieces

theorem TBJOmData.originalSumMap_range (Δ : TBJOmData Q p A r) :
    LinearMap.range Δ.originalSumMap = Δ.originalActive := by
  rw [TBJOmData.originalSumMap, TBJOmData.originalActive,
    Submodule.iSup_eq_range_dfinsupp_lsum]

noncomputable def TBJOmData.originalActiveEquiv [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r) :
    (Fin r → Δ.F.U o) ≃ₗ[K] Δ.originalActive :=
  (LinearEquiv.piCongrRight fun i => (Δ.planeIsometry hQ o i).toLinearEquiv).trans
    ((DFinsupp.linearEquivFunOnFintype (R := K) (M := fun i => Δ.F.U i)).symm.trans
      ((LinearEquiv.ofInjective Δ.originalSumMap Δ.originalSumMap_injective).trans
        (LinearEquiv.ofEq (LinearMap.range Δ.originalSumMap) Δ.originalActive
          Δ.originalSumMap_range)))

theorem TBJOmData.originalActiveEquiv_single [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (i : Fin r) (e : Δ.F.U o) :
    (Δ.originalActiveEquiv hQ o (Pi.single i e) : V) =
      (((Δ.planeIsometry hQ o i) e : Δ.F.U i) : V) := by
  have hφ : (LinearEquiv.piCongrRight
      fun i => (Δ.planeIsometry hQ o i).toLinearEquiv) (Pi.single i e) =
      Pi.single i (Δ.planeIsometry hQ o i e) := by
    funext k
    rw [LinearEquiv.piCongrRight_apply]
    by_cases hki : k = i
    · subst hki
      simp
    · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hki]
      exact map_zero (Δ.planeIsometry hQ o k).toLinearEquiv
  rw [TBJOmData.originalActiveEquiv]
  change (DFinsupp.lsum ℕ (fun i => (Δ.F.U i).subtype)
      (DFinsupp.equivFunOnFintype.symm
        ((LinearEquiv.piCongrRight fun i => (Δ.planeIsometry hQ o i).toLinearEquiv)
          (Pi.single i e))) : V) = _
  rw [hφ, DFinsupp.equivFunOnFintype_symm_single]
  exact DFinsupp.lsum_single ℕ (fun i => (Δ.F.U i).subtype) i
    (Δ.planeIsometry hQ o i e)

theorem TBJOmData.originalActiveEquiv_apply [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (x : Fin r → Δ.F.U o) :
    (Δ.originalActiveEquiv hQ o x : V) =
      ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
  have hsum : Δ.originalActiveEquiv hQ o x =
      ∑ i, Δ.originalActiveEquiv hQ o (Pi.single i (x i)) := by
    calc
      Δ.originalActiveEquiv hQ o x
          = Δ.originalActiveEquiv hQ o (∑ i, Pi.single i (x i)) := by
              rw [Finset.univ_sum_single]
      _ = ∑ i, Δ.originalActiveEquiv hQ o (Pi.single i (x i)) :=
              map_sum (Δ.originalActiveEquiv hQ o).toLinearMap
                (fun i => Pi.single i (x i)) Finset.univ
  calc
    (Δ.originalActiveEquiv hQ o x : V)
        = ((∑ i, Δ.originalActiveEquiv hQ o (Pi.single i (x i)) :
            Δ.originalActive) : V) :=
            congrArg (Submodule.subtype Δ.originalActive) hsum
    _ = ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
            have h := map_sum (Submodule.subtype Δ.originalActive)
              (fun i => Δ.originalActiveEquiv hQ o (Pi.single i (x i))) Finset.univ
            simpa [Δ.originalActiveEquiv_single hQ o] using h

noncomputable def TBJOmData.originalSumEquiv [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) :
    (Δ.originalAnchor × (Fin r → Δ.F.U o)) ≃ₗ[K] V :=
  ((LinearEquiv.refl K Δ.originalAnchor).prodCongr (Δ.originalActiveEquiv hQ o)).trans
    (Submodule.prodEquivOfIsCompl Δ.originalAnchor Δ.originalActive hWS)

noncomputable def TBJOmData.originalCoordinates [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) :
    V ≃ₗ[K] (Δ.originalAnchor × (Fin r → Δ.F.U o)) :=
  (Δ.originalSumEquiv hQ o hWS).symm

theorem TBJOmData.originalSumEquiv_apply [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (w : Δ.originalAnchor) (x : Fin r → Δ.F.U o) :
    (Δ.originalSumEquiv hQ o hWS (w, x) : V) =
      (w : V) + ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
  rw [TBJOmData.originalSumEquiv]
  simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    Submodule.coe_prodEquivOfIsCompl', LinearEquiv.refl_apply]
  rw [TBJOmData.originalActiveEquiv_apply]

theorem TBJOmData.originalCoordinates_symm_apply [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (w : Δ.originalAnchor) (x : Fin r → Δ.F.U o) :
    (Δ.originalCoordinates hQ o hWS).symm (w, x) =
      (w : V) + ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) :=
  Δ.originalSumEquiv_apply hQ o hWS w x

theorem TBJOmData.originalCoordinates_symm_anchor [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) (w : Δ.originalAnchor) :
    (Δ.originalCoordinates hQ o hWS).symm (w, 0) = (w : V) := by
  rw [TBJOmData.originalCoordinates_symm_apply]
  simp

theorem TBJOmData.originalCoordinates_symm_single [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (i : Fin r) (e : Δ.F.U o) :
    (Δ.originalCoordinates hQ o hWS).symm (0, Pi.single i e) =
      (((Δ.planeIsometry hQ o i) e : Δ.F.U i) : V) := by
  rw [TBJOmData.originalCoordinates_symm_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hki
    simp [Pi.single_eq_of_ne hki]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem TBJOmData.originalCoordinates_quadratic [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive)
    (w : Δ.originalAnchor) (x : Fin r → Δ.F.U o) :
    Q ((Δ.originalCoordinates hQ o hWS).symm (w, x)) =
      (Q.comp Δ.originalAnchor.subtype) w +
        ∑ i, (Q.comp (Δ.F.U o).subtype) (x i) := by
  rw [TBJOmData.originalCoordinates_symm_apply]
  have horth : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      ∀ k ∈ (Finset.univ : Finset (Fin r)), i ≠ k →
        polar Q (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)
          (((Δ.planeIsometry hQ o k) (x k) : Δ.F.U k) : V) = 0 := by
    intro i _ k _ hik
    exact Δ.F.orth i k hik _ ((Δ.planeIsometry hQ o i) (x i)).2
      _ ((Δ.planeIsometry hQ o k) (x k)).2
  have hz : ∀ i ∈ (Finset.univ : Finset (Fin r)),
      polar Q (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) (w : V) = 0 := by
    intro i _
    have hw : (w : V) ∈ polarPerp Q (⨆ i, Δ.F.U i) := by
      simpa [TBJOmData.originalAnchor, TBJOmData.originalActive] using w.2
    exact mem_polarPerp_iff.mp hw _
      (Submodule.mem_iSup_of_mem i ((Δ.planeIsometry hQ o i) (x i)).2)
  have hmain := CFSG.QuadraticMap.map_sum_add_of_polar_eq_zero Q Finset.univ
    (fun i => (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)) (w : V) horth hz
  calc
    Q ((w : V) + ∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V))
        = Q ((∑ i, (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)) + (w : V)) := by
            rw [add_comm]
    _ = (∑ i, Q (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V)) + Q (w : V) := hmain
    _ = Q (w : V) + ∑ i, Q (((Δ.planeIsometry hQ o i) (x i) : Δ.F.U i) : V) := by
            rw [add_comm]
    _ = (Q.comp Δ.originalAnchor.subtype) w +
        ∑ i, (Q.comp (Δ.F.U o).subtype) (x i) := by
            congr 1
            refine Finset.sum_congr rfl fun i _ => ?_
            exact (Δ.planeIsometry hQ o i).map_app (x i)

theorem TBJOmData.originalCoordinates_quadratic_apply [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) (v : V) :
    Q v = (Q.comp Δ.originalAnchor.subtype) ((Δ.originalCoordinates hQ o hWS) v).1 +
      ∑ i, (Q.comp (Δ.F.U o).subtype) (((Δ.originalCoordinates hQ o hWS) v).2 i) := by
  have h := Δ.originalCoordinates_quadratic hQ o hWS
    ((Δ.originalCoordinates hQ o hWS) v).1 ((Δ.originalCoordinates hQ o hWS) v).2
  simpa using h

theorem TBJOmData.coordAnchor_originalCoordinates [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) :
    coordAnchor (Δ.originalCoordinates hQ o hWS) = Δ.originalAnchor := by
  ext v
  rw [mem_coordAnchor]
  constructor
  · rintro ⟨w, rfl⟩
    rw [TBJOmData.originalCoordinates_symm_anchor]
    exact w.2
  · intro hv
    exact ⟨⟨v, hv⟩, by rw [TBJOmData.originalCoordinates_symm_anchor]⟩

theorem TBJOmData.coordPlane_originalCoordinates [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) (i : Fin r) :
    coordPlane (Δ.originalCoordinates hQ o hWS) i = Δ.F.U i := by
  ext v
  rw [mem_coordPlane]
  constructor
  · rintro ⟨e, rfl⟩
    rw [TBJOmData.originalCoordinates_symm_single]
    exact ((Δ.planeIsometry hQ o i) e).2
  · intro hv
    refine ⟨(Δ.planeIsometry hQ o i).symm ⟨v, hv⟩, ?_⟩
    rw [TBJOmData.originalCoordinates_symm_single]
    exact congrArg Subtype.val
      ((Δ.planeIsometry hQ o i).apply_symm_apply ⟨v, hv⟩)

theorem TBJOmData.coordSupport_originalCoordinates [Fact p.Prime]
    (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate) (o : Fin r)
    (hWS : IsCompl Δ.originalAnchor Δ.originalActive) (T : Finset (Fin r)) :
    coordSupport (Δ.originalCoordinates hQ o hWS) T =
      Δ.originalAnchor ⊔ T.sup Δ.F.U := by
  rw [coordSupport, TBJOmData.coordAnchor_originalCoordinates]
  congr 1
  exact Finset.sup_congr rfl fun i _ =>
    Δ.coordPlane_originalCoordinates hQ o hWS i

theorem TBJOmData.originalPlaneForm_nondegenerate (Δ : TBJOmData Q p A r) (o : Fin r) :
    (polarBilin (Q.comp (Δ.F.U o).subtype)).Nondegenerate :=
  CFSG.LieType.SeitzGeneration.nondegenerate_comp_subtype
    (fun u hu h => Δ.F.nondeg o u hu fun v hv => by
      rw [polar_comm]
      exact h v hv)

theorem TBJOmData.originalMinusAnchor_isCompl [Fact p.Prime]
    (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate)
    (hA : A ≤ orthDerived Q) (hr : 1 ≤ r) (hdim : finrank K V = 2 * (r + 1))
    (hminus : ¬ IsPlusType Q)
    (hrow : p ∣ Nat.card K - 1 ∨ Odd r ∧ p ∣ Nat.card K + 1) :
    IsCompl Δ.originalAnchor Δ.originalActive := by
  have h := (Δ.inactive_plane_of_minus hp2 hQ hA hr hdim hminus hrow).2.2.2.1
  simpa [TBJOmData.originalAnchor, TBJOmData.originalActive] using h

theorem TBJOmData.originalMinusAnchor_regular [Fact p.Prime]
    (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r) (hQ : (polarBilin Q).Nondegenerate)
    (hA : A ≤ orthDerived Q) (hr : 1 ≤ r) (hdim : finrank K V = 2 * (r + 1))
    (hminus : ¬ IsPlusType Q)
    (hrow : p ∣ Nat.card K - 1 ∨ Odd r ∧ p ∣ Nat.card K + 1) :
    (polarBilin (Q.comp Δ.originalAnchor.subtype)).Nondegenerate := by
  have h := (Δ.inactive_plane_of_minus hp2 hQ hA hr hdim hminus hrow).2.2.1
  change (polarBilin (Q.comp (polarPerp Q (⨆ i, Δ.F.U i)).subtype)).Nondegenerate at h
  exact h

end OrthTorus

end CFSG.StandardType

end
