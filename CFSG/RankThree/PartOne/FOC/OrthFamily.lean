module

public import CFSG.RankThree.PartOne.FOC.OrthInner
public import CFSG.RankThree.PartOne.FOC.OrthOuter
public import CFSG.RankThree.PartOne.FOC.LieAssemble
import CFSG.RankThree.PartOne.S11c.Sec66ClassCommon
import CFSG.RankThree.PartOne.KF.F128Cls

public section

namespace CFSG.RankThree.PartOne.FOC

open Module CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff LocalRankLeTwo)
open CFSG.RankThree.PartOne.KCOrthogonalD4 (bridgeEquiv)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

section Intrinsic

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem innerComp_projOrth [Finite (ProjOrthDerived Q)]
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ U : Submodule K V, finrank K U = 3 ∧ ∀ u ∈ U, Q u = 0) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) : InnerComp p (ProjOrthDerived Q) := by
  intro hrank b y hbp hyp hby E hE
  have hloc : localRank p (ProjOrthDerived Q) ≤ 3 := by
    by_contra h
    exact false_of_three_le_localRank hp hrank (by omega)
  have hmult := orthogonalLiftMultiplicity_of_cover
    (⊤ : Subgroup (ProjOrthDerived Q)) hQ hT hp (by omega) hpl hloc (Subgroup.subtype _)
    (fun t => ⟨⟨t, Subgroup.mem_top t⟩, rfl⟩)
    (by
      rw [(MonoidHom.ker_eq_bot_iff _).mpr (Subgroup.subtype_injective _)]
      exact bot_le) (MulEquiv.refl _)
  exact mem_sup_centralizer_of_component_orth hQ hT hp (by omega) hpl hmult hbp hyp hby hE

end Intrinsic

section Tags

theorem fieldInnerT_orth_odd {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hs : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hmodel : LieModel T .POmegaOdd n ℓ f) : FieldInnerT p T := by
  have hC : StatedClassicalModel T .POmegaOdd n ℓ f := (lieModel_classical_iff (by decide)).mp hmodel
  have hC' := hC
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC'
  obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_odd hC K hK e
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have hn3 : 3 ≤ n := hC.1.2.2.1
  have hd : 0 < 2 * n + 1 := by omega
  let ξ := coordinateOddWitnessEquiv K e
  have : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) := Finite.of_equiv T ξ.toEquiv
  have : Finite (ProjOrthDerived (coordinateQuadOdd n K)) :=
    Finite.of_equiv _ (bridgeEquiv (coordinateQuadOdd n K) hd).toEquiv
  have hsP : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    ξ.symm.isSimpleGroup
  have hnabP : ∃ a b : matrixProjectiveDerived (coordinateQuadOdd n K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨ξ a, ξ b, fun h => hab (ξ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hin : InnerComp p (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    InnerComp.of_mulEquiv (bridgeEquiv (coordinateQuadOdd n K) hd) hp
      (innerComp_projOrth hnd hS3 hp hp5 hpl)
  have hout : OuterComp p (matrixProjectiveDerived (coordinateQuadOdd n K)) :=
    outerComp_matrix_odd hC hp (by omega) hpℓ K hK e
  exact FieldInnerT.of_mulEquiv ξ hp
    (fieldInnerT_of_comp (center_eq_bot_of_nonab hsP hnabP) hin hout)

theorem fieldInnerT_orth_plus {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hs : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hmodel : LieModel T .POmegaPlus n ℓ f) : FieldInnerT p T := by
  have hC : StatedClassicalModel T .POmegaPlus n ℓ f :=
    (lieModel_classical_iff (by decide)).mp hmodel
  have hC' := hC
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hC'
  obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_plus hC K hK e
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have hn4 : 4 ≤ n := hC.1.2.2
  have hd : 0 < 2 * n := by omega
  let ξ := coordinatePlusWitnessEquiv K e
  have : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) := Finite.of_equiv T ξ.toEquiv
  have : Finite (ProjOrthDerived (coordinateQuadPlus n K)) :=
    Finite.of_equiv _ (bridgeEquiv (coordinateQuadPlus n K) hd).toEquiv
  have hsP : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    ξ.symm.isSimpleGroup
  have hnabP : ∃ a b : matrixProjectiveDerived (coordinateQuadPlus n K), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨ξ a, ξ b, fun h => hab (ξ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hin : InnerComp p (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    InnerComp.of_mulEquiv (bridgeEquiv (coordinateQuadPlus n K) hd) hp
      (innerComp_projOrth hnd hS3 hp hp5 hpl)
  have hout : OuterComp p (matrixProjectiveDerived (coordinateQuadPlus n K)) :=
    outerComp_matrix_plus hC hp (by omega) hpℓ K hK e
  exact FieldInnerT.of_mulEquiv ξ hp
    (fieldInnerT_of_comp (center_eq_bot_of_nonab hsP hnabP) hin hout)

theorem fieldInnerT_orth_minus {T : Type} [Group T] [Finite T] {n f ℓ p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hpℓ : p ≠ ℓ) (hs : IsSimpleGroup T) (hnab : ∃ a b : T, a * b ≠ b * a)
    (hmodel : LieModel T .POmegaMinus n ℓ f) : FieldInnerT p T := by
  have hC : StatedClassicalModel T .POmegaMinus n ℓ f :=
    (lieModel_classical_iff (by decide)).mp hmodel
  have hC' := hC
  obtain ⟨-, K, _, _, hK, b, c', hirr, ⟨e⟩⟩ := hC'
  have hn4 : 4 ≤ n := hC.1.2.2
  have hn : 1 ≤ n := by omega
  obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_minus hC K hK b c' hirr e
  have hpl : p ≠ ringChar K := by rw [hchar]; exact hpℓ
  have hd : 0 < 2 * n := by omega
  let ξ := coordinateMinusWitnessEquiv K hn b c' e
  have : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn b c')) :=
    Finite.of_equiv T ξ.toEquiv
  have : Finite (ProjOrthDerived (coordinateQuadMinus n K hn b c')) :=
    Finite.of_equiv _ (bridgeEquiv (coordinateQuadMinus n K hn b c') hd).toEquiv
  have hsP : IsSimpleGroup (matrixProjectiveDerived (coordinateQuadMinus n K hn b c')) :=
    ξ.symm.isSimpleGroup
  have hnabP : ∃ a b' : matrixProjectiveDerived (coordinateQuadMinus n K hn b c'),
      a * b' ≠ b' * a := by
    obtain ⟨a, b', hab⟩ := hnab
    exact ⟨ξ a, ξ b', fun h => hab (ξ.injective (by rw [map_mul, map_mul]; exact h))⟩
  have hin : InnerComp p (matrixProjectiveDerived (coordinateQuadMinus n K hn b c')) :=
    InnerComp.of_mulEquiv (bridgeEquiv (coordinateQuadMinus n K hn b c') hd) hp
      (innerComp_projOrth hnd hS3 hp hp5 hpl)
  have hout : OuterComp p (matrixProjectiveDerived (coordinateQuadMinus n K hn b c')) :=
    outerComp_matrix_minus hC hn hp (by omega) hpℓ K hK b c' hirr e
  exact FieldInnerT.of_mulEquiv ξ hp
    (fieldInnerT_of_comp (center_eq_bot_of_nonab hsP hnabP) hin hout)

theorem fieldInnerLie_POmegaOdd (hdefI : DefInnerComponent) (hdefO : DefOuterComponent) (ℓ : ℕ) :
    FieldInnerLie .POmegaOdd ℓ :=
  fieldInnerLie_of_nondef hdefI hdefO fun _ _ _ _ _ _ hp hp5 hpℓ hs hnab _ hmodel =>
    fieldInnerT_orth_odd hp hp5 hpℓ hs hnab hmodel

theorem fieldInnerLie_POmegaPlus (hdefI : DefInnerComponent) (hdefO : DefOuterComponent) (ℓ : ℕ) :
    FieldInnerLie .POmegaPlus ℓ :=
  fieldInnerLie_of_nondef hdefI hdefO fun _ _ _ _ _ _ hp hp5 hpℓ hs hnab _ hmodel =>
    fieldInnerT_orth_plus hp hp5 hpℓ hs hnab hmodel

theorem fieldInnerLie_POmegaMinus (hdefI : DefInnerComponent) (hdefO : DefOuterComponent)
    (ℓ : ℕ) : FieldInnerLie .POmegaMinus ℓ :=
  fieldInnerLie_of_nondef hdefI hdefO fun _ _ _ _ _ _ hp hp5 hpℓ hs hnab _ hmodel =>
    fieldInnerT_orth_minus hp hp5 hpℓ hs hnab hmodel

end Tags

end CFSG.RankThree.PartOne.FOC
