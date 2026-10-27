module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.LineTorus
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
import CFSG.RankThree.GF2n.Stroth80.Sec715OrthTorus
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.ClassicalGroups.Orthogonal.DiagonalTorusRankOddMinus
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
import CFSG.LieType.Universal.IrreducibleQuadratic
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open Matrix
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K]

private theorem mulSingle_pow_card_sub_one [Finite K] {ι : Type} [DecidableEq ι]
    (j₀ : ι) (u : Kˣ) :
    ∀ j : ι, (Pi.mulSingle j₀ u : ι → Kˣ) j ^ (Nat.card K - 1) = 1 := by
  have hu : u ^ (Nat.card K - 1) = 1 := by
    rw [← Nat.card_units (α := K)]
    exact pow_card_eq_one'
  intro j
  by_cases hj : j = j₀
  · subst hj
    simpa using hu
  · simp [Pi.mulSingle, hj]

theorem lineTorus_omegaPlus [Finite K] [CharP K 2] (m : ℕ) [NeZero m] :
    LineTorus (StatedOmega (StatedQuadPlus m K)) (Pi.single (Sum.inl 0) 1) := by
  intro c
  have hodd : Odd (Nat.card K - 1) :=
    CFSG.RankThree.GF2n.Stroth80.Sec715Torus.odd_card_sub_one_of_charTwo
  let t : Fin m → Kˣ := Pi.mulSingle 0 c
  let d : Fin m ⊕ Fin m → Kˣ := torusEntPlus m K t
  have ht : ∀ j, t j ^ (Nat.card K - 1) = 1 := by
    simpa [t] using mulSingle_pow_card_sub_one (j₀ := (0 : Fin m)) c
  have hd : ∀ j, d j ^ (Nat.card K - 1) = 1 := by
    intro j
    rcases j with j | j
    · simpa [d, torusEntPlus] using ht j
    · simp only [d, torusEntPlus, MonoidHom.coe_mk, OneHom.coe_mk, Sum.elim_inr]
      rw [inv_pow, ht j, inv_one]
  have hσ : ∀ v, StatedQuadPlus m K (v ∘ ⇑(Equiv.sumComm (Fin m) (Fin m))) =
      StatedQuadPlus m K v := by
    intro v
    change ∑ i, v (Sum.inr i) * v (Sum.inl i) = ∑ i, v (Sum.inl i) * v (Sum.inr i)
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hdQ : ∀ v, StatedQuadPlus m K (fun j => (d j : K) * v j) = StatedQuadPlus m K v := by
    intro v
    change ∑ i, ((t i : K) * v (Sum.inl i)) * ((((t i)⁻¹ : Kˣ) : K) * v (Sum.inr i)) =
      ∑ i, v (Sum.inl i) * v (Sum.inr i)
    refine Finset.sum_congr rfl fun i _ => ?_
    linear_combination (v (Sum.inl i) * v (Sum.inr i)) * (t i).mul_inv
  have hdσ : ∀ j, d (Equiv.sumComm (Fin m) (Fin m) j) = (d j)⁻¹ := by
    intro j
    rcases j with j | j <;> simp [d, torusEntPlus]
  have hmem : (diagGL d : GL (Fin m ⊕ Fin m) K) ∈ StatedOmega (StatedQuadPlus m K) :=
    diagGL_mem_statedOmega (Q := StatedQuadPlus m K)
      (σ := Equiv.sumComm (Fin m) (Fin m)) hσ hodd hd hdQ hdσ
  refine ⟨(diagGL d : GL (Fin m ⊕ Fin m) K), hmem, ?_⟩
  have hdc : (d (Sum.inl (0 : Fin m)) : K) = (c : K) := by
    rw [show d (Sum.inl (0 : Fin m)) = t 0 from rfl,
      show t (0 : Fin m) = c by simp [t]]
  rw [coe_diagGL, Matrix.diagonal_mulVec_single, hdc, mul_one, ← Pi.single_smul,
    smul_eq_mul, mul_one]

theorem lineTorus_omegaMinus [Finite K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m) (b c : K) :
    LineTorus (StatedOmega (StatedQuadMinus m K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) := by
  intro c'
  have hodd : Odd (Nat.card K - 1) :=
    CFSG.RankThree.GF2n.Stroth80.Sec715Torus.odd_card_sub_one_of_charTwo
  let d : Fin (m - 1) → Kˣ := Pi.mulSingle (⟨0, by omega⟩ : Fin (m - 1)) c'
  have hd : ∀ j, d j ^ (Nat.card K - 1) = 1 := by
    simpa [d] using
      mulSingle_pow_card_sub_one (j₀ := (⟨0, by omega⟩ : Fin (m - 1))) c'
  let γ : StatedOmega (StatedQuadMinus m K b c) :=
    minusDiagGL (b := b) (c := c) (n := m) hodd d hd
  refine ⟨(γ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K), γ.2, ?_⟩
  have hγ : ((γ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) : Matrix _ _ K) =
      diagonal (fun j => ((torusEntMinus (m - 1) K d j : Kˣ) : K)) := by
    rw [show (γ : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K) =
      diagGL (torusEntMinus (m - 1) K d) from rfl, coe_diagGL]
  have hdj : ((torusEntMinus (m - 1) K d (Sum.inl (⟨0, by omega⟩ : Fin (m - 1))) : Kˣ) : K) =
      (c' : K) := by
    rw [show torusEntMinus (m - 1) K d (Sum.inl (⟨0, by omega⟩ : Fin (m - 1))) = c' by
      simp [d, torusEntMinus]]
  rw [hγ, Matrix.diagonal_mulVec_single, hdj, mul_one, ← Pi.single_smul,
    smul_eq_mul, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
