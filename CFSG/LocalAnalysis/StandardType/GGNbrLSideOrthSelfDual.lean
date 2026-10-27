module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockModels
public import CFSG.Blueprint.Catalog
public import CFSG.Open.StatedDefs
import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.SympOrthOrthIdent
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniData
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU
import CFSG.LieType.SemisimpleCentralizers.HeldTwoDimUnitaryBlock
import CFSG.LocalAnalysis.StandardType.GGNbrLSideUniType
import CFSG.LieType.Steinberg.CentralExt.UnitaryField
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.Assembly.GL83StatedBridge
import CFSG.Assembly.OpenBridges
import CFSG.GroupTheory.HallHigmanPiCore
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnUniPieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types
import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors
import CFSG.RankThree.PartTwo.Sec12.Notation
import CFSG.RankThree.PartTwo.Sec4.Item47Diag
import CFSG.RankThree.PartTwo.Sec4.Item47Statement
import CFSG.RankThree.PartTwo.Sec4.Item47Witness
import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.StandardType

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.Open
open CFSG.LieType.SemisimpleCentralizers.Held (heldSU)

theorem ggNbrLSideOrth_selfDual_type {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {x : V ≃ₗ[K] V}
    (hx : OddOrderIsometry Q 3 x) (hchar : ringChar K = 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    ∃ (t : StatedLieTag) (m k : ℕ), ((t = .PSU ∧ 3 ≤ m) ∨ (t = .PSL ∧ m = 2)) ∧
      CFSG.Blueprint.LieModel (↥(specialBlock Q x h) ⧸ Subgroup.center ↥(specialBlock Q x h))
        t m 2 k := by
  classical
  haveI : CharP K 2 := by
    rw [← hchar]
    exact ringChar.charP K
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hf' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hf
  have hf1 : 1 ≤ (f : ℕ) := f.pos
  have hm2' : 2 ≤ primaryMultiplicity x.toLinearMap h := by
    by_contra hlt
    have hpos : 0 < primaryMultiplicity x.toLinearMap h := hx.primaryMultiplicity_pos hh
    have h1 : primaryMultiplicity x.toLinearMap h = 1 := by omega
    exact ne_bot_of_isQuasisimple hq (hx.specialBlock_eq_bot_of_finrank_eq_one hh h1)
  set m : ℕ := primaryMultiplicity x.toLinearMap h with hm_def
  have hm2 : 2 ≤ m := by omega
  obtain ⟨hdeg, b, hb⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_selfDual_matrix_data
      hx hh hne1 hself (m := m) hm_def.symm
  have hcardE : Nat.card (AdjoinRoot h) = (2 ^ (f : ℕ)) ^ 2 := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h, hf', hdeg]
  obtain ⟨τ, hτQ, hτ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnUni.exists_frob_equiv
      (K := AdjoinRoot h) (n := (f : ℕ)) hcardE
  obtain ⟨ε, -⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433.exists_specialBlock_equiv_SU
      hx hh (m := m) b hb
  have hSU : StatedSU m (Nat.card K) (AdjoinRoot h) = StatedSU m (2 ^ (f : ℕ)) (AdjoinRoot h) := by
    rw [hf']
  have hheld : heldSU m (AdjoinRoot h) τ hτ = StatedSU m (2 ^ (f : ℕ)) (AdjoinRoot h) :=
    CFSG.LieType.SemisimpleCentralizers.Held.hct_heldSU_eq_statedSU (a := m) (Q := 2 ^ (f : ℕ))
      hτQ
  have φ : ↥(specialBlock Q x h) ≃* ↥(heldSU m (AdjoinRoot h) τ hτ) :=
    (ε.trans (MulEquiv.subgroupCongr hSU)).trans (MulEquiv.subgroupCongr hheld).symm
  rcases Nat.lt_or_ge m 3 with hm3 | hm3
  ·
    have hm_eq : m = 2 := by omega
    rw [hm_eq] at φ
    haveI : CharP (AdjoinRoot h) 2 := by
      have h2 : ringChar (AdjoinRoot h) = 2 :=
        (Algebra.ringChar_eq K (AdjoinRoot h)).symm.trans hchar
      rw [← h2]
      exact ringChar.charP (AdjoinRoot h)
    haveI : Finite (AdjoinRoot h) := by
      have hmod : Module.Finite K (AdjoinRoot h) :=
        (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
      exact Module.finite_of_finite K
    obtain ⟨e2⟩ :=
      CFSG.LieType.SemisimpleCentralizers.Held.nonempty_heldSU_two_mulEquiv_statedSL
        (p := 2) (k := (f : ℕ)) (Q := 2 ^ (f : ℕ)) (M := AdjoinRoot h) (τ := τ) (hτ := hτ)
        rfl hcardE hτQ
    have hcard_fixed :
        Nat.card (CFSG.LieType.Steinberg.fixedSubfield (AdjoinRoot h) 2 (f : ℕ)) =
          2 ^ (f : ℕ) :=
      CFSG.LieType.Steinberg.card_fixedSubfield (F := AdjoinRoot h) (p := 2) (f := (f : ℕ))
        hcardE
    let ψ : ↥(specialBlock Q x h) ≃*
        ↥(StatedSL 2 (CFSG.LieType.Steinberg.fixedSubfield (AdjoinRoot h) 2 (f : ℕ))) :=
      φ.trans e2
    have hmodel :=
      ggNbrLSideUni_typeSL (f := (f : ℕ)) (b := 2)
        (E := CFSG.LieType.Steinberg.fixedSubfield (AdjoinRoot h) 2 (f : ℕ))
        (M := ↥(specialBlock Q x h)) hf1 hcard_fixed ψ hq
    exact ⟨.PSL, 2, (f : ℕ), Or.inr ⟨rfl, rfl⟩, hmodel⟩
  ·
    obtain ⟨t, m', htm, hmodel⟩ :=
      ggNbrLSideUni_typeSU (n := (f : ℕ)) (a := m) (E := AdjoinRoot h) (τ := τ) (hτ := hτ)
        (M := ↥(specialBlock Q x h)) hf1 hcardE hτQ φ hq
    rcases htm with ⟨ht, hm'⟩ | ⟨ht, hm'⟩
    · rw [ht, hm'] at hmodel
      exact ⟨.PSU, m, (f : ℕ), Or.inl ⟨rfl, hm3⟩, hmodel⟩
    · rw [ht, hm'] at hmodel
      exact ⟨.PSL, 2, (f : ℕ), Or.inr ⟨rfl, rfl⟩, hmodel⟩

end CFSG.StandardType

end
