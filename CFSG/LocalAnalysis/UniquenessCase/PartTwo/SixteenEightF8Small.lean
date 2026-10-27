module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Block
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
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement
open CFSG.LieType.Universal.Spin (quadPlus quadMinus coe_quadPlus coe_quadMinus)

theorem s16g_not_isQuasisimple_of_realizes_comm {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hΓ : ∀ x ∈ Γ, ∀ y ∈ Γ, x * y = y * x) {W : Type} [CommGroup W]
    {H : Subgroup (MulAut W)} {U Z : Subgroup W} (hR : (FFModel.nat Γ).Realizes H U Z) :
    ¬ CFSG.Open.IsQuasisimple ↥H := by
  obtain ⟨π, hπ, -⟩ := hR
  have hcomm : ∀ x y : ↥Γ, x * y = y * x := fun x y => Subtype.ext (hΓ x x.2 y y.2)
  refine fun hq => CFSG.LocalAnalysis.GLTheoremA.SFM12.not_all_commute_of_quasisimple hq
    fun a b => ?_
  obtain ⟨x, rfl⟩ := hπ a
  obtain ⟨y, rfl⟩ := hπ b
  rw [← map_mul, ← map_mul]
  exact congrArg π (hcomm x y)

theorem s16g_mul_comm_of_card_le_one {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (hι : Fintype.card ι ≤ 1) (x y : Matrix.GeneralLinearGroup ι K) : x * y = y * x := by
  haveI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 hι
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hk : ∀ k : ι, k = i := fun k => Subsingleton.elim k i
  simp only [Units.val_mul, Matrix.mul_apply]
  have hs : ∀ f : ι → K, ∑ k, f k = f i := fun f =>
    Finset.sum_eq_single i (fun k _ hne => absurd (hk k) hne)
      (fun h => absurd (Finset.mem_univ i) h)
  rw [hs, hs, show j = i from Subsingleton.elim j i]
  exact mul_comm _ _

private theorem s16g_commutator_comm_of_card {L : Type*} [Group L] {O : Subgroup L} {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2) (hO : Nat.card O = 2 * p ^ k) :
    ∀ a ∈ ⁅O, O⁆, ∀ b ∈ ⁅O, O⁆, a * b = b * a := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  haveI : Finite O := Nat.finite_of_card_ne_zero (by rw [hO]; omega)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := O) p (n := k)
    ⟨2, by rw [hO]; ring⟩
  have hidx : P.index = 2 := by
    have h := Subgroup.card_mul_index P
    rw [hP, hO] at h
    exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
  haveI : P.Normal := Subgroup.normal_of_index_eq_two hidx
  have hPcomm : ∀ x y : P, x * y = y * x := by
    rcases hk with rfl | rfl
    · haveI := isCyclic_of_prime_card (hP.trans (pow_one p))
      exact fun x y => mul_comm' x y
    · haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hP
      exact fun x y => mul_comm' x y
  have hQcard : Nat.card (O ⧸ P) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := isCyclic_of_prime_card hQcard
  have hcomm : ∀ x y : O, ⁅x, y⁆ ∈ P := by
    intro x y
    have h : (QuotientGroup.mk' P) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm' _ _)
    exact (QuotientGroup.eq_one_iff _).1 h
  have hle : ⁅O, O⁆ ≤ P.map O.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact ⟨⁅(⟨x, hx⟩ : O), ⟨y, hy⟩⁆, hcomm _ _, by simp [commutatorElement_def]⟩
  intro a ha b hb
  obtain ⟨a', ha', rfl⟩ := hle ha
  obtain ⟨b', hb', rfl⟩ := hle hb
  exact congrArg (fun z : P => O.subtype z.1) (hPcomm ⟨a', ha'⟩ ⟨b', hb'⟩)

private theorem s16g_comm_statedOmega_of_card {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K} (hQ : ⇑Q = Q₀) {p k : ℕ}
    (hp : p.Prime) (hk : k = 1 ∨ k = 2)
    (hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 * p ^ k) :
    ∀ x ∈ StatedOmega Q₀, ∀ y ∈ StatedOmega Q₀, x * y = y * x := by
  intro x hx y hy
  rw [statedOmega_eq_comap hQ, Subgroup.mem_comap] at hx hy
  have h := s16g_commutator_comm_of_card hp hk hO _ hx _ hy
  exact (toLinEquiv ι K).injective (by
    rw [map_mul, map_mul]
    exact h)

private theorem s16g_comm_statedOmegaMinus_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ x ∈ StatedOmega (StatedQuadMinus 1 K b c), ∀ y ∈ StatedOmega (StatedQuadMinus 1 K b c),
      x * y = y * x := by
  refine s16g_comm_statedOmega_of_card (coe_quadMinus 1 K b c) Nat.prime_three (Or.inr rfl) ?_
  have h : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (0 * (0 + 1)) * ((Nat.card K : ℤ) ^ (0 + 1) + 1) *
        ∏ i ∈ Finset.Icc 1 0, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    GroupTheory.WeirSylow.natCard_orthogonalGroup_quadMinus hirr 0
  have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadMinus 1 K b c)) : ℤ) =
      2 * 3 ^ 2 := by
    rw [h, hK]
    simp
  exact_mod_cast h2

private theorem s16g_comm_statedOmegaPlus_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) :
    ∀ x ∈ StatedOmega (StatedQuadPlus 1 K), ∀ y ∈ StatedOmega (StatedQuadPlus 1 K),
      x * y = y * x := by
  refine s16g_comm_statedOmega_of_card (coe_quadPlus 1 K) (by norm_num : Nat.Prime 7)
    (Or.inl rfl) ?_
  have h : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 1 K)) : ℤ) =
      2 * (Nat.card K : ℤ) ^ (0 * (0 + 1)) * ((Nat.card K : ℤ) ^ (0 + 1) - 1) *
        ∏ i ∈ Finset.Icc 1 0, (((Nat.card K : ℤ) ^ 2) ^ i - 1) :=
    GroupTheory.WeirSylow.natCard_orthogonalGroup_quadPlus (K := K) 0
  have h2 : (Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (quadPlus 1 K)) : ℤ) =
      2 * 7 ^ 1 := by
    rw [h, hK]
    simp
  exact_mod_cast h2

theorem s16g_comm_statedOmegaMinus_of_le_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {m : ℕ}
    (hm : m ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadMinus m K b c), ∀ y ∈ StatedOmega (StatedQuadMinus m K b c),
      x * y = y * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · exact s16g_comm_statedOmegaMinus_one hK hirr
  · exact s16g_comm_statedOmegaMinus_one hK hirr

theorem s16g_comm_statedOmegaPlus_of_le_one {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {m : ℕ} (hm : m ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadPlus m K), ∀ y ∈ StatedOmega (StatedQuadPlus m K),
      x * y = y * x := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hm with rfl | rfl
  · intro x _ y _
    exact s16g_mul_comm_of_card_le_one (by simp) x y
  · exact s16g_comm_statedOmegaPlus_one hK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
