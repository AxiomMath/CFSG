module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsOmegaRegular
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
import CFSG.ClassicalInvolution.PerfectCase.Basic
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.IIIaResidualDefs
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSideDefs
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Sporadic.J4Base
public import Certificates.Certificate8026Base

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.LieType.BorelTits (orthGroup statedOmega_le_orthGroup)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv closure_isometries_eq_comap)

private theorem s16low_isSolvable_statedProj_statedOmega_le_two
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [CharP K 2]
    (Q₀ : (ι → K) → K) (Q : QuadraticForm K (ι → K)) (hQ : ⇑Q = Q₀)
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K (ι → K) ≤ 2) :
    Group.IsSolvable (StatedProj (StatedOmega Q₀)) := by
  have : Group.IsSolvable (TauCeti.QuadraticMap.orthogonalGroup Q) :=
    CFSG.StandardType.LayerCores.OrthRegular.isSolvable_orthogonalGroup_of_finrank_le_two
      hnd hdim
  have hEq : orthGroup Q₀ =
      (TauCeti.QuadraticMap.orthogonalGroup Q).comap (toLinEquiv ι K).toMonoidHom :=
    closure_isometries_eq_comap (Q := Q) (Q₀ := Q₀) hQ
  have hOrth : Group.IsSolvable ↥(orthGroup Q₀) := by
    have hmap : (orthGroup Q₀).map (toLinEquiv ι K).toMonoidHom =
        TauCeti.QuadraticMap.orthogonalGroup Q := by
      rw [hEq]
      exact Subgroup.map_comap_eq_self_of_surjective
        (toLinEquiv ι K).surjective _
    let e := ((orthGroup Q₀).equivMapOfInjective
      (toLinEquiv ι K).toMonoidHom (toLinEquiv ι K).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
  have := hOrth
  have : Group.IsSolvable ↥(StatedOmega Q₀) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (statedOmega_le_orthGroup Q₀))
      (Subgroup.inclusion_injective _)
  exact Group.isSolvable_of_surjective
    (QuotientGroup.mk'_surjective ((StatedScalars ι K).subgroupOf (StatedOmega Q₀)))

theorem s16low_two_le_of_isSLn
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (_ha : a = 2 ∨ a = 3)
    (hshape : IsSLn X n a) :
    2 ≤ n := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  have hqSL : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin n) K) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv
      ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL n K).trans e.symm) hq
  exact CFSG.AGLEmbedding.LeviBlock.two_le_of_isQuasisimple_specialLinear hqSL

theorem s16low_two_le_of_isSpn
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (_ha : a = 2 ∨ a = 3)
    (hshape : IsSpn X n a) :
    2 ≤ n := by
  by_contra hlt
  obtain ⟨hev, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  have hn0 : n = 0 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rw [hn0] at e
  have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
  rw [hdiv] at e
  have : Subsingleton ↥(StatedSp 0 K) :=
    ⟨fun x y => Subtype.ext (Units.ext (Matrix.ext fun i => isEmptyElim i))⟩
  have : Subsingleton X :=
    ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩
  have : Nontrivial (X ⧸ Subgroup.center X) := hq.2.toNontrivial
  have : Nontrivial X := (QuotientGroup.mk'_surjective (Subgroup.center X)).nontrivial
  exact (not_subsingleton_iff_nontrivial (α := X)).mpr inferInstance inferInstance

theorem s16low_four_le_of_isOmegaPlus
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (_ha : a = 2 ∨ a = 3)
    (hshape : IsOmegaPlus X n a) :
    4 ≤ n := by
  by_contra hlt
  have hev : Even n := hshape.1
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have hsolv : ∀ r : ℕ, r ≤ 1 →
      Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus r K))) := by
    intro r hr
    have hQ : ⇑(CFSG.LieType.Universal.Spin.quadPlus r K) = StatedQuadPlus r K :=
      CFSG.LieType.Universal.Spin.coe_quadPlus r K
    have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadPlus r K)).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadPlus r K
    have hdim : Module.finrank K (Fin r ⊕ Fin r → K) ≤ 2 := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    exact s16low_isSolvable_statedProj_statedOmega_le_two (StatedQuadPlus r K)
      (CFSG.LieType.Universal.Spin.quadPlus r K) hQ hnd hdim
  have hn : n = 0 ∨ n = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rcases hn with rfl | rfl
  · have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (0 / 2) K))) := by
      simpa [hdiv] using hsolv 0 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance
  · have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadPlus (2 / 2) K))) := by
      simpa [hdiv] using hsolv 1 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance

theorem s16low_four_le_of_isOmegaMinus
    {X : Type} [Group X] {n a : ℕ}
    (hq : CFSG.Open.IsQuasisimple X) (_ha : a = 2 ∨ a = 3)
    (hshape : IsOmegaMinus X n a) :
    4 ≤ n := by
  by_contra hlt
  have hev : Even n := hshape.1
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hshape
  let := hKf
  let := hKfin
  have : CharP K 2 :=
    CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hKcard
  have hsolv : ∀ r : ℕ, r ≤ 1 →
      Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus r K b c))) := by
    intro r hr
    have hQ : ⇑(CFSG.LieType.Universal.Spin.quadMinus r K b c) = StatedQuadMinus r K b c :=
      CFSG.LieType.Universal.Spin.coe_quadMinus (n := r) (K := K) b c
    have hnd : (QuadraticMap.polarBilin (CFSG.LieType.Universal.Spin.quadMinus r K b c)).Nondegenerate :=
      CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
        (n := r) (K := K) hirr
    have hdim : Module.finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) ≤ 2 := by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      omega
    exact s16low_isSolvable_statedProj_statedOmega_le_two (StatedQuadMinus r K b c)
      (CFSG.LieType.Universal.Spin.quadMinus r K b c) hQ hnd hdim
  have hn : n = 0 ∨ n = 2 := by
    obtain ⟨k, hk⟩ := hev
    omega
  rcases hn with rfl | rfl
  · have hdiv : (0 : ℕ) / 2 = 0 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus (0 / 2) K b c))) := by
      simpa [hdiv] using hsolv 0 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance
  · have hdiv : (2 : ℕ) / 2 = 1 := by norm_num
    have : Group.IsSolvable (StatedProj (StatedOmega (StatedQuadMinus (2 / 2) K b c))) := by
      simpa [hdiv] using hsolv 1 (by norm_num)
    have : Group.IsSolvable X :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact CFSG.ClassicalInvolution.not_isSolvable_of_open_isQuasisimple hq inferInstance

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
