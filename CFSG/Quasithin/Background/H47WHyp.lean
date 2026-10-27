module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Quasithin.Vol2.Ch9Sec3L34QuadPf
public import CFSG.Quasithin.Vol2.Ch9Sec3L34KGMPf
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Open.StatedDefs
public import Certificates.Certificate7241
public import Certificates.Certificate7252
public import CFSG.CharacterTheory.Semidihedral.FixedFieldData
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aTop
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.Quasithin.Background.HFixSylBase
public import CFSG.Quasithin.Background.HTriSolv
public import CFSG.Quasithin.Background.HTriU3
public import CFSG.Quasithin.Background.HZ82Base
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.Quasithin.H47W

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Open
open scoped MatrixGroups


open CFSG.Quasithin.H13.Ch9 in
theorem factL34_hyps (V : Type) [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (M : Subgroup (MulAut V)) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2)
    (hL : Nonempty (↥(CFSG.generalizedFitting ↥M) ≃* PSL(3, K)))
    (hirr : IsIrredOn ((CFSG.generalizedFitting ↥M).map M.subtype) ⊤)
    (t : MulAut V) (htM : t ∈ M) (ht2 : orderOf t = 2) :
    XMod.IsIrrSec ↥(((CFSG.generalizedFitting ↥M).map M.subtype) ⊔ Subgroup.zpowers t)
        (⊥ : Subgroup V) ⊤ ∧
      (CFSG.generalizedFitting ↥M).map M.subtype ≤
        (((CFSG.generalizedFitting ↥M).map M.subtype) ⊔ Subgroup.zpowers t) ∧
      ((CFSG.generalizedFitting ↥M).map M.subtype) ⊔ Subgroup.zpowers t ≤
        Subgroup.normalizer (((CFSG.generalizedFitting ↥M).map M.subtype :
          Subgroup (MulAut V)) : Set (MulAut V)) ∧
      IsPSL 3 2 2 ↥((CFSG.generalizedFitting ↥M).map M.subtype) ∧
      (∀ x ∈ ((CFSG.generalizedFitting ↥M).map M.subtype) ⊔ Subgroup.zpowers t,
        (∀ l ∈ (CFSG.generalizedFitting ↥M).map M.subtype, x * l = l * x) → x = 1) ∧
      (∀ x ∈ ((CFSG.generalizedFitting ↥M).map M.subtype) ⊔ Subgroup.zpowers t,
        ∃ m : ℕ, x ^ 2 ^ m ∈ (CFSG.generalizedFitting ↥M).map M.subtype) := by
  haveI : Finite (MulAut V) :=
    Finite.of_injective (fun f : MulAut V => (f : V → V)) fun f g h => MulEquiv.ext (congrFun h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hL
  set F : Subgroup ↥M := CFSG.generalizedFitting ↥M with hFdef
  set L : Subgroup (MulAut V) := F.map M.subtype with hLdef
  have hFn : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := ↥M)).2
  have hLM : L ≤ M := by
    rintro _ ⟨f, -, rfl⟩
    exact f.2
  have hconj : ∀ g ∈ M, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    intro g hg l hl
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.1 hl
    exact Subgroup.mem_map.2 ⟨⟨g, hg⟩ * f * (⟨g, hg⟩ : ↥M)⁻¹, hFn.conj_mem f hf _, by simp⟩
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hinv : ∀ u : V, u⁻¹ = u := fun u => inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hV u)
  have htt' : ∀ v : V, t (t v) = v := fun v => by
    have := congrArg (fun f : MulAut V => f v) htt
    simpa using this
  have hA_cases : ∀ a ∈ Subgroup.zpowers t, a = 1 ∨ a = t := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    have h2 : t ^ (k % 2) = t ^ k := by
      have := zpow_mod_orderOf t k
      rw [ht2] at this
      simpa using this
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← h2, h, zpow_zero]
    · right
      rw [← h2, h, zpow_one]
  set X : Subgroup (MulAut V) := L ⊔ Subgroup.zpowers t with hXdef
  have htX : t ∈ X := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hLX : L ≤ X := le_sup_left
  have hXM : X ≤ M := sup_le hLM (Subgroup.zpowers_le.2 htM)
  have hcos : ∀ x ∈ X, x ∈ L ∨ ∃ l ∈ L, x = l * t := by
    intro x hx
    have hx' : x ∈ Subgroup.closure
        ((L : Set (MulAut V)) ∪ (Subgroup.zpowers t : Set (MulAut V))) := by
      rw [← Subgroup.sup_eq_closure]
      exact hx
    clear hx
    induction hx' using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact Or.inl hy
      · rcases hA_cases y hy with rfl | rfl
        · exact Or.inl L.one_mem
        · exact Or.inr ⟨1, L.one_mem, by simp⟩
    | one => exact Or.inl L.one_mem
    | mul y z _ _ hy hz =>
      rcases hy with hy | ⟨l, hl, rfl⟩ <;> rcases hz with hz | ⟨l', hl', rfl⟩
      · exact Or.inl (L.mul_mem hy hz)
      · exact Or.inr ⟨y * l', L.mul_mem hy hl', by rw [mul_assoc]⟩
      · exact Or.inr ⟨l * (t * z * t⁻¹), L.mul_mem hl (hconj t htM z hz), by group⟩
      · refine Or.inl ?_
        have e1 : l * t * (l' * t) = l * (t * l' * t⁻¹) := by
          rw [htinv]
          simp only [mul_assoc]
        rw [e1]
        exact L.mul_mem hl (hconj t htM l' hl')
    | inv y _ hy =>
      rcases hy with hy | ⟨l, hl, rfl⟩
      · exact Or.inl (L.inv_mem hy)
      · refine Or.inr ⟨t⁻¹ * l⁻¹ * t, ?_, ?_⟩
        · have h := hconj t⁻¹ (M.inv_mem htM) l⁻¹ (L.inv_mem hl)
          rwa [inv_inv] at h
        · rw [mul_assoc (t⁻¹ * l⁻¹) t t, htt, mul_one, mul_inv_rev]
  have hX2 : ∀ x ∈ X, ∃ m : ℕ, x ^ 2 ^ m ∈ L := by
    intro x hx
    rcases hcos x hx with hxL | ⟨l, hl, rfl⟩
    · exact ⟨0, by simpa using hxL⟩
    · refine ⟨1, ?_⟩
      rw [pow_one, sq]
      have e2 : l * t * (l * t) = l * (t * l * t⁻¹) * (t * t) := by group
      rw [e2, htt, mul_one]
      exact L.mul_mem hl (hconj t htM l hl)
  have hXN : X ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    refine sup_le (fun l hl => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.le_normalizer hl
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · exact hconj t htM h
      · intro hh
        have h' := hconj t⁻¹ (M.inv_mem htM) _ hh
        have e3 : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
        rwa [e3] at h'
  have hcen : Subgroup.center (PSL(3, K)) = ⊥ := by
    have hs : IsSimpleGroup (PSL(3, K)) :=
      (CFSG.LinearGroups.linear_projective_simple (K := K) (n := 3) (by norm_num)
        (Or.inl le_rfl)).2.1
    have hp : Group.IsPerfect (PSL(3, K)) :=
      CFSG.LinearGroups.linear_projective_perfect (K := K) (n := 3) (by norm_num) (Or.inl le_rfl)
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
    · exact h
    · exfalso
      have hc2 : ⁅(⊤ : Subgroup (PSL(3, K))), (⊤ : Subgroup (PSL(3, K)))⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro g _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        have hg : g ∈ Subgroup.center (PSL(3, K)) := by
          rw [h]
          exact Subgroup.mem_top g
        exact (Subgroup.mem_center_iff.1 hg) y
      have h3 : ⁅(⊤ : Subgroup (PSL(3, K))), (⊤ : Subgroup (PSL(3, K)))⁆ = ⊤ :=
        hp.commutator_eq_top
      rw [hc2] at h3
      exact top_ne_bot h3.symm
  have hcenF : ∀ y : ↥F, (∀ h : ↥F, h * y = y * h) → y = 1 := by
    intro y hy
    have hc : e y ∈ Subgroup.center (PSL(3, K)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨h, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul, hy h]
    rw [hcen] at hc
    have h1 : e y = 1 := Subgroup.mem_bot.1 hc
    exact e.injective (by rw [h1, map_one])
  have hCX : ∀ x ∈ X, (∀ l ∈ L, x * l = l * x) → x = 1 := by
    intro x hx hcomm
    have hxM : x ∈ M := hXM hx
    have hxF : (⟨x, hxM⟩ : ↥M) ∈ F := by
      apply CFSG.centralizer_generalizedFitting_le ↥M
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      apply Subtype.ext
      exact (hcomm _ (Subgroup.mem_map_of_mem _ hh)).symm
    have h1 := hcenF ⟨⟨x, hxM⟩, hxF⟩ (fun h => Subtype.ext (Subtype.ext
      (hcomm _ (Subgroup.mem_map_of_mem _ h.2)).symm))
    have h2 := congrArg (fun y : ↥F => ((y : ↥M) : MulAut V)) h1
    simpa using h2
  have hPSL : IsPSL 3 2 2 ↥L := by
    unfold IsPSL CFSG.Open.StatedClassicalModel
    refine ⟨⟨Nat.prime_two, by norm_num, by norm_num, by decide, by decide⟩, K, inferInstance,
      inferInstance, by rw [hK]; norm_num, ?_⟩
    exact ⟨((Subgroup.equivMapOfInjective F M.subtype (Subgroup.subtype_injective M)).symm.trans
      e).trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 K)⟩
  have hirrX : XMod.IsIrrSec ↥X (⊥ : Subgroup V) ⊤ := by
    refine ⟨lt_of_le_of_ne bot_le (fun h => hirr.1 h.symm), fun J hJ _ _ => ?_⟩
    refine hirr.2 J le_top (fun l hl u hu => ?_)
    exact hJ ⟨l, hLX hl⟩ u hu
  exact ⟨hirrX, hLX, hXN, hPSL, hCX, hX2⟩

end CFSG.Quasithin.H47W
