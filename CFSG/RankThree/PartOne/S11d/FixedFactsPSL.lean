module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66PSL
public import CFSG.RankThree.PartOne.S11c.Sec66PSL2
public import CFSG.RankThree.PartOne.S11c.Sec66TorusPSL
public import CFSG.SignalizerFunctorTheorem.NonLocal.LinearMain
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal
public import CFSG.Assembly.QuasithinDefs
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
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
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T
open CFSG.Assembly.LowTwoRank
  (StatedLieAdmissible StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)

theorem fixedFacts_PSL_ge_three {T : Type} [Group T] [Finite T] {p f₀ n : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hn3 : 3 ≤ n) (hM : LieModel T .PSL n 2 (p * f₀)) (hf₀ : 1 ≤ f₀)
    (hrank : LocalRankLeTwo p T) (α : MulAut T) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) :
    FixedFacts p α := by
  have hC : StatedClassicalModel T .PSL n 2 (p * f₀) :=
    (lieModel_classical_iff (by decide)).mp hM
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hdiag : ¬ p ∣ Nat.gcd n (2 ^ (p * f₀) - 1) := fun hd =>
    psl_torus_rank T n (p * f₀) p hp hp5 (hd.trans (Nat.gcd_dvd_left _ _))
      (hd.trans (Nat.gcd_dvd_right _ _)) hC hrank
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have hdiagK : ¬ p ∣ Nat.gcd n (Nat.card K - 1) := by rwa [hK]
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  let e : T ≃* projectiveSL n K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj n K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL n K)
  have : Finite (projectiveSL n K) := Finite.of_equiv T e.toEquiv
  have hα'inn : MulAut.congr e α ∉ innerAut (projectiveSL n K) :=
    fun h => hαinn ((mem_innerAut_congr e α).mp h)
  have hα'p : MulAut.congr e α ^ p = 1 := by
    rw [← map_pow, hαp, map_one]
  have hα'ord : orderOf (MulAut.congr e α) = p := by
    refine orderOf_eq_prime hα'p ?_
    intro h1
    exact hα'inn (h1 ▸ (innerAut (projectiveSL n K)).one_mem)
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) hn3
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := n) (K := K)
  have hE : MulAut.congr e α ∈ semilinearAutGroup n K := by
    have hidx' : (semilinearAutGroup n K).index ≤ 2 := by
      have h2' : (semilinearAutGroup n K).relIndex (standardAutGroup n K) ≤ 2 := hidx
      rwa [hgenTop, Subgroup.relIndex_top_right] at h2'
    refine OutStructure.mem_of_pow_mem_of_index_le_two _ hidx' (hp.odd_of_ne_two hp2) ?_
    rw [hα'p]
    exact Subgroup.one_mem _
  have hD : MulAut.congr e α ∉ linearAutGroup n K := by
    intro hD
    exact hα'inn (OutStructure.linear_D2 hp hn3 hdiagK _ hD 1
      (by rw [pow_one, hα'p]; exact Subgroup.one_mem _))
  obtain ⟨-, -, -, -, -, -, -, hdesc⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent Nat.prime_two hf
      hn3 hK
  obtain ⟨hpf, σ, hσord, ⟨h, -, hαh⟩, hkcard⟩ := hdesc p hp hp2 _ hE hD hα'ord
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hkcard
  have hfixset : {x : projectiveSL n K | fieldAut n K σ x = x} =
      ((linearSubfieldInclusion n (semilinearFixedSubfield σ)).range :
        Set (projectiveSL n K)) := by
    by_cases hpq : p ∣ 2 ^ (p * f₀) - 1
    · have hpn : ¬ p ∣ n := fun hpn => hdiag (Nat.dvd_gcd hpn hpq)
      have hcop : Nat.Coprime n p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn).symm
      exact (higher_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp hp2
        hf hn3 hcop hK σ hσord).2.1
    · exact (nonsplit_linear_prime_subfield_fixed_group_and_full_centralizer Nat.prime_two hp
        (by omega) hp2 hf hn3 hK hpq σ hσord).2.2.1
  have hinj := linearSubfieldInclusion_injective (by omega : 0 < n) (semilinearFixedSubfield σ)
  have hfixeq : fixSub (fieldAut n K σ) =
      (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range := by
    ext x
    exact Set.ext_iff.mp hfixset x
  have hs : IsSimpleGroup (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
    KCLinearSubfield.isSimpleGroup_projectiveSL hn3
  have hnab : ∃ a b : projectiveSL n ↥(semilinearFixedSubfield σ), a * b ≠ b * a := by
    have h1 := KCLinearSubfield.not_commutative_projectiveSL
      (n := n) (K := ↥(semilinearFixedSubfield σ)) hn3
    push Not at h1
    exact h1
  have hXmodel : LieModel (projectiveSL n ↥(semilinearFixedSubfield σ)) .PSL n 2 f₀ :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨⟨Nat.prime_two, hf₀, by omega, fun hc => by have := (Prod.mk.inj hc).1; omega,
          fun hc => by have := (Prod.mk.inj hc).1; omega⟩,
        ↥(semilinearFixedSubfield σ), inferInstance, inferInstance, hkcard,
        ⟨(LinearCover.projectiveSpecialLinearEquivProjectiveSL n
          ↥(semilinearFixedSubfield σ)).symm.trans
            (projectiveSpecialLinearGroupEquivStatedProj n ↥(semilinearFixedSubfield σ))⟩⟩
  set φ : T ≃* projectiveSL n K := e.trans (h⁻¹ : MulAut (projectiveSL n K)) with hφ
  have hφα : MulAut.congr φ α = fieldAut n K σ := by
    have : MulAut.congr φ α = h⁻¹ * MulAut.congr e α * h⁻¹⁻¹ := rfl
    rw [this, hαh]
    group
  set N := (linearSubfieldInclusion n (semilinearFixedSubfield σ)).range with hN
  have hNΓ : N ≤ fixSub (MulAut.congr φ α) := by rw [hφα, hfixeq]
  have hΓN : fixSub (MulAut.congr φ α) = N := by rw [hφα, hfixeq]
  have hNnorm : (N.subgroupOf (fixSub (MulAut.congr φ α))).Normal := by
    rw [hΓN, Subgroup.subgroupOf_self]
    exact Subgroup.normal_top
  have hsolv : Group.IsSolvable (↥(fixSub (MulAut.congr φ α)) ⧸
      N.subgroupOf (fixSub (MulAut.congr φ α))) := by
    have : Subsingleton (↥(fixSub (MulAut.congr φ α)) ⧸
        N.subgroupOf (fixSub (MulAut.congr φ α))) := by
      refine ⟨fun x y => ?_⟩
      induction x using QuotientGroup.induction_on with
      | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
          rw [QuotientGroup.eq]
          exact Subgroup.mem_subgroupOf.mpr (hΓN ▸ (x⁻¹ * y).2)
    exact inferInstance
  let eNk : ↥N ≃* projectiveSL n ↥(semilinearFixedSubfield σ) :=
    (MonoidHom.ofInjective hinj).symm
  have hNperf : Group.IsPerfect ↥N := by
    have hperf : Group.IsPerfect (projectiveSL n ↥(semilinearFixedSubfield σ)) :=
      isPerfect_of_simple_nonabelian hnab
    exact Group.IsPerfect.ofSurjective (f := eNk.symm.toMonoidHom) eNk.symm.surjective
  have hZ : Subgroup.center (projectiveSL n ↥(semilinearFixedSubfield σ)) = ⊥ :=
    center_eq_bot_of_simple' hnab
  have hX : LieModel (↥N ⧸ Subgroup.center ↥N) .PSL n 2 f₀ :=
    lieModel_of_mulEquiv
      ((centerQuotientCongr eNk).trans (centerQuotientEquivSelf hZ)).symm hXmodel
  exact fixedFacts_of_iso φ α hM hf₀ N hNΓ hNnorm hNperf hsolv
    (SignalizerFunctorTheorem.NonLocal.nonLocalized_linearSubfield hn3 _)
    (fun x hx _ => hΓN ▸ hx) (Or.inl fun x hx _ => hΓN ▸ hx) (Or.inl hX)


theorem fixedFacts_PSL_two {T : Type} [Group T] [Finite T]
    {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hM : LieModel T .PSL 2 2 (p * f₀)) (hf₀ : 2 ≤ f₀)
    (α : MulAut T) (hαp : α ^ p = 1) (hαinn : α ∉ innerAut T) : FixedFacts p α := by
  have hC : StatedClassicalModel T .PSL 2 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  obtain ⟨-, K, _, _, hK, ⟨e0⟩⟩ := hC
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos (by omega)
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := p * f₀) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαinn (h1 ▸ (innerAut T).one_mem)
  let ψ : T ≃* coordinateG K :=
    (e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (pslEquivCoordinateG K)
  obtain ⟨-, k, hkcard, ⟨eX⟩⟩ := psl_two_exists_fixSub_equiv hp hp2 hf hK ψ hαord hαinn
  have hfdiv : p * f₀ / p = f₀ := Nat.mul_div_cancel_left f₀ hp.pos
  rw [hfdiv] at hkcard
  have h4k : 4 ≤ Nat.card k := by
    rw [hkcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
  have : Fintype k := Fintype.ofFinite k
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := f₀) (by
    rw [← Nat.card_eq_fintype_card, hkcard])
  let eS : coordinateG k ≃* KCRootAxis.SL₂ k :=
    (pslEquivCoordinateG k).symm.trans (KCRootAxis.slEquivPSL k).symm
  have hsimple : IsSimpleGroup (KCRootAxis.SL₂ k) := KCRootAxis.sl2_isSimpleGroup h4k
  have hnab : ∃ x y : KCRootAxis.SL₂ k, x * y ≠ y * x :=
    exists_noncomm_of_perfect (KCRootAxis.sl2_isPerfect h4k).commutator_eq_top
  have hXmodel : LieModel (KCRootAxis.SL₂ k) .PSL 2 2 f₀ :=
    (lieModel_classical_iff (by decide)).mpr
      ⟨⟨Nat.prime_two, by omega, le_refl 2, fun hc => by
          have h2 : 2 ^ f₀ = 2 := (Prod.mk.inj hc).2
          have : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
          omega,
        fun hc => by
          have h2 : 2 ^ f₀ = 3 := (Prod.mk.inj hc).2
          have : 2 ^ 2 ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀
          omega⟩,
        k, inferInstance, inferInstance, hkcard,
        ⟨(KCRootAxis.slEquivPSL k).trans (projectiveSpecialLinearGroupEquivStatedProj 2 k)⟩⟩
  set N : Subgroup T := fixSub α with hN
  let eN : ↥N ≃* KCRootAxis.SL₂ k := eX.trans eS
  have hperfS : Group.IsPerfect (KCRootAxis.SL₂ k) := isPerfect_of_simple_nonabelian hnab
  have hNperf : Group.IsPerfect ↥N :=
    Group.IsPerfect.ofSurjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  let ψ' : T ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e0.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hns : ¬ Group.IsSolvable ↥(N.map ψ'.toMonoidHom) := by
    intro hs
    have hsN : Group.IsSolvable ↥N :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.equivMapOfInjective N ψ'.toMonoidHom ψ'.injective).toMonoidHom)
        (Subgroup.equivMapOfInjective N ψ'.toMonoidHom ψ'.injective).injective
    have : Nontrivial (KCRootAxis.SL₂ k) := hsimple.toNontrivial
    have : Nontrivial ↥N := eN.toEquiv.nontrivial
    exact Group.IsPerfect.not_isSolvable ↥N hsN
  have hNL : NonLocalized N :=
    nonLocalized_of_map_eq (φ := ψ') (W := N) rfl
      (SignalizerFunctorTheorem.CatalogBridge.nonLocalized_of_not_isSolvable_psl2 _ hns)
  have hcr : MulAut.congr (MulEquiv.refl T) α = α := MulEquiv.ext fun x => rfl
  have : IsSimpleGroup (KCRootAxis.SL₂ k) := hsimple
  exact fixedFacts_of_simple (MulEquiv.refl T) α hM (by omega)
    ((MulEquiv.subgroupCongr (by rw [hcr])).trans eN) hnab (by rw [hcr]; exact hNL)
    (Or.inl hXmodel)

theorem tagFixedFacts_PSL : TagFixedFacts .PSL := by
  intro T _ _ p hp hp5 hrank n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hC : StatedClassicalModel T .PSL n 2 (p * f₀) := (lieModel_classical_iff (by decide)).mp hM
  have hn2 : 2 ≤ n := hC.1.2.2.1
  by_cases hn3 : 3 ≤ n
  · exact fixedFacts_PSL_ge_three hp hp5 hn3 hM hf₀ hrank α hαp hαinn
  · have hn : n = 2 := by omega
    subst hn
    have hadm := admissible_of_fixModel hX₀
    have hf2 : 2 ≤ f₀ := by
      rcases hadm with ⟨-, -, -, h22, -⟩ | ⟨h, -, -⟩
      · by_contra hlt
        have : f₀ = 1 := by omega
        exact h22 (by rw [this, pow_one])
      · exact absurd h (by decide)
    exact fixedFacts_PSL_two hp hp5 hM hf2 α hαp hαinn

end CFSG.RankThree.PartOne.FieldFix
