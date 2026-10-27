module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthTorSU
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Phan.PhanDn.SpinModel
public import CFSG.RankThree.PartOne.S11d.OrthModels
import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
import CFSG.RankThree.PartOne.S11d.OrthCaseN
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusEightBasic
import CFSG.CharacterTheory.Burnside
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.LieType.Chevalley.C2E6StandardFixedData
import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotAnisoF6
import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotSetup
import CFSG.RankThree.PartOne.AUTSL.OmegaFamily
import CFSG.RankThree.PartOne.AUTSL.Rows
import CFSG.RankThree.PartOne.AUTSL.SylowTrick
import CFSG.RankThree.PartOne.CTP.StrongPSylow
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessEven
import CFSG.RankThree.PartOne.KC.OrthogonalD4WitnessOdd
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S12.Sec1511Y1
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.BorelTits
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.RankThree.OrthogonalInvolutions
open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]

private theorem plh_charP_two (E : QuadExt F K (unitaryInvolution K 2 1)) : CharP F 2 :=
  RingHom.charP (algebraMap F K) (algebraMap F K).injective 2

private theorem plh_finite_F {F : Type} [Field F] (hF : Nat.card F = 2) : Finite F :=
  Nat.finite_of_card_ne_zero (α := F) (by rw [hF]; norm_num)

private theorem plh_hirr (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2) :
    ∀ s : F, s ^ 2 + 1 * s + 1 ≠ 0 := by
  letI : CharP F 2 := plh_charP_two E
  intro s hs
  have h01 : s = 0 ∨ s = 1 := by
    obtain ⟨y, _, hyu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
    have hy1 : y = 1 := (hyu 1 one_ne_zero).symm
    by_cases hx : s = 0
    · exact Or.inl hx
    · exact Or.inr (by rw [hyu s hx, hy1])
  rcases h01 with rfl | rfl
  · norm_num at hs
  · rw [one_pow, one_mul] at hs
    rw [show (1 : F) + 1 + 1 = 1 from by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]] at hs
    exact one_ne_zero hs

private theorem plh_finrank_eq (E : QuadExt F K (unitaryInvolution K 2 1)) (a : ℕ) :
    finrank F (Fin a → K) = 2 * a := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, E.finrank_eq]
  ring

private theorem plh_hts_three (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2) :
    ∀ U : Submodule F (Fin 3 → K), finrank F U = 3 → ∃ u ∈ U, Qn E 3 u ≠ 0 := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  intro U hU
  by_contra hcon
  rw [not_exists] at hcon
  have hzero : ∀ u ∈ U, Qn E 3 u = 0 := by
    intro u hu
    by_contra hne
    exact hcon u ⟨hu, hne⟩
  have hdim : finrank F (Fin 3 → K) = 6 := by
    have h := plh_finrank_eq E 3
    omega
  have hplus : IsPlusType (Qn E 3) :=
    ⟨U, by have h := hU; have h' := hdim; omega, hzero⟩
  have hirr := plh_hirr E hF
  have e := Qn.isometryEquivQuadMinus E (show Odd 3 by decide) hirr
  exact not_isPlusType_quadMinus (K := F) (n := 3) (by norm_num) hirr
    ((isPlusType_congr e).mp hplus)

private theorem plh_hts_ge_four (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    {a : ℕ} (ha : 4 ≤ a) :
    ∃ T : Submodule F (Fin a → K), finrank F T = 3 ∧ ∀ x ∈ T, Qn E a x = 0 := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨-, T, hT, hTs⟩ := regular_quadPlus (K := F) (n := a) (by omega)
    have e := Qn.isometryEquivQuadPlus E he
    refine ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hT]
    · rintro x ⟨t, ht, rfl⟩
      exact (e.symm.map_app t).trans (hTs t ht)
  · obtain ⟨-, T, hT, hTs⟩ :=
      regular_quadMinus (K := F) (n := a) (by omega) (plh_hirr E hF)
    have e := Qn.isometryEquivQuadMinus E ho (plh_hirr E hF)
    refine ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
    · rw [LinearEquiv.finrank_map_eq, hT]
    · rintro x ⟨t, ht, rfl⟩
      exact (e.symm.map_app t).trans (hTs t ht)

private theorem plh_label_props {lab : LargeEvenLabel} {a : ℕ} (ha : 4 ≤ a)
    (htag : markTag lab = .POmegaPlus ∨ markTag lab = .POmegaMinus)
    (hrank : markRank lab = a) (hdeg : markDeg lab = 1) :
    lab.n = 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
  rcases lab with ⟨tag, rank, n⟩
  cases tag <;>
    simp only [markTag, markRank, markDeg] at htag hrank hdeg ⊢ <;>
    (try split_ifs at htag hrank hdeg ⊢) <;>
    simp_all <;> omega

private theorem plh_commSpace_smul (E : QuadExt F K (unitaryInvolution K 2 1)) {a : ℕ}
    {g : (Fin a → K) ≃ₗ[F] (Fin a → K)}
    (hK : ∀ (c : K) (z : Fin a → K), g (c • z) = c • g z) (c : K) (x : Fin a → K) :
    ((g : (Fin a → K) →ₗ[F] (Fin a → K)) - 1) (c • x) =
      c • (((g : (Fin a → K) →ₗ[F] (Fin a → K)) - 1) x) := by
  change (g : (Fin a → K) → (Fin a → K)) (c • x) - c • x =
    c • ((g : (Fin a → K) → (Fin a → K)) x - x)
  rw [hK c x, smul_sub]

private theorem plh_even_finrank_commSpace (E : QuadExt F K (unitaryInvolution K 2 1)) {a : ℕ}
    {g : (Fin a → K) ≃ₗ[F] (Fin a → K)}
    (hK : ∀ (c : K) (z : Fin a → K), g (c • z) = c • g z) :
    Even (finrank F (commSpace g)) := by
  let W : Submodule K (Fin a → K) :=
    { carrier := commSpace g
      zero_mem' := (commSpace g).zero_mem
      add_mem' := fun hx hy => (commSpace g).add_mem hx hy
      smul_mem' := fun c {x} hx => by
        change x ∈ LinearMap.range ((g : (Fin a → K) →ₗ[F] (Fin a → K)) - 1) at hx
        change c • x ∈ LinearMap.range ((g : (Fin a → K) →ₗ[F] (Fin a → K)) - 1)
        rw [LinearMap.mem_range] at hx ⊢
        obtain ⟨y, rfl⟩ := hx
        exact ⟨c • y, plh_commSpace_smul E hK c y⟩ }
  letI : Module K ↥W := Submodule.module W
  letI : Module F ↥W := Submodule.module (W.restrictScalars F)
  letI : IsScalarTower F K ↥W :=
    ⟨fun p q w => Subtype.ext (smul_assoc p q (w : Fin a → K))⟩
  letI : Module.Free K ↥W := Module.Free.of_divisionRing K ↥W
  letI : Module.Free F K := Module.Free.of_divisionRing F K
  have hmul := @Module.finrank_mul_finrank F K ↥W
    (inferInstance : Semiring F) (inferInstance : Semiring K) (inferInstance : AddCommMonoid ↥W)
    (inferInstance : Module F K) (inferInstance : Module K ↥W) (inferInstance : Module F ↥W)
    (inferInstance : IsScalarTower F K ↥W)
    (inferInstance : StrongRankCondition F) (inferInstance : StrongRankCondition K)
    (inferInstance : Module.Free F K) (inferInstance : Module.Free K ↥W)
  change Even (finrank F ↥W)
  rw [hmul.symm, E.finrank_eq]
  exact ⟨finrank K W, by ring⟩

private theorem plh_finite_orthogonal (E : QuadExt F K (unitaryInvolution K 2 1)) (a : ℕ)
    (hF : Nat.card F = 2) :
    Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E a)) := by
  haveI : Finite F := plh_finite_F hF
  haveI : Finite (Fin a → K) := inferInstance
  haveI : Finite ((Fin a → K) ≃ₗ[F] (Fin a → K)) :=
    Finite.of_injective
      (fun e : (Fin a → K) ≃ₗ[F] (Fin a → K) => (e : (Fin a → K) → (Fin a → K)))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  exact Finite.of_injective Subtype.val Subtype.val_injective

private theorem plh_solvable_zero (E : QuadExt F K (unitaryInvolution K 2 1)) :
    Group.IsSolvable ↥(orthDerived (Qn E 0)) := by
  haveI : Subsingleton ((Fin 0 → K) ≃ₗ[F] (Fin 0 → K)) :=
    ⟨fun f g => LinearEquiv.ext fun x => funext fun i => Fin.elim0 i⟩
  haveI : Subsingleton ↥(orthDerived (Qn E 0)) :=
    ⟨fun x y => Subtype.ext ((inferInstance : Subsingleton _).elim x.1 y.1)⟩
  infer_instance

private theorem plh_solvable_one (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) : Group.IsSolvable ↥(orthDerived (Qn E 1)) := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  have hnot : ¬ IsPlusType (Qn E 1) := by
    have e := Qn.isometryEquivQuadMinus E (show Odd 1 by decide) (plh_hirr E hF)
    exact fun h => not_isPlusType_quadMinus (K := F) (n := 1) (by norm_num) (plh_hirr E hF)
      ((isPlusType_congr e).mp h)
  have hQ := Qn_polarBilin_nondegenerate E 1
  have hdim : finrank F (Fin 1 → K) = 2 * (0 + 1) := by
    have h := plh_finrank_eq E 1
    omega
  have hcardZ := natCard_orthogonalGroup_of_type (K := F) (V := Fin 1 → K) hQ (m := 0) hdim
    (ε := -1) (Or.inr ⟨rfl, hnot⟩)
  have h6 : (2 * (Nat.card F : ℤ) ^ (0 * (0 + 1)) * ((Nat.card F : ℤ) ^ (0 + 1) - (-1)) *
      ∏ i ∈ Finset.Icc 1 0, (((Nat.card F : ℤ) ^ 2) ^ i - 1)) = 6 := by
    rw [hF]; norm_num
  have hcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 1)) = 6 := by
    have h := hcardZ
    rw [h6] at h
    exact_mod_cast h
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 1)) := plh_finite_orthogonal E 1 hF
  haveI : Fintype ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 1)) := Fintype.ofFinite _
  have hcardF : Fintype.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 1)) = 6 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hsolvO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 1)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (a := 1) (b := 1) (by rw [hcardF]; norm_num)
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion
      (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E 1))))
    (Subgroup.inclusion_injective _)

private theorem plh_solvable_two (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) : Group.IsSolvable ↥(orthDerived (Qn E 2)) := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  have hplus : IsPlusType (Qn E 2) :=
    (isPlusType_congr (Qn.isometryEquivQuadPlus E (by norm_num : Even 2))).mpr
      (isPlusType_quadPlus (K := F) 2)
  have hQ := Qn_polarBilin_nondegenerate E 2
  have hdim : finrank F (Fin 2 → K) = 2 * (1 + 1) := by
    have h := plh_finrank_eq E 2
    omega
  have hcardZ := natCard_orthogonalGroup_of_type (K := F) (V := Fin 2 → K) hQ (m := 1) hdim
    (ε := 1) (Or.inl ⟨rfl, hplus⟩)
  have h72 : (2 * (Nat.card F : ℤ) ^ (1 * (1 + 1)) * ((Nat.card F : ℤ) ^ (1 + 1) - 1) *
      ∏ i ∈ Finset.Icc 1 1, (((Nat.card F : ℤ) ^ 2) ^ i - 1)) = 72 := by
    rw [hF]; norm_num
  have hcard : Nat.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) = 72 := by
    have h := hcardZ
    rw [h72] at h
    exact_mod_cast h
  haveI : Finite ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) := plh_finite_orthogonal E 2 hF
  haveI : Fintype ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) := Fintype.ofFinite _
  have hcardF : Fintype.card ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) = 72 := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hsolvO : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup (Qn E 2)) :=
    CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
      Nat.prime_two Nat.prime_three (by norm_num) (a := 3) (b := 2) (by rw [hcardF]; norm_num)
  exact Group.isSolvable_of_isSolvable_injective
    (f := Subgroup.inclusion
      (Subgroup.commutator_le_self (TauCeti.QuadraticMap.orthogonalGroup (Qn E 2))))
    (Subgroup.inclusion_injective _)

theorem torOmega_isSolvable_of_le_two (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {a : ℕ} (ha : a ≤ 2) : Group.IsSolvable ↥(orthDerived (Qn E a)) := by
  interval_cases a
  · exact plh_solvable_zero E
  · exact plh_solvable_one E hF
  · exact plh_solvable_two E hF

private theorem plh_factor_three (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) :
    IsQuasisimple ↥(orthDerived (Qn E 3)) ∧
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥(orthDerived (Qn E 3)) ⧸ Subgroup.center ↥(orthDerived (Qn E 3))) ∧
          lab.n = 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  have hQ : (polarBilin (Qn E 3)).Nondegenerate := Qn_polarBilin_nondegenerate E 3
  have hdim : finrank F (Fin 3 → K) = 6 := by
    have h := plh_finrank_eq E 3
    omega
  obtain ⟨E', hFieldE', hFiniteE', hcardE', ⟨eSU⟩⟩ :=
    CFSG.SeitzReduction.OmegaPilot.nonempty_orthDerived_mulEquiv_statedSU_of_six
      (K := F) (W := Fin 3 → K) (R := Qn E 3) (f := 1) (by rw [hF, pow_one]) hQ hdim
      (plh_hts_three E hF)
  letI : Field E' := hFieldE'
  letI : Finite E' := hFiniteE'
  have hE4 : Nat.card E' = 4 := by rw [hcardE']; norm_num
  exact torSU_isQuasisimple_label hE4 (by norm_num : 4 ≤ 4) eSU

private theorem plh_factor_ge_four (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {a : ℕ} (ha4 : 4 ≤ a) :
    IsQuasisimple ↥(orthDerived (Qn E a)) ∧
      ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
        GGHasLabel lab (↥(orthDerived (Qn E a)) ⧸ Subgroup.center ↥(orthDerived (Qn E a))) ∧
          lab.n = 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2) := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  haveI : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  haveI : Nontrivial (Fin a → K) :=
    Module.nontrivial_of_finrank_pos (R := F) (by
      have h := plh_finrank_eq E a
      omega)
  have hQ : (polarBilin (Qn E a)).Nondegenerate := Qn_polarBilin_nondegenerate E a
  have hts := plh_hts_ge_four E hF ha4
  have hZ : Subgroup.center ↥(orthDerived (Qn E a)) = ⊥ :=
    CFSG.RankThree.PartOne.center_orthDerived_eq_bot hQ hts
  have hq : IsQuasisimple ↥(orthDerived (Qn E a)) :=
    CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_orthDerived hQ hts
  refine ⟨hq, ?_⟩
  rcases Nat.even_or_odd a with he | ho
  · have e := Qn.isometryEquivQuadPlus E he
    have hmodel : CFSG.Blueprint.LieModel ↥(orthDerived (Qn E a)) .POmegaPlus a 2 1 :=
      CFSG.RankThree.PartOne.lieModel_of_orthDerived_plus (K := F) (R := Qn E a)
        (G := ↥(orthDerived (Qn E a))) (m := a) (f := 1) ha4 (by norm_num)
        (by rw [hF, pow_one]) e (MulEquiv.refl _)
    obtain ⟨lab, hΛ, htag, hrank, hchar, hdeg, hraw⟩ :=
      exists_label_rawDatum_of_lieModel hZ hmodel
    have hprops := plh_label_props ha4 (Or.inl htag) hrank hdeg
    exact ⟨lab, hΛ,
      ggHasLabel_of_mulEquiv (CFSG.RankThree.PartOne.Sec66T.centerQuotientEquivSelf hZ).symm hraw,
      hprops.1, hprops.2.1, hprops.2.2⟩
  · have hirr := plh_hirr E hF
    have e := Qn.isometryEquivQuadMinus E ho hirr
    have hmodel : CFSG.Blueprint.LieModel ↥(orthDerived (Qn E a)) .POmegaMinus a 2 1 :=
      CFSG.RankThree.PartOne.lieModel_of_orthDerived_minus (K := F) (R := Qn E a)
        (G := ↥(orthDerived (Qn E a))) (m := a) (f := 1) ha4 (by norm_num)
        (by rw [hF, pow_one]) hirr e (MulEquiv.refl _)
    obtain ⟨lab, hΛ, htag, hrank, hchar, hdeg, hraw⟩ :=
      exists_label_rawDatum_of_lieModel hZ hmodel
    have hprops := plh_label_props ha4 (Or.inr htag) hrank hdeg
    exact ⟨lab, hΛ,
      ggHasLabel_of_mulEquiv (CFSG.RankThree.PartOne.Sec66T.centerQuotientEquivSelf hZ).symm hraw,
      hprops.1, hprops.2.1, hprops.2.2⟩

theorem torOmega_factor (E : QuadExt F K (unitaryInvolution K 2 1)) (hF : Nat.card F = 2)
    (a : ℕ) :
    Group.IsSolvable ↥(orthDerived (Qn E a)) ∨
      (IsQuasisimple ↥(orthDerived (Qn E a)) ∧
        ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
          GGHasLabel lab (↥(orthDerived (Qn E a)) ⧸ Subgroup.center ↥(orthDerived (Qn E a))) ∧
            lab.n = 1 ∧ lab.tag ≠ .A ∧ (lab.tag = .twD → lab.rank ≠ 2)) := by
  by_cases ha2 : a ≤ 2
  · left
    rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with rfl | rfl | rfl
    · exact plh_solvable_zero E
    · exact plh_solvable_one E hF
    · exact plh_solvable_two E hF
  · right
    rcases (show a = 3 ∨ 4 ≤ a by omega) with rfl | ha4
    · exact plh_factor_three E hF
    · exact plh_factor_ge_four E hF ha4

theorem torOmega_klinear_le_orthDerived (E : QuadExt F K (unitaryInvolution K 2 1))
    (hF : Nat.card F = 2) {a : ℕ} (ha : 3 ≤ a) {g : (Fin a → K) ≃ₗ[F] (Fin a → K)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn E a))
    (hK : ∀ (c : K) (z : Fin a → K), g (c • z) = c • g z) : g ∈ orthDerived (Qn E a) := by
  letI : CharP F 2 := plh_charP_two E
  haveI : Finite F := plh_finite_F hF
  have hQ : (polarBilin (Qn E a)).Nondegenerate := Qn_polarBilin_nondegenerate E a
  have hgω : g ∈ omegaGroup (Qn E a) hQ :=
    mem_omegaGroup.mpr ⟨hg, plh_even_finrank_commSpace E hK⟩
  rcases (show a = 3 ∨ 4 ≤ a by omega) with rfl | ha4
  · have hD := (CFSG.RankThree.PartOne.nonsplit_quasisimple_dicksonDerived (Qn E 3) hQ
      (Or.inr (by
        have h := plh_finrank_eq E 3
        omega))
      (fun U hU => plh_hts_three E hF U (by
        have h : finrank F (Fin 3 → K) = 6 := by
          have h' := plh_finrank_eq E 3
          omega
        rw [h] at hU
        norm_num at hU
        exact hU))).2
    exact hD ⟨g, hg⟩ (by
      rw [← MonoidHom.mem_ker, dicksonHom_ker, Subgroup.mem_subgroupOf]
      exact hgω)
  · exact CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hQ
      (plh_hts_ge_four E hF ha4) hgω

end CFSG.StandardType.QTwo

end
