module

public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticDiag
public import CFSG.LocalAnalysis.StandardType.GGTableBBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBLinear
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotTorus
import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LieType.Universal.Spin.Roots
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.Walter.JRFacts
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableBSymp

variable {K : Type} [Field K] {m : ℕ}

theorem sp_I_subset_inn [Finite K] [CharP K 2] :
    LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m) ⊆
      Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →* _) := by
  rintro φ ⟨A, ⟨μ, hμ0, hA⟩, hφ⟩
  have := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hl, zero_mul])
  set A' := Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A with hA'
  have hA'Sp : A' ∈ LargeEvenSpGroup K m :=
    Subgroup.subset_closure (TableB.exists_scalar_mul_mem_sp hA hl0 hl)
  have hconj : ∀ h : GL (Fin m ⊕ Fin m) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp
      (TableB.scalar_mem_center (ι := Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0)))
    rw [hA', mul_inv_rev]
    set s := Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0))
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSpGroup K m, (a : GL (Fin m ⊕ Fin m) K) = A' :=
    ⟨⟨A', hA'Sp⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSpGroup K m)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

noncomputable def spProjEquivSp [CharP K 2] [NeZero m] :
    LargeEvenProj (LargeEvenSpGroup K m) ≃* LargeEvenSpGroup K m :=
  (CFSG.SeitzReduction.F4Pilot.spProjEquiv m K).symm

theorem center_spProj_eq_bot [CharP K 2] [NeZero m] :
    Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) = ⊥ := by
  have h := CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := K) m
  rw [eq_bot_iff]
  intro x hx
  set e := spProjEquivSp (K := K) (m := m) with he
  have hx' : e x ∈ Subgroup.center (LargeEvenSpGroup K m) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
  have : e x = 1 := by
    have h' : spProjEquivSp x ∈ (⊥ : Subgroup (LargeEvenSpGroup K m)) := h ▸ hx'
    exact Subgroup.mem_bot.mp h'
  rw [Subgroup.mem_bot, ← e.map_eq_one_iff]
  exact this

theorem exists_orderOf_eq_of_dvd [Finite K] {p : ℕ} [Fact p.Prime] (hpq : p ∣ Nat.card K - 1) :
    ∃ ζ : Kˣ, orderOf ζ = p :=
  exists_prime_orderOf_dvd_card' p (by rw [Nat.card_units]; exact hpq)

theorem natCast_ne_zero_of_charTwo [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K 2]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm

theorem card_le_of_isElemAbelian_spProj [Finite K] [CharP K 2] [NeZero m] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1)
    {A : Subgroup (LargeEvenProj (LargeEvenSpGroup K m))} (hA : IsElemAbelian p A) :
    Nat.card A ≤ p ^ m := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo⟩ := exists_orderOf_eq_of_dvd (K := K) hpq
  set A' : Subgroup (GL (Fin m ⊕ Fin m) K) :=
    (A.map (spProjEquivSp (K := K) (m := m)).toMonoidHom).map (LargeEvenSpGroup K m).subtype
  have hA' : IsElemAbelian p A' := TableB.isElemAbelian_map (TableB.isElemAbelian_map hA _) _
  have hcard : Nat.card A' = Nat.card A := by
    rw [← Nat.card_congr ((A.map (spProjEquivSp (K := K) (m := m)).toMonoidHom).equivMapOfInjective
      _ (LargeEvenSpGroup K m).subtype_injective).toEquiv,
      ← Nat.card_congr (A.equivMapOfInjective _
        (spProjEquivSp (K := K) (m := m)).injective).toEquiv]
  rw [← hcard]
  exact card_le_of_isElemAbelian_sp (natCast_ne_zero_of_charTwo hp hp2) hζo
    (Subgroup.map_subtype_le _) hA'

section Inner

variable {R : Type*} [Group R]

theorem exists_of_subset_inn [Finite R] (hR : Subgroup.center R = ⊥) {p : ℕ}
    {E : Subgroup (MulAut R)} (hEI : (E : Set (MulAut R)) ⊆ Set.range (MulAut.conj : R →* _))
    (hE : IsElemAbelian p E) :
    ∃ A : Subgroup R, IsElemAbelian p A ∧ Nat.card A = Nat.card E := by
  have hinj := mulAut_conj_injective hR
  refine ⟨E.comap MulAut.conj, ⟨⟨⟨fun a b => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hE a.2 b.2
  · rw [map_pow, map_one]
    exact hE.2 _ hx
  · have hmap : (E.comap (MulAut.conj : R →* MulAut R)).map MulAut.conj = E := by
      rw [Subgroup.map_comap_eq, inf_eq_right.mpr]
      intro φ hφ
      exact hEI hφ
    rw [Nat.card_congr ((E.comap (MulAut.conj : R →* MulAut R)).equivMapOfInjective _
      hinj).toEquiv, hmap]

omit [Group R] in
theorem finite_mulAut [Group R] [Finite R] : Finite (MulAut R) :=
  Finite.of_injective (fun φ : MulAut R => (φ : R → R)) DFunLike.coe_injective

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem card_le_of_isCyclic_outer [Finite R] {p : ℕ} (hp : 0 < p) (hcyc : IsCyclic (Outer R))
    {E : Subgroup (MulAut R)} (hE : IsElemAbelian p E) :
    Nat.card E ≤ p * Nat.card (E ⊓ inner R : Subgroup (MulAut R)) := by
  have := finite_mulAut (R := R)
  set f : E →* Outer R := (QuotientGroup.mk' (inner R)).comp E.subtype with hf
  have h1 := TableB.card_range_mul_card_ker f
  have hker : Nat.card f.ker = Nat.card (E ⊓ inner R : Subgroup (MulAut R)) := by
    have : f.ker = (inner R).subgroupOf E := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hf, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      rfl
    rw [this, Nat.card_congr (((inner R).subgroupOf E).equivMapOfInjective _
      E.subtype_injective).toEquiv, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hrange : Nat.card f.range ≤ p := by
    have : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
    refine TableB.card_le_of_isCyclic hp inferInstance ?_
    rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ p = 1 from Subtype.ext (hE.2 e e.2), map_one]
  rw [hker] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ hrange

end Inner

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem ggBstarBound_symplectic [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1) (hm : 1 ≤ m) :
    GGBstarBound p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  intro Eb Eh hEbI hEb hr h3 hle hEh hcard
  exfalso
  have : NeZero m := ⟨by omega⟩
  have hZ := center_spProj_eq_bot (K := K) (m := m)
  obtain ⟨A, hA, hAc⟩ := exists_of_subset_inn hZ (fun φ hφ => sp_I_subset_inn (hEbI hφ)) hEb
  have hEbm : Nat.card Eb ≤ p ^ m := hAc ▸ card_le_of_isElemAbelian_spProj hp hp2 hpq hA
  by_cases hm3 : 3 ≤ m
  ·
    have hcyc : IsCyclic (Outer (LargeEvenProj (LargeEvenSpGroup K m))) :=
      CFSG.SeitzReduction.SymplecticPilot.isCyclic_outer_statedProj (K := K) hm3
    have h1 := card_le_of_isCyclic_outer hp.pos hcyc hEh
    obtain ⟨A', hA', hA'c⟩ := exists_of_subset_inn hZ
      (fun φ hφ => (inf_le_right : Eh ⊓ ComponentClassification.OuterAutomorphisms.inner _ ≤
        ComponentClassification.OuterAutomorphisms.inner _) hφ)
      (TableB.isElemAbelian_mono hEh inf_le_left)
    have h2 : Nat.card (Eh ⊓ ComponentClassification.OuterAutomorphisms.inner
        (LargeEvenProj (LargeEvenSpGroup K m)) :
        Subgroup (MulAut _)) ≤ p ^ m := hA'c ▸ card_le_of_isElemAbelian_spProj hp hp2 hpq hA'
    have h4 : p ^ (m + 2) ≤ p ^ (m + 1) := by
      calc p ^ (m + 2) = p ^ 2 * p ^ m := by ring
        _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
        _ ≤ Nat.card Eh := hcard
        _ ≤ p * p ^ m := h1.trans (Nat.mul_le_mul_left _ h2)
        _ = p ^ (m + 1) := by ring
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h4
    omega
  · have h5 : p ^ 3 ≤ p ^ m := h3.trans hEbm
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h5
    omega

theorem recipeSymplectic_torusLift_bstarBound {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGBstarBound p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_symplectic hp hp2 (by rw [hK]; exact hpn) hl,
    ggBstarBound_symplectic hp hp2 (by rw [hK]; exact hpn) hl⟩

end TableBSymp

end CFSG.StandardType
