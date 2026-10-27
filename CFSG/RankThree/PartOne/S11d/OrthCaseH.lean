module

public import CFSG.RankThree.PartOne.S11d.OrthGoodSingle
public import CFSG.RankThree.PartOne.S11d.OrthRational
public import CFSG.RankThree.PartOne.K159.Klein

public section

namespace CFSG.RankThree.PartOne

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonalSubfield
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.LieType.Universal.Spin
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedSL StatedProj StatedScalars
  projectiveSpecialLinearGroupEquivStatedProj specialLinearGroupEquivStatedSL)
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne.Sec66T (lieModel_classical_iff centerQuotientEquivSelf)

section Basic

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem dicksonDerived_of_threeSingular {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate)
    (hT : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0) : DicksonDerived R hR := by
  intro g hg
  refine CFSG.RankThree.PartOne.FieldFix.omegaGroup_le_orthDerived hR hT (mem_omegaGroup.mpr
    ⟨g.2, ?_⟩)
  rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
    ZMod.natCast_eq_zero_iff_even] at hg
  exact hg

noncomputable def fixedComponentImageEquiv (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    (hx : OddOrderIsometry Q p x) :
    ↥(fixedComponentImage Q x) ≃* ↥(orthDerived (Q.comp (fixedSpace x).subtype)) :=
  (Subgroup.equivMapOfInjective ((supportedFixedDerived Q x).subgroupOf (orthDerived Q))
    (piOrth Q) (piOrth_injective hQ)).symm.trans
    ((Subgroup.subgroupOfEquivOfLe hx.supportedFixedDerived_le_orthDerived).trans
      (supportedFixedDerivedEquiv hx))

omit [Finite K] [CharP K 2] in
theorem exists_threeSingular_of_isometry {W W' : Type} [AddCommGroup W] [Module K W]
    [AddCommGroup W'] [Module K W'] {R : QuadraticForm K W} {R' : QuadraticForm K W'}
    (e : R.IsometryEquiv R') (hT : ∃ U : Submodule K W', finrank K U = 3 ∧ ∀ u ∈ U, R' u = 0) :
    ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0 := by
  obtain ⟨U', hU', hU's⟩ := hT
  refine ⟨U'.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
  · rw [LinearEquiv.finrank_map_eq]
    exact hU'
  · rintro _ ⟨u', hu', rfl⟩
    change R (e.symm u') = 0
    rw [e.symm.map_app]
    exact hU's u' hu'

omit [CharP K 2] in
theorem exists_threeSingular_of_dim {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (R : QuadraticForm K W) (hR : (polarBilin R).Nondegenerate) {m : ℕ} (hm : 4 ≤ m)
    (hdim : finrank K W = 2 * m) : ∃ U : Submodule K W, finrank K U = 3 ∧ ∀ u ∈ U, R u = 0 := by
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus R hR (by omega) hdim with
    he | ⟨b, c, hirr, he⟩
  · obtain ⟨e⟩ := he
    exact exists_threeSingular_of_isometry e
      (CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := K) (n := m) (by omega)).2
  · obtain ⟨e⟩ := he
    exact exists_threeSingular_of_isometry e
      (CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := m) hm hirr).2

end Basic

section Models

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem center_SL4_eq_bot {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 4) F) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 4 = 0 := by
      linear_combination hr + (1 - 2 * r ^ 3 + 3 * r ^ 2 - 2 * r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  subst hr1
  ext1
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

noncomputable def statedSL4EquivStatedProj {F : Type} [Field F] [CharP F 2] :
    ↥(StatedSL 4 F) ≃* StatedProj (StatedSL 4 F) :=
  (specialLinearGroupEquivStatedSL 4 F).symm.trans
    (((QuotientGroup.quotientMulEquivOfEq center_SL4_eq_bot).trans
      QuotientGroup.quotientBot).symm.trans (projectiveSpecialLinearGroupEquivStatedProj 4 F))

noncomputable def orthDerivedEquivCommutator {W : Type*} [AddCommGroup W] [Module K W]
    (R : QuadraticForm K W) :
    ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) ≃* ↥(orthDerived R) :=
  (Subgroup.equivMapOfInjective _ (TauCeti.QuadraticMap.orthogonalGroup R).subtype
    (TauCeti.QuadraticMap.orthogonalGroup R).subtype_injective).trans
    (MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _))

theorem lieModel_fixedComponentImage_six (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    (hx : OddOrderIsometry Q p x) (hd : finrank K (fixedSpace x) = 6)
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) (hK : 4 ≤ Nat.card K) {f : ℕ} (hf : 1 ≤ f)
    (hcard : Nat.card K = 2 ^ f) :
    LieModel (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) .PSL 4 2 f := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  obtain ⟨κ⟩ := CFSG.RankThree.PartOne.K159.Klein.klein_commutator_orthogonal_six
    (Q.comp (fixedSpace x).subtype) hWnd hd hT hK
  let φ₁ := fixedComponentImageEquiv hQ hx
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  have hZ : Subgroup.center ↥(orthDerived (Q.comp (fixedSpace x).subtype)) = ⊥ :=
    center_orthDerived_eq_bot hWnd hT
  have hZG : Subgroup.center ↥(fixedComponentImage Q x) = ⊥ := by
    have h1 := Subgroup.map_center_eq φ₁
    rw [hZ] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ₁.injective).mp h1
  let φ : ↥(fixedComponentImage Q x) ≃* ↥(StatedSL 4 K) :=
    φ₁.trans ((orthDerivedEquivCommutator _).symm.trans κ)
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (centerQuotientEquivSelf hZG).symm
    ((lieModel_classical_iff (by decide)).mpr ⟨⟨Nat.prime_two, hf, by norm_num,
      fun hc => absurd (Prod.mk.inj hc).1 (by norm_num),
      fun hc => absurd (Prod.mk.inj hc).1 (by norm_num)⟩, K, inferInstance, inferInstance, hcard,
      ⟨φ.trans statedSL4EquivStatedProj⟩⟩)

theorem exists_model_fixedComponentImage_high (hQ : (polarBilin Q).Nondegenerate) [Nontrivial V]
    (hx : OddOrderIsometry Q p x) (h6 : 6 ≤ finrank K (fixedSpace x))
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) (hK : 4 ≤ Nat.card K) {f₀ : ℕ}
    (hf₀ : 1 ≤ f₀) (hp : 1 ≤ p) (hcard : Nat.card K = 2 ^ (p * f₀)) :
    ∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(fixedComponentImage Q x) ⧸ Subgroup.center ↥(fixedComponentImage Q x)) t' n' 2
        (p * f') := by
  have hWnd := hx.polarBilin_fixed_nondegenerate
  obtain ⟨m, hm⟩ := hx.even_finrank_fixed
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp hf₀
  by_cases hm4 : 4 ≤ m
  · obtain ⟨t', n', h⟩ := exists_lieModel_quotient_of_orthDerived hWnd hm4 (by omega) hpf hcard
      (fixedComponentImageEquiv hQ hx)
    exact ⟨t', n', f₀, hf₀, h⟩
  · exact ⟨.PSL, 4, f₀, hf₀, lieModel_fixedComponentImage_six hQ hx (by omega) hT hK hpf hcard⟩

end Models

section Good

variable {K : Type} [Field K] [Finite K] [CharP K 2] {k : Subfield K} {σ : K ≃+* K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)}

theorem orth_good_high (hσk : ∀ c, c ∈ k ↔ σ c = c) (hext : IsExtension k Q₀ Q)
    (hQS : ∀ v, Q (coordinateFieldMap d σ v) = σ (Q v)) (hQ : (polarBilin Q).Nondegenerate)
    (hK : 4 ≤ Nat.card K) (hσ : ∃ c, σ c ≠ c) {α : MulAut (ProjOrthDerived Q)}
    (hα : ActsBySemilinear Q (coordinateFieldMap d σ) α) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {x : (Fin d → K) ≃ₗ[K] (Fin d → K)} (hxΩ : x ∈ orthDerived Q) (hx : OddOrderIsometry Q p x)
    (hSx : ∀ v, coordinateFieldMap d σ (x v) = x (coordinateFieldMap d σ v))
    (hmult : ∀ h ∈ primaryFactors x.toLinearMap, h ≠ X - 1 →
      primaryMultiplicity x.toLinearMap h ≤ 1) (h6 : 6 ≤ finrank K (fixedSpace x))
    (hT : ∃ U : Submodule K (fixedSpace x), finrank K U = 3 ∧
      ∀ u ∈ U, (Q.comp (fixedSpace x).subtype) u = 0) {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hcard : Nat.card K = 2 ^ (p * f₀)) :
    GoodConclusion p (ProjOrthDerived Q) α (piOrth Q ⟨x, hxΩ⟩) := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : Nontrivial (Fin d → K) := nontrivial_of_four_le_finrank_fixed (x := x) (by omega)
  have hWnd := hx.polarBilin_fixed_nondegenerate
  exact orth_good_of_single hQ hK hodd hσ (coordinateFieldMap d σ) (coordinateFieldMap_smul σ) hQS
    hα hxΩ hx hmult (by omega) (dicksonDerived_of_threeSingular _ hWnd hT)
    (hx.isQuasisimple_fixedComponentImage hT)
    (exists_model_fixedComponentImage_high hQ hx h6 hT hK hf₀ hp.one_lt.le hcard)
    (exists_rational_eichler_pair k hσk hext hQS hK hodd hx hx.pow_eq_one hSx (by omega))

end Good

end CFSG.RankThree.PartOne
