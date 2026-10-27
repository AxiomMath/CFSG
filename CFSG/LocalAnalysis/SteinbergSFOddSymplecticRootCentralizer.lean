module

public import CFSG.LocalAnalysis.SteinbergBTOddClassicalScalarQuotientSL2
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpLift
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBDescent
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBUnitaryAllDimensions
public import CFSG.LocalAnalysis.SteinbergCCCentralQuotientComponentLift
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentation
public import CFSG.LocalAnalysis.ComponentClassification.OddClassSelectorSpCert

public noncomputable section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

open Subgroup Module CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBAlternatingIsometry
open CFSG.ComponentClassification.CatalogueBSymplecticB
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent
open CFSG.ComponentClassification.CatalogueBOrthogonalDescent
open CFSG.ComponentClassification.CatalogueBSymplecticRepresentation
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Config

@[expose] def FixedRootConfig {P : Type*} [Group P] (β : MulAut P) (K : Type*) [Field K] : Prop :=
  ∃ S : Subgroup (fixedSubgroup β), S.Normal ∧ IsSimpleGroup S ∧ (∃ a b : S, a * b ≠ b * a) ∧
    Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
    Nat.card (fixedSubgroup β ⊓
      centralizer ((S.map (fixedSubgroup β).subtype : Subgroup P) : Set P) : Subgroup P) ≤ 2

theorem map_centralizer_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (T : Subgroup G) :
    (centralizer (T : Set G)).map e.toMonoidHom =
      centralizer ((T.map e.toMonoidHom : Subgroup H) : Set H) := by
  ext y
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨t, ht, rfl⟩
    have h' := congrArg e (h t ht)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h'
  · intro h t ht
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h (e t) ⟨t, ht, rfl⟩

theorem FixedRootConfig.of_mulEquiv {P P' : Type*} [Group P] [Group P'] {K : Type*} [Field K]
    (e : P ≃* P') {β : MulAut P} {β' : MulAut P'} (hint : ∀ x, e (β x) = β' (e x))
    (h : FixedRootConfig β K) : FixedRootConfig β' K := by
  obtain ⟨S, hSn, hSs, ⟨a, b, hab⟩, ⟨φ⟩, hcard⟩ := h
  have hfix := OddClassSelector.map_fixedSubgroup_of_comm e β β' hint
  let eF : fixedSubgroup β ≃* fixedSubgroup β' :=
    ((fixedSubgroup β).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hfix)
  let eS : S ≃* S.map eF.toMonoidHom := S.equivMapOfInjective eF.toMonoidHom eF.injective
  have hmapS : (S.map eF.toMonoidHom).map (fixedSubgroup β').subtype =
      (S.map (fixedSubgroup β).subtype).map e.toMonoidHom := by
    rw [map_map, map_map]
    rfl
  refine ⟨S.map eF.toMonoidHom, hSn.map _ eF.surjective, eS.symm.isSimpleGroup,
    ⟨eS a, eS b, fun h' => hab (eS.injective (by rw [map_mul, map_mul, h']))⟩,
    ⟨eS.symm.trans φ⟩, ?_⟩
  rw [hmapS, ← map_centralizer_mulEquiv, ← hfix, ← map_inf_eq _ _ _ e.injective,
    card_map_of_injective e.injective]
  exact hcard

theorem three_le_card {G : Type*} [Group G] {H : Subgroup G} [Finite H] {a b : G} (ha : a ∈ H)
    (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card H := by
  classical
  have := Fintype.ofFinite H
  have hcard : ({⟨1, H.one_mem⟩, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  rw [Nat.card_eq_fintype_card, ← hcard]
  exact Finset.card_le_univ _

end Config

section Lift

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
  {B : LinearMap.BilinForm F V}

theorem isComponentOf_map_subtype {G : Type*} [Group G] {H : Subgroup G} (S : Subgroup H)
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a) :
    CFSG.Assembly.IsComponentOf (S.map H.subtype) H := by
  rw [isComponentOf_iff_isComponent_subgroupOf (map_subtype_le S)]
  have hS : (S.map H.subtype).subgroupOf H = S :=
    comap_map_eq_self_of_injective H.subtype_injective S
  rw [hS]
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hSnab).1, hSn.isSubnormal⟩

theorem nonempty_quotient_map {Y L Q : Type*} [Group Y] [Group L] [Group Q] (ι : Y ≃* L)
    (A : Subgroup Y) [A.Normal] (e : Y ⧸ A ≃* Q) :
    (A.map ι.toMonoidHom).Normal ∧ ∃ _ : (A.map ι.toMonoidHom).Normal,
      Nonempty (L ⧸ A.map ι.toMonoidHom ≃* Q) := by
  have hn : (A.map ι.toMonoidHom).Normal := Subgroup.Normal.map inferInstance _ ι.surjective
  exact ⟨hn, hn, ⟨(QuotientGroup.congr A (A.map ι.toMonoidHom) ι rfl).symm.trans e⟩⟩

end Lift

section Field

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {B : LinearMap.BilinForm F V}

theorem field_case_false {ℓ e : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hF : Nat.card F = ℓ ^ e) {r : ℕ} (hr : 2 ≤ r) (hdim : finrank F V = 2 * r)
    (hB : B.IsAlt) (hnd : B.Nondegenerate) (σ : F ≃+* F) (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1)
    (τ₀ : V ≃+ V) (μ lam : Fˣ) (hsemi : ∀ a x, τ₀ (a • x) = σ a • τ₀ x)
    (hform : ∀ x y, B (τ₀ x) (τ₀ y) = (μ : F) * σ (B x y))
    (hsquare : ∀ x, τ₀ (τ₀ x) = (lam : F) • x) {Y : Subgroup (isometryGroup B)}
    (hY : CFSG.Assembly.IsComponentOf Y (semilinearSymplecticCentralizer B τ₀))
    (A : Subgroup Y) [A.Normal] (hAZ : ∀ a ∈ A, (a : isometryGroup B) ∈ scalarSigns B)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : CharP F ℓ := finite_field_prime_power_characteristic hℓ he hF
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq F ℓ]; exact hℓ2)
  obtain ⟨-, -, -, ⟨b, c, hb, hc⟩, hall⟩ := odd_symplectic_quadratic_semilinear_descent σ hσ2
    hσ1 h2 (by omega) B hB hnd τ₀ μ lam hsemi hform hsquare
  obtain ⟨-, -, -, -, hfin, hrank, -, hB0alt, hB0nd, -, eD, -, -, heD, -⟩ := hall b c hb hc
  obtain ⟨hcard0, -⟩ := CatalogueBOrthogonalInvolutionRepresentation.field_involution_facts hℓ he
    hF hσ2 hσ1
  have hk₀ : Nat.card (fixedSubfield F σ) = Nat.card {c : F // σ c = c} :=
    Nat.card_congr (Equiv.subtypeEquivRight (mem_fixedSubfield F σ))
  have hodd : Odd (Nat.card (fixedSubfield F σ)) := by
    have hFodd : Odd (Nat.card F) := by rw [hF]; exact (hℓ.odd_of_ne_two hℓ2).pow
    rw [hcard0, ← hk₀] at hFodd
    exact (Nat.odd_pow_iff two_ne_zero).mp hFodd
  have := hfin
  have hY₁ := (isComponentOf_iff_isComponent_subgroupOf hY.1).mp hY
  have hq := isometry_quasisimple_of_four_le _ hB0alt hB0nd (by rw [hrank]; omega) hodd
  have htop := OddClassSelector.eq_top_of_isComponent_of_quasisimple hq
    (isComponent_map_of_isComponent eD hY₁)
  have hYC : Y = semilinearSymplecticCentralizer B τ₀ := by
    refine le_antisymm hY.1 fun g hg => ?_
    have h1 : eD ⟨g, hg⟩ ∈ (Y.subgroupOf _).map eD.toMonoidHom := by
      rw [htop]
      trivial
    rw [mem_map_equiv, MulEquiv.symm_apply_apply] at h1
    exact h1
  let ι : Y ≃* isometryGroup _ := (MulEquiv.subgroupCongr hYC).trans eD
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hscal : ∀ g ∈ A.map ι.toMonoidHom, ∃ c : fixedSubfield F σ, ∀ w,
      (g : originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
        originalFixedSubspace σ τ₀ b hsemi) w = c • w := by
    rintro _ ⟨a, ha, rfl⟩
    have hval : ∀ w : originalFixedSubspace σ τ₀ b hsemi,
        (((ι a : isometryGroup _) : originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
          originalFixedSubspace σ τ₀ b hsemi) w : V) =
          ((a : isometryGroup B) : V ≃ₗ[F] V) (w : V) := fun w => heD _ w
    rcases hAZ a ha with h1 | h1
    · refine ⟨1, fun w => Subtype.ext ?_⟩
      change (((ι a : isometryGroup _) : originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
        originalFixedSubspace σ τ₀ b hsemi) w : V) = _
      rw [hval, h1, one_smul]
      rfl
    · refine ⟨-1, fun w => Subtype.ext ?_⟩
      change (((ι a : isometryGroup _) : originalFixedSubspace σ τ₀ b hsemi ≃ₗ[fixedSubfield F σ]
        originalFixedSubspace σ τ₀ b hsemi) w : V) = _
      rw [hval, h1, negIsometry_apply, neg_one_smul, Submodule.coe_neg]
  obtain ⟨-, -, hr1, -⟩ :=
    (SteinbergBT.odd_classical_scalar_quotients_even_SL2_small_exception hn K hK).2.2.1
    (fixedSubfield F σ) hodd _ _ hB0alt hB0nd r (by omega) (hrank.trans hdim)
    (A.map ι.toMonoidHom) hscal ⟨eQ'⟩
  omega

end Field

section Generic

theorem isometry_component_eq_top {k : Type} [Field k] [Finite k] (hodd : Odd (Nat.card k))
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {C : BilinForm k W}
    (hC : C.IsAlt) (hCnd : C.Nondegenerate) (hdim : 2 ≤ finrank k W)
    {L : Subgroup (isometryGroup C)} (hL : CFSG.IsComponent L) : L = ⊤ := by
  by_cases hex : finrank k W = 2 ∧ Nat.card k = 3
  · exfalso
    have : Group.IsSolvable (isometryGroup C) := plane_fieldThree_solvable C hC hCnd hex.1 hex.2
    have : Group.IsPerfect L := hL.1.1
    have : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    exact Group.IsPerfect.not_isSolvable L inferInstance
  · have hq := isometry_quasisimple C hC hCnd hdim hodd (by tauto)
    exact OddClassSelector.eq_top_of_isComponent_of_quasisimple hq hL

theorem sp_component_quotient {k : Type} [Field k] [Finite k] (hodd : Odd (Nat.card k))
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] {C : BilinForm k W}
    (hC : C.IsAlt) (hCnd : C.Nondegenerate) (hdim : 2 ≤ finrank k W) {H : Type*} [Group H]
    (Φ : H ≃* isometryGroup C) {Y : Subgroup H} (hY : CFSG.IsComponent Y) (A : Subgroup Y)
    [A.Normal] (hA : ∀ a ∈ A, ∃ c : k, ∀ w, ((Φ a : isometryGroup C) : W ≃ₗ[k] W) w = c • w)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    finrank k W = 2 ∧ Nat.card k = 5 ∧ Nat.card A = 2 := by
  have htop := isometry_component_eq_top hodd hC hCnd hdim (isComponent_map_of_isComponent Φ hY)
  let ι : Y ≃* isometryGroup C := (Y.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hscal : ∀ g ∈ A.map ι.toMonoidHom, ∃ c : k, ∀ w, (g : W ≃ₗ[k] W) w = c • w := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA a ha
  obtain ⟨m, hm⟩ := even_finrank C hC hCnd
  obtain ⟨-, h5, hr1, hcardA, -⟩ :=
    (SteinbergBT.odd_classical_scalar_quotients_even_SL2_small_exception hn K hK).2.2.1 k hodd
      W C hC hCnd m (by omega) (by omega) (A.map ι.toMonoidHom) hscal ⟨eQ'⟩
  refine ⟨by omega, h5, ?_⟩
  rw [← hcardA, card_map_of_injective ι.injective]

theorem gl_component_quotient {k : Type} [Field k] [Finite k] (hodd : Odd (Nat.card k)) {m : ℕ}
    (hm : 2 ≤ m) {H : Type*} [Group H] (Φ : H ≃* GL (Fin m) k) {Y : Subgroup H}
    (hY : CFSG.IsComponent Y) (A : Subgroup Y) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : k, ((Φ a : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = c • 1)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    m = 2 ∧ Nat.card k = 5 ∧
      Y.map Φ.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange m k := by
  have hL' := isComponent_map_of_isComponent Φ hY
  have : Group.IsPerfect (Y.map Φ.toMonoidHom) := hL'.1.1
  have : Nontrivial (Y.map Φ.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  have hSL : Y.map Φ.toMonoidHom = CatalogueBGeneralLinear.specialLinearRange m k := by
    by_cases hs : m = 1 ∨ m = 2 ∧ (Nat.card k = 2 ∨ Nat.card k = 3)
    · exfalso
      have : Group.IsSolvable (GL (Fin m) k) :=
        CatalogueBGeneralLinear.generalLinear_small_solvable m k hs
      exact Group.IsPerfect.not_isSolvable (Y.map Φ.toMonoidHom) inferInstance
    · obtain ⟨hm2, h22, h23⟩ := CatalogueBGeneralLinear.retained_parameters m k (by omega) hs
      exact CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange m k hm2 h22 h23 _
        hL'.2
  let ι : Y ≃* Matrix.SpecialLinearGroup (Fin m) k :=
    (Y.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans ((MulEquiv.subgroupCongr hSL).trans
      (CatalogueBGeneralLinear.specialLinearEquivRange m k).symm)
  have hιval : ∀ y : Y, ((ι y : Matrix.SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) =
      ((Φ y : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
    intro y
    have h1 : (CatalogueBGeneralLinear.specialLinearEquivRange m k (ι y)).val =
        Φ (y : H) := by
      change (CatalogueBGeneralLinear.specialLinearEquivRange m k
        ((CatalogueBGeneralLinear.specialLinearEquivRange m k).symm _)).val = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [CatalogueBGeneralLinear.specialLinearEquivRange_val] at h1
    exact congrArg (fun g : GL (Fin m) k => (g : Matrix (Fin m) (Fin m) k)) h1
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
  have hscal : A.map ι.toMonoidHom ≤ LinearFlag.scalars m k := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, hc⟩ := hA a ha
    have hdet : c ^ m = 1 := by
      have h1 := (ι a).2
      rw [hιval, hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
      exact h1
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [zero_pow (by omega)] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 c hc0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet,
      Units.val_one]), ?_⟩
    change ((ι a : Matrix.SpecialLinearGroup (Fin m) k) : Matrix (Fin m) (Fin m) k) = _
    rw [hιval, hc, Units.val_mk0, Matrix.smul_one_eq_diagonal]
    rfl
  obtain ⟨-, h5, hm2, -⟩ :=
    SteinbergBT.linear_scalar_quotient_SL2 hodd hn K hK hm (A.map ι.toMonoidHom) hscal eQ'
  exact ⟨hm2, h5, hSL⟩

theorem unitary_component_quotient {E : Type} [Field E] [Finite E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] {ℓ e : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e)
    (hE : Nat.card E = (ℓ ^ e) ^ 2) {sigma : E ≃+* E} (hsig : ∀ x, sigma x = x ^ (ℓ ^ e))
    (h : V →ₛₗ[sigma.toRingHom] V →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hdim : 1 ≤ finrank E V) {H : Type*} [Group H]
    (Φ : H ≃* CatalogueBUnitaryIsometry.isometryGroup h) {Y : Subgroup H}
    (hY : CFSG.IsComponent Y) (A : Subgroup Y) [A.Normal]
    (hA : ∀ a ∈ A, ∃ c : E, ∀ v,
      ((Φ a : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) v = c • v)
    {K : Type*} [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y ⧸ A ≃* Matrix.SpecialLinearGroup (Fin 2) K) : finrank E V = 2 ∧ ℓ ^ e = 5 := by
  obtain rfl : sigma = CatalogueBUnitaryTwo.unitaryFieldConjugation ℓ e hE :=
    RingEquiv.ext fun x => by rw [hsig, CatalogueBUnitaryTwo.unitaryFieldConjugation_apply]
  obtain ⟨-, hsmall, hnonsmall⟩ :=
    CatalogueBUnitaryTwo.odd_unitary_all_dimensional_isometry_p_components ℓ e hℓ2 he hE h hsym
      hnd hdim
  have hL' := isComponent_map_of_isComponent Φ hY
  have : Group.IsPerfect (Y.map Φ.toMonoidHom) := hL'.1.1
  have : Nontrivial (Y.map Φ.toMonoidHom) := CFSG.LocalCores.isQuasisimple_nontrivial hL'.1
  by_cases hs : finrank E V = 1 ∨ (finrank E V, ℓ ^ e) = (2, 3)
  · exfalso
    obtain ⟨hsolv, -⟩ := hsmall hs
    exact Group.IsPerfect.not_isSolvable (Y.map Φ.toMonoidHom) inferInstance
  · push Not at hs
    obtain ⟨hq, -⟩ := hnonsmall hs
    have : Finite V := Module.finite_of_finite E
    have : Finite (V ≃ₗ[E] V) :=
      Finite.of_injective (fun g : V ≃ₗ[E] V => (g : V → V)) DFunLike.coe_injective
    have hsolv : Group.IsSolvable (CatalogueBUnitaryIsometry.isometryGroup h ⧸
        CatalogueBUnitaryIsometry.specialIsometry h) :=
      Group.isSolvable_of_isSolvable_injective
        (QuotientGroup.kerLift_injective (CatalogueBUnitaryIsometry.isometryDeterminant h))
    have hSU : Y.map Φ.toMonoidHom = CatalogueBUnitaryIsometry.specialIsometry h :=
      CentralQuotientLift.component_eq_of_quasisimple_normal _ hq hsolv hL'
    let ι : Y ≃* CatalogueBUnitaryIsometry.specialIsometry h :=
      (Y.equivMapOfInjective Φ.toMonoidHom Φ.injective).trans (MulEquiv.subgroupCongr hSU)
    obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A eQ
    have hscal : ∀ g ∈ A.map ι.toMonoidHom, ∃ c : E, ∀ v,
        ((g : CatalogueBUnitaryIsometry.isometryGroup h) : V ≃ₗ[E] V) v = c • v := by
      rintro _ ⟨a, ha, rfl⟩
      exact hA a ha
    obtain ⟨-, h5, hd2, -⟩ :=
      (SteinbergBT.odd_classical_scalar_quotients_even_SL2_small_exception hn K hK).2.1 ℓ e hℓ2
        he E hE V h hsym hnd (by omega) (A.map ι.toMonoidHom) hscal ⟨eQ'⟩
    exact ⟨hd2, h5⟩

end Generic

section Linear

variable {F : Type} [Field F] [Finite F] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {B : LinearMap.BilinForm F V}

theorem split_half_false (hodd : Odd (Nat.card F)) (h2 : (2 : F) ≠ 0) (hB : B.IsAlt)
    {M W : Submodule F V} (hMnd : (B.domRestrict₁₂ M M).Nondegenerate) (hM0 : M ≠ ⊥)
    (hW0 : W ≠ ⊥) {C : Subgroup (isometryGroup B)} {Y₁ : Subgroup C}
    (ρ : Y₁ →* isometryGroup (B.domRestrict₁₂ M M)) (hρi : Function.Injective ρ)
    (hρc : CFSG.IsComponent ρ.range)
    (hYW : ∀ y ∈ Y₁, ∀ w ∈ W, ((y : isometryGroup B) : V ≃ₗ[F] V) w = w) (A₁ : Subgroup Y₁)
    [A₁.Normal] (hA₁Z : ∀ a ∈ A₁, ((a : C) : isometryGroup B) ∈ scalarSigns B) {K : Type*}
    [Field K] {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (eQ : Y₁ ⧸ A₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  have hMalt : (B.domRestrict₁₂ M M).IsAlt := fun x => hB x
  have hA₁ : A₁ = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall A₁).mpr fun a ha => ?_
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
    rcases hA₁Z a ha with h | h
    · exact Subtype.ext (Subtype.ext h)
    · exfalso
      have h1 := hYW (a : C) a.2 w hwW
      rw [h, negIsometry_apply] at h1
      apply hw0
      have h3 : (2 : F) • w = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; exact neg_add_cancel w
      exact (smul_eq_zero.mp h3).resolve_left h2
  obtain ⟨m, hm⟩ := even_finrank _ hMalt hMnd
  have : Nontrivial M := Submodule.nontrivial_iff_ne_bot.mpr hM0
  have hMpos : 0 < finrank F M := Module.finrank_pos
  let ι : Y₁ ≃* ρ.range := MonoidHom.ofInjective hρi
  obtain ⟨-, hn', ⟨eQ'⟩⟩ := nonempty_quotient_map ι A₁ eQ
  have hbot : A₁.map ι.toMonoidHom = ⊥ := by rw [hA₁, Subgroup.map_bot]
  obtain ⟨-, -, hcard⟩ := sp_component_quotient hodd hMalt hMnd (by omega) (MulEquiv.refl _) hρc
    (A₁.map ι.toMonoidHom) (fun a ha => ⟨1, fun w => by
      rw [hbot, Subgroup.mem_bot] at ha
      rw [ha, one_smul]
      rfl⟩) hn hK eQ'
  rw [hbot, Subgroup.card_bot] at hcard
  omega

end Linear

end CFSG.LocalAnalysis.SymplecticFourStandard
