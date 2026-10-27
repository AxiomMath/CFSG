module

public import CFSG.Quasithin.H13.NQBlockTwoPrimeConfine
public import CFSG.Quasithin.SteinbergCCSylowNormalizerBootstrap
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Transport
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Witness

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_residualAction_subgroupOf_equiv {L X : Subgroup G} (hXL : X ≤ L)
    [(X.subgroupOf L).Characteristic] :
    ∃ Θ : (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) ⧸
        frattini (X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L)) ≃* WPlane X,
      ∀ (l : L) (hn : (l : G) ∈ normalizer (X : Set G)) w,
        Θ (residualAction (X.subgroupOf L) l w) = normalizerFrattiniConj X ⟨l, hn⟩ (Θ w) := by
  let e₁ : X.subgroupOf L ≃* X := subgroupOfEquivOfLe hXL
  let e₂ : X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  let Θ := QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)
  refine ⟨Θ, fun l hn w => ?_⟩
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
  rfl

theorem isOddResidualWitness_subgroupOf {L X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype) (hXc : (X.subgroupOf L).Characteristic)
    (hX2 : NoPQuotient 2 X) (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X))
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) :
    IsOddResidualWitness p (X.subgroupOf L) := by
  have hp : p.Prime := Fact.out
  have hXL : X ≤ L := hXR.trans (Subgroup.map_subtype_le _)
  have hLX : L ≤ normalizer (X : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (X.subgroupOf L)
    rw [map_subgroupOf_eq_of_le hXL] at h1
    exact Subgroup.le_normalizer.trans h1
  let e₁ : X.subgroupOf L ≃* X := subgroupOfEquivOfLe hXL
  let e₂ : X.subgroupOf L ⧸ CFSG.pCore 2 (X.subgroupOf L) ≃* X ⧸ CFSG.pCore 2 X :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  obtain ⟨Θ, hΘ⟩ := exists_residualAction_subgroupOf_equiv hXL
  refine ⟨hXc, ?_, CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective
    e₁.symm.toMonoidHom e₁.symm.surjective hX2, IsPGroup.of_equiv hXp e₂.symm,
    (Monoid.exponent_eq_of_mulEquiv e₂).trans hexp,
    (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e₂ p).trans hrank,
    (Nat.card_congr Θ.toEquiv).trans hW, ?_, ?_⟩
  · intro x hx
    obtain ⟨r, hr, hrx⟩ := hXR hx
    have hrx' : r = x := Subtype.ext hrx
    rw [← hrx']
    exact hr
  · intro h1
    obtain ⟨l, hlL, hl1⟩ := hLW
    apply hl1
    refine MulEquiv.ext fun w => ?_
    have h2 := hΘ ⟨l, hlL⟩ l.2 (Θ.symm w)
    rw [h1, MonoidHom.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply] at h2
    exact h2.symm
  · intro U hU
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hV := hirr (U.map Θ.toMonoidHom) (by
      rintro l hlL _ ⟨u, hu, rfl⟩
      exact ⟨_, hall ⟨l, hlL⟩ u hu, hΘ ⟨l, hlL⟩ l.2 u⟩)
    have hcard : Nat.card (U.map Θ.toMonoidHom) = p := by
      rw [Subgroup.card_map_of_injective Θ.injective, hU]
    rcases hV with h0 | h1
    · rw [h0, Subgroup.card_bot] at hcard
      exact hp.one_lt.ne hcard
    · rw [h1, Subgroup.card_top, hW] at hcard
      have h3 : p * p = p * 1 := by
        rw [mul_one, ← sq]
        exact hcard
      exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos h3)

theorem IsOddResidualWitness.map_mulEquiv {L₁ L₂ : Type*} [Group L₁] [Finite L₁] [Group L₂]
    [Finite L₂] {p : ℕ} [Fact p.Prime] {X : Subgroup L₁} (hX : IsOddResidualWitness p X)
    (φ : L₁ ≃* L₂) : IsOddResidualWitness p (X.map φ.toMonoidHom) := by
  have := hX.characteristic
  have hc : (X.map φ.toMonoidHom).Characteristic := characteristic_map_mulEquiv φ hX.characteristic
  let e₁ : X ≃* X.map φ.toMonoidHom := X.equivMapOfInjective φ.toMonoidHom φ.injective
  let e₂ : X ⧸ CFSG.pCore 2 X ≃* X.map φ.toMonoidHom ⧸ CFSG.pCore 2 (X.map φ.toMonoidHom) :=
    QuotientGroup.congr _ _ e₁ (CFSG.pCore_map_iso 2 e₁)
  let Θ := QuotientGroup.congr _ _ e₂ (map_frattini_mulEquiv e₂)
  have hΘ : ∀ (l : L₁) w, Θ (residualAction X l w) =
      @residualAction L₂ _ (X.map φ.toMonoidHom) hc (φ l) (Θ w) := by
    intro l w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective w
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective v
    have key : e₁ (MulAut.conjNormal l x) = @MulAut.conjNormal L₂ _ (X.map φ.toMonoidHom)
        (Subgroup.normal_of_characteristic _) (φ l) (e₁ x) := by
      apply Subtype.ext
      show φ.toMonoidHom ((l : L₁) * (x : L₁) * l⁻¹) = φ l * φ.toMonoidHom (x : L₁) * (φ l)⁻¹
      rw [map_mul, map_mul, map_inv]
      rfl
    exact congrArg (fun y : X.map φ.toMonoidHom =>
      (((y : X.map φ.toMonoidHom ⧸ CFSG.pCore 2 (X.map φ.toMonoidHom))) :
        (X.map φ.toMonoidHom ⧸ CFSG.pCore 2 (X.map φ.toMonoidHom)) ⧸
          frattini (X.map φ.toMonoidHom ⧸ CFSG.pCore 2 (X.map φ.toMonoidHom)))) key
  refine ⟨hc, ?_, CFSG.QuasithinUnique.Setup.Campbell.NoPQuotient.of_surjective e₁.toMonoidHom
    e₁.surjective hX.noTwoQuotient, hX.isPGroup.of_equiv e₂,
    (Monoid.exponent_eq_of_mulEquiv e₂.symm).trans hX.exponent,
    (CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv e₂.symm p).trans hX.pRank,
    (Nat.card_congr Θ.toEquiv).symm.trans hX.card_W, ?_, ?_⟩
  · rw [← CFSG.LieType.SteinbergBR.solvableRadical_map_equiv φ]
    exact Subgroup.map_mono hX.le_rad
  · intro h1
    apply hX.nontrivial
    refine MonoidHom.ext fun l => MulEquiv.ext fun w => ?_
    have h2 := hΘ l w
    rw [h1, MonoidHom.one_apply, MulAut.one_apply] at h2
    exact Θ.injective h2
  · intro U hU
    have hU' : Nat.card (U.comap Θ.toMonoidHom) = p := by
      rw [Subgroup.comap_equiv_eq_map_symm',
        Subgroup.card_map_of_injective (f := Θ.symm.toMonoidHom) Θ.symm.injective, hU]
    obtain ⟨l, u, hu, hnot⟩ := hX.irreducible (U.comap Θ.toMonoidHom) hU'
    refine ⟨φ l, Θ u, hu, fun h => hnot ?_⟩
    change Θ (residualAction X l u) ∈ U
    rw [hΘ]
    exact h

end Witness

section Control

open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isMaximalTwoLocal_iff_maxTwoLocal {M : Subgroup G} :
    CFSG.IsMaximalTwoLocal M ↔ quasithinIsMaxTwoLocal M := by
  constructor
  · rintro ⟨hM, hmax⟩
    refine ⟨hM, fun H hH hMH => ?_⟩
    by_contra hne
    exact hmax H (lt_of_le_of_ne hMH (Ne.symm hne)) hH
  · rintro ⟨hM, hmax⟩
    exact ⟨hM, fun H hMH hH => hMH.ne (hmax H hH hMH.le).symm⟩

theorem maximalTwoLocalsContaining_join_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    CFSG.maximalTwoLocalsContaining ((L ⊔ T : Subgroup G) : Set G) = {M} := by
  ext M'
  simp only [CFSG.maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hM', hsub⟩
    exact h.join_unique M' (isMaximalTwoLocal_iff_maxTwoLocal.mp hM')
      (SetLike.coe_subset_coe.mp hsub)
  · rintro rfl
    exact ⟨isMaximalTwoLocal_iff_maxTwoLocal.mpr h.max_two_local,
      SetLike.coe_subset_coe.mpr h.join_le⟩

theorem generalizedFitting_eq_pCore_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    CFSG.generalizedFitting L = CFSG.pCore 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := (quasithinGenFitting_eq_pCoreOf_iff L 2).mp h.faithful_local.2.2.1
  have h2 := (CFSG.Quasithin.centralizer_pCore_le_iff_pCoreOf 2 L).mpr h1
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore L 2).mp h2

theorem exists_prime_ne_of_fittingSubgroup_ne {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    [Fact p.Prime] (h : CFSG.fittingSubgroup Q ≠ CFSG.pCore p Q) :
    ∃ q ∈ (Nat.card (CFSG.fittingSubgroup Q)).primeFactors, q ≠ p := by
  by_contra hall
  simp only [not_exists, not_and, not_not] at hall
  apply h
  apply le_antisymm
  · have hne : Nat.card (CFSG.fittingSubgroup Q) ≠ 0 := Nat.card_pos.ne'
    have hF : IsPGroup p (CFSG.fittingSubgroup Q) :=
      IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hne fun {d} hd hdvd =>
        hall d (Nat.mem_primeFactors.mpr ⟨hd, hdvd, hne⟩))
    exact CFSG.Quasithin.SteinbergCC.le_pCore_of_normal_of_isPGroup inferInstance hF
  · exact CFSG.pCore_le_fitting Q p

omit [Finite G] in
theorem characteristic_map_subtype_subgroupOf {B : Subgroup G} {R C : Subgroup B}
    (hCc : (C.subgroupOf R).Characteristic) :
    ((C.map B.subtype).subgroupOf (R.map B.subtype)).Characteristic := by
  let ψR : R ≃* R.map B.subtype := R.equivMapOfInjective B.subtype B.subtype_injective
  have hmap : (C.subgroupOf R).map ψR.toMonoidHom =
      (C.map B.subtype).subgroupOf (R.map B.subtype) := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨(r : B), hr, rfl⟩
    · rintro ⟨c, hc, hcx⟩
      refine ⟨ψR.symm x, ?_, ψR.apply_symm_apply x⟩
      have h1 : (((ψR.symm x : R) : B) : G) = (x : G) :=
        congrArg (fun y : R.map B.subtype => (y : G)) (ψR.apply_symm_apply x)
      have h2 : ((ψR.symm x : R) : B) = c := Subtype.ext (h1.trans hcx.symm)
      change ((ψR.symm x : R) : B) ∈ C
      rw [h2]
      exact hc
  rw [← hmap]
  exact characteristic_map_mulEquiv ψR hCc

theorem confine_of_two_primes (h39 : SQTKCLayerPerfectResidual)
    (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXL : X ≤ L) (hXw : IsOddResidualWitness p (X.subgroupOf L))
    (hNX : normalizer (X : Set G) = M) {q : ℕ}
    (hqF : q ∈ (Nat.card (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L))).primeFactors)
    (hqp : q ≠ p) : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  have hLH : L ≤ L ⊔ T := le_sup_left
  have hTH : T ≤ L ⊔ T := le_sup_right
  have hTL : T ≤ normalizer (L : Set G) := h.t_le.trans h.eq_normalizer.le
  have hLHn : (L.subgroupOf (L ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr (sup_le Subgroup.le_normalizer hTL)
  have hLT : L.subgroupOf (L ⊔ T) ⊔ T.subgroupOf (L ⊔ T) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLH hTH, Subgroup.subgroupOf_self]
  let φ : L ≃* L.subgroupOf (L ⊔ T) := (subgroupOfEquivOfLe hLH).symm
  have hSQT : CFSG.IsStronglyQuasithin (L.subgroupOf (L ⊔ T)) :=
    CFSG.SectionRank.isStronglyQuasithin_of_mulEquiv φ.symm (isStronglyQuasithin_L_of_qtnq h)
  have hLC : CFSG.IsCComponent (⊤ : Subgroup (L.subgroupOf (L ⊔ T))) := by
    have h1 : L ∈ cComp L := cComp_mem_of_le h.maximal_local.1.2.1 le_rfl le_sup_left
    have h3 := mem_cComp_top_iff_isCComponent.mp
      (subgroupOf_mem_cComp (subgroupOf_mem_cComp_of_le hLH h1))
    rwa [Subgroup.subgroupOf_self] at h3
  have hq' : ¬ CFSG.IsQuasisimple (L.subgroupOf (L ⊔ T) ⧸ CFSG.pCore 2 (L.subgroupOf (L ⊔ T))) := by
    intro hq
    apply h.not_quasisimple
    exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ))).2 hq
  have hF : CFSG.generalizedFitting (L.subgroupOf (L ⊔ T)) =
      CFSG.pCore 2 (L.subgroupOf (L ⊔ T)) := by
    rw [← CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv φ,
      generalizedFitting_eq_pCore_of_qtnq h, CFSG.pCore_map_iso 2 φ]
  have hXw' : IsOddResidualWitness p ((X.subgroupOf L).map φ.toMonoidHom) :=
    hXw.map_mulEquiv φ
  let ψ : L ⧸ CFSG.pCore 2 L ≃* L.subgroupOf (L ⊔ T) ⧸ CFSG.pCore 2 (L.subgroupOf (L ⊔ T)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  have hqF' : q ∈ (Nat.card (CFSG.fittingSubgroup
      (L.subgroupOf (L ⊔ T) ⧸ CFSG.pCore 2 (L.subgroupOf (L ⊔ T))))).primeFactors := by
    rw [← CFSG.SignalizerFunctorTheorem.McBride.fittingSubgroup_map_equiv ψ,
      Subgroup.card_map_of_injective (f := ψ.toMonoidHom) ψ.injective]
    exact hqF
  obtain ⟨⟨A, hA12, hXA, hXqA⟩, hconfine⟩ :=
    original_two_prime_capture_confines_the_same_characteristic_normalizer_of h39 h2
      h.nonabelian h.qtke h.sylow hTH hLT hSQT hLC hq' hF hp5 hXw' hqF' hqp _ _ _ _ rfl rfl rfl
      rfl
  have hT' := quasithinIsSylowTwo_subgroupOf h.sylow hTH
  let T' : Sylow 2 ↥(L ⊔ T) := hT'.1.toSylow hT'.2
  have hLT' : L.subgroupOf (L ⊔ T) ⊔ (T' : Subgroup ↥(L ⊔ T)) = ⊤ := hLT
  obtain ⟨-, -, -, -, hC₁R, hC₁c, -, hC₂R, hC₂c, -⟩ :=
    original_multiple_prime_radical_captures_two_primes_in_actual_characteristic_normalizer
      hSQT hLC T' hLT' hq' hF hp5 hXw' hqF' hqp _ _ _ _ rfl rfl rfl rfl
  have hXG : (((X.subgroupOf L).map φ.toMonoidHom).map (L.subgroupOf (L ⊔ T)).subtype).map
      (L ⊔ T).subtype = X := by
    rw [Subgroup.map_map, Subgroup.map_map]
    have he : ((L ⊔ T).subtype.comp (L.subgroupOf (L ⊔ T)).subtype).comp φ.toMonoidHom =
        L.subtype := by
      ext x
      rfl
    rw [he, map_subgroupOf_eq_of_le hXL]
  have hRG : ((CFSG.pCore 2 (((X.subgroupOf L).map φ.toMonoidHom).map
      (L.subgroupOf (L ⊔ T)).subtype ⊔ T.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T))).map
        (((X.subgroupOf L).map φ.toMonoidHom).map (L.subgroupOf (L ⊔ T)).subtype ⊔
          T.subgroupOf (L ⊔ T)).subtype).map (L ⊔ T).subtype = pCoreOf 2 (X ⊔ T) := by
    have h1 := pCoreOf_map_subtype (H := L ⊔ T) (((X.subgroupOf L).map φ.toMonoidHom).map
      (L.subgroupOf (L ⊔ T)).subtype ⊔ T.subgroupOf (L ⊔ T))
    unfold CFSG.Open.pCoreOf at h1
    rw [h1, Subgroup.map_sup, map_subgroupOf_eq_of_le hTH, hXG]
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hconfC : ∀ C : Subgroup ↥(L ⊔ T), C ≤ (CFSG.pCore 2 (((X.subgroupOf L).map
      φ.toMonoidHom).map (L.subgroupOf (L ⊔ T)).subtype ⊔ T.subgroupOf (L ⊔ T) :
        Subgroup ↥(L ⊔ T))).map (((X.subgroupOf L).map φ.toMonoidHom).map
          (L.subgroupOf (L ⊔ T)).subtype ⊔ T.subgroupOf (L ⊔ T)).subtype →
      (C.subgroupOf ((CFSG.pCore 2 (((X.subgroupOf L).map φ.toMonoidHom).map
        (L.subgroupOf (L ⊔ T)).subtype ⊔ T.subgroupOf (L ⊔ T) : Subgroup ↥(L ⊔ T))).map
          (((X.subgroupOf L).map φ.toMonoidHom).map (L.subgroupOf (L ⊔ T)).subtype ⊔
            T.subgroupOf (L ⊔ T)).subtype)).Characteristic →
      normalizer ((C.map (L ⊔ T).subtype : Subgroup G) : Set G) ≤ normalizer (X : Set G) →
      normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ M := by
    intro C hCR hCc hNC
    have hc := characteristic_map_subtype_subgroupOf hCc
    rw [hRG] at hc
    have hCG : C.map (L ⊔ T).subtype ≤ pCoreOf 2 (X ⊔ T) := (Subgroup.map_mono hCR).trans hRG.le
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      ((C.map (L ⊔ T).subtype).subgroupOf (pCoreOf 2 (X ⊔ T)))
    rw [map_subgroupOf_eq_of_le hCG] at h1
    exact h1.trans (hNC.trans hNX.le)
  have hXeq : normalizer ((((((X.subgroupOf L).map φ.toMonoidHom).map
      (L.subgroupOf (L ⊔ T)).subtype).map (L ⊔ T).subtype : Subgroup G)) : Set G) =
        normalizer (X : Set G) := by
    rw [hXG]
  rcases hA12 with hA | hA
  · exact hconfC _ hC₁R hC₁c ((hconfine _ A (Or.inl ⟨rfl, hA⟩) hXA hXqA).trans hXeq.le)
  · exact hconfC _ hC₂R hC₂c ((hconfine _ A (Or.inr ⟨rfl, hA⟩) hXA hXqA).trans hXeq.le)

theorem original_radical_normalizer_and_core_control_before_same_witness_singleton_of
    (h39 : SQTKCLayerPerfectResidual) (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    {T L M : Subgroup G} (h : QTNQ T L M) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {X : Subgroup G} (hXR : X ≤ (CFSG.solvableRadical L).map L.subtype)
    (hXc : (X.subgroupOf L).Characteristic) (hO2X : CFSG.pCore 2 X ≠ ⊥) (hX2 : NoPQuotient 2 X)
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrank : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) (hW : Nat.card (WPlane X) = p ^ 2)
    (hLW : ∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1)
    (hirr : ∀ V : Subgroup (WPlane X),
      (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
        V = ⊥ ∨ V = ⊤) :
    normalizer (X : Set G) = M ∧ normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ M ∧
      pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) ∧
      IsSylowOf 2 (pCoreOf 2 (X ⊔ T)) (⨆ m ∈ M, CFSG.conjugate (pCoreOf 2 (X ⊔ T)) m) ∧
      (∀ B : Subgroup G, IsPGroup 2 B → X ≤ normalizer (B : Set G) → pCoreOf 2 (X ⊔ T) ≤ B →
        B = pCoreOf 2 (X ⊔ T)) ∧
      (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L) = CFSG.pCore p (L ⧸ CFSG.pCore 2 L) →
        ⁅pCoreOf 2 (X ⊔ T), L⁆ ≤ pCoreOf 2 L ∧
        ((pCoreOf 2 (X ⊔ T)).subgroupOf (L ⊔ T)).Normal ∧
        ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
          (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → normalizer (D : Set G) ≤ M) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have := h.simple
  have hXL : X ≤ L := hXR.trans (Subgroup.map_subtype_le _)
  have hLM : L ≤ M := h.l_le
  have hTM : T ≤ M := h.t_le
  have hML : M ≤ normalizer (L : Set G) := h.eq_normalizer.le
  have hTL : T ≤ normalizer (L : Set G) := hTM.trans hML
  have hMX : M ≤ normalizer (X : Set G) := by
    have h1 := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (X.subgroupOf L)
    rw [map_subgroupOf_eq_of_le hXL] at h1
    exact hML.trans h1
  have hNX : normalizer (X : Set G) = M := by
    have hQ1 : (CFSG.pCore 2 X).map X.subtype ≠ ⊥ := fun hb =>
      hO2X ((Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hb)
    have hQ2 : IsPGroup 2 ((CFSG.pCore 2 X).map X.subtype) := CFSG.pCore_isPGroup.map _
    have hXQ : normalizer (X : Set G) ≤ normalizer (((CFSG.pCore 2 X).map X.subtype :
        Subgroup G) : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.pCore 2 X)
    have heq := h.max_two_local.2 _ ⟨_, hQ1, hQ2, rfl⟩ (hMX.trans hXQ)
    exact le_antisymm (hXQ.trans heq.le) hMX
  have hXw : IsOddResidualWitness p (X.subgroupOf L) :=
    isOddResidualWitness_subgroupOf hXR hXc hX2 hXp hexp hrank hW hLW hirr
  let eXL : X.subgroupOf L ≃* X := subgroupOfEquivOfLe hXL
  have hO2X' : CFSG.pCore 2 (X.subgroupOf L) ≠ ⊥ := by
    intro hb
    apply hO2X
    rw [← CFSG.pCore_map_iso 2 eXL, hb, Subgroup.map_bot]
  have hXLmap : (X.subgroupOf L).map L.subtype = X := map_subgroupOf_eq_of_le hXL
  have hTs : IsSylowOf 2 T (L ⊔ T) := CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨le_sup_right,
    h.sylow.1, fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
  have hSQT := isStronglyQuasithin_L_of_qtnq h
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  have hMLT := maximalTwoLocalsContaining_join_of_qtnq h
  have hR' : pCoreOf 2 (X ⊔ T) = (CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  have hsingle : CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L) = CFSG.pCore p (L ⧸ CFSG.pCore 2 L) →
      ⁅pCoreOf 2 (X ⊔ T), L⁆ ≤ pCoreOf 2 L ∧
        ((pCoreOf 2 (X ⊔ T)).subgroupOf (L ⊔ T)).Normal ∧
        ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
          (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → normalizer (D : Set G) ≤ M := by
    intro hFQ
    obtain ⟨-, -, hRL, hRLT, hLTR, hconf⟩ :=
      single_odd_prime_radical_gives_pre_singleton_characteristic_normalizer_control hTL hTs hSQT
        hLC h.not_quasisimple hp5 hXw hO2X' hFQ
    rw [hXLmap] at hRL hRLT hLTR hconf
    obtain ⟨hD, -⟩ := hconf M hMLT
    rw [← hR'] at hRL hRLT hLTR hD
    refine ⟨?_, (Subgroup.normal_subgroupOf_iff_le_normalizer hRLT).mpr hLTR,
      fun D hD1 hDR hDc => hD D hDR hDc hD1⟩
    have hN : (CFSG.pCore 2 L).map L.subtype = pCoreOf 2 L := by
      unfold CFSG.Open.pCoreOf
      try with_reducible rfl
    rwa [hN] at hRL
  have hconf : normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ M := by
    by_cases hFQ : CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L) =
        CFSG.pCore p (L ⧸ CFSG.pCore 2 L)
    · obtain ⟨-, -, -, -, -, hconf⟩ :=
        single_odd_prime_radical_gives_pre_singleton_characteristic_normalizer_control hTL hTs
          hSQT hLC h.not_quasisimple hp5 hXw hO2X' hFQ
      have h3 := (hconf M hMLT).2
      rw [hXLmap, ← hR'] at h3
      exact h3
    · obtain ⟨q, hqF, hqp⟩ := exists_prime_ne_of_fittingSubgroup_ne hFQ
      exact confine_of_two_primes h39 h2 h hp5 hXL hXw hNX hqF hqp
  have hXMn : (X.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hXL.trans hLM)).mpr hMX
  have hTsM : IsSylowOf 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hTM, h.sylow.1,
    fun h2 => h.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hTM))⟩
  have hconf' : normalizer (((CFSG.pCore 2 (X ⊔ T : Subgroup G)).map (X ⊔ T).subtype :
      Subgroup G) : Set G) ≤ M := by
    rw [← hR']
    exact hconf
  obtain ⟨-, -, -, -, -, hRN, hRS, -, hRB⟩ :=
    CFSG.Quasithin.SteinbergCC.prime_residual_sylow_normalizer_core_bootstrap Nat.prime_two
      (hXL.trans hLM) hXMn hX2 hTsM hconf'
  rw [← hR'] at hRN hRS hRB
  refine ⟨hNX, hconf, ?_, hRS, hRB, hsingle⟩
  have hN : (CFSG.pCore 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G) : Subgroup G)).map
      (normalizer (pCoreOf 2 (X ⊔ T) : Set G)).subtype =
        pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) := by
    unfold CFSG.Open.pCoreOf
    try with_reducible rfl
  rw [← hN]
  exact hRN.symm

@[expose] def StmtOriginalRadicalNormalizerCoreControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ X : Subgroup G, X ≤ (CFSG.solvableRadical L).map L.subtype →
      (X.subgroupOf L).Characteristic → CFSG.pCore 2 X ≠ ⊥ → NoPQuotient 2 X →
      IsPGroup p (X ⧸ CFSG.pCore 2 X) → Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p →
      CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 → Nat.card (WPlane X) = p ^ 2 →
      (∃ l : normalizer (X : Set G), (l : G) ∈ L ∧ normalizerFrattiniConj X l ≠ 1) →
      (∀ V : Subgroup (WPlane X),
        (∀ l : normalizer (X : Set G), (l : G) ∈ L → ∀ w ∈ V, normalizerFrattiniConj X l w ∈ V) →
          V = ⊥ ∨ V = ⊤) →
      normalizer (X : Set G) = M ∧ normalizer (pCoreOf 2 (X ⊔ T) : Set G) ≤ M ∧
      pCoreOf 2 (normalizer (pCoreOf 2 (X ⊔ T) : Set G)) = pCoreOf 2 (X ⊔ T) ∧
      IsSylowOf 2 (pCoreOf 2 (X ⊔ T)) (⨆ m ∈ M, CFSG.conjugate (pCoreOf 2 (X ⊔ T)) m) ∧
      (∀ B : Subgroup G, IsPGroup 2 B → X ≤ normalizer (B : Set G) → pCoreOf 2 (X ⊔ T) ≤ B →
        B = pCoreOf 2 (X ⊔ T)) ∧
      (CFSG.fittingSubgroup (L ⧸ CFSG.pCore 2 L) = CFSG.pCore p (L ⧸ CFSG.pCore 2 L) →
        ⁅pCoreOf 2 (X ⊔ T), L⁆ ≤ pCoreOf 2 L ∧
        ((pCoreOf 2 (X ⊔ T)).subgroupOf (L ⊔ T)).Normal ∧
        ∀ D : Subgroup G, D ≠ ⊥ → D ≤ pCoreOf 2 (X ⊔ T) →
          (D.subgroupOf (pCoreOf 2 (X ⊔ T))).Characteristic → normalizer (D : Set G) ≤ M)

theorem stmtOriginalRadicalNormalizerCoreControl_of (h39 : SQTKCLayerPerfectResidual)
    (h2 : StmtQuasisimpleAmbientOneRankTwoPrime)
    : StmtOriginalRadicalNormalizerCoreControl :=
  fun _ _ _ _ _ _ h _ hp hp5 _ hXR hXc hO2X hX2 hXp hexp hrank hW hLW hirr =>
    original_radical_normalizer_and_core_control_before_same_witness_singleton_of h39 h2 h hp hp5
      hXR hXc hO2X hX2 hXp hexp hrank hW hLW hirr

end Control

end CFSG.Quasithin.H13.NQBlock
