module

public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldLinearTwo
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSqClass
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG CFSG.GorensteinWalter CFSG.Open
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.AutL2Facts
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)

section Gamma

theorem one_le_finiteFieldExponent (F : Type) [Field F] [Finite F] : 1 ≤ finiteFieldExponent F := by
  by_contra h0
  have h0' : finiteFieldExponent F = 0 := by omega
  have := finiteField_card_eq F
  rw [h0', pow_zero] at this
  exact absurd this (Finite.one_lt_card (α := F)).ne'

variable {F : Type} [Field F] [Finite F]

theorem fixedSubgroup_eq_signalizer {X : Type*} [Group X] (α : MulAut X) :
    fixedSubgroup α = signalizerFixedSubgroup α := rfl

theorem mem_pslRange_of_odd_pow {γ : PGammaL2 F} (hr : γ.right = 1) {k : ℕ}
    (h : γ ^ (2 * k + 1) = 1) : γ ∈ pGammaL2PSLRange F := by
  have h2 : γ ^ 2 ∈ pGammaL2PSLRange F := by
    rw [mem_pslRange_iff]
    refine ⟨?_, ?_⟩
    · rw [pow_two, SemidirectProduct.mul_right, hr, mul_one]
    · rw [pow_two]
      exact (sqLeft_mul γ γ).2 Iff.rfl
  have h3 : (γ ^ 2) ^ k * γ = 1 := by
    rw [← pow_mul, ← pow_succ]
    exact h
  have h4 : γ = ((γ ^ 2) ^ k)⁻¹ := eq_inv_of_mul_eq_one_right h3
  rw [h4]
  exact inv_mem (pow_mem h2 k)

theorem exists_inl_conj {p : ℕ} (hp : p.Prime) {γ : PGammaL2 F} (hγp : γ ^ p = 1)
    (hr : γ.right ≠ 1) :
    ∃ c : PGL2 F, γ = SemidirectProduct.inl c * SemidirectProduct.inr γ.right *
      (SemidirectProduct.inl c)⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  set a := coordinateSemilinearAction F γ with ha
  have haE : a ∈ coordinateE F := by
    rw [← coordinateSemilinearAction_range_eq_E]
    exact ⟨γ, rfl⟩
  have haD : a ∉ coordinateD F := by
    intro hD
    rw [← coordinatePGLAction_range_eq_D] at hD
    obtain ⟨g, hg⟩ := hD
    have hγg : γ = SemidirectProduct.inl g :=
      coordinateSemilinearAction_injective F (by rw [coordinateSemilinearAction_inl]; exact hg.symm)
    apply hr
    rw [hγg]
    simp
  have hγ1 : γ ≠ 1 := fun h => hr (by rw [h]; simp)
  have hap : orderOf a = p := by
    refine orderOf_eq_prime ?_ ?_
    · rw [ha, ← map_pow, hγp, map_one]
    · intro h1
      apply hγ1
      exact coordinateSemilinearAction_injective F (by rw [← ha, h1, map_one])
  have hf : 1 ≤ finiteFieldExponent F := one_le_finiteFieldExponent F
  obtain ⟨-, σ, -, ⟨h, hhD, hah⟩, -⟩ :=
    CFSG.RankThree.LinearTwo.linear_two_prime_semilinear_field_descent
      (finiteField_characteristic_prime F) hp hf F (finiteField_card_eq F) haE haD hap
  rw [← coordinatePGLAction_range_eq_D] at hhD
  obtain ⟨c, rfl⟩ := hhD
  have hγeq : γ = SemidirectProduct.inl c * SemidirectProduct.inr σ * (SemidirectProduct.inl c)⁻¹ :=
    coordinateSemilinearAction_injective F (by
      rw [← ha, hah]
      simp only [map_mul, map_inv, coordinateSemilinearAction_inl, coordinateSemilinearAction_inr])
  have hσ : γ.right = σ := by
    rw [hγeq, right_conj, SemidirectProduct.right_inr]
  exact ⟨c, by rw [hσ]; exact hγeq⟩

theorem exists_conj_fieldAut {p : ℕ} (hp : p.Prime) (hodd : Odd p) {σ : MulAut (PSL2 F)}
    (hσ : IsOuterOfOrder p σ) :
    ∃ (τ : F ≃+* F) (β : MulAut (PSL2 F)), orderOf τ = p ∧
      σ = β * psl2FieldAut F τ * β⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hord, hout⟩ := hσ
  set γ := (semilinearEquivAut F).symm σ with hγ
  have hγσ : semilinearAction F γ = σ := (semilinearEquivAut F).apply_symm_apply σ
  have hγp : γ ^ p = 1 := by
    rw [hγ, ← map_pow, ← hord, pow_orderOf_eq_one, map_one]
  have hr : γ.right ≠ 1 := by
    intro hr
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨y, hy⟩ := mem_pslRange_of_odd_pow hr (k := k) (by rw [← hk]; exact hγp)
    apply hout y
    rw [← hγσ, ← hy]
    exact semilinearAction_incl F y
  have hτp : γ.right ^ p = 1 := by
    have h := congrArg SemidirectProduct.rightHom hγp
    rwa [map_pow, map_one, SemidirectProduct.rightHom_eq_right] at h
  obtain ⟨c, hc⟩ := exists_inl_conj hp hγp hr
  refine ⟨γ.right, pglAction F c, orderOf_eq_prime hτp hr, ?_⟩
  calc σ = semilinearAction F γ := hγσ.symm
    _ = semilinearAction F (SemidirectProduct.inl c * SemidirectProduct.inr γ.right *
        (SemidirectProduct.inl c)⁻¹) := congrArg _ hc
    _ = pglAction F c * psl2FieldAut F γ.right * (pglAction F c)⁻¹ := by
      rw [map_mul, map_mul, map_inv, semilinearAction_inl, semilinearAction_inr]

end Gamma

section Fixed

variable {X : Type*} [Group X]

theorem signalizerFixedSubgroup_conj (β f : MulAut X) :
    signalizerFixedSubgroup (β * f * β⁻¹) = (signalizerFixedSubgroup f).map β.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨β⁻¹ x, ?_, by simp⟩
    have h : β (f (β⁻¹ x)) = x := hx
    have h2 := congrArg (fun y => β⁻¹ y) h
    change f (β⁻¹ x) = β⁻¹ x
    simpa using h2
  · rintro ⟨y, hy, rfl⟩
    have hy' : f y = y := hy
    change β (f (β⁻¹ (β y))) = β y
    simp [hy']

theorem isCoatom_map_mulAut (β : MulAut X) {K : Subgroup X} :
    IsCoatom (K.map β.toMonoidHom) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff β.mapSubgroup K

theorem nonempty_fixed_conj_equiv (β f : MulAut X) :
    Nonempty (signalizerFixedSubgroup (β * f * β⁻¹) ≃* signalizerFixedSubgroup f) :=
  ⟨(MulEquiv.subgroupCongr (signalizerFixedSubgroup_conj β f)).trans
    (Subgroup.equivMapOfInjective _ β.toMonoidHom β.injective).symm⟩

end Fixed

section Fields

theorem nonempty_psl2_equiv_of_card_eq {k₁ k₂ : Type} [Field k₁] [Finite k₁] [Field k₂]
    [Finite k₂] (h : Nat.card k₁ = Nat.card k₂) : Nonempty (PSL2 k₁ ≃* PSL2 k₂) := by
  have := Fintype.ofFinite k₁
  have := Fintype.ofFinite k₂
  exact ⟨CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv
    (FiniteField.ringEquivOfCardEq (by rwa [← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card])) (Fin 2)⟩

end Fields

section Data

variable {F : Type} [Field F] [Finite F]


private theorem fieldAutData_psl2_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmax : ∀ τ : F ≃+* F, orderOf τ = p →
      IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) ∨
        ¬ p ∣ Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ))) :
    FieldAutData (PSL2 F) p := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hfix : ∀ σ : MulAut (PSL2 F), IsOuterOfOrder p σ →
      ∃ (τ : F ≃+* F) (β : MulAut (PSL2 F)), orderOf τ = p ∧
        σ = β * psl2FieldAut F τ * β⁻¹ ∧
        Nonempty (signalizerFixedSubgroup σ ≃* PSL2 (fixedSubfield F τ)) := by
    intro σ hσ
    obtain ⟨τ, β, hτ, rfl⟩ := exists_conj_fieldAut hp hodd hσ
    obtain ⟨e⟩ := CFSG.SignalizerFunctorTheorem.CatalogBridge.nonempty_mulEquiv_fixed_psl2FieldAut
      hodd hτ
    obtain ⟨e'⟩ := nonempty_fixed_conj_equiv β (psl2FieldAut F τ)
    exact ⟨τ, β, hτ, rfl, ⟨e'.trans e⟩⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro E hE hEc
    have hcyc : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
    set Φ : PGammaL2 F ≃* MulAut (PSL2 F) := semilinearEquivAut F with hΦ
    set E' : Subgroup (PGammaL2 F) := E.comap Φ.toMonoidHom with hE'
    have hmem : ∀ x ∈ E', Φ x ∈ E := fun x hx => hx
    have hE'p : ∀ x ∈ E', x ^ p = 1 := by
      intro x hx
      apply Φ.injective
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) _ (hmem x hx)
    have hE'card : Nat.card E' = p ^ 2 := by
      have h1 : E'.map Φ.toMonoidHom = E :=
        Subgroup.map_comap_eq_self_of_surjective Φ.surjective E
      rw [← Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective, h1]
      exact hEc
    let f : E' →* (F ≃+* F) := SemidirectProduct.rightHom.comp E'.subtype
    have hrange : Nat.card f.range ∣ p := by
      have hexp : Monoid.exponent f.range ∣ p := by
        refine Monoid.exponent_dvd_of_forall_pow_eq_one fun y => ?_
        have hy : (y : F ≃+* F) ^ p = 1 := by
          obtain ⟨x, hx⟩ := y.2
          rw [← hx, ← map_pow]
          have : x ^ p = 1 := Subtype.ext (hE'p x.1 x.2)
          rw [this, map_one]
        exact Subtype.ext hy
      rwa [← IsCyclic.exponent_eq_card]
    have hker : p ≤ Nat.card f.ker := by
      have h1 := Subgroup.card_ker_mul_card_range f
      rw [hE'card] at h1
      have h2 : Nat.card f.range ≤ p := Nat.le_of_dvd hp.pos hrange
      have h3 : p * p ≤ Nat.card f.ker * p := by
        calc p * p = p ^ 2 := by ring
          _ = Nat.card f.ker * Nat.card f.range := h1.symm
          _ ≤ Nat.card f.ker * p := Nat.mul_le_mul_left _ h2
      exact Nat.le_of_mul_le_mul_right h3 hp.pos
    have hne : f.ker ≠ ⊥ := by
      intro h
      have := hker
      rw [h, Subgroup.card_bot] at this
      have h2 := hp.two_le
      omega
    obtain ⟨⟨x, hxk⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    have hxr : (x : PGammaL2 F).right = 1 := MonoidHom.mem_ker.mp hxk
    have hx1' : (x : PGammaL2 F) ≠ 1 := by
      intro h
      apply hx1
      exact Subtype.ext (Subtype.ext h)
    obtain ⟨k, hk⟩ := hodd
    obtain ⟨y, hy⟩ := mem_pslRange_of_odd_pow hxr (k := k) (by rw [← hk]; exact hE'p x.1 x.2)
    refine ⟨y, ?_, ?_⟩
    · rintro rfl
      apply hx1'
      rw [← hy, map_one]
    · have h1 : MulAut.conj y = Φ (x : PGammaL2 F) := by
        rw [← hy]
        exact (semilinearAction_incl F y).symm
      rw [h1]
      exact hmem _ x.2
  ·
    intro σ hσ _ x hx hcomm
    obtain ⟨τ, β, hτ, -, ⟨e⟩⟩ := hfix σ hσ
    have hz : e ⟨x, hx⟩ ∈ Subgroup.center (PSL2 (fixedSubfield F τ)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (hcomm y.1 y.2).symm)
    rw [psl2_center_eq_bot, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val (e.injective (hz.trans (map_one e).symm))
  ·
    intro σ τ' hσ hτ' hne
    obtain ⟨τ₁, β₁, hτ₁, hσeq, ⟨e₁⟩⟩ := hfix σ hσ
    obtain ⟨τ₂, β₂, hτ₂, hτ'eq, ⟨e₂⟩⟩ := hfix τ' hτ'
    have hpos := one_le_finiteFieldExponent F
    obtain ⟨-, hc₁⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield
      (finiteField_characteristic_prime F) hpos (finiteField_card_eq F) τ₁
    obtain ⟨-, hc₂⟩ := CFSG.RankThree.LinearTwo.card_fixedSubfield
      (finiteField_characteristic_prime F) hpos (finiteField_card_eq F) τ₂
    rw [hτ₁] at hc₁
    rw [hτ₂] at hc₂
    obtain ⟨e₃⟩ := nonempty_psl2_equiv_of_card_eq (hc₁.trans hc₂.symm)
    have hcard : Nat.card (signalizerFixedSubgroup σ) = Nat.card (signalizerFixedSubgroup τ') :=
      (Nat.card_congr e₁.toEquiv).trans
        ((Nat.card_congr e₃.toEquiv).trans (Nat.card_congr e₂.toEquiv).symm)
    rcases hmax τ₁ hτ₁ with hco | hsmall
    · left
      have hcoσ : IsCoatom (signalizerFixedSubgroup σ) := by
        rw [hσeq, signalizerFixedSubgroup_conj]
        exact (isCoatom_map_mulAut β₁).2 hco
      have hle : signalizerFixedSubgroup σ ≤
          Subgroup.closure ((signalizerFixedSubgroup σ : Set (PSL2 F)) ∪
            (signalizerFixedSubgroup τ' : Set (PSL2 F))) :=
        fun x hx => Subgroup.subset_closure (Or.inl hx)
      rcases hcoσ.le_iff.mp hle with h | h
      · exact h
      · exfalso
        have hQP : signalizerFixedSubgroup τ' ≤ signalizerFixedSubgroup σ := by
          intro x hx
          rw [← h]
          exact Subgroup.subset_closure (Or.inr hx)
        exact hne (Subgroup.eq_of_le_of_card_ge hQP hcard.le).symm
    · right
      change ¬ p ∣ Nat.card (signalizerFixedSubgroup σ)
      rw [hσeq, signalizerFixedSubgroup_conj, Subgroup.card_map_of_injective β₁.injective]
      exact hsmall

theorem fieldAutData_psl2 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hmax : ∀ τ : F ≃+* F, orderOf τ = p →
      IsCoatom (signalizerFixedSubgroup (psl2FieldAut F τ)) ∨
        ¬ p ∣ Nat.card (signalizerFixedSubgroup (psl2FieldAut F τ))) :
    FieldAutData (PSL2 F) p :=
  fieldAutData_psl2_of_ne_two hp (by omega) hmax

end Data

end CFSG.RankThree.PartOne.CTP
