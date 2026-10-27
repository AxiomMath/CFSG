module

public import CFSG.RankThree.PartOne.S11d.FixedFacts
public import CFSG.RankThree.PartOne.S11c.Sec66G2
public import CFSG.RankThree.PartOne.S11c.Sec66F4
public import CFSG.RankThree.PartOne.S11c.Sec66E78

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Chevalley
open CFSG.RankThree.LocalRank SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.ComponentClassification.UnbalancedCatalog (even_G2_exact_automorphism_normal_form)

@[expose] def ChevalleySubfieldNonLocalized :
    Prop :=
  ∀ {K : Type} [Field K] [Finite K] (τ : Tag),
    (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∀ (σ : K ≃+* K), NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))

theorem exc_fixedFacts_of_conj_entrywise
    {t : StatedLieTag} {τ : Tag}
    (ht : untwistedTag t = some τ) {T : Type} [Group T] [Finite T] {p f₀ : ℕ} (hp : p.Prime)
    {K : Type} [Field K] [Finite K] (hadm : StatedLieAdmissible t 0 2 f₀)
    (hKcard : Nat.card K = 2 ^ (p * f₀)) (e : T ≃* adjointGroup τ K)
    (hM : LieModel T t 0 2 (p * f₀)) (α : MulAut T) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (ψ : MulAut (adjointGroup τ K))
    (hψ : ψ * MulAut.congr e α * ψ⁻¹ = entrywiseAdjointAut τ σ)
    (hJC1 : ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup τ K).subtype = fixedFieldImage τ σ)
    (hsimple : IsSimpleGroup ↥(fixedFieldImage τ σ))
    (hnc : ¬ ∀ a b : ↥(fixedFieldImage τ σ), a * b = b * a)
    (hNL : NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))) :
    FixedFacts p α := by
  have hf₀ : 1 ≤ f₀ := hadm.2.1
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hZk : Subgroup.center (adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  have eJ : ↥(fixedFieldImage τ σ) ≃* AdjointQuotient τ (fixSubfield σ) :=
    (fixedFieldImageEquiv σ).symm.trans (centerQuotientEquivSelf hZk).symm
  obtain ⟨hdvd, hkcard⟩ := card_fixSubfield Nat.prime_two hf hKcard σ
  have hkcard' : Nat.card (fixSubfield σ) = 2 ^ f₀ := by
    rw [hkcard, hσord, Nat.mul_div_cancel_left f₀ hp.pos]
  have hXmodel : LieModel ↥(fixedFieldImage τ σ) t 0 2 f₀ :=
    (lieModel_untwisted_iff ht).mpr ⟨rfl, hadm, fixSubfield σ, inferInstance, inferInstance,
      hkcard', ⟨eJ⟩⟩
  have hnc' : ∃ a b : ↥(fixedFieldImage τ σ), a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  set φ : T ≃* adjointGroup τ K := e.trans ψ with hφ
  have hφα : MulAut.congr φ α = entrywiseAdjointAut τ σ := by
    have : MulAut.congr φ α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
    rw [this, hψ]
  have hfix : fixSub (entrywiseAdjointAut τ σ) =
      (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) := by
    ext x
    rw [Subgroup.mem_subgroupOf, ← hJC1]
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact (Subtype.ext hyx) ▸ hy
  have e3 : ↥(fixSub (entrywiseAdjointAut τ σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup τ K).subtype
      (adjointGroup τ K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  have : IsSimpleGroup ↥(fixedFieldImage τ σ) := hsimple
  exact fixedFacts_of_simple φ α hM hf₀ ((MulEquiv.subgroupCongr (by rw [hφα])).trans e3) hnc'
    (by rw [hφα, hfix]; exact hNL) (Or.inl hXmodel)

theorem tagFixedFacts_G2
    (hNL : ChevalleySubfieldNonLocalized) : TagFixedFacts .G2 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hadm : StatedLieAdmissible .G2 n 2 f₀ := by
    rcases admissible_of_fixModel hX₀ with h | ⟨h, -, -⟩
    · exact h
    · exact absurd h (by decide)
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_G2).mp hM).1
  subst hn0
  have hf₀2 : 2 ≤ f₀ := two_le_of_admissible_G2 hadm
  have hf2 : 2 ≤ p * f₀ := le_trans hf₀2 (Nat.le_mul_of_pos_left f₀ hp.pos)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_G2 hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup .G2 K) := MulAut.congr e α with hα'
  obtain ⟨hNF, -⟩ := even_G2_exact_automorphism_normal_form hf2 K hKcard
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut .G2 σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨h0, hh0⟩, -⟩ :=
    even_G2_noninner_prime_local_core_trivial hf2 hKcard hp ⊤ le_top ⟨α', Subgroup.mem_top _⟩
      hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  obtain ⟨-, hkcard, -, hJC1, -⟩ := even_G2_canonical_field_centralizer_all_orders hf2 hKcard σ
  have hk4 : 3 ≤ Nat.card (fixSubfield σ) := by
    rw [hkcard, hσord, Nat.mul_div_cancel_left f₀ hp.pos]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f₀ := Nat.pow_le_pow_right (by norm_num) hf₀2
  have hq' : CFSG.IsQuasisimple ↥(adjointGroup .G2 (fixSubfield σ)) :=
    CFSG.LieType.Steinberg.Adjoint.isQuasisimple_g2_of_three_le_card _ hk4
  obtain ⟨hsimple, hnc⟩ := fixedFieldImage_simple_of_quasisimple σ hq'
  exact exc_fixedFacts_of_conj_entrywise untwistedTag_G2 hp hadm hKcard e hM α σ hσord
    (MulAut.conj h0) hh0 hJC1 hsimple hnc (hNL .G2 (Or.inl rfl) σ)

theorem tagFixedFacts_F4
    (hNL : ChevalleySubfieldNonLocalized) : TagFixedFacts .F4 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_F4).mp hM).1
  subst hn0
  have hadm : StatedLieAdmissible .F4 0 2 f₀ := admissible_F4 hf₀
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_F4 hM
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hf
      hKcard
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup ReeTag.F4.tag K) := MulAut.congr e α with hα'
  obtain ⟨-, hNF, -⟩ := even_F4_exact_automorphism_normal_form hf K hKcard
  obtain ⟨⟨x, a⟩, hxa, -⟩ := hNF α'
  obtain ⟨-, hpf, ⟨σ, hσ⟩, hdesc, -⟩ :=
    even_F4_noninner_odd_prime_field_descent_and_local_core_trivial hf hKcard hp hp2 ⊤ le_top
      ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x a a.2 hxa
  obtain ⟨hσord, ψ, hψ⟩ := hdesc σ hσ
  obtain ⟨hJC1, -, hsimple, hnc, -⟩ := even_F4_canonical_field_centralizer_all_orders hf hKcard σ
  exact exc_fixedFacts_of_conj_entrywise untwistedTag_F4 hp hadm hKcard e hM α σ hσord ψ hψ hJC1
    hsimple hnc (hNL ReeTag.F4.tag (Or.inr (Or.inl rfl)) σ)

theorem tagFixedFacts_E78
    (hNL : ChevalleySubfieldNonLocalized) (t : StatedLieTag) (τ : Tag)
    (ht : untwistedTag t = some τ) (hτ : τ = .E7 ∨ τ = .E8)
    (hadmAll : ∀ {f : ℕ}, 1 ≤ f → StatedLieAdmissible t 0 2 f) : TagFixedFacts t := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hn0 : n = 0 := ((lieModel_untwisted_iff ht).mp hM).1
  subst hn0
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv ht hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup τ K) := MulAut.congr e α with hα'
  obtain ⟨hNF, -⟩ := even_E7_E8_exact_inner_field_automorphism_normal_form hf K hKcard τ hτ
  obtain ⟨⟨x, σ⟩, hxσ, -⟩ := hNF α'
  have hα'eq : α' = MulAut.conj x * entrywiseAdjointAut τ σ := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [hxσ h, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_entrywiseAdjointAut]
  obtain ⟨hσord, hpf, ⟨ψ, hψ⟩, -⟩ :=
    even_E7_E8_noninner_prime_field_descent_and_local_core_trivial τ hτ hf K hKcard hp ⊤ le_top
      ⟨α', Subgroup.mem_top _⟩ hα'inn (by rw [Subgroup.orderOf_mk]; exact hα'ord) x σ hα'eq
  obtain ⟨hJC1, -, hsimple, hnc, -⟩ :=
    even_E7_E8_canonical_field_centralizer_all_orders τ hτ hf K hKcard σ
  have hτ' : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  exact exc_fixedFacts_of_conj_entrywise ht hp (hadmAll hf₀) hKcard e hM α σ hσord ψ hψ hJC1
    hsimple hnc (hNL τ hτ' σ)

theorem tagFixedFacts_E7
    (hNL : ChevalleySubfieldNonLocalized) : TagFixedFacts .E7 :=
  tagFixedFacts_E78 hNL .E7 .E7 rfl (Or.inl rfl) fun hf => admissible_E7 hf

theorem tagFixedFacts_E8
    (hNL : ChevalleySubfieldNonLocalized) : TagFixedFacts .E8 :=
  tagFixedFacts_E78 hNL .E8 .E8 rfl (Or.inr rfl) fun hf => admissible_E8 hf

end CFSG.RankThree.PartOne.FieldFix
