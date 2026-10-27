module

public import CFSG.RankThree.PartOne.S11c.Sec66Conj
public import CFSG.RankThree.PartOne.S11c.Sec66TModels
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.RankThree.PartOne.Sec66T

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

theorem isCyclic_ringAut {K : Type} [Field K] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f) :
    IsCyclic (K ≃+* K) := by
  obtain ⟨σ, -, -, hgen, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  refine ⟨σ, fun x => ?_⟩
  have h : x ∈ Subgroup.zpowers σ := by
    rw [hgen]
    exact Subgroup.mem_top x
  exact h

theorem one_le_of_mul_eq {f p f' : ℕ} (hf : 1 ≤ f) (hff' : f = p * f') : 1 ≤ f' := by
  rcases Nat.eq_zero_or_pos f' with h0 | h0
  · rw [h0, mul_zero] at hff'
    omega
  · exact h0

theorem exists_adjoint_equiv
    {T : Type} [Group T] {t : StatedLieTag} {τ : Tag}
    (ht : untwistedTag t = some τ) {n f : ℕ} (hM : LieModel T t n 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ f ∧
      Nonempty (T ≃* adjointGroup τ K) := by
  obtain ⟨-, -, K, hKf, hKfin, hKcard, ⟨eQ⟩⟩ := (lieModel_untwisted_iff ht).mp hM
  exact ⟨K, hKf, hKfin, hKcard, ⟨eQ.trans (centerQuotientEquivSelf center_adjointGroup_eq_bot)⟩⟩

theorem fixedFieldImage_simple_of_quasisimple
    {τ :
    Tag} {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (hq : CFSG.IsQuasisimple ↥(adjointGroup τ (fixSubfield σ))) :
    IsSimpleGroup ↥(fixedFieldImage τ σ) ∧
      ¬ ∀ a b : ↥(fixedFieldImage τ σ), a * b = b * a := by
  have hZ : Subgroup.center ↥(adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨-, hs, a, b, hab⟩ := hq
  let eZ := centerQuotientEquivSelf hZ
  have hs' : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)) := by
    have := hs
    exact eZ.symm.isSimpleGroup
  let e := fixedFieldImageEquiv (τ := τ) σ
  refine ⟨e.symm.isSimpleGroup, fun h => hab ?_⟩
  have h2 : ∀ x y : ↥(adjointGroup τ (fixSubfield σ)), x * y = y * x := fun x y => by
    apply e.injective
    rw [map_mul, map_mul]
    exact h _ _
  have := h2 (eZ a) (eZ b)
  have h3 : eZ (a * b) = eZ (b * a) := by
    rw [map_mul, map_mul]
    exact this
  exact eZ.injective h3

theorem fieldAutT_of_conj_entrywise
    {t : StatedLieTag} {τ : Tag}
    (ht : untwistedTag t = some τ)
    {T : Type} [Group T] [Finite T] {p f f' : ℕ} (hp : p.Prime) {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible t 0 2 f') (hf : 1 ≤ f) (hKcard : Nat.card K = 2 ^ f)
    (e : T ≃* adjointGroup τ K)
    (hM : LieModel T t 0 2 f) (α : MulAut T) (σ : K ≃+* K) (hσord : orderOf σ = p)
    (hff' : f = p * f') (ψ : MulAut (adjointGroup τ K))
    (hψ : ψ * MulAut.congr e α * ψ⁻¹ = entrywiseAdjointAut τ σ)
    (hJC1 : ((entrywiseAdjointAut τ σ).toMonoidHom.eqLocus (MonoidHom.id _)).map
      (adjointGroup τ K).subtype = fixedFieldImage τ σ)
    (hsimple : IsSimpleGroup ↥(fixedFieldImage τ σ))
    (hnc : ¬ ∀ a b : ↥(fixedFieldImage τ σ), a * b = b * a) :
    FieldAutT p α := by
  have hf'pos : 1 ≤ f' := hadm.2.1
  have hZk : Subgroup.center (adjointGroup τ (fixSubfield σ)) = ⊥ := center_adjointGroup_eq_bot
  have eJ : ↥(fixedFieldImage τ σ) ≃* AdjointQuotient τ (fixSubfield σ) :=
    (fixedFieldImageEquiv σ).symm.trans (centerQuotientEquivSelf hZk).symm
  obtain ⟨hdvd, hkcard⟩ := card_fixSubfield Nat.prime_two hf hKcard σ
  have hkcard' : Nat.card (fixSubfield σ) = 2 ^ f' := by
    rw [hkcard, hσord, hff', Nat.mul_div_cancel_left f' hp.pos]
  have hXmodel : LieModel ↥(fixedFieldImage τ σ) t 0 2 f' :=
    (lieModel_untwisted_iff ht).mpr ⟨rfl, hadm, fixSubfield σ, inferInstance, inferInstance,
      hkcard', ⟨eJ⟩⟩
  have e3 : ↥(fixSub (entrywiseAdjointAut τ σ)) ≃* ↥(fixedFieldImage τ σ) :=
    (Subgroup.equivMapOfInjective _ (adjointGroup τ K).subtype
      (adjointGroup τ K).subtype_injective).trans (MulEquiv.subgroupCongr hJC1)
  have := hsimple
  have hnc' : ∃ a b : ↥(fixedFieldImage τ σ), a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  exact fieldAutT_of_conj_fix e hM hff' hf'pos α (entrywiseAdjointAut τ σ) ψ hψ
    (lieModel_fixRes_of_simple hnc' e3 hXmodel)

theorem exists_canonical_generator {K : Type} [Field K] {f p f' : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {σ : K ≃+* K} (hσ : orderOf σ = p) (hp : 0 < p)
    (hff' : f = p * f') :
    ∃ σ₀ : K ≃+* K, (∀ c, σ₀ c = c ^ 2 ^ f') ∧ Subgroup.zpowers σ = Subgroup.zpowers σ₀ := by
  obtain ⟨φ, hφ, hφord, hgen, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hf hK
  have hcyc : IsCyclic (K ≃+* K) := by
    refine ⟨φ, fun x => ?_⟩
    have h : x ∈ Subgroup.zpowers φ := by
      rw [hgen]
      exact Subgroup.mem_top x
    exact h
  have hf'0 : f' ≠ 0 := by
    rintro rfl
    omega
  have hpow : ∀ (k : ℕ) (c : K), (φ ^ k) c = c ^ 2 ^ k := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [pow_succ, RingAut.mul_apply, hφ, map_pow, ih, ← pow_mul, ← pow_succ]
  refine ⟨φ ^ f', hpow f', ?_⟩
  have hdvd : f' ∣ orderOf φ := ⟨p, by rw [hφord, hff']; ring⟩
  have hord0 : orderOf (φ ^ f') = p := by
    rw [orderOf_pow_of_dvd hf'0 hdvd, hφord, hff', Nat.mul_div_cancel p (Nat.pos_of_ne_zero hf'0)]
  have h1 : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσ]
  have h2 : Nat.card (Subgroup.zpowers (φ ^ f')) = p := by rw [Nat.card_zpowers, hord0]
  have : Finite (Subgroup.zpowers σ) := Nat.finite_of_card_ne_zero (by rw [h1]; exact hp.ne')
  have : Finite (Subgroup.zpowers (φ ^ f')) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; exact hp.ne')
  exact IsCyclic.subgroup_eq_iff_card_eq.mpr (h1.trans h2.symm)

end CFSG.RankThree.PartOne.Sec66T
