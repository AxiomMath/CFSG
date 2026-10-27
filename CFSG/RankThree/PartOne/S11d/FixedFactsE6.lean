module

public import CFSG.RankThree.PartOne.S11d.FixedFactsExc
public import CFSG.LieType.Chevalley.OrdinaryEAlgebraicTorusCartanIndex
public import CFSG.RankThree.PartOne.S11c.Sec66E6

public section

namespace CFSG.RankThree.PartOne.FieldFix

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec66T CFSG.RankThree.Chevalley SteinbergBT
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.LieType.CurtisTits (lieModel_of_mulEquiv)

theorem tagFixedFacts_E6
    (hNL : ChevalleySubfieldNonLocalized) : TagFixedFacts .E6 := by
  intro T _ _ p hp hp5 _ n f₀ hf₀ hM α₀ _ _ _ hX₀ α hαp hαinn _ _
  have hn0 : n = 0 := ((lieModel_untwisted_iff untwistedTag_E6).mp hM).1
  subst hn0
  have hf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := exists_adjoint_equiv untwistedTag_E6 hM
  obtain ⟨hα'inn, hα'ord⟩ := congr_noninner_prime hp e hαp hαinn
  set α' : MulAut (adjointGroup Tag.E6 K) := MulAut.congr e α with hα'
  obtain ⟨Θ, -, hΘ, -⟩ := ordinary_E_field_graph_quotient_and_involutions Tag.E6 (Or.inl rfl) K
  obtain ⟨⟨σ, -, hσord, ψ, hψ⟩, hpf, -⟩ :=
    even_E6_noninner_large_prime_field_descent_and_local_core_trivial hf K hKcard Θ hΘ hp
      (by omega) ⊤ le_top ⟨α', Subgroup.mem_top _⟩ hα'inn
      (by rw [Subgroup.orderOf_mk]; exact hα'ord)
  obtain ⟨f', hff'⟩ := hpf
  have hf'f₀ : f' = f₀ := (Nat.eq_of_mul_eq_mul_left hp.pos hff').symm
  have hf'pos : 1 ≤ f' := by omega
  obtain ⟨σ₀, hσ₀, hzp⟩ := exists_canonical_generator hf hKcard hσord hp.pos hff'
  have hσ₀ord : orderOf σ₀ = p := by
    rw [← Nat.card_zpowers, ← hzp, Nat.card_zpowers, hσord]
  have hfix_eq : fixSub (ψ * MulAut.congr e α * ψ⁻¹) = fixSub (entrywiseAdjointAut Tag.E6 σ₀) := by
    have h1 : ψ * MulAut.congr e α * ψ⁻¹ = entrywiseAdjointAut Tag.E6 σ := hψ
    rw [h1]
    apply fixSub_eq_of_zpowers_eq
    have h2 := congrArg (Subgroup.map (entrywiseAdjointAutHom (τ := Tag.E6) (K := K))) hzp
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at h2
    exact h2
  have hK' : Nat.card K = 2 ^ (f' * p) := by rw [hKcard, hf'f₀, mul_comm]
  obtain ⟨-, -, hder, hJC0, hsimple0, hnc0, -⟩ :=
    even_E6_canonical_field_derived_subgroup_and_pointwise_centralizer hf'pos hp.two_le K hK' σ₀
      hσ₀
  have hJC : fixedFieldImage Tag.E6 σ₀ ≤ adjointGroup Tag.E6 K := hJC0
  have hsimple : IsSimpleGroup ↥(fixedFieldImage Tag.E6 σ₀) := hsimple0
  have hnc : ¬∀ a b : ↥(fixedFieldImage Tag.E6 σ₀), a * b = b * a := hnc0
  set Γ : Subgroup ↥(adjointGroup Tag.E6 K) := fixSub (entrywiseAdjointAut Tag.E6 σ₀) with hΓ
  set N : Subgroup ↥(adjointGroup Tag.E6 K) :=
    (fixedFieldImage Tag.E6 σ₀).subgroupOf (adjointGroup Tag.E6 K) with hN
  have hder' : ⁅Γ, Γ⁆ = N := hder
  have hNsub : N.subgroupOf Γ = commutator ↥Γ := by
    rw [← hder', ← Subgroup.map_subtype_commutator]
    exact Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hNΓ : N ≤ Γ := hder' ▸ Subgroup.commutator_le_self Γ
  have hNnormal : (N.subgroupOf Γ).Normal := by
    rw [hNsub]
    exact inferInstance
  have hsolv : Group.IsSolvable (↥Γ ⧸ N.subgroupOf Γ) := by
    have : (N.subgroupOf Γ).Normal := hNnormal
    have : CommGroup (↥Γ ⧸ commutator ↥Γ) := inferInstanceAs (CommGroup (Abelianization ↥Γ))
    have : Group.IsSolvable (↥Γ ⧸ commutator ↥Γ) := inferInstance
    exact Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hNsub.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hNsub.symm).surjective
  have hnc' : ∃ a b : ↥(fixedFieldImage Tag.E6 σ₀), a * b ≠ b * a := by
    push Not at hnc
    exact hnc
  have hNperf : Group.IsPerfect ↥N :=
    have : Group.IsPerfect ↥(fixedFieldImage Tag.E6 σ₀) := isPerfect_of_simple_nonabelian hnc'
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJC).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJC).symm.surjective
  have hZk : Subgroup.center (adjointGroup Tag.E6 (fixSubfield σ₀)) = ⊥ :=
    center_adjointGroup_eq_bot
  let eN : ↥N ⧸ Subgroup.center ↥N ≃* AdjointQuotient Tag.E6 (fixSubfield σ₀) :=
    centerQuotientCongr ((Subgroup.subgroupOfEquivOfLe hJC).trans (fixedFieldImageEquiv σ₀).symm)
  obtain ⟨hdvd, hkcard⟩ := card_fixSubfield Nat.prime_two hf hKcard σ₀
  have hkcard' : Nat.card (fixSubfield σ₀) = 2 ^ f₀ := by
    rw [hkcard, hσ₀ord, Nat.mul_div_cancel_left f₀ hp.pos]
  have hXmodel : LieModel (AdjointQuotient Tag.E6 (fixSubfield σ₀)) .E6 0 2 f₀ :=
    (lieModel_untwisted_iff untwistedTag_E6).mpr ⟨rfl, admissible_E6 hf₀, fixSubfield σ₀,
      inferInstance, inferInstance, hkcard', ⟨MulEquiv.refl _⟩⟩
  have hΓmat : ∀ x ∈ Γ, (x : ModGL Tag.E6 K) ∈ entrywiseFixedGroup Tag.E6 σ₀ := by
    intro x hx
    refine mem_entrywiseFixedGroup.mpr ⟨x.2, ?_⟩
    have h := congrArg Subtype.val (mem_fixSub.mp hx)
    rwa [coe_entrywiseAdjointAut] at h
  obtain ⟨-, hCnorm, hCidx, -⟩ := ((ordinary_E_algebraic_torus_and_finite_fixed_group_Cartan_index
    Tag.E6 3 (Or.inl ⟨rfl, rfl⟩)).2 K σ₀)
  have hPq : ∀ q : ℕ, q.Prime → q ≠ 3 → ∀ x ∈ Γ, (∃ k : ℕ, orderOf x = q ^ k) → x ∈ N := by
    intro q hq hq3 x hx ⟨k, hk⟩
    have : ((fixedFieldImage Tag.E6 σ₀).subgroupOf (entrywiseFixedGroup Tag.E6 σ₀)).Normal :=
      hCnorm
    have hmem := pElement_mem_of_index_dvd_pow hq Nat.prime_three hq3
      ((fixedFieldImage Tag.E6 σ₀).subgroupOf (entrywiseFixedGroup Tag.E6 σ₀)) (k := 1)
      (by simpa using hCidx)
      (x := (⟨(x : ModGL Tag.E6 K), hΓmat x hx⟩ : ↥(entrywiseFixedGroup Tag.E6 σ₀)))
      ⟨k, by rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk]⟩
    exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hmem)
  set φ : T ≃* adjointGroup Tag.E6 K := e.trans ψ with hφ
  have hφα : MulAut.congr φ α = ψ * MulAut.congr e α * ψ⁻¹ := rfl
  have hΓφ : fixSub (MulAut.congr φ α) = Γ := by rw [hφα, hfix_eq]
  exact fixedFacts_of_iso_of_eq φ α hM hf₀ Γ N hΓφ hNΓ hNnormal hNperf hsolv
    (hNL .E6 (Or.inr (Or.inr (Or.inl rfl))) σ₀) (hPq p hp (by omega))
    (Or.inl (hPq 2 Nat.prime_two (by norm_num))) (Or.inl (lieModel_of_mulEquiv eN.symm hXmodel))

end CFSG.RankThree.PartOne.FieldFix
