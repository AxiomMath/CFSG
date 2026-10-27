module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestCore
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangChev
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang

namespace RawAutChev

@[expose] def ChevOddAutOn (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) (p : ℕ) :
    Prop :=
  GGOddAutInnField p (markIDImage S K (MarkChev.chevH τ.cartan S K false))
    (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false))

theorem ChevOddAutOn.of_eq {K : Type} [Field K] {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop}
    {p : ℕ} (hS : S = S') (h : ChevOddAutOn K τ S p) : ChevOddAutOn K τ S' p :=
  hS ▸ h


variable {τ : Tag} {K : Type} [Field K] [Finite K]

theorem ggOddAutInnField_adjoint {p : ℕ}
    (hC : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      ∃ w : inndiagGroup τ K, ∃ σ : K ≃+* K, α = inndiagConj τ K w * entrywiseAdjointAut τ σ) :
    GGOddAutInnField p (markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  intro φ hφ
  obtain ⟨w, σ, hw⟩ := hC (autEquiv τ K φ) (by rw [← map_pow, hφ, map_one])
  refine ⟨(autEquiv τ K).symm (inndiagConj τ K w), inndiagConj_mem_markID w,
    (autEquiv τ K).symm (entrywiseAdjointAut τ σ),
    Subgroup.subset_closure (markField_of_entrywise σ), ?_⟩
  rw [← map_mul, ← hw, MulEquiv.symm_apply_apply]

theorem chevOddAutOn_isRoot {p : ℕ}
    (hC : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      ∃ w : inndiagGroup τ K, ∃ σ : K ≃+* K, α = inndiagConj τ K w * entrywiseAdjointAut τ σ) :
    ChevOddAutOn K τ (IsRoot τ) p := by
  unfold ChevOddAutOn
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
      GGOddAutInnField p (markIDImage (IsRoot τ) K H)
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) from
    key _ (chevH_false_eq_adjointGroup K τ)
  intro H hH
  subst hH
  exact ggOddAutInnField_adjoint hC

theorem ggOddAutInnField_chev {p : ℕ}
    (hC : ∀ α : MulAut (adjointGroup τ K), α ^ p = 1 →
      ∃ w : inndiagGroup τ K, ∃ σ : K ≃+* K, α = inndiagConj τ K w * entrywiseAdjointAut τ σ) :
    GGOddAutInnField p (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have h := (chevOddAutOn_isRoot hC).of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      GGOddAutInnField p (LargeEvenChevIDImage τ.cartan K H)
        (LargeEvenChevFieldImage τ.cartan K H) from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

set_option linter.unusedSectionVars false in
theorem exists_inndiag_entrywise_of_nf
    (hnf : ∀ α : MulAut (adjointGroup τ K), ∃! gσ : adjointGroup τ K × (K ≃+* K),
      ∀ h : adjointGroup τ K, (α h : ModGL τ K) = (gσ.1 : ModGL τ K) *
        Units.map (entrywiseHom gσ.2.toRingHom) (h : ModGL τ K) * (gσ.1 : ModGL τ K)⁻¹)
    (α : MulAut (adjointGroup τ K)) :
    ∃ w : inndiagGroup τ K, ∃ σ : K ≃+* K, α = inndiagConj τ K w * entrywiseAdjointAut τ σ := by
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hnf α
  refine ⟨⟨g, adjointGroup_le_inndiagGroup g.2⟩, σ, MulEquiv.ext fun h => Subtype.ext ?_⟩
  rw [hgσ h, MulAut.mul_apply, coe_inndiagConj, coe_entrywiseAdjointAut]

theorem exists_inndiag_entrywise_E6 {p : ℕ} (hp : Odd p)
    (α : MulAut (adjointGroup TwistTag.E6.tag K)) (hα : α ^ p = 1) :
    ∃ w : inndiagGroup TwistTag.E6.tag K, ∃ σ : K ≃+* K,
      α = inndiagConj TwistTag.E6.tag K w * entrywiseAdjointAut TwistTag.E6.tag σ := by
  obtain ⟨Θ, -, hΘ, hker, -⟩ :=
    ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) K
  set σ := (Θ α).1 with hσdef
  have hσΘ : Θ (entrywiseAdjointAut TwistTag.E6.tag σ) = (σ, 1) := by
    have h1 := hΘ (entrywiseAdjointAut TwistTag.E6.tag σ) 1 1 σ ⟨0, exactE_pos _⟩ fun h => by
      rw [coe_entrywiseAdjointAut, rootDiagUnit_one]
      change _ = _ * _ * exactQ TwistTag.E6.tag K 0 * _ * (exactQ TwistTag.E6.tag K 0)⁻¹ * _ * _
      rw [exactQ_zero]
      simp
    rw [h1]
    simp
  have h2 : (Θ α).2 = 1 := by
    have hxp : (Θ α).2 ^ p = 1 := by
      have := congrArg Prod.snd (congrArg Θ hα)
      rw [map_pow, map_one] at this
      exact this
    have hx2 : (Θ α).2 ^ 2 = 1 := by
      have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
      exact hall _
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_right.mpr hp)
      (orderOf_dvd_of_pow_eq_one hxp) (orderOf_dvd_of_pow_eq_one hx2))
  have hαΘ : Θ α = (σ, 1) := Prod.ext rfl h2
  have hk : α * (entrywiseAdjointAut TwistTag.E6.tag σ)⁻¹ ∈ Θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hαΘ, hσΘ, mul_inv_cancel]
  obtain ⟨g, a, hga⟩ := (hker _).mp hk
  have hw : (g : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag a ∈
      inndiagGroup TwistTag.E6.tag K :=
    mul_mem (adjointGroup_le_inndiagGroup g.2) (rootDiagUnit_mem_inndiagGroup a)
  refine ⟨⟨_, hw⟩, σ, MulEquiv.ext fun h => Subtype.ext ?_⟩
  have e := hga (entrywiseAdjointAut TwistTag.E6.tag σ h)
  rw [MulAut.mul_apply, MulAut.inv_apply_self] at e
  rw [e, MulAut.mul_apply, coe_inndiagConj]
  simp only
  group

theorem exists_inndiag_entrywise_F4 {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : Odd p)
    (α : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)) (hα : α ^ p = 1) :
    ∃ w : inndiagGroup CFSG.LieType.Ree.ReeTag.F4.tag K, ∃ σ : K ≃+* K,
      α = inndiagConj CFSG.LieType.Ree.ReeTag.F4.tag K w *
        entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag σ := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  have : CharP K 2 := charP_two_of_card hK
  obtain ⟨-, hnf, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
  have hpow : Θ α ^ p = 1 := by rw [← map_pow, hα, map_one]
  rw [hΘ α g k hgk, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff] at hpow
  have h2 : 2 ∣ (k : ℕ) :=
    (Nat.coprime_two_left.mpr hp).dvd_of_dvd_mul_left ((Dvd.intro f rfl).trans hpow)
  obtain ⟨j, hj⟩ := h2
  have hσ : ∀ c : K, frobeniusEquiv K 2 c = c ^ 2 := fun c => by
    rw [coe_frobeniusEquiv, frobenius_def]
  refine ⟨⟨(g : ModGL _ K), adjointGroup_le_inndiagGroup g.2⟩, frobeniusEquiv K 2 ^ j, ?_⟩
  have e : CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ (2 * j) =
      CFSG.LieType.Ree.ReeTag.F4.finiteFrobeniusAut K ^ j :=
    finiteExceptionalAut_pow_two_mul CFSG.LieType.Ree.ReeTag.F4 j
  rw [hgk, hj, e, inndiagConj_of_mem]
  congr 1
  exact MulEquiv.ext fun h => Subtype.ext (by
    rw [CFSG.LieType.Ree.ReeTag.coe_finiteFrobeniusAut_pow hσ j h, coe_entrywiseAdjointAut])

end RawAutChev

open RawAutChev

section Labels


theorem ggOddAutOn_G2 : GGOddAutOn fun lab => lab.tag = .G2 := by
  intro p lab _ _ hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  dsimp only at ht
  subst ht
  obtain ⟨-, hn2⟩ := hl
  exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ _ => ggOddAutInnField_chev (τ := .G2) fun α _ =>
      exists_inndiag_entrywise_of_nf
        (CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
          hn2 K hK).1 α) hQ

theorem ggOddAutOn_E7E8 : GGOddAutOn fun lab => lab.tag = .E7 ∨ lab.tag = .E8 := by
  intro p lab _ _ hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  rcases ht with ht | ht <;> dsimp only at ht <;> subst ht
  · exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R →
        (∃ a b : R, a * b ≠ b * a) → GGOddAutInnField p I F)
      (fun K _ _ hK _ _ => ggOddAutInnField_chev (τ := .E7) fun α _ =>
        exists_inndiag_entrywise_of_nf
          (even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E7 (Or.inl rfl)).1 α) hQ
  · exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R →
        (∃ a b : R, a * b ≠ b * a) → GGOddAutInnField p I F)
      (fun K _ _ hK _ _ => ggOddAutInnField_chev (τ := .E8) fun α _ =>
        exists_inndiag_entrywise_of_nf
          (even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E8 (Or.inr rfl)).1 α) hQ

theorem ggOddAutOn_E6 : GGOddAutOn fun lab => lab.tag = .E6 := by
  intro p lab hp hp2 _ ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ _ _ _ => ggOddAutInnField_chev (τ := TwistTag.E6.tag) fun α hα =>
      exists_inndiag_entrywise_E6 (hp.odd_of_ne_two hp2) α hα) hQ

theorem ggOddAutOn_F4 : GGOddAutOn fun lab => lab.tag = .F4 := by
  intro p lab hp hp2 hlab ht _ Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at ht
  subst ht
  exact recipeChevalley_and (P := fun R _ I F => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      GGOddAutInnField p I F)
    (fun K _ _ hK _ _ => ggOddAutInnField_chev (τ := .F4) fun α hα =>
      exists_inndiag_entrywise_F4 hn hK (hp.odd_of_ne_two hp2) α hα) hQ

end Labels

end CFSG.StandardType

end
