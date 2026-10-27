module

public import CFSG.LocalAnalysis.StandardType.GGTableBMarkedTheta
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestChev
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RecipeExcLang

private def ExcMarkedModel (K : Type) [Field K] (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop)
    (p : ℕ) : Prop :=
  ∃ f : MulAut (LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false)),
    GGTableBFieldSylowMark p
      (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false)) f ∧
    GGTableBMarkedFactorization p
      (markIDImage S K (MarkChev.chevH τ.cartan S K false)) f

private theorem ExcMarkedModel.of_eq {K : Type} [Field K] {τ : Tag}
    {S S' : (Fin τ.rank → ℤ) → Prop} {p : ℕ} (hS : S = S')
    (h : ExcMarkedModel K τ S p) : ExcMarkedModel K τ S' p :=
  hS ▸ h

private theorem theta_entrywise_of_nf
    {τ : Tag} {K : Type} [Field K]
    (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K))
    (hΘ : ∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
      (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
      Θ α = σ)
    (σ : K ≃+* K) : Θ (entrywiseAdjointAut τ σ) = σ :=
  hΘ _ 1 σ fun h => by rw [coe_entrywiseAdjointAut]; simp

private theorem f4_entrywise_eq_finiteExceptionalAut_pow_two_mul
    {K : Type} [Field K] [Finite K] [CharP K CFSG.LieType.Ree.ReeTag.F4.prime]
    (Fr : K ≃+* K) (hFr : ∀ x : K, Fr x = x ^ 2) (j : ℕ) :
    entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag (Fr ^ j) =
      MulAut.conj (1 : adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K) *
        CFSG.LieType.Ree.ReeTag.F4.finiteExceptionalAut K ^ (2 * j) := by
  have hσc : ∀ c : K, (Fr ^ j) c = c ^ CFSG.LieType.Ree.ReeTag.F4.prime ^ j :=
    fun c => RecipeFieldExcInn.pow_apply_of_sq' hFr j c
  have h1 : entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag (Fr ^ j) =
      exactNormalAut CFSG.LieType.Ree.ReeTag.F4.tag K 1 (Fr ^ j) 0 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_entrywiseAdjointAut, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one,
      mul_one]
  rw [h1, exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.F4 hσc,
    ← finiteExceptionalAut_pow_two_mul, map_one, one_mul]

theorem exists_marked_chev_of_quotient
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ} {G : Type} [Group G]
    (Θ : MulAut (adjointGroup τ K) →* G) (σ₀ : G) (hσ₀ : ∃ c : ℕ, orderOf σ₀ = p ^ c)
    (hgen : ∀ σ : G, (∃ k : ℕ, σ ^ p ^ k = 1) → ∃ j : ℤ, σ = σ₀ ^ j)
    (hlift : ∃ σ : K ≃+* K, Θ (entrywiseAdjointAut τ σ) = σ₀)
    (hent : ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut τ σ) = 1 → σ = 1)
    (hker : ∀ α : MulAut (adjointGroup τ K), Θ α = 1 →
      ∃ w : inndiagGroup τ K, α = inndiagConj τ K w) :
    ∃ f : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)),
      GGTableBFieldSylowMark p
        (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f ∧
      GGTableBMarkedFactorization p
        (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f := by
  have hmodel : ExcMarkedModel K τ (IsRoot τ) p := by
    unfold ExcMarkedModel
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
        ∃ f : MulAut (LargeEvenCenterQuot H),
          GGTableBFieldSylowMark p (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) f ∧
          GGTableBMarkedFactorization p (markIDImage (IsRoot τ) K H) f from
      key _ (chevH_false_eq_adjointGroup K τ)
    intro H hH
    subst hH
    have hlift' : ∃ φ ∈ Subgroup.closure
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)),
        (Θ.comp (autEquiv τ K).toMonoidHom) φ = σ₀ := by
      obtain ⟨σ, hσ⟩ := hlift
      refine ⟨(autEquiv τ K).symm (entrywiseAdjointAut τ σ),
        Subgroup.subset_closure (markField_of_entrywise σ), ?_⟩
      change Θ (autEquiv τ K ((autEquiv τ K).symm (entrywiseAdjointAut τ σ))) = σ₀
      rw [MulEquiv.apply_symm_apply, hσ]
    have hinj' : ∀ φ ∈ Subgroup.closure
        (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)),
        (Θ.comp (autEquiv τ K).toMonoidHom) φ = 1 → φ = 1 := by
      intro φ hφ hφ1
      obtain ⟨σ, hσ⟩ := exists_eq_entrywise_of_mem_closure_markField hφ
      have hΘσ : Θ (entrywiseAdjointAut τ σ) = 1 := by
        change Θ (autEquiv τ K φ) = 1 at hφ1
        rw [← hσ]
        exact hφ1
      have hσ1 : σ = 1 := hent σ hΘσ
      have hφeq : autEquiv τ K φ = 1 := by
        rw [hσ, hσ1, entrywiseAdjointAut_one]
      exact (autEquiv τ K).injective (by rw [hφeq, map_one])
    have hker' : ∀ φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K)),
        (Θ.comp (autEquiv τ K).toMonoidHom) φ = 1 →
          φ ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) := by
      intro φ hφ1
      change Θ (autEquiv τ K φ) = 1 at hφ1
      obtain ⟨w, hw⟩ := hker (autEquiv τ K φ) hφ1
      have hφeq : φ = (autEquiv τ K).symm (inndiagConj τ K w) := by
        rw [← hw, MulEquiv.symm_apply_apply]
      rw [hφeq]
      exact inndiagConj_mem_markID w
    exact exists_marked_of_quotient (R := LargeEvenCenterQuot (adjointGroup τ K)) (p := p)
      (Θ.comp (autEquiv τ K).toMonoidHom) σ₀ hσ₀ hgen hlift' hinj' hker'
  have h := ExcMarkedModel.of_eq (largeEvenIsRoot_eq_isRoot τ).symm hmodel
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      ∃ f : MulAut (LargeEvenCenterQuot H),
        GGTableBFieldSylowMark p (LargeEvenChevFieldImage τ.cartan K H) f ∧
        GGTableBMarkedFactorization p (LargeEvenChevIDImage τ.cartan K H) f from
    key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [RecipeExcLang.largeEvenChevIDImage_eq]
  exact h

theorem exists_marked_chev_E78
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p.Prime) :
    ∃ f' : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false)),
      GGTableBFieldSylowMark p
        (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f' ∧
      GGTableBMarkedFactorization p
        (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false)) f' := by
  obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK τ hτ
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
      (fun σ τ h => DFunLike.ext _ _ fun x => congrFun h x)
  have : IsCyclic (K ≃+* K) := isCyclic_ringEquiv_of_card hK
  obtain ⟨σ₀, hσ₀ord, hσ₀gen⟩ := exists_pPart_generator_of_isCyclic (G := K ≃+* K) hp
  have hent : ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut τ σ) = 1 → σ = 1 := by
    intro σ hσ
    have hΘσ : Θ (entrywiseAdjointAut τ σ) = σ := theta_entrywise_of_nf Θ hΘ σ
    rw [← hΘσ]
    exact hσ
  have hker' : ∀ α : MulAut (adjointGroup τ K), Θ α = 1 →
      ∃ w : inndiagGroup τ K, α = inndiagConj τ K w := by
    intro α hα
    have hmem : α ∈ Θ.ker := by rw [MonoidHom.mem_ker]; exact hα
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := hmem
    refine ⟨⟨g, adjointGroup_le_inndiagGroup g.2⟩, ?_⟩
    rw [inndiagConj_of_mem]
    exact hg.symm
  exact exists_marked_chev_of_quotient Θ σ₀ hσ₀ord hσ₀gen
    ⟨σ₀, theta_entrywise_of_nf Θ hΘ σ₀⟩ hent hker'

theorem exists_marked_chev_F4
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ f' : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.F4.cartan K false)),
      GGTableBFieldSylowMark p
        (LargeEvenChevFieldImage Tag.F4.cartan K (LargeEvenChevH Tag.F4.cartan K false)) f' ∧
      GGTableBMarkedFactorization p
        (LargeEvenChevIDImage Tag.F4.cartan K (LargeEvenChevH Tag.F4.cartan K false)) f' := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨-, hnf, ⟨Θ, hΘ, hsurj, hker⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form hf K hK
  have : NeZero (2 * f) := ⟨by omega⟩
  have : Finite (Multiplicative (ZMod (2 * f))) :=
    Finite.of_injective Multiplicative.toAdd Multiplicative.toAdd.injective
  have : IsCyclic (Multiplicative (ZMod (2 * f))) := inferInstance
  obtain ⟨σ₀, hσ₀ord, hσ₀gen⟩ :=
    exists_pPart_generator_of_isCyclic (G := Multiplicative (ZMod (2 * f))) hp
  have hent : ∀ σ : K ≃+* K,
      Θ (entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag σ) = 1 → σ = 1 := by
    intro σ hσ
    have hmem : entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag σ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker]
      exact hσ
    rw [hker] at hmem
    obtain ⟨x, hx⟩ := hmem
    exact RecipeFieldExcInn.eq_one_of_entrywise_eq_conj_F4 hf K hK σ x hx.symm
  have hker' : ∀ α : MulAut (adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K), Θ α = 1 →
      ∃ w : inndiagGroup CFSG.LieType.Ree.ReeTag.F4.tag K,
        α = inndiagConj CFSG.LieType.Ree.ReeTag.F4.tag K w := by
    intro α hα
    have hmem : α ∈ Θ.ker := by rw [MonoidHom.mem_ker]; exact hα
    rw [hker] at hmem
    obtain ⟨g, hg⟩ := hmem
    refine ⟨⟨g, adjointGroup_le_inndiagGroup g.2⟩, ?_⟩
    rw [inndiagConj_of_mem]
    exact hg.symm
  have hlift : ∃ σ : K ≃+* K,
      Θ (entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag σ) = σ₀ := by
    obtain ⟨α, hα⟩ := hsurj σ₀
    obtain ⟨⟨g, k⟩, hgk, -⟩ := hnf α
    have hσ₀k : σ₀ = Multiplicative.ofAdd ((k : ℕ) : ZMod (2 * f)) := by
      rw [← hα, hΘ α g k hgk]
    obtain ⟨c, hc⟩ := hσ₀ord
    have hpow : σ₀ ^ p ^ c = 1 := by rw [← hc]; exact pow_orderOf_eq_one σ₀
    rw [hσ₀k] at hpow
    rw [← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff] at hpow
    have hcop : Nat.Coprime 2 (p ^ c) :=
      (Nat.coprime_two_left.mpr (hp.odd_of_ne_two hp2)).pow_right c
    have h2 : 2 ∣ (k : ℕ) :=
      hcop.dvd_of_dvd_mul_left ((Dvd.intro f rfl).trans hpow)
    obtain ⟨j, hj⟩ := h2
    obtain ⟨Fr, hFr, -, -, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hf hK
    refine ⟨Fr ^ j, ?_⟩
    have hint : Θ (entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag (Fr ^ j)) =
        Multiplicative.ofAdd (((2 * j : ℕ)) : ZMod (2 * f)) :=
      hΘ _ 1 (2 * j) (f4_entrywise_eq_finiteExceptionalAut_pow_two_mul Fr hFr j)
    rw [hint, hσ₀k]
    congr 1
    rw [hj]
  exact exists_marked_chev_of_quotient Θ σ₀ hσ₀ord hσ₀gen hlift hent hker'

end CFSG.StandardType
