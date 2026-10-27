module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcOut
public import CFSG.LieType.Chevalley.E6CanonicalFieldGraphFixed
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RecipeFieldExcInn

section RootSet

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (S : (Fin r → ℤ) → Prop) (K : Type) [Field K]

@[expose] def markFieldImage (H : Subgroup (MarkChev.GLS S K)) :
    Set (MulAut (LargeEvenCenterQuot H)) :=
  {φ | ∃ σ : K ≃+* K, LargeEvenGraphAut (LargeEvenCenterMk H)
    (fun h h' => ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
      MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _)) φ}

@[expose] def ChevFieldInnOn (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) : Prop :=
  ∀ φ ∈ markFieldImage S K (MarkChev.chevH τ.cartan S K false),
    φ ∈ (MulAut.conj : LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false) →* _).range →
      φ = 1

variable {K} in
theorem ChevFieldInnOn.of_eq {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop} (hS : S = S')
    (h : ChevFieldInnOn K τ S) : ChevFieldInnOn K τ S' :=
  hS ▸ h

end RootSet

theorem ggRawInnField_of_chevFieldInnOn (τ : Tag) (K : Type) [Field K]
    (hC : ChevFieldInnOn K τ (IsRoot τ))
    (hsub : LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) →* _).range)
    {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) := by
  have h := hC.of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  have key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      ∀ φ ∈ LargeEvenChevFieldImage τ.cartan K H,
        φ ∈ (MulAut.conj : LargeEvenCenterQuot H →* _).range → φ = 1 := by
    intro H hH
    subst hH
    exact h
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage τ.cartan K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  exact key _ (largeEvenChevH_eq τ.cartan K false) φ hφ (hsub hφI)


theorem chevFieldInnOn_isRoot_of_inner (τ : Tag) (K : Type) [Field K] [Finite K]
    (hinner : ∀ (σ : K ≃+* K) (x : adjointGroup τ K),
      entrywiseAdjointAut τ σ = MulAut.conj x → σ = 1) :
    ChevFieldInnOn K τ (IsRoot τ) := by
  suffices h : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
      ∀ φ ∈ markFieldImage (IsRoot τ) K H,
        φ ∈ (MulAut.conj : LargeEvenCenterQuot H →* _).range → φ = 1 from
    h _ (chevH_false_eq_adjointGroup K τ)
  intro H hH
  subst hH
  rintro φ ⟨σ, hσ⟩ ⟨y, rfl⟩
  have hZ : Subgroup.center (adjointGroup τ K) = ⊥ := center_adjointGroup_eq_bot
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hmk : Function.Injective (LargeEvenCenterMk (adjointGroup τ K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, LargeEvenCenterMk, QuotientGroup.ker_mk', hZ]
  have hconj : ∀ h : adjointGroup τ K, entrywiseAdjointAut τ σ h = x * h * x⁻¹ := by
    intro h
    apply hmk
    have e1 := hσ h (entrywiseAdjointAut τ σ h) (by
      show ((entrywiseAdjointAut τ σ h : ModGL τ K) : Module.End K (RootModule τ K)) = _
      rw [coe_entrywiseAdjointAut]
      rfl)
    rw [← e1, MulAut.conj_apply]
    simp [LargeEvenCenterMk]
  have hα : entrywiseAdjointAut τ σ = MulAut.conj x := MulEquiv.ext fun h => by
    rw [hconj, MulAut.conj_apply]
  have hσ1 : σ = 1 := hinner σ x hα
  subst hσ1
  ext z
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective z
  rw [MulAut.conj_apply, MulAut.one_apply]
  have := congrArg (fun α : MulAut (adjointGroup τ K) => α h) hα
  simp only [MulAut.conj_apply] at this
  have h1 : (entrywiseAdjointAut τ (1 : K ≃+* K) h) = h := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_entrywiseAdjointAut]
    apply Finsupp.lhom_ext'
    intro b
    ext l
    simp [entrywiseHom, entrywise]
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← this, h1]

theorem chevFieldInnOn_isRoot_of_hom (τ : Tag) (K : Type) [Field K] [Finite K]
    (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K))
    (hΘ : ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut τ σ) = σ)
    (hinn : ∀ x : adjointGroup τ K, Θ (MulAut.conj x) = 1) :
    ChevFieldInnOn K τ (IsRoot τ) :=
  chevFieldInnOn_isRoot_of_inner τ K fun σ x hα => by rw [← hΘ σ, hα, hinn]

theorem pow_apply_of_sq' {K : Type} [Field K] {φ : K ≃+* K} (hφ : ∀ x, φ x = x ^ 2) :
    ∀ (k : ℕ) (x : K), (φ ^ k) x = x ^ 2 ^ k := by
  intro k
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]

theorem eq_one_of_entrywise_eq_conj_F4 {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) (σ : K ≃+* K)
    (x : adjointGroup CFSG.LieType.Ree.ReeTag.F4.tag K)
    (hα : entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag σ = MulAut.conj x) : σ = 1 := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨Fr, hFr, hord, hzp, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
    Nat.prime_two hf hK
  have hfin : IsOfFinOrder Fr := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨j, hj, rfl⟩ : ∃ j < f, Fr ^ j = σ := by
    have hmem : σ ∈ Subgroup.zpowers Fr := hzp ▸ Subgroup.mem_top σ
    rw [← hfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    exact ⟨k % f, Nat.mod_lt _ (by omega), by rw [← hk, ← hord, pow_mod_orderOf]⟩
  have hσc : ∀ c, (Fr ^ j) c = c ^ CFSG.LieType.Ree.ReeTag.F4.prime ^ j :=
    fun c => pow_apply_of_sq' hFr j c
  have h1 : entrywiseAdjointAut CFSG.LieType.Ree.ReeTag.F4.tag (Fr ^ j) =
      exactNormalAut CFSG.LieType.Ree.ReeTag.F4.tag K 1 (Fr ^ j) 0 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [coe_entrywiseAdjointAut, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one,
      mul_one]
  rw [h1, exactNormalAut_one_eq_finiteFrobeniusAut_pow CFSG.LieType.Ree.ReeTag.F4 hσc,
    ← finiteExceptionalAut_pow_two_mul] at hα
  obtain ⟨-, -, ⟨Θ, hΘ, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have e1 := hΘ _ 1 (2 * j) (by rw [map_one, one_mul])
  have e2 : Θ (MulAut.conj x) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨x, rfl⟩
  rw [hα, e2] at e1
  have h2 : ((2 * j : ℕ) : ZMod (2 * f)) = 0 := by
    have := congrArg Multiplicative.toAdd e1
    simpa using this.symm
  rw [ZMod.natCast_eq_zero_iff] at h2
  have h3 : f ∣ j := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
  have hj0 : j = 0 := Nat.eq_zero_of_dvd_of_lt h3 hj
  subst hj0
  rfl

theorem chevFieldInnOn_isRoot (τ : Tag) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hτ : (τ = .G2 ∧ 2 ≤ f) ∨ τ = .E7 ∨ τ = .E8) :
    ChevFieldInnOn K τ (IsRoot τ) := by
  have hrange : ∀ (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K)),
      Θ.ker = (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ∀ x : adjointGroup τ K, Θ (MulAut.conj x) = 1 := fun Θ hker x => by
    rw [← MonoidHom.mem_ker, hker]
    exact ⟨x, rfl⟩
  have hent : ∀ (Θ : MulAut (adjointGroup τ K) →* (K ≃+* K)),
      (∀ (α : MulAut (adjointGroup τ K)) (g : adjointGroup τ K) (σ : K ≃+* K),
        (∀ h : adjointGroup τ K, (α h : ModGL τ K) = (g : ModGL τ K) *
          Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * (g : ModGL τ K)⁻¹) →
        Θ α = σ) → ∀ σ : K ≃+* K, Θ (entrywiseAdjointAut τ σ) = σ := fun Θ hΘ σ =>
    hΘ _ 1 σ fun h => by rw [coe_entrywiseAdjointAut]; simp
  rcases hτ with ⟨rfl, hf2⟩ | rfl | rfl
  · obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form hf2 K hK
    exact chevFieldInnOn_isRoot_of_hom .G2 K Θ (hent Θ hΘ) (hrange Θ hker)
  · obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E7 (Or.inl rfl)
    exact chevFieldInnOn_isRoot_of_hom .E7 K Θ (hent Θ hΘ) (hrange Θ hker)
  · obtain ⟨-, Θ, hΘ, -, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hf K hK .E8 (Or.inr rfl)
    exact chevFieldInnOn_isRoot_of_hom .E8 K Θ (hent Θ hΘ) (hrange Θ hker)

theorem eq_one_of_mem_field_of_mem_inn (τ : Tag) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = 2 ^ f) (hτ : (τ = .G2 ∧ 2 ≤ f) ∨ τ = .E7 ∨ τ = .E8)
    {φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))}
    (hφ : φ ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false))
    (hinn : φ ∈ (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) →* _).range) :
    φ = 1 := by
  have h := (chevFieldInnOn_isRoot τ hf K hK hτ).of_eq (largeEvenIsRoot_eq_isRoot τ).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      ∀ φ ∈ LargeEvenChevFieldImage τ.cartan K H,
        φ ∈ (MulAut.conj : LargeEvenCenterQuot H →* _).range → φ = 1 from
    key _ (largeEvenChevH_eq τ.cartan K false) φ hφ hinn
  intro H hH
  subst hH
  exact h

theorem ggRawInnField_excInn (τ : Tag) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ f) (hτ : (τ = .G2 ∧ 2 ≤ f) ∨ τ = .E7 ∨ τ = .E8) {p : ℕ}
    (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevIDImage τ.cartan K _) (LargeEvenChevFieldImage τ.cartan K _) := by
  have hsub : LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) →* _).range := by
    have : CharP K 2 := charP_two_of_card hK
    rcases hτ with ⟨rfl, -⟩ | rfl | rfl
    · exact chevIDImage_subset_inn_of_top (τ := .G2)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanG2_inv
          fun s => ⟨s, pow_one s⟩)
    · exact chevIDImage_subset_inn_of_top (τ := .E7)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE7_adj
          (TableB.exists_sq_eq_of_charTwo K))
    · exact chevIDImage_subset_inn_of_top (τ := .E8)
        (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanE8_inv
          fun s => ⟨s, pow_one s⟩)
  refine ggRawInnField_of_subgroup hp
    (Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage τ.cartan K _)) rfl
    (conj_mem_chevIDImage _) fun φ hφ hφI => ?_
  exact eq_one_of_mem_field_of_mem_inn τ hf K hK hτ hφ (hsub hφI)

theorem ggRawInnField_F4 {f : ℕ} (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {p : ℕ} (hp : p ≠ 1) :
    GGRawInnField p (LargeEvenCenterQuot (LargeEvenChevH Tag.F4.cartan K false))
      (LargeEvenChevIDImage Tag.F4.cartan K _) (LargeEvenChevFieldImage Tag.F4.cartan K _) :=
  ggRawInnField_of_chevFieldInnOn .F4 K
    (chevFieldInnOn_isRoot_of_inner .F4 K fun σ x hα =>
      eq_one_of_entrywise_eq_conj_F4 hf K hK σ x hα)
    (chevIDImage_subset_inn_of_top (τ := .F4)
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanF4_inv
        fun s => ⟨s, pow_one s⟩)) hp

end RecipeFieldExcInn

open RecipeFieldExcInn

@[expose] def GGRecipeExcInnLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .E7 ∨ lab.tag = .E8

theorem ggRawInnFieldOn_excInn :
    GGRawInnFieldOn GGRecipeExcInnLabel := by
  intro p hp _ lab hlab hS Q hQ
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  rcases hS with ht | ht | ht <;> dsimp only at ht <;> subst ht
  · obtain ⟨-, hn2⟩ := hl
    exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .G2 hn K hK (Or.inl ⟨rfl, hn2⟩) hp1) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .E7 hn K hK (Or.inr (Or.inl rfl)) hp1) hQ
  · exact recipeChevalley_and (fun K _ _ hK =>
      ggRawInnField_excInn .E8 hn K hK (Or.inr (Or.inr rfl)) hp1) hQ

theorem ggRawInnFieldOn_F4 :
    GGRawInnFieldOn fun lab => lab.tag = .F4 := by
  intro p hp _ lab hlab hS Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hS
  subst hS
  exact recipeChevalley_and (fun K _ _ hK => ggRawInnField_F4 hn K hK hp.one_lt.ne') hQ

end CFSG.StandardType

end
