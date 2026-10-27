module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false

@[expose] def TwistedConjOn (K : Type) [Field K] (t : TwistTag) (n : ℕ)
    (S : (Fin t.tag.rank → ℤ) → Prop) (p : ℕ) : Prop :=
  GGRawFieldConj p (LargeEvenCenterQuot (MarkChev.twistedH t.tag.cartan S K t.perm n))
    (markIDImage S K (MarkChev.twistedH t.tag.cartan S K t.perm n))
    (RecipeFieldExcInn.markFieldImage S K (MarkChev.twistedH t.tag.cartan S K t.perm n))

theorem TwistedConjOn.of_eq {K : Type} [Field K] {t : TwistTag} {n : ℕ}
    {S S' : (Fin t.tag.rank → ℤ) → Prop} {p : ℕ} (hS : S = S') (h : TwistedConjOn K t n S p) :
    TwistedConjOn K t n S' p :=
  hS ▸ h


variable {K : Type} [Field K] [Finite K]

theorem ggRawFieldConj_C0_D4 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp3 : p ≠ 3) :
    GGRawFieldConj p (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (markIDImage (IsRoot TwistTag.D4.tag) K (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  intro _ _ u hu f _ huf hpow
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  set e := centerQuotEquivOfBot hZ with he
  set Ψ := MulAut.congr e with hΨ
  have hInn : ∀ y, (MulAut.conj y : MulAut (LargeEvenCenterQuot
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) ∈ markIDImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    fun y => Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
  have hΨconj : ∀ y, Ψ (MulAut.conj (e.symm y)) = MulAut.conj y := fun y => by
    rw [hΨ, mulAut_congr_conj, MulEquiv.apply_symm_apply]
  set x := Ψ (u * f) with hx
  have hxp : x ^ p = 1 := by rw [hx, ← map_pow, hpow, map_one]
  have hxinn : ∀ y, x ≠ MulAut.conj y := by
    intro y hy
    apply huf
    have : u * f = MulAut.conj (e.symm y) := Ψ.injective (by rw [← hx, hy, hΨconj])
    rw [this]
    exact hInn _
  obtain ⟨hfield, huniq, ⟨Θ, hΘ, -, -, -⟩, -⟩ :=
    even_triality_exact_automorphism_normal_form hn K hK σ hσ
  obtain ⟨⟨y, δ⟩, hyδ, -⟩ := huniq x
  simp only at hyδ
  have hΘx : Θ x = δ := hΘ x y δ hyδ
  have hδp : δ ^ p = 1 := by rw [← hΘx, ← map_pow, hxp, map_one]
  have hδ1 : δ ≠ 1 := by
    rintro rfl
    apply hxinn y
    rw [hyδ, fieldActor_one, mul_one]
  have : Fact p.Prime := ⟨hp⟩
  have hδord : orderOf δ = p := orderOf_eq_prime hδp hδ1
  obtain ⟨g, hg⟩ := exists_conj_eq_fieldActor_D4 hn hK σ hσ hp hp3 δ hδord y
    (by rw [← hyδ]; exact hxp)
  refine ⟨Ψ.symm (fieldActor σ δ), ⟨δ, fun h h' hrel => ?_⟩, MulAut.conj (e.symm g⁻¹), hInn _,
    ?_, ?_⟩
  ·
    rw [hΨ, congr_symm_apply_mk hZ]
    congr 1
    refine Subtype.ext (Units.ext ?_)
    rw [hfield δ h]
    exact hrel.symm
  ·
    rw [MulEquiv.orderOf_eq]
    refine orderOf_eq_prime ?_ fun h1 => hδ1 ?_
    · rw [← fieldActorHom_apply (t := TwistTag.D4), ← map_pow, hδp, map_one]
    · have h2 := hΘ (fieldActor σ δ) 1 δ (by rw [map_one, one_mul])
      rw [h1, map_one] at h2
      exact h2.symm
  ·
    apply Ψ.injective
    have hR : Ψ (MulAut.conj (e.symm g⁻¹) * Ψ.symm (fieldActor σ δ) *
        (MulAut.conj (e.symm g⁻¹))⁻¹) = MulAut.conj g⁻¹ * fieldActor σ δ *
          (MulAut.conj g⁻¹)⁻¹ := by
      rw [map_mul, map_mul, map_inv Ψ (MulAut.conj (e.symm g⁻¹)), hΨconj,
        MulEquiv.apply_symm_apply]
    have e0 : MulAut.conj y * fieldActor σ δ = (MulAut.conj g)⁻¹ * (MulAut.conj g *
        (MulAut.conj y * fieldActor σ δ) * (MulAut.conj g)⁻¹) * MulAut.conj g := by group
    rw [hR, ← hx, hyδ, e0, hg, map_inv, inv_inv]

theorem twistedConjOn_isRoot_D4 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hp : p.Prime) (hp3 : p ≠ 3) :
    TwistedConjOn K TwistTag.D4 n (IsRoot TwistTag.D4.tag) p := by
  unfold TwistedConjOn
  have hH : MarkChev.twistedH TwistTag.D4.tag.cartan (IsRoot TwistTag.D4.tag) K
      TwistTag.D4.perm n = graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.D4 n σ.toRingHom hσ).trans
      (even_triality_exact_automorphism_normal_form hn K hK σ hσ).2.2.2.2.2.1
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.D4.tag) K),
      H = graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
      GGRawFieldConj p (LargeEvenCenterQuot H) (markIDImage (IsRoot TwistTag.D4.tag) K H)
        (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K H) from key _ hH
  intro H hH'
  subst hH'
  exact ggRawFieldConj_C0_D4 hn hK σ hσ hp hp3

theorem ggRawFieldConj_triD4 {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (hp : p.Prime) (hp3 : p ≠ 3) :
    GGRawFieldConj p (LargeEvenCenterQuot
        (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm n))
      (LargeEvenChevIDImage TwistTag.D4.tag.cartan K _)
      (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K _) := by
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  have : CharP K 2 := charP_two_of_card hK3
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  have h := (twistedConjOn_isRoot_D4 hn hK σ hσ hp hp3).of_eq
    (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag).symm
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.D4.tag.cartan K),
      H = MarkChev.twistedH TwistTag.D4.tag.cartan (LargeEvenIsRoot TwistTag.D4.tag.cartan) K
        TwistTag.D4.perm n →
      GGRawFieldConj p (LargeEvenCenterQuot H) (LargeEvenChevIDImage TwistTag.D4.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h

end RecipeExcLang

open RecipeExcLang

theorem ggRawFieldConjOn_triD4 :
    GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧ lab.tag = .triD4 := by
  intro p hp _ lab hlab ⟨hne, ht⟩ Q h
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht hne
  subst ht
  have hp3 : p ≠ 3 := fun h3 => hne ⟨rfl, h3⟩
  obtain ⟨hn, -⟩ := hlab
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggRawFieldConj_triD4 hn hK hp hp3⟩

end CFSG.StandardType
