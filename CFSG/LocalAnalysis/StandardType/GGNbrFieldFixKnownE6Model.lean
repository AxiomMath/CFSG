module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Arith
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Fixed
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Geom
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Restrict
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.RecipeExcLang

@[expose] def E6FixConcl {S : (Fin Tag.E6.rank → ℤ) → Prop} {K k : Type} [Field K] [Field k]
    (H : Subgroup (MarkChev.GLS S K)) (H₀ : Subgroup (MarkChev.GLS S k))
    (f : MulAut (LargeEvenCenterQuot H)) : Prop :=
  IsSimpleGroup (LargeEvenCenterQuot H₀) ∧ (∃ a b : LargeEvenCenterQuot H₀, a * b ≠ b * a) ∧
    ∃ θ₀ : ggFixDer f ≃* LargeEvenCenterQuot H₀,
      GGFixGeom (markIDImage S K H) f (markIDImage S k H₀) θ₀

@[expose] def E6FixOn (K : Type) [Field K] (S : (Fin Tag.E6.rank → ℤ) → Prop) (n p : ℕ) : Prop :=
  ∀ H : Subgroup (MarkChev.GLS S K), H = MarkChev.chevH Tag.E6.cartan S K false →
    ∀ f ∈ RecipeFieldExcInn.markFieldImage S K H, orderOf f = p →
      ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (n / p) ∧
        ∀ H₀ : Subgroup (MarkChev.GLS S k), H₀ = MarkChev.chevH Tag.E6.cartan S k false →
          E6FixConcl H H₀ f

theorem E6FixOn.of_eq {K : Type} [Field K] {S S' : (Fin Tag.E6.rank → ℤ) → Prop} {n p : ℕ}
    (hS : S = S') (h : E6FixOn K S n p) : E6FixOn K S' n p :=
  hS ▸ h

section Model

theorem e6FixOn_isRoot
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hF : p ∣ 2 ^ n - 1) : E6FixOn K (IsRoot Tag.E6) n p := by
  intro H hH f hf hord
  rw [chevH_false_eq_adjointGroup K Tag.E6] at hH
  subst hH
  have hrank : 0 < Tag.E6.rank := by decide
  obtain ⟨σ, hσ⟩ :=
    RecipeExcLang.autEquiv_eq_entrywise_of_mem_markField (τ := Tag.E6) (K := K) hf
  have hσord : orderOf σ = p := by
    rw [← CFSG.RankThree.Chevalley.SteinbergBT.orderOf_entrywiseAdjointAut
      (τ := Tag.E6) (K := K) hrank σ, ← hσ, MulEquiv.orderOf_eq, hord]
  have hσpow : σ ^ p = 1 := by
    rw [← hσord]
    exact pow_orderOf_eq_one σ
  have hcop : Nat.Coprime p 3 := (Nat.coprime_primes hp Nat.prime_three).2 hp3
  obtain ⟨hdvd, hcardfix⟩ :=
    CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      Nat.prime_two hn hK σ
  rw [hσord] at hdvd hcardfix
  have hbig : 2 < Nat.card (fixSubfield σ) := by
    rw [hcardfix]
    exact two_lt_two_pow_div_of_dvd hp hp2 hdvd hn hF
  let m : LargeEvenCenterQuot (adjointGroup Tag.E6 K) ≃* adjointGroup Tag.E6 K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  let m₀ : LargeEvenCenterQuot (adjointGroup Tag.E6 ↥(fixSubfield σ)) ≃*
      adjointGroup Tag.E6 ↥(fixSubfield σ) :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot
  have hm : MulAut.congr m = autEquiv Tag.E6 K := rfl
  have hm₀ : MulAut.congr m₀ = autEquiv Tag.E6 ↥(fixSubfield σ) := rfl
  have hs : entrywiseAdjointAut Tag.E6 σ = MulAut.congr m f := by
    rw [← hσ, ← hm]
  refine ⟨↥(fixSubfield σ), inferInstance, inferInstance, hcardfix, ?_⟩
  intro H₀ hH₀
  rw [chevH_false_eq_adjointGroup ↥(fixSubfield σ) Tag.E6] at hH₀
  subst hH₀
  have hq : CFSG.IsQuasisimple ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) :=
    CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 ↥(fixSubfield σ)
  haveI : IsSimpleGroup (LargeEvenCenterQuot (adjointGroup Tag.E6 ↥(fixSubfield σ))) :=
    hq.2.1
  refine ⟨hq.2.1, hq.2.2, ?_⟩
  refine ggFixGeom_of_transport hq.2.2 m m₀ hs (E6FieldFix.fixE6Equiv σ hσpow hcop) ?_ ?_
  · intro φ hφ hcomm
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hc : inndiagConj Tag.E6 K w * entrywiseAdjointAut Tag.E6 σ =
        entrywiseAdjointAut Tag.E6 σ * inndiagConj Tag.E6 K w := by
      have h1 := congrArg (MulAut.congr m) hcomm
      rwa [map_mul, map_mul, hwm, ← hs] at h1
    obtain ⟨w₀, hw₀⟩ :=
      E6FieldFix.exists_inndiagConj_restrict hn hK hp hσord hσpow hcop w hc
    refine ⟨(autEquiv Tag.E6 ↥(fixSubfield σ)).symm
      (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀), ?_, ?_⟩
    · exact RecipeExcLang.inndiagConj_mem_markID w₀
    · intro y
      have h0 : MulAut.congr m₀ ((autEquiv Tag.E6 ↥(fixSubfield σ)).symm
          (inndiagConj Tag.E6 ↥(fixSubfield σ) w₀)) =
          inndiagConj Tag.E6 ↥(fixSubfield σ) w₀ := by
        rw [← hm₀]
        exact MulEquiv.apply_symm_apply _ _
      rw [hwm, h0]
      exact hw₀ y
  · intro φ hφ hcomm hfix
    obtain ⟨w, hw⟩ :=
      RecipeExcLang.exists_inndiagConj_of_mem_markID (τ := Tag.E6) (K := K) hφ
    have hwm : MulAut.congr m φ = inndiagConj Tag.E6 K w := by
      rw [← hw, ← hm]
    have hfixw : ∀ x : ↥(ggFixSub (entrywiseAdjointAut Tag.E6 σ)),
        inndiagConj Tag.E6 K w (x : adjointGroup Tag.E6 K) = x := by
      intro x
      rw [← hwm]
      exact hfix x
    have hw1 : inndiagConj Tag.E6 K w = 1 :=
      E6FieldFix.eq_one_of_inndiagConj_fixes hbig w hfixw
    have h1 : MulAut.congr m φ = 1 := by rw [hwm, hw1]
    exact (MulAut.congr m).injective (by rw [h1, map_one])

theorem e6_fixStd
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hF : p ∣ 2 ^ n - 1)
    {f : MulAut (LargeEvenCenterQuot (LargeEvenChevH Tag.E6.cartan K false))}
    (hf : f ∈ LargeEvenChevFieldImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false))
    (hord : orderOf f = p) :
    LargeEvenRecipeChevalley Tag.E6.cartan (2 ^ (n / p)) false fun R₀ _ I₀ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧
        ∃ θ₀ : ggFixDer f ≃* R₀,
          GGFixGeom
            (LargeEvenChevIDImage Tag.E6.cartan K (LargeEvenChevH Tag.E6.cartan K false)) f I₀
            θ₀ := by
  have h := (e6FixOn_isRoot hn hK hp hp2 hp3 hF).of_eq (largeEvenIsRoot_eq_isRoot Tag.E6).symm
  obtain ⟨k, _, _, hk, hconcl⟩ :=
    h (LargeEvenChevH Tag.E6.cartan K false) (largeEvenChevH_eq _ K false) f hf hord
  refine ⟨k, inferInstance, inferInstance, hk, ?_⟩
  obtain ⟨hs, hna, θ₀, hg⟩ :=
    hconcl (LargeEvenChevH Tag.E6.cartan k false) (largeEvenChevH_eq _ k false)
  refine ⟨hs, hna, θ₀, ?_⟩
  rw [largeEvenChevIDImage_eq, largeEvenChevIDImage_eq]
  exact hg

end Model

end CFSG.StandardType

end
