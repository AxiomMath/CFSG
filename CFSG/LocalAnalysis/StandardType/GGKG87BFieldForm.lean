module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwE6Conj
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldTransport
import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherTwE6
import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

namespace CFSG.StandardType.KG87B

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_recipeEquiv_eq_fieldActor
    {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hconj : GGRawFieldConj 3 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n)
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)))
    (hs : IsSimpleGroup (TwE6Delta.RecipeR K n))
    (hna : ∃ a b : TwE6Delta.RecipeR K n, a * b ≠ b * a)
    {x : MulAut (TwE6Delta.RecipeR K n)}
    (hx : x ∈ Subgroup.closure (TwE6Delta.RecipeI K n ∪
      LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)))
    (hxI : x ∉ TwE6Delta.RecipeI K n) (hx3 : x ^ 3 = 1) :
    ∃ (d : ℕ) (ε : ↥(twistedE6RootGroup K σ) ≃* TwE6Delta.RecipeR K n) (δ : K ≃+* K),
      n = 3 * d ∧
      (∀ y, MulAut.congr ε y ∈ TwE6Delta.RecipeI K n ↔ y ∈ (RecipeExcLang.twConj K σ).range) ∧
      orderOf δ = 3 ∧ x = MulAut.congr ε (fieldActor (t := TwistTag.E6) σ δ) := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup (MulAut (TwE6Delta.RecipeR K n)),
      TwE6Delta.RecipeI K n = D := ⟨_, rfl⟩
  have hN : GGInndiagNormal (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) :=
    InndiagE6.ggInndiagNormal_twE6 hn K hK
  have hle : ggInndiag (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ≤ D := by
    refine sup_le ?_ ?_
    · rintro _ ⟨y, rfl⟩
      have hy : MulAut.conj y ∈ TwE6Delta.RecipeI K n :=
        Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
      rw [hD] at hy
      exact hy
    · rw [Subgroup.closure_le, hD]
  have : D.Normal := ⟨fun ψ hψ α => hle (hN α ψ (by rw [hD]; exact hψ))⟩
  have hcl : Subgroup.closure (TwE6Delta.RecipeI K n ∪
      LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) ≤
      D ⊔ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)) := by
    rw [Subgroup.closure_le]
    rintro y (hy | hy)
    · rw [hD] at hy
      exact Subgroup.mem_sup_left hy
    · exact Subgroup.mem_sup_right (Subgroup.subset_closure hy)
  obtain ⟨u, hu, f, hf, rfl⟩ : ∃ u ∈ D, ∃ f ∈ Subgroup.closure
      (LargeEvenChevFieldImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n)), u * f = x := by
    have h := hcl hx
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at h
    exact Set.mem_mul.mp h
  have huI : u ∈ TwE6Delta.RecipeI K n := by
    rw [hD]
    exact hu
  obtain ⟨f', hf'F, u', hu'I, hf'o, e⟩ := hconj hs hna u huI f hf hxI hx3
  obtain ⟨ε₀, hε₀, hF⟩ := TwE6FieldCore.exists_recipeConj_field hn hK σ hσ
  obtain ⟨δ, rfl⟩ := hF f' hf'F
  have hδ : orderOf δ = 3 := by
    rw [← TwE6FieldCore.orderOf_fieldActor hn hK hσ δ, ← MulEquiv.orderOf_eq (MulAut.congr ε₀),
      hf'o]
  obtain ⟨w, hw⟩ := (hε₀ u').2 hu'I
  have hK2n : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, -⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := 2 * n)
    Nat.prime_two (by omega) hK2n δ
  rw [hδ] at hdvd
  obtain ⟨d, hd⟩ : 3 ∣ n :=
    ((Nat.coprime_primes Nat.prime_three Nat.prime_two).2 (by norm_num)).dvd_of_dvd_mul_left hdvd
  have hkey : ∀ y, MulAut.congr ((RecipeExcLang.twConj K σ w).trans ε₀) y =
      MulAut.congr ε₀ (RecipeExcLang.twConj K σ w * y * (RecipeExcLang.twConj K σ w)⁻¹) :=
    fun y => MulEquiv.ext fun r => rfl
  refine ⟨d, (RecipeExcLang.twConj K σ w).trans ε₀, δ, hd, fun y => ?_, hδ, ?_⟩
  · rw [hkey, ← hε₀]
    constructor
    · rintro ⟨v, hv⟩
      rw [TwE6Transport.recipeConj_eq] at hv
      refine ⟨w⁻¹ * v * w, ?_⟩
      rw [map_mul, map_mul, map_inv, (MulAut.congr ε₀).injective hv]
      group
    · rintro ⟨v, rfl⟩
      refine ⟨w * v * w⁻¹, ?_⟩
      rw [TwE6Transport.recipeConj_eq, map_mul (RecipeExcLang.twConj K σ),
        map_mul (RecipeExcLang.twConj K σ), map_inv]
  · rw [e, ← hw, TwE6Transport.recipeConj_eq, hkey, map_mul, map_mul, map_inv]

end CFSG.StandardType.KG87B

end
