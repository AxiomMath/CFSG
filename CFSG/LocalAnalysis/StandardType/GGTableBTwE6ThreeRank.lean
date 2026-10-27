module

public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6Dvd

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RecipeFieldE6

namespace TwE6Three

noncomputable abbrev recipeJ (K : Type) [Field K] (n : ℕ) :
    Subgroup (MulAut (TwE6Delta.RecipeR K n)) :=
  Subgroup.closure (LargeEvenInnSet _ ∪
    LargeEvenChevDiagImage (LargeEvenCartanE 6) K (TwE6Delta.RecipeH K n))

theorem mem_recipeJ_iff {K : Type} [Field K] {n : ℕ} {φ : MulAut (TwE6Delta.RecipeR K n)} :
    φ ∈ recipeJ K n ↔ φ ∈ TwE6Delta.RecipeI K n :=
  Iff.rfl

variable {n : ℕ} {K : Type} [Field K] [Finite K]

theorem exists_theta (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    ∃ Θ : MulAut (TwE6Delta.RecipeR K n) →* (K ≃+* K),
      ∀ φ, Θ φ = 1 → φ ∈ TwE6Delta.RecipeI K n := by
  have hQ := RawAutTwE6.twE6Quot_recipe hn K hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      ∃ Θ : MulAut (LargeEvenCenterQuot H) →* (K ≃+* K),
        ∀ φ, Θ φ = 1 → φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  obtain ⟨Θ, -, hker, -, -⟩ := hQ
  exact ⟨Θ, fun φ h => mem_chevID_iff_isInnDiagOn.mpr ((hker φ).mp h)⟩

theorem card_le_three_mul_inf (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {E : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 * Nat.card (E ⊓ recipeJ K n : Subgroup (MulAut (TwE6Delta.RecipeR K n))) := by
  have := TwE6Delta.finite_mulAut_recipeR hK
  obtain ⟨Θ, hker⟩ := exists_theta hn hK
  have hcyc : IsCyclic (K ≃+* K) :=
    TableBExc.isCyclic_ringAut K (f := 2 * n) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  set φ : E →* (K ≃+* K) := Θ.comp E.subtype with hφ
  have h1 := TableB.card_range_mul_card_ker φ
  have hrange : Nat.card φ.range ≤ 3 := by
    have : Finite φ.range := Finite.of_surjective _ φ.rangeRestrict_surjective
    refine TableB.card_le_of_isCyclic (by norm_num) inferInstance ?_
    rintro _ ⟨e, rfl⟩
    rw [← map_pow, show e ^ 3 = 1 from Subtype.ext (hE.2 e e.2), map_one]
  have hkerle : Nat.card φ.ker ≤
      Nat.card (E ⊓ recipeJ K n : Subgroup (MulAut (TwE6Delta.RecipeR K n))) := by
    refine Nat.card_le_card_of_injective
      (fun e => (⟨(e : E), (e : E).2, hker _ (MonoidHom.mem_ker.mp e.2)⟩ :
          (E ⊓ recipeJ K n : Subgroup (MulAut (TwE6Delta.RecipeR K n))))) fun x y hxy => ?_
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (E ⊓ recipeJ K n : Subgroup (MulAut (TwE6Delta.RecipeR K n))) =>
      (z : MulAut (TwE6Delta.RecipeR K n))) hxy
  calc Nat.card E = Nat.card φ.range * Nat.card φ.ker := h1.symm
    _ ≤ 3 * Nat.card (E ⊓ recipeJ K n : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :=
      Nat.mul_le_mul hrange hkerle

theorem le_recipeJ_of_not_dvd (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (h3n : ¬ 3 ∣ n)
    {E : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hE : IsElemAbelian 3 E) :
    E ≤ recipeJ K n := fun φ hφ =>
  TwE6Per.mem_recipeI_of_pow_eq_one hn hK Nat.prime_three (by norm_num) h3n (hE.2 φ hφ)

theorem card_le_of_inndiag (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hX : ∀ X : Subgroup (MulAut (TwE6Delta.RecipeR K n)), IsElemAbelian 3 X →
      (X : Set (MulAut (TwE6Delta.RecipeR K n))) ⊆ TwE6Delta.RecipeI K n → Nat.card X ≤ 3 ^ 6)
    {E : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 7 ∧ (¬ 3 ∣ n → Nat.card E ≤ 3 ^ 6) := by
  refine ⟨?_, fun h3n => hX E hE (le_recipeJ_of_not_dvd hn hK h3n hE)⟩
  have hEJ := hX _ (TableB.isElemAbelian_mono hE inf_le_left) fun φ hφ => hφ.2
  calc Nat.card E ≤ 3 * Nat.card (E ⊓ recipeJ K n :
        Subgroup (MulAut (TwE6Delta.RecipeR K n))) := card_le_three_mul_inf hn hK hE
    _ ≤ 3 * 3 ^ 6 := Nat.mul_le_mul_left _ hEJ
    _ = 3 ^ 7 := by norm_num

end TwE6Three

end CFSG.StandardType
