module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangPow

public section

namespace CFSG.StandardType.E6FieldFix

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang

variable {τ : Tag} {K : Type} [Field K] [Finite K]

private theorem iterateFrobenius_two_pow_apply_of_fixed [ExpChar K 2] {e : ℕ} (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2 ^ e) {a : K} (ha : σ a = a) :
    iterateFrobenius K 2 e a = a := by
  rw [iterateFrobenius_def]
  have ha' : a ∈ fixSubfield σ := (mem_fixSubfield σ).2 ha
  haveI : Fintype ↥(fixSubfield σ) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(fixSubfield σ) = 2 ^ e := by
    rw [← Nat.card_eq_fintype_card]
    exact hk
  have hb : (⟨a, ha'⟩ : fixSubfield σ) ^ Fintype.card ↥(fixSubfield σ) = ⟨a, ha'⟩ :=
    FiniteField.pow_card _
  have h2 : (fixSubfield σ).subtype ((⟨a, ha'⟩ : fixSubfield σ) ^
      Fintype.card ↥(fixSubfield σ)) = (fixSubfield σ).subtype ⟨a, ha'⟩ := by
    rw [hb]
  rw [map_pow, hcard] at h2
  simpa using h2

private theorem entrywise_iterateFrobenius_eq_self
    [ExpChar K 2] {e : ℕ} (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2 ^ e) {A : Module.End K (RootModule τ K)}
    (hA : entrywise σ.toRingHom A = A) :
    entrywise (iterateFrobenius K 2 e) A = A := by
  refine end_ext_single fun b => ?_
  rw [entrywise_single]
  apply Finsupp.ext
  intro l
  rw [Finsupp.mapRange_apply]
  refine iterateFrobenius_two_pow_apply_of_fixed σ hk ?_
  have h1 := congrArg (fun f : Module.End K (RootModule τ K) =>
    f (Finsupp.single b 1)) hA
  simp only [entrywise_single] at h1
  simpa using congrArg (fun x : RootModule τ K => x l) h1

theorem exists_inndiagGroup_of_fixed
    {n e : ℕ} (hK : Nat.card K = 2 ^ n) (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2 ^ e) {w : ModGL τ K} (hw : w ∈ inndiagGroup τ K)
    (hfix : Units.map (entrywiseHom σ.toRingHom) w = w) :
    ∃ w₀ ∈ inndiagGroup τ (fixSubfield σ), baseChangeGL (fixSubfield σ).subtype w₀ = w := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rw [← Nat.card_eq_fintype_card]
    exact hK
  set L := AlgebraicClosure K with hL
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : IsScalarTower (fixSubfield σ) K L := inferInstance
  have hιk : algebraMap (fixSubfield σ) L = (algebraMap K L).comp (fixSubfield σ).subtype :=
    IsScalarTower.algebraMap_eq (fixSubfield σ) K L
  haveI : Module.Finite (fixSubfield σ) K := inferInstance
  haveI : Algebra.IsAlgebraic (fixSubfield σ) K :=
    Algebra.IsAlgebraic.of_finite (fixSubfield σ) K
  haveI : Algebra.IsAlgebraic (fixSubfield σ) L :=
    Algebra.IsAlgebraic.trans (fixSubfield σ) K L
  set Fr := iterateFrobenius L 2 e with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ Nat.card (fixSubfield σ) := by
    intro c
    rw [hFrdef, iterateFrobenius_def, hk]
  have hW : baseChangeGL (algebraMap K L) w ∈ adjointGroup τ L :=
    baseChangeGL_mem_adjointGroup_of_mem_inndiag (algebraMap K L) hw
  have hTfix : Units.map (entrywiseHom (iterateFrobenius K 2 e)) w = w := by
    refine Units.ext ?_
    rw [Units.coe_map]
    exact entrywise_iterateFrobenius_eq_self σ hk (congrArg Units.val hfix)
  have hFrc : Fr.comp (algebraMap K L) = (algebraMap K L).comp (iterateFrobenius K 2 e) := by
    ext c
    simp only [RingHom.comp_apply, hFrdef, iterateFrobenius_def, map_pow]
  have hWfix : Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) w) =
      baseChangeGL (algebraMap K L) w := by
    rw [units_map_entrywiseHom_eq_baseChangeGL Fr]
    rw [baseChangeGL_baseChangeGL (f := algebraMap K L) (f' := Fr)]
    rw [hFrc]
    rw [← baseChangeGL_baseChangeGL (f := iterateFrobenius K 2 e) (f' := algebraMap K L)]
    rw [← units_map_entrywiseHom_eq_baseChangeGL (iterateFrobenius K 2 e)]
    rw [hTfix]
  obtain ⟨a, u, hu, hWu⟩ :=
    exists_rootDiagUnit_mul_of_frobenius_fixed (K := fixSubfield σ) (L := L) τ Fr hFr hW hWfix
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  have hmul : baseChangeGL (algebraMap (fixSubfield σ) L) (rootDiagUnit τ a * u₀) =
      baseChangeGL (algebraMap K L) w := by
    rw [map_mul, ← hWu]
  refine ⟨rootDiagUnit τ a * u₀, ⟨a, u₀, hu₀, rfl⟩, ?_⟩
  apply baseChangeGL_injective (algebraMap K L)
  rw [baseChangeGL_baseChangeGL, ← hιk]
  exact hmul

end CFSG.StandardType.E6FieldFix

end
