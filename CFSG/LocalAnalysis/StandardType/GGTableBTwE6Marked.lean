module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcCoverRows
public import CFSG.LocalAnalysis.StandardType.GGTableBMarkedTheta
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley RawAutTwE6 RecipeFieldE6 RecipeFieldExcInn

private def TwE6FieldHinj (n : ℕ) (K : Type) [Field K] [Finite K]
    (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop) : Prop :=
  ∀ Θ : MulAut (LargeEvenCenterQuot
      (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)) →* RingAut K,
    (∀ (σ : K ≃+* K) (φ : MulAut (LargeEvenCenterQuot
        (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n))),
      φ ∈ markFieldImage S K (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n) →
      (∀ h h' : MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n,
        ((h' : MarkChev.GLS S K) : Module.End K (MarkChev.Space S K)) =
          MarkChev.entrywise S K σ (map_zero σ) ((h : MarkChev.GLS S K) : Module.End K _) →
        φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h') → Θ φ = σ) →
    ∀ φ ∈ Subgroup.closure (markFieldImage S K
        (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)), Θ φ = 1 → φ = 1

private theorem twE6_fieldHinj_isRoot
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    TwE6FieldHinj n K (IsRoot TwistTag.E6.tag) := by
  have hchar : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  set σ₀ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ₀ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, hfield, -, -, -, -, hZ, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ₀ hσ
  have hC : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K TwistTag.E6.perm n
      = twistedE6RootGroup K σ₀ := by
    rw [twistedH_eq_commutator K .E6 n σ₀.toRingHom hσ]
    exact (finite_fixed_root_group_perfect TwistTag.E6 Nat.prime_two hn K hK σ₀.toRingHom hσ).2.2.1
  unfold TwE6FieldHinj
  suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
      H = twistedE6RootGroup K σ₀ →
      ∀ (Θ : MulAut (LargeEvenCenterQuot H) →* RingAut K),
        (∀ (σ : K ≃+* K) (φ : MulAut (LargeEvenCenterQuot H)),
          φ ∈ markFieldImage (IsRoot TwistTag.E6.tag) K H →
          (∀ h h' : H,
            ((h' : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
                Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) =
              MarkChev.entrywise (IsRoot TwistTag.E6.tag) K σ (map_zero σ)
                ((h : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
                  Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) →
            φ (LargeEvenCenterMk _ h) = LargeEvenCenterMk _ h') → Θ φ = σ) →
        ∀ φ ∈ Subgroup.closure (markFieldImage (IsRoot TwistTag.E6.tag) K H), Θ φ = 1 → φ = 1 from
    key _ hC
  intro H hH
  subst hH
  intro Θ hfieldQ φ hφ hΘ1
  let Ψ : RingAut K →* MulAut (LargeEvenCenterQuot (twistedE6RootGroup K σ₀)) :=
    ((MulAut.congr (centerQuotEquivOfBot hZ)).symm).toMonoidHom.comp (fieldActorHom σ₀)
  have hΨapply : ∀ σ : RingAut K,
      Ψ σ = (MulAut.congr (centerQuotEquivOfBot hZ)).symm (fieldActor σ₀ σ) := fun σ => rfl
  have hΨact : ∀ σ : RingAut K,
      ∀ h h' : twistedE6RootGroup K σ₀,
        ((h' : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
            Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) =
          MarkChev.entrywise (IsRoot TwistTag.E6.tag) K (⇑σ) (map_zero σ)
            ((h : MarkChev.GLS (IsRoot TwistTag.E6.tag) K) :
              Module.End K (MarkChev.Space (IsRoot TwistTag.E6.tag) K)) →
        Ψ σ (LargeEvenCenterMk (twistedE6RootGroup K σ₀) h) =
          LargeEvenCenterMk (twistedE6RootGroup K σ₀) h' := by
    intro σ h h' hh'
    rw [hΨapply σ]
    rw [congr_centerQuotEquivOfBot_mk hZ
      ((MulAut.congr (centerQuotEquivOfBot hZ)).symm (fieldActor σ₀ σ)) h]
    have h1 : (MulAut.congr (centerQuotEquivOfBot hZ))
          ((MulAut.congr (centerQuotEquivOfBot hZ)).symm (fieldActor σ₀ σ)) =
        fieldActor σ₀ σ := MulEquiv.apply_symm_apply _ _
    rw [h1]
    apply congrArg (LargeEvenCenterMk (twistedE6RootGroup K σ₀))
    apply Subtype.ext
    apply Units.ext
    rw [hfield, hh']
    rfl
  have hΨmem : ∀ σ : RingAut K,
      Ψ σ ∈ markFieldImage (IsRoot TwistTag.E6.tag) K (twistedE6RootGroup K σ₀) :=
    fun σ => ⟨σ, hΨact σ⟩
  have hΘΨ : ∀ σ : RingAut K, Θ (Ψ σ) = σ := fun σ =>
    hfieldQ σ (Ψ σ) (hΨmem σ) (hΨact σ)
  have hFle : Subgroup.closure (markFieldImage (IsRoot TwistTag.E6.tag) K
        (twistedE6RootGroup K σ₀)) ≤ Ψ.range := by
    rw [Subgroup.closure_le]
    intro f hf
    obtain ⟨σ, hσf⟩ := hf
    have he : MulAut.congr (centerQuotEquivOfBot hZ) f = fieldActor σ₀ σ := by
      refine MulEquiv.ext fun h => ?_
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
        centerQuotEquivOfBot_symm, hσf h (fieldActor σ₀ σ h) (by rfl),
        centerQuotEquivOfBot_mk]
    refine ⟨σ, ?_⟩
    rw [hΨapply]
    rw [← he, MulEquiv.symm_apply_apply]
  obtain ⟨σ, hσeq⟩ := hFle hφ
  have hσ1 : σ = 1 := by rw [← hΘΨ σ, hσeq, hΘ1]
  rw [← hσeq, hσ1, map_one]

private theorem twE6_fieldHinj
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) :
    TwE6FieldHinj n K (LargeEvenIsRoot TwistTag.E6.tag.cartan) :=
  (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm ▸ twE6_fieldHinj_isRoot hn K hK

private theorem exists_marked_factorization_twE6_aux
    {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) :
    ∃ f : MulAut (LargeEvenCenterQuot
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)),
      GGTableBFieldSylowMark p
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
          (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) f ∧
      GGTableBMarkedFactorization p
        (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
          (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) f := by
  have hcyc : IsCyclic (K ≃+* K) :=
    isCyclic_ringEquiv_of_card (f := n * 2) (by rw [hK, pow_mul])
  have hfin : Finite (K ≃+* K) :=
    Finite.of_injective (fun f : K ≃+* K => (f : K → K))
      (fun f g h => RingEquiv.ext (congrFun h))
  rw [largeEvenTwistedH_eq TwistTag.E6.tag.cartan K TwistTag.E6.perm n]
  have hQ := twE6Quot_recipe hn K hK
  obtain ⟨Θ, -, hker, hfieldQ, hex⟩ := hQ
  obtain ⟨σg, hσg, hgen⟩ := exists_pPart_generator_of_isCyclic (G := K ≃+* K) hp
  refine exists_marked_of_quotient Θ σg hσg hgen ?_ ?_ ?_
  · obtain ⟨φ, hφ, hΘφ⟩ := hex σg
    exact ⟨φ, Subgroup.subset_closure hφ, hΘφ⟩
  · exact twE6_fieldHinj hn K hK Θ hfieldQ
  · intro φ h1
    exact mem_chevID_iff_isInnDiagOn.mpr ((hker φ).mp h1)

theorem exists_marked_factorization_twE6
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hrow : GGL48TBTwE6Row p lab) :
    LargeEvenLabelAll lab fun R _ I F =>
      ∃ f : MulAut R, GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, -⟩ := hlab
  obtain ⟨ht, -, -⟩ := hrow
  dsimp only at ht
  subst ht
  intro Q hQ
  exact recipeTwisted_and
    (P := fun R _ I F => ∃ f : MulAut R,
      GGTableBFieldSylowMark p F f ∧ GGTableBMarkedFactorization p I f)
    (fun K _ _ hK => exists_marked_factorization_twE6_aux hn K hK hp) hQ

end CFSG.StandardType
