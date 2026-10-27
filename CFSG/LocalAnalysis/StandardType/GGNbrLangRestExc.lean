module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRestField
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTriality
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagRee
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form)

@[expose] def GGExcCoprimeDegLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ (lab.tag = .triD4 ∧ p ≠ 3) ∨
    lab.tag = .twF4 ∨ lab.tag = .twB2) ∧ ¬ p ∣ lab.n

namespace NbrLangRest

theorem pow_mem_of_hom_ker_eq_inn {R C Γ : Type*} [Group R] [Group C] [Group Γ] (e : R ≃* C)
    {I : Set (MulAut R)} (hinn : ∀ r : R, MulAut.conj r ∈ I) (Θ : MulAut C →* Γ)
    (hker : Θ.ker = (MulAut.conj : C →* MulAut C).range) {p : ℕ}
    (hΓ : ∀ γ : Γ, γ ^ p = 1 → γ = 1) (φ : MulAut R) (hφ : φ ^ p = 1) : φ ∈ I := by
  have h1 : Θ (MulAut.congr e φ) ^ p = 1 := by rw [← map_pow, ← map_pow, hφ, map_one, map_one]
  have h2 : MulAut.congr e φ ∈ Θ.ker := hΓ _ h1
  rw [hker] at h2
  obtain ⟨c, hc⟩ := h2
  have h3 : φ = MulAut.conj (e.symm c) := by
    apply (MulAut.congr e).injective
    rw [mulAut_congr_conj, MulEquiv.apply_symm_apply, hc]
  rw [h3]
  exact hinn _

theorem eq_one_of_pow_ringAut {K : Type} [Field K] [Finite K] {f p : ℕ} (hp : p.Prime)
    (hK : Nat.card K = 2 ^ f) (hpf : ¬ p ∣ f) {γ : K ≃+* K} (hγ : γ ^ p = 1) : γ = 1 := by
  have h1 : orderOf γ ∣ p := orderOf_dvd_of_pow_eq_one hγ
  have h2 : orderOf γ ∣ f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hK).1 ▸
      orderOf_dvd_natCard γ
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ h2) hpf

theorem eq_one_of_pow_zmod {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    {γ : Multiplicative (ZMod (2 * f))} (hγ : γ ^ p = 1) : γ = 1 := by
  have : NeZero (2 * f) := ⟨by omega⟩
  have h1 : orderOf γ ∣ p := orderOf_dvd_of_pow_eq_one hγ
  have h2 : orderOf γ ∣ 2 * f := by
    have := orderOf_dvd_natCard γ
    rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at this
  rcases (Nat.dvd_prime hp).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    rcases (Nat.Prime.dvd_mul hp).mp h2 with h' | h'
    · exact absurd (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h') hp.two_le) hp2
    · exact absurd h' hpf

theorem eq_one_of_pow_of_dvd {M : Type*} [Monoid M] {γ : M} {p m : ℕ} (hp : p.Prime)
    (hγ : γ ^ p = 1) (hm : orderOf γ ∣ m) (hpm : ¬ p ∣ m) : γ = 1 := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hγ) with h | h
  · exact orderOf_eq_one_iff.mp h
  · exact absurd (h ▸ hm) hpm

theorem recipeSuzuki_pow_mem {a p : ℕ} (ha : 1 ≤ a)
    (hp : p.Prime) (hpa : ¬ p ∣ 2 * a + 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F => Q R I F ∧ ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      ∀ φ : MulAut (LargeEvenCenterQuot H), φ ^ p = 1 → φ ∈ LargeEvenInnSet _ from
    key _ (largeEvenSzGroup_eq a K)
  rintro H rfl
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  have hcard := (CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK).2
  exact pow_mem_of_hom_ker_eq_inn (centerQuotEquivOfBot hZ)
    (fun r => show MulAut.conj r ∈ Set.range MulAut.conj from Set.mem_range_self r)
    (QuotientGroup.mk' (inner _)) (QuotientGroup.ker_mk' _)
    (fun γ hγ => eq_one_of_pow_of_dvd hp hγ ((orderOf_dvd_natCard γ).trans hcard) hpa)

section Exc


theorem recipeTwF4_pow_mem {a p : ℕ} (ha : 1 ≤ a) (hp : p.Prime) (hpa : ¬ p ∣ 2 * a + 1)
    {Q : LargeEvenRawCont} (h : LargeEvenRecipeTwF4 a Q) :
    LargeEvenRecipeTwF4 a fun R _ I F => Q R I F ∧ ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have : CharP K ReeTag.F4.prime := charP_two_of_card hK
  obtain ⟨-, -, -, -, hcard, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  obtain ⟨e₁⟩ := centerQuot_twF4H_equiv K a
  obtain ⟨E⟩ := ReeTag.nonempty_derivedCentralQuotient_mulEquiv_reeGamma ha hK
  have e₂ : DerivedCentralQuotient (reeFixedGroup Tag.F4 K reeF4Perm
        fun i => if i ∈ reeF4Long then 2 ^ a else 2 ^ (a + 1)) ≃*
      DerivedCentralQuotient (ReeTag.F4.reeGamma K a) := by
    rw [ReeTag.reeGamma_eq_reeFixedGroup]
    exact MulEquiv.refl _
  exact pow_mem_of_hom_ker_eq_inn (e₁.trans (e₂.trans E)) (conj_mem_chevIDImage _)
    (QuotientGroup.mk' (inner _)) (QuotientGroup.ker_mk' _)
    (fun γ hγ => eq_one_of_pow_of_dvd hp hγ (hcard ▸ orderOf_dvd_natCard γ) hpa)

theorem largeEvenLabelAll_pow_mem_excCoprimeDeg {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGExcCoprimeDegLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨hn, hl⟩ := hlab
  obtain ⟨ht, hpn⟩ := h
  dsimp only at hn hpn
  intro Q hQ
  rcases ht with ht | ht | ht | ht | ⟨ht, hp3⟩ | ht | ht <;> dsimp only at ht <;> subst ht <;>
    dsimp only [LargeEvenRawDatum] at hQ ⊢
  · obtain ⟨-, hn2⟩ := hl
    refine recipeChevalley_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => ?_) hQ
    obtain ⟨-, Θ, -, -, hker, -⟩ :=
      CFSG.ComponentClassification.UnbalancedCatalog.even_G2_exact_automorphism_normal_form
        hn2 K hK
    exact pow_mem_of_hom_ker_eq_inn (recipeChevEquiv .G2 K) (conj_mem_chevIDImage _) Θ hker
      (fun γ hγ => eq_one_of_pow_ringAut hp hK hpn hγ)
  · refine recipeChevalley_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => ?_) hQ
    have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := charP_two_of_card hK
    obtain ⟨-, -, ⟨Θ, -, -, hker⟩, -⟩ := even_F4_exact_automorphism_normal_form hn K hK
    exact pow_mem_of_hom_ker_eq_inn (recipeChevEquiv .F4 K) (conj_mem_chevIDImage _) Θ hker
      (fun γ hγ => eq_one_of_pow_zmod hn hp hp2 hpn hγ)
  · refine recipeChevalley_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => ?_) hQ
    obtain ⟨-, Θ, -, -, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E7 (Or.inl rfl)
    exact pow_mem_of_hom_ker_eq_inn (recipeChevEquiv .E7 K) (conj_mem_chevIDImage _) Θ hker
      (fun γ hγ => eq_one_of_pow_ringAut hp hK hpn hγ)
  · refine recipeChevalley_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => ?_) hQ
    obtain ⟨-, Θ, -, -, hker, -⟩ :=
      even_E7_E8_exact_inner_field_automorphism_normal_form hn K hK .E8 (Or.inr rfl)
    exact pow_mem_of_hom_ker_eq_inn (recipeChevEquiv .E8 K) (conj_mem_chevIDImage _) Θ hker
      (fun γ hγ => eq_one_of_pow_ringAut hp hK hpn hγ)
  · refine recipeTwisted_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => ?_) hQ
    have : CharP K 2 := charP_two_of_card (m := n * 3) (by rw [hK, pow_mul])
    set σ := iterateFrobeniusEquiv K 2 n with hσdef
    have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
      rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
    obtain ⟨-, -, ⟨Θ, -, -, hker, -⟩, -, hcard, -, -, ⟨e₂⟩⟩ :=
      CFSG.LieType.Chevalley.even_triality_exact_automorphism_normal_form hn K hK σ hσ
    obtain ⟨e₁⟩ := centerQuot_twistedH_equiv K .D4 n σ.toRingHom hσ
    refine pow_mem_of_hom_ker_eq_inn (e₁.trans e₂) (conj_mem_chevIDImage _) Θ hker
      (fun γ hγ => ?_)
    have h1 : orderOf γ ∣ p := orderOf_dvd_of_pow_eq_one hγ
    have h2 : orderOf γ ∣ 3 * n := hcard ▸ orderOf_dvd_natCard γ
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at h2
      rcases (Nat.Prime.dvd_mul hp).mp h2 with h' | h'
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h') hp3
      · exact absurd h' hpn
  · obtain ⟨-, ⟨k, hk⟩, h3⟩ := hl
    dsimp only at hk h3
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    rw [e] at hQ ⊢
    exact recipeTwF4_pow_mem (by omega) hp hpn hQ
  · obtain ⟨-, ⟨k, hk⟩, h3⟩ := hl
    dsimp only at hk h3
    subst hk
    have e : (2 * k + 1 - 1) / 2 = k := by omega
    rw [e] at hQ ⊢
    exact recipeSuzuki_pow_mem (by omega) hp hpn hQ

end Exc

end NbrLangRest

open NbrLangRest

theorem ggNbrLangTorusAxisOn_excCoprimeDeg :
    GGNbrLangTorusAxisOn GGExcCoprimeDegLabel :=
  ggNbrLangTorusAxisOn_of_pow_mem fun _ _ hp hp2 hlab h =>
    largeEvenLabelAll_pow_mem_excCoprimeDeg hp hp2 hlab h

end CFSG.StandardType

end
