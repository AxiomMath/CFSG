module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourToral
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6DeltaOutdiag
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw
public import CFSG.LocalAnalysis.StandardType.GGE6RankFiveTorality

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
  CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.PartOne.KE

theorem e6AdLangToral_of_toral {Ω' : Type} [Field Ω'] [IsAlgClosed Ω'] [CharP Ω' 2] {n : ℕ}
    (hn : 1 ≤ n) (Fr' : Ω' →+* Ω') (hFr' : ∀ c, Fr' c = c ^ 2 ^ n)
    {X : Subgroup (ModGL Tag.E6 Ω')} (hXR : X ≤ TwistedDiag.Rgrp Ω' Fr') (h : E6AdToral X) :
    E6AdLangToral Fr' X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain rfl : Fr' = iterateFrobenius Ω' 2 n := RingHom.ext fun c => by
    rw [hFr', iterateFrobenius_def]
  obtain ⟨C, hC, hCX⟩ := h
  exact exists_lang_torus_of_conj_torus_twisted' (L := Ω') 2 TwistTag.E6 n hn
    (fun x hx => ((TwistedDiag.mem_Rgrp _).1 (hXR hx)).2) hC hCX

section Model

variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)

@[expose] noncomputable def rgrpRecipeAut :
    ↥(TwistedDiag.Rgrp Ω Fr) →* MulAut (TwE6Delta.RecipeR K n) :=
  (MulAut.congr ε).toMonoidHom.comp (rgrpConjAut hn hK σ hσ Fr hFr)

private theorem rgrpRecipeAut_def (r : ↥(TwistedDiag.Rgrp Ω Fr)) :
    rgrpRecipeAut hn hK σ hσ Fr hFr ε r = MulAut.congr ε (rgrpConjAut hn hK σ hσ Fr hFr r) :=
  rfl

private theorem symm_rgrpRecipeAut (r : ↥(TwistedDiag.Rgrp Ω Fr)) :
    (MulAut.congr ε).symm (rgrpRecipeAut hn hK σ hσ Fr hFr ε r) =
      rgrpConjAut hn hK σ hσ Fr hFr r := by
  rw [rgrpRecipeAut_def, MulEquiv.symm_apply_apply]

theorem rgrpRecipeAut_injective : Function.Injective (rgrpRecipeAut hn hK σ hσ Fr hFr ε) :=
  fun r s h => rgrpConjAut_injective hn hK σ hσ Fr hFr ((MulAut.congr ε).injective
    (by rwa [rgrpRecipeAut_def, rgrpRecipeAut_def] at h))

theorem rgrpRecipeAut_apply (r : ↥(TwistedDiag.Rgrp Ω Fr))
    (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ε c) = ε (rgrpConjAut hn hK σ hσ Fr hFr r c) := by
  rw [rgrpRecipeAut_def, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]

theorem mem_range_rgrpRecipeAut
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (φ : MulAut (TwE6Delta.RecipeR K n)) :
    φ ∈ (rgrpRecipeAut hn hK σ hσ Fr hFr ε).range ↔ φ ∈ TwE6Delta.RecipeI K n := by
  have h := hε ((MulAut.congr ε).symm φ)
  rw [MulEquiv.apply_symm_apply, ← rgrpConjAut_range hn hK σ hσ Fr hFr] at h
  rw [h]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, (symm_rgrpRecipeAut hn hK σ hσ Fr hFr ε r).symm⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by rw [rgrpRecipeAut_def, hr, MulEquiv.apply_symm_apply]⟩

theorem baseChange_rgrpConjAut (r : ↥(TwistedDiag.Rgrp Ω Fr))
    (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (rgrpConjAut hn hK σ hσ Fr hFr r c).1 =
      r.1 * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 * r.1⁻¹ := by
  have key : ∀ a b : ModGL TwistTag.E6.tag K,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) (a * b * a⁻¹) =
        baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a *
          baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) b *
            (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective r
  rw [rgrpConjAut_apply_baseChange, RecipeExcLang.coe_twConj]
  exact key w.1 c.1

@[expose] noncomputable def rgrpModel (A : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
    Subgroup (ModGL Tag.E6 Ω) :=
  (A.comap (rgrpRecipeAut hn hK σ hσ Fr hFr ε)).map (TwistedDiag.Rgrp Ω Fr).subtype

theorem rgrpModel_le_Rgrp (A : Subgroup (MulAut (TwE6Delta.RecipeR K n))) :
    rgrpModel hn hK σ hσ Fr hFr ε A ≤ TwistedDiag.Rgrp Ω Fr :=
  Subgroup.map_subtype_le _

theorem mem_rgrpModel {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} {x : ModGL Tag.E6 Ω} :
    x ∈ rgrpModel hn hK σ hσ Fr hFr ε A ↔
      ∃ hx : x ∈ TwistedDiag.Rgrp Ω Fr, rgrpRecipeAut hn hK σ hσ Fr hFr ε ⟨x, hx⟩ ∈ A := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r.2, hr⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem card_rgrpModel
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} (hAI : ∀ φ ∈ A, φ ∈ TwE6Delta.RecipeI K n) :
    Nat.card (rgrpModel hn hK σ hσ Fr hFr ε A) = Nat.card A := by
  have hle : A ≤ (rgrpRecipeAut hn hK σ hσ Fr hFr ε).range := fun φ hφ =>
    (mem_range_rgrpRecipeAut hn hK σ hσ Fr hFr ε hε φ).2 (hAI φ hφ)
  rw [rgrpModel, Subgroup.card_map_of_injective Subtype.val_injective,
    ← Subgroup.card_map_of_injective (rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε),
    Subgroup.map_comap_eq_self hle]

theorem isElemAbelian_rgrpModel {p : ℕ} {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))}
    (hA : IsElemAbelian p A) : IsElemAbelian p (rgrpModel hn hK σ hσ Fr hFr ε A) :=
  (hA.comap (rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε)).map _

theorem exists_equiv_rgrpModel_of_cover
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l)) :
    ∃ e : ↥A ≃* ↥(rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)),
      (∀ (a : ↥A) (l : L'),
        (e a : ModGL Tag.E6 Ω) *
          baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ l)).1 *
          (e a : ModGL Tag.E6 Ω)⁻¹ =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ (a.1 l))).1) ∧
      ∀ (x : L') (hx : MulAut.conj x ∈ Subgroup.normalizer (A : Set (MulAut L')))
        (a : ↥A),
        (e (ggConjAut A hx a) : ModGL Tag.E6 Ω) =
          baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ x)).1 *
            (e a : ModGL Tag.E6 Ω) *
            (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ x)).1)⁻¹ := by
  classical
  let B := TypeA.inducedSub ψ A
  let Φ := rgrpRecipeAut hn hK σ hσ Fr hFr ε
  have hΦ : Function.Injective Φ := rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε
  have hB : B ≤ Φ.range := by
    intro b hb
    obtain ⟨a, ha, hba⟩ := TypeA.mem_inducedSub.mp hb
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    apply (mem_range_rgrpRecipeAut hn hK σ hσ Fr hFr ε hε b).2
    rwa [TypeA.induced_unique ψ hψ hba hφa]
  let e₀ : ↥(B.comap Φ) ≃* ↥B :=
    ((B.comap Φ).equivMapOfInjective Φ hΦ).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hB))
  let e₁ := (B.comap Φ).equivMapOfInjective (TwistedDiag.Rgrp Ω Fr).subtype
    (Subgroup.subtype_injective _)
  let e₂ := TypeA.inducedSubEquiv hψ hker hperf (fun a ha => by
    obtain ⟨φ, -, hφ⟩ := hAI a ha
    exact ⟨φ, hφ⟩)
  let e := e₂.trans (e₀.symm.trans e₁)
  have he : ∀ a : ↥A, Φ (e₀.symm (e₂ a)).1 = (e₂ a).1 := by
    intro a
    exact congrArg Subtype.val (e₀.apply_symm_apply (e₂ a))
  refine ⟨e, ?_, ?_⟩
  · intro a l
    let r : ↥(TwistedDiag.Rgrp Ω Fr) := (e₀.symm (e₂ a)).1
    have hr : Φ r = (e₂ a).1 := he a
    have hact : ε (rgrpConjAut hn hK σ hσ Fr hFr r (ε.symm (ψ l))) = ψ (a.1 l) := by
      rw [← rgrpRecipeAut_apply, MulEquiv.apply_symm_apply]
      change Φ r (ψ l) = ψ (a.1 l)
      rw [hr]
      exact TypeA.inducedSubEquiv_apply hψ hker hperf _ a l
    have hact' : rgrpConjAut hn hK σ hσ Fr hFr r (ε.symm (ψ l)) =
        ε.symm (ψ (a.1 l)) := by
      apply ε.injective
      rw [hact, MulEquiv.apply_symm_apply]
    change r.1 * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (ε.symm (ψ l)).1 * r.1⁻¹ = _
    rw [← baseChange_rgrpConjAut hn hK σ hσ Fr hFr, hact']
  · intro x hx a
    let c := ε.symm (ψ x)
    let r : ↥(TwistedDiag.Rgrp Ω Fr) := twInndiagEquivRgrp hn hK σ hσ Fr hFr
      ⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩
    have hr : r.1 = baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 :=
      twInndiagEquivRgrp_apply hn hK σ hσ Fr hFr _
    have hΦr : Φ r = MulAut.conj (ψ x) := by
      change MulAut.congr ε (rgrpConjAut hn hK σ hσ Fr hFr r) = _
      rw [rgrpConjAut_apply_baseChange, RecipeExcLang.twConj_of_mem_C0]
      ext m
      rw [MulAut.congr_apply]
      change ε (c * ε.symm m * c⁻¹) = ψ x * m * (ψ x)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    have hconj : Φ (e₀.symm (e₂ (ggConjAut A hx a))).1 =
        Φ (r * (e₀.symm (e₂ a)).1 * r⁻¹) := by
      rw [he, map_mul, map_mul, map_inv, hΦr, he]
      apply MulEquiv.ext
      intro m
      obtain ⟨l, rfl⟩ := hψ m
      rw [TypeA.inducedSubEquiv_apply]
      exact (TypeA.conj_induced_apply ψ (TypeA.inducedSubEquiv_apply hψ hker hperf _ a) x l).symm
    have h := congrArg Subtype.val (hΦ hconj)
    change (e (ggConjAut A hx a) : ModGL Tag.E6 Ω) =
      r.1 * (e a : ModGL Tag.E6 Ω) * r.1⁻¹ at h
    rwa [hr] at h

theorem card_le_four_of_not_e6AdToral_rgrpModel
    [CharP Ω 2]
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {A : Subgroup (MulAut (TwE6Delta.RecipeR K n))} [Finite A] (hA : IsElemAbelian 3 A)
    (hAI : ∀ φ ∈ A, φ ∈ TwE6Delta.RecipeI K n)
    (hNT : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε A)) : Nat.card A ≤ 3 ^ 4 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hcard := card_rgrpModel hn hK σ hσ Fr hFr ε hε hAI
  have : Finite (rgrpModel hn hK σ hσ Fr hFr ε A) :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hG : rgrpModel hn hK σ hσ Fr hFr ε A ≤ adjointGroup Tag.E6 Ω :=
    fun x hx => ((TwistedDiag.mem_Rgrp _).mp (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε A hx)).1
  rw [← hcard]
  exact E6RankFive.card_le_of_not_e6AdToral hG
    (isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε hA) hNT

theorem card_le_four_of_not_e6AdToral_rgrpModel_of_cover
    [CharP Ω 2]
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} [Finite A]
    (hA : IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hNT : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A))) :
    Nat.card A ≤ 3 ^ 4 := by
  have hact : ∀ a ∈ A, ∃ φ : MulAut (TwE6Delta.RecipeR K n),
      ∀ l, φ (ψ l) = ψ (a l) := fun a ha => (hAI a ha).imp fun _ h => h.2
  have hcard := TypeA.card_inducedSub hψ hker hperf hact
  have : Finite (TypeA.inducedSub ψ A) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  rw [← hcard]
  apply card_le_four_of_not_e6AdToral_rgrpModel hn hK σ hσ Fr hFr ε hε
    (TypeA.isElemAbelian_inducedSub hψ hA) _ hNT
  intro φ hφ
  obtain ⟨a, ha, hφa⟩ := TypeA.mem_inducedSub.mp hφ
  obtain ⟨φ', hφ', hφ'a⟩ := hAI a ha
  rwa [TypeA.induced_unique ψ hψ hφa hφ'a]

end Model

end CFSG.StandardType.SCFourCover

end
