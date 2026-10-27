module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ConnectedReflection
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6ReflectionRadical
public import CFSG.LocalAnalysis.StandardType.GGCellWitness

public noncomputable section
namespace CFSG.StandardType.SCFourCover

open Subgroup CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent
  CFSG.LieType.AlgebraicGroups


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
  [Algebra K GGFinModel.GGL] [IsAlgClosure K GGFinModel.GGL]
  (Fr : GGFinModel.GGL →+* GGFinModel.GGL) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)

theorem reflection_difference_mem_connectedCentralizer_of_tableB
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    {A : Subgroup (MulAut L')} [Finite L']
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {φ : MulAut A}
    (hφA : φ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφ : GGIsReflection 3 φ) :
    ∀ a : A,
      (recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1
        hTB.2.2.2.2.1 (φ a * a⁻¹) : ModGL Tag.E6 GGFinModel.GGL) ∈
      closedIdentityComponent
        (adjointGroup Tag.E6 GGFinModel.GGL ⊓ centralizer
          (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) :
            Set (ModGL Tag.E6 GGFinModel.GGL))) := by
  classical
  obtain ⟨c, hcH, hg, hgφ_eq⟩ := eq_ggConjAut_of_mem_ggAutomizer hφA
  obtain ⟨g, rfl⟩ := hcH
  have hgφ : ggConjAut A hg = φ := hgφ_eq.symm
  intro a
  have h := reflection_difference_mem_full_connected_centralizer
    hn hK σ hσ Fr hFr ε hε hTB hnt hg hgφ hφ a
  simpa [map_mul, map_inv] using h

section B2

theorem reflectionProduct_pow_eighteen_eq_one_of_tableB
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    {A : Subgroup (MulAut L')} [Finite L']
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {φ₀ φ₁ : MulAut A}
    (hφ₀A : φ₀ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφ₁A : φ₁ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφ₀ : GGIsReflection 3 φ₀) (hφ₁ : GGIsReflection 3 φ₁) :
    (φ₀ * φ₁) ^ 18 = 1 := by
  classical
  haveI : IsAlgClosed GGFinModel.GGL := IsAlgClosure.isAlgClosed K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := CFSG.StandardType.charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have : CharP GGFinModel.GGL 2 := charP_of_injective_algebraMap (algebraMap K GGFinModel.GGL).injective 2
  let γ := recipeActorModelEquiv hn hK σ hσ Fr hFr ε hε hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1
  let E := rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  let S := closedIdentityComponent
    (adjointGroup Tag.E6 GGFinModel.GGL ⊓ centralizer (E : Set (ModGL Tag.E6 GGFinModel.GGL)))
  have hA : CFSG.Open.IsElemAbelian 3 A := hTB.2.2.2.1
  have hEG : E ≤ adjointGroup Tag.E6 GGFinModel.GGL := fun x hx =>
    ((TwistedDiag.mem_Rgrp _).mp (rgrpModel_le_Rgrp hn hK σ hσ Fr hFr ε _ hx)).1
  have hE : CFSG.Open.IsElemAbelian 3 E :=
    isElemAbelian_rgrpModel hn hK σ hσ Fr hFr ε (TypeA.isElemAbelian_inducedSub hTB.1 hA)
  have hcardA : Nat.card A = 3 ^ 4 := le_antisymm
    (card_le_four_of_not_e6AdToral_rgrpModel_of_cover hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.1 hTB.2.2.2.2.1 hnt)
    hTB.2.2.2.2.2.1
  have hcardE : Nat.card E = 3 ^ 4 :=
    (Nat.card_congr γ.toEquiv).symm.trans hcardA
  haveI : Finite E := Finite.of_equiv A γ
  have hP₀ : ∀ a : A,
      (γ (φ₀ a * a⁻¹) : ModGL Tag.E6 GGFinModel.GGL) ∈ S :=
    reflection_difference_mem_connectedCentralizer_of_tableB hn hK σ hσ Fr hFr ε hε
      hTB hnt hφ₀A hφ₀
  have hP₁ : ∀ a : A,
      (γ (φ₁ a * a⁻¹) : ModGL Tag.E6 GGFinModel.GGL) ∈ S :=
    reflection_difference_mem_connectedCentralizer_of_tableB hn hK σ hσ Fr hFr ε hε
      hTB hnt hφ₁A hφ₁
  let P : MulAut A → Prop := fun θ =>
    ∀ a : A, (γ (θ a * a⁻¹) : ModGL Tag.E6 GGFinModel.GGL) ∈ S
  have hP₀' : P φ₀ := hP₀
  have hP₁' : P φ₁ := hP₁
  have hPmul : ∀ θ η : MulAut A, P θ → P η → P (θ * η) := by
    intro θ η hθ hη a
    have harg : (θ * η) a * a⁻¹ =
        (θ (η a) * (η a)⁻¹) * ((η a) * a⁻¹) := by
      simp only [MulAut.mul_apply]
      group
    rw [harg, map_mul]
    exact S.mul_mem (hθ (η a)) (hη a)
  have hPone : P 1 := by
    intro a
    have h : (1 : MulAut A) a * a⁻¹ = 1 := by simp
    rw [h, map_one]
    simpa using Subgroup.one_mem S
  have hPpow : ∀ m : ℕ, ∀ θ : MulAut A, P θ → P (θ ^ m) := by
    intro m
    induction m with
    | zero =>
        intro θ _hθ
        simpa using hPone
    | succ m ih =>
        intro θ hθ
        rw [pow_succ]
        exact hPmul (θ ^ m) θ (ih θ hθ) hθ
  have hPα : P (φ₀ * φ₁) := hPmul φ₀ φ₁ hP₀' hP₁'
  have hPβ : P ((φ₀ * φ₁) ^ 6) := hPpow 6 (φ₀ * φ₁) hPα
  obtain ⟨c₀, hc₀H, hg₀, hg₀φ_eq⟩ := eq_ggConjAut_of_mem_ggAutomizer hφ₀A
  obtain ⟨g₀, rfl⟩ := hc₀H
  have hg₀φ : ggConjAut A hg₀ = φ₀ := hg₀φ_eq.symm
  obtain ⟨c₁, hc₁H, hg₁, hg₁φ_eq⟩ := eq_ggConjAut_of_mem_ggAutomizer hφ₁A
  obtain ⟨g₁, rfl⟩ := hc₁H
  have hg₁φ : ggConjAut A hg₁ = φ₁ := hg₁φ_eq.symm
  obtain ⟨e₀, he₀, hφ₀e₀⟩ := hφ₀.exists_inverted_ne_one (by norm_num : Nat.Prime 3)
  have he₀S : (γ e₀ : ModGL Tag.E6 GGFinModel.GGL) ∈ S :=
    negative_mem_full_connected_centralizer_of_actual_reflection_of_connected
      hn hK σ hσ Fr hFr ε hε hTB hnt hg₀ hg₀φ hφ₀ he₀ hφ₀e₀
  have he₀1 : (γ e₀ : ModGL Tag.E6 GGFinModel.GGL) ≠ 1 := by
    intro h
    exact he₀ (γ.injective (Subtype.ext (by simpa using h)))
  let R : ModGL Tag.E6 GGFinModel.GGL := recipeMatrixHom σ ε (ψ := ψ) (g₀ * g₁)
  have hg01 : MulAut.conj (g₀ * g₁) ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    rw [map_mul]
    exact Subgroup.mul_mem _ hg₀ hg₁
  have hgg_eq (g : L')
      (hg : MulAut.conj g ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
      ggConjAut A hg = A.normalizerMonoidHom ⟨MulAut.conj g, hg⟩ := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    rw [ggConjAut_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hgg01' : A.normalizerMonoidHom ⟨MulAut.conj (g₀ * g₁), hg01⟩ =
      A.normalizerMonoidHom ⟨MulAut.conj g₀, hg₀⟩ *
        A.normalizerMonoidHom ⟨MulAut.conj g₁, hg₁⟩ := by
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    exact map_mul MulAut.conj g₀ g₁
  have hgg01 : ggConjAut A hg01 = φ₀ * φ₁ := by
    calc
      ggConjAut A hg01 = A.normalizerMonoidHom ⟨MulAut.conj (g₀ * g₁), hg01⟩ :=
        hgg_eq (g₀ * g₁) hg01
      _ = A.normalizerMonoidHom ⟨MulAut.conj g₀, hg₀⟩ *
          A.normalizerMonoidHom ⟨MulAut.conj g₁, hg₁⟩ := hgg01'
      _ = ggConjAut A hg₀ * ggConjAut A hg₁ := by
        rw [← hgg_eq g₀ hg₀, ← hgg_eq g₁ hg₁]
      _ = φ₀ * φ₁ := by rw [hg₀φ, hg₁φ]
  have hconj (a : A) : R * (γ a : ModGL Tag.E6 GGFinModel.GGL) * R⁻¹ =
      (γ ((φ₀ * φ₁) a) : ModGL Tag.E6 GGFinModel.GGL) := by
    rw [← recipeActorModelEquiv_conj hn hK σ hσ Fr hFr ε hε
      hTB.1 hTB.2.1 hTB.2.2.1 hTB.2.2.2.2.1 hg01 a, hgg01]
  have hRG : R ∈ adjointGroup Tag.E6 GGFinModel.GGL :=
    ((TwistedDiag.mem_Rgrp _).mp
      (recipeMatrixHom_mem_Rgrp hn hK σ hσ Fr hFr ε (ψ := ψ) (g₀ * g₁))).1
  have hRE : R ∈ Subgroup.normalizer (E : Set (ModGL Tag.E6 GGFinModel.GGL)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨a, ha⟩ := γ.surjective ⟨x, hx⟩
      have hax : ((γ a : E) : ModGL Tag.E6 GGFinModel.GGL) = x := congrArg Subtype.val ha
      change R * x * R⁻¹ ∈ E
      rw [← hax]
      rw [hconj]
      exact (γ ((φ₀ * φ₁) a)).2
    · intro x hx
      let a : A := γ.symm ⟨x, hx⟩
      refine ⟨(γ ((φ₀ * φ₁).symm a) : ModGL Tag.E6 GGFinModel.GGL), (γ ((φ₀ * φ₁).symm a)).2, ?_⟩
      change R * (γ ((φ₀ * φ₁).symm a) : ModGL Tag.E6 GGFinModel.GGL) * R⁻¹ = x
      rw [hconj]
      change (γ ((φ₀ * φ₁) ((φ₀ * φ₁).symm a)) : ModGL Tag.E6 GGFinModel.GGL) = x
      rw [MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val (γ.apply_symm_apply ⟨x, hx⟩)
  have hcentral : ∀ t : ModGL Tag.E6 GGFinModel.GGL, t ∈ S → R ^ 6 * t * (R ^ 6)⁻¹ = t := by
    intro t ht
    exact TwE6E4bTorus.normalizer_pow_six_centralizes_connectedCentralizer
      (halg := CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (k := K))
      hEG hE hcardE hnt he₀1 he₀S hRG hRE ht
  have hRpow : ∀ (m : ℕ) (a : A),
      R ^ m * (γ a : ModGL Tag.E6 GGFinModel.GGL) * (R ^ m)⁻¹ =
        (γ (((φ₀ * φ₁) ^ m) a) : ModGL Tag.E6 GGFinModel.GGL) := by
    intro m
    induction m with
    | zero =>
        intro a
        simp
    | succ m ih =>
        intro a
        calc
          R ^ (m + 1) * (γ a : ModGL Tag.E6 GGFinModel.GGL) * (R ^ (m + 1))⁻¹ =
              R * (R ^ m * (γ a : ModGL Tag.E6 GGFinModel.GGL) * (R ^ m)⁻¹) * R⁻¹ := by
                rw [pow_succ']
                group
          _ = R * ((γ (((φ₀ * φ₁) ^ m) a) : ModGL Tag.E6 GGFinModel.GGL)) * R⁻¹ := by rw [ih a]
          _ = (γ ((φ₀ * φ₁) (((φ₀ * φ₁) ^ m) a)) : ModGL Tag.E6 GGFinModel.GGL) := hconj _
          _ = (γ (((φ₀ * φ₁) ^ (m + 1)) a) : ModGL Tag.E6 GGFinModel.GGL) := by
                rw [pow_succ', MulAut.mul_apply]
                rfl
  let β : MulAut A := (φ₀ * φ₁) ^ 6
  have hβU : ∀ u : A, (γ u : ModGL Tag.E6 GGFinModel.GGL) ∈ S → β u = u := by
    intro u hu
    apply γ.injective
    apply Subtype.ext
    have h6 := hRpow 6 u
    change R ^ 6 * (γ u : ModGL Tag.E6 GGFinModel.GGL) * (R ^ 6)⁻¹ =
      (γ (β u) : ModGL Tag.E6 GGFinModel.GGL) at h6
    exact h6.symm.trans (hcentral (γ u) hu)
  have hβ3 : β ^ 3 = 1 := by
    apply MulEquiv.ext
    intro a
    change β (β (β a)) = a
    let δ : A := β a * a⁻¹
    have hδS : (γ δ : ModGL Tag.E6 GGFinModel.GGL) ∈ S := hPβ a
    have hδ2S : (γ (δ ^ 2) : ModGL Tag.E6 GGFinModel.GGL) ∈ S := by
      have h := S.pow_mem hδS 2
      simpa only [map_pow, coe_pow] using h
    have hβa : β a = δ * a := by simp [δ]
    have hfixδ : β δ = δ := hβU δ hδS
    have hfixδ2 : β (δ ^ 2) = δ ^ 2 := hβU (δ ^ 2) hδ2S
    calc
      β (β (β a)) = β (β (δ * a)) := by rw [hβa]
      _ = β (β δ * β a) := by rw [map_mul]
      _ = β (δ * (δ * a)) := by rw [hfixδ, hβa]
      _ = β ((δ * δ) * a) := by rw [← mul_assoc]
      _ = β ((δ ^ 2) * a) := by rw [← pow_two]
      _ = β (δ ^ 2) * β a := by rw [map_mul]
      _ = (δ ^ 2) * (δ * a) := by rw [hfixδ2, hβa]
      _ = δ ^ 3 * a := by group
      _ = a := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one]
        rw [hA.2 (δ : MulAut L') δ.2, one_mul]
  have h18 : (φ₀ * φ₁) ^ 18 = 1 := by
    have h := hβ3
    change (((φ₀ * φ₁) ^ 6) ^ 3) = 1 at h
    rw [← pow_mul] at h
    exact h
  exact h18

theorem orderOf_reflectionProduct_ne_four_of_tableB
    {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    {A : Subgroup (MulAut L')} [Finite L']
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    (hnt : ¬ E6AdToral (rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A)))
    {φ₀ φ₁ : MulAut A}
    (hφ₀A : φ₀ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφ₁A : φ₁ ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A)
    (hφ₀ : GGIsReflection 3 φ₀) (hφ₁ : GGIsReflection 3 φ₁) :
    orderOf (φ₀ * φ₁) ≠ 4 := by
  intro h4
  have h18 := reflectionProduct_pow_eighteen_eq_one_of_tableB hn hK σ hσ Fr hFr ε hε
    hTB hnt hφ₀A hφ₁A hφ₀ hφ₁
  have hdvd : orderOf (φ₀ * φ₁) ∣ 18 := orderOf_dvd_of_pow_eq_one h18
  rw [h4] at hdvd
  norm_num at hdvd

end B2

end CFSG.StandardType.SCFourCover
