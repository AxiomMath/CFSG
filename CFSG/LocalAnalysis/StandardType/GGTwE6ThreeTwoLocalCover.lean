module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeTwoLocal
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRootGenFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
import CFSG.LocalAnalysis.StandardType.GGTwE6FieldDescent

public section

namespace CFSG.StandardType.TwE6ThreeRootGen

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.E6ThreeModel


theorem le_ker_of_isPGroup_two {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* ↥(twistedE6RootGroup K σ)} (hψ₀ : Function.Surjective ψ₀)
    (hker : ψ₀.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian 3 A)
    (hAH : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l, φ (ψ₀ l) = ψ₀ (a l))
    (h5 : 3 ^ 5 ≤ Nat.card A) (hsc : GGTorusSelfCent 3 A)
    {U : Subgroup L'} (hU2 : IsPGroup 2 U)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) : U ≤ ψ₀.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let Fr := iterateFrobenius (AlgebraicClosure K) 2 n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have h30 : (3 : AlgebraicClosure K) ≠ 0 :=
    three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := AlgebraicClosure K) h30
  obtain ⟨g, D, hL, hD, hgood⟩ := exists_lang_frame hn hK σ hσ h3 hFr hζ hζo
  obtain ⟨γ, ψ', ρ', -, hψ', hkerEq, hker', hρinj, hρ', hal, -⟩ :=
    align_data (K := K) (σ := σ) hψ₀ hker hperf hA hAH h5 D hD.H_eq hgood
  obtain ⟨κ, T, w, hΦ, -, hκrange, -⟩ :=
    model_data hn hK σ hσ h3 hψ' hkerEq hker' hperf D hgood hρ' hρinj hA hsc hal
  have hinner : ∀ x ∈ NoOffRest.hypE6, ∃ a : A, κ a = Multiplicative.ofAdd x := by
    intro x hx
    have hmem : Multiplicative.ofAdd x ∈ κ.range := hκrange.elim
      (fun hfull => by rw [hfull]; trivial) (fun hh => (hh x).2 hx)
    exact hmem
  have hnorm : ∀ x ∈ NoOffRest.hypE6, ∀ u ∈ U.map ψ', D.ad x u ∈ U.map ψ' := by
    intro x hx
    obtain ⟨a, ha⟩ := hinner x hx
    have hact : D.ad x = ρ' a := by
      rw [FrameData.ad, ← ha, hΦ]
    rintro _ ⟨u, hu, rfl⟩
    rw [hact, hρ']
    exact ⟨(a : MulAut L') u, hAU a a.2 u hu, rfl⟩
  have hbot : U.map ψ' = ⊥ := TwE6RootKill.eq_bot_of_isPGroup_two_of_tFrame
    hn hK σ hσ Fr hFr h3 hL hζ hζo hD hgood (hU2.map ψ') hnorm
  have hle : U ≤ ψ'.ker := by simpa only [Subgroup.map_eq_bot_iff] using hbot
  rwa [hkerEq] at hle

theorem le_ker_of_isPGroup_two_recipe {n : ℕ} (hn : 1 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ A)
    {U : Subgroup L'} (hU2 : IsPGroup 2 U) (hAU : ∀ a ∈ A, ∀ u ∈ U, a u ∈ U) :
    U ≤ ψ.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := TwE6FieldCore.charP_two_of_card_sq hK
  let σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨(iterateFrobenius K 2 n).injective,
      Finite.surjective_of_injective (iterateFrobenius K 2 n).injective⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  obtain ⟨hψ, hker, hperf, hA, hAH, h5, -, hsc⟩ := hTB
  let ψ' := ε.symm.toMonoidHom.comp ψ
  have hψ' : Function.Surjective ψ' := ε.symm.surjective.comp hψ
  have hkerEq : ψ'.ker = ψ.ker := by
    ext l
    change ε.symm (ψ l) = 1 ↔ ψ l = 1
    exact ⟨fun h => ε.symm.injective (by rw [h, map_one]), fun h => by rw [h, map_one]⟩
  have hAH' : ∀ a ∈ A, ∃ φ ∈ (RecipeExcLang.twConj K σ).range,
      ∀ l, φ (ψ' l) = ψ' (a l) := by
    intro a ha
    obtain ⟨φ, hφ, hφact⟩ := hAH a ha
    let φ' := (MulAut.congr ε).symm φ
    have hcongr : MulAut.congr ε φ' = φ := (MulAut.congr ε).apply_symm_apply φ
    refine ⟨φ', (hε φ').1 (by rw [hcongr]; exact hφ), ?_⟩
    intro l
    apply ε.injective
    change ε (φ' (ε.symm (ψ l))) = ε (ε.symm (ψ (a l)))
    rw [MulEquiv.apply_symm_apply]
    change (MulAut.congr ε φ') (ψ l) = ψ (a l)
    rw [hcongr, hφact]
  have hle := le_ker_of_isPGroup_two hn hK σ hσ h3 hψ'
    (hkerEq ▸ hker) hperf hA hAH' h5 hsc hU2 hAU
  rwa [hkerEq] at hle

end CFSG.StandardType.TwE6ThreeRootGen

end
