module

public import CFSG.LocalAnalysis.StandardType.GGTBTorTwE6ThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistCover
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem ggTwE6Three_tbGroup_twisted {n : ℕ} (hn : 2 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K n} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ₀ A) :
    ∃ (σ : K ≃+* K) (_ : ∀ c, σ c = c ^ 2 ^ n) (ψ : L' →* ↥(twistedE6RootGroup K σ)),
      ψ.ker = ψ₀.ker ∧ GGTorusTBGroup 3 5 ↥(twistedE6RootGroup K σ)
        ((RecipeExcLang.twConj K σ).range : Set (MulAut ↥(twistedE6RootGroup K σ))) L' ψ A := by
  obtain ⟨hψ0, hker0, hperf0, hAe, hAI, h5, h3A, hsc⟩ := hTB
  obtain ⟨σ, hσ, ε, hε⟩ := TwE6Transport.exists_recipeConj (K := K) (n := n) (by omega) hK
  let ψ : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ₀
  have hk : ψ.ker = ψ₀.ker :=
    MonoidHom.ker_comp_of_injective ψ₀ ε.symm.toMonoidHom ε.symm.injective
  refine ⟨σ, hσ, ψ, hk, ε.symm.surjective.comp hψ0, hk ▸ hker0, hperf0, hAe, ?_, h5, h3A, hsc⟩
  intro a ha
  obtain ⟨φ, hφI, hφ⟩ := hAI a ha
  obtain ⟨w, hw⟩ := (hε φ).2 hφI
  refine ⟨RecipeExcLang.twConj K σ w, ⟨w, rfl⟩, fun l => ?_⟩
  have h1 := hφ l
  rw [← hw, TwE6Transport.recipeConj_apply] at h1
  change RecipeExcLang.twConj K σ w (ε.symm (ψ₀ l)) = ε.symm (ψ₀ (a l))
  rw [← h1, MulEquiv.symm_apply_apply]

theorem ggTwE6Three_ker_pow_three {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ 2 ^ n + 1) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) {L' : Type} [Group L'] [Finite L']
    {ψ₀ : L' →* TwE6Delta.RecipeR K n} {A : Subgroup (MulAut L')}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) L' ψ₀ A) :
    ∀ z ∈ ψ₀.ker, z ^ 3 = 1 := by
  have hn3 : 3 ≤ n := by
    by_contra h
    have hn2 : n = 2 := by omega
    rw [hn2] at h3
    norm_num at h3
  have hdvd : Nat.card ψ₀.ker ∣ 3 :=
    TwE6Delta.card_ker_dvd_three_q8 hn3 hK hTB.1 hTB.2.1 hTB.2.2.1
  intro z hz
  exact orderOf_dvd_iff_pow_eq_one.1 ((Subgroup.orderOf_dvd_natCard ψ₀.ker hz).trans hdvd)

theorem ggTwE6Three_hKer
    {G : Type} [Group G] [Finite G] {Bs X : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) {n : ℕ} (hn : 2 ≤ n) (h3 : 3 ∣ 2 ^ n + 1)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
    {ψ₀ : ↥X →* TwE6Delta.RecipeR K n}
    (hTB : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K n) (TwE6Delta.RecipeI K n) ↥X ψ₀
      (ggGamma X hN).range) :
    ∀ g : ↥(X ⊓ Subgroup.normalizer (Bs : Set G)), ggTDρA hN g = 1 → ggTDρB X Bs g = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n)
    (by rw [Fintype.card_eq_nat_card, hK, ← pow_mul, mul_comm])
  obtain ⟨σ, hσ, ψ, hk, hTB'⟩ := ggTwE6Three_tbGroup_twisted hn hK hTB
  have hodd : Odd (Nat.card ψ₀.ker) := by
    rw [← hk]
    exact TBE6IndTwist.odd_card_ker_of_two_le hn hK σ hσ ψ hTB'.1 hTB'.2.1 hTB'.2.2.1
  obtain ⟨w, hw⟩ := TwE6ThreeLang.torData_recipe_odd (by omega) hK h3 hTB hodd
  intro g hg
  exact ggTD_ker hN hw (by norm_num) hBs g hg

end CFSG.StandardType

end
