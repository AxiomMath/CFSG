module

public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6EndNodeThreeTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEnd
import CFSG.LocalAnalysis.StandardType.GGTwE6DeltaThreeEndLift
import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public section

namespace CFSG.StandardType.TwE6EndNode3

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.TwE6D3

section Big


theorem endNode_of_big (hCore : TwE6RootAs.TwE6CorootCore) {n : ℕ} (hn : 1 ≤ n) {K : Type}
    [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1) {L' : Type}
    [Group L'] [Finite L'] (ψ : L' →* TwE6Delta.RecipeR K n) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hA : IsElemAbelian 3 A) (hInd : ∀ a ∈ A, Induces ψ a) (h5 : 3 ^ 5 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) ∧
      ∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hinj : Function.Injective (iterateFrobenius K 2 n) := (iterateFrobenius K 2 n).injective
  set σ : K ≃+* K := RingEquiv.ofBijective (iterateFrobenius K 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩ with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hK σ hσ
  set ψ' : L' →* ↥(twistedE6RootGroup K σ) := ε.symm.toMonoidHom.comp ψ with hψ'def
  have hψ'ψ : ∀ l, ψ' l = ε.symm (ψ l) := fun l => rfl
  have hψ' : Function.Surjective ψ' := ε.symm.surjective.comp hψ
  have hZ' : Subgroup.center ↥(twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hker' : ψ'.ker ≤ Subgroup.center L' := fun x hx => hker (by
    have h : ε.symm (ψ x) = 1 := hx
    exact (map_eq_one_iff _ ε.symm.injective).1 h)
  have hρinj : Function.Injective (ggIE_indAutHom hψ' hZ' hker') :=
    ggIE_indAutHom_injective hψ' hZ' hker' hperf
  have hiff := rho_mem_range_twConj_iff hε hψ'ψ hψ' hZ' hker'
  have hACel : IsElemAbelian 3 (A.map (ggIE_indAutHom hψ' hZ' hker')) :=
    ggIE_isElemAbelian_map _ hA
  have hACc : 3 ^ 5 ≤ Nat.card (A.map (ggIE_indAutHom hψ' hZ' hker')) := by
    rw [Subgroup.card_map_of_injective hρinj]
    exact h5
  have hACI : A.map (ggIE_indAutHom hψ' hZ' hker') ≤ (RecipeExcLang.twConj K σ).range := by
    rintro _ ⟨y, hy, rfl⟩
    exact (hiff y).1 (hInd y hy)
  set Fr : AlgebraicClosure K →+* AlgebraicClosure K := iterateFrobenius (AlgebraicClosure K) 2 n
    with hFrdef
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hg, hgn, hle⟩ := TwE6DD2.exists_cubeTorus_lang hn hK σ hσ h3 Fr hFr hACel hACI hACc
  obtain ⟨γ, ζ, hγ, hζ, hζ1, hd, hτ⟩ := exists_coroot_mem_of_le hn hK σ hσ Fr hFr h3 hg hgn hle hACc
  obtain ⟨τ, hτA, hτ1, X, D, hfix, hXc, hXD, hDq, h7, -, hcent⟩ :=
    exists_coroot_data_of_mem hCore hn hK σ hσ h3 hFr hg hgn hACel hle hγ hζ hζ1 hd hτ
  obtain ⟨t, htA, rfl⟩ := hτA
  have ht1 : t ≠ 1 := fun h => hτ1 (by rw [h, map_one])
  have hcent' : ∀ y ∈ A, (∀ x ∈ D, ggIE_indAutHom hψ' hZ' hker' y x = x) →
      ∃ x ∈ X, ggIE_indAutHom hψ' hZ' hker' y = MulAut.conj x := fun y hy hyD =>
    hcent _ ⟨y, hy, rfl⟩ hyD
  obtain ⟨hend, -⟩ := endNode_of_data hψ' hZ' hker' hperf hA htA ht1 hfix hXc hXD hDq h7 hcent'
  exact ⟨t, hend.1, hend.2.1, hend.2.2.1, hend.2.2.2⟩

end Big

end CFSG.StandardType.TwE6EndNode3

end
