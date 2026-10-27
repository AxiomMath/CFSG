module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInternal
public import CFSG.LocalAnalysis.StandardType.GGTorusGenExcTwoCent
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggQ2CentExcTwoAux_at
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hperf : commutator L = ⊤)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup τ K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hinnI : TableBExc.RecipeID τ K ⊆ Set.range (MulAut.conj :
      TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)))
    (hlift : GGTorusLift 3 (τ.rank - 1) (TableBExc.RecipeGroup τ K))
    (hcp : GGCenterPrime 3 (TableBExc.RecipeGroup τ K))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID τ K,
      LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :
    actionThree (ggBeta L θ' hN).range := by
  classical
  have : Finite (TableBExc.RecipeGroup τ K) := TableBExc.finite_recipeGroup τ K
  have : Finite (MulAut (TableBExc.RecipeGroup τ K)) := MulEquiv.finite_left
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hAea : IsElemAbelian 3 (ggBeta L θ' hN).range := isElemAbelian_range_ggBeta θ' hBs hN
  have hinner : ∀ a ∈ (ggBeta L θ' hN).range, ∃ r, a = MulAut.conj r := by
    rintro a ⟨b, rfl⟩
    obtain ⟨r, hr⟩ := hinnI (ggBeta_mem L θ' hN hBs3 b)
    exact ⟨r, hr.symm⟩
  have hZ := ggQ2Cent_center_eq_bot hperf θ'
  have hinj : Function.Injective (MulAut.conj :
      TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)) :=
    fun a b hab => ggQ2Cent_eq_of_conj_eq hZ hab
  let E := (ggBeta L θ' hN).range.comap (MulAut.conj :
      TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K))
  have hEmap : E.map MulAut.conj = (ggBeta L θ' hN).range := by
    refine le_antisymm (Subgroup.map_comap_le _ _) ?_
    intro a ha
    obtain ⟨r, rfl⟩ := hinner a ha
    exact ⟨r, ha, rfl⟩
  have hEea : IsElemAbelian 3 E := hAea.comap hinj
  have hcard : 3 ^ (τ.rank - 1) ≤ Nat.card E := by
    have hEcard : Nat.card E = Nat.card (ggBeta L θ' hN).range := by
      rw [← hEmap, Subgroup.card_map_of_injective hinj]
    rw [hEcard]
    have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
    have hBBs : B ≤ Bs := hS.1.1.2.1.1
    have hBN : B ≤ Subgroup.normalizer (L : Set G) := hBBs.trans hN
    exact le_trans (pow_le_card_range_ggBeta Nat.prime_three hSS hperf θ' hBN hlift)
      (Subgroup.card_le_of_le (range_ggBeta_le θ' hBBs hBN hN))
  have hSC : ∀ g : TableBExc.RecipeGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ 3 = 1 → g ∈ E := by
    intro g hg hg3
    let ψ : L →* TableBExc.RecipeGroup τ K :=
      θ'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
    have hψker : ψ.ker = Subgroup.center L := by
      ext l
      rw [MonoidHom.mem_ker]
      change θ' (QuotientGroup.mk l) = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center L) :=
      hcp L ψ (θ'.surjective.comp (QuotientGroup.mk'_surjective _)) hψker.le hperf
    refine conj_mem_range_ggBeta_of_centerPrime hS θ' hN h3Z (fun a ha => ?_) hg3
    obtain ⟨r, rfl⟩ := hinner a ha
    have hrE : r ∈ E := ha
    rw [MulAut.conj_apply, ← hg r hrE, mul_inv_cancel_right]
  let e := TableBExc.recipeEquiv τ K
  let E₂ := E.map e.toMonoidHom
  have hE₂ : IsElemAbelian 3 E₂ := hEea.map _
  have hcard₂ : 3 ^ (τ.rank - 1) ≤ Nat.card E₂ := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact hcard
  have hmem₂ : ∀ y, y ∈ E₂ ↔ e.symm y ∈ E := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change e.symm (e z) ∈ E
      rw [MulEquiv.symm_apply_apply]
      exact hz
    · intro hy
      exact ⟨e.symm y, hy, e.apply_symm_apply y⟩
  have hcomm₂ : ∀ y : adjointGroup τ K, (∀ e₂ ∈ E₂, y * e₂ = e₂ * y) →
      ∀ e₁ ∈ E, e.symm y * e₁ = e₁ * e.symm y := by
    intro y hy e₁ he₁
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e e₁) ⟨e₁, he₁, rfl⟩
  have hSC₂ : ∀ y : adjointGroup τ K, (∀ e₂ ∈ E₂, y * e₂ = e₂ * y) → y ^ 3 = 1 → y ∈ E₂ := by
    intro y hy hy3
    rw [hmem₂]
    refine hSC _ (hcomm₂ y hy) ?_
    rw [← map_pow, hy3, map_one]
  have hF := Irred937.exists_langFrame_of_sc hτ (p := 3) (Or.inl rfl) K (by rw [hK]) E₂ hE₂
    hcard₂ (fun y hy hy3 => hSC₂ y (fun e₂ he₂ =>
      (Subgroup.mem_centralizer_iff.mp hy e₂ he₂).symm) hy3)
  intro r hfix _
  have hrcomm : ∀ e₁ ∈ E, r * e₁ = e₁ * r := by
    intro e₁ he₁
    have h1 : MulAut.conj e₁ r = r := hfix _ he₁
    rw [MulAut.conj_apply] at h1
    calc r * e₁ = e₁ * r * e₁⁻¹ * e₁ := by rw [h1]
      _ = e₁ * r := by group
  have he₂ : e r ∈ E₂ := by
    refine ExcTwoGen.mem_of_commute_of_langFrame_two hτ hK hSC₂ hF ?_
    intro e₂ he₂
    have h1 := hrcomm _ ((hmem₂ e₂).mp he₂)
    have h2 := congrArg e h1
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have hrE : r ∈ E := by
    have h1 := (hmem₂ (e r)).mp he₂
    rwa [MulEquiv.symm_apply_apply] at h1
  exact hrE

private theorem ggQ2CentExcTwoAux_dataE7 {G : Type} [Group G] {Bs L : Subgroup G}
    (hon : labelOn (fun lab => lab.tag = .E7) 3 Bs L) :
    commutator L = ⊤ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E7 K,
        ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID .E7 K,
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, htag⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  refine ⟨hperf, ?_⟩
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hn htag
  subst hn htag
  obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
  exact ⟨K, i1, i2, by rw [hK]; norm_num, θ', hBs3⟩

private theorem ggQ2CentExcTwoAux_dataE8 {G : Type} [Group G] {Bs L : Subgroup G}
    (hon : labelOn (fun lab => lab.tag = .E8) 3 Bs L) :
    commutator L = ⊤ ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ∧
      ∃ θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E8 K,
        ∀ b ∈ Bs, ∃ φ ∈ TableBExc.RecipeID .E8 K,
          LargeEvenInduces θ' (fun l l' => (l' : G) = b⁻¹ * l * b) φ := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hon
  obtain ⟨-, -, -, -, -, -, -, ⟨hq2, htag⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hn : lab.n = 1 := by
    have h1 : 1 ≤ lab.n := hlab.1
    have h2 : lab.n < 2 := hq2
    omega
  refine ⟨hperf, ?_⟩
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hn htag
  subst hn htag
  obtain ⟨K, i1, i2, hK, -, -, θ', -, -, hBs3⟩ := hraw
  exact ⟨K, i1, i2, by rw [hK]; norm_num, θ', hBs3⟩

theorem eSevenTwoInput_holds :
    eSevenTwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, K, _, _, hK, θ', hBs3⟩ := ggQ2CentExcTwoAux_dataE7 hon
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  exact actionThree_ggBeta_congr θ θ' hN
    (ggQ2CentExcTwoAux_at (Or.inl rfl) hS hperf hK θ' hN (TableBExc.idImage_subset_inn_E7 K)
      TableBExcTwo.ggTorusLift_E7Two
      (ExcSplitL.ggCenterPrime_recipe_E7 (f := 1) le_rfl (by rw [hK]; norm_num)
        Nat.prime_three (by norm_num))
      hBs3)

theorem eEightTwoInput_holds :
    eEightTwoInput := by
  intro G _ _ p B Bs x L D J hS hon R _ θ hN
  have hp3 : p = 3 := ggQ2_pThree hS
  subst hp3
  obtain ⟨hperf, K, _, _, hK, θ', hBs3⟩ := ggQ2CentExcTwoAux_dataE8 hon
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  exact actionThree_ggBeta_congr θ θ' hN
    (ggQ2CentExcTwoAux_at (Or.inr rfl) hS hperf hK θ' hN (TableBExc.idImage_subset_inn_E8 K)
      TableBExcTwo.ggTorusLift_E8Two
      (ExcSplitL.ggCenterPrime_recipe_E8 Nat.prime_three (by norm_num))
      hBs3)

end CFSG.StandardType.GGQ2CentPort

end
