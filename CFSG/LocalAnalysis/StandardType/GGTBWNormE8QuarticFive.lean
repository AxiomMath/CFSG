module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE8FiveAutFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SF5UY6Max

public noncomputable section

namespace CFSG.StandardType.E8WNorm

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType.TableBExc CFSG.LocalAnalysis.GLTheoremA.S265.SF5U


theorem five_pow_four_le_card_of_selfCent {K : Type} [Field K] [Finite K]
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1)
    (E : Subgroup (adjointGroup .E8 K)) (hE : IsElemAbelian 5 E)
    (h3 : 5 ^ 3 ≤ Nat.card E)
    (hsc : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ 5 = 1 → g ∈ E) :
    5 ^ 4 ≤ Nat.card E := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite (ModGL Tag.E8 K) := finite_modGL
  by_cases h4 : 5 ^ 4 ≤ Nat.card E
  · exact h4
  obtain ⟨k, hk⟩ := (TableB.isPGroup_of_isElemAbelian hE).exists_card_eq
  have hk3 : k = 3 := by
    have hlow : 3 ≤ k := (Nat.pow_le_pow_iff_right (by decide : 1 < 5)).mp (hk ▸ h3)
    have hupp : k < 4 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 5)).mp
      (hk ▸ lt_of_not_ge h4)
    omega
  have hE3 : Nat.card E = 5 ^ 3 := by rw [hk, hk3]
  obtain ⟨F, hEF, hF, hFcard⟩ := e8FiveMaxRank_holds K h5 E hE hE3
  have hFE : F ≤ E := by
    intro g hg
    exact hsc g (fun e he => TableB.IsElemAbelian.comm hF hg (hEF he)) (hF.2 g hg)
  rw [le_antisymm hEF hFE, hFcard]


theorem ggTorusWNormSC_recipe_E8_quartic_five {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1) :
    GGTorusWNormSC 5 (RecipeGroup .E8 K) (RecipeID .E8 K) := by
  classical
  letI : Algebra (ZMod 2) K := ZMod.algebra _ _
  intro L _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have hIp : GGOutdiagPrime 5 (RecipeGroup .E8 K) (RecipeID .E8 K) := by
    intro φ hφ _
    obtain ⟨x, rfl⟩ := idImage_subset_inn_E8 K hφ
    exact ⟨x, rfl⟩
  obtain ⟨Λ₀, hΛeq, -, -, hAΛ, hE, hEc, hEsc⟩ :=
    TwE6TB.exists_innerModel Nat.prime_five (center_recipeGroup_eq_bot .E8 K) hIp
      (ExcSplitL.ggCenterPrime_recipe_E8 Nat.prime_five (by decide))
      ψ hψ hker hperf hA hAI hsc
  let ε := recipeEquiv .E8 K
  let E := (A.comap Λ₀).map ε.toMonoidHom
  have hEg : IsElemAbelian 5 E := TableB.isElemAbelian_map hE _
  have hEcard : Nat.card E = Nat.card A :=
    (Subgroup.card_map_of_injective ε.injective).trans hEc
  have hEgs : ∀ g, (∀ e ∈ E, g * e = e * g) → g ^ 5 = 1 → g ∈ E := by
    intro g hg hgp
    have hg' : ε.symm g ∈ A.comap Λ₀ := by
      apply hEsc
      · intro e he
        apply ε.injective
        rw [map_mul, map_mul, ε.apply_symm_apply]
        exact hg (ε e) (Subgroup.mem_map_of_mem _ he)
      · rw [← map_pow, hgp, map_one]
    exact ⟨ε.symm g, hg', ε.apply_symm_apply g⟩
  have h4 := five_pow_four_le_card_of_selfCent h5 E hEg (hEcard ▸ h3) hEgs
  let ψ₁ : L →* adjointGroup .E8 K := ε.toMonoidHom.comp ψ
  have hψ₁ : Function.Surjective ψ₁ := ε.surjective.comp hψ
  have hker₁ : ψ₁.ker ≤ Subgroup.center L := by
    intro l hl
    apply hker
    rw [MonoidHom.mem_ker] at hl ⊢
    have h1 : ε (ψ l) = 1 := hl
    rwa [ε.map_eq_one_iff] at h1
  let Λ₁ : adjointGroup .E8 K →* MulAut L := Λ₀.comp ε.symm.toMonoidHom
  have hΛ₁ψ : ∀ l, Λ₁ (ψ₁ l) = MulAut.conj l := by
    intro l
    change Λ₀ (ε.symm (ε (ψ l))) = MulAut.conj l
    rw [ε.symm_apply_apply]
    exact hΛeq rfl
  have hEA : E.map Λ₁ = A := by
    change ((A.comap Λ₀).map ε.toMonoidHom).map (Λ₀.comp ε.symm.toMonoidHom) = A
    rw [Subgroup.map_map]
    have hcomp : (Λ₀.comp ε.symm.toMonoidHom).comp ε.toMonoidHom = Λ₀ := by
      refine MonoidHom.ext fun x => ?_
      change Λ₀ (ε.symm (ε x)) = Λ₀ x
      rw [ε.symm_apply_apply]
    rw [hcomp]
    exact Subgroup.map_comap_eq_self (fun a ha => hAΛ a ha)
  have hAut : ∀ β : MulAut (adjointGroup .E8 K), ∃ r, ∀ e ∈ E, β e = r * e * r⁻¹ :=
    fun β => NoOffE8Five.exists_conj_eq_on_E8_five hn hK h5 hEg h4 β
  intro _ Γ _ _ M C V _ _ ι φ h α _ _ _ _ hgen s hs
  exact ggWNormConcl_of_centralCover_innerAction ψ₁ hψ₁ hker₁ center_adjointGroup_eq_bot
    Λ₁ hΛ₁ψ E A hEA hAut ι φ h α hgen hs

theorem largeEvenLabelAll_wnorm_E8_quartic_five {lab : LargeEvenLabel}
    (htag : lab.tag = .E8) (h5 : 5 ∣ (2 ^ lab.n) ^ 2 + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC 5 R I := by
  obtain ⟨t, r, f⟩ := lab
  dsimp only at htag h5 ⊢
  subst htag
  have hf : 1 ≤ f := by
    by_contra hf
    have hf0 : f = 0 := by omega
    norm_num [hf0] at h5
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, i1, i2, hK, hQK⟩ := hQ
  letI : CharP K 2 := charP_two_of_card hK
  refine ⟨K, i1, i2, hK, hQK, ?_⟩
  exact ggTorusWNormSC_recipe_E8_quartic_five hf hK (by rw [hK]; simpa [pow_two] using h5)

end CFSG.StandardType.E8WNorm
