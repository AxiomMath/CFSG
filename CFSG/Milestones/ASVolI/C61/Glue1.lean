module

public import CFSG.Milestones.ASVolI.C61.CS
public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.Milestones.ASVolI.C6

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC

theorem burnsideC56_glue_conj_one {G : Type} [Group G] (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

theorem burnsideC56_glue_conjJoin {G : Type} [Group G] (S K : Subgroup G) :
    conjJoin S K = ⨆ t ∈ S, conjByElt t K := by
  unfold conjJoin conjByElt
  rw [iSup_subtype']

theorem burnsideC56_glue_blocks {G : Type} [Group G] [Finite G] {H TH R K₁ : Subgroup G}
    (hcfg : BlockConfig H TH R K₁) :
    conjJoin TH K₁ = K₁ ∨
      ∃ t ∈ TH, K₁.map (MulAut.conj t).toMonoidHom ≠ K₁ ∧
        conjJoin TH K₁ = K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ∧
        ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ = ⊥ := by
  have h1 := burnsideC56_glue_conj_one K₁
  by_cases hs : ∀ t ∈ TH, conjByElt t K₁ = K₁
  · left
    rw [burnsideC56_glue_conjJoin]
    apply le_antisymm
    · exact iSup₂_le fun s hs' => (hs s hs').le
    · exact le_iSup₂_of_le (1 : G) (one_mem TH) h1.ge
  · right
    push Not at hs
    obtain ⟨t, ht, hne⟩ := hs
    refine ⟨t, ht, hne, ?_, ?_⟩
    · rw [burnsideC56_glue_conjJoin]
      apply le_antisymm
      · refine iSup₂_le fun s hs' => ?_
        rcases hcfg.card_le 1 (one_mem TH) t ht s hs' with h | h | h
        · exact absurd (h1 ▸ h).symm hne
        · rw [← h, h1]; exact le_sup_left
        · rw [← h]; exact le_sup_right
      · exact sup_le (le_iSup₂_of_le (1 : G) (one_mem TH) h1.ge) (le_iSup₂_of_le t ht le_rfl)
    · have := hcfg.commute 1 (one_mem TH) t ht (by rw [h1]; exact fun h => hne h.symm)
      rw [h1] at this
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr this

section


theorem burnsideC56_glue_setup
    (hS1 : ∀ {G : Type} [Group G] [Finite G] {H : Subgroup G}, CharTwo H →
      ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) → IsSQTKIn H)
    (hS2 : ∀ {G : Type} [Group G] [Finite G] {H T : Subgroup G}, CharTwo H →
      ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) →
      IsSylowTwoOf T H → IsMinimalParabolic T H)
    (hS3 : ∀ {G : Type} [Group G] [Finite G] {H T : Subgroup G}, CharTwo H →
      ((∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
        QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2))) →
      IsSylowTwoOf T H → ∃ N : Subgroup G, CFSG.Quasithin.IsUniqueMaxOver H T N)
    {G : Type} [Group G] [Finite G] {H Λ : Subgroup G} (hc : CharTwo H)
    (hi : (∃ n : ℕ, 1 ≤ n ∧ QuotHas (oTwoUpper H) (pCoreOf 2 H) (fun Y _ => IsPSL 2 2 n Y)) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* Equiv.Perm (Fin 3))) ∨
      QuotHas H (pCoreOf 2 H) (fun Y _ => Nonempty (Y ≃* S3wrZ2)))
    (hΛ2 : IsPGroup 2 Λ) (hsyl : IsSylowTwoOf (Λ ⊓ H) H) (hlt : Λ ⊓ H < Λ)
    (hiv : ∀ T₀ : Subgroup G, T₀ ≠ ⊥ → T₀ ≤ Λ ⊓ H → H ≤ Subgroup.normalizer (T₀ : Set G) →
      Λ ⊓ Subgroup.normalizer (T₀ : Set G) = Λ ⊓ H) :
    ∃ (M₀ K₁ : Subgroup G), Λ ⊓ H ≤ M₀ ∧ M₀ ≤ Λ ∧ (Λ ⊓ H).relIndex M₀ = 2 ∧
      SetC53 H M₀ (Λ ⊓ H) (Λ ⊓ H) K₁ ∧ burnsideC56_CS G Λ ⊤ H (Λ ⊓ H) K₁ ∧
      conjJoin (Λ ⊓ H) K₁ = oTwoUpper H := by
  obtain ⟨M₀, hTM, hMΛ, h2⟩ :=
    CFSG.QuasithinUnique.exists_relIndex_two hΛ2 (inf_le_left : Λ ⊓ H ≤ Λ) (ne_of_lt hlt)
  have hMN : M₀ ≤ Subgroup.normalizer ((Λ ⊓ H : Subgroup G) : Set G) :=
    CFSG.QuasithinUnique.normalizer_of_relIndex_two hTM h2
  have hHeq : H = oTwoUpper H ⊔ (Λ ⊓ H) := CFSG.Quasithin.eq_oTwoUpper_sup_of_isSylowTwoOf hsyl
  have hyp1 : HypC_5_1 H M₀ (Λ ⊓ H) (Λ ⊓ H) :=
    { sqtk := hS1 hc hi
      charTwo := hc
      sylow := hsyl
      unique_max := hS3 hc hi hsyl
      R_le := le_rfl
      TH_le := hTM
      sylow_R := by rw [sup_comm, ← hHeq]; exact hsyl
      R_norm := hMN }
  have hyp2 : HypC_5_2 M₀ H (Λ ⊓ H) := by
    intro R₀ hR₀ hne hN
    have h1 := hiv R₀ hne hR₀ (le_sup_right.trans hN)
    have h3 : M₀ ≤ Λ ⊓ Subgroup.normalizer (R₀ : Set G) := le_inf hMΛ (le_sup_left.trans hN)
    rw [h1] at h3
    have : M₀ = Λ ⊓ H := le_antisymm h3 hTM
    rw [this, Subgroup.relIndex_self] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨K₁, hcfg⟩ := as_C_5_3 G H M₀ (Λ ⊓ H) (Λ ⊓ H) hyp1 hyp2
  have hjoin : conjJoin (Λ ⊓ H) K₁ = oTwoUpper H := by
    rw [hcfg.prod, burnsideC56_glue_conjJoin]
  refine ⟨M₀, K₁, hTM, hMΛ, h2, ⟨hyp1, hyp2, hcfg⟩, ?_, hjoin⟩
  exact
    { T_two := hΛ2
      l244 := hiv
      charTwo := hc
      sylow := hsyl
      le_T := inf_le_left
      ne_T := ne_of_lt hlt
      block := hcfg.chi0
      thompson := hcfg.comm_J
      eq_join := by rw [hjoin]; exact hHeq
      blocks := burnsideC56_glue_blocks hcfg
      minParabolic := hS2 hc hi hsyl }

end

end CFSG.ASVolI
