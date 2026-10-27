module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3315R

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique

@[expose] def Step3_3_12RB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D Y : Subgroup G), Hyp331 G T M L D →
    Y ∈ lFamilyOf L T → pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ → L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) →
    ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧
      (D ≤ Subgroup.normalizer (Y : Set G) ∨
        (IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          InducesInnerOn T Y ∧ A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) K)))

theorem step3_3_12RB_of
    (h14 : Stmt3_3_14) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h312 : A312ForSQTK) (h36 : Vol2Native.A36ForSQTKCat) (h128 : Lemma128One)
    (hF : L3312.Facts3312) : Step3_3_12RB := by
  intro G _ _ T M L D Y h hY hO htype
  have H : L3312.Hyp3312 G T M L D Y := ⟨h, hY, hO⟩
  have : IsSimpleGroup G := h.simple
  set X := Y ⊔ T ⊔ D with hX
  obtain ⟨K, hK, hYK⟩ := H.exists_cComp h37 h39
  have hHK := H.sup_le_normalizer_K h14 h37 h38 h128 hK hYK
  refine ⟨K, hK, hYK, hHK, ?_⟩
  have hKX : K ≤ X := le_of_mem_cComp hK
  have hlist := lemma_1_2_4_list h.qtke h.simple h.nonabelian h312 hO H.isSylowTwoOf_H
    (le_sup_left.trans le_sup_left) (mem_lFamily_of_isLocal H.isLocal) hK hYK
  have hKc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have h36K := Vol2Native.lemma_1_2_1_four_strong hKc h36 hO hK
  obtain ⟨e⟩ := L3312.Hyp3312.modO2_equiv (T := T) (D := D) (Y := Y)
  have htype' : L3312.Type3312R (ModO2 (modO2Image X Y)) := L3312.Type3312R.of_equiv e htype
  have hYK' : modO2Image X Y ≤ modO2Image X K := Subgroup.map_mono fun y hy => hYK hy
  rcases L3312.oddNorm_or_j1 hF hYK' htype' h36K hlist with hc | hON
  · obtain ⟨h1, h2, h3⟩ := H.j1_case h14 h37 h128 hF.j1 hK hYK hHK hc htype
    exact Or.inr ⟨h1, h2, h3, hc⟩
  · exact Or.inl (H.le_normalizer_D_of_oddNorm h14 h37 h128 hKX hYK hHK hON)

@[expose] def Step3_3_15RB : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D Y₁ Y₂ : Subgroup G), Hyp331 G T M L D →
    Y₁ ∈ lFamilyOf L T → Y₂ ∈ lFamilyOf L T → L ⊔ T = Y₁ ⊔ Y₂ ⊔ T →
    pCoreOf 2 (Y₁ ⊔ T ⊔ D) ≠ ⊥ → pCoreOf 2 (Y₂ ⊔ T ⊔ D) ≠ ⊥ →
    L3312.Type3312R (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁) → L3312.Type3312R (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂) →
    ∃ Y : Subgroup G, (Y = Y₁ ∨ Y = Y₂) ∧ ¬ D ≤ Subgroup.normalizer (Y : Set G) ∧
      IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ InducesInnerOn T Y ∧
      ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
        Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧
        A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) K)

theorem step3_3_15RB_of (h6 : Stmt3_3_6) (h14 : Stmt3_3_14) (h12 : Step3_3_12RB) :
    Step3_3_15RB := by
  intro G _ _ T M L D Y₁ Y₂ h hY₁ hY₂ hLT hO₁ hO₂ ht₁ ht₂
  have hnot : ¬ (D ≤ Subgroup.normalizer (Y₁ : Set G) ∧ D ≤ Subgroup.normalizer (Y₂ : Set G)) := by
    rintro ⟨hD₁, hD₂⟩
    obtain ⟨hML, -⟩ := h14 G T M L D h
    have hne : L ⊔ T ≠ ⊥ := fun hb => h.toSetup331.T_ne_bot (le_bot_iff.mp (hb ▸ le_sup_right))
    have hb := (h6 G T M L D h).2.1.2 (L ⊔ T) hne (by rw [hML]) (by rw [hML]; exact
      Subgroup.le_normalizer)
    apply hb
    rw [hLT]
    exact fun d hd => L3312.mem_normalizer_sup' (L3312.mem_normalizer_sup' (hD₁ hd) (hD₂ hd))
      (h.DN hd)
  have key : ∀ Y : Subgroup G, Y ∈ lFamilyOf L T → pCoreOf 2 (Y ⊔ T ⊔ D) ≠ ⊥ →
      L3312.Type3312R (↥Y ⧸ CFSG.pCore 2 ↥Y) → ¬ D ≤ Subgroup.normalizer (Y : Set G) →
      IsPSL 2 2 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧ InducesInnerOn T Y ∧
        ∃ K ∈ cComp (Y ⊔ T ⊔ D), Y ≤ K ∧ IsSporadic .J1 (↥K ⧸ CFSG.pCore 2 ↥K) ∧
          Y ⊔ T ⊔ D ≤ Subgroup.normalizer (K : Set G) ∧
          A312C15 (modO2Image (Y ⊔ T ⊔ D) Y) (modO2Image (Y ⊔ T ⊔ D) K) := by
    intro Y hY hO ht hDY
    obtain ⟨K, hK, hYK, hHK, hc⟩ := h12 G T M L D Y h hY hO ht
    rcases hc with hc | ⟨h1, h2, h3, h4⟩
    · exact absurd hc hDY
    · exact ⟨h1, h3, K, hK, hYK, h2, hHK, h4⟩
  by_cases hD₁ : D ≤ Subgroup.normalizer (Y₁ : Set G)
  · have hD₂ : ¬ D ≤ Subgroup.normalizer (Y₂ : Set G) := fun hD₂ => hnot ⟨hD₁, hD₂⟩
    exact ⟨Y₂, Or.inr rfl, hD₂, key Y₂ hY₂ hO₂ ht₂ hD₂⟩
  · exact ⟨Y₁, Or.inl rfl, hD₁, key Y₁ hY₁ hO₁ ht₁ hD₁⟩

end CFSG.Quasithin.H13
