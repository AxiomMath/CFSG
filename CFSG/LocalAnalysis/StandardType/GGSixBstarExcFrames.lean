module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank ExcFrames

@[expose] def GGExcF4HalfLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .F4 ∧ p ∣ 2 ^ f + 1

@[expose] def GGExcF4RestLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .F4 ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1

@[expose] def GGExcE7HalfLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E7 ∧ p ∣ 2 ^ f + 1

@[expose] def GGExcE7RestLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E7 ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1

@[expose] def GGExcE8HalfLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ p ∣ 2 ^ f + 1

@[expose] def GGExcE8RestLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ ¬ p ∣ 2 ^ f - 1 ∧ ¬ p ∣ 2 ^ f + 1 ∧ p ≠ 5

section Cover

theorem GGSixBstarExcFrameOn.of_or {τ : Tag} {P Q R : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hQ : GGSixBstarExcFrameOn τ Q) (hR : GGSixBstarExcFrameOn τ R)
    (h : ∀ t n f p, P t n f p → Q t n f p ∨ R t n f p) : GGSixBstarExcFrameOn τ P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  rcases h t n f p hP with h' | h'
  · exact hQ G p B Bs x L D J t n f ψ h' hctx hC
  · exact hR G p B Bs x L D J t n f ψ h' hctx hC

end Cover

theorem false_of_card_lt {τ : Tag}
    {K : Type} [Field K] {p : ℕ} {G : Type} [Group G] (χ : adjointGroup τ K →* G)
    (hχ : Function.Injective χ) {Bs : Subgroup G} (hBsR : Bs ≤ χ.range)
    (hBs : IsElemAbelian p Bs) (h4 : p ^ 4 ≤ Nat.card Bs)
    (h : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → Nat.card E < p ^ 4) : False := by
  have hlt := h (Bs.comap χ) (isElemAbelian_comap_frame χ hχ hBs)
  rw [card_comap_of_le_range χ hχ hBsR] at hlt
  omega

section Frames


@[expose] def GGExcNonsplitRankInput (τ : Tag) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (p : ℕ), p.Prime → p ≠ 2 →
    ¬ p ∣ Nat.card K - 1 → ¬ p ∣ Nat.card K + 1 →
    ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → Nat.card E < p ^ 4

theorem ggSixBstarExcFrameOn_F4Rest_of_rank (h : GGExcNonsplitRankInput .F4) :
    GGSixBstarExcFrameOn .F4 GGExcF4RestLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hq1, hq2⟩ := hP
  exfalso
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  exact false_of_card_lt ψ hinj hBsR hBs h4
    (h (GaloisField 2 f) p hp hp2 (by rwa [hK]) (by rwa [hK]))

theorem ggSixBstarExcFrameOn_E7Rest_of_rank
    (h : GGExcNonsplitRankInput .E7) : GGSixBstarExcFrameOn .E7 GGExcE7RestLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hq1, hq2⟩ := hP
  exfalso
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hCψ, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  set e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  set χ : adjointGroup .E7 (GaloisField 2 f) →* G := ψ.comp e.symm.toMonoidHom with hχ
  have hχinj : Function.Injective χ := hinj.comp e.symm.injective
  have hBsR' : Bs ≤ χ.range := fun b hb => by
    obtain ⟨u, hu⟩ := hBsR hb
    refine ⟨e u, ?_⟩
    have h1 : e.symm (e u) = u := e.symm_apply_apply u
    show ψ (e.symm (e u)) = b
    rw [h1]
    exact hu
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  exact false_of_card_lt χ hχinj hBsR' hBs h4
    (h (GaloisField 2 f) p hp hp2 (by rwa [hK]) (by rwa [hK]))

theorem ggSixBstarExcFrameOn_F4_of_rest
    (hH : GGSixBstarExcFrameOn .F4 GGExcF4HalfLabel) (hN : GGExcNonsplitRankInput .F4) :
    GGSixBstarExcFrameOn .F4 GGExcF4Label := by
  have hNs : GGSixBstarExcFrameOn .F4 fun t _ f p => t = .F4 ∧ ¬ p ∣ 2 ^ f - 1 :=
    GGSixBstarExcFrameOn.of_or hH (ggSixBstarExcFrameOn_F4Rest_of_rank hN) fun _ _ f p h => by
      by_cases h2 : p ∣ 2 ^ f + 1
      · exact Or.inl ⟨h.1, h2⟩
      · exact Or.inr ⟨h.1, h.2, h2⟩
  exact GGSixBstarExcFrameOn.of_or ggSixBstarExcFrameOn_F4Split hNs fun _ _ f p h => by
    by_cases h1 : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, h1⟩

theorem ggSixBstarExcFrameOn_E7_of_rest
    (hH : GGSixBstarExcFrameOn .E7 GGExcE7HalfLabel) (hN : GGExcNonsplitRankInput .E7) :
    GGSixBstarExcFrameOn .E7 GGExcE7Label := by
  have hNs : GGSixBstarExcFrameOn .E7 fun t _ f p => t = .E7 ∧ ¬ p ∣ 2 ^ f - 1 :=
    GGSixBstarExcFrameOn.of_or hH (ggSixBstarExcFrameOn_E7Rest_of_rank hN) fun _ _ f p h => by
      by_cases h2 : p ∣ 2 ^ f + 1
      · exact Or.inl ⟨h.1, h2⟩
      · exact Or.inr ⟨h.1, h.2, h2⟩
  exact GGSixBstarExcFrameOn.of_or ggSixBstarExcFrameOn_E7Split hNs fun _ _ f p h => by
    by_cases h1 : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨h, h1⟩
    · exact Or.inr ⟨h, h1⟩

theorem ggSixBstarExcFrameOn_E8_of_rest (hH : GGSixBstarExcFrameOn .E8 GGExcE8HalfLabel)
    (hN : GGSixBstarExcFrameOn .E8 GGExcE8RestLabel) :
    GGSixBstarExcFrameOn .E8 GGExcE8FrameLabel := by
  have hNs : GGSixBstarExcFrameOn .E8 fun t _ f p => t = .E8 ∧ ¬ p ∣ 2 ^ f - 1 ∧
      (p ∣ 2 ^ f + 1 ∨ p ≠ 5) :=
    GGSixBstarExcFrameOn.of_or hH hN fun _ _ f p h => by
      by_cases h2 : p ∣ 2 ^ f + 1
      · exact Or.inl ⟨h.1, h2⟩
      · refine Or.inr ⟨h.1, h.2.1, h2, ?_⟩
        rcases h.2.2 with h' | h'
        · exact absurd h' h2
        · exact h'
  exact GGSixBstarExcFrameOn.of_or ggSixBstarExcFrameOn_E8Split hNs fun _ _ f p h => by
    by_cases h1 : p ∣ 2 ^ f - 1
    · exact Or.inl ⟨h.1, h1⟩
    · refine Or.inr ⟨h.1, h1, ?_⟩
      rcases h.2 with h' | h' | h'
      · exact absurd h' h1
      · exact Or.inl h'
      · exact Or.inr h'

@[expose] def GGSixBstarExcFramesRest : Prop :=
  GGSixBstarExcFrameOn .F4 GGExcF4HalfLabel ∧ GGExcNonsplitRankInput .F4 ∧
    GGSixBstarExcFrameOn .E7 GGExcE7HalfLabel ∧ GGExcNonsplitRankInput .E7 ∧
      GGSixBstarExcFrameOn .E8 GGExcE8HalfLabel ∧ GGSixBstarExcFrameOn .E8 GGExcE8RestLabel ∧
        GGSixBstarExcFrameOn .E6 GGExcE6SplitLabel ∧
          GGSixBstarExcFrameOn .F4 GGExcE6NonsplitLabel ∧
            GGSixBstarExcFrameOn .E6 GGExcTwE6SplitLabel ∧
              GGSixBstarExcFrameOn .F4 GGExcTwE6NonsplitLabel

theorem ggSixBstarExcFrames_of_rest
    (h : GGSixBstarExcFramesRest) : GGSixBstarExcFrames := by
  obtain ⟨hF4H, hF4N, hE7H, hE7N, hE8H, hE8N, hE6S, hE6N, hTwS, hTwN⟩ := h
  exact ⟨ggSixBstarExcFrameOn_F4_of_rest hF4H hF4N, ggSixBstarExcFrameOn_E7_of_rest hE7H hE7N,
    ggSixBstarExcFrameOn_E8_of_rest hE8H hE8N, hE6S, hE6N, hTwS, hTwN⟩

end Frames

end CFSG.StandardType
