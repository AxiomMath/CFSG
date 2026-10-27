module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfExt
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFrames

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Minuscule CFSG.Assembly.LowTwoRank ExcFrames ExcFramesHalf

@[expose] def GGExcE7HalfLargeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E7 ∧ p ∣ 2 ^ f + 1 ∧ p ≠ 3 ∧ p ≠ 5

@[expose] def GGExcE7HalfSmallLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E7 ∧ p ∣ 2 ^ f + 1 ∧ (p = 3 ∨ p = 5)

@[expose] def GGExcE8HalfLargeLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ p ∣ 2 ^ f + 1 ∧ p ≠ 3 ∧ p ≠ 5

@[expose] def GGExcE8HalfSmallLabel (t : StatedLieTag) (_n f p : ℕ) : Prop :=
  t = .E8 ∧ p ∣ 2 ^ f + 1 ∧ (p = 3 ∨ p = 5)

section Rank

@[expose] def GGExcHalfBstarRankOn (τ : Tag) (P : StatedLieTag → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), P t n f p →
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ →
    Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥ → p ^ τ.rank ≤ Nat.card Bs

theorem GGExcHalfBstarRankOn.of_or {τ : Tag} {P Q R : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hQ : GGExcHalfBstarRankOn τ Q) (hR : GGExcHalfBstarRankOn τ R)
    (h : ∀ t n f p, P t n f p → Q t n f p ∨ R t n f p) : GGExcHalfBstarRankOn τ P := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  rcases h t n f p hP with h' | h'
  · exact hQ G p B Bs x L D J t n f ψ h' hctx hC
  · exact hR G p B Bs x L D J t n f ψ h' hctx hC

end Rank

section Frames


theorem halfF4_inj_le_range {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .F4 n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .F4 n f).D .F4 n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) :
    Function.Injective ψ ∧ Bs ≤ ψ.range := by
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hZ : Subgroup.center (adjointGroup .F4 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  refine ⟨hinj, fun b hb => ?_⟩
  obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_F4 (K := GaloisField 2 f) ψ hker
    (hctx.2.2.2.2.2.2.1.2 b hb)
  have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
  have hg' : g ∈ ψ.range := hg
  rw [hCψ, Subgroup.mem_bot] at hbg'
  rw [eq_inv_of_mul_eq_one_left hbg']
  exact ψ.range.inv_mem hg'

theorem halfE8_inj_le_range {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {n f : ℕ} {ψ : (ggU .E8 n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU .E8 n f).D .E8 n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) :
    Function.Injective ψ ∧ Bs ≤ ψ.range := by
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hZ : Subgroup.center (adjointGroup .E8 (GaloisField 2 f)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hCψ : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact hC
  refine ⟨hinj, fun b hb => ?_⟩
  obtain ⟨g, hg, hbg⟩ := PsiDiag.Adj.exists_mem_centralizer_E8 (K := GaloisField 2 f) ψ hker
    (hctx.2.2.2.2.2.2.1.2 b hb)
  have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
  have hg' : g ∈ ψ.range := hg
  rw [hCψ, Subgroup.mem_bot] at hbg'
  rw [eq_inv_of_mul_eq_one_left hbg']
  exact ψ.range.inv_mem hg'

theorem ggExcHalfBstarRankOn_E8Large : GGExcHalfBstarRankOn .E8 GGExcE8HalfLargeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hp3, hp5⟩ := hP
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hinj, hBsR⟩ := halfE8_inj_le_range hctx hC
  have h11 := eleven_le_of_dvd_two_pow_add_one hp hp2 hpq hp3 hp5
  exact pow_le_card_of_sylowTorus
    (sylowTorus_E8_half (GaloisField 2 f) hp h11 (by rw [hK]; exact hpq)) ψ hinj hBsR
    hctx.2.1.2.1 hctx.2.1.2.2.2

theorem halfE7_chi
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ}
    {ψ : (ggU .E7 n f).K →* G} (hctx : GGSixCtxV2 p B Bs x L D J (ggU .E7 n f).D .E7 n f ψ)
    (hC : Subgroup.centralizer (ggG0 p B x L D J : Set G) = ⊥) :
    ∃ χ : adjointGroup .E7 (GaloisField 2 f) →* G, Function.Injective χ ∧
      (χ.range : Set G) = ψ.range ∧ Bs ≤ χ.range := by
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
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
  refine ⟨ψ.comp e.symm.toMonoidHom, hinj.comp e.symm.injective, ?_, ?_⟩
  · ext b
    exact ⟨fun ⟨u, hu⟩ => ⟨e.symm u, hu⟩, fun ⟨u, hu⟩ => ⟨e u, by
      have h1 : e.symm (e u) = u := e.symm_apply_apply u
      show ψ (e.symm (e u)) = b
      rw [h1]
      exact hu⟩⟩
  · intro b hb
    obtain ⟨u, hu⟩ := hBsR hb
    refine ⟨e u, ?_⟩
    have h1 : e.symm (e u) = u := e.symm_apply_apply u
    show ψ (e.symm (e u)) = b
    rw [h1]
    exact hu

theorem ggExcHalfBstarRankOn_E7Large :
    GGExcHalfBstarRankOn .E7 GGExcE7HalfLargeLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq, hp3, hp5⟩ := hP
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨χ, hχ, -, hBsR⟩ := halfE7_chi hctx hC
  have h11 := eleven_le_of_dvd_two_pow_add_one hp hp2 hpq hp3 hp5
  exact pow_le_card_of_sylowTorus
    (sylowTorus_E7_half (GaloisField 2 f) hp h11 (by rw [hK]; exact hpq)) χ hχ hBsR
    hctx.2.1.2.1 hctx.2.1.2.2.2

theorem ggSixBstarExcFrameOn_F4Half :
    GGSixBstarExcFrameOn .F4 GGExcF4HalfLabel := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx hC
  obtain ⟨rfl, hpq⟩ := hP
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  have hrange := hctx.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hinj, hBsR⟩ := halfF4_inj_le_range hctx hC
  have hcfg : GGConfig p B Bs x L D J := ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩
  obtain ⟨-, hBs, -, -, h4⟩ := hcfg.tableB_facts
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_half_of_card (Or.inl rfl) hf hK hp2
    (by rw [hK]; exact hpq) ψ hinj hBsR hBs h4
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  exact h

theorem ggSixBstarExcFrameOn_E8Half_of_rankOn
    {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hP : ∀ t n f p, P t n f p → t = .E8 ∧ p ∣ 2 ^ f + 1) (h : GGExcHalfBstarRankOn .E8 P) :
    GGSixBstarExcFrameOn .E8 P := by
  intro G _ _ p B Bs x L D J t n f ψ hPl hctx hC
  have hr := h G p B Bs x L D J t n f ψ hPl hctx hC
  obtain ⟨rfl, hpq⟩ := hP t n f p hPl
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  have hrange := hctx.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨hinj, hBsR⟩ := halfE8_inj_le_range hctx hC
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_half_of_card (Or.inr (Or.inr rfl)) hf hK hp2
    (by rw [hK]; exact hpq) ψ hinj hBsR hctx.2.1.2.1 hr
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  exact h

theorem ggSixBstarExcFrameOn_E7Half_of_rankOn
    {P : StatedLieTag → ℕ → ℕ → ℕ → Prop}
    (hP : ∀ t n f p, P t n f p → t = .E7 ∧ p ∣ 2 ^ f + 1) (h : GGExcHalfBstarRankOn .E7 P) :
    GGSixBstarExcFrameOn .E7 P := by
  intro G _ _ p B Bs x L D J t n f ψ hPl hctx hC
  have hr := h G p B Bs x L D J t n f ψ hPl hctx hC
  obtain ⟨rfl, hpq⟩ := hP t n f p hPl
  left
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  have := Fact.mk hp
  have hrange := hctx.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨χ, hχ, hχr, hBsR⟩ := halfE7_chi hctx hC
  obtain ⟨ι, hι, hιr, hact⟩ := exists_weylFrame_half_of_card (Or.inr (Or.inl rfl)) hf hK hp2
    (by rw [hK]; exact hpq) χ hχ hBsR hctx.2.1.2.1 hr
  refine ⟨ι, hι, hιr, fun g hgM hgB hgp => hact g ?_ hgB hgp⟩
  have h : g ∈ Subgroup.normalizer (ψ.range : Set G) := by rw [hrange]; exact hgM
  rw [hχr]
  exact h

end Frames

end CFSG.StandardType
