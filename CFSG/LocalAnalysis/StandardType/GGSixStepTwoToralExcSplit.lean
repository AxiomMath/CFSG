module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralExcAdj
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesTags

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg.Minuscule
  CFSG.Assembly.LowTwoRank

namespace StepTwoToralExc

theorem eleven_le_of_not_dvd_weylE7 {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ 2903040) : 11 ≤ p := by
  by_contra hlt
  have h2 := hp.two_le
  interval_cases p
  · exact h (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact h (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)
  · exact absurd hp (by norm_num)

end StepTwoToralExc

open StepTwoToralExc

section SplitWeyl

theorem ggStepTwoExcSplitWeylOn_F4 : GGStepTwoExcSplitWeylOn .F4 :=
  ggStepTwoExcSplitWeylOn_F4_of_adj ggExcSplitWeylF4Input_holds

theorem ggStepTwoExcSplitWeylOn_E8 : GGStepTwoExcSplitWeylOn .E8 :=
  ggStepTwoExcSplitWeylOn_E8_of_adj ggExcSplitWeylE8Input_holds

theorem ggStepTwoExcSplitWeylOn_E7 :
    GGStepTwoExcSplitWeylOn .E7 := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hW hq
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp11 : 11 ≤ p := eleven_le_of_not_dvd_weylE7 hp hW
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by rw [hK]; exact hq
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hZ : Subgroup.center ↥(e7Data_valid.minGroup (GaloisField 2 f)) = ⊥ :=
    CFSG.SeitzReduction.E8Pilot.center_minGroup_e7_eq_bot
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hker.trans hZ.le
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by rw [hrange]; exact s1.1
  have hBsR : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ := PsiDiag.Minu.exists_mem_centralizer_E7 (k := GaloisField 2 f) ψ hker
      (hctx.2.2.2.2.2.2.1.2 b hb)
    have hbg' : b * g ∈ Subgroup.centralizer (ψ.range : Set G) := hbg
    have hg' : g ∈ ψ.range := hg
    rw [hC, Subgroup.mem_bot] at hbg'
    rw [eq_inv_of_mul_eq_one_left hbg']
    exact ψ.range.inv_mem hg'
  set e := CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f) with he
  set χ : adjointGroup .E7 (GaloisField 2 f) →* G := ψ.comp e.symm.toMonoidHom with hχ
  have hχinj : Function.Injective χ := hinj.comp e.symm.injective
  have hχr : χ.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext b
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨e.symm u, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨e u, ?_⟩
      have h1 : e.symm (e u) = u := e.symm_apply_apply u
      show ψ (e.symm (e u)) = ψ u
      rw [h1]
  have hBsG₀ : Bs ≤ ggG0 p B x L D J := hrange ▸ hBsR
  obtain ⟨hA, hcomp⟩ := StepTwoSplit.splitWeyl_of_adjAt (τ := .E7) (K := GaloisField 2 f) hp
    hχinj hχr hctx.2.1 hBsG₀ (TableBExc.not_dvd_index_torusGroup_E7 hp hp11 hpq)
    (ggExcSplitWeylAdjAt_E7 hp hp11 hpq)
  exact ⟨hA, fun b L₁ hpair => hcomp b hpair.1 hpair.2.1 L₁ hpair.2.2.1⟩

end SplitWeyl

section Witness

theorem ggStepTwoToralWitness_of_splitWeyl {t : StatedLieTag} (hS : GGStepTwoExcSplitWeylOn t)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    (hW : ¬ p ∣ ggExcWeylOrder t) (hq : p ∣ 2 ^ f - 1) {b : G} {L₁ : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J b L₁) :
    ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
      ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hDBs : D ≤ Bs := hctx.2.2.1.1.1.trans hctx.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hctx.2.2.1.1.2.2.1
  obtain ⟨hA, hpairs⟩ := hS G p B Bs x L D J n f ψ hctx s1 hW hq
  obtain ⟨hVL, Q, hQL, hQN, hC⟩ := hpairs b L₁ hpair
  have hQG₀ : Q ≤ ggG0 p B x L D J := hQL.trans (hpair.2.2.1.1.trans inf_le_left)
  exact ggStepTwoWitness_of_card_le_mul hp hctx.2.1.2.1 hDBs hDcard
    (hpair.card_le_mul_of_weyl hp hctx.2.1.2.1 hVL hQL hQN
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (ggAutomizer_mono Bs hQG₀)) hA) hC)

@[expose] def GGStepTwoToralWitnessExcRestOn (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f → (¬ p ∣ 2 ^ f - 1 ∨ p ∣ ggExcWeylOrder t) →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        ∃ a ∈ Bs ⊓ (Subgroup.zpowers b ⊔ L₁), a ≠ 1 ∧
          ∃ m ∈ ggG0 p B x L D J ⊓ Subgroup.normalizer (Bs : Set G), m⁻¹ * a * m ∈ D

theorem ggStepTwoToralWitnessOn_of_excRest {t : StatedLieTag} (hS : GGStepTwoExcSplitWeylOn t)
    (hR : GGStepTwoToralWitnessExcRestOn t) : GGStepTwoToralWitnessOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hlin b L₁ hpair
  by_cases h : p ∣ 2 ^ f - 1 ∧ ¬ p ∣ ggExcWeylOrder t
  · exact ggStepTwoToralWitness_of_splitWeyl hS hctx s1 h.2 h.1 hpair
  · have h' : ¬ p ∣ 2 ^ f - 1 ∨ p ∣ ggExcWeylOrder t := by
      by_cases hq : p ∣ 2 ^ f - 1
      · exact Or.inr (by_contra fun hW => h ⟨hq, hW⟩)
      · exact Or.inl hq
    exact hR G p B Bs x L D J n f ψ hctx s1 hlin h' b L₁ hpair

theorem ggStepTwoToralWitnessExcRestOn_of_index_small {t : StatedLieTag}
    (hI : GGStepTwoExcIndexNonsplitOn t) (hS : GGStepTwoToralWitnessSmallOn t) :
    GGStepTwoToralWitnessExcRestOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 _ hreg b L₁ hpair
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hDBs : D ≤ Bs := hctx.2.2.1.1.1.trans hctx.2.1.1
  have hDcard : Nat.card D = p ^ 2 := hctx.2.2.1.1.2.2.1
  by_cases hW : p ∣ ggExcWeylOrder t
  · by_cases hDR : D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥
    · exact hS G p B Bs x L D J n f ψ hctx s1 hW b L₁ hpair hDR
    · exact ggStepTwoWitness_of_inf_ne_bot hDBs hDR
  · exact ggStepTwoWitness_of_card_le_mul hp hctx.2.1.2.1 hDBs hDcard
      (hI G p B Bs x L D J n f ψ hctx s1 hW (hreg.resolve_right hW) b L₁ hpair)

end Witness

end CFSG.StandardType
