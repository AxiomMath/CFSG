module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Seitz
public import CFSG.RankThree.PartTwo.Sec4.Census.Wiring
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

theorem exists_surjective_layer_quotient_center {G₀ : Type} [Group G₀] {H : Subgroup G₀}
    {G : Type} [Group G] (f : H →* G) (hf : Function.Surjective f) :
    ∃ (H₁ : Subgroup G₀) (g : H₁ →* layer G ⧸ Subgroup.center (layer G)),
      Function.Surjective g := by
  set H₁' : Subgroup H := (layer G).comap f with hH₁'
  set H₁ : Subgroup G₀ := H₁'.map H.subtype with hH₁
  set e : H₁' ≃* H₁ := H₁'.equivMapOfInjective H.subtype H.subtype_injective with he
  set g₁ : H₁' →* layer G := (f.comp H₁'.subtype).codRestrict (layer G) fun x => x.2 with hg₁
  have hg₁s : Function.Surjective g₁ := by
    rintro ⟨l, hl⟩
    obtain ⟨h, rfl⟩ := hf l
    exact ⟨⟨h, hl⟩, rfl⟩
  refine ⟨H₁, (QuotientGroup.mk' (Subgroup.center (layer G))).comp
    (g₁.comp e.symm.toMonoidHom), ?_⟩
  exact (QuotientGroup.mk'_surjective _).comp (hg₁s.comp e.symm.surjective)

@[expose] def Item434LayerRanks : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
      (∀ p : ℕ, p.Prime → 3 < p → p ∣ Nat.card f.ker →
          CFSG.Assembly.RankThreeEven.localRank p
            (layer G ⧸ Subgroup.center (layer G)) < 3) ∧
        (Subgroup.center (layer G) ≠ ⊥ →
          CFSG.Assembly.RankThreeEven.localRank 3 (layer G ⧸ Subgroup.center (layer G)) ≤ 3)

open CFSG.Assembly.RankThreeEven (localRank) in
theorem item434LayerRanks_of_item4_1 (h41 : Item4_1) : Item434LayerRanks := by
  intro G₀ _ _ hG₀ H G _ _ f hf _ A M Q hc
  obtain ⟨H₁, g, hg⟩ := exists_surjective_layer_quotient_center f hf
  have hq := hc.isQuasisimple
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hq.2.1
  have e : H₁ ⧸ g.ker ≃* layer G ⧸ Subgroup.center (layer G) :=
    QuotientGroup.quotientKerEquivOfSurjective g hg
  have hq' : IsQuasisimple (H₁ ⧸ g.ker) :=
    isQuasisimple_of_mulEquiv e.symm (isQuasisimple_of_isSimpleGroup hq.2.2).1
  have hX := Census.sectionFourHyp_of_mulEquiv e
    (Census.sectionFourHyp_of_section h41 hG₀ H₁ g.ker hq')
  exact ⟨fun p hp hp3 _ => hX.localRank_lt p hp hp3, fun _ =>
    (OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hX.evenRank_le⟩

open CFSG.Assembly.RankThreeEven (localRank) in
theorem localRank_three_layer_quotient_center_le {G : Type} [Group G] [Finite G]
    (hZ : Subgroup.center (layer G) = ⊥) :
    localRank 3 (layer G ⧸ Subgroup.center (layer G)) ≤ localRank 3 G := by
  have e : layer G ⧸ Subgroup.center (layer G) ≃* layer G :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  rw [Census.localRank_eq_of_mulEquiv e Nat.prime_three]
  exact localRank_subgroup_le Nat.prime_three (layer G)

namespace Ctx434Core

open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem localRank_layer_quotient_center_le (h : Ctx434Core G A M Q) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    localRank p (layer G ⧸ Subgroup.center (layer G)) ≤ localRank p G := by
  have hZ : ¬ p ∣ Nat.card (Subgroup.center (layer G)) := by
    intro hpZ
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.isPGroup_center_layer
    rw [hk] at hpZ
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hpZ))
  exact (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 _ hZ).trans
    (localRank_subgroup_le hp (layer G))

theorem sectionFourHyp_layer (hR : Item434LayerRanks) {G₀ : Type} [Group G₀] [Finite G₀]
    (hG₀ : SectionFourHyp G₀) (H : Subgroup G₀) (f : H →* G) (hf : Function.Surjective f)
    (hker : ¬ 3 ∣ Nat.card f.ker) (h : Ctx434Core G A M Q) :
    SectionFourHyp (layer G ⧸ Subgroup.center (layer G)) := by
  obtain ⟨hRp, hR3⟩ := hR G₀ hG₀ H G f hf hker A M Q h
  have e : H ⧸ f.ker ≃* G := QuotientGroup.quotientKerEquivOfSurjective f hf
  have hKG : IsKGroup G := CFSG.SectionRank.K_group_section_closure_inCatalog hG₀.kGroup H f.ker e
  have hKL : IsKGroup (layer G ⧸ Subgroup.center (layer G)) :=
    CFSG.SectionRank.K_group_section_closure_inCatalog hKG (layer G) (Subgroup.center (layer G))
      (MulEquiv.refl _)
  have hH : ∀ p : ℕ, p.Prime → localRank p H ≤ localRank p G₀ := fun p hp =>
    localRank_subgroup_le hp H
  have hGeq : ∀ p : ℕ, p.Prime → localRank p G = localRank p (H ⧸ f.ker) := fun p hp =>
    (Census.localRank_eq_of_mulEquiv e hp).symm
  have hGle : ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ Nat.card f.ker →
      localRank p G ≤ localRank p G₀ := fun p hp hp2 hpN => by
    rw [hGeq p hp]
    exact (CFSG.RankThree.Classical2.localRank_quotient_le hp hp2 f.ker hpN).trans (hH p hp)
  have hG3 : localRank 3 G ≤ 3 :=
    (hGle 3 Nat.prime_three (by norm_num) hker).trans
      ((OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hG₀.evenRank_le)
  have hGp : ∀ p : ℕ, p.Prime → 3 < p → localRank p G ≤ 3 := fun p hp hp3 => by
    rw [hGeq p hp]
    exact (OddKernel.rank_three_three_complement_quotient_sharp_local_bounds f.ker).2.1 p hp hp3
      (by have := (hH p hp).trans_lt (hG₀.localRank_lt p hp hp3); omega)
  have hL3 : localRank 3 (layer G ⧸ Subgroup.center (layer G)) ≤ 3 := by
    by_cases hZ : Subgroup.center (layer G) = ⊥
    · exact (localRank_three_layer_quotient_center_le hZ).trans hG3
    · exact hR3 hZ
  have hLp : ∀ p : ℕ, p.Prime → 3 < p →
      localRank p (layer G ⧸ Subgroup.center (layer G)) ≤ localRank p G := fun p hp hp3 =>
    h.localRank_layer_quotient_center_le hp (by omega) (by omega)
  refine ⟨hKL, Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, fun p hp hp3 => ?_⟩
  · rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
    · exact hL3
    · exact (hLp p hp hp3).trans (hGp p hp hp3)
  · by_cases hpN : p ∣ Nat.card f.ker
    · exact hRp p hp hp3 hpN
    · exact (hLp p hp hp3).trans_lt ((hGle p hp (by omega) hpN).trans_lt
        (hG₀.localRank_lt p hp hp3))

end Ctx434Core

section Families


@[expose] def Item434SecFor (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q →
        P (layer G ⧸ Subgroup.center (layer G)) → Concl434 A Q

theorem item434SecFor_generic (hS : Seitz434) : Item434SecFor IsLie42Generic :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hL => (hc.false_of_seitz434 hS hL).elim

@[expose] def Item434CharThree : Prop :=
  Item434SecFor IsLie42CharThree

@[expose] def Item434SmallTwo : Prop :=
  Item434SecFor IsLie42SmallTwo

@[expose] def Item434Alt : Prop :=
  Item434SecFor IsAlt42

@[expose] def Item434Spor : Prop :=
  Item434SecFor IsSpor42

end Families

section Assembly

theorem item4_34Sec_of (hS : Seitz434) (hR : Item434LayerRanks) (h3 : Item434CharThree)
    (h2 : Item434SmallTwo) (hA : Item434Alt) (hSp : Item434Spor) : Item4_34Sec := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc
  have hq := hc.isQuasisimple
  have : IsSimpleGroup (layer G ⧸ Subgroup.center (layer G)) := hq.2.1
  have hX : SectionFourHyp (layer G ⧸ Subgroup.center (layer G)) :=
    hc.sectionFourHyp_layer hR hG₀ H f hf hker
  rcases list42_cases (Census.rank3II_4_2 _ hX this hq.2.2) with hgen | hc3 | hc2 | halt | hspor
  · exact item434SecFor_generic hS G₀ hG₀ H G f hf hker A M Q hc hgen
  · exact h3 G₀ hG₀ H G f hf hker A M Q hc hc3
  · exact h2 G₀ hG₀ H G f hf hker A M Q hc hc2
  · exact hA G₀ hG₀ H G f hf hker A M Q hc halt
  · exact hSp G₀ hG₀ H G f hf hker A M Q hc hspor

theorem item4_34Sec_of_item4_1 (hS : Seitz434) (h41 : Item4_1) (h3 : Item434CharThree)
    (h2 : Item434SmallTwo) (hA : Item434Alt) (hSp : Item434Spor) : Item4_34Sec :=
  item4_34Sec_of hS (item434LayerRanks_of_item4_1 h41) h3 h2 hA hSp

end Assembly

end CFSG.RankThree.PartTwo.Sec4
