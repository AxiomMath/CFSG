module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107OutAct
import CFSG.ClassicalInvolution.Q3.TL4OddMu4
import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.P812Fusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPCube
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15P812GlueB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107Odd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)

variable {G : Type} [Group G] [Finite G]

theorem map_conj_eq_or_eq {D : Data G} (h82 : F08.R82 D) (hnsp : ¬ IsStronglyPEmbedded 3 D.M)
    {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M) (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂)
    (r₁ : CFSG.Open.pRank 3 L₁ = 1) (r₂ : CFSG.Open.pRank 3 L₂ = 1) {g : G} (hg : g ∈ D.M) :
    L₁.map (MulAut.conj g).toMonoidHom = L₁ ∨ L₁.map (MulAut.conj g).toMonoidHom = L₂ := by
  by_contra h
  push Not at h
  have hK : L₁.map (MulAut.conj g).toMonoidHom ∈ conjSetOf D.M L₁ := ⟨g, hg, rfl⟩
  exact hnsp (h82 _ (R8107Odd.hyp81_of_three_rankOne hL₁ hL₂
    (uc22p2214_calC_of_mem_conjSetOf hL₁ hK) h12 (Ne.symm h.1) (Ne.symm h.2) r₁ r₂
    ((PartOne.Section8.pRank_three_conj_of_mem_conjSetOf hK).trans r₁)))

theorem mem_normalizer_of_conj_eq {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M)
    (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂) (r₁ : CFSG.Open.pRank 3 L₁ = 1)
    (r₂ : CFSG.Open.pRank 3 L₂ = 1) (hZ₁ : center (Bar2 L₁) = ⊥) {a g : G} (haL : a ∈ L₁)
    (ha3 : orderOf a = 3) (hg : g ∈ D.M) (hga : g * a * g⁻¹ = a) :
    g ∈ normalizer (L₁ : Set G) ∧ g ∈ normalizer (L₂ : Set G) := by
  have h₁ : L₁.map (MulAut.conj g).toMonoidHom = L₁ := by
    refine (map_conj_eq_or_eq h82 hnsp hL₁ hL₂ h12 r₁ r₂ hg).resolve_right fun h => ?_
    have haK : a ∈ L₁.map (MulAut.conj g).toMonoidHom := ⟨a, haL, hga⟩
    rw [h] at haK
    have ha3' : a ^ 3 = 1 := ha3 ▸ pow_orderOf_eq_one a
    have ha1 : a ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ha3; omega
    exact rhoL_ne_one_of_mem hZ₁ haL ha3' ha1 (rhoL_eq_one_of_mem hL₁ hL₂ h12 haK _)
  refine ⟨mem_normalizer_iff_map_conj_eq.2 h₁, mem_normalizer_iff_map_conj_eq.2 ?_⟩
  refine (map_conj_eq_or_eq h82 hnsp hL₂ hL₁ h12.symm r₂ r₁ hg).resolve_right fun h => h12 ?_
  exact map_injective (MulAut.conj g).injective (h₁.trans h.symm)

private theorem mem_normalizer_zpowers {S L A : Subgroup G} (hc : IsCyclic ↥(S ⊓ L))
    (hAS : A ≤ S) (hA3 : ∀ x ∈ A, x ^ 3 = 1) {a g : G} (haA : a ∈ A) (haL : a ∈ L)
    (ha3 : orderOf a = 3) (hgA : g ∈ normalizer (A : Set G))
    (hgL : g ∈ normalizer (L : Set G)) : g ∈ normalizer (zpowers a : Set G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine mem_normalizer_fintype fun n hn => ?_
  have hxA := (mem_normalizer_iff.1 hgA n).1 (zpowers_le.2 haA hn)
  have hxL := (mem_normalizer_iff.1 hgL n).1 (zpowers_le.2 haL hn)
  by_cases hx1 : g * n * g⁻¹ = 1
  · rw [hx1]
    exact one_mem _
  exact CFSG.AGLEmbedding.mem_zpowers_of_isCyclic_of_orderOf_eq_three hc ⟨hAS haA, haL⟩
    ⟨hAS hxA, hxL⟩ ha3 (orderOf_eq_prime (hA3 _ hxA) hx1)

theorem mem_uniqueSet_of_outer {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L₁ L₂ : Subgroup G} (hL₁ : L₁ ∈ calC D.M)
    (hL₂ : L₂ ∈ calC D.M) (h12 : L₁ ≠ L₂) (r₁ : CFSG.Open.pRank 3 L₁ = 1)
    (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (hs₁ : R8107Shape.ThinShape (Bar2 L₁) ∨ ∃ n : ℕ, IsU3 (Bar2 L₁) n)
    (hs₂ : R8107Shape.ThinShape (Bar2 L₂) ∨ ∃ n : ℕ, IsU3 (Bar2 L₂) n)
    (hZ₁ : center (Bar2 L₁) = ⊥) (hZ₂ : center (Bar2 L₂) = ⊥) (hM3 : CFSG.Open.pRank 3 D.M ≤ 3)
    {R : Subgroup G} (hR : CFSG.ABGLocalTools.IsSylowOf 3 R D.M)
    (hR₁ : R ≤ normalizer (L₁ : Set G)) {a₁ a₂ : G} (ha₁ : a₁ ∈ R ⊓ L₁) (ha₂ : a₂ ∈ R ⊓ L₂)
    (ho₁ : orderOf a₁ = 3) (ho₂ : orderOf a₂ = 3)
    (hN₁ : normalizer (zpowers a₁ : Set G) ≤ D.M) (hN₂ : normalizer (zpowers a₂ : Set G) ≤ D.M)
    (hN₁₂ : normalizer ((zpowers a₁ ⊔ zpowers a₂ : Subgroup G) : Set G) ≤ D.M) {a₀ : G}
    (ha₀ : a₀ ∈ R) (ha₀3 : a₀ ^ 3 = 1) (hout : ¬ IsInnerAut (UC6S846.rhoL L₁ ⟨a₀, hR₁ ha₀⟩)) :
    zpowers a₁ ∈ uniqueSet D.M ∧ zpowers a₂ ∈ uniqueSet D.M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hRp : IsPGroup 3 R := hR.isPGroup
  have hR₂ : R ≤ normalizer (L₂ : Set G) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hRp
    exact R8107Odd.le_normalizer_of_odd h82 hnsp hL₂ r₂ hR.le (hn ▸ Odd.pow (by decide))
  obtain ⟨b, hbR, hb3, hb₁, hb₂⟩ :=
    exists_outer_or_trivial hL₁ hL₂ h12 r₂ hZ₂ hRp hR₁ hR₂ ha₂ ho₂ ha₀ ha₀3 hout
  have hc₁3 : Nat.card (zpowers a₁) = 3 := by rw [Nat.card_zpowers, ho₁]
  have hc₂3 : Nat.card (zpowers a₂) = 3 := by rw [Nat.card_zpowers, ho₂]
  obtain ⟨hAel, hA27, hΩ⟩ := omega_eq_of_outer hL₁ hL₂ h12 r₁ r₂ hs₁ hs₂ hZ₁ hZ₂ hR hR₁ hR₂ hM3
    (zpowers_le.2 ha₁) hc₁3 (zpowers_le.2 ha₂) hc₂3 hbR hb3 hb₁
  set A := zpowers a₁ ⊔ zpowers a₂ ⊔ zpowers b with hA
  have hgen : closure {b, a₁, a₂} = A := by
    rw [hA, Set.insert_eq, Set.insert_eq, Subgroup.closure_union, Subgroup.closure_union,
      ← zpowers_eq_closure, ← zpowers_eq_closure, ← zpowers_eq_closure]
    exact sup_comm _ _
  have hAR : A ≤ R := sup_le (sup_le (zpowers_le.2 ha₁.1) (zpowers_le.2 ha₂.1)) (zpowers_le.2 hbR)
  have hbA : b ∈ A := mem_sup_right (mem_zpowers b)
  have ha₁A : a₁ ∈ A := mem_sup_left (mem_sup_left (mem_zpowers a₁))
  have ha₂A : a₂ ∈ A := mem_sup_left (mem_sup_right (mem_zpowers a₂))
  have hc₁ := le_centralizer_of_pRank_eq_one r₁ hRp hR₁ (zpowers_le.2 ha₁) hc₁3 (mem_zpowers a₁)
  have hc₂ := le_centralizer_of_pRank_eq_one r₂ hRp hR₂ (zpowers_le.2 ha₂) hc₂3 (mem_zpowers a₂)
  have hfix : ∀ {t u : G} {K : Subgroup G}, t ∈ centralizer (K : Set G) → u ∈ K →
      t * u * t⁻¹ = u := fun ht hu => by
    rw [← mem_centralizer_iff.1 ht _ hu, mul_inv_cancel_right]
  have hNA : ∀ g, g * b * g⁻¹ ∈ A → g * a₁ * g⁻¹ ∈ A → g * a₂ * g⁻¹ ∈ A →
      g ∈ normalizer (A : Set G) := fun g h₀ h₁ h₂ => by
    rw [← hgen] at h₀ h₁ h₂ ⊢
    exact CFSG.ClassicalInvolution.Q3.TL4.mem_normalizer_closure_three h₀ h₁ h₂
  have hB₁ : zpowers b ⊔ zpowers a₂ ≤ R := sup_le (zpowers_le.2 hbR) (zpowers_le.2 ha₂.1)
  obtain ⟨t₁, ⟨-, ht₁c⟩, ht₁⟩ := exists_inverting hL₁ r₁ hs₁ (hRp.to_le hB₁) (hB₁.trans hR₁)
    (hR₁ hbR) hb3 (Or.inl hb₁)
    (fun u hu hu₂ => rhoL_eq_one_of_mem hL₁ hL₂ h12 (zpowers_le.2 ha₂.2 hu₂) hu) ha₁.2 ho₁
    (centralizer_le (SetLike.coe_subset_coe.2 hB₁) hc₁)
  have hB₂ : zpowers b ⊔ zpowers a₁ ≤ R := sup_le (zpowers_le.2 hbR) (zpowers_le.2 ha₁.1)
  obtain ⟨t₂, ⟨-, ht₂c⟩, ht₂⟩ := exists_inverting hL₂ r₂ hs₂ (hRp.to_le hB₂) (hB₂.trans hR₂)
    (hR₂ hbR) hb3 hb₂
    (fun u hu hu₁ => rhoL_eq_one_of_mem hL₂ hL₁ h12.symm (zpowers_le.2 ha₁.2 hu₁) hu) ha₂.2 ho₂
    (centralizer_le (SetLike.coe_subset_coe.2 hB₂) hc₂)
  have ht₁b := hfix ht₁c (mem_sup_left (mem_zpowers b))
  have ht₁a₂ := hfix ht₁c (mem_sup_right (mem_zpowers a₂))
  have ht₂b := hfix ht₂c (mem_sup_left (mem_zpowers b))
  have ht₂a₁ := hfix ht₂c (mem_sup_right (mem_zpowers a₁))
  obtain ⟨x, hxRL, hxb, hxa₁⟩ := exists_transvection hL₁ r₁ hs₁ hR hR₁ ha₁ ho₁ hbR hb3 hb₁
  have hxa₁' : x * a₁ * x⁻¹ = a₁ := by rw [hxa₁, mul_inv_cancel_right]
  have hxa₂ : x * a₂ * x⁻¹ = a₂ := by
    rw [mem_centralizer_iff.1 hc₂ x hxRL.1, mul_inv_cancel_right]
  have hNAM : normalizer (A : Set G) ≤ D.M :=
    RankThreeUC.S15.P812.caseII_normalizer_le_of_fixes (a := ![b, a₁, a₂]) (k := 1) (by decide)
      (Or.inl rfl) hAel (by rw [hA27]; norm_num) (fun i => by fin_cases i; exacts [hbA, ha₁A, ha₂A])
      hgen (hNA t₁ (by rw [ht₁b]; exact hbA) (by rw [ht₁]; exact A.inv_mem ha₁A)
        (by rw [ht₁a₂]; exact ha₂A))
      (hNA t₂ (by rw [ht₂b]; exact hbA) (by rw [ht₂a₁]; exact ha₁A)
        (by rw [ht₂]; exact A.inv_mem ha₂A))
      (hNA x (by rw [hxb]; exact A.mul_mem hbA ha₁A) (by rw [hxa₁']; exact ha₁A)
        (by rw [hxa₂]; exact ha₂A))
      ⟨ht₁b, ht₁, ht₁a₂⟩ ⟨ht₂b, ht₂a₁, ht₂⟩ ⟨hxb, hxa₁', hxa₂⟩ hN₁ hN₂ hN₁₂
      fun g hgA hgM j hj hgj => by
        obtain ⟨hg₁, hg₂⟩ : g ∈ normalizer (L₁ : Set G) ∧ g ∈ normalizer (L₂ : Set G) := by
          rcases hj with rfl | rfl
          · exact mem_normalizer_of_conj_eq h82 hnsp hL₁ hL₂ h12 r₁ r₂ hZ₁ ha₁.2 ho₁ hgM hgj
          · exact (mem_normalizer_of_conj_eq h82 hnsp hL₂ hL₁ h12.symm r₂ r₁ hZ₂ ha₂.2 ho₂ hgM
              hgj).symm
        exact ⟨mem_normalizer_zpowers (R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₁
            inf_le_right hRp.to_inf_left) hAR hAel.2 ha₁A ha₁.2 ho₁ hgA hg₁,
          mem_normalizer_zpowers (R8107Shape.isCyclic_of_isPGroup_of_pRank_eq_one r₂
            inf_le_right hRp.to_inf_left) hAR hAel.2 ha₂A ha₂.2 ho₂ hgA hg₂⟩
  exact ⟨AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hAR hAel hΩ hNAM
      (zpowers_le.2 ha₁A) hN₁,
    AGL81TheoremCD.Section8.mem_uniqueSet_of_normalizer_le_of_omega hR hAR hAel hΩ hNAM
      (zpowers_le.2 ha₂A) hN₂⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Out
