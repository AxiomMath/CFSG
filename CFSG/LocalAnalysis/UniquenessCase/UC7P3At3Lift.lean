module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Layer3
import CFSG.Assembly.OrderReductions.ThompsonQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem alt1_of_quotient (k : Sec7Core4 G) (h75 : Step75 k) {H : Subgroup G} (hH : Config k H)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M))
    {Pb : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)}
    (hPb : (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) = Pb)
    (hPF : Pb ≤ CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
    (hexp : ∀ x ∈ Pb, x ^ k.p = 1)
    (hNP : ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
      normalizer (Pb : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))
    (hirr : ∀ W : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H), W ≤ Pb →
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ⊓
          normalizer (Pb : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
        normalizer (W : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) →
      W ≤ ⁅Pb, Pb⁆ ∨ W = Pb) :
    (∀ x ∈ P, x ^ k.p = 1) ∧ H ⊓ k.M = H ⊓ normalizer (P : Set G) ∧
      ∀ W : Subgroup G, W ≤ P →
        CFSG.Open.rankThreeLayer H ⊓ normalizer (P : Set G) ≤ normalizer (W : Set G) →
          W ≤ ⁅P, P⁆ ∨ W = P := by
  subst hPb
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hPHM, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hPH : P ≤ H := hPHM.trans inf_le_left
  have hinj := CFSG.OrderReductions.ThompsonQuotient.prime_subgroup_injective_of_coprime_kernel
    k.p (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))
    (by
      rw [QuotientGroup.ker_mk']
      exact (k.prime.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (p := k.p) (G := ↥H)))
    (P.subgroupOf H) hPp.comap_subtype
  have hinj' : ∀ a ∈ P.subgroupOf H, ∀ b ∈ P.subgroupOf H,
      QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) a =
        QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) b → a = b :=
    fun a ha b hb hab =>
      congrArg Subtype.val (hinj (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hab))
  have hpow : ∀ x ∈ P, x ^ k.p = 1 := by
    intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr hx
    have h1 := hinj' _ (pow_mem hx' k.p) 1 (one_mem _) (by
      rw [map_pow, map_one]
      exact hexp _ ⟨_, hx', rfl⟩)
    simpa using congrArg Subtype.val h1
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, hi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
    rw [Subgroup.relIndex_bot_left] at hi
    exact hi ((dvd_pow_self k.p two_ne_zero).trans ((pow_dvd_pow k.p hH.two_le_pRank).trans
      (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card k.p k.prime _)))
  have hPK := k.commutator_pPrimeCore_eq_bot_of_isPGroup h75 hH hPH hPp hPF
  have hle : H ⊓ k.M ≤ normalizer (P : Set G) := fun x hx =>
    mem_normalizer_of_mk_mem_normalizer (h := ⟨x, hx.1⟩) hPH hPp hPK
      (hNP ⟨⟨x, hx.1⟩, mem_subgroupOf.mpr hx, rfl⟩)
  have hge : normalizer (P : Set G) ≤ k.M :=
    k.strong.normalizer_le hP1 hPp (hPHM.trans inf_le_right)
  refine ⟨hpow, le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left H hge),
    fun W hWP hWN => ?_⟩
  rcases hirr _ (map_mono (subgroupOf_mono H hWP))
      ((k.fstar_inf_normalizer_le_map h75 hH hPH hPp hPF).trans
        ((map_mono (subgroupOf_mono H
          ((inf_le_inf_right _ (k.layerLift_le_rankThreeLayer h75 hH)).trans hWN))).trans
          ((map_mono (le_normalizer_comap H.subtype)).trans (le_normalizer_map _)))) with
    h | h
  ·
    refine Or.inl fun w hw => ?_
    have hw' : (⟨w, hPH (hWP hw)⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr (hWP hw)
    have hwm : QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨w, hPH (hWP hw)⟩ ∈
        ⁅(P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)),
          (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))⁆ :=
      h ⟨_, mem_subgroupOf.mpr hw, rfl⟩
    rw [← map_commutator] at hwm
    obtain ⟨y, hy, hyw⟩ := mem_map.mp hwm
    obtain rfl := hinj' y (commutator_le_self _ hy) _ hw' hyw
    have hc : (⁅P.subgroupOf H, P.subgroupOf H⁆).map H.subtype = ⁅P, P⁆ := by
      rw [map_commutator, map_subgroupOf_eq_of_le hPH]
    rw [← hc]
    exact ⟨_, hy, rfl⟩
  ·
    refine Or.inr (le_antisymm hWP fun x hx => ?_)
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr hx
    have hxm : QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨x, hPH hx⟩ ∈
        (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
      rw [h]
      exact ⟨_, hx', rfl⟩
    obtain ⟨w, hwW, hw⟩ := hxm
    obtain rfl := hinj' w (subgroupOf_mono H hWP hwW) _ hx' hw
    exact mem_subgroupOf.mp hwW

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
