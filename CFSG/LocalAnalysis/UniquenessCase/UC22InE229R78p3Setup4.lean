module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229R78p3
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3LinTwoRow
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Core3
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Layer3
import CFSG.LocalAnalysis.UniquenessCase.UC7P3LinTwoIrr

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem r7_8p3_of_config (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {H : Subgroup G} (hH : Config k H)
    (hr : 3 ≤ CFSG.Open.pRank k.p (H ⊓ k.M)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M)) :
    (∀ x ∈ P, x ^ 3 = 1) ∧ H ⊓ k.M = H ⊓ normalizer (P : Set G) ∧
      ∀ W : Subgroup G, W ≤ P →
        CFSG.Open.rankThreeLayer H ⊓ normalizer (P : Set G) ≤ normalizer (W : Set G) →
          W = ⊥ ∨ W = P := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨hPHM, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hPH : P ≤ H := hPHM.trans inf_le_left
  have h75 := step75_of_stronglyEmbeddedThree k hp3 hK3
  obtain ⟨P', hP'eq, hP'N⟩ := k.exists_sylow_map_of_isSylowOf hH hP
  obtain ⟨q, hq3, hqI, hPF, hPel, hPcard, -, hNP⟩ :=
    k.exists_isoLie_A1_of_config hG3 hRee hp3 hH hr P' hP'N
  rw [hP'eq] at hPF hPel hPcard hNP
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
  have hpow : ∀ x ∈ P, x ^ 3 = 1 := by
    intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr hx
    have h1 := hinj' _ (pow_mem hx' 3) 1 (one_mem _) (by
      rw [map_pow, map_one]
      exact hPel.2 _ ⟨_, hx', rfl⟩)
    simpa using congrArg Subtype.val h1
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    rw [bot_subgroupOf, Subgroup.map_bot, card_bot, q.card_def] at hPcard
    exact (Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt).ne hPcard
  have hPK := k.commutator_pPrimeCore_eq_bot_of_isPGroup h75 hH hPH hPp hPF
  have hle : H ⊓ k.M ≤ normalizer (P : Set G) := fun x hx =>
    mem_normalizer_of_mk_mem_normalizer (h := ⟨x, hx.1⟩) hPH hPp hPK
      (hNP ⟨⟨x, hx.1⟩, mem_subgroupOf.mpr hx, rfl⟩)
  have hge : normalizer (P : Set G) ≤ k.M :=
    k.strong.normalizer_le hP1 hPp (hPHM.trans inf_le_right)
  refine ⟨hpow, le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left H hge),
    fun W hWP hWN => ?_⟩
  rcases eq_bot_or_eq_of_le_of_isoLie_A1 (by rw [hq3]; norm_num) hqI hPF hPcard
      (map_mono (subgroupOf_mono H hWP))
      ((k.fstar_inf_normalizer_le_map h75 hH hPH hPp hPF).trans
        ((map_mono (subgroupOf_mono H
          ((inf_le_inf_right _ (k.layerLift_le_rankThreeLayer h75 hH)).trans hWN))).trans
          ((map_mono (le_normalizer_comap H.subtype)).trans (le_normalizer_map _)))) with
    h | h
  · refine Or.inl (eq_bot_iff.2 fun w hw => ?_)
    have hw' : (⟨w, hPH (hWP hw)⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr (hWP hw)
    have hwm : QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨w, hPH (hWP hw)⟩ ∈
        (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :=
      ⟨_, mem_subgroupOf.mpr hw, rfl⟩
    rw [h, mem_bot] at hwm
    have h1 := hinj' _ hw' 1 (one_mem _) (by rw [hwm, map_one])
    exact mem_bot.mpr (by simpa using congrArg Subtype.val h1)
  · refine Or.inr (le_antisymm hWP fun x hx => ?_)
    have hx' : (⟨x, hPH hx⟩ : ↥H) ∈ P.subgroupOf H := mem_subgroupOf.mpr hx
    have hxm : QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H) ⟨x, hPH hx⟩ ∈
        (W.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
      rw [h]
      exact ⟨_, hx', rfl⟩
    obtain ⟨w, hwW, hw⟩ := hxm
    have h1 := hinj' w (subgroupOf_mono H hWP hwW) _ hx' hw
    subst h1
    exact mem_subgroupOf.mp hwW

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open PartOne.Section7 (Sec7Core4 StronglyEmbeddedThree normalizer_le_of_r6_3)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem r7_8R3p3_dataOfSetup4 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hC : TheoremCAt S.M) : R7_8R3p3 (UC6.dataOfSetup4 hS hU S) := by
  intro H P D₀ hH hP hD₀ hr
  obtain ⟨-, -, hsp, hHt, hHM, h2⟩ := hH
  obtain ⟨hpow, hMN, hirr⟩ := Sec7Core4.r7_8p3_of_config hG3 hRee hK3
    (Sec7Core4.ofHuniq (UC6.dataOfSetup4 hS hU S).standing hU S.M S.maxLocal 3 Nat.prime_three
      (by norm_num) hsp fun T hT hT2 hT3 => normalizer_le_of_r6_3 _
        (UC6.r6_3_dataOfSetup4 hS hU S hC) Nat.prime_three (by norm_num) hsp hT hT2 hT3)
    rfl ⟨hHt, hHM, h2⟩ hr hP
  subst hD₀
  rw [CFSG.RankThree.PartOne.CTP.omegaOne_eq_of_pow_eq_one hpow]
  refine ⟨hpow, hMN, ?_, rfl⟩
  intro W hFW hWP hWN
  rcases hirr W hWP hWN with rfl | rfl
  · exact Or.inl (le_bot_iff.mp hFW).symm
  · exact Or.inr rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22
