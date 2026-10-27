module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKLeaves
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight8xKPorts887
import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
import CFSG.LocalAnalysis.UniquenessCase.UC6R869T3
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R71 R72 Sec7Hyp ImageModK QuotK7 PPrimeCoreIn)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)

theorem r889_pRank_subgroupOf_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K D : Subgroup G} (h : K ≤ D) :
    CFSG.Open.pRank p (K.subgroupOf D) = CFSG.Open.pRank p K := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (K.subgroupOf D),
    CFSG.SectionRank.pRank_eq_pRank_top_subgroup K]
  exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv
    (Fact.out : p.Prime).one_lt (Subgroup.subgroupOfEquivOfLe h)

theorem r889_imageModK_opp_normal {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G} :
    (ImageModK p H (Opp p H)).Normal := by
  have hOppH : ((Opp p H).subgroupOf H).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : G) ∈ Subgroup.normalizer (Opp p H : Set G) :=
      CFSG.LocalAnalysis.UniquenessCase.UC6.mem_normalizer_Opp_uc6
        (Subgroup.le_normalizer g.2) p
    exact (Subgroup.mem_normalizer_iff.mp hg n).mp hn
  have h := hOppH.map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))
    (QuotientGroup.mk'_surjective _)
  simpa [ImageModK] using h

theorem r889_alt6_section_of_le {G : Type} [Group G] [Finite G] {M K H : Subgroup G} {p : ℕ}
    (hKM : K ≤ M) (hKH : K ≤ H) (hA6 : IsA6Z3 (Bar2 K))
    (hK : ¬ 2 ∣ Nat.card (PPrimeCoreIn p H)) :
    ∃ (A : Subgroup ↥(ImageModK p H (H ⊓ M))) (V : Subgroup ↥A) (_ : V.Normal),
      IsAlt (↥A ⧸ V) 6 := by
  classical
  let q0 : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  let f : ↥K →* Bar2 K ⧸ Subgroup.center (Bar2 K) :=
    (QuotientGroup.mk' (Subgroup.center (Bar2 K))).comp q0
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  let qH : ↥H →* QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let φ₀ : ↥K →* QuotK7 p H := qH.comp (Subgroup.inclusion hKH)
  have hφ₀ : ∀ c : ↥K, φ₀ c ∈ ImageModK p H (H ⊓ M) := by
    intro c
    refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion hKH c, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr ⟨hKH c.2, hKM c.2⟩
  let φ : ↥K →* ↥(ImageModK p H (H ⊓ M)) := φ₀.codRestrict _ hφ₀
  have hodd : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map K.subtype ≤ PPrimeCoreIn p H := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : φ x = 1 := hx
      have hx2 : φ₀ x = 1 := congrArg Subtype.val hx1
      have hx3 : Subgroup.inclusion hKH x ∈ CFSG.pPrimeCore p ↥H :=
        (QuotientGroup.eq_one_iff _).mp hx2
      exact Subgroup.mem_map_of_mem H.subtype hx3
    have hcardmap : Nat.card (φ.ker.map K.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective K.subtype_injective
    have hdvd : Nat.card φ.ker ∣ Nat.card (PPrimeCoreIn p H) := by
      rw [← hcardmap]
      exact Subgroup.card_dvd_of_le hle
    exact fun h => hK (h.trans hdvd)
  have hQsimple : IsSimpleGroup (Bar2 K ⧸ Subgroup.center (Bar2 K)) := hA6.1.2.1
  have hQ2 : 2 ∣ Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
    have h360 : Nat.card (Bar2 K ⧸ Subgroup.center (Bar2 K)) = 360 := by
      obtain ⟨e⟩ := hA6.2.2
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4
    rw [h360]
    norm_num
  obtain ⟨A, V, hV, ⟨e⟩⟩ := r887_exists_section_of_hom φ f hf hodd hQ2
  obtain ⟨e'⟩ := hA6.2.2
  exact ⟨A, V, hV, ⟨e.trans e'⟩⟩

theorem s889_five_of_facts {G : Type} [Group G] [Finite G] (D : Data G) (hSg : SigmaStd D)
    (h71 : R71 D) (h72 : R72 D) (h885 : R885 D) (hAlt6 : FiveEmbeddedNoAlt6)
    (hFacts : AllFacts889 D) : S889Five D := by
  intro L P ω hω X hXtop hKX hXM
  have hS : Set880 D L P := hω.set880
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨-, hsig, -⟩ := h885 L P hS
  have hns : ¬ Group.IsSolvable ↥D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.not_solvable_of_mem_calC hS.mem
  have h5 : (5 : ℕ) ∈ D.sig := by
    rw [hsig]
    exact Set.mem_singleton 5
  have hsp : IsStronglyPEmbedded 5 D.M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.sp_of_mem_sig hSg hns h5
  obtain ⟨H, hHc, hXH⟩ := (IsCoatomic.eq_top_or_exists_le_coatom X).resolve_left hXtop
  have hHM : ¬ H ≤ D.M := fun h => hXM (hXH.trans h)
  by_contra hrk
  have hrk1 : 1 < CFSG.Open.pRank 5 (X ⊓ D.M) := not_le.mp hrk
  have hrankH : 2 ≤ CFSG.Open.pRank 5 (H ⊓ D.M) :=
    lt_of_lt_of_le hrk1
      (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) (inf_le_inf_right _ hXH))
  have hSec : Sec7Hyp D 5 H :=
    ⟨Nat.prime_five, by norm_num, hsp, hHc.ne_top, hHM, hrankH⟩
  have hKH : K889 L ω ≤ H := hKX.trans hXH
  have hKM : K889 L ω ≤ D.M := (r889_K889_le_left L ω).trans (r889_le_M hS)
  obtain ⟨hodd, -, -⟩ := h71 5 H hSec
  have hK : ¬ 2 ∣ Nat.card (PPrimeCoreIn 5 H) := by
    intro h
    have := Nat.odd_iff.mp hodd
    omega
  obtain ⟨hFstar, hlist⟩ := h72 5 H hSec
  have hNstrong : IsStronglyPEmbedded 5 (ImageModK 5 H (H ⊓ D.M)) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6.R869S.isStronglyPEmbedded_map_quotient_pPrimeCore
      Nat.prime_five hsp hHM hrankH
  have hnot5K : ¬ 5 ∣ Nat.card (CFSG.pPrimeCore 5 ↥H) :=
    (Nat.prime_five.coprime_iff_not_dvd).mp
      (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := 5))
  have hrk' : 1 < CFSG.Open.pRank 5 (ImageModK 5 H (H ⊓ D.M)) := by
    have h1 : CFSG.Open.pRank 5 (ImageModK 5 H (H ⊓ D.M)) =
        CFSG.Open.pRank 5 ((H ⊓ D.M).subgroupOf H) :=
      CFSG.pRank_map_eq_of_not_dvd_card_ker (QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H))
        (QuotientGroup.mk'_surjective _) Nat.prime_five
        (by rw [QuotientGroup.ker_mk']; exact hnot5K) ((H ⊓ D.M).subgroupOf H)
    have h2 : CFSG.Open.pRank 5 ((H ⊓ D.M).subgroupOf H) = CFSG.Open.pRank 5 (H ⊓ D.M) :=
      r889_pRank_subgroupOf_eq inf_le_left
    omega
  refine hAlt6 (QuotK7 5 H) (ImageModK 5 H (Opp 5 H)) (ImageModK 5 H (H ⊓ D.M))
    r889_imageModK_opp_normal hFstar ?_ hNstrong hrk'
    (r889_alt6_section_of_le hKM hKH (hFacts L P ω hω).alt6 hK)
  rcases hlist with h | h | ⟨h3, -⟩ | ⟨-, h | h | h | h⟩ | ⟨h11, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · omega
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
