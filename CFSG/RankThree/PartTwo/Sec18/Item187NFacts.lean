module

public import CFSG.RankThree.PartTwo.Sec18.Item187NQuot
import CFSG.RankThree.PartTwo.Sec18.Item187NLayer
public import CFSG.RankThree.PartTwo.Sec18.Item187F0Basic
import CFSG.RankThree.PartTwo.Sec18.Item187Syl
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item187Frattini
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartTwo.Sec16.Item167Proof

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)

section Facts

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.isSylowOf_S (h186 : Item186H) (hX : MinCex A M H c X) :
    IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X :=
  isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
theorem MinCex.inf_centralizer_pCoreOf_M_le (h186 : Item186H) (hX : MinCex A M H c X)
    {Kt : Subgroup G} (hKt : Kt ≤ X) :
    Kt ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M :=
  (inf_le_inf_right _ (hKt.trans hX.le_M)).trans
    (hX.sec18H.charTwoType M (mem_scriptM_iff.mp hX.sec18H.mem_scriptM).1.1)
theorem MinCex.A_le_M (hX : MinCex A M H c X) : A ≤ M :=
  (isE27_of_mem_partTwoE hX.sec18H.mem_partTwoE).le_gamma.trans
    (SetLike.coe_subset_coe.mp (mem_scriptM_iff.mp hX.sec18H.mem_scriptM).2)
theorem MinCex.c_mem_A (hX : MinCex A M H c X) : c ∈ A :=
  (mem_and_commutator_mem_of_sec18H hX.sec18H).1
theorem MinCex.c_mem_normalizer (hX : MinCex A M H c X) :
    c ∈ Subgroup.normalizer (X : Set G) :=
  hX.le_normalizer (Subgroup.mem_sup_left hX.c_mem_A)
theorem MinCex.c_pow_three (hX : MinCex A M H c X) : c ^ 3 = 1 :=
  pow_three_eq_one_of_sec18H hX.sec18H
theorem MinCex.ne_top (hX : MinCex A M H c X) : X ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hX.sec18H.isSimpleGroup
  obtain ⟨P, hP1, hP2, hMP⟩ := (mem_scriptM_iff.mp hX.sec18H.mem_scriptM).1.1
  refine normalizer_ne_top_of_isPGroup_two hX.sec18H.nonabelian hP2 hP1 ?_
  rw [← hMP]
  exact top_le_iff.mp (htop ▸ hX.le_M)
theorem MinCex.isKGroup (hX : MinCex A M H c X) : CFSG.IsKGroup ↥X :=
  (hX.sec18H.toTheoremFourHyp.sectionFourHyp hX.ne_top).kGroup
theorem MinCex.isKGroup_Y (hX : MinCex A M H c X) : CFSG.IsKGroup (NSolY X) :=
  CFSG.RankThree.PartOne.EmbeddingTransport.isKGroup_quotient hX.isKGroup _
theorem MinCex.not_three_dvd_Y (hX : MinCex A M H c X) : ¬ 3 ∣ Nat.card (NSolY X) := fun h =>
  hX.not_three_dvd (h.trans (Subgroup.card_quotient_dvd_card _))
theorem MinCex.rank_Y (hX : MinCex A M H c X) :
    ∀ r : ℕ, r.Prime → 3 < r → CFSG.Open.pRank r (⊤ : Subgroup (NSolY X)) ≤ 2 := by
  intro r hr hr3
  obtain ⟨P, hP1, hP2, hMP⟩ := (mem_scriptM_iff.mp hX.sec18H.mem_scriptM).1.1
  exact Sec16.pRank_quot_pCore_two_le hX.sec18H.toTheoremFourHyp hP1 hP2 (hMP ▸ hX.le_M) hr hr3

private theorem nsolMk_surjective_of_card (X : Subgroup G) : Function.Surjective (nsolMk X) := by
  have hker : (nsolMk X).ker = CFSG.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, nsolMk_eq_one_iff, pCoreOf_eq_map_pCore]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hcard : Nat.card (nsolMk X).range = Nat.card (NSolY X) := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (nsolMk X)).toEquiv]
    exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv
  have hrange : (nsolMk X).range = ⊤ := (Subgroup.card_eq_iff_eq_top _).mp hcard
  intro y
  have hy : y ∈ (nsolMk X).range := by
    rw [hrange]
    exact Subgroup.mem_top y
  exact MonoidHom.mem_range.mp hy

theorem MinCex.layer_sup_sylowImage_eq_top (h186 : Item186H) (hX : MinCex A M H c X)
    (hl : layer (NSolY X) ≠ ⊥) :
    layer (NSolY X) ⊔ sylowImage X (CFSG.Open.pCoreOf 2 (H ⊓ M)) = ⊤ := by
  have hS : IsSylowOf 2 (CFSG.Open.pCoreOf 2 (H ⊓ M)) X := hX.isSylowOf_S h186
  haveI := CFSG.LocalCores.layer_characteristic (G := NSolY X)
  haveI : (layer (NSolY X)).Normal := inferInstance
  have hVX : nsolPre X (layer (NSolY X)) ≤ X := nsolPre_le X (layer (NSolY X))
  have hXV : X ≤ Subgroup.normalizer (nsolPre X (layer (NSolY X)) : Set G) :=
    le_normalizer_nsolPre X (layer (NSolY X))
  have hAV : A ≤ Subgroup.normalizer (nsolPre X (layer (NSolY X)) : Set G) :=
    le_normalizer_nsolPre_of_characteristic X (layer (NSolY X))
      (fun a ha => hX.le_normalizer (Subgroup.mem_sup_left ha))
  rcases hX.sup_eq_or_inf_le hS hVX hXV hAV with h | h
  ·
    have hle : X ≤ nsolPre X
        (layer (NSolY X) ⊔ sylowImage X (CFSG.Open.pCoreOf 2 (H ⊓ M))) := by
      refine h.symm.le.trans (sup_le ?_ ?_)
      · intro g hg
        obtain ⟨hgX, hgE⟩ := mem_nsolPre.mp hg
        exact mem_nsolPre.mpr ⟨hgX, Subgroup.mem_sup_left hgE⟩
      · intro s hs
        have hsX : s ∈ X := hX.pCoreOf_le hs
        have hmem : nsolMk X ⟨s, hsX⟩ ∈ sylowImage X (CFSG.Open.pCoreOf 2 (H ⊓ M)) :=
          mem_sylowImage.mpr ⟨⟨s, hsX⟩, hs, rfl⟩
        exact mem_nsolPre.mpr ⟨hsX, Subgroup.mem_sup_right hmem⟩
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := nsolMk_surjective_of_card X y
    obtain ⟨_, hxT⟩ := mem_nsolPre.mp (hle x.2)
    exact hxT
  ·
    exfalso
    apply layer_inf_ne_bot_of_isSylowOf hl (isSylowOf_sylowImage hS)
    rw [Subgroup.eq_bot_iff_forall]
    rintro t ⟨htE, htT⟩
    obtain ⟨s, hsS, rfl⟩ := mem_sylowImage.mp htT
    have hsV : (s : G) ∈ nsolPre X (layer (NSolY X)) := mem_nsolPre.mpr ⟨s.2, htE⟩
    rw [nsolMk_eq_one_iff]
    exact h (Subgroup.mem_inf.mpr ⟨hsV, hsS⟩)

end Facts

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
