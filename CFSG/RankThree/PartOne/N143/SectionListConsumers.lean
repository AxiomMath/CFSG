module

public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.RankThree.PartTwo.Setup

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.ABGLocalTools CFSG.RankThree.PartOne.StrongP

theorem theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt (h : SectionListBound)
    {G : Type} [Group G] [Finite G] (hKP : CFSG.IsKProper G) (he : CFSG.twoLocalOddRank G ≤ 3)
    {p : ℕ} (hp : p.Prime) {a : G} {I : Subgroup G} (hI : I ∈ thetaComponentsAt p a)
    (hItop : I ≠ ⊤) :
    TheoremThreeListHyp ((↥I ⧸ aschbacherSolvableCore p ↥I) ⧸
      Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)) := by
  have hKI : CFSG.IsKGroup ↥I := hKP I hItop
  have heI : CFSG.Assembly.evenRank ↥I ≤ 3 :=
    (CFSG.RankThree.PartTwo.evenRank_subgroup_le I).trans
      ((CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).le.trans he)
  have hq : CFSG.IsQuasisimple (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  exact h.listHyp hKI heI ⊤ hq
    ((QuotientGroup.mk' (aschbacherSolvableCore p ↥I)).comp
      (Subgroup.topEquiv : (⊤ : Subgroup ↥I) ≃* ↥I).toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp
      (Subgroup.topEquiv : (⊤ : Subgroup ↥I) ≃* ↥I).surjective)

@[expose] def KF159List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    E = A → ∀ X ∈ thetaCompE p E,
      Census3.TheoremThreeList ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))

@[expose] def KF159ListFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompE p E,
      Census3.TheoremThreeList ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
        Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X))

theorem theoremThreeListHyp_simpleQuot_of_mem_thetaCompE (h : SectionListBound) {G : Type} [Group G]
    [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h15 : Sec15Hyp G p A c L E)
    {X : Subgroup G} (hX : X ∈ thetaCompE p E) :
    TheoremThreeListHyp ((↥X ⧸ aschbacherSolvableCore p ↥X) ⧸
      Subgroup.center (↥X ⧸ aschbacherSolvableCore p ↥X)) := by
  have h12 := h15.h12
  have hp := h12.prime
  have hsimple : IsSimpleGroup G := h12.setup.1
  have hnonab : ∃ a b : G, a * b ≠ b * a := h12.setup.2.1
  have hKP : IsKProper G := h12.setup.2.2.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h12.setup.2.2.2.2.1.le
  obtain ⟨B, hB, hXB⟩ := hX
  obtain ⟨x, hxB, hx1, hXx⟩ := mem_thetaComponentFamily_iff.1 hXB
  have hXC : X ≤ Subgroup.centralizer ({x} : Set G) := (mem_thetaComponentsAt_iff.1 hXx).1
  have hXtop : X ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab hx1
      (eq_top_iff.2 (htop ▸ hXC))
  exact theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt h hKP hrk3 hp hXx hXtop

theorem kf159List_of_list (h : SectionListBound) : KF159List := by
  intro G _ _ p A c L E h15 hF hout hEA X hX
  exact (theoremThreeListHyp_simpleQuot_of_mem_thetaCompE h h15 hX).onList

theorem kf159ListFive_of_list (h : SectionListBound) : KF159ListFive := by
  intro G _ _ p A c L E h15 hF hout X hX
  exact (theoremThreeListHyp_simpleQuot_of_mem_thetaCompE h h15 hX).onList

theorem ne_top_of_normalizes_two_group {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {S Y : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hYS : Y ≤ Subgroup.normalizer (S : Set G)) : Y ≠ ⊤ := by
  rintro rfl
  have hN : S.Normal := Subgroup.normalizer_eq_top_iff.1 (eq_top_iff.2 hYS)
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal S with h | h
  · exact hS1 h
  · obtain ⟨a, b, hab⟩ := hnab
    have hG : IsPGroup 2 G := by
      subst h
      exact hS2.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G)
    have : Nontrivial G := ⟨a, b, fun hh => hab (by rw [hh])⟩
    have hZ : Nontrivial (Subgroup.center G) := hG.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
    · obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center G)
      exact hz1 (Subtype.ext (by simpa [h0] using hz))
    · exact hab (Subgroup.mem_center_iff.1 (h0 ▸ Subgroup.mem_top b) a)

theorem center_eq_bot_of_simple_nonab {G : Type} [Group G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact (hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)).elim

@[expose] def KF1511List : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ Y : Subgroup G, (∃ S : Subgroup G, S ≠ ⊥ ∧ IsPGroup 2 ↥S ∧ Y ≤ Subgroup.normalizer (S : Set G)) →
      ¬ Y ≤ lieNormalizer p E →
      (∃ Y₀ : Subgroup (↥Y ⧸ pPrimeCore p ↥Y), IsStronglyPEmbedded p Y₀) →
        Census3.TheoremThreeList ↥(generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y))

theorem kf1511List_of_list (h : SectionListBound) : KF1511List := by
  intro G _ _ p A c L E h15 hF hout Y hY hYN hspe
  have h12 := h15.h12
  have hp : p.Prime := h12.prime
  have : Fact p.Prime := ⟨hp⟩
  have hsimple : IsSimpleGroup G := h12.setup.1
  have hnonab : ∃ a b : G, a * b ≠ b * a := h12.setup.2.1
  have hKP : IsKProper G := h12.setup.2.2.1
  have hrk3 : CFSG.twoLocalOddRank G ≤ 3 := h12.setup.2.2.2.2.1.le
  obtain ⟨S, hS1, hS2, hYS⟩ := hY
  have hYtop : Y ≠ ⊤ := ne_top_of_normalizes_two_group hsimple hnonab hS1 hS2 hYS
  have hKY : CFSG.IsKGroup ↥Y := hKP Y hYtop
  have heY : CFSG.Assembly.evenRank ↥Y ≤ 3 :=
    (CFSG.RankThree.PartTwo.evenRank_subgroup_le Y).trans
      ((CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank G).le.trans hrk3)
  obtain ⟨Y₀, hY₀⟩ := hspe
  have hObot : pPrimeCore p (↥Y ⧸ pPrimeCore p ↥Y) = ⊥ :=
    _root_.CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot p
  obtain ⟨hFsimple, hFnonab, -, -⟩ := Sec1511.spe_fstar hp hObot hY₀
  have hq : CFSG.IsQuasisimple ↥(generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hFnonab).1
  let H : Subgroup ↥Y := (generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y)).comap
    (QuotientGroup.mk' (pPrimeCore p ↥Y))
  let π : ↥H →* ↥(generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y)) :=
    (QuotientGroup.mk' (pPrimeCore p ↥Y)).subgroupComap
      (generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y))
  have hπ : Function.Surjective π :=
    MonoidHom.subgroupComap_surjective _ _ (QuotientGroup.mk'_surjective _)
  have hl := (h ↥Y hKY heY H _ hq π hπ).1
  have hZ : Subgroup.center ↥(generalizedFitting (↥Y ⧸ pPrimeCore p ↥Y)) = ⊥ :=
    center_eq_bot_of_simple_nonab hFnonab
  exact Census3.TheoremThreeList.of_mulEquiv
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot) hl

end CFSG.RankThree.PartOne.N143
