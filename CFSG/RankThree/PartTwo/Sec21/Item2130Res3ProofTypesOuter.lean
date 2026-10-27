module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofLocal
public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof417
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec13.Item131Transport
import CFSG.RankThree.PartTwo.Sec6.Item612Core
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

namespace Item2130Res3Proof

variable {G : Type} [Group G] [Finite G]

theorem isSLThreePiTheta_of_inducesOuterTheta
    (h47 : Sec4.Item4_7) {A E U L : Subgroup G} {c b : G} {U₀ Y : Subgroup G}
    (hcfg : Config2130 G A E U c L) (hC : Choice2130 A E c L b U₀ Y)
    (hNF : ∀ x ∈ A, ¬ KFacts.InducesStdKind Y x .field ∧
      ¬ KFacts.InducesStdKind Y x .graphField)
    {a : G} (haA : a ∈ A) (ha : Sec4.InducesOuterTheta a Y) : Sec4.IsSLThreePiTheta Y := by
  have hAe : IsElemAbelian 3 A := hcfg.pair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hbA : b ∈ A := hC.b_mem.1
  have hb1 := hC.b_ne_one
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hAe.2 b hbA) hb1
  have hYb : Y ∈ thetaComponentsAt 3 b := lZeroStarAt_subset A b hC.y_mem
  have hG := hcfg.pair.standing.toTheoremFourHyp
  set H := Subgroup.centralizer ({b} : Set G) with hHdef
  have hbH : b ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨hYH, hY'⟩ := mem_thetaComponentsIn_iff.mp hYb
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr (hcomm b hbA a haA).symm
  have hH : SectionFourHyp H := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG hb1)
  have h3H : 3 ∣ Nat.card (Subgroup.center H) := by
    have hz : (⟨b, hbH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    have hord : orderOf (⟨⟨b, hbH⟩, hz⟩ : Subgroup.center H) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hb3]
    exact hord ▸ orderOf_dvd_natCard _
  set Y' := Y.subgroupOf H with hY'def
  set eθ : Y' ⧸ aschbacherSolvableCore 3 Y' ≃* Y ⧸ aschbacherSolvableCore 3 Y :=
    Sec4.thetaQuotCongr (Subgroup.subgroupOfEquivOfLe hYH) with heθ
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact KFacts.not_inducesOuterTheta_one Y ha
  have ha3 : orderOf (⟨a, haH⟩ : H) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 a haA) ha1
  have h47' := h47 H hH h3H Y' hY' ⟨a, haH⟩ ha3 (Sec4.inducesOuterTheta_subgroupOf hYH haH ha)
  have hYY : Y'.map H.subtype = Y := by
    rw [hY'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYH]
  have hk : ∀ k : KFacts.AutKind, KFacts.InducesStdKind Y' ⟨a, haH⟩ k →
      KFacts.InducesStdKind Y a k := by
    intro k hk
    have h1 := Sec13.inducesStdKind_sub H Y' hk
    rwa [hYY] at h1
  rcases h47' with ⟨p, e, _, -, -, -, hf⟩ | ⟨p, e, _, -, he, -, hsl, -⟩ | ⟨-, hf⟩ |
      ⟨n, hn, hsl, -⟩ | ⟨n, -, -, hgf, -⟩
  · exact ((hNF a haA).1 (hk _ hf)).elim
  · refine ⟨p, e, inferInstance, he, ?_⟩
    rcases hsl with h | h
    · exact Or.inl (Sec4.Res417.isSLThreePiAt_congr eθ.symm h)
    · exact Or.inr (Sec4.Res417.isoLThreePi_congr eθ.symm h)
  · exact ((hNF a haA).1 (hk _ hf)).elim
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine ⟨2, n, inferInstance, hn, ?_⟩
    rcases hsl with h | h
    · exact Or.inl (Sec4.Res417.isSLThreePiAt_congr eθ.symm h)
    · exact Or.inr (Sec4.Res417.isoLThreePi_congr eθ.symm h)
  · exact ((hNF a haA).2 (hk _ hgf)).elim

end Item2130Res3Proof

end CFSG.RankThree.PartTwo.Sec21
