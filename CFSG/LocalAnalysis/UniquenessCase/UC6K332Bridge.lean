module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.Models.PGL
import CFSG.RankThree.PartTwo.Sec4.RonanK432Transport
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.OddRankOneQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint CFSG.PGLModel
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (GoodRow)

theorem isQuasisimple_open {L : Type} [Group L] (h : CFSG.IsQuasisimple L) :
    CFSG.Open.IsQuasisimple L :=
  ⟨@Group.IsPerfect.commutator_eq_top L _ h.1, h.2.1⟩

theorem nonabelian_of_isQuasisimple {L : Type} [Group L] (h : CFSG.IsQuasisimple L) :
    ∃ a b : L, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem center_eq_bot_of_simple {L : Type} [Group L] (hs : IsSimpleGroup L)
    (hna : ∃ a b : L, a * b ≠ b * a) : Subgroup.center L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center L := by
      rw [h]
      exact Subgroup.mem_top a
    exact absurd ((Subgroup.mem_center_iff.mp ha) b).symm hab

theorem nonempty_quotCenter_mulEquiv {L : Type} [Group L] (h : Subgroup.center L = ⊥) :
    Nonempty (L ⧸ Subgroup.center L ≃* L) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem goodRow_quot_of_simple {L : Type} [Group L] [Finite L] (hs : IsSimpleGroup L)
    (hna : ∃ a b : L, a * b ≠ b * a) (h : GoodRow L) : GoodRow (L ⧸ Subgroup.center L) := by
  obtain ⟨e⟩ := nonempty_quotCenter_mulEquiv (center_eq_bot_of_simple hs hna)
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.GoodRow.of_mulEquiv e.symm h

theorem nonempty_projSL_of_lieModel {S : Type} [Group S] {n p f : ℕ} [Fact p.Prime]
    (h : LieModel S .PSL n p f) : Nonempty (S ≃* projSL n (GaloisField p f)) := by
  exact (CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (h.statedClassicalModel (by decide))
    (statedClassicalModel_of_mulEquiv_projSL h.admissible (MulEquiv.refl _)))

theorem nonempty_projSU_of_lieModel {S : Type} [Group S] {n p f : ℕ} [Fact p.Prime]
    (h : LieModel S .PSU n p f) : Nonempty (S ≃* projSU n p f) := by
  exact (CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (h.statedClassicalModel (by decide))
    (statedClassicalModel_of_mulEquiv_projSU h.admissible (MulEquiv.refl _)))

theorem nonempty_projSp_of_lieModel {S : Type} [Group S] {n p f : ℕ} [Fact p.Prime]
    (h : LieModel S .PSp n p f) : Nonempty (S ≃* projSp n (GaloisField p f)) := by
  exact (CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel
    (h.statedClassicalModel (by decide))
    (statedClassicalModel_of_mulEquiv_projSp h.admissible (MulEquiv.refl _)))

theorem isCatalogGroup_quot {L : Type} [Group L] (hK : CFSG.Open.IsKGroup L)
    (hq : CFSG.IsQuasisimple L) : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) := by
  haveI := hq.2.1
  refine
    CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.isCatalogGroup_of_isKGroup_of_surjective
      hK ⊤ hq.2.2 ((QuotientGroup.mk' (Subgroup.center L)).comp (⊤ : Subgroup L).subtype) ?_
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) x
  exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩

theorem pRank_quot_le_one {L : Type} [Group L] [Finite L]
    (h : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 1) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) ≤ 1 := by
  have h1 : CFSG.pRank 3 L ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact h
  have h2 := CFSG.LocalAnalysis.RankThreeUC.OddRankOneQuotient.pRank_le_one_of_surjective
    Nat.prime_three (by norm_num) h1 (QuotientGroup.mk' (Subgroup.center L))
    (QuotientGroup.mk'_surjective _)
  rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at h2

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route
