module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicM11J1
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicM23
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicJ2HSRu
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicHeJ4
public import CFSG.Quasithin.Background.RonanG72Basic

public section

namespace CFSG.Quasithin.RonanG73

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.Blueprint
open CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]


theorem false_of_sporadic_excluded
    {L Γ A : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hq : CFSG.IsQuasisimple ↥L) (hSQT : CFSG.IsStronglyQuasithin ↥L)
    (s : TauCeti.SporadicName) (hs12 : s ≠ .M12) (hs22 : s ≠ .M22) (hs24 : s ≠ .M24)
    (he : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier s)) : False := by
  obtain ⟨e⟩ := he
  have hodd := CFSG.Quasithin.RonanG72.odd_card_center h.H_irr
  have hnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.1.toNontrivial
  cases s with
  | M11 => exact false_of_M11 h ⟨e⟩
  | M12 => exact hs12 rfl
  | M22 => exact hs22 rfl
  | M23 => exact false_of_M23 h ⟨e⟩
  | M24 => exact hs24 rfl
  | J1 => exact false_of_J1 h ⟨e⟩
  | J2 => exact false_of_J2 h ⟨e⟩
  | J4 => exact false_of_J4 h ⟨e⟩
  | HS => exact false_of_HS h ⟨e⟩
  | He => exact false_of_He h ⟨e⟩
  | Ru => exact false_of_Ru h ⟨e⟩
  | J3 => exact ((CFSG.SectionRank.J3_odd_central_quotient_exclusion hSQT _ le_rfl hodd).false
      e).elim
  | M => exact ((CFSG.SectionRank.M_nontrivial_central_quotient_exclusion hSQT _ le_rfl hnt).false
      e).elim
  | McL => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.McL_elementary_three_rank_four).false e).elim
  | Suz => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Suz_elementary_three_rank_four).false e).elim
  | ONan => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.ON_elementary_three_rank_four).false e).elim
  | Co1 => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Co1_elementary_three_rank_four).false e).elim
  | Co2 => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Co2_elementary_three_rank_four).false e).elim
  | Co3 => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Co3_elementary_three_rank_four).false e).elim
  | Fi22 => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Fi22_elementary_three_rank_four).false e).elim
  | Fi23 => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Fi23_elementary_three_rank_four).false e).elim
  | Fi24Prime => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _
      le_rfl CFSG.SectionRank.Fi24prime_elementary_three_rank_four).false e).elim
  | HN => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.HN_elementary_three_rank_four).false e).elim
  | Ly => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Ly_elementary_three_rank_four).false e).elim
  | Th => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.Th_elementary_three_rank_four).false e).elim
  | B => exact ((CFSG.SectionRank.central_quotient_exclusion_of_three_rank_four hSQT _ le_rfl
      CFSG.SectionRank.B_elementary_three_rank_four).false e).elim

end CFSG.Quasithin.RonanG73
