module

public import CFSG.Quasithin.Background.RonanG72Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Main
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42RuMain
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.SporadicHeJ4
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.RonanG72

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
  CFSG.Blueprint
open scoped commutatorElement

theorem j4_dim
    (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    (σ : NativeSporadic.Carrier .J4 →* MulAut W) (hσ : Function.Injective σ) :
    2 ^ 110 ≤ Nat.card W := by
  have hF := CFSG.Sporadic.J4.j4Facts
  have es : NativeSporadic.Carrier .J4 ≃* CFSG.Sporadic.J4.J :=
    CFSG.Sporadic.J4.seedEquiv hF.mat
  obtain ⟨h1, -, h3, h4, h5, -, -, -⟩ := CFSG.Sporadic.J4.QT.witness11 hF
  have hcomm : ⁅es.symm CFSG.Sporadic.J4.QT.xE, es.symm CFSG.Sporadic.J4.QT.yE⁆ =
      es.symm CFSG.Sporadic.J4.QT.zE := by
    rw [← map_commutatorElement, commutatorElement_def]
    rfl
  refine dim_of_extraspecial11 (x := es.symm CFSG.Sporadic.J4.QT.xE)
    (y := es.symm CFSG.Sporadic.J4.QT.yE) ?_ ?_ ?_ ?_ W hW σ hσ
  · rw [← map_pow, h1, map_one]
  · rw [hcomm]
    exact fun h => h3 (es.symm.injective (h.trans (map_one es.symm).symm))
  · rw [hcomm]
    exact Commute.map (show Commute CFSG.Sporadic.J4.QT.zE CFSG.Sporadic.J4.QT.xE from h4.symm)
      es.symm
  · rw [hcomm]
    exact Commute.map (show Commute CFSG.Sporadic.J4.QT.zE CFSG.Sporadic.J4.QT.yE from h5.symm)
      es.symm

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem j4_le
    {L : Subgroup (GLV V)} (h : IsSporadic .J4 ↥L) : 110 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨e⟩ := h
  exact le_finrank_of_mulEquiv e (fun W _ _ hW σ hσ => j4_dim W hW σ hσ)

theorem j2_le
    {L : Subgroup (GLV V)} (h : IsSporadic .J2 ↥L) : 12 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨e⟩ := h
  exact le_finrank_of_mulEquiv e (fun W _ _ hW σ hσ =>
    CFSG.QuasithinUnique.Bridge.J2Excl.j2_dim W hW σ hσ)

theorem hs_he_ru_le
    {L : Subgroup (GLV V)}
    (h : IsSporadic .HS ↥L ∨ IsSporadic .He ↥L ∨ IsSporadic .Ru ↥L) :
    20 ≤ Module.finrank (ZMod 2) V := by
  rcases h with h | h | h
  · obtain ⟨e⟩ := h
    exact le_finrank_of_mulEquiv e (fun W _ _ hW σ hσ =>
      CFSG.QuasithinUnique.Bridge.HSExcl.hs_dim W hW σ hσ)
  · obtain ⟨e⟩ := h
    have := le_finrank_of_mulEquiv e (ρ := 21) (fun W _ _ hW σ hσ =>
      CFSG.QuasithinUnique.Setup.X1.he_dim W hW σ hσ)
    omega
  · obtain ⟨e⟩ := h
    have := le_finrank_of_mulEquiv e (ρ := 28) (fun W _ _ hW σ hσ =>
      CFSG.QuasithinUnique.Bridge.RuExcl.ru_dim W hW σ hσ)
    omega

theorem ten_le_of_sporadic
    {L : Subgroup (GLV V)} (hq : CFSG.IsQuasisimple ↥L) (hSQT : CFSG.IsStronglyQuasithin ↥L)
    (hirr : IsIrr L ⊤) (h : ∃ s : TauCeti.SporadicName, IsSporadic s (↥L ⧸ Subgroup.center ↥L)) :
    10 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨s, ⟨e⟩⟩ := h
  have hodd := odd_card_center hirr
  have hnt : Nontrivial (↥L ⧸ Subgroup.center ↥L) := hq.2.1.toNontrivial
  cases s with
  | M11 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .M11) = 7920 from CFSG.Sporadic.Mathieu.card_M11]
      norm_num)
  | M12 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .M12) = 95040 from CFSG.Sporadic.Mathieu.card_M12]
      norm_num)
  | M22 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .M22) = 443520 from
        CFSG.Sporadic.Mathieu.card_M22]
      norm_num)
  | M23 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .M23) = 10200960 from
        CFSG.Sporadic.Schreier.m23_card]
      norm_num)
  | M24 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .M24) = 244823040 from
        CFSG.Sporadic.Mathieu.card_M24]
      norm_num)
  | J1 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .J1) = 175560 from CFSG.Sporadic.J1.card_J1]
      norm_num)
  | J4 => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .J4) = 86775571046077562880 from
        CFSG.Sporadic.J4.card_J4]
      norm_num)
  | HS => exact ten_le_of_eleven_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .HS) = 44352000 from CFSG.Sporadic.HS.card_HS]
      norm_num)
  | Ru =>
    have := twelve_le_of_thirteen_dvd e (by
      rw [show Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 from
        CFSG.Sporadic.Ru.card_Ru]
      norm_num)
    omega
  | J2 =>
    obtain ⟨f⟩ := mulEquiv_of_cover hq hirr e (fun E _ _ _ π hπ hC hodd =>
      CFSG.QuasithinUnique.Bridge.J2Excl.j2_cover E π hπ hC hodd)
    have := j2_le (L := L) ⟨f⟩
    omega
  | He =>
    obtain ⟨f⟩ := mulEquiv_of_cover hq hirr e (fun E _ _ _ π hπ hC hodd =>
      CFSG.QuasithinUnique.Setup.X1.he_cover E π hπ hC hodd)
    have := le_finrank_of_mulEquiv f (ρ := 21) (fun W _ _ hW σ hσ =>
      CFSG.QuasithinUnique.Setup.X1.he_dim W hW σ hσ)
    omega
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

end CFSG.Quasithin.RonanG72
