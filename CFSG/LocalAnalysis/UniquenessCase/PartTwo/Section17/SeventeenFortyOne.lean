module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeS
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.GL83PartI.I713.Extension
public import CFSG.LocalAnalysis.WeakClosure81.FourteenFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge2
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma84AuxGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

theorem s1741_barSub_opp_eq (D : Data G) {V₀ V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hMs : D.M ≤ stabTil V₀ V) :
    barSub V₀ V hV (Opp 5 D.M) =
      RankThree.PartOne.pElementSubgroup 5 (barSub V₀ V hV D.M) := by
  have hmap : (RankThree.PartOne.pElementSubgroup 5
      (D.M.subgroupOf (stabTil V₀ V))).map (stabTil V₀ V).subtype = Opp 5 D.M := by
    rw [s13_pElementSubgroup_map Nat.prime_five (stabTil V₀ V).subtype
      (D.M.subgroupOf (stabTil V₀ V))]
    rw [Subgroup.map_subgroupOf_eq_of_le hMs]
    rfl
  have hsub : RankThree.PartOne.pElementSubgroup 5 (D.M.subgroupOf (stabTil V₀ V)) =
      (Opp 5 D.M).subgroupOf (stabTil V₀ V) := by
    ext x
    constructor
    · intro hx
      have hx' : (x : G) ∈ (RankThree.PartOne.pElementSubgroup 5
          (D.M.subgroupOf (stabTil V₀ V))).map (stabTil V₀ V).subtype :=
        Subgroup.mem_map_of_mem _ hx
      rwa [hmap] at hx'
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      have hx' : (x : G) ∈ (RankThree.PartOne.pElementSubgroup 5
          (D.M.subgroupOf (stabTil V₀ V))).map (stabTil V₀ V).subtype := by
        rwa [hmap]
      obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx'
      have hyx : y = x := Subtype.ext hxy
      rwa [hyx] at hy
  calc
    barSub V₀ V hV (Opp 5 D.M)
        = (((Opp 5 D.M).subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)) := rfl
    _ = ((RankThree.PartOne.pElementSubgroup 5 (D.M.subgroupOf (stabTil V₀ V))).map
          (actTil V₀ V hV)) := by rw [hsub]
    _ = RankThree.PartOne.pElementSubgroup 5
          ((D.M.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV)) :=
        s13_pElementSubgroup_map Nat.prime_five (actTil V₀ V hV) _
    _ = RankThree.PartOne.pElementSubgroup 5 (barSub V₀ V hV D.M) := rfl

theorem s1741_pRank_five_mbar (D : Data G) {V₀ V : Subgroup G}
    (h17_40 : R17_40At D V₀ V) (hKU : Inputs1719.KU34Data)
    {L : Subgroup G} {n : ℕ} (c : Ctx17_40 D V₀ V L n) :
    CFSG.Open.pRank 5 (Mbar D.M V₀ V c.ctx.hyp125.isElemAbelian) = 2 := by
  have hpf := c.ctx.hyp125.pairFacts
  have hV := hpf.elemAbelian
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have h40L := h17_40 L n c
  have hp5L : CFSG.Open.pRank 5 (barSub V₀ V hV L) = 2 := by
    have h := hKU (↥(barSub V₀ V hV L)) h40L.2.1
    have h' : CFSG.pRank 5 ↥(⊤ : Subgroup ↥(barSub V₀ V hV L)) = 2 := h.2.2.2.1
    rw [CFSG.pRank_congr_of_mulEquiv
      (Subgroup.topEquiv (G := ↥(barSub V₀ V hV L))) 5] at h'
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank 5 (barSub V₀ V hV L)] at h'
  have hEq : RankThree.PartOne.pElementSubgroup 5 (barSub V₀ V hV D.M) =
      barSub V₀ V hV L := by
    rw [← s1741_barSub_opp_eq D hV hMs]
    exact h40L.1.symm
  calc
    CFSG.Open.pRank 5 (Mbar D.M V₀ V hV)
        = CFSG.Open.pRank 5
            (RankThree.PartOne.pElementSubgroup 5 (barSub V₀ V hV D.M)) :=
          (s13_pRank_pElementSubgroup Nat.prime_five _).symm
    _ = CFSG.Open.pRank 5 (barSub V₀ V hV L) := by rw [hEq]
    _ = 2 := hp5L

theorem seventeen_fortyone_one (D : Data G) (V₀ V : Subgroup G)
    (h17_40 : R17_40At D V₀ V)
    (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (hKU : Inputs1719.KU34Data) :
    R17_41_1At D V₀ V := by
  intro L n c
  have hpf := c.ctx.hyp125.pairFacts
  have hV := hpf.elemAbelian
  have h40L := h17_40 L n c
  have hsig : D.sig = {5} := h40L.2.2
  have h5sig : 5 ∈ D.sig := by rw [hsig]; simp
  have h5M : 3 ≤ CFSG.Open.pRank 5 D.M := hSg.three_le 5 h5sig
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hnorm : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
    cTilde_subgroupOf_normal hV hpf.le_normalizer hpf.le_normalizer₀
  haveI : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := hnorm
  have hp5Mbar : CFSG.Open.pRank 5
      (Mbar D.M V₀ V hV) = 2 := s1741_pRank_five_mbar D h17_40 hKU c
  have hp5bar11 : CFSG.Open.pRank 5
      (⊤ : Subgroup (F11.MBar11 D.M V₀ V)) = 2 := by
    rw [s15_Three_pRank_MBar11 hV hMs 5,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, hp5Mbar]
  have hext := GL83.I713.pRank_top_le_add_pRank_quotient (p := 5) Nat.prime_five
    ((F11.CTilde D.M V₀ V).subgroupOf D.M)
  have hext' : CFSG.Open.pRank 5 D.M ≤
      CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) + 2 := by
    have h := hext
    rw [hp5bar11] at h
    have hN : CFSG.Open.pRank 5 ((F11.CTilde D.M V₀ V).subgroupOf D.M) =
        CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) := by
      calc
        CFSG.Open.pRank 5 ((F11.CTilde D.M V₀ V).subgroupOf D.M)
            = CFSG.pRank 5 ↥((F11.CTilde D.M V₀ V).subgroupOf D.M) :=
              (CFSG.SectionRank.pRank_coe_eq_openPRank 5 _).symm
        _ = CFSG.pRank 5 ↥(F11.CTilde D.M V₀ V) :=
              CFSG.pRank_congr_of_mulEquiv
                (Subgroup.subgroupOfEquivOfLe (cTilde_le_M D.M V₀ V)) 5
        _ = CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) :=
              CFSG.SectionRank.pRank_coe_eq_openPRank 5 _
    rw [hN] at h
    rwa [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup D.M] at h
  have hC : 1 ≤ CFSG.Open.pRank 5 (F11.CTilde D.M V₀ V) := by omega
  have hdvd : 5 ∣ Nat.card (F11.CTilde D.M V₀ V) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.dvd_card_of_one_le_pRank
      Nat.prime_five hC
  have hpi : 5 ∈ piSet (F11.CTilde D.M V₀ V) := ⟨Nat.prime_five, hdvd⟩
  have hCeq : F11.CTilde D.M V₀ V = D.M ⊓ centralizer (V : Set G) := by
    rw [c.v0]
    exact UC22.cTilde_bot D.M V
  rw [hCeq] at hpi
  exact hpi

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
