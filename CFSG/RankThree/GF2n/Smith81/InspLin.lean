module

public import CFSG.RankThree.GF2n.Smith81.LinLane
public import CFSG.RankThree.GF2n.Smith81.InspKStatements
public import CFSG.RankThree.GF2n.Smith81.InspKFacts
import CFSG.RankThree.GF2n.Smith81.LinInspectData
import CFSG.RankThree.GF2n.Smith81.InspLinLocal
import CFSG.RankThree.GF2n.Smith81.TiBridge
import CFSG.RankThree.GF2n.Smith81.InspLinCore

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
  CFSG.RankThree.GF2n.Stroth80 CFSG.Timmesfeld
open CFSG.SeitzReduction.F4Pilot (ordSL)

theorem linInspect_of (hK1 : K1NSLStatement) (hK2L : K2PSLStatement2) (hK2S : K2PSpStatement2)
    (hKCO : KCOmegaStatement2) : LinInspectStatement := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn h3 z hz hz1 hroot hconj _
  classical
  have H := hc.hyp
  obtain ⟨f, hf, hf2, hHyp, hl, hcardroot, -, hpow, -⟩ :=
    linInspect_data hc hS (by omega) h3 hz hz1 hroot hconj
  have hw : Nat.card Q = Nat.card Z ^ (2 * n + 1) := hS.width H
  rcases rootOutcome_of_K1NSL hK1 hHyp hl with ⟨t, k, f', -, htag, hL, hroot'⟩ | hU
  · have hff : f' = f := by
      have h1 := hroot' (selfIn z) (IsConj.refl z)
      rw [hcardroot] at h1
      exact (Nat.pow_right_injective (le_refl 2) h1).symm
    rw [hff] at htag hL hroot'
    have hQ : (2 ^ f) ^ (2 * n + 1) ≤ Nat.card (pCoreOf 2 (Subgroup.centralizer
        ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G))))) := by
      have h1 := card_Q_le_pCoreOf H hz hz1
      rwa [hw, hf] at h1
    have hP : (2 ^ f) ^ (2 * n + 1) * ordSL n (2 ^ f) ∣ Nat.card (Subgroup.centralizer
        ({selfIn z} : Set ↥(Subgroup.normalClosure ({z} : Set G)))) := by
      have h1 := card_Lgen_dvd_centralizer hc hz hz1
      rwa [card_Lgen_eq hS (by omega), hw, hf] at h1
    have hup : (Nat.card ↥(Subgroup.normalClosure ({z} : Set G))).factorization 2 ≤
        f * (2 * n + 1) + f * (n * (n - 1) / 2) + 2 * f.factorization 2 + 2 :=
      le_trans ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card _) 2) (factorization_card_le_lin hc hS (by omega) hf)
    obtain ⟨rfl, rfl⟩ :=
      linCore hK2L hK2S hKCO hHyp hf2 htag hL hroot' hn (IsConj.refl z) hQ hP hup
    exact ⟨f, hf, hL⟩
  · exfalso
    have h5 := factorization_psu_three_three hU
    have hle := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hpow
    rw [h5] at hle
    nlinarith

end CFSG.RankThree.GF2n.Smith81.Insp
