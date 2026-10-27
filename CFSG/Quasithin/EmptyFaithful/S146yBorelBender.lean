module

public import CFSG.Quasithin.EmptyFaithful.S146yBorelBase
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.TheoremC.BorelHold
public import CFSG.Timmesfeld.Bridge.NoPolarConnected
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.C25RankOne
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalBender

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.ProperTwoGeneratedCore.TheoremC

namespace CFSG.Quasithin

theorem borelRigid_of_benderBorelFacts {Y : Type} [Group Y]
    (h : ∀ Q : Sylow 2 Y, BenderBorelFacts Y (Q : Subgroup Y)) : BorelRigid Y := by
  intro S hS β _ hβB
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hS
  have facts := h Q
  have hQfix : ∀ q ∈ (Q : Subgroup Y), β q = q := fun q hq => hβB q (Subgroup.le_normalizer hq)
  obtain ⟨r, hrQ, hr⟩ := facts.aut_inner β hQfix
  obtain ⟨D, -, hDN, -, htrans, -⟩ := facts.torus
  have hrc : InCenterOf (Q : Subgroup Y) r := by
    refine ⟨hrQ, fun q hq => ?_⟩
    have h1 := hr q
    rw [hQfix q hq] at h1
    show q * r = r * q
    calc q * r = (r * q * r⁻¹) * r := by rw [← h1]
      _ = r * q := by group
  have hr1 : r = 1 := by
    by_contra hne
    have hsub : {w : Y | InCenterOf (Q : Subgroup Y) w} ⊆ {1, r} := by
      intro w hw
      by_cases hw1 : w = 1
      · simp [hw1]
      · obtain ⟨d, hd, hdw⟩ := htrans w r hw hw1 hrc hne
        have hdd : r * d * r⁻¹ = d := by rw [← hr d]; exact hβB d (hDN hd)
        have hcomm : d * r = r * d := by
          calc d * r = (r * d * r⁻¹) * r := by rw [hdd]
            _ = r * d := by group
        have : w = r := by
          calc w = d * (d⁻¹ * w * d) * d⁻¹ := by group
            _ = d * r * d⁻¹ := by rw [hdw]
            _ = r := by rw [hcomm]; group
        simp [this]
    have hcard := facts.center_card
    have h2 : Set.ncard {w : Y | InCenterOf (Q : Subgroup Y) w} ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite _)).trans
        ((Set.ncard_insert_le (1 : Y) {r}).trans (by simp))
    have h3 : Nat.card {w : Y // InCenterOf (Q : Subgroup Y) w} =
        Set.ncard {w : Y | InCenterOf (Q : Subgroup Y) w} := Nat.card_coe_set_eq _
    omega
  ext y
  simpa [hr1] using hr y

theorem isBenderGroup_of_isBenderOf {n : ℕ} {Y : Type} [Group Y] (h : E2.IsBenderOf n Y) :
    CFSG.BenderSuzuki.IsBenderGroup Y := by
  refine CFSG.Timmesfeld.Bridge.isBenderGroup_of_fusionIsBenderGroup ?_
  obtain ⟨hn, h | h | h⟩ := h
  · exact A5.C25.fusionIsBenderGroup_of_isPSL h
  · exact A5.C25.fusionIsBenderGroup_of_isSz h
  · exact K1.fusionIsBenderGroup_of_stated_psu_three hn h

theorem borelRigid_of_isBenderOf {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    (h : E2.IsBenderOf n Y) : BorelRigid Y :=
  borelRigid_of_benderBorelFacts fun Q => benderBorelFactsHold Y (isBenderGroup_of_isBenderOf h) Q

end CFSG.Quasithin
