module

public import CFSG.Quasithin.Vol2.Ch6StatementsSec2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem10

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

theorem stmt6_2_14_of (h6210 : Stmt6_2_10) (h6211 : Stmt6_2_11) (h6212 : Stmt6_2_12) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
      let H := Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
      let U := conjClosure (ch6ZS T L V) H
      ch6ZS T L V < V ⊓ U → V ⊓ U = V ⊓ pCoreOf 2 H ∧ Nat.card ↥(V ⊓ U) = 2 ^ 3 := by
  intro G _ _ T M L V h H U hlt
  obtain ⟨⟨-, hUQ, -⟩, -, -, -, -⟩ := h6210 G T M L V h
  have h2 := h6211 G T M L V h
  obtain ⟨-, -, hCQ⟩ := h6212 G T M L V h
  simp only at h2 hCQ
  rw [hCQ] at h2
  have hV16 : Nat.card V = 16 := by rw [h.natural.card_eq]; norm_num
  have hZS4 : Nat.card (ch6ZS T L V) = 4 := by rw [h.toHyp611Nat.card_ZS]; norm_num
  have hVQ : Nat.card ↥(V ⊓ pCoreOf 2 H) = 8 := by
    have h1 := Subgroup.relIndex_mul_card (V ⊓ pCoreOf 2 H) V
    rw [inf_of_le_left inf_le_left, h2, hV16] at h1
    omega
  have hle : V ⊓ U ≤ V ⊓ pCoreOf 2 H := inf_le_inf_left _ hUQ
  have hZSle : ch6ZS T L V ≤ V ⊓ U := hlt.le
  have hdvd : 4 ∣ Nat.card ↥(V ⊓ U) := hZS4 ▸ Subgroup.card_dvd_of_le hZSle
  have hgt : 4 < Nat.card ↥(V ⊓ U) := hZS4 ▸ Subgroup.card_lt_of_lt hlt
  have hle8 : Nat.card ↥(V ⊓ U) ≤ 8 := hVQ ▸ Subgroup.card_le_of_le hle
  have h8 : Nat.card ↥(V ⊓ U) = 8 := by
    obtain ⟨k, hk⟩ := hdvd
    rcases k with _ | _ | _ | k
    · omega
    · omega
    · omega
    · omega
  refine ⟨Subgroup.eq_of_le_of_card_ge hle (by rw [hVQ, h8]), by rw [h8]; norm_num⟩

end CFSG.Quasithin.H13
