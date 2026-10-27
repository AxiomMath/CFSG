module

public import CFSG.RankThree.GF2n.Smith81.InspLinOrder
import CFSG.RankThree.GF2n.Stroth80.Sec1110Core

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG.Open CFSG.RankThree.GF2n.Stroth80
open CFSG.SeitzReduction.F4Pilot (ordSL)

section Lin

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem card_Lgen_eq (hS : LinSetup M Q Z B n V₁ V₂) (hn : 1 ≤ n) :
    Nat.card (Lgen M (LB M Q B)) = Nat.card Q * ordSL n (Nat.card Z) := by
  obtain ⟨K, _, _, hKZ, φ, hrange, hker, -⟩ := hS
  have h := Subgroup.card_ker_mul_card_range φ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q_le_Lgen M Q B)).toEquiv, hrange,
    StatedAPI.card_statedSL, LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq hn, hKZ] at h
  exact h.symm

theorem factorization_card_le_lin (hc : Ctx M Q Z B) (hS : LinSetup M Q Z B n V₁ V₂)
    (hn : 3 ≤ n) {f : ℕ} (hf : Nat.card Z = 2 ^ f) :
    (Nat.card G).factorization 2 ≤
      f * (2 * n + 1) + f * (n * (n - 1) / 2) + 2 * f.factorization 2 + 2 := by
  have h2 : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  have h := factorization_card_le_lin_of_centDvdN hc hS (by omega) (by norm_num)
    hS.centDvdN_two hf
  rw [h2] at h
  omega

end Lin

end CFSG.RankThree.GF2n.Smith81.Insp
