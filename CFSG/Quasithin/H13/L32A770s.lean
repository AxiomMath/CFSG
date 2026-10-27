module

public import CFSG.Quasithin.H13.L32A770r
public import CFSG.Quasithin.H13.KGFactF618Big
public import CFSG.Quasithin.H13.L32A770d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem lemma14_7_70_two_of_inputs
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h38 : Lemma14_7_38) (h64 : Remark14_7_64) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (hedge : GoldschmidtEdgeBoundS3) (hF618 : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) (h1434 : Lemma1434One) : Lemma14_7_70_two := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  intro G _ _ T L V h
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) := Setting147.hypF98 S0 h13322 hMod h1222
  have h8le := (h64 G T L V h).2.2.1
  by_contra hgt
  push Not at hgt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ↥(u0 T V) := (pCoreOf_isPGroup 2 (hz T V)).to_le
    ((centralizerMod_le_left _ _ _).trans
      (by rw [fsuU_eq_conjClosure_hz hMod h]; exact hF.conjClosure_Vp_le_pCoreOf))
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h8 : Nat.card ↥(u0 T V) = 8 := by
    rw [hn] at hgt h8le ⊢
    have hn3 : n = 3 := by
      rcases Nat.lt_or_ge n 3 with hl | hl
      · interval_cases n <;> omega
      · rcases Nat.eq_or_lt_of_le hl with he | he
        · exact he.symm
        · have : 2 ^ 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) he
          omega
    rw [hn3]
    norm_num
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', g', k₀, N₀⟩ := exists_not1471 hF s (h38 G T L V (hz T V) S0 γ γ' g s)
  have h2₀ := h69 G T L V h δ δ' g' k₀ N₀
  obtain ⟨k, N, s, hsW, hsQ, hsT⟩ := N₀.exists_central h hMod h63 hF h1222 h1332 h1334 h2₀
  have h2 := h69 G T L V h δ δ' g' k N
  exact N.false_of_card_eight hedge hF618 hBig h1434 h hMod h63 hF h1222 h1332 h1334 h13314 h64
    h68 h69 h2 h8 hsW hsQ hsT

theorem lemma14_7_70_two_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h38 : Lemma14_7_38) (h64 : Remark14_7_64) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (hedge : GoldschmidtEdgeBoundS3) (hF618 : F6.TheoremF618Cat)
    (h1434 : Lemma1434One) : Lemma14_7_70_two :=
  lemma14_7_70_two_of_inputs h1222 h1332 h13314 h63 h38 h64 h68 h69 hedge hF618
    A5.factF618Big_holds h1434

end CFSG.Quasithin.H13.L32A
