module

public import CFSG.Quasithin.H13.L32A770c
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def Lemma14_7_70_two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Hyp147 G T L V →
    Nat.card ↥(L32A.u0 T V) ≤ 4

namespace L32A

theorem lemma14_7_70_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h38 : Lemma14_7_38) (h64 : Remark14_7_64) (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h702 : Lemma14_7_70_two) : Lemma14_7_70 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  intro G _ _ T L V h
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) := Setting147.hypF98 S0 h13322 hMod h1222
  have hcard := h702 G T L V h
  refine ⟨hcard, ?_⟩
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  obtain ⟨γ, γ', g, s⟩ := hF.exists_F8Setup
  obtain ⟨δ, δ', g', k₀, N₀⟩ := exists_not1471 hF s (h38 G T L V (hz T V) S0 γ γ' g s)
  obtain ⟨l, hlL, hlH, hZ⟩ := N₀.exists_choice h hMod h63 hF h1222 h1332 h1334 h68 hV2
    (h69 G T L V h δ δ' g' k₀ N₀)
  obtain ⟨k, N, hZ'⟩ : ∃ k, Not1471 T L V (hz T V) δ δ' g' k ∧
      conjSub ((k : G) * g') (fsuV1 T V) ≤ V₂ ⊔ u0 T V :=
    ⟨_, N₀.mul_left hF hlL hlH, by rw [Subgroup.coe_mul, mul_assoc]; exact hZ⟩
  have h2 := h69 G T L V h δ δ' g' k N
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV1U0 := fsuV1_le_u0 h hMod
  have hp : IsPGroup 2 ↥(u0 T V) := (pCoreOf_isPGroup 2 (hz T V)).to_le
    ((centralizerMod_le_left _ _ _).trans
      (by rw [fsuU_eq_conjClosure_hz hMod h]; exact hF.conjClosure_Vp_le_pCoreOf))
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h2le : 2 ≤ Nat.card ↥(u0 T V) := by
    have := Subgroup.card_le_of_le hV1U0
    rwa [hF.card_V₁] at this
  have hn2 : n ≤ 2 := by
    by_contra hc
    have h8 : 8 ≤ 2 ^ n :=
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have key : conjSub ((k : G) * g') (fsuV1 T V) ≤ V₂ ∧
      ⁅fsuU T V, conjSub ((k : G) * g') (fsuU T V)⁆ ⊔ V = V ⊔ u0 T V := by
    interval_cases n
    · rw [pow_zero] at hn
      omega
    · rw [pow_one] at hn
      exact N.zα_le_of_eq h hMod h63 hF h1222 h1332 h1334
        (Subgroup.eq_of_le_of_card_ge hV1U0 (hn.trans hF.card_V₁.symm).le).symm hV2 hZ' h2
    · exact N.zα_le_of_card_four h hMod h63 hF h1222 h1332 h1334 h13314 h64 h68
        (by rw [hn]; norm_num) hV2 hZ' h2
  obtain ⟨hZV2, hFV⟩ := key
  obtain ⟨h3a, h3b, h3c, hb3, l₀, hl₀, hUα⟩ :=
    N.lemma14_7_70_three_four h hMod h63 hF h1222 h1332 h1334 hV2 h2 hZV2 hFV
  refine ⟨δ, δ', g', k, V₂, N, hV2, ?_, h3a, h3b, h3c, hb3, l₀, hl₀, hUα⟩
  rw [F8.A₁, ← conjSub_mul]
  exact hZV2

end L32A

end CFSG.Quasithin.H13
