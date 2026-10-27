module

public import CFSG.Quasithin.H13.L32AL2p
public import CFSG.Quasithin.H13.L32AL2m

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V K H : Subgroup G}

theorem exists_topW_of_le (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    {W' : Subgroup G} (hV₁W : fsuV1 T V ≤ W') (hWU : W' < conjClosure V H)
    (hHW : H ≤ Subgroup.normalizer (W' : Set G)) :
    ∃ W : Subgroup G, W' ≤ W ∧ TopW T L V H W := by
  classical
  set 𝒮 : Set (Subgroup G) := {W | W' ≤ W ∧ W < conjClosure V H ∧
    H ≤ Subgroup.normalizer (W : Set G)} with h𝒮
  obtain ⟨W, hW⟩ := 𝒮.toFinite.exists_maximal ⟨W', le_rfl, hWU, hHW⟩
  refine ⟨W, hW.1.1, S, hF, hV₁W.trans hW.1.1, hW.1.2.1, hW.1.2.2, fun W₂ hWW₂ hW₂U hHW₂ => ?_⟩
  by_cases h : W₂ = conjClosure V H
  · exact Or.inr h
  · left
    exact (hW.2 ⟨hW.1.1.trans hWW₂, lt_of_le_of_ne hW₂U h, hHW₂⟩ hWW₂).antisymm hWW₂

theorem L2Red.irred (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6) (h33 : Lemma14_7_33)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) (hcase : L2CaseOne G T L V) {W' : Subgroup G}
    (hV₁W : fsuV1 T V ≤ W') (hWU : W' ≤ conjClosure V (A6.g1 T V))
    (hHW : A6.g1 T V ≤ Subgroup.normalizer (W' : Set G)) :
    W' = fsuV1 T V ∨ W' = conjClosure V (A6.g1 T V) := by
  by_cases hU : W' = conjClosure V (A6.g1 T V)
  · exact Or.inr hU
  left
  have : IsMulCommutative ↥(conjClosure V (A6.g1 T V)) := hF.F911_3.1
  obtain ⟨W, hW'W, hW⟩ := exists_topW_of_le R.S hF hV₁W (lt_of_le_of_ne hWU hU) hHW
  obtain ⟨t₀, C⟩ := exists_ctxL2_of_red hA37 hA38 R
  have X : TopCtx T L V K W t₀ := ⟨R, C, hW⟩
  obtain ⟨F, _, _, π, β, Y⟩ :=
    X.exists_model hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334
  have Wd := Y.wrData hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
  obtain ⟨-, γ, γ', g, s, hcard, hH2, -, -⟩ := hcase
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)), x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hall y hy)
    rw [this, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨t, htU, rfl⟩ := mem_modO2Image'.mp hx
  have ht2 : t * t = 1 := Subtype.ext (by
    have := hF.isElemAbelian_Uγ.2 _ htU
    simpa [pow_two] using this)
  have ht1 : X.top.act t ≠ 1 := fun h1 => hx1 (by
    apply X.actDot_injective hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
    rw [X.actDot_mk t, h1, map_one])
  have hidx := relIndex_centralizer_le hH2 hF.card_A₁ htU
  have hWV := X.eq_fsuV1 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 Wd ht2 ht1 hidx
  exact le_antisymm (hW'W.trans hWV.le) hV₁W

end CFSG.Quasithin.H13.L32A.L2
