module

public import CFSG.Quasithin.Background.RonanE628Unbarred
import CFSG.Quasithin.Background.VolIE54

public section

namespace CFSG.Quasithin.RonanE628

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E6
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def AlphaBetaNonempty (M V : Subgroup G) : Prop :=
  ∃ U : Subgroup G, U ≤ V ∧
    (¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)) 1 ≤
        M ⊓ Subgroup.centralizer (V : Set G) ∨
      1 < E3.nPrime (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)))

theorem normalizer_ne_top {T M V : Subgroup G} (h : HypE61 T M V) :
    Subgroup.normalizer (V : Set G) ≠ ⊤ := by
  intro htop
  haveI : V.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases h.simple.eq_bot_or_eq_top_of_normal V with hb | ht
  · exact h.ne_bot hb
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    apply hab
    have ha : a ∈ V := by rw [ht]; exact Subgroup.mem_top a
    have hb : b ∈ V := by rw [ht]; exact Subgroup.mem_top b
    exact congrArg Subtype.val (h.isElemAbelian.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem rParam_le_mQuot_bot {T M V : Subgroup G} (h : HypE61 T M V) :
    E3.rParam V ≤ (E3.mQuot V ⊥ : ℕ∞) := by
  refine E3.rParam_le_mQuot bot_le fun hle => normalizer_ne_top h ?_
  refine top_le_iff.1 (le_trans ?_ hle)
  intro g _
  exact Subgroup.mem_centralizer_iff.2 fun x hx => by
    rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]

theorem lt_pRank_of_lt_rParam {T M V X : Subgroup G} (h : HypE61 T M V) (hVX : V ≤ X) {j : ℕ}
    (hr : (j : ℕ∞) < E3.rParam V) : j < CFSG.Open.pRank 2 X := by
  have hjm : j < E3.mQuot V ⊥ := by
    have := lt_of_lt_of_le hr (rParam_le_mQuot_bot h)
    exact_mod_cast this
  have hcard := VolI.E54.card_le_two_pow_pRank_of_le hVX h.isElemAbelian
  have hV2 : Nat.card V = 2 ^ E3.mQuot V ⊥ := by
    have := E3.card_eq_two_pow_mul h.isPGroup_V (bot_le : (⊥ : Subgroup G) ≤ V)
    simpa using this
  have hle : E3.mQuot V ⊥ ≤ CFSG.Open.pRank 2 X :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (hV2 ▸ hcard)
  omega

theorem le_inf_centralizer_of_le {T M V U : Subgroup G} (h : HypE61 T M V) (hUV : U ≤ V) :
    V ≤ M ⊓ Subgroup.centralizer (U : Set G) :=
  le_inf (h.le.trans h.inM.2) fun v hv => Subgroup.mem_centralizer_iff.2 fun u hu =>
    B2F.isElemAbelian_comm h.isElemAbelian (hUV hu) hv

theorem mem_alphaBeta_of_ne_bot (hPT : ParabolicTorusFact) {T M V U : Subgroup G}
    (h : HypE61 T M V) (hr : 1 < E3.rParam V) (hUV : U ≤ V) (hU1 : U ≠ ⊥)
    (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) :
    ¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)) 1 ≤
        M ⊓ Subgroup.centralizer (V : Set G) ∨
      1 < E3.nPrime (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hJ, hn⟩ := hcon
  have hCN : M ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    inf_centralizer_le_normalizer_of_le h hU1 hUV
  have heq : M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G) =
      M ⊓ Subgroup.centralizer (U : Set G) :=
    le_antisymm (fun x hx => ⟨hx.1.1, hx.2⟩) fun x hx => ⟨⟨hx.1, hCN hx⟩, hx.2⟩
  rw [heq] at hJ hn
  have hr1 : ((1 : ℕ) : ℕ∞) < E3.rParam V := by exact_mod_cast hr
  have hJk : H13.thompsonJk 1 (M ⊓ Subgroup.centralizer (U : Set G)) ≤
      M ⊓ Subgroup.centralizer (V : Set G) := by
    rw [← VolI.E54.thompsonJi_eq_thompsonJk
      (lt_pRank_of_lt_rParam h (le_inf_centralizer_of_le h hUV) hr1)]
    exact hJ
  have hCM := e6_27_unbarred hPT h hU1 hUV Nat.one_pos hr1 hJk hn
  exact hCU fun x hx => hCN ⟨hCM hx, hx⟩

theorem bot_mem_alpha_of_not_le {T M V : Subgroup G} (h : HypE61 T M V) (hr : 1 < E3.rParam V)
    (hJ : ¬ thompsonJi T 1 ≤ T ⊓ Subgroup.centralizer (V : Set G)) :
    ¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓
        Subgroup.centralizer ((⊥ : Subgroup G) : Set G)) 1 ≤
      M ⊓ Subgroup.centralizer (V : Set G) := by
  have hC : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    refine top_unique fun g _ => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]
  rw [hC, inf_top_eq]
  intro hle
  apply hJ
  have hTMV : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (V : Set G)) :=
    A4.isSylowTwoOf_mono h.isSylowIn_normalizer (le_inf h.inM.2 h.normal) inf_le_right
  have hr1 : ((1 : ℕ) : ℕ∞) < E3.rParam V := by exact_mod_cast hr
  have hVMV : V ≤ M ⊓ Subgroup.normalizer (V : Set G) :=
    le_inf (h.le.trans h.inM.2) Subgroup.le_normalizer
  rw [VolI.E54.thompsonJi_eq_thompsonJk (lt_pRank_of_lt_rParam h hVMV hr1)] at hle
  rw [VolI.E54.thompsonJi_eq_thompsonJk (lt_pRank_of_lt_rParam h h.le hr1)]
  exact le_inf (E5.thompsonJk_le 1 T)
    (((thompsonJk_le_of_isSylowTwoOf hTMV).trans hle).trans inf_le_right)

theorem alphaBetaNonempty_of_torus {T M V Y B : Subgroup G} (h : HypE61 T M V) {c : ℕ}
    (hc : 2 ≤ c) (hYB : Y ≤ B) (hBM : B ≤ M ⊓ Subgroup.normalizer (V : Set G))
    (hY : IsCyclic ↥Y) (hYc : Nat.card Y = 2 ^ c - 1) (hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBodd : Odd (Nat.card B)) (hBT : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    AlphaBetaNonempty M V := by
  refine ⟨⊥, bot_le, Or.inr ?_⟩
  have hC : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    refine top_unique fun g _ => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    rw [Subgroup.mem_bot.1 (SetLike.mem_coe.1 hx), one_mul, mul_one]
  rw [hC, inf_top_eq]
  have hTMV : IsSylowIn 2 T (M ⊓ Subgroup.normalizer (V : Set G)) :=
    A4.isSylowTwoOf_mono h.isSylowIn_normalizer (le_inf h.inM.2 h.normal) inf_le_right
  exact lt_of_lt_of_le (by omega) (E3.le_nPrime hYB hBM hY hYc hBab hBodd hTMV hBT)

theorem min_le_rParam (hPT : ParabolicTorusFact) {T M V : Subgroup G} (h : HypE61 T M V)
    (hr : 1 < E3.rParam V)
    (hres : (∀ U : Subgroup G, U ≤ V → U ≠ ⊥ →
        Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (V : Set G)) →
      thompsonJi T 1 ≤ T ⊓ Subgroup.centralizer (V : Set G) → AlphaBetaNonempty M V)
    {α β : ℕ∞}
    (hα : α = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧
        ¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)) 1 ≤
          M ⊓ Subgroup.centralizer (V : Set G)}, (E3.mQuot V U : ℕ∞))
    (hβ : β = ⨅ U ∈ {U : Subgroup G | U ≤ V ∧
        1 < E3.nPrime (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G))},
      (E3.mQuot V U : ℕ∞)) :
    min α β ≤ E3.rParam V := by
  have hmem : ∀ U : Subgroup G, U ≤ V →
      (¬ thompsonJi (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G)) 1 ≤
          M ⊓ Subgroup.centralizer (V : Set G) ∨
        1 < E3.nPrime (M ⊓ Subgroup.normalizer (V : Set G) ⊓ Subgroup.centralizer (U : Set G))) →
      min α β ≤ (E3.mQuot V U : ℕ∞) := by
    intro U hUV hU
    rcases hU with hU | hU
    · exact (min_le_left _ _).trans (hα ▸ iInf₂_le U ⟨hUV, hU⟩)
    · exact (min_le_right _ _).trans (hβ ▸ iInf₂_le U ⟨hUV, hU⟩)
  unfold E3.rParam
  refine le_iInf₂ fun U hU => ?_
  by_cases hU0 : U = ⊥
  · subst hU0
    have hmono : ∀ U' : Subgroup G, (E3.mQuot V U' : ℕ∞) ≤ (E3.mQuot V ⊥ : ℕ∞) := fun U' =>
      by exact_mod_cast E3.mQuot_mono bot_le
    by_cases hex : ∃ U₁ : Subgroup G, U₁ ≤ V ∧ U₁ ≠ ⊥ ∧
        ¬ Subgroup.centralizer (U₁ : Set G) ≤ Subgroup.normalizer (V : Set G)
    · obtain ⟨U₁, hU₁V, hU₁0, hU₁C⟩ := hex
      exact (hmem U₁ hU₁V (mem_alphaBeta_of_ne_bot hPT h hr hU₁V hU₁0 hU₁C)).trans (hmono U₁)
    · push Not at hex
      by_cases hJ : thompsonJi T 1 ≤ T ⊓ Subgroup.centralizer (V : Set G)
      · obtain ⟨U₂, hU₂V, hU₂⟩ := hres hex hJ
        exact (hmem U₂ hU₂V hU₂).trans (hmono U₂)
      · exact hmem ⊥ bot_le (Or.inl (bot_mem_alpha_of_not_le h hr hJ))
  · exact hmem U hU.1 (mem_alphaBeta_of_ne_bot hPT h hr hU.1 hU0 hU.2)

end CFSG.Quasithin.RonanE628
