module

public import CFSG.Quasithin.MS93.ASC134
public import CFSG.Quasithin.MS93.ASC134Ord
public import CFSG.Quasithin.MS93.Burnside.D468Base
public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc
public import CFSG.Quasithin.MS93.MS93FrontierDeep
public import CFSG.Quasithin.MS93.S4XKey

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

theorem burnsideMS93R_not_le_of_isSum {G : Type} [Group G] {A V Z : Subgroup G} {ι : Type}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {F : Type} [Field F]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)} {α : ↥A →* ↥Γ} {dual : Bool} {k : ℕ}
    (hk : 0 < k) (h : IsSumOfNaturalModulesVia A V Z α dual k) : ¬ V ≤ Z := by
  intro hVZ
  obtain ⟨-, -, β, hβ, hker, -⟩ := h
  obtain ⟨v, hv⟩ := hβ (Multiplicative.ofAdd (fun _ _ => (1 : F)))
  have hv1 : v ∈ β.ker := by
    rw [hker]
    exact Subgroup.mem_subgroupOf.mpr (hVZ v.2)
  rw [MonoidHom.mem_ker] at hv1
  rw [hv1] at hv
  have h01 := congrArg
    (fun y : Multiplicative (Fin k → ι → F) => Multiplicative.toAdd y ⟨0, hk⟩
      (Classical.arbitrary ι)) hv
  simp at h01

theorem burnsideMS93R_card_of_isE2 {V : Type} [Group V] {m : ℕ} (h : IsE2 m V) :
    Nat.card V = 2 ^ m := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  simp

section Main

set_option linter.unusedSectionVars false


variable {G : Type} [Group G] [Finite G]

theorem burnsideMS93R_four_lt_and_sl3U
    {G₀ R K M T : Subgroup G}
    (h : PUHyp M T K) (hmin : PUMin M T K) (hV : Vq M K = c134Q G₀ K)
    (h4 : IsC134Case4Corr G₀ R K) :
    4 < critDist (puAmalgam h.le) ∧ IsSL3U M T K := by
  obtain ⟨⟨n, F, _, _, α, hF, -, hE, hZ, -, hU, hΦ, -, -⟩, -⟩ := h4
  have hpos := h.critDist_pos
  obtain ⟨m, hm⟩ := h.critDist_even
  have hb2 : critDist (puAmalgam h.le) ≠ 2 := by
    intro hb
    obtain ⟨h36a, -⟩ := s36_of_g2 s38G2_holds G M T K h hb
    have hle : frattiniIn (Vq M K) ≤ CFSG.Quasithin.centerOf (Vq M K) := by
      rcases h36a with hVU | hD
      · have hcomm : ∀ x ∈ Vq M K, ∀ y ∈ Vq M K, x * y = y * x := by
          rw [hVU]
          exact isMulCommutative_subgroup_iff.mp h.isElemAbelian_Uq.1
        have hc : CFSG.Quasithin.centerOf (Vq M K) = Vq M K :=
          inf_eq_left.mpr fun x hx =>
            Subgroup.mem_centralizer_iff.mpr fun y hy => hcomm y hy x hx
        rw [hc]
        exact Subgroup.map_subtype_le _
      · rw [hD.1]
        exact bot_le
    rw [hV] at hle
    exact burnsideMS93R_not_le_of_isSum one_pos hΦ hle
  have hb2' : 2 < critDist (puAmalgam h.le) := by omega
  have hSL : IsSL3U M T K := by
    rcases s38_of_g2 s38G2_holds G M T K h hb2' with hSL | hSp
    · exact hSL
    · exfalso
      by_cases hF : IsSp4Full M T K
      · exact s512_holds G M T K h hmin hb2' hF
      · exact S4L.burnsideSp4H_noNonlinSp G M T K h hmin hb2' hSp hF
  have hb4 : critDist (puAmalgam h.le) ≠ 4 := by
    intro hb
    have hfull := S4L.Core.sl3Full_of_b4 ms14AS_holds sqtkQuot_holds h hmin hSL
      (centHyp_of_S32 s32_holds h) hb
    obtain ⟨n', F', _, _, α', -, hα', hZnat, -, -⟩ :=
      CFSG.Yardstones.M71b2fd3d34b9.burnsideD468_s46_of_base s32_holds s43_holds ms14AS_holds
        sqtkQuot_holds G M T K h hmin hb hfull
    rw [hV] at hZnat
    have hYW : c134CQ G₀ K ≤ CFSG.Quasithin.centerOf (c134Q G₀ K) := by
      rw [hZ]
      exact le_sup_left
    have hKY : K ≤ Subgroup.normalizer (c134CQ G₀ K : Set G) := by
      refine le_normalizer_inf ?_ (le_normalizer_centralizer Subgroup.le_normalizer)
      rw [← hV]
      exact h.L_le.trans (le_normalizer_Vq h.le_normalizer)
    rcases eq_or_eq_of_natural hα' statedSL3_transitive hZnat bot_le hYW hKY with hY | hY
    · have hc := burnsideMS93R_card_of_isE2 hE
      rw [hY, Subgroup.card_bot] at hc
      have hn := one_le_of_card_eq_two_pow hF
      have : 2 ≤ 2 ^ (2 * n) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (2 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · have hbot : ⁅CFSG.Quasithin.centerOf (c134Q G₀ K), K⁆ ≤ ⊥ := by
        rw [← hY, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact inf_le_right
      exact burnsideMS93R_not_le_of_isSum one_pos hU hbot
  exact ⟨by omega, hSL⟩

theorem burnsideMS93R_four_lt_and_full
    {G₀ R K M T : Subgroup G}
    (h : PUHyp M T K) (hmin : PUMin M T K) (hV : Vq M K = c134Q G₀ K)
    (h4 : IsC134Case4Corr G₀ R K) (hlin : S4L.NoNonlinSLGt4 ∨ T ≤ K ⊔ pCoreOf 2 M) :
    4 < critDist (puAmalgam h.le) ∧ IsSL3Full M T K := by
  obtain ⟨hb, hSL⟩ := burnsideMS93R_four_lt_and_sl3U h hmin hV h4
  refine ⟨hb, ?_⟩
  rcases hlin with hsl | hlin
  · by_contra hF
    exact hsl G M T K h hmin hb hSL hF
  · exact S34D.sl3Full_of_le_sup h hSL hlin

end Main

end CFSG.Quasithin.MS93
