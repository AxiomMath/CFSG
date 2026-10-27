module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920Comm
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XChiefY
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920IMNilp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsChiefFactorUnder)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_chief_factor_Y (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    {X Y Z O M : Subgroup G} (hKG : CFSG.Open.IsKGroup ↥(O ⊔ Y)) (hZX : Z ≤ X) (hXY : X ≤ Y)
    (hYX : Y ≤ normalizer (X : Set G)) (hZ3 : Nat.card Z = 3) (hYM : Y ≤ M)
    (hCZ : centralizer (Z : Set G) ≤ M) (hXperf : ⁅X, X⁆ = X)
    (hXgen : ∀ B : Subgroup G, B ≤ X → X ≤ normalizer (B : Set G) → Z ≤ B → B = X)
    (hYO : Y ≤ normalizer (O : Set G)) (hO3 : ¬ 3 ∣ Nat.card O) (hOM : ¬ O ≤ M) :
    ∃ (r : ℕ) (U W : Subgroup G), r.Prime ∧ r ≠ 3 ∧ IsChiefFactorUnder r Y U W ∧ U ≤ O ∧
      W ≤ M ∧ U ⊓ M ≤ W ∧ (∀ u ∈ U, (∀ x ∈ Z, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W) ∧
      ∀ V : Subgroup G, V ≤ O → Y ≤ normalizer (V : Set G) → ¬ V ≤ M →
        Nat.card U ≤ Nat.card V := by
  classical
  obtain ⟨V₀, hV₀O, hV₀Y, hV₀M, hV₀min⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F09.exists_minimal_invariant_not_le
      (K := Y) (O := O) (M := M) hYO hOM
  have hKG' : CFSG.Open.IsKGroup ↥(V₀ ⊔ Y) :=
    CFSG.Open.IsKGroup.of_le hKG (sup_le_sup hV₀O le_rfl)
  have hV₀3 : ¬ 3 ∣ Nat.card V₀ := fun h =>
    hO3 (h.trans (Subgroup.card_dvd_of_le hV₀O))
  obtain ⟨r, U, W, hr, hr3, hchief, hUV₀, hWM, hUMW, hfix⟩ :=
    exists_chief_factor_not_le_Y (O := V₀) hSch hKG' hZX hXY hYX hZ3 hYM hCZ hXperf hXgen
      hV₀Y hV₀3 hV₀M
  have hUO : U ≤ O := hUV₀.trans hV₀O
  have hUY : Y ≤ normalizer (U : Set G) := hchief.2.1
  have hUM : ¬ U ≤ M := by
    intro hUM'
    have hUW : U ≤ W := by
      have hinf : U ⊓ M = U := inf_eq_left.mpr hUM'
      rwa [hinf] at hUMW
    exact absurd hUW (not_le_of_gt hchief.1)
  have hcard : Nat.card U = Nat.card V₀ := by
    apply le_antisymm
    · exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hUV₀)
    · exact hV₀min U hUO hUY hUM
  refine ⟨r, U, W, hr, hr3, hchief, hUO, hWM, hUMW, hfix, ?_⟩
  intro V hVO hVY hVM
  rw [hcard]
  exact hV₀min V hVO hVY hVM

theorem commutator_eq_of_minimal_chief_factor {r : ℕ} {Y L U W D₃ M O : Subgroup G}
    (hLY : L ≤ Y) (hYL : Y ≤ normalizer (L : Set G)) (hD₃L : D₃ ≤ L)
    (hUW : IsChiefFactorUnder r Y U W) (hUO : U ≤ O) (hWM : W ≤ M) (hUM : U ⊓ M ≤ W)
    (hfix : ∀ u ∈ U, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hmin : ∀ V : Subgroup G, V ≤ O → Y ≤ normalizer (V : Set G) → ¬ V ≤ M →
      Nat.card U ≤ Nat.card V) : ⁅U, L⁆ = U := by
  classical
  have hYU : Y ≤ normalizer (U : Set G) := hUW.2.1
  have hLU : L ≤ normalizer (U : Set G) := hLY.trans hYU
  have hCU : ⁅U, L⁆ ≤ U := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp hLU
  have hYcomm : Y ≤ normalizer (⁅U, L⁆ : Subgroup G) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYU hy),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hYL hy)]
  have hUMnot : ¬ U ≤ M := by
    intro hUM'
    have hUW' : U ≤ W := by
      have hinf : U ⊓ M = U := inf_eq_left.mpr hUM'
      rwa [hinf] at hUM
    exact absurd hUW' (not_le_of_gt hUW.1)
  have hYsup : Y ≤ normalizer ((⁅U, L⁆ ⊔ W : Subgroup G) : Set G) :=
    (le_inf hYcomm hUW.2.2.1).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  rcases hUW.2.2.2.2.2.2 (⁅U, L⁆ ⊔ W) le_sup_right (sup_le hCU hUW.1.le) hYsup with hW | hU
  · exfalso
    have hCW : ⁅U, L⁆ ≤ W := by rw [← hW]; exact le_sup_left
    have hUW' : U ≤ W := by
      intro u hu
      exact hfix u hu fun x hx =>
        (by
          have hxL : x ∈ L := hD₃L hx
          have hcomm : ⁅x, u⁆ ∈ ⁅U, L⁆ := by
            rw [Subgroup.commutator_comm]
            exact Subgroup.commutator_mem_commutator hxL hu
          simpa [commutatorElement_def] using hCW hcomm)
    exact (not_le_of_gt hUW.1) hUW'
  · have hCM : ¬ ⁅U, L⁆ ≤ M := by
      intro hCM'
      have hUM'' : U ≤ M := by
        rw [← hU]
        exact sup_le hCM' hWM
      exact hUMnot hUM''
    have hminC : Nat.card U ≤ Nat.card (⁅U, L⁆ : Subgroup G) :=
      hmin ⁅U, L⁆ (hCU.trans hUO) hYcomm hCM
    exact Subgroup.eq_of_le_of_card_ge hCU hminC

theorem not_seven_dvd_card_of_minimal_chief_factor {r : ℕ} [Fact r.Prime] (hr7 : r ≠ 7)
    {Y L U W D₃ M O : Subgroup G} (hL : L ∈ calC M) (hL2 : IsL2 (Bar2 L) 3) (hLY : L ≤ Y)
    (hYL : Y ≤ normalizer (L : Set G)) (hD₃L : D₃ ≤ L) (hUW : IsChiefFactorUnder r Y U W)
    (hUO : U ≤ O) (hWM : W ≤ M) (hW3 : ¬ 3 ∣ Nat.card W) (hUM : U ⊓ M ≤ W)
    (hfix : ∀ u ∈ U, (∀ x ∈ D₃, x * u * x⁻¹ * u⁻¹ ∈ W) → u ∈ W)
    (hmin : ∀ V : Subgroup G, V ≤ O → Y ≤ normalizer (V : Set G) → ¬ V ≤ M →
      Nat.card U ≤ Nat.card V) : ¬ 7 ∣ Nat.card U := by
  classical
  have hcomm : ⁅U, L⁆ = U :=
    commutator_eq_of_minimal_chief_factor hLY hYL hD₃L hUW hUO hWM hUM hfix hmin
  have hWinv : W ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.F09.Inv9' M L 3 :=
    ⟨hWM, hW3, hLY.trans hUW.2.2.1⟩
  have hWL : ⁅W, L⁆ ≤ pCoreOf 2 W :=
    commutator_le_pCoreOf_of_mem_inv9' hL hL2 hWinv
  have hT_le_W : pCoreOf 2 W ≤ W := CFSG.LieType.BorelTits.pCoreOf_le 2 W
  have hW_le_U : W ≤ U := hUW.1.le
  have hU_norm_W : U ≤ normalizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hUW.2.2.2.1 x hx y hy
    · intro hy
      have hxinv : x⁻¹ ∈ U := U.inv_mem hx
      have h := hUW.2.2.2.1 x⁻¹ hxinv (x * y * x⁻¹) hy
      have heq : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ = y := by group
      rwa [heq] at h
  have hU_norm_T : U ≤ normalizer (pCoreOf 2 W : Set G) :=
    hU_norm_W.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  have hL_norm_U : L ≤ normalizer (U : Set G) := hLY.trans hUW.2.1
  have hL_norm_W : L ≤ normalizer (W : Set G) := hLY.trans hUW.2.2.1
  have hL_norm_T : L ≤ normalizer (pCoreOf 2 W : Set G) :=
    hL_norm_W.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 W)
  have hpows : ∀ u ∈ U, ∃ k : ℕ, u ^ r ^ k ∈ pCoreOf 2 W :=
    exists_pow_mem_of_commutator_action hT_le_W hW_le_U hU_norm_T hU_norm_W hL_norm_U
      hL_norm_W hL_norm_T hcomm hWL hUW.2.2.2.2.1 hUW.2.2.2.2.2.1
  intro h7
  obtain ⟨u, huord⟩ := exists_prime_orderOf_dvd_card' 7 (hp := ⟨Nat.prime_seven⟩) h7
  obtain ⟨k, hk⟩ := hpows (u : G) u.2
  have hcop7r : (7 : ℕ).Coprime r :=
    (Nat.prime_seven.coprime_iff_not_dvd).mpr fun hdvd =>
      hr7 ((Nat.prime_dvd_prime_iff_eq Nat.prime_seven Fact.out).mp hdvd).symm
  have hcop7rk : (7 : ℕ).Coprime (r ^ k) := hcop7r.pow_right k
  have horder_u : orderOf ((u : G)) = 7 := by
    rw [Subgroup.orderOf_coe u, huord]
  have horder : orderOf ((u : G) ^ (r ^ k)) = 7 := by
    have hcop : (orderOf ((u : G))).Coprime (r ^ k) := by
      rw [horder_u]
      exact hcop7rk
    exact (Nat.Coprime.orderOf_pow hcop).trans horder_u
  obtain ⟨n, hn⟩ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 W).exists_orderOf_eq_pow
      ⟨(u : G) ^ (r ^ k), hk⟩
  have h2 : 2 ^ n = 7 := by
    rw [← hn]
    exact (Subgroup.orderOf_coe ⟨(u : G) ^ (r ^ k), hk⟩).symm.trans horder
  have hdvd : 7 ∣ 2 ^ n := by rw [h2]
  exact absurd (Nat.prime_seven.dvd_of_dvd_pow hdvd) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
