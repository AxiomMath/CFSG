module

public import CFSG.LocalAnalysis.WeakClosure81.W19EBridge
public import CFSG.LocalAnalysis.WeakClosure81.W19K
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries
public import CFSG.LocalAnalysis.WeakClosure81.W19SixSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem twoResidual_le_sup_pCoreOf (c : MinCex193 D V₀ V p X) :
    twoResidual (X ⊔ D.T) ≤ X ⊔ pCoreOf 2 (X ⊔ D.T) := by
  have hN : X ⊔ D.T ≤ normalizer ((X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) :=
    c.le_normalizer_sup_pCoreOf
  have hNH : X ⊔ pCoreOf 2 (X ⊔ D.T) ≤ X ⊔ D.T :=
    sup_le le_sup_left (c.hyp.pCoreOf_le_T.trans le_sup_right)
  refine twoResidual_le_of_isTwoQuotient hNH hN fun y hy => ?_
  have hTN : D.T ≤ normalizer ((X ⊔ pCoreOf 2 (X ⊔ D.T) : Subgroup G) : Set G) :=
    le_sup_right.trans hN
  have hHeq : X ⊔ D.T = D.T ⊔ (X ⊔ pCoreOf 2 (X ⊔ D.T)) :=
    le_antisymm (sup_le (le_sup_left.trans le_sup_right) le_sup_left)
      (sup_le le_sup_right hNH)
  rw [hHeq] at hy
  exact exists_pow_mem_of_mem_sup_pGroup c.hyp.isSylowIn_T.isPGroup hTN hy

theorem mem_gammaSet_one_iff (c : MinCex193 D V₀ V p X) {g : G} {B : Subgroup G} :
    B ∈ E3.gammaSet V 1 (conjSubgroup V g) ↔
      B ≤ conjSubgroup V g ∧ E3.mQuot (conjSubgroup V g) B = 1 := by
  refine ⟨fun ⟨hBA, g', hBg', hm⟩ => ⟨hBA, ?_⟩, fun ⟨hBA, hm⟩ => ⟨hBA, g, hBA, hm⟩⟩
  have h1 := E3.card_eq_two_pow_mul (E3.isPGroup_conjSubgroup c.isPGroup_V g') hBg'
  have h2 := E3.card_eq_two_pow_mul (E3.isPGroup_conjSubgroup c.isPGroup_V g) hBA
  rw [E3.card_conjSubgroup, hm] at h1
  rw [E3.card_conjSubgroup] at h2
  have hpos : 0 < Nat.card B := Nat.card_pos
  have h3 : 2 ^ E3.mQuot (conjSubgroup V g) B * Nat.card B = 2 ^ 1 * Nat.card B := by
    rw [← h1, ← h2]
  exact Nat.pow_right_injective (le_refl 2) (Nat.eq_of_mul_eq_mul_right hpos h3)

theorem X_le_twoResidual (c : MinCex193 D V₀ V p X) : X ≤ twoResidual (X ⊔ D.T) := by
  intro x hx
  obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient (X ⊔ D.T) x (Subgroup.mem_sup_left hx)
  exact E1.mem_of_pow_mem_two_p c.hyp.prime c.hyp.odd (k := 1)
    (by rw [pow_one, c.hyp.exponent x hx]; exact Subgroup.one_mem _) hk

end MinCex193

namespace Hyp197

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X E F : Subgroup G} {g : G}

theorem A_le_H (h : Hyp197 D V X E F g) : conjSubgroup V g ≤ X ⊔ D.T :=
  h.le_T.trans le_sup_right

theorem A_le_normalizer_E (h : Hyp197 D V X E F g) :
    conjSubgroup V g ≤ normalizer (E : Set G) :=
  h.A_le_H.trans h.normalizer_E

theorem A_le_normalizer_F (h : Hyp197 D V X E F g) :
    conjSubgroup V g ≤ normalizer (F : Set G) :=
  h.A_le_H.trans h.normalizer_F

theorem F_lt_E (h : Hyp197 D V X E F g) : F < E := by
  refine lt_of_le_of_ne h.F_le fun hFE => h.comm_ne ?_
  have hC : X ⊔ D.T ≤ centralizerQuot (X ⊔ D.T) E F := by
    intro k hk
    refine ⟨hk, h.normalizer_F hk, fun e he => ?_⟩
    have h1 : k * e * k⁻¹ ∈ F := by
      rw [hFE]
      exact (Subgroup.mem_normalizer_iff.1 (h.normalizer_E hk) e).1 he
    have he' : e ∈ F := by rw [hFE]; exact he
    rw [commutatorElement_def]
    exact F.mul_mem h1 (F.inv_mem he')
  refine le_trans ?_ hC
  refine Subgroup.commutator_le.2 fun x hx a ha => ?_
  have hxH : x ∈ X ⊔ D.T := twoResidual_le _ hx
  rw [commutatorElement_def]
  exact (X ⊔ D.T).mul_mem ((X ⊔ D.T).mul_mem ((X ⊔ D.T).mul_mem hxH (h.A_le_H ha))
    ((X ⊔ D.T).inv_mem hxH)) ((X ⊔ D.T).inv_mem (h.A_le_H ha))

theorem pCoreOf_le_centralizerQuot (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g) :
    pCoreOf 2 (X ⊔ D.T) ≤ centralizerQuot (X ⊔ D.T) E F := by
  obtain ⟨W, _, _, _, ρ, ι, -, -, -, -, -, hker, hO⟩ :=
    exists_rep c.hyp.isSolvable h.E_le h.isElemAbelian h.F_lt_E h.normalizer_E h.normalizer_F
      h.irreducible
  intro n hn
  have hnH : n ∈ X ⊔ D.T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hn
  exact (hker ⟨n, hnH⟩).1 (hO ⟨n, hnH⟩ hn)

theorem not_comm_le_pCoreOf (c : MinCex193 D V₀ V p X) (h : Hyp197 D V X E F g) :
    ¬ ⁅X, conjSubgroup V g⁆ ≤ pCoreOf 2 (X ⊔ D.T) := by
  intro hXA
  apply h.comm_ne
  have hXn : X ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hAn : conjSubgroup V g ≤ normalizer (pCoreOf 2 (X ⊔ D.T) : Set G) :=
    h.A_le_H.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  calc ⁅twoResidual (X ⊔ D.T), conjSubgroup V g⁆
      ≤ ⁅X ⊔ pCoreOf 2 (X ⊔ D.T), conjSubgroup V g⁆ :=
        Subgroup.commutator_mono c.twoResidual_le_sup_pCoreOf le_rfl
    _ = ⁅conjSubgroup V g, X ⊔ pCoreOf 2 (X ⊔ D.T)⁆ := Subgroup.commutator_comm _ _
    _ ≤ ⁅conjSubgroup V g, X⁆ ⊔ pCoreOf 2 (X ⊔ D.T) := E1.commutator_sup_le hAn hXn
    _ ≤ pCoreOf 2 (X ⊔ D.T) :=
        sup_le (by rw [Subgroup.commutator_comm]; exact hXA) le_rfl
    _ ≤ centralizerQuot (X ⊔ D.T) E F := h.pCoreOf_le_centralizerQuot c

theorem good (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) (h : Hyp197 D V X E F g) :
    g ∉ D.M ∧ V₀ ≤ conjSubgroup D.M g := by
  obtain ⟨K, hK⟩ := c.exists_conf196 h.le_T (h.not_comm_le_pCoreOf c)
  exact ⟨hK.g_not_mem_M c, c.V₀_le_V.trans (hK.V_le_conj_M c h162).1⟩

theorem X_inf_conj_M (c : MinCex193 D V₀ V p X) (h162 : W3Thm162Gt2 G) (h : Hyp197 D V X E F g) :
    X ⊓ conjSubgroup D.M g = ⊥ :=
  c.hyp.inf_eq_bot g (h.good c h162).1 (h.good c h162).2

theorem normalizer_centralizerQuot (h : Hyp197 D V X E F g) :
    X ⊔ D.T ≤ normalizer (centralizerQuot (X ⊔ D.T) E F : Set G) := by
  intro k hk
  refine E1.mem_normalizer_of_conj_mem fun c hc => ?_
  obtain ⟨hcH, hcF, hce⟩ := hc
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hcH) (Subgroup.inv_mem _ hk),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (h.normalizer_F hk) hcF)
      (Subgroup.inv_mem _ (h.normalizer_F hk)), fun e he => ?_⟩
  have hke : k⁻¹ * e * k ∈ E := by
    have := (Subgroup.mem_normalizer_iff.1 (h.normalizer_E (Subgroup.inv_mem _ hk)) e).1 he
    simpa using this
  have h1 := hce _ hke
  have eq : ⁅k * c * k⁻¹, e⁆ = k * ⁅c, k⁻¹ * e * k⁆ * k⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [eq]
  exact (Subgroup.mem_normalizer_iff.1 (h.normalizer_F hk) _).1 h1

end Hyp197

end CFSG.LocalAnalysis.WeakClosure81

end
