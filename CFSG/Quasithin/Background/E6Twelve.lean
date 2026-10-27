module

public import CFSG.Quasithin.Background.E6ElevenTwo
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch6Inputs

public section

namespace CFSG.Quasithin
namespace E6

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_maximal_centralizer_not_le {V M U : Subgroup G} (hUV : U ≤ V)
    (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    ∃ U₂ : Subgroup G, U ≤ U₂ ∧ U₂ ≤ V ∧ ¬ Subgroup.centralizer (U₂ : Set G) ≤ M ∧
      ∀ W : Subgroup G, U₂ ≤ W → W ≤ V → ¬ Subgroup.centralizer (W : Set G) ≤ M → W = U₂ := by
  classical
  let P : ℕ → Prop := fun n => ∃ W : Subgroup G, U ≤ W ∧ W ≤ V ∧
    ¬ Subgroup.centralizer (W : Set G) ≤ M ∧ Nat.card W = n
  obtain ⟨U₂, hUU₂, hU₂V, hCU₂, hc⟩ :=
    Nat.findGreatest_spec (P := P) (Subgroup.card_le_card_group U) ⟨U, le_rfl, hUV, hCU, rfl⟩
  refine ⟨U₂, hUU₂, hU₂V, hCU₂, fun W hW hWV hCW => ?_⟩
  have h1 : Nat.card W ≤ Nat.findGreatest P (Nat.card G) :=
    Nat.le_findGreatest (Subgroup.card_le_card_group W) ⟨W, hUU₂.trans hW, hWV, hCW, rfl⟩
  exact (Subgroup.eq_of_le_of_card_ge hW (by rw [hc]; exact h1)).symm

omit [Finite G] in
theorem twoPrimeResidual_le_self' (X : Subgroup G) : twoPrimeResidual X ≤ X :=
  iInf₂_le X ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; norm_num⟩

theorem e6_12
    (hComp : E611ComponentCase) {T M V U : Subgroup G} (h : HypE61 T M V) (hU1 : U ≠ ⊥)
    (hUV : U ≤ V)
    (hCM : M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (V : Set G))
    (hCU : ¬ Subgroup.centralizer (U : Set G) ≤ M) :
    (∃ U₁ : Subgroup G, U ≤ U₁ ∧ U₁ ≤ V ∧ E3.mQuot V U₁ = 1 ∧
      ¬ Subgroup.centralizer (U₁ : Set G) ≤ M) ∧ E3.rParam V = 1 := by
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  obtain ⟨U₁, hUU₁, hU₁V, hCU₁, hmax₁⟩ := exists_maximal_centralizer_not_le hUV hCU
  have hmax : ∀ W : Subgroup G, U₁ < W → W ≤ V → Subgroup.centralizer (W : Set G) ≤ M := by
    intro W hW hWV
    by_contra hCW
    exact (ne_of_lt hW) (hmax₁ W hW.le hWV hCW).symm
  have hCM₁ : M ⊓ Subgroup.centralizer (U₁ : Set G) = M ⊓ Subgroup.centralizer (V : Set G) :=
    le_antisymm ((inf_le_inf_left M (Subgroup.centralizer_le hUU₁)).trans hCM.le)
      (inf_le_inf_left M (Subgroup.centralizer_le hU₁V))
  have hU₁1 : U₁ ≠ ⊥ := fun h0 => hU1 (le_bot_iff.1 (h0 ▸ hUU₁))
  have hΓ : U₁ ∈ gammaE64 V M :=
    ⟨hU₁V, hU₁1, hCU₁, (twoPrimeResidual_le_self' _).trans hCM₁.le⟩
  have hU₁ne : U₁ ≠ V := by
    rintro rfl
    exact hCU₁ h.centralizer_le
  have hm1 : E3.mQuot V U₁ = 1 := by
    have h1 := one_le_mQuot hV2 hU₁V hU₁ne
    by_contra hne
    have hn : 1 < E3.mQuot V U₁ := lt_of_le_of_ne h1 (Ne.symm hne)
    obtain ⟨x, hx, hxj⟩ := e6_11_two hComp h hΓ hmax hn
    have hxV : x ∈ Subgroup.centralizer (V : Set G) := by
      rw [hCM₁] at hx
      exact hx.2
    have hdvd := (hxj 1).1 (by rw [pow_one]; exact hxV)
    have h2 : 2 ^ E3.mQuot V U₁ - 1 = 1 := Nat.eq_one_of_dvd_one hdvd
    have h3 : 2 ^ 2 ≤ 2 ^ E3.mQuot V U₁ := Nat.pow_le_pow_right (by norm_num) hn
    omega
  refine ⟨⟨U₁, hUU₁, hU₁V, hm1, hCU₁⟩, le_antisymm ?_ ?_⟩
  · have hle := E3.rParam_le_mQuot hU₁V fun hle => hCU₁ (hle.trans h.normalizer_le)
    rw [hm1] at hle
    exact_mod_cast hle
  · refine le_iInf₂ fun W hW => ?_
    have hWne : W ≠ V := by
      rintro rfl
      exact hW.2 (Subgroup.centralizer_le_normalizer _)
    exact_mod_cast one_le_mQuot hV2 hW.1 hWne

theorem as_E_6_12_of
    (hComp : E611ComponentCase) : ASInputs.AS_E_6_12 :=
  fun _ _ _ _ _ _ _ h hU1 hUV hCM hCU => e6_12 hComp h hU1 hUV hCM hCU

theorem ch6InE612_of
    (hComp : E611ComponentCase) : H13.Ch6InE612 :=
  fun _ _ _ _ _ _ _ h hU1 hUV hCM hCU => e6_12 hComp h hU1 hUV hCM hCU

end E6
end CFSG.Quasithin
