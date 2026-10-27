module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Split
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusFrameFusion
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter

public section

namespace CFSG.StandardType.TwE6SplitRootGen

open CFSG.Assembly TableB

theorem ggTorusModelAt_recipeR_twE6Split_of_five_le
    {K : Type} [Field K] [Finite K] {n p : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpn : p ∣ 2 ^ n - 1) {E : Subgroup (TwE6Delta.RecipeR K n)}
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : TwE6Delta.RecipeR K n, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    GGTorusModelAt p E := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    omega
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  have hex : ∃ ζ : Kˣ, orderOf ζ = p := by
    have hdvd : p ∣ Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have h1 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        have h2 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        have := Nat.mul_self_sub_mul_self_eq (2 ^ n) 1
        simpa [sq] using this
      rw [h1]
      exact Dvd.dvd.mul_left hpn _
    exact exists_prime_orderOf_dvd_card' p hdvd
  obtain ⟨ζ, hζo⟩ := hex
  have hζ : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  set σ : K →+* K := iterateFrobenius K 2 n
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  have hζσ : σ (ζ : K) = ζ := by
    have h1 : ζ ^ (2 ^ n - 1) = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, hζo]
      exact hpn
    have h2 : ζ ^ (2 ^ n) = ζ := by
      rw [show 2 ^ n = 2 ^ n - 1 + 1 from
        (Nat.sub_add_cancel (Nat.one_le_two_pow)).symm, pow_succ, h1, one_mul]
    rw [hσ (ζ : K), ← Units.val_pow_eq_pow_val, h2]
  obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup hn hK σ hσ
  have hT := ggTorusModelAt_range_twE6SplitFrameHom (K := K) σ hp2 hζo hζ hζσ
  have hinj := ExcFrames.twE6SplitFrameHom_injective (K := K) σ hp5 hζo hζ hζσ
  let T := ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
  let E₀ : Subgroup (TwE6Delta.RecipeR K n) := T.range.map e.symm.toMonoidHom
  have hmodel₀ : GGTorusModelAt p E₀ := GGTorusModelAt.map hT e.symm
  have hel₀ : IsElemAbelian p E₀ := by
    have h := ExcFrames.isElemAbelian_range_frame (e.symm.toMonoidHom.comp T)
    rw [MonoidHom.range_comp] at h
    exact h
  have hcardT : Nat.card T.range = p ^ 4 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hcard₀ : Nat.card E₀ = p ^ 4 := by
    show Nat.card (T.range.map e.symm.toMonoidHom) = p ^ 4
    rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hcardT
  haveI := TwE6Delta.finite_recipeR (K := K) hK
  obtain ⟨c, hc⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp
    (sylowTorus_recipeR_split hn hK hp hp5 hpn) (N := 4) hel₀ hcard₀ hE hsc
  rw [hc]
  exact GGTorusModelAt.map hmodel₀ (MulAut.conj c)

end CFSG.StandardType.TwE6SplitRootGen

end
