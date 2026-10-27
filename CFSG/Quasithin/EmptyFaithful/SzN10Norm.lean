module

public import CFSG.Quasithin.EmptyFaithful.SzN10Borel
public import CFSG.Quasithin.EmptyFaithful.SzN10Borel2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Vol2.Ch10.SecA

section Norm

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem szN10_R_le_MI (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t) : R153 T V₁ Yp ≤ M ⊓ I := by
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := ctx.ctx.hyp
  have hI : IsHPlus Yp (Sgp153 T V₁) M I := ctx.ctx.inH
  have hF : Facts15311 T M V₁ Yp I := ctx.facts
  have hYI : Yp ≤ I := le_sup_left.trans hI.1.1
  have hYM : Yp ≤ M := by
    intro y hy
    have h1 : y ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := ⟨hYI hy, Subgroup.le_normalizer hy⟩
    rw [hF.norm_eq] at h1
    exact h1.1
  have hSM : Sgp153 T V₁ ≤ M := fun x hx => hh.hyp.T_le hx.1
  have hSI : Sgp153 T V₁ ≤ I := hF.sylow.1
  have hle : R153 T V₁ Yp ≤ Yp ⊔ Sgp153 T V₁ := pCoreOf_le 2 _
  exact hle.trans (sup_le (le_inf hYM hYI) (le_inf hSM hSI))

omit [Finite G] in
theorem szN10_center_bot_of_lin2 [Finite G] {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥ := by
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, α, hαs, hαk, -⟩ := id hlin
  have hF₀' : Nat.card F₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card]; exact hcard₀
  have e₀ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F₀ :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have hN : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) := by
    rw [Nat.card_congr e₀.toEquiv, card_SL_two_pow hF₀']
  have hsl : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F₀) :=
    isSimpleGroup_sl_two_pow hn hcard₀
  have hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := e₀.isSimpleGroup
  have hnp : ¬ (Nat.card (↥L ⧸ CFSG.pCore 2 ↥L)).Prime := by
    rw [hN]
    refine Nat.not_prime_mul ?_ ?_
    · have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
    · have : 4 ^ 2 ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      omega
  exact center_eq_bot_of_simple_of_card_not_prime hnp

theorem szN10_normalizer_RL_le_MI (ctx : Ctx15316 T Mc M V₁ V₂ Yp I L t)
    (hRL : IsSylowTwoOf (R153 T V₁ Yp ⊓ L) L) {n : ℕ} (hn : 1 < n) (hlin : IsLin2Type L n) :
    L ⊓ Subgroup.normalizer ((R153 T V₁ Yp ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I := by
  have hR : R153 T V₁ Yp ≤ Subgroup.normalizer (L : Set G) := ctx.c16.R_norm
  have hBor := szN10_borel_of_lin2 ctx hn hlin
  obtain ⟨h1, -, -⟩ := ctx.c16.desc
  have hZ := szN10_center_bot_of_lin2 hn hlin
  have hNV : L ⊔ R153 T V₁ Yp ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := h1.2.2.2.1
  have hker : ∀ l ∈ L, l ∈ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) → l ∈ pCoreOf 2 L := by
    intro l hl hlC
    have hlLR : l ∈ (L ⊔ R153 T V₁ Yp) ⊓ Subgroup.centralizer
        (omegaOneCenterOf (pCoreOf 2 (L ⊔ R153 T V₁ Yp)) : Set G) := ⟨Subgroup.mem_sup_left hl, hlC⟩
    have h2 : l ∈ pCoreOf 2 (L ⊔ R153 T V₁ Yp) :=
      centralizer_le_pCoreOf_of_center_eq_bot hR hZ h1.2.1 hlLR
    have hLQ : L ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ R153 T V₁ Yp) : Set G) :=
      le_sup_left.trans (le_normalizer_pCoreOf 2 _)
    have hle : L ⊓ pCoreOf 2 (L ⊔ R153 T V₁ Yp) ≤ pCoreOf 2 L :=
      le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hLQ hg⟩)
        ((pCoreOf_isPGroup 2 _).to_le inf_le_right)
    exact hle ⟨hl, h2⟩
  have hEq := szN10_borel_eq (le_sup_left.trans hNV) hker inf_le_right hRL
    (inf_le_inf_right L (szN10_R_le_MI ctx)) hBor
  intro x hx
  have hx' : x ∈ (M ⊓ I) ⊓ L := hEq ▸ hx
  exact hx'.1

end Norm

end CFSG.Quasithin
