module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIOrd3
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep3

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem exists_y0 (h1222 : Stmt12_2_2) {T L V V₁ V₂ : Subgroup G} (hcx : Cx1291 G T L V 4)
    (hs : Setting1282One G T L V 4 V₁ V₂) :
    ∃ y₀ : G, y₀ ∈ L ⊓ Subgroup.centralizer (V₂ : Set G) ∧ orderOf y₀ = 3 := by
  classical
  obtain ⟨hc, -⟩ := hcx.hyp.natural
  obtain ⟨hcard, hsq, -⟩ := hcx.hyp.card_sq
  haveI := hc
  letI : Module (ZMod 2) (Additive ↥V) := zmodModuleOf hsq
  have hV₂V : V₂ ≤ V := hs.v2.1
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hcx.hyp.hyp.irrPlus.2.2.1
  have htop : autOn L V = ⊤ := autOn_eq_top_of_hyp1281One hcx.hyp
  have hV₂4 : Nat.card V₂ = 4 := by simpa using hs.v2.2.1
  have hM : Module.finrank (ZMod 2) (Additive ↥V) = 4 := by
    apply finrank_of_natCard (n := 4)
    show Nat.card ↥V = 2 ^ 4
    rw [hcard]
  have hℓ : Module.finrank (ZMod 2) (subOf (V := V) V₂) = 2 := by
    apply finrank_of_natCard (n := 2)
    rw [natCard_subOf hV₂V, hV₂4]
    norm_num
  obtain ⟨γ, hγ3, hγ1, hγfix⟩ := exists_order_three_fix hM (subOf (V := V) V₂) hℓ
  have hγstab : γ ∈ stabS (subOf (V := V) V₂) := by
    rw [mem_stabS_iff]
    intro v
    constructor
    · intro hv
      rw [hγfix v hv]
      exact hv
    · intro hv
      have h1 : γ v ∈ subOf (V := V) V₂ := hv
      have h2 := hγfix (γ v) hv
      have h3 : γ.symm (γ v) = v := γ.symm_apply_apply v
      have h4 : γ.symm (γ v) = γ.symm (γ v) := rfl
      rw [← h3]
      have h5 : γ.symm (γ v) ∈ subOf (V := V) V₂ := by
        have : γ.symm (γ v) = γ v := by
          conv_lhs => rw [← hγfix (γ v) hv]
          exact (γ.symm_apply_apply _).trans (by rw [← hγfix (γ v) hv])
        rw [this]
        exact hv
      exact h5
  obtain ⟨l, hl, hlL, hlN, hlin⟩ := exists_lift hLV htop hV₂V hγstab
  have hlC : l ∈ Subgroup.centralizer (V₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hv := hγfix (Additive.ofMul (⟨h, hV₂V hh⟩ : ↥V)) ((mem_subOf (V := V)).2 (by simpa using hh))
    have hc' := congrArg (fun y : Additive ↥V => ((Additive.toMul y : ↥V) : G)) hv
    rw [← hlin] at hc'
    rw [coe_linAct] at hc'
    simp only [toMul_ofMul] at hc'
    exact (mul_inv_eq_iff_eq_mul.1 hc').symm
  have hγord : orderOf γ = 3 := orderOf_eq_prime hγ3 hγ1
  have hl_fin : IsOfFinOrder (⟨l, hl⟩ : Subgroup.normalizer (V : Set G)) :=
    isOfFinOrder_of_finite _
  have hdvd : 3 ∣ orderOf l := by
    have h1 := orderOf_map_dvd (linAct (V := V)) (⟨l, hl⟩ : Subgroup.normalizer (V : Set G))
    rw [hlin, hγord] at h1
    have h2 : orderOf (⟨l, hl⟩ : Subgroup.normalizer (V : Set G)) = orderOf l :=
      (Subgroup.orderOf_coe (⟨l, hl⟩ : Subgroup.normalizer (V : Set G))).symm
    rw [h2] at h1
    exact h1
  have hpos : 0 < orderOf l := (isOfFinOrder_of_finite l).orderOf_pos
  have hn0 : orderOf l / 3 ≠ 0 := by
    intro h0
    rw [Nat.div_eq_zero_iff] at h0
    have := Nat.le_of_dvd hpos hdvd
    omega
  refine ⟨l ^ (orderOf l / 3), Subgroup.pow_mem _ (Subgroup.mem_inf.2 ⟨hlL, hlC⟩) _, ?_⟩
  rw [orderOf_pow_of_dvd hn0 (Nat.div_dvd_of_dvd hdvd), Nat.div_div_self hdvd (by omega)]

end CFSG.Quasithin.H13.C1294
