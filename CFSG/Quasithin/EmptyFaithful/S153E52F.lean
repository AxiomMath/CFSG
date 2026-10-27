module

public import CFSG.Quasithin.EmptyFaithful.S153E51A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace S153E

section Coprime

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_pGroup_two_three {P Q : Subgroup G} (hP : IsPGroup 2 P) (hQ : IsPGroup 3 Q) :
    P ⊓ Q = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h2 : IsPGroup 2 ↥(P ⊓ Q) := hP.to_inf_left
  have h3 : IsPGroup 3 ↥(P ⊓ Q) := hQ.to_inf_right
  obtain ⟨a, ha⟩ := (IsPGroup.iff_orderOf.mp h2) ⟨x, hx⟩
  obtain ⟨b, hb⟩ := (IsPGroup.iff_orderOf.mp h3) ⟨x, hx⟩
  have hab : 2 ^ a = 3 ^ b := ha.symm.trans hb
  have ha0 : a = 0 := by
    by_contra hne
    have : 2 ∣ 3 ^ b := by
      rw [← hab]
      exact dvd_pow_self 2 hne
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
    omega
  rw [ha0, pow_zero] at ha
  have : (⟨x, hx⟩ : ↥(P ⊓ Q)) = 1 := orderOf_eq_one_iff.mp ha
  exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)

end Coprime

section Fifty2F

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ : Subgroup G} {t : G}

theorem card_Y_eq (cx : Ctx15350 T Mc M V₁ V₂ t) :
    Nat.card ↥(Y153 Mc M) = Nat.card ↥(pCoreOf 2 (Y153 Mc M)) * 9 := by
  obtain ⟨e⟩ := cx.r49.case_one.2
  have h9 : Nat.card (OTwoQuot (Y153 Mc M)) = 9 := by
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 3) ≃ (Fin 2 → ZMod 3))]
    simp
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥(Y153 Mc M))
  have h2 : Nat.card ↥(pCoreOf 2 (Y153 Mc M)) = Nat.card ↥(CFSG.Open.pCore 2 ↥(Y153 Mc M)) :=
    Subgroup.card_map_of_injective (Y153 Mc M).subtype_injective
  rw [h2]
  have h3 : Nat.card (OTwoQuot (Y153 Mc M)) = Nat.card (↥(Y153 Mc M) ⧸ CFSG.Open.pCore 2 ↥(Y153 Mc M)) := rfl
  rw [h1, ← h3, h9]
  ring

theorem Y_eq_sup_of_sylow (cx : Ctx15350 T Mc M V₁ V₂ t) {D : Subgroup G}
    (hDY : D ≤ Y153 Mc M) (hD3 : IsPGroup 3 D) (hDi : ¬ 3 ∣ D.relIndex (Y153 Mc M)) :
    Y153 Mc M = pCoreOf 2 (Y153 Mc M) ⊔ D := by
  set Y := Y153 Mc M with hYdef
  set A := pCoreOf 2 Y with hA
  have hA2 : IsPGroup 2 A := pCoreOf_isPGroup 2 Y
  have hAY : A ≤ Y := pCoreOf_le 2 Y
  have hinf : A ⊓ D = ⊥ := inf_eq_bot_of_pGroup_two_three hA2 hD3
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  obtain ⟨m, hm⟩ := hD3.exists_card_eq
  have hY9 : Nat.card ↥Y = Nat.card ↥A * 9 := card_Y_eq cx
  have hrel := Subgroup.relIndex_mul_card D Y
  rw [inf_eq_left.2 hDY, hm] at hrel
  rw [hk] at hY9
  have hr3 : Nat.Coprime 3 (D.relIndex Y) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hDi
  have hD9 : Nat.card ↥D = 9 := by
    have hrel' : D.relIndex Y * 3 ^ m = 2 ^ k * 9 := by rw [← hY9]; exact hrel
    have hd1 : (3 : ℕ) ^ m ∣ 9 := by
      have h1 : 3 ^ m ∣ 2 ^ k * 9 := ⟨D.relIndex Y, by rw [← hrel']; ring⟩
      have hc : Nat.Coprime (3 ^ m) (2 ^ k) := Nat.Coprime.pow m k (by norm_num)
      exact hc.dvd_of_dvd_mul_left h1
    have hd2 : (9 : ℕ) ∣ 3 ^ m := by
      have h1 : 9 ∣ D.relIndex Y * 3 ^ m := ⟨2 ^ k, by rw [hrel']; ring⟩
      have hc : Nat.Coprime 9 (D.relIndex Y) := by
        have : Nat.Coprime (3 ^ 2) (D.relIndex Y) := Nat.Coprime.pow_left 2 hr3
        simpa using this
      exact hc.dvd_of_dvd_mul_left h1
    rw [hm]
    exact Nat.dvd_antisymm hd1 hd2
  have hDN : D ≤ Subgroup.normalizer (A : Set G) := hDY.trans (le_normalizer_pCoreOf 2 Y)
  have h1 := A4.relIndex_sup_eq_of_le_normalizer' hDN
  have h2 := Subgroup.relIndex_mul_card A (D ⊔ A)
  have h3 := Subgroup.relIndex_mul_card A D
  rw [inf_of_le_left le_sup_right, h1] at h2
  rw [hinf, Subgroup.card_bot, mul_one] at h3
  have hle : D ⊔ A ≤ Y := sup_le hDY hAY
  have hcard : Nat.card ↥(D ⊔ A) = Nat.card ↥Y := by
    rw [← h2, h3, hD9, hY9, hk]
    ring
  rw [sup_comm]
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])).symm

theorem fixed_V_D_eq_one (h113 : StageLemma14113) (cx : Ctx15350 T Mc M V₁ V₂ t) {D : Subgroup G}
    (hDY : D ≤ Y153 Mc M) (hD3 : IsPGroup 3 D)
    (hYD : Y153 Mc M = pCoreOf 2 (Y153 Mc M) ⊔ D) :
    ∀ v ∈ VZ T M, (∀ d ∈ D, d * v * d⁻¹ = v) → v = 1 := by
  obtain ⟨L₁, L₂, tb, s₁, s₂, τ, a₁, a₂, hS, hF, -, -⟩ := exists_bar_model cx
  have hV := cx.c.hyp.elemAbelian
  have hMN := cx.c.hyp.le_normalizer
  have hYN : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) := (Y153_le Mc M).trans hMN
  have hDN : D ≤ Subgroup.normalizer (VZ T M : Set G) := hDY.trans hYN
  have hAC : pCoreOf 2 (Y153 Mc M) ≤ Subgroup.centralizer (VZ T M : Set G) := by
    rw [cx.r49.case_one.1]
    exact inf_le_right
  have hAN : pCoreOf 2 (Y153 Mc M) ≤ Subgroup.normalizer (VZ T M : Set G) :=
    (pCoreOf_le 2 _).trans hYN
  have hbar : autI hV (Y153 Mc M) = autI hV D := by
    conv_lhs => rw [hYD]
    rw [autI_sup hV hAN hDN, autI_eq_bot_of_le_centralizer hV hAC, bot_sup_eq]
  have hYbar : autI hV (Y153 Mc M) = oTwoUpper (autI hV M) := cx.c.hyp.autOn_Y153 h113
  have hcomm : commV (autI hV D) = ⊤ := by
    rw [← hbar, hYbar]
    exact hS.commV_oTwoUpper
  have hP3 : IsPGroup 3 ↥(autI hV D) :=
    (hD3.of_equiv (Subgroup.subgroupOfEquivOfLe hDN).symm).map (convI hV)
  have hodd : Odd (Nat.card ↥(autI hV D)) := by
    obtain ⟨n, hn⟩ := hP3.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hexp : ∀ w : IntMod (VZ T M) hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨-, hmeet⟩ := coprime_decomp (W := ⊤) hodd hexp (fun g _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, hcomm, top_inf_eq] at hmeet
  have hfix : fixV (autI hV D) = ⊥ := by
    rw [top_inf_eq] at hmeet
    exact hmeet
  intro v hv hvD
  have hw : IntMod.mk hV ⟨v, hv⟩ ∈ fixV (autI hV D) := by
    rw [mem_fixV_autI hV hDN]
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have := hvD d hd
    show d * v = v * d
    calc d * v = (d * v * d⁻¹) * d := by group
      _ = v * d := by rw [this]
  rw [hfix, Subgroup.mem_bot] at hw
  have := congrArg IntMod.val hw
  exact this

end Fifty2F

end S153E

end CFSG.Quasithin
