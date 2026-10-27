module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFComp
public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.Quasithin.SBd19F

open CFSG CFSG.LocalCores CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {H : Type} [Group H] [Finite H]

theorem pRank_le_two (hsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin H) (K : Subgroup H) :
    CFSG.Open.pRank 3 K ≤ 2 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans (hsq 3 Nat.prime_three (by norm_num))

omit [Finite H] in
theorem exists_component_not_centralized {Q : Subgroup H} (hQ : IsQuasisimple ↥Q)
    (hQE : Q ≤ layer H) : ∃ C : Subgroup H, IsComponent C ∧ ⁅Q, C⁆ ≠ ⊥ := by
  by_contra hcon
  push Not at hcon
  have hle : layer H ≤ Subgroup.centralizer (Q : Set H) := sSup_le fun K hK => by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcon K hK
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have hxy : (x : H) * (y : H) = (y : H) * (x : H) :=
    (Subgroup.mem_centralizer_iff.mp (hle (hQE x.2)) y y.2).symm
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext hxy)

omit [Finite H] in
theorem commutator_mul_mul_of_commute {z₁ z₂ l₁ l₂ : H} (h12 : z₁ * z₂ = z₂ * z₁)
    (h1 : z₁ * l₁ = l₁ * z₁) (h2 : z₁ * l₂ = l₂ * z₁) (h3 : z₂ * l₁ = l₁ * z₂)
    (h4 : z₂ * l₂ = l₂ * z₂) : ⁅z₁ * l₁, z₂ * l₂⁆ = ⁅l₁, l₂⁆ := by
  have hc1 : Commute z₁ (l₁ * z₂ * l₂ * l₁⁻¹) :=
    (((show Commute z₁ l₁ from h1).mul_right (show Commute z₁ z₂ from h12)).mul_right
      (show Commute z₁ l₂ from h2)).mul_right (show Commute z₁ l₁ from h1).inv_right
  have hc2 : Commute z₂ (l₁ * l₂ * l₁⁻¹) :=
    ((show Commute z₂ l₁ from h3).mul_right (show Commute z₂ l₂ from h4)).mul_right
      (show Commute z₂ l₁ from h3).inv_right
  calc ⁅z₁ * l₁, z₂ * l₂⁆ = z₁ * (l₁ * z₂ * l₂ * l₁⁻¹) * z₁⁻¹ * l₂⁻¹ * z₂⁻¹ := by
        rw [commutatorElement_def]; group
    _ = (l₁ * z₂ * l₂ * l₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by
        rw [hc1.eq]; group
    _ = z₂ * (l₁ * l₂ * l₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by
        have : l₁ * z₂ * l₂ * l₁⁻¹ = z₂ * (l₁ * l₂ * l₁⁻¹) := by
          have := hc2.eq
          calc l₁ * z₂ * l₂ * l₁⁻¹ = (l₁ * z₂) * l₂ * l₁⁻¹ := rfl
            _ = (z₂ * l₁) * l₂ * l₁⁻¹ := by rw [h3]
            _ = z₂ * (l₁ * l₂ * l₁⁻¹) := by group
        rw [this]
    _ = ⁅l₁, l₂⁆ := by
        rw [commutatorElement_def]
        have : z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) = (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂ := by
          have hc3 : Commute z₂ (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
            (((show Commute z₂ l₁ from h3).mul_right (show Commute z₂ l₂ from h4)).mul_right
              (show Commute z₂ l₁ from h3).inv_right).mul_right
              (show Commute z₂ l₂ from h4).inv_right
          exact hc3.eq
        calc z₂ * (l₁ * l₂ * l₁⁻¹) * l₂⁻¹ * z₂⁻¹ = z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂⁻¹ := by group
          _ = (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂ * z₂⁻¹ := by rw [this]
          _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by group

theorem exists_rankTwo_component (hsq : CFSG.Open.SQTKTauCeti.StronglyQuasithin H)
    (hno1 : ∀ C : Subgroup H, IsComponent C → CFSG.Open.pRank 3 C ≠ 1)
    (huniq : ∀ C C' : Subgroup H, IsComponent C → IsComponent C' → CFSG.Open.pRank 3 C = 2 →
      CFSG.Open.pRank 3 C' = 2 → C = C')
    {Q : Subgroup H} (hQ : IsQuasisimple ↥Q) (hQE : Q ≤ layer H)
    (h3 : 3 ∣ (Subgroup.center ↥Q).index) :
    ∃ L₂ : Subgroup H, IsComponent L₂ ∧ CFSG.Open.pRank 3 L₂ = 2 ∧ Q ≤ L₂ ∧ L₂.Normal := by
  classical
  obtain ⟨L₂, hL₂, hQL₂⟩ := exists_component_not_centralized hQ hQE
  have hrk2 : CFSG.Open.pRank 3 L₂ = 2 := by
    have h3L : 3 ∣ Nat.card L₂ := by
      by_contra hn
      exact hQL₂ (commutator_eq_bot_of_not_three_dvd hQ hQE hL₂ h3 hn)
    have hne0 : CFSG.Open.pRank 3 L₂ ≠ 0 := fun h0 =>
      not_three_dvd_card_of_pRank_eq_zero h0 h3L
    have := hno1 L₂ hL₂
    have := pRank_le_two hsq L₂
    omega
  have hother : ∀ K : Subgroup H, IsComponent K → K ≠ L₂ → ⁅Q, K⁆ = ⊥ := by
    intro K hK hKL
    have h0 : CFSG.Open.pRank 3 K = 0 := by
      have h1 := hno1 K hK
      have h2 : CFSG.Open.pRank 3 K ≠ 2 := fun h => hKL (huniq K L₂ hK hL₂ h hrk2)
      have := pRank_le_two hsq K
      omega
    exact commutator_eq_bot_of_not_three_dvd hQ hQE hK h3 (not_three_dvd_card_of_pRank_eq_zero h0)
  have hQle : Q ≤ L₂ := by
    set D : Subgroup H := ⨆ (K : Subgroup H) (_ : IsComponent K ∧ K ≠ L₂), K with hD
    have hDQ : D ≤ Subgroup.centralizer (Q : Set H) := by
      refine iSup₂_le fun K hK => ?_
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact hother K hK.1 hK.2
    have hDL : D ≤ Subgroup.centralizer (L₂ : Set H) := by
      refine iSup₂_le fun K hK => ?_
      rcases distinct_components_commute hK.1 hL₂ with h | h
      · exact absurd h hK.2
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hlay : layer H ≤ D ⊔ L₂ := by
      refine sSup_le fun K hK => ?_
      by_cases hKL : K = L₂
      · rw [hKL]; exact le_sup_right
      · exact le_sup_of_le_left (le_iSup₂_of_le K ⟨hK, hKL⟩ le_rfl)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right D L₂
      (hDL.trans (Subgroup.centralizer_le_normalizer _))
    have hdec : ∀ q ∈ Q, ∃ d ∈ D, ∃ l ∈ L₂, q = d * l ∧
        (∀ d' ∈ D, d * d' = d' * d) := by
      intro q hq
      have hq' : q ∈ ((D ⊔ L₂ : Subgroup H) : Set H) := hlay (hQE hq)
      rw [hset] at hq'
      obtain ⟨d, hd, l, hl, rfl⟩ := hq'
      refine ⟨d, hd, l, hl, rfl, fun d' hd' => ?_⟩
      have h1 : (d * l) * d' = d' * (d * l) := Subgroup.mem_centralizer_iff.mp (hDQ hd') _ hq
      have h2 : l * d' = d' * l := Subgroup.mem_centralizer_iff.mp (hDL hd') l hl
      calc d * d' = d * (l * d') * l⁻¹ := by rw [h2]; group
        _ = (d * l) * d' * l⁻¹ := by group
        _ = d' * (d * l) * l⁻¹ := by rw [h1]
        _ = d' * d := by group
    have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ L₂ := by
      intro x hx y hy
      obtain ⟨d₁, hd₁, l₁, hl₁, rfl, hc₁⟩ := hdec x hx
      obtain ⟨d₂, hd₂, l₂, hl₂, rfl, hc₂⟩ := hdec y hy
      have e1 : l₁ * d₂ = d₂ * l₁ := Subgroup.mem_centralizer_iff.mp (hDL hd₂) l₁ hl₁
      have e2 : l₂ * d₁ = d₁ * l₂ := Subgroup.mem_centralizer_iff.mp (hDL hd₁) l₂ hl₂
      have e3 : d₁ * d₂ = d₂ * d₁ := hc₁ d₂ hd₂
      have h1l : d₁ * l₁ = l₁ * d₁ := (Subgroup.mem_centralizer_iff.mp (hDL hd₁) l₁ hl₁).symm
      have h2l : d₂ * l₂ = l₂ * d₂ := (Subgroup.mem_centralizer_iff.mp (hDL hd₂) l₂ hl₂).symm
      have : ⁅d₁ * l₁, d₂ * l₂⁆ = ⁅l₁, l₂⁆ :=
        commutator_mul_mul_of_commute e3 h1l e2.symm e1.symm h2l
      rw [this, commutatorElement_def]
      exact L₂.mul_mem (L₂.mul_mem (L₂.mul_mem hl₁ hl₂) (L₂.inv_mem hl₁)) (L₂.inv_mem hl₂)
    have : Group.IsPerfect ↥Q := hQ.1
    calc Q = ⁅Q, Q⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ L₂ := Subgroup.commutator_le.mpr hcomm
  refine ⟨L₂, hL₂, hrk2, hQle, ?_⟩
  refine ⟨fun n hn g => ?_⟩
  have hconj := isComponent_conj hL₂ g
  have hrkc : CFSG.Open.pRank 3 (L₂.map (MulAut.conj g).toMonoidHom) = 2 := by
    rw [pRank_map_conj]; exact hrk2
  have heq := huniq _ _ hconj hL₂ hrkc hrk2
  rw [← heq]
  exact ⟨n, hn, rfl⟩

end CFSG.Quasithin.SBd19F
