module

public import CFSG.RankThree.PartOne.S10.NonquasisimpleMovingMinimalOddCoreAction
import CFSG.RankThree.GroupTheory.SteinbergBYAlphaMixedCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.GroupTheory.SteinbergBY
open scoped commutatorElement Pointwise

theorem exists_plane_of_index_prime_subgroup {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A B : Subgroup G} (hAe : IsElementaryAbelian p A)
    (hAcard : Nat.card A = p ^ 3) (hBA : B ≤ A) (hrel : B.relIndex A = p) :
    ∃ a b : G, a ∈ A ∧ a ∉ B ∧ b ∈ B ∧ b ≠ 1 ∧ zpowers a ⊔ zpowers b ≤ A ∧
      IsElementaryAbelian p ↥(zpowers a ⊔ zpowers b) ∧
      Nat.card ↥(zpowers a ⊔ zpowers b) = p ^ 2 ∧
      (∀ x ∈ A, ∃ β ∈ B, ∃ y ∈ zpowers a ⊔ zpowers b, x = β * y) ∧
      Nat.card ↥((zpowers a ⊔ zpowers b) ⊓ B) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have hBcard : Nat.card B = p ^ 2 := by
    have h := Subgroup.relIndex_mul_card B A
    rw [inf_eq_left.mpr hBA, hrel, hAcard] at h
    have hp0 : 0 < p := hp.pos
    have : p * Nat.card B = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hp0 this
  obtain ⟨a, haA, haB⟩ : ∃ a ∈ A, a ∉ B := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.relIndex_eq_one.mpr (fun x hx => hcon x hx : A ≤ B)
    rw [hrel] at this
    exact hp.one_lt.ne' this
  obtain ⟨b, hbB, hb1⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hBbot : B = ⊥ := (Subgroup.eq_bot_iff_forall B).mpr hcon
    rw [hBbot, Subgroup.card_bot] at hBcard
    have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have ha1 : a ≠ 1 := fun h => haB (h ▸ B.one_mem)
  have hbA : b ∈ A := hBA hbB
  have hoa : orderOf a = p := orderOf_eq_of_isElementaryAbelian hp haA ha1
  have hob : orderOf b = p := orderOf_eq_of_isElementaryAbelian hp hbA hb1
  have hbza : b ∉ zpowers a := by
    intro hb
    have hle : zpowers b ≤ zpowers a := zpowers_le.mpr hb
    have heq : zpowers b = zpowers a := Subgroup.eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers, Nat.card_zpowers, hoa, hob])
    apply haB
    have : a ∈ zpowers b := heq ▸ mem_zpowers a
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp this
    exact B.zpow_mem hbB k
  set A₀ := zpowers a ⊔ zpowers b with hA₀
  have hA₀A : A₀ ≤ A := sup_le (zpowers_le.mpr haA) (zpowers_le.mpr hbA)
  have hA₀card : Nat.card A₀ = p ^ 2 := card_zpowers_sup_zpowers hp hAcard haA ha1 hbA hbza
  have : Finite A₀ := inferInstance
  have hza : IsElementaryAbelian p (zpowers a) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian a haA)
  have hzb : IsElementaryAbelian p (zpowers b) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian b hbA)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    mul_comm_of_isMulCommutative hx hy
  have hzbc : zpowers b ≤ Subgroup.centralizer (zpowers a : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x (zpowers_le.mpr haA hx) y ((zpowers_le.mpr hbA) hy)
  have hA₀elem : IsElementaryAbelian p ↥A₀ := IsElementaryAbelian.sup_of_le_centralizer hzbc
  have hzaN : zpowers a ≤ normalizer (B : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x (hBA hx) y (zpowers_le.mpr haA hy)
  have hBsup : B ⊔ zpowers a = A := by
    have hle : B ⊔ zpowers a ≤ A := sup_le hBA (zpowers_le.mpr haA)
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    have hlt : B < B ⊔ zpowers a :=
      lt_of_le_of_ne le_sup_left fun h => haB (h ▸ mem_sup_right (mem_zpowers a))
    have h1 := Subgroup.card_lt_of_lt hlt
    rw [hBcard] at h1
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp).mp (hAcard ▸ Subgroup.card_dvd_of_le hle)
    rw [hAcard, hjc]
    rw [hjc] at h1
    have hj3 : j ≤ 3 := hj
    have : 2 < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp h1
    rw [show j = 3 by omega]
  refine ⟨a, b, haA, haB, hbB, hb1, hA₀A, hA₀elem, hA₀card, ?_, ?_⟩
  · intro x hx
    rw [← hBsup, ← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left B _ hzaN] at hx
    obtain ⟨β, hβ, y, hy, rfl⟩ := hx
    exact ⟨β, hβ, y, Subgroup.mem_sup_left hy, rfl⟩
  ·
    have hzbB : zpowers b ≤ A₀ ⊓ B := le_inf le_sup_right (zpowers_le.mpr hbB)
    have hdvd : Nat.card ↥(A₀ ⊓ B) ∣ p ^ 2 :=
      hA₀card ▸ Subgroup.card_dvd_of_le (inf_le_left : A₀ ⊓ B ≤ A₀)
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hpd : p ∣ Nat.card ↥(A₀ ⊓ B) := by
      have h := Subgroup.card_dvd_of_le hzbB
      rw [Nat.card_zpowers, hob] at h
      exact h
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hjc
      rw [hjc] at hpd
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpd)
    have hj2 : j ≠ 2 := by
      rintro rfl
      have heq : A₀ ⊓ B = A₀ := Subgroup.eq_of_le_of_card_ge (inf_le_left : A₀ ⊓ B ≤ A₀) (by
        rw [hA₀card, hjc])
      apply haB
      have : a ∈ A₀ ⊓ B := by rw [heq]; exact mem_sup_left (mem_zpowers a)
      exact this.2
    rw [hjc, show j = 1 by omega, pow_one]

theorem plane_transfer {G : Type*} [Group G] {A A₀ B R U : Subgroup G}
    (hfac : ∀ x ∈ A, ∃ β ∈ B, ∃ y ∈ A₀, x = β * y) (hA₀A : A₀ ≤ A)
    (hBR : B ≤ Subgroup.centralizer (R : Set G)) (hUR : U ≤ R)
    (hA₀U : A₀ ≤ normalizer (U : Set G)) :
    A ≤ normalizer (U : Set G) ∧ ⁅U, A⁆ = ⁅U, A₀⁆ := by
  have hconj : ∀ y ∈ A₀, ∀ u ∈ U, y * u * y⁻¹ ∈ U := fun y hy u hu =>
    (Subgroup.mem_normalizer_iff.mp (hA₀U hy) u).mp hu
  have hcomm : ∀ β ∈ B, ∀ r ∈ R, β * r = r * β := fun β hβ r hr =>
    (Subgroup.mem_centralizer_iff.mp (hBR hβ) r hr).symm
  refine ⟨le_normalizer_of_conj_mem_forall fun x hx u hu => ?_,
    le_antisymm ?_ (Subgroup.commutator_mono le_rfl hA₀A)⟩
  · obtain ⟨β, hβ, y, hy, rfl⟩ := hfac x hx
    have h1 := hconj y hy u hu
    have h2 := hcomm β hβ _ (hUR h1)
    have h3 : β * y * u * (β * y)⁻¹ = y * u * y⁻¹ := by
      calc β * y * u * (β * y)⁻¹ = (β * (y * u * y⁻¹)) * β⁻¹ := by group
        _ = ((y * u * y⁻¹) * β) * β⁻¹ := by rw [h2]
        _ = y * u * y⁻¹ := by group
    rw [h3]
    exact h1
  · rw [Subgroup.commutator_le]
    intro u hu x hx
    obtain ⟨β, hβ, y, hy, rfl⟩ := hfac x hx
    have h1 : ⁅u, y⁆ ∈ U := by
      have := U.mul_mem hu (hconj y hy u⁻¹ (U.inv_mem hu))
      rw [commutatorElement_def]
      simpa [mul_assoc] using this
    have h2 := hcomm β hβ _ (hUR h1)
    have h3 := hcomm β hβ u (hUR hu)
    have h4 : ⁅u, β * y⁆ = ⁅u, y⁆ := by
      calc ⁅u, β * y⁆ = (u * β) * y * u⁻¹ * y⁻¹ * β⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = (β * u) * y * u⁻¹ * y⁻¹ * β⁻¹ := by rw [← h3]
        _ = β * ⁅u, y⁆ * β⁻¹ := by simp only [commutatorElement_def]; group
        _ = (⁅u, y⁆ * β) * β⁻¹ := by rw [h2]
        _ = ⁅u, y⁆ := by group
    rw [h4]
    exact Subgroup.commutator_mem_commutator hu hy

theorem minTwoActionSetting_of_plane {G : Type*} [Group G] {p q : ℕ} {A A₀ D R : Subgroup G}
    (hp : p.Prime) (hq : q.Prime) (hp3 : 3 < p) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hA₀elem : IsElementaryAbelian p A₀) (hA₀card : Nat.card A₀ = p ^ 2) (hA₀A : A₀ ≤ A)
    (hfac : ∀ x ∈ A, ∃ β ∈ A ⊓ Subgroup.centralizer (R : Set G), ∃ y ∈ A₀, x = β * y)
    (hRAD : R ⊔ A ≤ normalizer (D : Set G)) (hDexp : ∀ x ∈ D, x ^ q = 1)
    (hDcl : ⁅⁅D, D⁆, D⁆ = ⊥) (hR2 : IsPGroup 2 R) (hAR : A ≤ normalizer (R : Set G))
    (hRA : ⁅R, A⁆ = R) (hR1 : R ≠ ⊥) (hRD : ⁅R, D⁆ ≠ ⊥)
    (hmin : ∀ U : Subgroup G, U < R → A ≤ normalizer (U : Set G) → ⁅U, A⁆ = U → ⁅U, D⁆ = ⊥) :
    MinTwoActionSetting p q A₀ D R := by
  have hBR : A ⊓ Subgroup.centralizer (R : Set G) ≤ Subgroup.centralizer (R : Set G) :=
    inf_le_right
  have hA₀R : A₀ ≤ normalizer (R : Set G) := hA₀A.trans hAR
  have hDq : IsPGroup q D := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hDexp x x.2)⟩
  exact
    { prime_p := hp
      prime_q := hq
      three_lt_p := hp3
      q_ne_two := hq2
      p_ne_q := hqp.symm
      A_elem := hA₀elem
      A_card := hA₀card
      D_inv := sup_le (le_sup_left.trans hRAD) (hA₀A.trans (le_sup_right.trans hRAD))
      D_pgroup := hDq
      D_exp := hDexp
      D_class := hDcl
      R_two := hR2
      R_inv := hA₀R
      R_comm := by
        rw [← (plane_transfer hfac hA₀A hBR le_rfl hA₀R).2]
        exact hRA
      R_ne := hR1
      R_act := hRD
      R_min := by
        intro U hUR hA₀U hUA₀
        obtain ⟨hAU, hUA⟩ := plane_transfer hfac hA₀A hBR hUR.le hA₀U
        have hbot := hmin U hUR hAU (hUA.trans hUA₀)
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot }

theorem nonquasisimple_moving_theta_component_prime_cut_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    NonquasisimpleMovingThetaComponentPrimeCut := by
  intro hTwo G _ _ he p hp hp3 hvan A hAe hAcard L hL
  by_cases hqs : CFSG.IsQuasisimple L
  · exact Or.inl hqs
  refine Or.inr ?_
  obtain ⟨q, hq, hq2, hqp, D, R, hD1, hDL, hDchar, hDO, hDexp, hDcl, hR2, hRL, hAR, hRA, hR1, hRD,
    hmin, hrel, hrank⟩ :=
    nonquasisimple_moving_theta_component_minimal_odd_core_action_of hB5 G he p hp hp3 hvan A hAe
      hAcard L hL hqs
  have hAL : A ≤ normalizer (L : Set G) := hB5.2 G he p hp hp3 A hAe L hL.1
  have hAD : A ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf hAL hDL hDchar
  have hLD : L ≤ normalizer (D : Set G) :=
    le_normalizer_of_characteristic_subgroupOf Subgroup.le_normalizer hDL hDchar
  have hBA : A ⊓ Subgroup.centralizer (R : Set G) ≤ A := inf_le_left
  obtain ⟨a, b, haA, haB, hbB, hb1, hA₀A, hA₀elem, hA₀card, hfac, -⟩ :=
    exists_plane_of_index_prime_subgroup hp hAe hAcard hBA hrel
  set A₀ := zpowers a ⊔ zpowers b with hA₀
  have hRAD : R ⊔ A ≤ normalizer (D : Set G) := sup_le (hRL.trans hLD) hAD
  have hset : MinTwoActionSetting p q A₀ D R :=
    minTwoActionSetting_of_plane hp hq hp3 hq2 hqp hA₀elem hA₀card hA₀A hfac hRAD hDexp hDcl hR2
      hAR hRA hR1 hRD hmin
  obtain ⟨hAlt, -, -⟩ := hTwo
  rcases hAlt G p q A₀ D R hset hrank with
    ⟨⟨⟨h5, -⟩ | ⟨h7, -⟩, -⟩⟩ | ⟨h5, -⟩ | ⟨h5, -⟩
  · exact Or.inl h5
  · exact Or.inr h7
  · exact Or.inl h5
  · exact Or.inl h5

end CFSG.RankThree.PartOne
