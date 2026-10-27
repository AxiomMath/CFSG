module

public import CFSG.RankThree.GF2n.Stroth80.Sec9NComm
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9ROneC

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem mem_sup_conj_of_normalizes {A B : Subgroup G} {g : G} (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ B) : ∀ h ∈ A ⊔ B, g * h * g⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_sup_left (hA a ha)
    · exact Subgroup.mem_sup_right (hB b hb)
  intro h hh
  exact hle hh

theorem normal_eq_Y (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bCard : Stroth311bCardStatement) (h311bComm : Stroth311bCommStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {X Y : Subgroup G}
    (hsplit : Split95 M Q Z B t X Y) (h4 : Sec4Concl M Q Z B X Y) {x : G}
    (hx : x ∈ LB M Q B ⊓ X) (hxQ : x ∉ Q) (hOm : OmegaPlusNat hc x 2) {Y' : Subgroup G}
    (hQY' : Q ≤ Y') (hY'R : Y' ≤ Rt M (LB M Q B) x)
    (hnorm : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y' = Y')
    (hY'sl : QuotSat Y' Q (IsSLModel 2 (Nat.card Z))) : Y' = Y := by
  classical
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hOm, hs.large⟩
  have hsplit0 := hsplit
  obtain ⟨⟨hQX, hXR, hQY, hYRt, hXY, hXYQ, hcXY⟩, hYsl, -⟩ := hsplit
  have hYsl0 := hYsl
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact ⟨e, he⟩
  have hqev : 2 ∣ Nat.card Z := by
    obtain ⟨s, hs'⟩ := hq2
    have hs0 : s ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hs'
      omega
    rw [hs']
    exact dvd_pow_self 2 hs0
  have hYR : Y ≤ Rt M (LB M Q B) x := le_sup_right.trans (one_part_a hc hsplit0 h4 hxL hx.2)
  have hRne : Rt M (LB M Q B) x ≠ LB M Q B := Rt_ne_LB_of_Y_le hc hsplit0 h4 hYR
  have hNR : hc.CN x ≤ Rt M (LB M Q B) x := fun y hy => (Ctx.mem_CN.mp hy).1
  have hQN : Q ≤ hc.CN x := hc.Q_le_CN hxL
  have hQL : Q ≤ LB M Q B := le_sup_left
  have hLM : LB M Q B ≤ M := hc.LB_le_M
  have hRM : Rt M (LB M Q B) x ≤ M := Rt_le_M hLM x
  have hLR : LB M Q B ≤ Rt M (LB M Q B) x := le_Rt (M := M) (LB M Q B) hxL
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := hc.hyp.Q_normal.2
  have hN2 : IsPGroup 2 ↥(hc.CN x) := isPGroup_CN h34 h311a hs hxL hxQ
  have hYN : Y ⊓ hc.CN x ≤ Q := Y_inf_CN_le_Q h34 h311a hc hs hxL hxQ hQY hYR hYsl
  have hY'N : Y' ⊓ hc.CN x ≤ Q := Y_inf_CN_le_Q h34 h311a hc hs hxL hxQ hQY' hY'R hY'sl
  have hNY'Q : hc.CN x ⊓ Y' = Q :=
    le_antisymm (fun z hz => hY'N ⟨hz.2, hz.1⟩) (le_inf hQN hQY')
  obtain ⟨hYQn, hYmod⟩ := hYsl
  obtain ⟨hYcard, -⟩ := isSLModel_two_data hq4 hq2 hYmod
  have hQYidx : Q.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := hYcard
  obtain ⟨hY'Qn, hY'mod⟩ := hY'sl
  obtain ⟨hY'card, -⟩ := isSLModel_two_data hq4 hq2 hY'mod
  have hQY'idx : Q.relIndex Y' = Nat.card Z * (Nat.card Z ^ 2 - 1) := hY'card
  have e1 : Nat.card ↥Y = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y)
    rw [inf_eq_left.mpr hQY, hQYidx] at this
    exact this.symm
  have e2 : Nat.card ↥Y' = Nat.card Z * (Nat.card Z ^ 2 - 1) * Nat.card ↥Q := by
    have := Subgroup.relIndex_mul_card (H := Q) (K := Y')
    rw [inf_eq_left.mpr hQY', hQY'idx] at this
    exact this.symm
  have hRcard : Nat.card ↥(Rt M (LB M Q B) x) =
      Nat.card ↥(hc.CN x) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) ^ 2 := by
    obtain ⟨K, fK, finK, hK, φ, hφ, hker, -⟩ := hOm
    haveI : CharP K 2 := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact charP_two_of_card_eq_two_pow (hK.trans he)
    have hK4 : 4 ≤ Nat.card K := hK ▸ hq4
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hker, hφ, card_omegaPlus_four hK4, hK] at h1
    have h2 : Nat.card ↥((hc.CN x).subgroupOf (Rt M (LB M Q B) x)) = Nat.card ↥(hc.CN x) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
    rw [h2] at h1
    exact h1.symm
  have hRnN : ∀ r ∈ Rt M (LB M Q B) x, ∀ k ∈ hc.CN x, r * k * r⁻¹ ∈ hc.CN x :=
    fun r hr k hk => hc.CN_conj_mem hxL hr hk
  have hY'nR : ∀ r ∈ Rt M (LB M Q B) x, ∀ y ∈ Y', r * y * r⁻¹ ∈ Y' := fun r hr y hy => by
    have h1 : r * y * r⁻¹ ∈ conjSubgroup r Y' := by
      rw [mem_conjSubgroup, show r⁻¹ * (r * y * r⁻¹) * r = y by group]
      exact hy
    rwa [hnorm r hr] at h1
  have hY'nN : Y' ≤ Subgroup.normalizer ((hc.CN x : Subgroup G) : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype fun k hk => hRnN y (hY'R hy) k hk
  have hNnY' : hc.CN x ≤ Subgroup.normalizer (Y' : Set G) := fun k hk =>
    Subgroup.mem_normalizer_fintype fun y hy => hY'nR k (hNR hk) y hy
  have hRnA : ∀ r ∈ Rt M (LB M Q B) x, ∀ a ∈ hc.CN x ⊔ Y', r * a * r⁻¹ ∈ hc.CN x ⊔ Y' :=
    fun r hr => mem_sup_conj_of_normalizes (hRnN r hr) (hY'nR r hr)
  have hYnA : Y ≤ Subgroup.normalizer ((hc.CN x ⊔ Y' : Subgroup G) : Set G) := fun y hy =>
    Subgroup.mem_normalizer_fintype (hRnA y (hYR hy))
  have hAR : hc.CN x ⊔ Y' ≤ Rt M (LB M Q B) x := sup_le hNR hY'R
  have hQA : Q ≤ hc.CN x ⊔ Y' := hQN.trans le_sup_left
  by_cases hK : (hc.CN x ⊔ Y') ⊓ Y ≤ Q
  ·
    exfalso
    have hAYQ : (hc.CN x ⊔ Y') ⊓ Y = Q := le_antisymm hK (le_inf hQA hQY)
    have hprodA := card_sup_mul_card_inf_of_le_normalizer hY'nN
    rw [hNY'Q, e2] at hprodA
    have hAcard : Nat.card ↥(hc.CN x ⊔ Y') =
        Nat.card ↥(hc.CN x) * (Nat.card Z * (Nat.card Z ^ 2 - 1)) := by
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) ?_
      rw [hprodA]
      ring
    have hprodB := card_sup_mul_card_inf_of_le_normalizer hYnA
    rw [hAYQ, hAcard, e1] at hprodB
    have hRA : hc.CN x ⊔ Y' ⊔ Y = Rt M (LB M Q B) x := by
      refine Subgroup.eq_of_le_of_card_ge (sup_le hAR hYR) (le_of_eq ?_)
      refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := ↥Q)) ?_
      rw [hprodB, hRcard]
      ring
    have hQE : Q ≤ LB M Q B ⊓ X := le_inf hQL hQX
    have hnormEY : (LB M Q B ⊓ X) ≤ Subgroup.normalizer ((LB M Q B ⊓ Y : Subgroup G) : Set G) :=
      normalizer_of_commutator_le (X := LB M Q B ⊓ Y) (Y := LB M Q B ⊓ X)
        (le_inf hQL hQY) fun a ha y hy => by
          have := Q.inv_mem (hcXY y hy.2 a ha.2)
          rwa [commutatorElement_inv] at this
    have hN0E : LB M Q B ⊓ hc.CN x ≤ LB M Q B ⊓ X := by
      intro z hz
      have hLeq : z ∈ (LB M Q B ⊓ X) ⊔ (LB M Q B ⊓ Y) := h4.2.2 ▸ hz.1
      obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_le_normalizer hnormEY hLeq
      have haR : a ∈ Rt M (LB M Q B) x := hLR ha.1
      have hbQ : b ∈ Q := by
        refine mem_of_comm_mem_Q hq4 hq2 hYsl0 hb.2 fun y hy => ?_
        have hzy : ⁅z, y⁆ ∈ hc.CN x := by
          have e : ⁅z, y⁆ = z * (y * z⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
          rw [e]
          exact (hc.CN x).mul_mem hz.2 (hRnN y (hYR hy) z⁻¹ ((hc.CN x).inv_mem hz.2))
        have h1 : a * ⁅b, y⁆ * a⁻¹ ∈ hc.CN x := by
          have e : a * ⁅b, y⁆ * a⁻¹ = ⁅z, y⁆ * ⁅a, y⁆⁻¹ := by
            rw [← hab]
            simp only [commutatorElement_def]
            group
          rw [e]
          exact (hc.CN x).mul_mem hzy ((hc.CN x).inv_mem (hQN (hcXY a ha.2 y hy)))
        have h2 : ⁅b, y⁆ ∈ hc.CN x := by
          have := hRnN a⁻¹ ((Rt M (LB M Q B) x).inv_mem haR) _ h1
          have e : a⁻¹ * (a * ⁅b, y⁆ * a⁻¹) * a⁻¹⁻¹ = ⁅b, y⁆ := by group
          rwa [e] at this
        have h3 : ⁅b, y⁆ ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.mul_mem hb.2 hy) (Y.inv_mem hb.2)) (Y.inv_mem hy)
        exact hYN ⟨h3, h2⟩
      rw [← hab]
      exact (LB M Q B ⊓ X).mul_mem ha (hQE hbQ)
    have hQN0 : Q ≤ LB M Q B ⊓ hc.CN x := le_inf hQL hQN
    have hNcomm : ⁅hc.CN x, hc.CN x⁆ ≤ LB M Q B :=
      sec9NComm_of_311b h34 h311bComm G M Q Z B hc n x hsx
    have hYn0 : Y ≤ Subgroup.normalizer ((LB M Q B ⊓ hc.CN x : Subgroup G) : Set G) := fun y hy =>
      Subgroup.mem_normalizer_fintype fun e he => by
        have he' : e ∈ LB M Q B ⊓ hc.CN x := he
        have e' : y * e * y⁻¹ = ⁅e, y⁆⁻¹ * e := by simp only [commutatorElement_def]; group
        rw [e']
        exact (LB M Q B ⊓ hc.CN x).mul_mem
          ((LB M Q B ⊓ hc.CN x).inv_mem (hQN0 (hcXY e (hN0E he').2 y hy))) he'
    have hY'n0 : Y' ≤ Subgroup.normalizer ((LB M Q B ⊓ hc.CN x : Subgroup G) : Set G) :=
      fun y hy => Subgroup.mem_normalizer_fintype fun e he => by
        have he' : e ∈ LB M Q B ⊓ hc.CN x := he
        have heR : e ∈ Rt M (LB M Q B) x := hLR he'.1
        have e' : y * e * y⁻¹ = ⁅y, e⁆ * e := by simp only [commutatorElement_def]; group
        have h1 : ⁅y, e⁆ ∈ Y' := by
          have e'' : ⁅y, e⁆ = y * (e * y⁻¹ * e⁻¹) := by simp only [commutatorElement_def]; group
          rw [e'']
          exact Y'.mul_mem hy (hY'nR e heR y⁻¹ (Y'.inv_mem hy))
        have h2 : ⁅y, e⁆ ∈ hc.CN x := by
          have e'' : ⁅y, e⁆ = (y * e * y⁻¹) * e⁻¹ := commutatorElement_def y e
          rw [e'']
          exact (hc.CN x).mul_mem (hRnN y (hY'R hy) e he'.2) ((hc.CN x).inv_mem he'.2)
        rw [e']
        exact (LB M Q B ⊓ hc.CN x).mul_mem (hQN0 (hY'N ⟨h1, h2⟩)) he'
    have hNn0 : hc.CN x ≤ Subgroup.normalizer ((LB M Q B ⊓ hc.CN x : Subgroup G) : Set G) :=
      fun n' hn' => Subgroup.mem_normalizer_fintype fun e he => by
        have he' : e ∈ LB M Q B ⊓ hc.CN x := he
        have e' : n' * e * n'⁻¹ = ⁅n', e⁆ * e := by simp only [commutatorElement_def]; group
        have h1 : ⁅n', e⁆ ∈ LB M Q B ⊓ hc.CN x :=
          ⟨hNcomm (Subgroup.commutator_mem_commutator hn' he'.2), by
            have e'' : ⁅n', e⁆ = n' * (e * n'⁻¹ * e⁻¹) := by
              simp only [commutatorElement_def]; group
            rw [e'']
            exact (hc.CN x).mul_mem hn' ((hc.CN x).mul_mem ((hc.CN x).mul_mem he'.2
              ((hc.CN x).inv_mem hn')) ((hc.CN x).inv_mem he'.2))⟩
        rw [e']
        exact (LB M Q B ⊓ hc.CN x).mul_mem h1 he'
    have hRn0 : Rt M (LB M Q B) x ≤
        Subgroup.normalizer ((LB M Q B ⊓ hc.CN x : Subgroup G) : Set G) := by
      rw [← hRA]
      exact sup_le (sup_le hNn0 hY'n0) hYn0
    have hN311 := h311a G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen x hxL hxQ hRne
    have hNN0 : hc.CN x ≤ LB M Q B ⊓ hc.CN x := by
      refine hN311.le.trans (iSup₂_le fun h hh z hz => ?_)
      have hzL : h⁻¹ * z * h ∈ LB M Q B := mem_conjSubgroup.mp hz.1
      have hzN : h⁻¹ * z * h ∈ hc.CN x := by
        have := hRnN h⁻¹ ((Rt M (LB M Q B) x).inv_mem hh) z hz.2
        simpa using this
      have hz0 : h⁻¹ * z * h ∈ LB M Q B ⊓ hc.CN x := ⟨hzL, hzN⟩
      have := (Subgroup.mem_normalizer_iff.mp (hRn0 hh) _).mp hz0
      simpa [mul_assoc] using this
    have hNE : hc.CN x ≤ LB M Q B ⊓ X := hNN0.trans hN0E
    obtain ⟨T, hT⟩ := exists_centLB hc x
    have hYC : Y ≤ centMod M Q (hc.CN x) hQn := fun y hy =>
      ⟨hRM (hYR hy), fun k hk => by
        rw [← commutatorElement_inv]
        exact Q.inv_mem (hcXY k (hNE hk).2 y hy)⟩
    have hY'C : Y' ≤ centMod M Q (hc.CN x) hQn := fun y hy =>
      ⟨hRM (hY'R hy), fun k hk => by
        have heR : k ∈ Rt M (LB M Q B) x := hNR hk
        have h1 : ⁅y, k⁆ ∈ Y' := by
          have e'' : ⁅y, k⁆ = y * (k * y⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
          rw [e'']
          exact Y'.mul_mem hy (hY'nR k heR y⁻¹ (Y'.inv_mem hy))
        have h2 : ⁅y, k⁆ ∈ hc.CN x := by
          have e'' : ⁅y, k⁆ = (y * k * y⁻¹) * k⁻¹ := commutatorElement_def y k
          rw [e'']
          exact (hc.CN x).mul_mem (hRnN y (hY'R hy) k hk) ((hc.CN x).inv_mem hk)
        exact hY'N ⟨h1, h2⟩⟩
    have hNC : hc.CN x ≤ centMod M Q (hc.CN x) hQn := fun n' hn' =>
      ⟨hRM (hNR hn'), fun k hk =>
        hc.commutator_LB_le_Q
          (Subgroup.commutator_mem_commutator (hNE hn').1 (hNE hk).1)⟩
    have hRC : Rt M (LB M Q B) x ≤ centMod M Q (hc.CN x) hQn := by
      rw [← hRA]
      exact sup_le (sup_le hNC hY'C) hYC
    have hNT : hc.CN x ≤ T := fun k hk =>
      (hT k).mpr ⟨(hNE hk).1, fun r hr => (hRC hr).2 k hk⟩
    have hcardT := h311bCard G M Q Z B hc n hs5.width hs5.n_gt hs5.noA2 hs5.gen x hxL hxQ hRne
      (sec9_not_SLNat hsx) T hT
    have hcardN : Nat.card ↥(hc.CN x) ≤ Nat.card ↥T := Subgroup.card_le_of_le hNT
    exact absurd (hs.large x hxL hxQ) (not_lt.mpr (hcardN.trans hcardT))
  ·
    have hKnorm : ∀ y ∈ Y, ∀ k ∈ (hc.CN x ⊔ Y') ⊓ Y, y * k * y⁻¹ ∈ (hc.CN x ⊔ Y') ⊓ Y :=
      fun y hy k hk =>
        ⟨hRnA y (hYR hy) k hk.1, Y.mul_mem (Y.mul_mem hy hk.2) (Y.inv_mem hy)⟩
    have hAY : (hc.CN x ⊔ Y') ⊓ Y = Y :=
      eq_of_normal_of_ne_Q hq4 hq2 hYsl0 (le_inf hQA hQY) inf_le_right hKnorm hK
    have hYA : Y ≤ hc.CN x ⊔ Y' := inf_eq_right.mp hAY
    have hYnY' : Y ≤ Subgroup.normalizer (Y' : Set G) := fun y hy =>
      Subgroup.mem_normalizer_fintype fun k hk => hY'nR y (hYR hy) k hk
    have hYY' : Y ≤ Y' := by
      by_cases hK2 : Y ⊓ Y' ≤ Q
      · exfalso
        have hKQ : Y ⊓ Y' = Q := le_antisymm hK2 (le_inf hQY hQY')
        have h1 : Y'.relIndex Y = Nat.card Z * (Nat.card Z ^ 2 - 1) := by
          rw [← Subgroup.inf_relIndex_right Y' Y, inf_comm, hKQ, hQYidx]
        have h2 := relIndex_dvd_of_normalizes (A := Y) (B := Y') (C := hc.CN x ⊔ Y') hYA
          le_sup_right hYnY'
        have h3 : Y'.relIndex (hc.CN x ⊔ Y') = Y'.relIndex (hc.CN x) :=
          relIndex_sup_right_of_le_normalizer hNnY'
        obtain ⟨k, hk⟩ := relIndex_two_pow_of_isPGroup Y' hN2
        rw [h1, h3, hk] at h2
        exact not_dvd_two_pow_of_sq_sub_one hq4 hqev h2
      · have hKn : ∀ y ∈ Y, ∀ k ∈ Y ⊓ Y', y * k * y⁻¹ ∈ Y ⊓ Y' := fun y hy k hk =>
          ⟨Y.mul_mem (Y.mul_mem hy hk.1) (Y.inv_mem hy), hY'nR y (hYR hy) k hk.2⟩
        have := eq_of_normal_of_ne_Q hq4 hq2 hYsl0 (le_inf hQY hQY') inf_le_left hKn hK2
        exact this ▸ inf_le_right
    exact (Subgroup.eq_of_le_of_card_ge hYY' (by rw [e1, e2])).symm

end HS9

theorem sec97OneOmega_of (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bCard : Stroth311bCardStatement) (h311bComm : Stroth311bCommStatement)
    (h95 : Stroth95Statement) : Sec97OneOmega := by
  intro G _ _ M Q Z B hc n t hs X Y hsplit h4 x hx hxQ hOm
  have hs5 := hs.toSec5
  have hxL : x ∈ LB M Q B := hx.1
  have hsx : Sec9Hyp hc n x :=
    ⟨⟨hs5.width, hs5.n_gt, hs5.noA2, hs5.gen, hxL, hxQ⟩, hOm, hs.large⟩
  obtain ⟨X', Y', hsplit'⟩ := h95 G M Q Z B hc n x hsx
  obtain ⟨⟨hQX', hX'R, hQY', hY'R, hXY', hXYQ', hcXY'⟩, hY'sl, -⟩ := hsplit'
  have hX'n : X' ≤ Subgroup.normalizer (Y' : Set G) :=
    HS9.normalizer_of_commutator_le (X := Y') (Y := X') hQY' fun a ha y hy => by
      have := Q.inv_mem (hcXY' y hy a ha)
      rwa [commutatorElement_inv] at this
  have hnorm' : ∀ r ∈ Rt M (LB M Q B) x, conjSubgroup r Y' = Y' := by
    intro r hr
    rw [← hXY'] at hr
    exact conjSubgroup_eq_self_iff.mpr ((sup_le hX'n Subgroup.le_normalizer : _ ≤ _) hr)
  have hY' : Y' = Y := HS9.normal_eq_Y h34 h311a h311bCard h311bComm hc hs hsplit h4 hx hxQ hOm
    hQY' hY'R hnorm' hY'sl
  exact ⟨fun r hr => hY' ▸ hnorm' r hr, fun Y'' hQ hR hn hsl =>
    HS9.normal_eq_Y h34 h311a h311bCard h311bComm hc hs hsplit h4 hx hxQ hOm hQ hR hn hsl⟩

end CFSG.RankThree.GF2n.Stroth80
