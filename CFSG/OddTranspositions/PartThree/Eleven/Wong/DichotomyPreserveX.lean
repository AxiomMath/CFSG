module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyInvol
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyCentX
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement
open CFSG.ABGLocalTools

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.not_isConj_x_of_trivial [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ x ∧ n⁻¹ * i₂ x * n = i₂ x) :
    ¬ IsConj t (i₁ hM * i₂ hM) := by
  intro hconj
  let K : Subgroup G := i₁.range ⊔ i₂.range
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  let x : G := i₁ hM * i₂ hM
  let y : G := i₁ cM * i₂ cM
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let U : Subgroup G := C ⊓ Cx
  have hcommK : ∀ a ∈ K, Commute a n := by
    have h₁ : i₁.range ≤ Subgroup.centralizer ({n} : Set G) := by
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc i₁ g * n = n * (n⁻¹ * i₁ g * n) := by group
        _ = n * i₁ g := by rw [(hact g).1]
    have h₂ : i₂.range ≤ Subgroup.centralizer ({n} : Set G) := by
      rintro _ ⟨g, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc i₂ g * n = n * (n⁻¹ * i₂ g * n) := by group
        _ = n * i₂ g := by rw [(hact g).2]
    intro a ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (sup_le h₁ h₂ ha)
  have hnx : Commute n x := by
    have h1 : Commute n (i₁ hM) := (hcommK (i₁ hM) (mem_sup_left ⟨hM, rfl⟩)).symm
    have h2 : Commute n (i₂ hM) := (hcommK (i₂ hM) (mem_sup_right ⟨hM, rfl⟩)).symm
    exact h1.mul_right h2
  have hxy : Commute y x := by
    have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
      fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hrel : hM * cM = (-1 : SL5) * (cM * hM) := by decide
    have ht1 : i₁ (-1) = t := by
      have hmem : t ∈ i₁.range := by
        have hz := Subgroup.mem_zpowers t
        rw [← h.inf_eq] at hz
        exact hz.1
      exact (eq_apply_neg_one hi₁ h.orderOf_t hmem).symm
    have ht2 : i₂ (-1) = t := by
      have hmem : t ∈ i₂.range := by
        have hz := Subgroup.mem_zpowers t
        rw [← h.inf_eq] at hz
        exact hz.2
      exact (eq_apply_neg_one hi₂ h.orderOf_t hmem).symm
    have htt : t * t = 1 := by
      rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
    have hphi : prodHom hcomm ((-1 : SL5), (-1 : SL5)) = 1 := by
      rw [prodHom_apply, ht1, ht2, htt]
    have hmain : x * y = y * x := by
      calc x * y = prodHom hcomm (hM, hM) * prodHom hcomm (cM, cM) := rfl
        _ = prodHom hcomm ((hM, hM) * (cM, cM)) :=
              (map_mul (prodHom hcomm) (hM, hM) (cM, cM)).symm
        _ = prodHom hcomm (hM * cM, hM * cM) := rfl
        _ = prodHom hcomm ((-1 : SL5) * (cM * hM), (-1 : SL5) * (cM * hM)) := by rw [hrel]
        _ = prodHom hcomm ((-1, -1) * (cM * hM, cM * hM)) := rfl
        _ = prodHom hcomm (-1, -1) * prodHom hcomm (cM * hM, cM * hM) :=
              map_mul (prodHom hcomm) (-1, -1) (cM * hM, cM * hM)
        _ = 1 * prodHom hcomm (cM * hM, cM * hM) := by rw [hphi]
        _ = prodHom hcomm (cM * hM, cM * hM) := one_mul _
        _ = prodHom hcomm (cM, cM) * prodHom hcomm (hM, hM) :=
              map_mul (prodHom hcomm) (cM, cM) (hM, hM)
        _ = y * x := rfl
    exact hmain.symm
  have hpx : ∀ p ∈ U, Commute p x := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp hp.2
  have decomp : ∀ p ∈ U, ∃ k ∈ K, p = k ∨ p = k * n := by
    intro p hp
    by_cases hpK : p ∈ K
    · exact ⟨p, hpK, Or.inl rfl⟩
    · refine ⟨p * n⁻¹, ?_, Or.inr ?_⟩
      · exact h.mul_mem_sup_of_not_mem hp.1 (C.inv_mem hn) hpK (fun hh =>
          hnK (by simpa using K.inv_mem hh))
      · group
  have hred_r : ∀ k ∈ K, ∀ k' ∈ K, ⁅k, k' * n⁆ = ⁅k, k'⁆ := by
    intro k hk k' hk'
    rw [commutatorElement_mul_right_eq_mul_conj, (hcommK k hk).commutator_eq]
    group
  have hred_l : ∀ k ∈ K, ∀ k' ∈ K, ⁅k * n, k'⁆ = ⁅k, k'⁆ := by
    intro k hk k' hk'
    rw [commutatorElement_mul_left_eq_conj_mul, (hcommK k' hk').symm.commutator_eq]
    group
  have hred_b : ∀ k ∈ K, ∀ k' ∈ K, ⁅k * n, k' * n⁆ = ⁅k, k'⁆ := by
    intro k hk k' hk'
    rw [commutatorElement_mul_left_eq_conj_mul, hred_r k hk k' hk',
      ((hcommK k' hk').symm.mul_right (Commute.refl n)).commutator_eq]
    group
  have hUcomm : ∀ p ∈ U, ∀ q ∈ U, ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = t := by
    intro p hp q hq
    obtain ⟨kp, hkpK, hpkp | hpkp⟩ := decomp p hp
    · have hkpx : Commute kp x := hpkp ▸ hpx p hp
      obtain ⟨kq, hkqK, hqkq | hqkq⟩ := decomp q hq
      · have hkqx : Commute kq x := hqkq ▸ hpx q hq
        rw [hpkp, hqkq]
        exact h.commutator_eq_of_commute_x hi₁ hi₂ hkpK hkqK hkpx hkqx
      · have hkqx : Commute kq x := by
          have h1 : Commute (kq * n) x := hqkq ▸ hpx q hq
          have h3 : kq = (kq * n) * n⁻¹ := by group
          rw [h3]
          exact h1.mul_left hnx.inv_left
        rw [hpkp, hqkq, hred_r kp hkpK kq hkqK]
        exact h.commutator_eq_of_commute_x hi₁ hi₂ hkpK hkqK hkpx hkqx
    · have hkpx : Commute kp x := by
        have h1 : Commute (kp * n) x := hpkp ▸ hpx p hp
        have h3 : kp = (kp * n) * n⁻¹ := by group
        rw [h3]
        exact h1.mul_left hnx.inv_left
      obtain ⟨kq, hkqK, hqkq | hqkq⟩ := decomp q hq
      · have hkqx : Commute kq x := hqkq ▸ hpx q hq
        rw [hpkp, hqkq, hred_l kp hkpK kq hkqK]
        exact h.commutator_eq_of_commute_x hi₁ hi₂ hkpK hkqK hkpx hkqx
      · have hkqx : Commute kq x := by
          have h1 : Commute (kq * n) x := hqkq ▸ hpx q hq
          have h3 : kq = (kq * n) * n⁻¹ := by group
          rw [h3]
          exact h1.mul_left hnx.inv_left
        rw [hpkp, hqkq, hred_b kp hkpK kq hkqK]
        exact h.commutator_eq_of_commute_x hi₁ hi₂ hkpK hkqK hkpx hkqx
  have hhm : i₁ hM ∈ U := by
    refine ⟨h.sup_le_centralizer (mem_sup_left ⟨hM, rfl⟩), ?_⟩
    show i₁ hM ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    show i₁ hM * (i₁ hM * i₂ hM) = (i₁ hM * i₂ hM) * i₁ hM
    rw [mul_assoc, (h.commute (i₁ hM) ⟨hM, rfl⟩ (i₂ hM) ⟨hM, rfl⟩).eq.symm]
  have hyU : y ∈ U := by
    refine ⟨C.mul_mem (h.sup_le_centralizer (mem_sup_left ⟨cM, rfl⟩))
      (h.sup_le_centralizer (mem_sup_right ⟨cM, rfl⟩)), ?_⟩
    show y ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hxy.eq
  have hcom : ⁅i₁ hM, y⁆ = t := h.commutator_hM_y hi₁
  have ht_ne : t ≠ 1 := by
    intro h1
    have h2 := h.orderOf_t
    rw [h1, orderOf_one] at h2
    norm_num at h2
  have hN : Subgroup.normalizer (U : Set G) ⊓ Cx ≤ C :=
    inf_le_left.trans (normalizer_le_centralizer_of_commutator ht_ne hUcomm hhm hyU hcom)
  have hU2 : IsSylowOf 2 U U := by
    rw [isSylowOf_iff]
    refine ⟨le_refl U, IsPGroup.of_card_dvd_pow (n := 5) ?_, ?_⟩
    · simpa only [show (2 : ℕ) ^ 5 = 32 by norm_num] using h.card_centralizer_inf_dvd hi₁ hi₂
    · rw [Subgroup.relIndex_self]
      norm_num
  have h64 : Nat.card U = 64 := h.card_eq_sixtyFour_of_isSylowOf hconj hU2 hN
  have hdvd : Nat.card U ∣ 32 := h.card_centralizer_inf_dvd hi₁ hi₂
  exact absurd (h64 ▸ hdvd) (by decide)

theorem WongHyp.not_isConj_x_of_outer_one [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G))
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ x) :
    ¬ IsConj t (i₁ hM * i₂ hM) := by
  intro hconj
  let x : G := i₁ hM * i₂ hM
  let y : G := i₁ cM * i₂ cM
  let m : G := n * i₁ cM
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hc' : c * t * c⁻¹ = x := hc
  have ht1 : i₁ (-1) = t := by
    have hmem : t ∈ i₁.range := by
      have hz := Subgroup.mem_zpowers t
      rw [← h.inf_eq] at hz
      exact hz.1
    exact (eq_apply_neg_one hi₁ h.orderOf_t hmem).symm
  have ht2 : i₂ (-1) = t := by
    have hmem : t ∈ i₂.range := by
      have hz := Subgroup.mem_zpowers t
      rw [← h.inf_eq] at hz
      exact hz.2
    exact (eq_apply_neg_one hi₂ h.orderOf_t hmem).symm
  have htt : t * t = 1 := by
    rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
  have hcx : c⁻¹ * x * c = t := by
    calc c⁻¹ * x * c = c⁻¹ * (c * t * c⁻¹) * c := by rw [← hc']
      _ = t := by group
  have hxy : Commute y x := by
    have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
      fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have hrel : hM * cM = (-1 : SL5) * (cM * hM) := by decide
    have hphi : prodHom hcomm ((-1 : SL5), (-1 : SL5)) = 1 := by
      rw [prodHom_apply, ht1, ht2, htt]
    have hmain : x * y = y * x := by
      calc x * y = prodHom hcomm (hM, hM) * prodHom hcomm (cM, cM) := rfl
        _ = prodHom hcomm ((hM, hM) * (cM, cM)) :=
              (map_mul (prodHom hcomm) (hM, hM) (cM, cM)).symm
        _ = prodHom hcomm (hM * cM, hM * cM) := rfl
        _ = prodHom hcomm ((-1 : SL5) * (cM * hM), (-1 : SL5) * (cM * hM)) := by rw [hrel]
        _ = prodHom hcomm ((-1, -1) * (cM * hM, cM * hM)) := rfl
        _ = prodHom hcomm (-1, -1) * prodHom hcomm (cM * hM, cM * hM) :=
              map_mul (prodHom hcomm) (-1, -1) (cM * hM, cM * hM)
        _ = 1 * prodHom hcomm (cM * hM, cM * hM) := by rw [hphi]
        _ = prodHom hcomm (cM * hM, cM * hM) := one_mul _
        _ = prodHom hcomm (cM, cM) * prodHom hcomm (hM, hM) :=
              map_mul (prodHom hcomm) (cM, cM) (hM, hM)
        _ = y * x := rfl
    exact hmain.symm
  have hmx : Commute m x := by
    have h1 : n⁻¹ * i₁ hM * n = i₁ hM⁻¹ := by
      have hh := (hact hM).1
      rwa [deltaAut_hM] at hh
    have h2 : n⁻¹ * i₂ hM * n = i₂ hM := (hact hM).2
    have h3 : (i₁ cM)⁻¹ * i₁ hM⁻¹ * i₁ cM = i₁ hM := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      have h4 : cM⁻¹ * hM⁻¹ * cM = (cM⁻¹ * hM * cM)⁻¹ := by group
      rw [h4, cM_inv_mul_hM_mul_cM, inv_inv]
    have hmx' : m⁻¹ * x * m = x := by
      calc m⁻¹ * x * m
          = (i₁ cM)⁻¹ * (n⁻¹ * i₁ hM * n) * (n⁻¹ * i₂ hM * n) * i₁ cM := by
              show (n * i₁ cM)⁻¹ * (i₁ hM * i₂ hM) * (n * i₁ cM) = _
              rw [mul_inv_rev]
              group
        _ = (i₁ cM)⁻¹ * i₁ hM⁻¹ * i₂ hM * i₁ cM := by rw [h1, h2]
        _ = (i₁ cM)⁻¹ * i₁ hM⁻¹ * i₁ cM * i₂ hM := by
              rw [show (i₁ cM)⁻¹ * i₁ hM⁻¹ * i₂ hM * i₁ cM
                    = (i₁ cM)⁻¹ * i₁ hM⁻¹ * (i₂ hM * i₁ cM) by group,
                  (h.commute (i₁ cM) ⟨cM, rfl⟩ (i₂ hM) ⟨hM, rfl⟩).eq.symm]
              group
        _ = i₁ hM * i₂ hM := by rw [h3]
        _ = x := rfl
    rw [commute_iff_eq]
    calc m * x = m * (m⁻¹ * x * m) := by rw [hmx']
      _ = x * m := by group
  have hmym : m⁻¹ * y * m = i₁ (hM * cM) * i₂ cM := by
    have h1 : n⁻¹ * i₁ cM * n = i₁ (deltaAut cM) := (hact cM).1
    have h2 : n⁻¹ * i₂ cM * n = i₂ cM := (hact cM).2
    calc m⁻¹ * y * m
        = (i₁ cM)⁻¹ * (n⁻¹ * i₁ cM * n) * (n⁻¹ * i₂ cM * n) * i₁ cM := by
            show (n * i₁ cM)⁻¹ * (i₁ cM * i₂ cM) * (n * i₁ cM) = _
            rw [mul_inv_rev]
            group
      _ = (i₁ cM)⁻¹ * i₁ (deltaAut cM) * i₂ cM * i₁ cM := by rw [h1, h2]
      _ = i₁ (hM * cM) * i₂ cM := by
            rw [deltaAut_cM, ← map_inv, ← map_mul]
            have hc1 : cM⁻¹ * (cM * hM) = hM := by group
            rw [hc1]
            rw [show i₁ hM * i₂ cM * i₁ cM = i₁ hM * (i₂ cM * i₁ cM) by group,
                (h.commute (i₁ cM) ⟨cM, rfl⟩ (i₂ cM) ⟨cM, rfl⟩).eq.symm,
                ← mul_assoc (i₁ hM) (i₁ cM) (i₂ cM), ← map_mul]
  let e : G := ⁅y⁻¹, m⁻¹⁆
  have he : e = i₁ hM⁻¹ := by
    have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
      fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    calc e = ⁅y⁻¹, m⁻¹⁆ := rfl
      _ = y⁻¹ * (m⁻¹ * y * m) := by rw [commutatorElement_def, inv_inv]; group
      _ = y⁻¹ * (i₁ (hM * cM) * i₂ cM) := by rw [hmym]
      _ = prodHom hcomm (cM⁻¹, cM⁻¹) * prodHom hcomm (hM * cM, cM) := by
            rw [show y⁻¹ = prodHom hcomm (cM⁻¹, cM⁻¹) by
                  rw [show y = prodHom hcomm (cM, cM) from rfl, ← map_inv, Prod.inv_mk]]
            rfl
      _ = prodHom hcomm ((cM⁻¹, cM⁻¹) * (hM * cM, cM)) :=
            (map_mul (prodHom hcomm) (cM⁻¹, cM⁻¹) (hM * cM, cM)).symm
      _ = prodHom hcomm (cM⁻¹ * (hM * cM), cM⁻¹ * cM) := rfl
      _ = prodHom hcomm (hM⁻¹, 1) := by
            rw [show cM⁻¹ * (hM * cM) = hM⁻¹ by
                  rw [← mul_assoc, cM_inv_mul_hM_mul_cM],
                inv_mul_cancel]
      _ = i₁ hM⁻¹ := by rw [prodHom_apply, map_one, mul_one]
  have hc_inv_y : c⁻¹ * y⁻¹ * c ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hcx]
    rw [show (c⁻¹ * y⁻¹ * c) * (c⁻¹ * x * c) = c⁻¹ * (y⁻¹ * x) * c by group,
        show (c⁻¹ * x * c) * (c⁻¹ * y⁻¹ * c) = c⁻¹ * (x * y⁻¹) * c by group,
        (hxy.inv_left).eq]
  have hc_inv_m : c⁻¹ * m⁻¹ * c ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← hcx]
    rw [show (c⁻¹ * m⁻¹ * c) * (c⁻¹ * x * c) = c⁻¹ * (m⁻¹ * x) * c by group,
        show (c⁻¹ * x * c) * (c⁻¹ * m⁻¹ * c) = c⁻¹ * (x * m⁻¹) * c by group,
        (hmx.inv_left).eq]
  have heK : c⁻¹ * e * c ∈ i₁.range ⊔ i₂.range := by
    have hconj : c⁻¹ * e * c = ⁅c⁻¹ * y⁻¹ * c, c⁻¹ * m⁻¹ * c⁆ := by
      show c⁻¹ * ⁅y⁻¹, m⁻¹⁆ * c = _
      simpa only [inv_inv] using conjugate_commutatorElement y⁻¹ m⁻¹ c⁻¹
    have hmem : c⁻¹ * e * c ∈
        ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
      rw [hconj]
      exact Subgroup.commutator_mem_commutator hc_inv_y hc_inv_m
    rwa [h.commutator_centralizer] at hmem
  have hM_orderOf : orderOf hM = 4 := by
    apply (orderOf_eq_iff (n := 4) (by norm_num)).mpr
    refine ⟨by decide, ?_⟩
    intro k hk4 hk0
    interval_cases k <;> decide
  have horder : orderOf (c⁻¹ * e * c) = 4 := by
    have hsem : SemiconjBy c⁻¹ e (c⁻¹ * e * c) := by
      show c⁻¹ * e = (c⁻¹ * e * c) * c⁻¹
      group
    rw [← SemiconjBy.orderOf_eq c⁻¹ hsem, he,
        orderOf_injective i₁ hi₁ hM⁻¹, orderOf_inv]
    exact hM_orderOf
  have hsq := h.sq_eq_of_mem_sup_of_orderOf_eq_four hi₁ hi₂ heK horder
  have he2x : e ^ 2 = x := by
    have h' : c⁻¹ * e ^ 2 * c = t := by
      rw [← hsq, pow_two, pow_two]
      group
    calc e ^ 2 = c * (c⁻¹ * e ^ 2 * c) * c⁻¹ := by group
      _ = c * t * c⁻¹ := by rw [h']
      _ = x := hc'
  have he2t : e ^ 2 = t := by
    rw [he, pow_two, ← map_mul]
    have hsq' : hM⁻¹ * hM⁻¹ = -1 := by
      rw [← mul_inv_rev, ← pow_two, hM_sq, sl5_inv_neg_one]
    rw [hsq', ht1]
  exact h.x_ne_t hi₁ hi₂ (by change x = t; rw [← he2x, he2t])

end CFSG.OddTranspositions.PartThree.Wong
