module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.NormalForm
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem exists_sq_eq_neg_one_commute {g : SL5} (hg : g ^ 4 = 1) :
    ∃ g' : SL5, g' ^ 2 = -1 ∧ Commute g g' := by
  have hg2 : g ^ 2 * g ^ 2 = 1 := by
    rw [← pow_two, ← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num, hg]
  rcases sl5_eq_one_or_neg_one_of_mul_self hg2 with hsq | hsq
  · have hg1 : g * g = 1 := by rwa [pow_two] at hsq
    rcases sl5_eq_one_or_neg_one_of_mul_self hg1 with hg1 | hgneg
    · exact ⟨hM, hM_sq, by rw [hg1]; exact Commute.one_left hM⟩
    · exact ⟨hM, hM_sq, by rw [hgneg, commute_iff_eq]; decide⟩
  · exact ⟨g, hsq, Commute.refl g⟩

theorem WongHyp.x_ne_t (h : WongHyp t i₁.range i₂.range) (hi₁ : Function.Injective i₁)
    (hi₂ : Function.Injective i₂) : i₁ hM * i₂ hM ≠ t := by
  intro hxt
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have ht : t = i₁ (-1) := eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq
  have heq : i₁ (-1) * i₂ 1 = i₁ hM * i₂ hM := by
    rw [map_one, mul_one, ← ht]
    exact hxt.symm
  have hkey := (prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcomm h.inf_eq
    (x := (-1 : SL5)) (y := 1) (x' := hM) (y' := hM)).mp heq
  have hne : hM ≠ (-1 : SL5) := by decide
  exact hne (hkey.elim (fun hh => hh.1) fun hh => hh.2)

theorem WongHyp.commutator_hM_y (h : WongHyp t i₁.range i₂.range) (hi₁ : Function.Injective i₁) :
    ⁅i₁ hM, i₁ cM * i₂ cM⁆ = t := by
  have hac : Commute (i₁ hM) (i₂ cM) := h.commute _ ⟨hM, rfl⟩ _ ⟨cM, rfl⟩
  rw [commutatorElement_mul_right_eq_mul_conj, hac.commutator_eq, mul_one, mul_inv_cancel_right]
  rw [← map_commutatorElement]
  have hmat : ⁅hM, cM⁆ = (-1 : SL5) := by decide
  rw [hmat]
  exact (eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq).symm

theorem WongHyp.exists_mem_sup_conj_eq (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {v : G}
    (hvK : v ∈ i₁.range ⊔ i₂.range) (hv : orderOf v = 2) (hvt : v ≠ t) :
    ∃ k ∈ i₁.range ⊔ i₂.range, k * (i₁ hM * i₂ hM) * k⁻¹ = v := by
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨g, g', hgg⟩ := (mem_sup_iff hcomm).mp hvK
  have hv2 : v ^ 2 = 1 := by
    have := pow_orderOf_eq_one v
    rwa [hv] at this
  have hsq : i₁ (g * g) * i₂ (g' * g') = 1 := by
    have h2 : prodHom hcomm ((g, g') * (g, g')) = 1 := by
      rw [map_mul]
      simp only [prodHom_apply, hgg, ← pow_two, hv2]
    rwa [Prod.mk_mul_mk, prodHom_apply] at h2
  rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp hsq with
    ⟨hg1, hg2⟩ | ⟨hg1, hg2⟩
  · exfalso
    have hv1 : v = 1 ∨ v = t := by
      rw [← hgg]
      rcases sl5_eq_one_or_neg_one_of_mul_self hg1 with rfl | rfl <;>
        rcases sl5_eq_one_or_neg_one_of_mul_self hg2 with rfl | rfl
      · left; simp
      · right; rw [map_one, one_mul]
        exact (eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq).symm
      · right; rw [map_one, mul_one]
        exact (eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq).symm
      · left
        rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq,
          ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq, ← pow_two, ← h.orderOf_t,
          pow_orderOf_eq_one]
    rcases hv1 with h1 | h1
    · rw [h1, orderOf_one] at hv
      norm_num at hv
    · exact hvt h1
  · obtain ⟨p, hp⟩ := exists_conj_hM_of_sq_eq_neg_one (x := g) (by rw [pow_two]; exact hg1)
    obtain ⟨q, hq⟩ := exists_conj_hM_of_sq_eq_neg_one (x := g') (by rw [pow_two]; exact hg2)
    have hp' : p⁻¹ * hM * p = g := by rw [← hp]; group
    have hq' : q⁻¹ * hM * q = g' := by rw [← hq]; group
    refine ⟨i₁ p⁻¹ * i₂ q⁻¹, ?_, ?_⟩
    · exact mul_mem (mem_sup_left ⟨p⁻¹, rfl⟩) (mem_sup_right ⟨q⁻¹, rfl⟩)
    · calc
        (i₁ p⁻¹ * i₂ q⁻¹) * (i₁ hM * i₂ hM) * (i₁ p⁻¹ * i₂ q⁻¹)⁻¹
            = prodHom hcomm (p⁻¹, q⁻¹) * prodHom hcomm (hM, hM) *
                (prodHom hcomm (p⁻¹, q⁻¹))⁻¹ := rfl
        _ = prodHom hcomm ((p⁻¹, q⁻¹) * (hM, hM) * (p, q)) := by
              rw [show (prodHom hcomm (p⁻¹, q⁻¹))⁻¹ = prodHom hcomm (p, q) by
                    rw [← map_inv]; simp,
                  ← map_mul, ← map_mul]
        _ = prodHom hcomm (p⁻¹ * hM * p, q⁻¹ * hM * q) := by simp [Prod.mk_mul_mk]
        _ = i₁ (p⁻¹ * hM * p) * i₂ (q⁻¹ * hM * q) :=
              prodHom_apply hcomm (p⁻¹ * hM * p, q⁻¹ * hM * q)
        _ = i₁ g * i₂ g' := by rw [hp', hq']
        _ = v := hgg

theorem WongHyp.isConj_x_of_commute_sq_eq [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {v a : G} (hv : IsConj t v)
    (hvt : v ≠ t) (ha : Commute a v) (ha2 : a ^ 2 = t) : IsConj t (i₁ hM * i₂ hM) := by
  obtain ⟨c, hcv⟩ := isConj_iff.mp hv
  have hct : c⁻¹ * v * c = t := by rw [← hcv]; group
  have hcomm_a't : Commute (c⁻¹ * a * c) t := by
    rw [← hct, commute_iff_eq]
    calc c⁻¹ * a * c * (c⁻¹ * v * c) = c⁻¹ * (a * v) * c := by group
      _ = c⁻¹ * (v * a) * c := by rw [ha.eq]
      _ = (c⁻¹ * v * c) * (c⁻¹ * a * c) := by group
  have ha'C : c⁻¹ * a * c ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_a't.eq
  set w : G := c⁻¹ * t * c with hw
  have hwK : w ∈ i₁.range ⊔ i₂.range := by
    have h1 : (c⁻¹ * a * c) ^ 2 ∈ i₁.range ⊔ i₂.range := h.sq_mem_sup ha'C
    have h2 : (c⁻¹ * a * c) ^ 2 = w := by
      rw [show (c⁻¹ * a * c) ^ 2 = c⁻¹ * a ^ 2 * c by rw [pow_two, pow_two]; group,
        ha2, ← hw]
    rwa [h2] at h1
  have ht2 : t ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.orderOf_t] at this
  have hw2 : w ^ 2 = 1 := by
    rw [hw, show (c⁻¹ * t * c) ^ 2 = c⁻¹ * t ^ 2 * c by rw [pow_two, pow_two]; group,
      ht2]
    group
  have hw_ne : w ≠ 1 := by
    intro h1
    have hwt1 : c⁻¹ * t * c = 1 := hw ▸ h1
    have ht1 : t = 1 := by
      calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
        _ = c * 1 * c⁻¹ := by rw [hwt1]
        _ = 1 := by group
    have h2 : orderOf t = 1 := by rw [ht1, orderOf_one]
    have h3 : orderOf t = 2 := h.orderOf_t
    omega
  have hw_order : orderOf w = 2 := orderOf_eq_prime hw2 hw_ne
  have hw_ne_t : w ≠ t := by
    intro hwt
    apply hvt
    have hwt' : c⁻¹ * t * c = t := hw ▸ hwt
    have : c * t * c⁻¹ = t := by
      calc c * t * c⁻¹ = c * (c⁻¹ * t * c) * c⁻¹ := by rw [hwt']
        _ = t := by group
    exact hcv ▸ this
  obtain ⟨k, hkK, hkx⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hwK hw_order hw_ne_t
  have hisConj_xw : IsConj (i₁ hM * i₂ hM) w := isConj_iff.mpr ⟨k, hkx⟩
  have hisConj_wt : IsConj w t := isConj_iff.mpr ⟨c, by rw [hw]; group⟩
  exact (hisConj_xw.trans hisConj_wt).symm

end CFSG.OddTranspositions.PartThree.Wong
