module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyInvol
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyCentX
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.isConj_n_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = 1)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) {v : G}
    (hvC : v ∈ centralizer ({t} : Set G)) (hvK : v ∉ i₁.range ⊔ i₂.range) (hv : v ^ 2 = 1) :
    IsConj n v := by
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hn_mul : n * n = 1 := by rw [← pow_two]; exact hn2
  have hn_inv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn_mul
  have hvnK : v * n ∈ i₁.range ⊔ i₂.range := h.mul_mem_sup_of_not_mem hvC hn hvK hnK
  obtain ⟨g, g', hgv⟩ := (mem_sup_iff hcomm).mp hvnK
  have hv_eq : v = i₁ g * i₂ g' * n := by
    rw [hgv, mul_assoc, ← pow_two, hn2, mul_one]
  have hconj₁ : n * i₁ g * n⁻¹ = i₁ (deltaAut g) := by
    simpa only [hn_inv] using (hact g).1
  have hconj₂ : n * i₂ g' * n⁻¹ = i₂ (deltaAut g') := by
    simpa only [hn_inv] using (hact g').2
  have hconj : n * (i₁ g * i₂ g') * n⁻¹ = i₁ (deltaAut g) * i₂ (deltaAut g') := by
    rw [show n * (i₁ g * i₂ g') * n⁻¹ = (n * i₁ g * n⁻¹) * (n * i₂ g' * n⁻¹) by group,
      hconj₁, hconj₂]
  have hvsq : v ^ 2 = i₁ (g * deltaAut g) * i₂ (g' * deltaAut g') := by
    have e : v ^ 2 = i₁ g * i₂ g' * (n * (i₁ g * i₂ g') * n) := by
      rw [hv_eq, pow_two]
      group
    rw [e, show n * (i₁ g * i₂ g') * n = n * (i₁ g * i₂ g') * n⁻¹ by rw [hn_inv], hconj]
    rw [map_mul, map_mul]
    rw [show i₁ g * i₂ g' * (i₁ (deltaAut g) * i₂ (deltaAut g'))
          = i₁ g * (i₂ g' * i₁ (deltaAut g)) * i₂ (deltaAut g') by group]
    rw [← (hcomm (deltaAut g) g').eq]
    group
  have hprod : i₁ (g * deltaAut g) * i₂ (g' * deltaAut g') = 1 := by
    rw [← hvsq, hv]
  have hg1 : g * deltaAut g = 1 := by
    rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp hprod with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (mul_deltaAut_ne_neg_one g)
  have hg2 : g' * deltaAut g' = 1 := by
    rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp hprod with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (mul_deltaAut_ne_neg_one g')
  obtain ⟨r, hr⟩ := exists_mul_eq_deltaAut hg1
  obtain ⟨s, hs⟩ := exists_mul_eq_deltaAut hg2
  have hrg : r⁻¹ * deltaAut r = g := by rw [← hr]; group
  have hsg : s⁻¹ * deltaAut s = g' := by rw [← hs]; group
  have hkey₁ : ∀ z : SL5, (i₁ z)⁻¹ * n * (i₁ z) = i₁ (z⁻¹ * deltaAut z) * n := by
    intro z
    have hz : n * i₁ z = i₁ (deltaAut z) * n := by
      have h1 : n * i₁ z * n⁻¹ = i₁ (deltaAut z) := by
        have hz' := (hact (deltaAut z)).1
        rw [deltaAut_deltaAut] at hz'
        calc n * i₁ z * n⁻¹ = n * (n⁻¹ * i₁ (deltaAut z) * n) * n⁻¹ := by rw [hz']
          _ = i₁ (deltaAut z) := by group
      calc n * i₁ z = n * i₁ z * n⁻¹ * n := by group
        _ = i₁ (deltaAut z) * n := by rw [h1]
    calc (i₁ z)⁻¹ * n * (i₁ z) = (i₁ z)⁻¹ * (n * i₁ z) := by group
      _ = (i₁ z)⁻¹ * (i₁ (deltaAut z) * n) := by rw [hz]
      _ = i₁ (z⁻¹ * deltaAut z) * n := by
            rw [map_mul, map_inv]
            group
  have hkey₂ : ∀ z : SL5, (i₂ z)⁻¹ * n * (i₂ z) = i₂ (z⁻¹ * deltaAut z) * n := by
    intro z
    have hz : n * i₂ z = i₂ (deltaAut z) * n := by
      have h1 : n * i₂ z * n⁻¹ = i₂ (deltaAut z) := by
        have hz' := (hact (deltaAut z)).2
        rw [deltaAut_deltaAut] at hz'
        calc n * i₂ z * n⁻¹ = n * (n⁻¹ * i₂ (deltaAut z) * n) * n⁻¹ := by rw [hz']
          _ = i₂ (deltaAut z) := by group
      calc n * i₂ z = n * i₂ z * n⁻¹ * n := by group
        _ = i₂ (deltaAut z) * n := by rw [h1]
    calc (i₂ z)⁻¹ * n * (i₂ z) = (i₂ z)⁻¹ * (n * i₂ z) := by group
      _ = (i₂ z)⁻¹ * (i₂ (deltaAut z) * n) := by rw [hz]
      _ = i₂ (z⁻¹ * deltaAut z) * n := by
            rw [map_mul, map_inv]
            group
  have hcalc : (i₁ r * i₂ s)⁻¹ * n * (i₁ r * i₂ s) = v := by
    have hcomm_rs : Commute (i₁ (r⁻¹ * deltaAut r)) (i₂ s) := hcomm (r⁻¹ * deltaAut r) s
    calc (i₁ r * i₂ s)⁻¹ * n * (i₁ r * i₂ s)
        = (i₂ s)⁻¹ * ((i₁ r)⁻¹ * n * (i₁ r)) * (i₂ s) := by group
      _ = (i₂ s)⁻¹ * (i₁ (r⁻¹ * deltaAut r) * n) * (i₂ s) := by rw [hkey₁ r]
      _ = i₁ (r⁻¹ * deltaAut r) * ((i₂ s)⁻¹ * n * (i₂ s)) := by
            rw [show (i₂ s)⁻¹ * (i₁ (r⁻¹ * deltaAut r) * n) * (i₂ s)
                  = ((i₂ s)⁻¹ * i₁ (r⁻¹ * deltaAut r)) * n * (i₂ s) by group,
                hcomm_rs.symm.inv_left.eq]
            group
      _ = i₁ (r⁻¹ * deltaAut r) * (i₂ (s⁻¹ * deltaAut s) * n) := by rw [hkey₂ s]
      _ = v := by
            rw [hrg, hsg]
            rw [show i₁ g * (i₂ g' * n) = i₁ g * i₂ g' * n by group, ← hv_eq]
  exact isConj_iff.mpr ⟨(i₁ r * i₂ s)⁻¹, by rw [inv_inv]; exact hcalc⟩

theorem WongHyp.isConj_x_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = 1)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) :
    IsConj t (i₁ hM * i₂ hM) := by
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_t]; exact pow_orderOf_eq_one t
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact ht2)
  have htK : t ∈ i₁.range ⊔ i₂.range := by
    apply mem_sup_left
    rw [eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq]
    exact ⟨-1, rfl⟩
  have hxK : i₁ hM * i₂ hM ∈ i₁.range ⊔ i₂.range :=
    mul_mem (mem_sup_left ⟨hM, rfl⟩) (mem_sup_right ⟨hM, rfl⟩)
  have htxK : t * (i₁ hM * i₂ hM) ∈ i₁.range ⊔ i₂.range := mul_mem htK hxK
  have htC : t ∈ centralizer ({t} : Set G) := h.sup_le_centralizer htK
  have hxC : i₁ hM * i₂ hM ∈ centralizer ({t} : Set G) := h.sup_le_centralizer hxK
  have htxC : t * (i₁ hM * i₂ hM) ∈ centralizer ({t} : Set G) :=
    h.sup_le_centralizer htxK
  have ht_n : Commute t n := (mem_centralizer_singleton_iff.mp hn).symm
  have ht_x : Commute t (i₁ hM * i₂ hM) :=
    (mem_centralizer_singleton_iff.mp hxC).symm
  have hx2 : (i₁ hM * i₂ hM) ^ 2 = 1 := by
    rw [(hcomm hM hM).mul_pow 2]
    rw [show (i₁ hM) ^ 2 = t by
          rw [← map_pow, hM_sq, ← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq],
        show (i₂ hM) ^ 2 = t by
          rw [← map_pow, hM_sq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq],
        show t * t = 1 by rw [← pow_two]; exact ht2]
  have hactn₁ : ∀ z : SL5, i₁ z * n = n * i₁ (deltaAut z) := by
    intro z
    calc i₁ z * n = n * (n⁻¹ * i₁ z * n) := by group
      _ = n * i₁ (deltaAut z) := by rw [(hact z).1]
  have hactn₂ : ∀ z : SL5, i₂ z * n = n * i₂ (deltaAut z) := by
    intro z
    calc i₂ z * n = n * (n⁻¹ * i₂ z * n) := by group
      _ = n * i₂ (deltaAut z) := by rw [(hact z).2]
  have hneg : hM = -hM⁻¹ := by rw [neg_hM.symm, neg_neg]
  have hprod_eq : i₁ (deltaAut hM) * i₂ (deltaAut hM) = i₁ hM * i₂ hM := by
    rw [deltaAut_hM, prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcomm h.inf_eq]
    right
    exact ⟨hneg, hneg⟩
  have hxn : Commute (i₁ hM * i₂ hM) n := by
    rw [commute_iff_eq]
    calc (i₁ hM * i₂ hM) * n = i₁ hM * (i₂ hM * n) := by group
      _ = i₁ hM * (n * i₂ (deltaAut hM)) := by rw [hactn₂ hM]
      _ = (i₁ hM * n) * i₂ (deltaAut hM) := by group
      _ = (n * i₁ (deltaAut hM)) * i₂ (deltaAut hM) := by rw [hactn₁ hM]
      _ = n * (i₁ (deltaAut hM) * i₂ (deltaAut hM)) := by group
      _ = n * (i₁ hM * i₂ hM) := by rw [hprod_eq]
  have htn2 : (t * n) ^ 2 = 1 := by
    rw [(ht_n).mul_pow 2, ht2, hn2, mul_one]
  have hxn2 : ((i₁ hM * i₂ hM) * n) ^ 2 = 1 := by
    rw [(hxn).mul_pow 2, hx2, hn2, mul_one]
  have htx2 : (t * (i₁ hM * i₂ hM)) ^ 2 = 1 := by
    rw [(ht_x).mul_pow 2, ht2, hx2, mul_one]
  have htxn2 : (t * (i₁ hM * i₂ hM) * n) ^ 2 = 1 := by
    rw [show t * (i₁ hM * i₂ hM) * n = (t * (i₁ hM * i₂ hM)) * n by group,
      ((ht_n).mul_left hxn).mul_pow 2, htx2, hn2, mul_one]
  obtain ⟨g, hvC, hvne⟩ := exists_conj_mem_centralizer_ne h.orderOf_t h.sup_oddCore_ne_top
  have hv_conj : IsConj t (g⁻¹ * t * g) := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩
  have hvord : orderOf (g⁻¹ * t * g) = 2 := by
    have hord := orderOf_injective ((MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective t
    rw [h.orderOf_t] at hord
    simpa [MulAut.conj_apply] using hord
  by_cases hvK : g⁻¹ * t * g ∈ i₁.range ⊔ i₂.range
  · obtain ⟨k, hkK, hk⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hvK hvord hvne
    exact hv_conj.trans (isConj_iff.mpr ⟨k, hk⟩).symm
  · have hv2 : (g⁻¹ * t * g) ^ 2 = 1 := by
      have := pow_orderOf_eq_one (g⁻¹ * t * g)
      rwa [hvord] at this
    have hn_v : IsConj n (g⁻¹ * t * g) :=
      isConj_n_of_outer_outer h hi₁ hi₂ hn hnK hn2 hact hvC hvK hv2
    have hnt : IsConj t n := hv_conj.trans hn_v.symm
    obtain ⟨c, hc⟩ := isConj_iff.mp hnt
    have hcn : c⁻¹ * n * c = t := by rw [← hc]; group
    have memC : ∀ w : G, Commute w n → c⁻¹ * w * c ∈ centralizer ({t} : Set G) := by
      intro w hwn
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * w * c) * t = (c⁻¹ * w * c) * (c⁻¹ * n * c) := by rw [hcn]
        _ = c⁻¹ * (w * n) * c := by group
        _ = c⁻¹ * (n * w) * c := by rw [hwn.eq]
        _ = (c⁻¹ * n * c) * (c⁻¹ * w * c) := by group
        _ = t * (c⁻¹ * w * c) := by rw [hcn]
    have htn_n : Commute (t * n) n := (ht_n).mul_left (Commute.refl n)
    have hxn_n : Commute ((i₁ hM * i₂ hM) * n) n := (hxn).mul_left (Commute.refl n)
    have htn_notK : t * n ∉ i₁.range ⊔ i₂.range := fun hh => hnK (by
      have h1 := mul_mem htK hh
      rwa [show t * (t * n) = n by rw [← mul_assoc, ← pow_two, ht2, one_mul]] at h1)
    have hxn_notK : (i₁ hM * i₂ hM) * n ∉ i₁.range ⊔ i₂.range := fun hh => hnK (by
      have h1 := mul_mem (inv_mem hxK) hh
      rwa [show (i₁ hM * i₂ hM)⁻¹ * ((i₁ hM * i₂ hM) * n) = n by group] at h1)
    have htxn_notK : t * (i₁ hM * i₂ hM) * n ∉ i₁.range ⊔ i₂.range := fun hh => hnK (by
      have h1 := mul_mem (inv_mem htxK) hh
      rwa [show (t * (i₁ hM * i₂ hM))⁻¹ * (t * (i₁ hM * i₂ hM) * n) = n by group] at h1)
    have hx_ne_one : i₁ hM * i₂ hM ≠ 1 := by
      intro h1
      rcases (diag_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with h2 | h2
      · exact (by decide : hM ≠ 1) h2
      · exact (by decide : hM ≠ -1) h2
    have ht_ne_one : t ≠ 1 := by
      intro h1
      have ht_ord := h.orderOf_t
      rw [h1, orderOf_one] at ht_ord
      exact (by norm_num : (1 : ℕ) ≠ 2) ht_ord
    have htx_ne_one : t * (i₁ hM * i₂ hM) ≠ 1 := by
      intro h1
      have h2 : i₁ hM * i₂ hM = t := by
        calc i₁ hM * i₂ hM = t⁻¹ * (t * (i₁ hM * i₂ hM)) := by group
          _ = t⁻¹ * 1 := by rw [h1]
          _ = t⁻¹ := mul_one _
          _ = t := ht_inv
      exact (x_ne_t h hi₁ hi₂) h2
    have hwn_tn : t * n ≠ n := by
      intro h1
      apply ht_ne_one
      have := congrArg (fun z => z * n⁻¹) h1
      simpa [mul_assoc] using this
    have hwn_xn : (i₁ hM * i₂ hM) * n ≠ n := by
      intro h1
      apply hx_ne_one
      have := congrArg (fun z => z * n⁻¹) h1
      simpa [mul_assoc] using this
    have hwn_txn : t * (i₁ hM * i₂ hM) * n ≠ n := by
      intro h1
      apply htx_ne_one
      have := congrArg (fun z => z * n⁻¹) h1
      simpa [mul_assoc] using this
    have step : ∀ w : G, w ∈ centralizer ({t} : Set G) → w ∉ i₁.range ⊔ i₂.range →
        w ^ 2 = 1 → w ≠ n → c⁻¹ * w * c ∈ i₁.range ⊔ i₂.range →
        IsConj t (i₁ hM * i₂ hM) := by
      intro w hwC hwK hw2 hwn hwK'
      have hwt : w ≠ t := fun h1 => hwK (by rw [h1]; exact htK)
      have hitem1 : IsConj n w :=
        isConj_n_of_outer_outer h hi₁ hi₂ hn hnK hn2 hact hwC hwK hw2
      have hww : IsConj w (c⁻¹ * w * c) := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
      have hw'2 : (c⁻¹ * w * c) ^ 2 = 1 := by
        have h1 : (MulAut.conj c⁻¹) w = c⁻¹ * w * c := by
          rw [MulAut.conj_apply, inv_inv]
        rw [← h1, ← map_pow, hw2, map_one]
      have hw'1 : c⁻¹ * w * c ≠ 1 := by
        intro h1
        have hw1 : w ≠ 1 := fun h2 => hwK (by rw [h2]; exact one_mem _)
        apply hw1
        calc w = c * (c⁻¹ * w * c) * c⁻¹ := by group
          _ = c * 1 * c⁻¹ := by rw [h1]
          _ = 1 := by group
      have hw'ord : orderOf (c⁻¹ * w * c) = 2 := orderOf_eq_prime hw'2 hw'1
      have hw'ne : c⁻¹ * w * c ≠ t := by
        intro h1
        apply hwn
        have h2 : c⁻¹ * w * c = c⁻¹ * n * c := by rw [h1, hcn]
        exact mul_left_cancel (mul_right_cancel h2)
      obtain ⟨k, hkK, hk⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hwK' hw'ord hw'ne
      have hxw' : IsConj (i₁ hM * i₂ hM) (c⁻¹ * w * c) := isConj_iff.mpr ⟨k, hk⟩
      exact (hnt.trans hitem1).trans (hww.trans hxw'.symm)
    by_cases h1 : c⁻¹ * (t * n) * c ∈ i₁.range ⊔ i₂.range
    · have hwC : t * n ∈ centralizer ({t} : Set G) := mul_mem htC hn
      exact step (t * n) hwC htn_notK htn2 hwn_tn h1
    · by_cases h2 : c⁻¹ * ((i₁ hM * i₂ hM) * n) * c ∈ i₁.range ⊔ i₂.range
      · have hwC : (i₁ hM * i₂ hM) * n ∈ centralizer ({t} : Set G) := mul_mem hxC hn
        exact step ((i₁ hM * i₂ hM) * n) hwC hxn_notK hxn2 hwn_xn h2
      · have hmem_prod : (c⁻¹ * (t * n) * c) * (c⁻¹ * ((i₁ hM * i₂ hM) * n) * c)
            ∈ i₁.range ⊔ i₂.range :=
          h.mul_mem_sup_of_not_mem (memC (t * n) htn_n)
            (memC ((i₁ hM * i₂ hM) * n) hxn_n) h1 h2
        have hnx : n * (i₁ hM * i₂ hM) * n = i₁ hM * i₂ hM := by
          rw [mul_assoc, hxn.eq, ← mul_assoc, ← pow_two, hn2, one_mul]
        have htx_eq : (c⁻¹ * (t * n) * c) * (c⁻¹ * ((i₁ hM * i₂ hM) * n) * c)
            = c⁻¹ * (t * (i₁ hM * i₂ hM)) * c := by
          rw [show (c⁻¹ * (t * n) * c) * (c⁻¹ * ((i₁ hM * i₂ hM) * n) * c)
                = c⁻¹ * (t * n * (i₁ hM * i₂ hM) * n) * c by group,
            show t * n * (i₁ hM * i₂ hM) * n = t * (i₁ hM * i₂ hM) by
              rw [show t * n * (i₁ hM * i₂ hM) * n
                    = t * (n * (i₁ hM * i₂ hM) * n) by group, hnx]]
        have htx_mem : c⁻¹ * (t * (i₁ hM * i₂ hM)) * c ∈ i₁.range ⊔ i₂.range := by
          rw [← htx_eq]
          exact hmem_prod
        have htxn_mem : c⁻¹ * (t * (i₁ hM * i₂ hM) * n) * c ∈ i₁.range ⊔ i₂.range := by
          rw [show c⁻¹ * (t * (i₁ hM * i₂ hM) * n) * c
                = (c⁻¹ * (t * (i₁ hM * i₂ hM)) * c) * (c⁻¹ * n * c) by group, hcn]
          exact mul_mem htx_mem htK
        have hwC : t * (i₁ hM * i₂ hM) * n ∈ centralizer ({t} : Set G) :=
          mul_mem htxC hn
        exact step (t * (i₁ hM * i₂ hM) * n) hwC htxn_notK htxn2 hwn_txn htxn_mem

theorem WongHyp.isConj_t_n_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = 1)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) :
    IsConj t n := by
  by_contra hnt
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_t]; exact pow_orderOf_eq_one t
  have htx : IsConj t (i₁ hM * i₂ hM) :=
    isConj_x_of_outer_outer h hi₁ hi₂ hn hnK hn2 hact
  obtain ⟨c, hc⟩ := isConj_iff.mp htx
  have hcx : c⁻¹ * (i₁ hM * i₂ hM) * c = t := by rw [← hc]; group
  have hx_ne_one : i₁ hM * i₂ hM ≠ 1 := by
    intro h1
    rcases (diag_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with h2 | h2
    · exact (by decide : hM ≠ 1) h2
    · exact (by decide : hM ≠ -1) h2
  have hyK : i₁ cM * i₂ cM ∈ i₁.range ⊔ i₂.range :=
    mul_mem (mem_sup_left ⟨cM, rfl⟩) (mem_sup_right ⟨cM, rfl⟩)
  have hhyK : i₁ hM * (i₁ cM * i₂ cM) ∈ i₁.range ⊔ i₂.range :=
    mul_mem (mem_sup_left ⟨hM, rfl⟩) hyK
  have hy2 : (i₁ cM * i₂ cM) ^ 2 = 1 := by
    rw [(hcomm cM cM).mul_pow 2]
    rw [show (i₁ cM) ^ 2 = t by
          rw [← map_pow, cM_sq, ← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq],
        show (i₂ cM) ^ 2 = t by
          rw [← map_pow, cM_sq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq],
        show t * t = 1 by rw [← pow_two]; exact ht2]
  have hhy_eq : i₁ hM * (i₁ cM * i₂ cM) = i₁ (hM * cM) * i₂ cM := by
    rw [show i₁ hM * (i₁ cM * i₂ cM) = (i₁ hM * i₁ cM) * i₂ cM by group, ← map_mul]
  have hhy2 : (i₁ hM * (i₁ cM * i₂ cM)) ^ 2 = 1 := by
    rw [hhy_eq, (hcomm (hM * cM) cM).mul_pow 2]
    rw [show (i₁ (hM * cM)) ^ 2 = t by
          rw [← map_pow, hM_mul_cM_sq, ← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq],
        show (i₂ cM) ^ 2 = t by
          rw [← map_pow, cM_sq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq],
        show t * t = 1 by rw [← pow_two]; exact ht2]
  have hy_ne_one : i₁ cM * i₂ cM ≠ 1 := by
    intro h1
    rcases (diag_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with h2 | h2
    · exact (by decide : cM ≠ 1) h2
    · exact (by decide : cM ≠ -1) h2
  have hhy_ne_one : i₁ hM * (i₁ cM * i₂ cM) ≠ 1 := by
    intro h1
    have h2 : i₁ (hM * cM) * i₂ cM = 1 := by rwa [hhy_eq] at h1
    rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h2 with ⟨h3, _⟩ | ⟨h3, h4⟩
    · exact (by decide : hM * cM ≠ 1) h3
    · exact (by decide : cM ≠ -1) h4
  have hy_ne_t : i₁ cM * i₂ cM ≠ t := by
    intro h1
    have h2 : i₁ cM * i₂ cM = i₁ (-1) * i₂ 1 := by
      rw [h1, eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq, map_one, mul_one]
    rcases (prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcomm h.inf_eq).mp h2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (by decide : (-1 : SL5) ≠ cM) h3
    · exact (by decide : (-1 : SL5) ≠ -cM) h3
  have hhy_ne_t : i₁ hM * (i₁ cM * i₂ cM) ≠ t := by
    intro h1
    have h2 : i₁ (hM * cM) * i₂ cM = i₁ (-1) * i₂ 1 := by
      rw [← hhy_eq, h1, eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq, map_one, mul_one]
    rcases (prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcomm h.inf_eq).mp h2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (by decide : (-1 : SL5) ≠ hM * cM) h3
    · exact (by decide : (-1 : SL5) ≠ -(hM * cM)) h3
  have hanti : cM * hM = -(hM * cM) := by decide
  have hanti' : hM * cM = -(cM * hM) := by rw [hanti, neg_neg]
  have hyx : Commute (i₁ cM * i₂ cM) (i₁ hM * i₂ hM) := by
    rw [commute_iff_eq]
    have e1 : (i₁ cM * i₂ cM) * (i₁ hM * i₂ hM) = i₁ (cM * hM) * i₂ (cM * hM) := by
      rw [show (i₁ cM * i₂ cM) * (i₁ hM * i₂ hM)
            = i₁ cM * (i₂ cM * i₁ hM) * i₂ hM by group]
      rw [(hcomm hM cM).eq.symm]
      rw [show i₁ cM * (i₁ hM * i₂ cM) * i₂ hM
            = (i₁ cM * i₁ hM) * (i₂ cM * i₂ hM) by group]
      rw [← map_mul, ← map_mul]
    have e2 : (i₁ hM * i₂ hM) * (i₁ cM * i₂ cM) = i₁ (hM * cM) * i₂ (hM * cM) := by
      rw [show (i₁ hM * i₂ hM) * (i₁ cM * i₂ cM)
            = i₁ hM * (i₂ hM * i₁ cM) * i₂ cM by group]
      rw [(hcomm cM hM).eq.symm]
      rw [show i₁ hM * (i₁ cM * i₂ hM) * i₂ cM
            = (i₁ hM * i₁ cM) * (i₂ hM * i₂ cM) by group]
      rw [← map_mul, ← map_mul]
    rw [e1, e2]
    rw [prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcomm h.inf_eq]
    right
    exact ⟨hanti', hanti'⟩
  have hih_x : Commute (i₁ hM) (i₁ hM * i₂ hM) :=
    (Commute.refl (i₁ hM)).mul_right (hcomm hM hM)
  have hhyx : Commute (i₁ hM * (i₁ cM * i₂ cM)) (i₁ hM * i₂ hM) :=
    hih_x.mul_left hyx
  have key : ∀ w : G, w ∈ i₁.range ⊔ i₂.range → w ^ 2 = 1 → w ≠ 1 → w ≠ t →
      Commute w (i₁ hM * i₂ hM) → c⁻¹ * w * c ∈ i₁.range ⊔ i₂.range := by
    intro w hwK hw2 hw_ne_one hwt hwx
    by_contra hwK'
    have hword : orderOf w = 2 := orderOf_eq_prime hw2 hw_ne_one
    have hwC : c⁻¹ * w * c ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (c⁻¹ * w * c) * t = (c⁻¹ * w * c) * (c⁻¹ * (i₁ hM * i₂ hM) * c) := by rw [hcx]
        _ = c⁻¹ * (w * (i₁ hM * i₂ hM)) * c := by group
        _ = c⁻¹ * ((i₁ hM * i₂ hM) * w) * c := by rw [hwx.eq]
        _ = (c⁻¹ * (i₁ hM * i₂ hM) * c) * (c⁻¹ * w * c) := by group
        _ = t * (c⁻¹ * w * c) := by rw [hcx]
    have hw'2 : (c⁻¹ * w * c) ^ 2 = 1 := by
      have h1 : (MulAut.conj c⁻¹) w = c⁻¹ * w * c := by rw [MulAut.conj_apply, inv_inv]
      rw [← h1, ← map_pow, hw2, map_one]
    have hitem1 : IsConj n (c⁻¹ * w * c) :=
      isConj_n_of_outer_outer h hi₁ hi₂ hn hnK hn2 hact hwC hwK' hw'2
    have hxw : IsConj (i₁ hM * i₂ hM) w := by
      obtain ⟨j, hjK, hj⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hwK hword hwt
      exact isConj_iff.mpr ⟨j, hj⟩
    have hww : IsConj w (c⁻¹ * w * c) := isConj_iff.mpr ⟨c⁻¹, by rw [inv_inv]⟩
    exact hnt ((htx.trans hxw).trans (hww.trans hitem1.symm))
  have hyK' : c⁻¹ * (i₁ cM * i₂ cM) * c ∈ i₁.range ⊔ i₂.range :=
    key (i₁ cM * i₂ cM) hyK hy2 hy_ne_one hy_ne_t hyx
  have hhyK' : c⁻¹ * (i₁ hM * (i₁ cM * i₂ cM)) * c ∈ i₁.range ⊔ i₂.range :=
    key (i₁ hM * (i₁ cM * i₂ cM)) hhyK hhy2 hhy_ne_one hhy_ne_t hhyx
  have hicK : c⁻¹ * i₁ hM * c ∈ i₁.range ⊔ i₂.range := by
    have h := mul_mem hhyK' (inv_mem hyK')
    rwa [show c⁻¹ * (i₁ hM * (i₁ cM * i₂ cM)) * c * (c⁻¹ * (i₁ cM * i₂ cM) * c)⁻¹
          = c⁻¹ * i₁ hM * c by group] at h
  have hcomm_ident : c⁻¹ * ⁅i₁ hM, i₁ cM * i₂ cM⁆ * c
      = ⁅c⁻¹ * i₁ hM * c, c⁻¹ * (i₁ cM * i₂ cM) * c⁆ := by
    simp only [commutatorElement_def]
    group
  have hcitK : c⁻¹ * t * c ∈ i₁.range ⊔ i₂.range := by
    rw [← commutator_hM_y h hi₁, hcomm_ident, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hicK hyK') (inv_mem hicK)) (inv_mem hyK')
  have hcitord : orderOf (c⁻¹ * t * c) = 2 := by
    have hord := orderOf_injective ((MulAut.conj c⁻¹).toMonoidHom)
      (MulAut.conj c⁻¹).injective t
    rw [h.orderOf_t] at hord
    simpa [MulAut.conj_apply] using hord
  have hcitne : c⁻¹ * t * c ≠ t := by
    intro h1
    have h2 : c * t * c⁻¹ = t := by
      have h3 := congrArg (fun z => c * z * c⁻¹) h1
      have h4 : c * (c⁻¹ * t * c) * c⁻¹ = t := by group
      rw [h4] at h3
      exact h3.symm
    exact (x_ne_t h hi₁ hi₂) (by rw [← hc, h2])
  obtain ⟨k, hkK, hk⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hcitK hcitord hcitne
  set c' : G := c * k with hc'_def
  have hkt : Commute k t := mem_centralizer_singleton_iff.mp (h.sup_le_centralizer hkK)
  have hc'x : c'⁻¹ * (i₁ hM * i₂ hM) * c' = t := by
    rw [hc'_def]
    calc (c * k)⁻¹ * (i₁ hM * i₂ hM) * (c * k)
        = k⁻¹ * (c⁻¹ * (i₁ hM * i₂ hM) * c) * k := by group
      _ = k⁻¹ * t * k := by rw [hcx]
      _ = t := hkt.inv_mul_cancel
  have hc't : c'⁻¹ * t * c' = i₁ hM * i₂ hM := by
    rw [hc'_def]
    calc (c * k)⁻¹ * t * (c * k) = k⁻¹ * (c⁻¹ * t * c) * k := by group
      _ = k⁻¹ * (k * (i₁ hM * i₂ hM) * k⁻¹) * k := by rw [← hk]
      _ = i₁ hM * i₂ hM := by group
  have hc'ihK : c'⁻¹ * i₁ hM * c' ∈ i₁.range ⊔ i₂.range := by
    rw [hc'_def]
    rw [show (c * k)⁻¹ * i₁ hM * (c * k) = k⁻¹ * (c⁻¹ * i₁ hM * c) * k by group]
    exact mul_mem (mul_mem (inv_mem hkK) hicK) hkK
  have hc'yK : c'⁻¹ * (i₁ cM * i₂ cM) * c' ∈ i₁.range ⊔ i₂.range := by
    rw [hc'_def]
    rw [show (c * k)⁻¹ * (i₁ cM * i₂ cM) * (c * k)
          = k⁻¹ * (c⁻¹ * (i₁ cM * i₂ cM) * c) * k by group]
    exact mul_mem (mul_mem (inv_mem hkK) hyK') hkK
  have hih_t : Commute (i₁ hM) t :=
    mem_centralizer_singleton_iff.mp (h.sup_le_centralizer (mem_sup_left ⟨hM, rfl⟩))
  have hy_t : Commute (i₁ cM * i₂ cM) t :=
    mem_centralizer_singleton_iff.mp (h.sup_le_centralizer hyK)
  have hc'ihx : Commute (c'⁻¹ * i₁ hM * c') (i₁ hM * i₂ hM) := by
    rw [← hc't]
    simpa [inv_inv] using (hih_t).conj c'⁻¹
  have hc'yhx : Commute (c'⁻¹ * (i₁ cM * i₂ cM) * c') (i₁ hM * i₂ hM) := by
    rw [← hc't]
    simpa [inv_inv] using (hy_t).conj c'⁻¹
  have hcomm_eq : ⁅c'⁻¹ * i₁ hM * c', c'⁻¹ * (i₁ cM * i₂ cM) * c'⁆ = c'⁻¹ * t * c' := by
    rw [← commutator_hM_y h hi₁]
    simp only [commutatorElement_def]
    group
  have hcase := h.commutator_eq_of_commute_x hi₁ hi₂ hc'ihK hc'yK hc'ihx hc'yhx
  rw [hcomm_eq, hc't] at hcase
  rcases hcase with h1 | h1
  · exact hx_ne_one h1
  · exact (x_ne_t h hi₁ hi₂) h1

end CFSG.OddTranspositions.PartThree.Wong
