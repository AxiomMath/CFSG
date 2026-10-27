module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyInvol
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyCentX
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.sq_ne_one_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) {v : G}
    (hvC : v ∈ centralizer ({t} : Set G)) (hvK : v ∉ i₁.range ⊔ i₂.range) : v ^ 2 ≠ 1 := by
  intro hv1
  have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
    fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  let φ : SL5 × SL5 →* G := prodHom hcomm
  have hφ : ∀ p : SL5 × SL5, φ p = i₁ p.1 * i₂ p.2 := fun p => prodHom_apply hcomm p
  have hn'invC : n⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hn
  have hn'invK : n⁻¹ ∉ i₁.range ⊔ i₂.range :=
    fun hh => hnK (by simpa using (i₁.range ⊔ i₂.range).inv_mem hh)
  have hvn : v * n⁻¹ ∈ i₁.range ⊔ i₂.range :=
    h.mul_mem_sup_of_not_mem hvC hn'invC hvK hn'invK
  obtain ⟨g, g', hgg'⟩ := (mem_sup_iff hcomm).mp hvn
  have hv_eq : v = i₁ g * i₂ g' * n := by
    rw [hgg', mul_assoc, inv_mul_cancel, mul_one]
  have hnconj₁ : ∀ a : SL5, n * i₁ a * n⁻¹ = i₁ (deltaAut a) := by
    intro a
    have h1 := (hact (deltaAut a)).1
    rw [deltaAut_deltaAut] at h1
    rw [← h1]; group
  have hnconj₂ : ∀ a : SL5, n * i₂ a * n⁻¹ = i₂ (deltaAut a) := by
    intro a
    have h1 := (hact (deltaAut a)).2
    rw [deltaAut_deltaAut] at h1
    rw [← h1]; group
  have hnφ : n * φ (g, g') * n⁻¹ = φ (deltaAut g, deltaAut g') := by
    rw [hφ (g, g'), hφ (deltaAut g, deltaAut g')]
    rw [show n * (i₁ g * i₂ g') * n⁻¹ = (n * i₁ g * n⁻¹) * (n * i₂ g' * n⁻¹) by group,
      hnconj₁, hnconj₂]
  have hsq : v ^ 2 = φ (g * deltaAut g, g' * deltaAut g') * t := by
    rw [hv_eq, pow_two]
    have e : (i₁ g * i₂ g' * n) * (i₁ g * i₂ g' * n) =
        φ (g, g') * (n * φ (g, g') * n⁻¹) * (n * n) := by
      rw [hφ (g, g')]; group
    rw [e, hnφ]
    rw [show n * n = t by rw [← pow_two, hn2]]
    rw [← map_mul]
    rfl
  have h1 : φ (g * deltaAut g, g' * deltaAut g') * t = 1 := by rw [← hsq, hv1]
  have h1' : i₁ (g * deltaAut g) * i₂ ((g' * deltaAut g') * (-1)) = 1 := by
    have htmp := h1
    rw [hφ (g * deltaAut g, g' * deltaAut g'),
      eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq, mul_assoc, ← map_mul] at htmp
    exact htmp
  rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1' with ⟨-, hy⟩ | ⟨hx, -⟩
  · have hgy : g' * deltaAut g' = -1 := by
      have h2 := mul_eq_one_iff_eq_inv.mp hy
      rwa [sl5_inv_neg_one] at h2
    exact mul_deltaAut_ne_neg_one g' hgy
  · exact mul_deltaAut_ne_neg_one g hx

theorem WongHyp.sq_ne_one_of_swap [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₂ x ∧ n⁻¹ * i₂ x * n = i₁ x) {v : G}
    (hvC : v ∈ centralizer ({t} : Set G)) (hvK : v ∉ i₁.range ⊔ i₂.range) : v ^ 2 ≠ 1 := by
  intro hv1
  have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
    fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  let φ : SL5 × SL5 →* G := prodHom hcomm
  have hφ : ∀ p : SL5 × SL5, φ p = i₁ p.1 * i₂ p.2 := fun p => prodHom_apply hcomm p
  have hn'invC : n⁻¹ ∈ centralizer ({t} : Set G) := inv_mem hn
  have hn'invK : n⁻¹ ∉ i₁.range ⊔ i₂.range :=
    fun hh => hnK (by simpa using (i₁.range ⊔ i₂.range).inv_mem hh)
  have hvn : v * n⁻¹ ∈ i₁.range ⊔ i₂.range :=
    h.mul_mem_sup_of_not_mem hvC hn'invC hvK hn'invK
  obtain ⟨g, g', hgg'⟩ := (mem_sup_iff hcomm).mp hvn
  have hv_eq : v = i₁ g * i₂ g' * n := by
    rw [hgg', mul_assoc, inv_mul_cancel, mul_one]
  have hnconj₁ : ∀ a : SL5, n * i₁ a * n⁻¹ = i₂ a := by
    intro a
    have h1 := (hact a).2
    rw [← h1]; group
  have hnconj₂ : ∀ a : SL5, n * i₂ a * n⁻¹ = i₁ a := by
    intro a
    have h1 := (hact a).1
    rw [← h1]; group
  have hnφ : n * φ (g, g') * n⁻¹ = φ (g', g) := by
    rw [hφ (g, g'), hφ (g', g)]
    rw [show n * (i₁ g * i₂ g') * n⁻¹ = (n * i₁ g * n⁻¹) * (n * i₂ g' * n⁻¹) by group,
      hnconj₁, hnconj₂]
    exact (hcomm g' g).eq.symm
  have hsq : v ^ 2 = φ (g * g', g' * g) * t := by
    rw [hv_eq, pow_two]
    have e : (i₁ g * i₂ g' * n) * (i₁ g * i₂ g' * n) =
        φ (g, g') * (n * φ (g, g') * n⁻¹) * (n * n) := by
      rw [hφ (g, g')]; group
    rw [e, hnφ]
    rw [show n * n = t by rw [← pow_two, hn2]]
    rw [← map_mul]
    rfl
  have h1 : φ (g * g', g' * g) * t = 1 := by rw [← hsq, hv1]
  have h1' : i₁ (g * g') * i₂ ((g' * g) * (-1)) = 1 := by
    have htmp := h1
    rw [hφ (g * g', g' * g), eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq, mul_assoc, ← map_mul] at htmp
    exact htmp
  rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1' with ⟨hw, hy⟩ | ⟨hw, hy⟩
  · have hgy : g' * g = -1 := by
      have h2 := mul_eq_one_iff_eq_inv.mp hy
      rwa [sl5_inv_neg_one] at h2
    have hgg : g' * g = 1 := by
      rw [show g' * g = g⁻¹ * (g * g') * g by group, hw]; group
    exact sl5_neg_one_ne_one (hgy.symm.trans hgg)
  · have hgy : g' * g = 1 := by
      refine mul_right_cancel (b := (-1 : SL5)) ?_
      rw [hy, one_mul]
    have hneg_cen : ∀ a : SL5, a * (-1) = (-1) * a := fun a => by rw [mul_neg_one, neg_one_mul]
    have hgg : g' * g = -1 := by
      rw [show g' * g = g⁻¹ * (g * g') * g by group, hw]
      calc g⁻¹ * (-1) * g = ((-1) * g⁻¹) * g := by rw [hneg_cen g⁻¹]
        _ = (-1) * (g⁻¹ * g) := by rw [mul_assoc]
        _ = -1 := by rw [inv_mul_cancel, mul_one]
    exact sl5_neg_one_ne_one (hgg.symm.trans hgy)

theorem WongHyp.false_of_forall_sq_ne_one [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂)
    (hno : ∀ v ∈ centralizer ({t} : Set G), v ∉ i₁.range ⊔ i₂.range → v ^ 2 ≠ 1) : False := by
  let C : Subgroup G := centralizer ({t} : Set G)
  let K : Subgroup G := i₁.range ⊔ i₂.range
  let x : G := i₁ hM * i₂ hM
  let y : G := i₁ cM * i₂ cM
  have hcomm : ∀ a b : SL5, Commute (i₁ a) (i₂ b) :=
    fun a b => h.commute _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  let φ : SL5 × SL5 →* G := prodHom hcomm
  have hφ : ∀ p : SL5 × SL5, φ p = i₁ p.1 * i₂ p.2 := fun p => prodHom_apply hcomm p
  obtain ⟨g, hgC, hgne⟩ :=
    exists_conj_mem_centralizer_ne h.orderOf_t h.sup_oddCore_ne_top
  set v : G := g⁻¹ * t * g with hv_def
  have hvC : v ∈ C := by rw [hv_def]; exact hgC
  have hvne : v ≠ t := by rw [hv_def]; exact hgne
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
  have hv2 : v ^ 2 = 1 := by
    rw [hv_def, pow_two]
    calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht2]; group
  have hvK : v ∈ K := by
    by_contra hvKn
    exact hno v hvC hvKn hv2
  have hvne1 : v ≠ 1 := by
    intro hv1
    have ht1 : t = 1 := by
      calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
        _ = g * v * g⁻¹ := by rw [hv_def]
        _ = 1 := by rw [hv1]; group
    have h2 : orderOf t = 1 := by rw [ht1, orderOf_one]
    rw [h.orderOf_t] at h2
    exact absurd h2 (by norm_num)
  have hvord : orderOf v = 2 := orderOf_eq_prime hv2 hvne1
  obtain ⟨k, hkK, hkx⟩ := h.exists_mem_sup_conj_eq hi₁ hi₂ hvK hvord hvne
  have hxk_conj : IsConj x v := isConj_iff.mpr ⟨k, hkx⟩
  have htv_conj : IsConj t v := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv, hv_def]⟩
  have hx_conj : IsConj t x := htv_conj.trans hxk_conj.symm
  have hxK : x ∈ K :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨hM, rfl⟩) (Subgroup.mem_sup_right ⟨hM, rfl⟩)
  have hxC : x ∈ C := h.sup_le_centralizer hxK
  have hyK : y ∈ K :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨cM, rfl⟩) (Subgroup.mem_sup_right ⟨cM, rfl⟩)
  have hyC : y ∈ C := h.sup_le_centralizer hyK
  have hhMK : i₁ hM ∈ K := Subgroup.mem_sup_left ⟨hM, rfl⟩
  have hhMC : i₁ hM ∈ C := h.sup_le_centralizer hhMK
  have hxφ : x = φ (hM, hM) := (hφ (hM, hM)).symm
  have hyφ : y = φ (cM, cM) := (hφ (cM, cM)).symm
  have hhφ : i₁ hM = φ (hM, 1) := by
    rw [hφ (hM, 1)]
    simp
  have hx2 : x ^ 2 = 1 := by
    rw [hxφ, ← map_pow]
    rw [show (hM, hM) ^ 2 = (-1, -1) by decide]
    rw [hφ (-1, -1)]
    rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
    exact ht2
  have hy2 : y ^ 2 = 1 := by
    rw [hyφ, ← map_pow]
    rw [show (cM, cM) ^ 2 = (-1, -1) by decide]
    rw [hφ (-1, -1)]
    rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
    exact ht2
  have hhMy2 : (i₁ hM * y) ^ 2 = 1 := by
    have hhy : i₁ hM * y = φ (hM * cM, cM) := by
      rw [hhφ, hyφ, ← map_mul]
      congr 1
      ext <;> simp
    rw [hhy, ← map_pow]
    rw [show (hM * cM, cM) ^ 2 = (-1, -1) by decide]
    rw [hφ (-1, -1)]
    rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
    exact ht2
  have hcomm_hM_x : Commute (i₁ hM) x := by
    rw [hhφ, hxφ]
    show φ (hM, 1) * φ (hM, hM) = φ (hM, hM) * φ (hM, 1)
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hconjφ : y⁻¹ * x * y = x⁻¹ := by
    have hArg : (cM, cM)⁻¹ * (hM, hM) * (cM, cM) = (hM, hM)⁻¹ := by
      ext <;> simp [cM_inv_mul_hM_mul_cM]
    calc y⁻¹ * x * y = φ ((cM, cM)⁻¹ * (hM, hM) * (cM, cM)) := by
          simp only [hyφ, hxφ, ← map_inv, ← map_mul]
      _ = φ ((hM, hM)⁻¹) := by rw [hArg]
      _ = x⁻¹ := by
            rw [map_inv]
            exact congrArg (fun z : G => z⁻¹) hxφ.symm
  have hxself : x = x⁻¹ := eq_inv_of_mul_eq_one_right (by simpa [pow_two] using hx2)
  have hyx : Commute y x := by
    have h1 : x * y = y * x⁻¹ := by
      calc x * y = (y * y⁻¹) * x * y := by group
        _ = y * (y⁻¹ * x * y) := by group
        _ = y * x⁻¹ := by rw [hconjφ]
    show y * x = x * y
    rw [h1, ← hxself]
  have hxCx : x ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x)
  have hyCx : y ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyx
  have hhMCx : i₁ hM ∈ centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm_hM_x
  let U : Subgroup G := C ⊓ centralizer ({x} : Set G)
  have hyU : y ∈ U := ⟨hyC, hyCx⟩
  have hhMU : i₁ hM ∈ U := ⟨hhMC, hhMCx⟩
  have hhMyU : i₁ hM * y ∈ U := U.mul_mem hhMU hyU
  have hnorm_le : Subgroup.normalizer (U : Set G) ≤ C := by
    intro c hc
    have hcyU : c * y * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hc y).mp hyU
    have hchyU : c * (i₁ hM * y) * c⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hc (i₁ hM * y)).mp hhMyU
    have hcyK : c * y * c⁻¹ ∈ K := by
      by_contra hnot
      exact hno _ hcyU.1 hnot
        (by rw [show (c * y * c⁻¹) ^ 2 = c * y ^ 2 * c⁻¹ from conj_pow, hy2]; group)
    have hchyK : c * (i₁ hM * y) * c⁻¹ ∈ K := by
      by_contra hnot
      exact hno _ hchyU.1 hnot
        (by rw [show (c * (i₁ hM * y) * c⁻¹) ^ 2 = c * (i₁ hM * y) ^ 2 * c⁻¹ from conj_pow,
          hhMy2]; group)
    have hchMU : c * i₁ hM * c⁻¹ ∈ U := by
      have e : c * i₁ hM * c⁻¹ = (c * (i₁ hM * y) * c⁻¹) * (c * y * c⁻¹)⁻¹ := by group
      rw [e]
      exact U.mul_mem hchyU (U.inv_mem hcyU)
    have hchMK : c * i₁ hM * c⁻¹ ∈ K := by
      have e : c * i₁ hM * c⁻¹ = (c * (i₁ hM * y) * c⁻¹) * (c * y * c⁻¹)⁻¹ := by group
      rw [e]
      exact K.mul_mem hchyK (K.inv_mem hcyK)
    have hck : Commute (c * i₁ hM * c⁻¹) x :=
      Subgroup.mem_centralizer_singleton_iff.mp hchMU.2
    have hcyx : Commute (c * y * c⁻¹) x :=
      Subgroup.mem_centralizer_singleton_iff.mp hcyU.2
    have hcommut := h.commutator_eq_of_commute_x hi₁ hi₂ hchMK hcyK hck hcyx
    have hconj : ⁅c * i₁ hM * c⁻¹, c * y * c⁻¹⁆ = c * t * c⁻¹ := by
      have hy_eq : y = i₁ cM * i₂ cM := rfl
      rw [hy_eq]
      rw [show ⁅c * i₁ hM * c⁻¹, c * (i₁ cM * i₂ cM) * c⁻¹⁆ =
          c * ⁅i₁ hM, i₁ cM * i₂ cM⁆ * c⁻¹ by
            simp only [commutatorElement_def]; group]
      rw [h.commutator_hM_y hi₁]
    rcases hcommut with h1 | h1
    · rw [hconj] at h1
      exfalso
      have ht1 : t = 1 := by
        calc t = c⁻¹ * (c * t * c⁻¹) * c := by group
          _ = 1 := by rw [h1]; group
      have h2 : orderOf t = 1 := by rw [ht1, orderOf_one]
      rw [h.orderOf_t] at h2
      exact absurd h2 (by norm_num)
    · rw [hconj] at h1
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc c * t = (c * t * c⁻¹) * c := by group
          _ = t * c := by rw [h1])
  have hP : IsPGroup 2 U := by
    refine IsPGroup.of_card_dvd_pow (n := 5) ?_
    rw [show (2 : ℕ) ^ 5 = 32 by norm_num]
    exact h.card_centralizer_inf_dvd hi₁ hi₂
  have hUSyl : CFSG.ABGLocalTools.IsSylowOf 2 U (C ⊓ centralizer ({x} : Set G)) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_rfl, hP, ?_⟩
    show ¬ 2 ∣ U.relIndex U
    rw [Subgroup.relIndex_self]
    norm_num
  have hN : Subgroup.normalizer (U : Set G) ⊓ centralizer ({x} : Set G) ≤ C :=
    inf_le_left.trans hnorm_le
  have hcard64 : Nat.card U = 64 := h.card_eq_sixtyFour_of_isSylowOf hx_conj hUSyl hN
  have hdiv : Nat.card U ∣ 32 := h.card_centralizer_inf_dvd hi₁ hi₂
  have h6432 : (64 : ℕ) ∣ 32 := by rw [← hcard64]; exact hdiv
  exact absurd h6432 (by norm_num)

end CFSG.OddTranspositions.PartThree.Wong
