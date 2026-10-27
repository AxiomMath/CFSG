module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.DichotomyPreserveX
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
import CFSG.OddTranspositions.PartThree.Eleven.Wong.OddCore

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.exists_commute_sq_eq_of_trivial [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hn2 : n ^ 2 = 1 ∨ n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ x ∧ n⁻¹ * i₂ x * n = i₂ x) {v : G}
    (hvC : v ∈ centralizer ({t} : Set G)) (hvK : v ∉ i₁.range ⊔ i₂.range) (hv : v ^ 2 = 1) :
    ∃ a : G, Commute a v ∧ a ^ 2 = t := by
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hnK' : n⁻¹ ∉ i₁.range ⊔ i₂.range := fun hnk =>
    hnK (by simpa using (i₁.range ⊔ i₂.range).inv_mem hnk)
  have hv_mem : v * n⁻¹ ∈ i₁.range ⊔ i₂.range :=
    h.mul_mem_sup_of_not_mem hvC (inv_mem hn) hvK hnK'
  obtain ⟨g, g', hgg'⟩ := (mem_sup_iff hcomm).mp hv_mem
  have hv_eq : v = i₁ g * i₂ g' * n := by rw [hgg']; group
  have hn_i1 : ∀ x : SL5, Commute (i₁ x) n := fun x => by
    rw [commute_iff_eq]
    have hx := (hact x).1
    calc i₁ x * n = n * (n⁻¹ * i₁ x * n) := by group
      _ = n * i₁ x := by rw [hx]
  have hn_i2 : ∀ x : SL5, Commute (i₂ x) n := fun x => by
    rw [commute_iff_eq]
    have hx := (hact x).2
    calc i₂ x * n = n * (n⁻¹ * i₂ x * n) := by group
      _ = n * i₂ x := by rw [hx]
  have hPn : Commute (i₁ g * i₂ g') n := (hn_i1 g).mul_left (hn_i2 g')
  have hP2 : (i₁ g * i₂ g') * (i₁ g * i₂ g') = i₁ (g * g) * i₂ (g' * g') := by
    calc (i₁ g * i₂ g') * (i₁ g * i₂ g')
        = i₁ g * (i₂ g' * i₁ g) * i₂ g' := by group
      _ = i₁ g * (i₁ g * i₂ g') * i₂ g' := by rw [(hcomm g g').eq.symm]
      _ = i₁ (g * g) * i₂ (g' * g') := by rw [map_mul, map_mul]; group
  have hv2 : v ^ 2 = i₁ (g * g) * i₂ (g' * g') * n ^ 2 := by
    rw [hv_eq, pow_two]
    calc (i₁ g * i₂ g' * n) * (i₁ g * i₂ g' * n)
        = (i₁ g * i₂ g') * (n * (i₁ g * i₂ g')) * n := by group
      _ = (i₁ g * i₂ g') * ((i₁ g * i₂ g') * n) * n := by rw [← hPn.eq]
      _ = (i₁ g * i₂ g') * (i₁ g * i₂ g') * (n * n) := by group
      _ = (i₁ (g * g) * i₂ (g' * g')) * (n * n) := by rw [hP2]
      _ = i₁ (g * g) * i₂ (g' * g') * n ^ 2 := by rw [pow_two]
  have hsq : i₁ (g * g) * i₂ (g' * g') * n ^ 2 = 1 := by rw [← hv2, hv]
  have hg2 : g ^ 2 = 1 ∨ g ^ 2 = -1 := by
    rcases hn2 with hn2 | hn2
    · have h1 : i₁ (g * g) * i₂ (g' * g') = 1 := by simpa [hn2] using hsq
      rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with ⟨hgg, _⟩ | ⟨hgg, _⟩
      · exact Or.inl (by rw [pow_two]; exact hgg)
      · exact Or.inr (by rw [pow_two]; exact hgg)
    · have h1 : i₁ (g * g) * i₂ ((g' * g') * (-1)) = 1 := by
        have h' := hsq
        rw [hn2, show t = i₂ (-1) from eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq] at h'
        rwa [mul_assoc, ← map_mul] at h'
      rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with ⟨hgg, _⟩ | ⟨hgg, _⟩
      · exact Or.inl (by rw [pow_two]; exact hgg)
      · exact Or.inr (by rw [pow_two]; exact hgg)
  have hg4 : g ^ 4 = 1 := by
    have h : g ^ 4 = (g ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [h]
    rcases hg2 with h2 | h2 <;> rw [h2]
    · exact one_pow 2
    · rw [pow_two, neg_mul_neg, one_mul]
  obtain ⟨g'', hg''2, hgg''⟩ := exists_sq_eq_neg_one_commute hg4
  refine ⟨i₁ g'', ?_, ?_⟩
  · rw [hv_eq]
    exact ((hgg''.symm.map i₁).mul_right (hcomm g'' g')).mul_right (hn_i1 g'')
  · rw [pow_two, ← map_mul, ← pow_two, hg''2]
    exact (eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq).symm

theorem WongHyp.exists_commute_sq_eq_of_outer_one [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hn2 : n ^ 2 = 1 ∨ n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ x) {v : G}
    (hvC : v ∈ centralizer ({t} : Set G)) (hvK : v ∉ i₁.range ⊔ i₂.range) (hv : v ^ 2 = 1) :
    ∃ a : G, Commute a v ∧ a ^ 2 = t := by
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hnK' : n⁻¹ ∉ i₁.range ⊔ i₂.range := fun hnk =>
    hnK (by simpa using (i₁.range ⊔ i₂.range).inv_mem hnk)
  have hv_mem : v * n⁻¹ ∈ i₁.range ⊔ i₂.range :=
    h.mul_mem_sup_of_not_mem hvC (inv_mem hn) hvK hnK'
  obtain ⟨g, g', hgg'⟩ := (mem_sup_iff hcomm).mp hv_mem
  have hv_eq : v = i₁ g * i₂ g' * n := by rw [hgg']; group
  have hn_i1' : ∀ x : SL5, n * i₁ x = i₁ (deltaAut x) * n := fun x => by
    have hx := (hact (deltaAut x)).1
    rw [deltaAut_deltaAut] at hx
    calc n * i₁ x = n * (n⁻¹ * i₁ (deltaAut x) * n) := by rw [hx]
      _ = i₁ (deltaAut x) * n := by group
  have hn_i2 : ∀ x : SL5, Commute (i₂ x) n := fun x => by
    rw [commute_iff_eq]
    have hx := (hact x).2
    calc i₂ x * n = n * (n⁻¹ * i₂ x * n) := by group
      _ = n * i₂ x := by rw [hx]
  have hnP : n * (i₁ g * i₂ g') = (i₁ (deltaAut g) * i₂ g') * n := by
    rw [← mul_assoc, hn_i1' g, mul_assoc, ← (hn_i2 g').eq, mul_assoc]
  have hPQ : (i₁ g * i₂ g') * (i₁ (deltaAut g) * i₂ g') =
      i₁ (g * deltaAut g) * i₂ (g' * g') := by
    calc (i₁ g * i₂ g') * (i₁ (deltaAut g) * i₂ g')
        = i₁ g * (i₂ g' * i₁ (deltaAut g)) * i₂ g' := by group
      _ = i₁ g * (i₁ (deltaAut g) * i₂ g') * i₂ g' := by
            rw [(hcomm (deltaAut g) g').eq.symm]
      _ = i₁ (g * deltaAut g) * i₂ (g' * g') := by rw [map_mul, map_mul]; group
  have hv2 : v ^ 2 = i₁ (g * deltaAut g) * i₂ (g' * g') * n ^ 2 := by
    rw [hv_eq, pow_two]
    calc (i₁ g * i₂ g' * n) * (i₁ g * i₂ g' * n)
        = (i₁ g * i₂ g') * (n * (i₁ g * i₂ g')) * n := by group
      _ = (i₁ g * i₂ g') * ((i₁ (deltaAut g) * i₂ g') * n) * n := by rw [hnP]
      _ = (i₁ g * i₂ g') * (i₁ (deltaAut g) * i₂ g') * (n * n) := by group
      _ = (i₁ (g * deltaAut g) * i₂ (g' * g')) * (n * n) := by rw [hPQ]
      _ = i₁ (g * deltaAut g) * i₂ (g' * g') * n ^ 2 := by rw [pow_two]
  have hsq : i₁ (g * deltaAut g) * i₂ (g' * g') * n ^ 2 = 1 := by rw [← hv2, hv]
  have hg2 : g' ^ 2 = 1 ∨ g' ^ 2 = -1 := by
    rcases hn2 with hn2 | hn2
    · have h1 : i₁ (g * deltaAut g) * i₂ (g' * g') = 1 := by simpa [hn2] using hsq
      rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with ⟨_, hgg⟩ | ⟨_, hgg⟩
      · exact Or.inl (by rw [pow_two]; exact hgg)
      · exact Or.inr (by rw [pow_two]; exact hgg)
    · have h1 : i₁ ((g * deltaAut g) * (-1)) * i₂ (g' * g') = 1 := by
        have h' := hsq
        rw [hn2, show t = i₁ (-1) from eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq] at h'
        rwa [mul_assoc, ← (hcomm (-1) (g' * g')).eq, ← mul_assoc, ← map_mul] at h'
      rcases (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h1 with ⟨_, hgg⟩ | ⟨_, hgg⟩
      · exact Or.inl (by rw [pow_two]; exact hgg)
      · exact Or.inr (by rw [pow_two]; exact hgg)
  have hg4 : g' ^ 4 = 1 := by
    have h : g' ^ 4 = (g' ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    rw [h]
    rcases hg2 with h2 | h2 <;> rw [h2]
    · exact one_pow 2
    · rw [pow_two, neg_mul_neg, one_mul]
  obtain ⟨g'', hg''2, hgg''⟩ := exists_sq_eq_neg_one_commute hg4
  refine ⟨i₂ g'', ?_, ?_⟩
  · rw [hv_eq]
    exact (((hcomm g g'').symm).mul_right (hgg''.symm.map i₂)).mul_right (hn_i2 g'')
  · rw [pow_two, ← map_mul, ← pow_two, hg''2]
    exact (eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq).symm

theorem WongHyp.false_of_trivial [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hn2 : n ^ 2 = 1 ∨ n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ x ∧ n⁻¹ * i₂ x * n = i₂ x) : False := by
  obtain ⟨c, hcC, hcne⟩ := exists_conj_mem_centralizer_ne h.orderOf_t h.sup_oddCore_ne_top
  set v := c⁻¹ * t * c with hvdef
  have hvC : v ∈ centralizer ({t} : Set G) := by rw [hvdef]; exact hcC
  have hvt : v ≠ t := by rw [hvdef]; exact hcne
  have hsc : SemiconjBy c⁻¹ t v := by
    rw [hvdef]
    show c⁻¹ * t = (c⁻¹ * t * c) * c⁻¹
    group
  have hv_ord : orderOf v = 2 := by
    rw [hvdef, ← SemiconjBy.orderOf_eq c⁻¹ hsc, h.orderOf_t]
  have hv2 : v ^ 2 = 1 := by rw [← hv_ord, pow_orderOf_eq_one]
  have hvisConj : IsConj t v := isConj_iff.mpr ⟨c⁻¹, by rw [hvdef]; group⟩
  by_cases hvK : v ∈ i₁.range ⊔ i₂.range
  · obtain ⟨k, _, hk⟩ := exists_mem_sup_conj_eq h hi₁ hi₂ hvK hv_ord hvt
    have hxv : IsConj (i₁ hM * i₂ hM) v := isConj_iff.mpr ⟨k, hk⟩
    exact not_isConj_x_of_trivial h hi₁ hi₂ hn hnK hact (hxv.trans hvisConj.symm).symm
  · obtain ⟨a, hav, ha2⟩ :=
      exists_commute_sq_eq_of_trivial h hi₁ hi₂ hn hnK hn2 hact hvC hvK hv2
    exact not_isConj_x_of_trivial h hi₁ hi₂ hn hnK hact
      (isConj_x_of_commute_sq_eq h hi₁ hi₂ hvisConj hvt hav ha2)

theorem WongHyp.false_of_outer_one [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range)
    (hn2 : n ^ 2 = 1 ∨ n ^ 2 = t)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ x) : False := by
  obtain ⟨c, hcC, hcne⟩ := exists_conj_mem_centralizer_ne h.orderOf_t h.sup_oddCore_ne_top
  set v := c⁻¹ * t * c with hvdef
  have hvC : v ∈ centralizer ({t} : Set G) := by rw [hvdef]; exact hcC
  have hvt : v ≠ t := by rw [hvdef]; exact hcne
  have hsc : SemiconjBy c⁻¹ t v := by
    rw [hvdef]
    show c⁻¹ * t = (c⁻¹ * t * c) * c⁻¹
    group
  have hv_ord : orderOf v = 2 := by
    rw [hvdef, ← SemiconjBy.orderOf_eq c⁻¹ hsc, h.orderOf_t]
  have hv2 : v ^ 2 = 1 := by rw [← hv_ord, pow_orderOf_eq_one]
  have hvisConj : IsConj t v := isConj_iff.mpr ⟨c⁻¹, by rw [hvdef]; group⟩
  by_cases hvK : v ∈ i₁.range ⊔ i₂.range
  · obtain ⟨k, _, hk⟩ := exists_mem_sup_conj_eq h hi₁ hi₂ hvK hv_ord hvt
    have hxv : IsConj (i₁ hM * i₂ hM) v := isConj_iff.mpr ⟨k, hk⟩
    exact not_isConj_x_of_outer_one h hi₁ hi₂ hn hact (hxv.trans hvisConj.symm).symm
  · obtain ⟨a, hav, ha2⟩ :=
      exists_commute_sq_eq_of_outer_one h hi₁ hi₂ hn hnK hn2 hact hvC hvK hv2
    exact not_isConj_x_of_outer_one h hi₁ hi₂ hn hact
      (isConj_x_of_commute_sq_eq h hi₁ hi₂ hvisConj hvt hav ha2)

end CFSG.OddTranspositions.PartThree.Wong
