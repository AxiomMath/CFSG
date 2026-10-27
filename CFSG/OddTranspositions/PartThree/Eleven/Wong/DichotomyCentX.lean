module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.NormalForm
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentLocal

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

theorem WongHyp.sq_eq_of_mem_sup_of_orderOf_eq_four (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {k : G}
    (hk : k ∈ i₁.range ⊔ i₂.range) (hk4 : orderOf k = 4) : k ^ 2 = t := by
  have hMsq : ∀ y : SL5, y ^ 2 ≠ hM := by
    intro y hy
    have hc : Commute y hM := by
      rw [commute_iff_eq]
      calc y * hM = y * y ^ 2 := by rw [hy]
        _ = y ^ 2 * y := by rw [pow_two]; group
        _ = hM * y := by rw [hy]
    rcases (commute_hM_iff y).mp hc with rfl | rfl | rfl | rfl
    · exact absurd hy (by decide)
    · exact absurd hy (by decide)
    · exact absurd hy (by decide)
    · exact absurd hy (by decide)
  have hnot : ∀ x : SL5, x ^ 4 ≠ -1 := by
    intro x hx
    have hx2 : (x ^ 2) ^ 2 = -1 := by rw [← pow_mul]; exact hx
    obtain ⟨c, hc⟩ := exists_conj_hM_of_sq_eq_neg_one hx2
    exact hMsq (c * x * c⁻¹) (by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
      exact hc)
  have hcommSL : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  obtain ⟨g, g', hk_eq⟩ := (mem_sup_iff hcommSL).mp hk
  have hcomm : Commute (i₁ g) (i₂ g') := hcommSL g g'
  have hkpow : k ^ 4 = 1 := by rw [← hk4, pow_orderOf_eq_one]
  have h4 : i₁ (g ^ 4) * i₂ (g' ^ 4) = 1 := by
    rw [map_pow i₁ g 4, map_pow i₂ g' 4, ← hcomm.mul_pow 4, hk_eq]
    exact hkpow
  have hcases := (prodHom_eq_one_iff hi₁ hi₂ h.orderOf_t h.inf_eq).mp h4
  have hg4 : g ^ 4 = 1 := by
    rcases hcases with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd h1 (hnot g)
  have hg'4 : g' ^ 4 = 1 := by
    rcases hcases with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact h1
    · exact absurd h1 (hnot g')
  have hg2 : g ^ 2 = 1 ∨ g ^ 2 = -1 :=
    sl5_eq_one_or_neg_one_of_mul_self (by rw [← pow_two, ← pow_mul]; exact hg4)
  have hg'2 : g' ^ 2 = 1 ∨ g' ^ 2 = -1 :=
    sl5_eq_one_or_neg_one_of_mul_self (by rw [← pow_two, ← pow_mul]; exact hg'4)
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
  have hmem1 : i₁ (g ^ 2) = 1 ∨ i₁ (g ^ 2) = t := by
    rcases hg2 with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1, ← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq]
  have hmem2 : i₂ (g' ^ 2) = 1 ∨ i₂ (g' ^ 2) = t := by
    rcases hg'2 with h1 | h1
    · left; rw [h1, map_one]
    · right; rw [h1, ← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
  have hk2 : k ^ 2 = i₁ (g ^ 2) * i₂ (g' ^ 2) := by
    rw [← hk_eq, hcomm.mul_pow 2, ← map_pow i₁ g 2, ← map_pow i₂ g' 2]
  have hk2ne : k ^ 2 ≠ 1 := by
    intro h1
    have hdvd : orderOf k ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    rw [hk4] at hdvd
    exact absurd hdvd (by norm_num)
  rcases hmem1 with h1 | h1 <;> rcases hmem2 with h2 | h2
  · exact absurd (by rw [hk2, h1, h2, one_mul]) hk2ne
  · rw [hk2, h1, h2, one_mul]
  · rw [hk2, h1, h2, mul_one]
  · exact absurd (by rw [hk2, h1, h2, ht2]) hk2ne

theorem WongHyp.commutator_eq_of_commute_x (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {k k' : G}
    (hk : k ∈ i₁.range ⊔ i₂.range) (hk' : k' ∈ i₁.range ⊔ i₂.range)
    (hkx : Commute k (i₁ hM * i₂ hM)) (hk'x : Commute k' (i₁ hM * i₂ hM)) :
    ⁅k, k'⁆ = 1 ∨ ⁅k, k'⁆ = t := by
  have hcommSL : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hprod : ∀ x y x' y' : SL5,
      (i₁ x * i₂ y) * (i₁ x' * i₂ y') = i₁ (x * x') * i₂ (y * y') := by
    intro x y x' y'
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (i₂ y), ← (hcommSL x' y).eq,
      mul_assoc (i₁ x'), ← mul_assoc]
  have hchar : ∀ x y : SL5, Commute (i₁ x * i₂ y) (i₁ hM * i₂ hM) ↔
      (hM * x = x * hM ∧ hM * y = y * hM) ∨
        (hM * x = -(x * hM) ∧ hM * y = -(y * hM)) := by
    intro x y
    rw [commute_iff_eq, hprod x y hM hM, hprod hM hM x y,
      prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcommSL h.inf_eq]
  have hc1 : cM⁻¹ = -cM :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← pow_two, cM_sq, neg_neg])
  have hc2 : (-cM)⁻¹ = cM :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul, ← pow_two, cM_sq, neg_neg])
  have hc3 : (hM * cM)⁻¹ = -(hM * cM) :=
    inv_eq_of_mul_eq_one_right (by rw [mul_neg, ← pow_two, hM_mul_cM_sq, neg_neg])
  have hc4 : (-(hM * cM))⁻¹ = hM * cM :=
    inv_eq_of_mul_eq_one_right (by rw [neg_mul, ← pow_two, hM_mul_cM_sq, neg_neg])
  have hcomm_hM : ∀ x : SL5, hM * x = x * hM → x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM := by
    intro x hx
    have hc : Commute x hM := by rw [commute_iff_eq]; exact hx.symm
    exact (commute_hM_iff x).mp hc
  have hcomm_inv : ∀ x : SL5, hM * x = -(x * hM) →
      x = cM ∨ x = -cM ∨ x = hM * cM ∨ x = -(hM * cM) := by
    intro x hx
    have hx' : hM * x = x * hM⁻¹ := by rw [hx, ← mul_neg, neg_hM]
    have h1 : x⁻¹ * hM * x = hM⁻¹ := by
      calc x⁻¹ * hM * x = x⁻¹ * (hM * x) := by group
        _ = x⁻¹ * (x * hM⁻¹) := by rw [hx']
        _ = hM⁻¹ := by group
    rcases (conj_hM_eq_inv_iff x⁻¹).mp (by simpa using h1) with h1 | h1 | h1 | h1
    · right; left; rw [← inv_inv x, h1, hc1]
    · left; rw [← inv_inv x, h1, hc2]
    · right; right; right; rw [← inv_inv x, h1, hc3]
    · right; right; left; rw [← inv_inv x, h1, hc4]
  have hQ8comm : ∀ x y : SL5,
      x ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) →
      y ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) →
      ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = -1 := by
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide
  obtain ⟨g, g', hk_eq⟩ := (mem_sup_iff hcommSL).mp hk
  obtain ⟨f, f', hk'_eq⟩ := (mem_sup_iff hcommSL).mp hk'
  have hkx' : Commute (i₁ g * i₂ g') (i₁ hM * i₂ hM) := by rw [hk_eq]; exact hkx
  have hk'x' : Commute (i₁ f * i₂ f') (i₁ hM * i₂ hM) := by rw [hk'_eq]; exact hk'x
  have hgQ : g ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar g g').mp hkx' with ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases hcomm_hM g h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv g h1 with hh | hh | hh | hh <;> simp [hh]
  have hg'Q : g' ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar g g').mp hkx' with ⟨-, h1⟩ | ⟨-, h1⟩
    · rcases hcomm_hM g' h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv g' h1 with hh | hh | hh | hh <;> simp [hh]
  have hfQ : f ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar f f').mp hk'x' with ⟨h1, -⟩ | ⟨h1, -⟩
    · rcases hcomm_hM f h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv f h1 with hh | hh | hh | hh <;> simp [hh]
  have hf'Q : f' ∈ ({1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)} : Set SL5) := by
    rcases (hchar f f').mp hk'x' with ⟨-, h1⟩ | ⟨-, h1⟩
    · rcases hcomm_hM f' h1 with hh | hh | hh | hh <;> simp [hh]
    · rcases hcomm_inv f' h1 with hh | hh | hh | hh <;> simp [hh]
  have hgf : ⁅g, f⁆ = 1 ∨ ⁅g, f⁆ = -1 := hQ8comm g f hgQ hfQ
  have hg'f' : ⁅g', f'⁆ = 1 ∨ ⁅g', f'⁆ = -1 := hQ8comm g' f' hg'Q hf'Q
  have hfactor : ⁅k, k'⁆ = i₁ ⁅g, f⁆ * i₂ ⁅g', f'⁆ := by
    rw [show k = i₁ g * i₂ g' from hk_eq.symm, show k' = i₁ f * i₂ f' from hk'_eq.symm]
    rw [show i₁ g * i₂ g' = prodHom hcommSL (g, g') from rfl,
      show i₁ f * i₂ f' = prodHom hcommSL (f, f') from rfl]
    rw [← map_commutatorElement (prodHom hcommSL) (g, g') (f, f'), prodHom_apply]
    rfl
  have hmem : ∀ e : SL5, e = 1 ∨ e = -1 → i₁ e = 1 ∨ i₁ e = t := by
    rintro e (rfl | rfl)
    · left; rw [map_one]
    · right; rw [← eq_i1_neg_one hi₁ h.orderOf_t h.inf_eq]
  have hmem' : ∀ e : SL5, e = 1 ∨ e = -1 → i₂ e = 1 ∨ i₂ e = t := by
    rintro e (rfl | rfl)
    · left; rw [map_one]
    · right; rw [← eq_i2_neg_one hi₂ h.orderOf_t h.inf_eq]
  have ht2 : t * t = 1 := by rw [← pow_two, ← h.orderOf_t, pow_orderOf_eq_one]
  rw [hfactor]
  rcases hmem _ hgf with h1 | h1 <;> rcases hmem' _ hg'f' with h2 | h2 <;> rw [h1, h2]
  · left; rw [one_mul]
  · right; rw [one_mul]
  · right; rw [mul_one]
  · left; rw [ht2]

theorem WongHyp.card_centralizer_inf_dvd [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) :
    Nat.card (centralizer ({t} : Set G) ⊓ centralizer ({i₁ hM * i₂ hM} : Set G) : Subgroup G) ∣
      32 := by
  set C : Subgroup G := centralizer ({t} : Set G) with hC
  set Dc : Subgroup G := centralizer ({i₁ hM * i₂ hM} : Set G) with hDc
  set K : Subgroup G := i₁.range ⊔ i₂.range with hK
  have hcommSL : ∀ x y : SL5, Commute (i₁ x) (i₂ y) :=
    fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hKleC : K ≤ C := by rw [hK, hC]; exact sup_le_centralizer h
  have hrelKC : K.relIndex C = 2 := by rw [hK, hC]; exact h.relIndex_eq
  have hcardKD : Nat.card (K ⊓ Dc : Subgroup G) = 16 := by
    have hprod : ∀ a b a' b' : SL5,
        (i₁ a * i₂ b) * (i₁ a' * i₂ b') = i₁ (a * a') * i₂ (b * b') := by
      intro a b a' b'
      rw [map_mul, map_mul, mul_assoc, ← mul_assoc (i₂ b), ← (hcommSL a' b).eq,
        mul_assoc (i₁ a'), ← mul_assoc]
    have hchar : ∀ x y : SL5, i₁ x * i₂ y ∈ Dc ↔
        (hM * x = x * hM ∧ hM * y = y * hM) ∨
          (hM * x = -(x * hM) ∧ hM * y = -(y * hM)) := by
      intro x y
      rw [hDc]
      rw [mem_centralizer_singleton_iff, hprod x y hM hM, hprod hM hM x y,
        prodHom_eq_iff hi₁ hi₂ h.orderOf_t hcommSL h.inf_eq]
    have hmap : (comap (prodHom hcommSL) Dc).map (prodHom hcommSL) = K ⊓ Dc := by
      rw [map_comap_eq, range_prodHom]
    have hker : (prodHom hcommSL).ker ≤ comap (prodHom hcommSL) Dc :=
      fun p hp => by rw [mem_comap, MonoidHom.mem_ker.mp hp]; exact one_mem _
    have hset : ((comap (prodHom hcommSL) Dc : Subgroup (SL5 × SL5)) : Set (SL5 × SL5)) =
        ↑((centHM ×ˢ centHM) ∪ (invHM ×ˢ invHM)) := by
      ext ⟨x, y⟩
      simp only [SetLike.mem_coe, mem_comap, prodHom_apply, Finset.coe_union, Finset.coe_product,
        Set.mem_union, Set.mem_prod]
      rw [hchar, hM_mul_eq_iff, hM_mul_eq_iff, hM_mul_eq_neg_iff, hM_mul_eq_neg_iff]
      simp only [centHM, invHM, Finset.mem_insert, Finset.mem_singleton]
    have hQ : Nat.card (comap (prodHom hcommSL) Dc) = 32 := by
      rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
        card_centHM_product_union]
    have h2 := relIndex_mul_card (H := (prodHom hcommSL).ker)
      (K := comap (prodHom hcommSL) Dc)
    rw [relIndex_ker, hmap, inf_eq_left.mpr hker,
      card_ker_prodHom hi₁ hi₂ h.orderOf_t hcommSL h.inf_eq, hQ] at h2
    omega
  have hrel : (K ⊓ Dc).relIndex (C ⊓ Dc) ≤ 2 := by
    have heq : (K ⊓ Dc).relIndex (C ⊓ Dc) = K.relIndex (C ⊓ Dc) := by
      have h1 : K ⊓ Dc = (C ⊓ Dc) ⊓ K := by
        rw [inf_comm K Dc, inf_comm C Dc, inf_assoc, inf_eq_right.mpr hKleC]
      rw [h1]
      exact inf_relIndex_left (C ⊓ Dc) K
    rw [heq]
    calc K.relIndex (C ⊓ Dc) ≤ K.relIndex C :=
          relIndex_le_of_le_right inf_le_left (by rw [hrelKC]; norm_num)
      _ = 2 := hrelKC
  have key := relIndex_mul_card (H := K ⊓ Dc) (K := C ⊓ Dc)
  have hinf : (K ⊓ Dc) ⊓ (C ⊓ Dc) = K ⊓ Dc := inf_eq_left.mpr (inf_le_inf hKleC le_rfl)
  rw [hinf, hcardKD] at key
  have hcases : (K ⊓ Dc).relIndex (C ⊓ Dc) = 1 ∨ (K ⊓ Dc).relIndex (C ⊓ Dc) = 2 := by
    have h0 : 0 < (K ⊓ Dc).relIndex (C ⊓ Dc) := by
      by_contra hc
      have hc0 : (K ⊓ Dc).relIndex (C ⊓ Dc) = 0 := Nat.eq_zero_of_not_pos hc
      rw [hc0, zero_mul] at key
      have hpos : 0 < Nat.card (C ⊓ Dc : Subgroup G) := by
        rw [Nat.card_pos_iff]
        exact ⟨⟨1, one_mem _⟩, inferInstance⟩
      omega
    omega
  rw [← key]
  rcases hcases with h1 | h2
  · rw [h1]; norm_num
  · rw [h2]

theorem normalizer_le_centralizer_of_commutator (ht : t ≠ 1) {U : Subgroup G}
    (hU : ∀ p ∈ U, ∀ q ∈ U, ⁅p, q⁆ = 1 ∨ ⁅p, q⁆ = t) {a b : G} (ha : a ∈ U) (hb : b ∈ U)
    (hab : ⁅a, b⁆ = t) : normalizer (U : Set G) ≤ centralizer ({t} : Set G) := by
  intro g hg
  have hga : g * a * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg a).mp ha
  have hgb : g * b * g⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hg b).mp hb
  have hcomm := hU _ hga _ hgb
  rw [show ⁅g * a * g⁻¹, g * b * g⁻¹⁆ = g * ⁅a, b⁆ * g⁻¹ by
    simp only [commutatorElement_def]; group] at hcomm
  rw [hab] at hcomm
  rcases hcomm with h1 | h1
  · exfalso
    exact ht (by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc g * t = g * t * g⁻¹ * g := by group
        _ = t * g := by rw [h1])

end CFSG.OddTranspositions.PartThree.Wong
