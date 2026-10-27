module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.NormalForm
import CFSG.OddTranspositions.PartThree.Eleven.Wong.Basic
import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentralProduct
import CFSG.OddTranspositions.PartThree.Eleven.Wong.SylowLift

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup
open CFSG.ABGLocalTools
open scoped commutatorElement
open scoped Pointwise

variable {G : Type} [Group G] {t : G} {i₁ i₂ : SL5 →* G}

set_option maxRecDepth 4000 in
theorem WongHyp.exists_sylow_le_of_outer_outer [Finite G] (h : WongHyp t i₁.range i₂.range)
    (hi₁ : Function.Injective i₁) (hi₂ : Function.Injective i₂) {n : G}
    (hn : n ∈ centralizer ({t} : Set G)) (hnK : n ∉ i₁.range ⊔ i₂.range) (hn2 : n ^ 2 = 1)
    (hact : ∀ x, n⁻¹ * i₁ x * n = i₁ (deltaAut x) ∧ n⁻¹ * i₂ x * n = i₂ (deltaAut x)) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ centralizer ({t} : Set G) := by
  let Q8 : Subgroup SL5 :=
    { carrier := {x | x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM ∨ x = cM ∨ x = -cM ∨
          x = hM * cM ∨ x = -(hM * cM)}
      mul_mem' := by decide
      one_mem' := by decide
      inv_mem' := by decide }
  have mem_Q8 : ∀ x : SL5, x ∈ Q8 ↔ (x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM ∨ x = cM ∨
      x = -cM ∨ x = hM * cM ∨ x = -(hM * cM)) := by
    intro x
    change x ∈ ({y : SL5 | y = 1 ∨ y = -1 ∨ y = hM ∨ y = -hM ∨ y = cM ∨ y = -cM ∨
      y = hM * cM ∨ y = -(hM * cM)} : Set SL5) ↔ _
    rfl
  have hneg_ord : orderOf (-1 : SL5) = 2 := by
    apply orderOf_eq_prime <;> decide
  have hQ8_closure : Q8 = Subgroup.closure ({hM, cM} : Set SL5) := by
    apply le_antisymm
    · intro x hx
      rcases (mem_Q8 x).mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem _
      · rw [← hM_sq]; exact pow_mem (subset_closure (by simp)) 2
      · exact subset_closure (by simp)
      · rw [neg_hM]; exact inv_mem (subset_closure (by simp))
      · exact subset_closure (by simp)
      · rw [show -cM = cM⁻¹ by decide]; exact inv_mem (subset_closure (by simp))
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · rw [show -(hM * cM) = (hM * cM)⁻¹ by decide]
        exact inv_mem (mul_mem (subset_closure (by simp)) (subset_closure (by simp)))
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact (mem_Q8 hM).mpr (Or.inr (Or.inr (Or.inl rfl)))
      · exact (mem_Q8 cM).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have card_Q8 : Nat.card Q8 = 8 := by
    let q8Fin : Finset SL5 := {1, -1, hM, -hM, cM, -cM, hM * cM, -(hM * cM)}
    have hset : (Q8 : Set SL5) = (q8Fin : Set SL5) := by
      ext x
      change x ∈ Q8 ↔ x ∈ (q8Fin : Set SL5)
      rw [mem_Q8 x]
      simp only [q8Fin, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
    change Nat.card (Q8 : Set SL5) = 8
    rw [Nat.card_coe_set_eq, hset, Set.ncard_coe_finset]
    decide
  have hcent_Q8 : Subgroup.centralizer (Q8 : Set SL5) = zpowers (-1 : SL5) := by
    ext x
    rw [Subgroup.mem_centralizer_iff, mem_zpowers_of_orderOf_eq_two hneg_ord]
    constructor
    · intro hx
      have h1 : hM * x = x * hM := hx hM ((mem_Q8 hM).mpr (Or.inr (Or.inr (Or.inl rfl))))
      have h2 : cM * x = x * cM :=
        hx cM ((mem_Q8 cM).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      rcases (commute_hM_iff x).mp h1.symm with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
    · rintro (rfl | rfl)
      · intro y hy
        exact (mul_one y).trans (one_mul y).symm
      · intro y hy
        rcases (mem_Q8 y).mp hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hdelta_Q8 : Q8.map deltaAut.toMonoidHom = Q8 := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      rcases (mem_Q8 y).mp hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (mem_Q8 _).mpr (by decide)
    · intro hx
      rw [Subgroup.mem_map]
      refine ⟨deltaAut x, ?_, by simp⟩
      rcases (mem_Q8 x).mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact (mem_Q8 _).mpr (by decide)
  have hcomm : ∀ x y : SL5, Commute (i₁ x) (i₂ y) := fun x y => h.commute _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have hmeet : i₁.range ⊓ i₂.range = zpowers t := h.inf_eq
  have ht : orderOf t = 2 := h.orderOf_t
  have ht1 : t = i₁ (-1) := eq_i1_neg_one hi₁ ht hmeet
  have ht2 : t = i₂ (-1) := eq_i2_neg_one hi₂ ht hmeet
  have ne_neg_self : ∀ y : SL5, y ≠ -y := by
    intro y hy
    apply sl5_neg_one_ne_one
    calc (-1 : SL5) = -y * y⁻¹ := by rw [neg_mul, mul_inv_cancel]
      _ = y * y⁻¹ := by rw [← hy]
      _ = 1 := mul_inv_cancel y
  have prod_eq_iff : ∀ {x y x' y' : SL5},
      i₁ x * i₂ y = i₁ x' * i₂ y' ↔ (x' = x ∧ y' = y) ∨ (x' = -x ∧ y' = -y) :=
    fun {x y x' y'} => prodHom_eq_iff (inj1 := hi₁) (inj2 := hi₂) (ht := ht) (hcomm := hcomm)
      (hmeet := hmeet)
  have hn_inv : n⁻¹ = n := by
    rw [pow_two] at hn2
    exact inv_eq_of_mul_eq_one_right hn2
  have hact₁ : ∀ x : SL5, n * i₁ x * n⁻¹ = i₁ (deltaAut x) :=
    fun x => by simpa [hn_inv] using (hact x).1
  have hact₂ : ∀ x : SL5, n * i₂ x * n⁻¹ = i₂ (deltaAut x) :=
    fun x => by simpa [hn_inv] using (hact x).2
  have hn_ne_one : n ≠ 1 := fun h1 => hnK (by rw [h1]; exact one_mem _)
  have hn_ord : orderOf n = 2 := orderOf_eq_prime hn2 hn_ne_one
  have card_formula : ∀ {H K : Subgroup G}, H ≤ Subgroup.normalizer (K : Set G) →
      Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
    intro H K hHK
    haveI : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHK
    haveI : (K.subgroupOf (H ⊔ K)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hHK
    have quotient_card := Nat.card_congr
      (QuotientGroup.quotientInfEquivProdNormalizerQuotient H K hHK).toEquiv
    have first_card := (K.subgroupOf H).card_mul_index
    have product_card := (K.subgroupOf (H ⊔ K)).card_mul_index
    rw [Subgroup.index_eq_card] at first_card
    rw [Subgroup.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show K ≤ H ⊔ K from le_sup_right)).toEquiv,
      ← quotient_card] at product_card
    rw [← product_card]
    have hinter : Nat.card (K.subgroupOf H) = Nat.card ↥(H ⊓ K) := by
      rw [← Subgroup.inf_subgroupOf_left K H]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    calc
      Nat.card K * Nat.card (H ⧸ K.subgroupOf H) * Nat.card ↥(H ⊓ K) =
          Nat.card K * (Nat.card ↥(H ⊓ K) * Nat.card (H ⧸ K.subgroupOf H)) := by ac_rfl
      _ = Nat.card K * Nat.card H := by rw [← hinter, first_card]
      _ = Nat.card H * Nat.card K := mul_comm _ _
  let Q : Subgroup G := Q8.map i₁ ⊔ Q8.map i₂
  let U : Subgroup G := Q ⊔ Subgroup.zpowers n
  have hQ_le_K : Q ≤ i₁.range ⊔ i₂.range := by
    change Q8.map i₁ ⊔ Q8.map i₂ ≤ i₁.range ⊔ i₂.range
    exact sup_le (le_trans (Subgroup.map_le_range (f := i₁) Q8) le_sup_left)
      (le_trans (Subgroup.map_le_range (f := i₂) Q8) le_sup_right)
  have hn_not_Q : n ∉ Q := fun hnQ => hnK (hQ_le_K hnQ)
  have hQ_le_C : Q ≤ Subgroup.centralizer ({t} : Set G) :=
    le_trans hQ_le_K h.sup_le_centralizer
  have hU_le_C : U ≤ Subgroup.centralizer ({t} : Set G) := by
    change Q ⊔ Subgroup.zpowers n ≤ Subgroup.centralizer ({t} : Set G)
    exact sup_le hQ_le_C (Subgroup.zpowers_le.mpr hn)
  have hmap_i₁ : (Q8.map i₁).map (↑(MulAut.conj n)) = Q8.map i₁ := by
    change (Q8.map i₁).map (MulAut.conj n).toMonoidHom = Q8.map i₁
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj n).toMonoidHom.comp i₁ = i₁.comp deltaAut.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hact₁ x
    rw [hcomp, ← Subgroup.map_map, hdelta_Q8]
  have hmap_i₂ : (Q8.map i₂).map (↑(MulAut.conj n)) = Q8.map i₂ := by
    change (Q8.map i₂).map (MulAut.conj n).toMonoidHom = Q8.map i₂
    rw [Subgroup.map_map]
    have hcomp : (MulAut.conj n).toMonoidHom.comp i₂ = i₂.comp deltaAut.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hact₂ x
    rw [hcomp, ← Subgroup.map_map, hdelta_Q8]
  have hn_norm_Q : n ∈ Subgroup.normalizer (Q : Set G) := by
    change n ∈ Subgroup.normalizer ((Q8.map i₁ ⊔ Q8.map i₂ : Subgroup G) : Set G)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, hmap_i₁, hmap_i₂]
  have hzp_norm_Q : Subgroup.zpowers n ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr hn_norm_Q
  have hmap_i₁_card : Nat.card (Q8.map i₁) = 8 := by
    rw [Subgroup.card_map_of_injective hi₁, card_Q8]
  have hmap_i₂_card : Nat.card (Q8.map i₂) = 8 := by
    rw [Subgroup.card_map_of_injective hi₂, card_Q8]
  have hnorm_le : Q8.map i₁ ≤ Subgroup.centralizer ((Q8.map i₂ : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact (hcomm a b).eq.symm
  have hnorm : Q8.map i₁ ≤ Subgroup.normalizer ((Q8.map i₂ : Subgroup G) : Set G) :=
    le_trans hnorm_le (Subgroup.centralizer_le_normalizer _)
  have hinter : (Q8.map i₁ ⊓ Q8.map i₂ : Subgroup G) = zpowers t := by
    apply le_antisymm
    · calc Q8.map i₁ ⊓ Q8.map i₂ ≤ i₁.range ⊓ i₂.range :=
          inf_le_inf (Subgroup.map_le_range (f := i₁) Q8) (Subgroup.map_le_range (f := i₂) Q8)
        _ = zpowers t := hmeet
    · refine le_inf ?_ ?_
      · exact Subgroup.zpowers_le.mpr ⟨-1, (mem_Q8 (-1)).mpr (Or.inr (Or.inl rfl)), ht1.symm⟩
      · exact Subgroup.zpowers_le.mpr ⟨-1, (mem_Q8 (-1)).mpr (Or.inr (Or.inl rfl)), ht2.symm⟩
  have hQcard : Nat.card Q = 32 := by
    have hcf := card_formula (H := Q8.map i₁) (K := Q8.map i₂) hnorm
    change Nat.card ↥(Q8.map i₁ ⊔ Q8.map i₂) = 32
    rw [hinter, hmap_i₁_card, hmap_i₂_card, Nat.card_zpowers, ht] at hcf
    omega
  have decomp : ∀ {g : G}, g ∈ Q → ∃ a ∈ Q8, ∃ b ∈ Q8, i₁ a * i₂ b = g := by
    intro g hg
    have hcomm' : ∀ a ∈ Q8.map i₁, ∀ b ∈ Q8.map i₂, Commute a b := by
      intro a ha b hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      exact hcomm a' b'
    have hg' : g ∈ Q8.map i₁ ⊔ Q8.map i₂ := hg
    obtain ⟨a, ha, b, hb, hab⟩ :=
      exists_mul_eq_of_commute (L₁ := Q8.map i₁) (L₂ := Q8.map i₂) hcomm' hg'
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    exact ⟨a', ha', b', hb', hab⟩
  have hhM_Q : i₁ hM ∈ Q := by
    change i₁ hM ∈ Q8.map i₁ ⊔ Q8.map i₂
    exact Subgroup.mem_sup_left ⟨hM, (mem_Q8 hM).mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  have hcM_Q : i₁ cM ∈ Q := by
    change i₁ cM ∈ Q8.map i₁ ⊔ Q8.map i₂
    exact Subgroup.mem_sup_left
      ⟨cM, (mem_Q8 cM).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), rfl⟩
  have hh2M_Q : i₂ hM ∈ Q := by
    change i₂ hM ∈ Q8.map i₁ ⊔ Q8.map i₂
    exact Subgroup.mem_sup_right ⟨hM, (mem_Q8 hM).mpr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  have hc2M_Q : i₂ cM ∈ Q := by
    change i₂ cM ∈ Q8.map i₁ ⊔ Q8.map i₂
    exact Subgroup.mem_sup_right
      ⟨cM, (mem_Q8 cM).mpr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), rfl⟩
  have hhM_U : i₁ hM ∈ U := by
    change i₁ hM ∈ Q ⊔ Subgroup.zpowers n
    exact Subgroup.mem_sup_left hhM_Q
  have hcM_U : i₁ cM ∈ U := by
    change i₁ cM ∈ Q ⊔ Subgroup.zpowers n
    exact Subgroup.mem_sup_left hcM_Q
  have commute_a_of : ∀ {g a b : SL5},
      i₁ g * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₁ g → Commute a g := by
    intro g a b hx
    have hL : i₁ g * (i₁ a * i₂ b) = i₁ (g * a) * i₂ b := by
      calc i₁ g * (i₁ a * i₂ b) = i₁ g * i₁ a * i₂ b := by group
        _ = i₁ (g * a) * i₂ b := by rw [map_mul]
    have hR : (i₁ a * i₂ b) * i₁ g = i₁ (a * g) * i₂ b := by
      calc (i₁ a * i₂ b) * i₁ g = i₁ a * i₂ b * i₁ g := by group
        _ = i₁ a * i₁ g * i₂ b := by
          rw [show i₁ a * i₂ b * i₁ g = i₁ a * (i₂ b * i₁ g) by group,
            show i₂ b * i₁ g = i₁ g * i₂ b by exact (hcomm g b).eq.symm,
            show i₁ a * (i₁ g * i₂ b) = i₁ a * i₁ g * i₂ b by group]
        _ = i₁ (a * g) * i₂ b := by rw [map_mul]
    rw [hL, hR] at hx
    rcases (prod_eq_iff (x := g * a) (y := b) (x' := a * g) (y' := b)).mp hx with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (ne_neg_self b)
  have commute_b_of : ∀ {g a b : SL5},
      i₂ g * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₂ g → Commute b g := by
    intro g a b hx
    have hL : i₂ g * (i₁ a * i₂ b) = i₁ a * i₂ (g * b) := by
      calc i₂ g * (i₁ a * i₂ b) = i₂ g * i₁ a * i₂ b := by group
        _ = i₁ a * i₂ g * i₂ b := by rw [(hcomm a g).eq.symm]
        _ = i₁ a * (i₂ g * i₂ b) := by group
        _ = i₁ a * i₂ (g * b) := by rw [map_mul]
    have hR : (i₁ a * i₂ b) * i₂ g = i₁ a * i₂ (b * g) := by
      calc (i₁ a * i₂ b) * i₂ g = i₁ a * (i₂ b * i₂ g) := by group
        _ = i₁ a * i₂ (b * g) := by rw [map_mul]
    rw [hL, hR] at hx
    rcases (prod_eq_iff (x := a) (y := g * b) (x' := a) (y' := b * g)).mp hx with
      ⟨-, h1⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 (ne_neg_self a)
  have extract : ∀ {y : SL5} {a b : SL5},
      i₁ y * (i₁ a * i₂ b * n) = (i₁ a * i₂ b * n) * i₁ y → a * deltaAut y = y * a := by
    intro y a b hx
    have hn : n * i₁ y = i₁ (deltaAut y) * n := by rw [← hact₁ y]; group
    have hL : i₁ y * (i₁ a * i₂ b * n) = i₁ (y * a) * i₂ b * n := by
      rw [map_mul]; group
    have hR : (i₁ a * i₂ b * n) * i₁ y = i₁ (a * deltaAut y) * i₂ b * n := by
      rw [show (i₁ a * i₂ b * n) * i₁ y = i₁ a * i₂ b * (n * i₁ y) by group, hn, map_mul]
      rw [show i₁ a * i₂ b * (i₁ (deltaAut y) * n) =
          i₁ a * i₁ (deltaAut y) * (i₂ b * n) by
        rw [show i₁ a * i₂ b * (i₁ (deltaAut y) * n) =
              i₁ a * (i₂ b * (i₁ (deltaAut y) * n)) by rw [mul_assoc],
          show i₁ a * (i₂ b * (i₁ (deltaAut y) * n)) =
              i₁ a * (i₁ (deltaAut y) * (i₂ b * n)) by
            rw [← mul_assoc (i₂ b), (hcomm (deltaAut y) b).eq.symm, mul_assoc],
          show i₁ a * (i₁ (deltaAut y) * (i₂ b * n)) =
              i₁ a * i₁ (deltaAut y) * (i₂ b * n) by rw [mul_assoc]]]
      group
    have hc : i₁ (y * a) * i₂ b = i₁ (a * deltaAut y) * i₂ b := by
      rw [hL, hR] at hx
      exact mul_right_cancel hx
    rcases (prod_eq_iff (x := y * a) (y := b) (x' := a * deltaAut y) (y' := b)).mp hc with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd h2 (ne_neg_self b)
  have hcenter_Q : Subgroup.center Q = (Subgroup.zpowers t).subgroupOf Q := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      obtain ⟨a, ha, b, hb, hab⟩ := decomp x.2
      have hxcent : ∀ y : Q, y * x = x * y := Subgroup.mem_center_iff.mp hx
      have h1 : i₁ hM * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₁ hM := by
        have hh : i₁ hM * x.1 = x.1 * i₁ hM := by
          simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₁ hM, hhM_Q⟩)
        rw [← hab] at hh
        exact hh
      have h2 : i₁ cM * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₁ cM := by
        have hh : i₁ cM * x.1 = x.1 * i₁ cM := by
          simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₁ cM, hcM_Q⟩)
        rw [← hab] at hh
        exact hh
      have h1b : i₂ hM * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₂ hM := by
        have hh : i₂ hM * x.1 = x.1 * i₂ hM := by
          simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₂ hM, hh2M_Q⟩)
        rw [← hab] at hh
        exact hh
      have h2b : i₂ cM * (i₁ a * i₂ b) = (i₁ a * i₂ b) * i₂ cM := by
        have hh : i₂ cM * x.1 = x.1 * i₂ cM := by
          simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₂ cM, hc2M_Q⟩)
        rw [← hab] at hh
        exact hh
      have ha_cen : a ∈ Subgroup.centralizer (Q8 : Set SL5) := by
        rw [hQ8_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro y hy
        rcases hy with rfl | rfl
        · exact (commute_a_of h1).symm.eq
        · exact (commute_a_of h2).symm.eq
      have hb_cen : b ∈ Subgroup.centralizer (Q8 : Set SL5) := by
        rw [hQ8_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
        intro y hy
        rcases hy with rfl | rfl
        · exact (commute_b_of h1b).symm.eq
        · exact (commute_b_of h2b).symm.eq
      have ha_zp : a ∈ zpowers (-1 : SL5) := by rw [← hcent_Q8]; exact ha_cen
      have hb_zp : b ∈ zpowers (-1 : SL5) := by rw [← hcent_Q8]; exact hb_cen
      rw [mem_zpowers_of_orderOf_eq_two ht, ← hab]
      rcases (mem_zpowers_of_orderOf_eq_two hneg_ord).mp ha_zp with rfl | rfl <;>
        rcases (mem_zpowers_of_orderOf_eq_two hneg_ord).mp hb_zp with rfl | rfl
      · left; rw [map_one, map_one, mul_one]
      · right; rw [map_one, one_mul, ← ht2]
      · right; rw [map_one, mul_one, ← ht1]
      · left; rw [← ht1, ← ht2, ← pow_two, ← ht]; exact pow_orderOf_eq_one t
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hx' : (x : G) ∈ zpowers t := Subgroup.mem_subgroupOf.mp hx
      rcases (mem_zpowers_of_orderOf_eq_two ht).mp hx' with hx1 | hx1
      · refine Subtype.ext ?_
        change (y : G) * (x : G) = (x : G) * (y : G)
        rw [hx1, mul_one, one_mul]
      · refine Subtype.ext ?_
        change (y : G) * (x : G) = (x : G) * (y : G)
        rw [hx1]
        exact Subgroup.mem_centralizer_singleton_iff.mp (hQ_le_C y.2)
  have hUprod : (U : Set G) = (Q : Set G) * (Subgroup.zpowers n : Set G) := by
    change (↑(Q ⊔ Subgroup.zpowers n) : Set G) = _
    exact coe_mul_of_right_le_normalizer_left Q (Subgroup.zpowers n) hzp_norm_Q
  have hcenter_U : Subgroup.center U = (Subgroup.zpowers t).subgroupOf U := by
    apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      have hxcent : ∀ y : U, y * x = x * y := Subgroup.mem_center_iff.mp hx
      have hxU : (x : G) ∈ (U : Set G) := x.2
      have hmem : (x : G) ∈ Q ∨ ∃ q ∈ Q, (x : G) = q * n := by
        rw [hUprod, Set.mem_mul] at hxU
        obtain ⟨q, hq, m, hm, hqm⟩ := hxU
        rcases (mem_zpowers_of_orderOf_eq_two hn_ord).mp hm with rfl | rfl
        · rw [mul_one] at hqm
          exact Or.inl (hqm ▸ hq)
        · exact Or.inr ⟨q, hq, hqm.symm⟩
      rcases hmem with hxQ | ⟨q, hq, hxqn⟩
      · have hxQcenter : (⟨x.1, hxQ⟩ : Q) ∈ Subgroup.center Q := by
          rw [Subgroup.mem_center_iff]
          intro y
          refine Subtype.ext ?_
          have hh : (y : G) * x.1 = x.1 * (y : G) := by
            simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨(y : G), by
              change (y : G) ∈ Q ⊔ Subgroup.zpowers n
              exact Subgroup.mem_sup_left y.2⟩)
          simpa only [Subgroup.coe_mul] using hh
        rw [hcenter_Q, Subgroup.mem_subgroupOf] at hxQcenter
        exact hxQcenter
      · exfalso
        obtain ⟨a, ha, b, hb, hab⟩ := decomp hq
        have h1 : i₁ hM * (i₁ a * i₂ b * n) = (i₁ a * i₂ b * n) * i₁ hM := by
          have hh : i₁ hM * x.1 = x.1 * i₁ hM := by
            simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₁ hM, hhM_U⟩)
          rw [hxqn, ← hab] at hh
          exact hh
        have h2 : i₁ cM * (i₁ a * i₂ b * n) = (i₁ a * i₂ b * n) * i₁ cM := by
          have hh : i₁ cM * x.1 = x.1 * i₁ cM := by
            simpa only [Subgroup.coe_mul] using congrArg Subtype.val (hxcent ⟨i₁ cM, hcM_U⟩)
          rw [hxqn, ← hab] at hh
          exact hh
        exact (not_conj_deltaAut_fix_hM_cM a) ⟨extract h1, extract h2⟩
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have hx' : (x : G) ∈ zpowers t := Subgroup.mem_subgroupOf.mp hx
      rcases (mem_zpowers_of_orderOf_eq_two ht).mp hx' with hx1 | hx1
      · refine Subtype.ext ?_
        change (y : G) * (x : G) = (x : G) * (y : G)
        rw [hx1, mul_one, one_mul]
      · refine Subtype.ext ?_
        change (y : G) * (x : G) = (x : G) * (y : G)
        rw [hx1]
        exact Subgroup.mem_centralizer_singleton_iff.mp (hU_le_C y.2)
  have hUcard : Nat.card U = 64 := by
    have hcf := card_formula (H := Subgroup.zpowers n) (K := Q) hzp_norm_Q
    have hinf_bot : (Subgroup.zpowers n ⊓ Q : Subgroup G) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Subgroup.mem_inf] at hx
      rcases (mem_zpowers_of_orderOf_eq_two hn_ord).mp hx.1 with rfl | rfl
      · exact Subgroup.mem_bot.mpr rfl
      · exact absurd hx.2 hn_not_Q
    change Nat.card ↥(Q ⊔ Subgroup.zpowers n) = 64
    rw [show Subgroup.zpowers n ⊔ Q = Q ⊔ Subgroup.zpowers n from sup_comm .., hinf_bot,
      Subgroup.card_bot, Nat.card_zpowers, hn_ord, hQcard] at hcf
    norm_num at hcf
    omega
  have htQ : t ∈ Q := by
    rw [ht1]
    change i₁ (-1) ∈ Q8.map i₁ ⊔ Q8.map i₂
    exact Subgroup.mem_sup_left ⟨-1, (mem_Q8 (-1)).mpr (Or.inr (Or.inl rfl)), rfl⟩
  have htU : t ∈ U := by
    change t ∈ Q ⊔ Subgroup.zpowers n
    exact Subgroup.mem_sup_left htQ
  have two_pow : 2 ^ (14400 : ℕ).factorization 2 = 64 := by
    rw [Nat.factorization_def 14400 Nat.prime_two]
    have h1 : (14400 : ℕ) = 2 ^ 6 * 225 := by norm_num
    rw [h1, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num : ¬ (2 : ℕ) ∣ 225)]
    norm_num
  have hU_syl : IsSylowOf 2 U (Subgroup.centralizer ({t} : Set G)) := by
    refine isSylowOf_of_card hU_le_C ?_
    rw [hUcard, h.card_centralizer, two_pow]
  have hchar : ((Subgroup.zpowers t).subgroupOf U).Characteristic := by
    rw [← hcenter_U]
    exact Subgroup.centerCharacteristic
  have hN : Subgroup.normalizer (U : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
    normalizer_le_centralizer_of_characteristic ht htU hchar
  have htop : IsSylowOf 2 U ⊤ := (h.isSylowOf_top_of_normalizer_le hU_syl hN).1
  have hcardG : Nat.card U = 2 ^ (Nat.card G).factorization 2 := by
    rw [← Subgroup.card_top (G := G)]
    exact IsSylowOf.card_eq htop
  exact ⟨Sylow.ofCard U hcardG, by rw [Sylow.coe_ofCard]; exact hU_le_C⟩

end CFSG.OddTranspositions.PartThree.Wong
