module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34SecFix

public section

namespace CFSG.Quasithin.H13.SecFix

@[expose] def hom33 {M : Type*} [Group M] (a b : M) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) : Multiplicative (ZMod 3 × ZMod 3) →* M where
  toFun x := a ^ (Multiplicative.toAdd x).1.val * b ^ (Multiplicative.toAdd x).2.val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, ZMod.val_add]
    rw [← pow_eq_pow_mod _ ha, ← pow_eq_pow_mod _ hb, pow_add, pow_add]
    have h1 : Commute (a ^ (Multiplicative.toAdd y).1.val) (b ^ (Multiplicative.toAdd x).2.val) :=
      (hab.pow_left _).pow_right _
    calc a ^ (Multiplicative.toAdd x).1.val * a ^ (Multiplicative.toAdd y).1.val *
          (b ^ (Multiplicative.toAdd x).2.val * b ^ (Multiplicative.toAdd y).2.val)
        = a ^ (Multiplicative.toAdd x).1.val * (a ^ (Multiplicative.toAdd y).1.val *
          b ^ (Multiplicative.toAdd x).2.val) * b ^ (Multiplicative.toAdd y).2.val := by group
      _ = a ^ (Multiplicative.toAdd x).1.val * (b ^ (Multiplicative.toAdd x).2.val *
          a ^ (Multiplicative.toAdd y).1.val) * b ^ (Multiplicative.toAdd y).2.val := by
        rw [h1.eq]
      _ = _ := by group

theorem hom33_apply {M : Type*} [Group M] (a b : M) (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : Commute a b) (i j : ZMod 3) :
    hom33 a b ha hb hab (Multiplicative.ofAdd (i, j)) = a ^ i.val * b ^ j.val := rfl

theorem nine_dvd_card_add {X : Type*} [Finite X]
    (ρ : Multiplicative (ZMod 3 × ZMod 3) →* Equiv.Perm X) (c : ℕ)
    (hc : ∀ g, g ≠ 1 → Nat.card {x // ρ g x = x} = c) : 9 ∣ Nat.card X + 8 * c := by
  classical
  have := Fintype.ofFinite X
  let _ : MulAction (Multiplicative (ZMod 3 × ZMod 3)) X := MulAction.compHom X ρ
  have hb := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (Multiplicative (ZMod 3 × ZMod 3)) X
  have hfix : ∀ g : Multiplicative (ZMod 3 × ZMod 3),
      Fintype.card (MulAction.fixedBy X g) = Nat.card {x // ρ g x = x} := by
    intro g
    rw [← Nat.card_eq_fintype_card]
    rfl
  have hsum : (∑ g : Multiplicative (ZMod 3 × ZMod 3), Fintype.card (MulAction.fixedBy X g)) =
      Nat.card X + 8 * c := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
    have h1 : Fintype.card (MulAction.fixedBy X (1 : Multiplicative (ZMod 3 × ZMod 3))) =
        Nat.card X := by
      rw [hfix, map_one]
      simp only [Equiv.Perm.coe_one, id_eq]
      exact Nat.card_congr (Equiv.subtypeUnivEquiv fun _ => trivial)
    have h2 : ∑ g ∈ Finset.univ.erase (1 : Multiplicative (ZMod 3 × ZMod 3)),
        Fintype.card (MulAction.fixedBy X g) = ∑ _g ∈ Finset.univ.erase
          (1 : Multiplicative (ZMod 3 × ZMod 3)), c := by
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [hfix]
      exact hc g (Finset.ne_of_mem_erase hg)
    rw [h1, h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, smul_eq_mul]
    congr 1
  rw [← hsum, hb]
  exact Dvd.intro_left _ (by rw [Fintype.card_multiplicative]; rfl)

variable {G : Type*} [Group G]

@[expose] def conjOn (A : Subgroup G) {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    ↥A → ↥A := fun a => ⟨g * a * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg a).mp a.2⟩

@[expose] def secMap (A B : Subgroup G) {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) : (↥A ⧸ B.subgroupOf A) → (↥A ⧸ B.subgroupOf A) :=
  Quotient.map' (conjOn A hgA) fun a a' h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
    have := (Subgroup.mem_normalizer_iff.mp hgB _).mp h
    simpa [conjOn, mul_assoc] using this

theorem secMap_mk (A B : Subgroup G) {g : G} (hgA : g ∈ Subgroup.normalizer (A : Set G))
    (hgB : g ∈ Subgroup.normalizer (B : Set G)) (a : ↥A) :
    secMap A B hgA hgB (QuotientGroup.mk a) = QuotientGroup.mk (conjOn A hgA a) := rfl

@[expose] def secPermHom (A B K : Subgroup G) (hKA : K ≤ Subgroup.normalizer (A : Set G))
    (hKB : K ≤ Subgroup.normalizer (B : Set G)) : ↥K →* Equiv.Perm (↥A ⧸ B.subgroupOf A) where
  toFun g :=
    { toFun := secMap A B (hKA g.2) (hKB g.2)
      invFun := secMap A B (hKA (K.inv_mem g.2)) (hKB (K.inv_mem g.2))
      left_inv := fun x => by
        induction x using QuotientGroup.induction_on with
        | H a =>
          rw [secMap_mk, secMap_mk]
          congr 1
          apply Subtype.ext
          simp [conjOn, mul_assoc]
      right_inv := fun x => by
        induction x using QuotientGroup.induction_on with
        | H a =>
          rw [secMap_mk, secMap_mk]
          congr 1
          apply Subtype.ext
          simp [conjOn, mul_assoc] }
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a =>
      show QuotientGroup.mk (conjOn A (hKA (1 : ↥K).2) a) = QuotientGroup.mk a
      congr 1
      apply Subtype.ext
      simp [conjOn]
  map_mul' g h := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H a =>
      show QuotientGroup.mk (conjOn A (hKA (g * h).2) a) =
        QuotientGroup.mk (conjOn A (hKA g.2) (conjOn A (hKA h.2) a))
      congr 1
      apply Subtype.ext
      simp [conjOn, mul_assoc]

theorem ElemSec.secPermHom_eq_one {A B K : Subgroup G} (h : ElemSec A B)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    {g : ↥K} (hg : ∀ x ∈ A, (g : G) * x * (g : G)⁻¹ * x⁻¹ ∈ B) :
    secPermHom A B K hKA hKB g = 1 := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H a =>
    show QuotientGroup.mk (conjOn A (hKA g.2) a) = QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := (Subgroup.mem_normalizer_iff.mp (h.normalizes (A.inv_mem a.2)) _).mp
      (B.inv_mem (hg a a.2))
    have e : (((conjOn A (hKA g.2) a)⁻¹ * a : ↥A) : G) =
        (a : G)⁻¹ * ((g : G) * a * (g : G)⁻¹ * (a : G)⁻¹)⁻¹ * (a : G)⁻¹⁻¹ := by
      simp only [conjOn, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact h1

theorem ElemSec.card_fixMod_eq [Finite G] {A B K : Subgroup G} (h : ElemSec A B)
    (hKA : K ≤ Subgroup.normalizer (A : Set G)) (hKB : K ≤ Subgroup.normalizer (B : Set G))
    (g : ↥K) :
    Nat.card (fixMod (g : G) A B) =
      Nat.card B * Nat.card {x // secPermHom A B K hKA hKB g x = x} := by
  set t : Set (↥A ⧸ B.subgroupOf A) := {x | secPermHom A B K hKA hKB g x = x} with ht
  have hpre := QuotientGroup.card_preimage_mk (B.subgroupOf A) t
  have hB : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hmem : ∀ a : ↥A, (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) ∈ t ↔
      (a : G) ∈ fixMod (g : G) A B := by
    intro a
    rw [h.mem_fixMod_iff le_rfl h.le le_rfl]
    have hc : (QuotientGroup.mk a : ↥A ⧸ B.subgroupOf A) ∈ t ↔
        ((g : G) * a * (g : G)⁻¹)⁻¹ * a ∈ B := by
      show QuotientGroup.mk (conjOn A (hKA g.2) a) = QuotientGroup.mk a ↔ _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      rfl
    rw [hc]
    have haN : (a : G) ∈ Subgroup.normalizer (B : Set G) := h.normalizes a.2
    constructor
    · intro hw
      refine ⟨a.2, ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp haN _).mp (B.inv_mem hw)
      rwa [show (a : G) * (((g : G) * a * (g : G)⁻¹)⁻¹ * a)⁻¹ * (a : G)⁻¹ =
        (g : G) * a * (g : G)⁻¹ * (a : G)⁻¹ by group] at h1
    · rintro ⟨-, hw⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp hw
      have h2 := B.inv_mem h1
      rwa [show ((a : G)⁻¹ * ((g : G) * a * (g : G)⁻¹ * (a : G)⁻¹) * (a : G)⁻¹⁻¹)⁻¹ =
        ((g : G) * a * (g : G)⁻¹)⁻¹ * a by group] at h2
  have hpre := QuotientGroup.card_preimage_mk (B.subgroupOf A) t
  have hB : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have hF : Nat.card (QuotientGroup.mk ⁻¹' t : Set ↥A) = Nat.card (fixMod (g : G) A B) := by
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1, (hmem a.1).mp a.2⟩
        invFun := fun x => ⟨⟨x.1, fixMod_le _ _ _ x.2⟩, (hmem _).mpr x.2⟩
        left_inv := fun a => rfl
        right_inv := fun x => rfl }
  rw [← hF, hpre, hB]
  rfl

end CFSG.Quasithin.H13.SecFix
