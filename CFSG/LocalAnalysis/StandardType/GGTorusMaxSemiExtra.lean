module

public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Equiv.Basic

public section

namespace CFSG.StandardType.FrameRoute

open scoped commutatorElement

private lemma card_hom_le_card {A Z : Type} [Group A] [Finite A] [Group Z] [Finite Z]
    (hZ : Nat.card Z = 3) (h3 : ∀ a : A, a ^ 3 = 1) :
    Nat.card (A →* Z) ≤ Nat.card A := by
  classical
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic Z := isCyclic_of_prime_card hZ
  let eZ : Z ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq hZ (by simp)
  have h3ab : ∀ a : Abelianization A, a ^ 3 = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro a
    change (Abelianization.of a) ^ 3 = 1
    rw [← map_pow, h3 a, map_one]
  let : Finite (Abelianization A) :=
    Finite.of_surjective (Abelianization.of (G := A)) (QuotientGroup.mk_surjective)
  let : Finite (Additive (Abelianization A)) := inferInstance
  let : Module (ZMod 3) (Additive (Abelianization A)) :=
    AddCommGroup.zmodModule (fun x => by
      show (3 : ℕ) • x = 0
      rw [← ofMul_toMul x, ← ofMul_pow, h3ab (Additive.toMul x), ofMul_one])
  let : Module.Finite (ZMod 3) (Additive (Abelianization A)) := Module.Finite.of_finite
  have hdual : Nat.card (Module.Dual (ZMod 3) (Additive (Abelianization A))) =
      Nat.card (Additive (Abelianization A)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 3)]
    rw [show Module.finrank (ZMod 3) (Module.Dual (ZMod 3) (Additive (Abelianization A))) =
        Module.finrank (ZMod 3) (Additive (Abelianization A)) from Subspace.dual_finrank_eq]
    rw [← Module.natCard_eq_pow_finrank (K := ZMod 3) (V := Additive (Abelianization A))]
  have h1 : Nat.card (A →* Z) = Nat.card (Abelianization A →* Z) :=
    Nat.card_congr (Abelianization.lift (A := Z))
  let eHom : (Abelianization A →* Z) ≃ (Abelianization A →* Multiplicative (ZMod 3)) :=
    { toFun := fun f => eZ.toMonoidHom.comp f
      invFun := fun f => eZ.symm.toMonoidHom.comp f
      left_inv := fun f => by ext x; simp
      right_inv := fun f => by ext x; simp }
  have h2 : Nat.card (Abelianization A →* Z) =
      Nat.card (Abelianization A →* Multiplicative (ZMod 3)) :=
    Nat.card_congr eHom
  have h3a : Nat.card (Abelianization A →* Multiplicative (ZMod 3)) =
      Nat.card (Additive (Abelianization A) →+ ZMod 3) :=
    Nat.card_congr (MonoidHom.toAdditiveLeft (α := Abelianization A) (β := ZMod 3))
  have h3b : Nat.card (Additive (Abelianization A) →+ ZMod 3) =
      Nat.card (Module.Dual (ZMod 3) (Additive (Abelianization A))) :=
    Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 3).toEquiv
  calc Nat.card (A →* Z)
      = Nat.card (Abelianization A) := by
        rw [h1, h2, h3a, h3b, hdual]
        exact Nat.card_congr (Additive.toMul (α := Abelianization A))
    _ ≤ Nat.card A := by
        exact Nat.card_le_card_of_surjective (Abelianization.of (G := A)) (QuotientGroup.mk_surjective)

private lemma commutator_mul_left {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) (a b c : P) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul]
  have hb : ⁅b, c⁆ ∈ Z := hcomm b c
  have hconj : a * ⁅b, c⁆ * a⁻¹ = ⁅b, c⁆ := by
    rw [← hZc ⁅b, c⁆ hb a, mul_assoc, mul_inv_cancel, mul_one]
  rw [hconj]
  exact (hZc ⁅a, c⁆ (hcomm a c) ⁅b, c⁆).symm

private lemma commutator_mul_right {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) (a b c : P) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  have hc : ⁅a, c⁆ ∈ Z := hcomm a c
  have hconj : b * ⁅a, c⁆ * b⁻¹ = ⁅a, c⁆ := by
    rw [← hZc ⁅a, c⁆ hc b, mul_assoc, mul_inv_cancel, mul_one]
  calc ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ = ⁅a, b⁆ * (b * ⁅a, c⁆ * b⁻¹) := by
        rw [mul_assoc ⁅a, b⁆ b ⁅a, c⁆, mul_assoc ⁅a, b⁆ (b * ⁅a, c⁆) b⁻¹]
    _ = ⁅a, b⁆ * ⁅a, c⁆ := by rw [hconj]

private lemma commutator_inv_left {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) (a c : P) :
    ⁅a⁻¹, c⁆ = ⁅a, c⁆⁻¹ := by
  rw [commutatorElement_inv_left]
  have hz : ⁅c, a⁆ ∈ Z := hcomm c a
  have hconj : a⁻¹ * ⁅c, a⁆ * a = ⁅c, a⁆ := by
    rw [← hZc ⁅c, a⁆ hz a⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [hconj, commutatorElement_inv]

private lemma commutator_inv_right {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) (a b : P) :
    ⁅a, b⁻¹⁆ = ⁅a, b⁆⁻¹ := by
  rw [commutatorElement_inv_right]
  have hz : ⁅b, a⁆ ∈ Z := hcomm b a
  have hconj : b⁻¹ * ⁅b, a⁆ * b = ⁅b, a⁆ := by
    rw [← hZc ⁅b, a⁆ hz b⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  rw [hconj, commutatorElement_inv]

private lemma commutator_div_eq_one_of_eq_left {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) {a b c : P}
    (h : ⁅a, c⁆ = ⁅b, c⁆) : ⁅a / b, c⁆ = 1 := by
  rw [div_eq_mul_inv, commutator_mul_left Z hZc hcomm a b⁻¹ c,
    commutator_inv_left Z hZc hcomm b c, h, mul_inv_cancel]

private lemma commutator_div_eq_one_of_eq_right {P : Type} [Group P] (Z : Subgroup P)
    (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) {a c d : P}
    (h : ⁅a, c⁆ = ⁅a, d⁆) : ⁅a, c / d⁆ = 1 := by
  rw [div_eq_mul_inv, commutator_mul_right Z hZc hcomm a c d⁻¹,
    commutator_inv_right Z hZc hcomm a d, h, mul_inv_cancel]

theorem tmExtra_card_maxAbelian {P : Type} [Group P] [Finite P] (Z : Subgroup P)
    (hZ : Nat.card Z = 3) (hZc : ∀ z ∈ Z, ∀ a : P, z * a = a * z)
    (hcen : ∀ a : P, (∀ b : P, a * b = b * a) → a ∈ Z)
    (hcomm : ∀ a b : P, a * b * a⁻¹ * b⁻¹ ∈ Z) (hexp : ∀ a : P, a ^ 3 ∈ Z)
    (C : Subgroup P) (hCab : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a)
    (hCmax : ∀ a : P, (∀ c ∈ C, a * c = c * a) → a ∈ C) :
    Nat.card C ^ 2 = 3 * Nat.card P := by
  classical
  have hZC : Z ≤ C := by
    intro z hz
    exact hCmax z (fun c _ => hZc z hz c)
  have hZnormal : Z.Normal := by
    refine ⟨fun z hz g => ?_⟩
    have hg : g * z * g⁻¹ = z := by
      rw [← hZc z hz g, mul_assoc, mul_inv_cancel, mul_one]
    simpa [hg] using hz
  have hCnormal : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    have hcz : ⁅c⁻¹, g⁆ ∈ Z := hcomm c⁻¹ g
    have hmem : c * ⁅c⁻¹, g⁆ ∈ C := C.mul_mem hc (hZC hcz)
    convert hmem using 1
    rw [commutatorElement_def]
    group
  let : Z.Normal := hZnormal
  let : C.Normal := hCnormal
  let Zc : Subgroup C := Z.subgroupOf C
  let : Zc.Normal := hZnormal.subgroupOf C
  have hZc_card : Nat.card Zc = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv, hZ]
  have h3PC : ∀ a : P ⧸ C, a ^ 3 = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hZC (hexp a)
  have h3CZ : ∀ a : C ⧸ Zc, a ^ 3 = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have h : (a : P) ^ 3 ∈ Z := hexp (a : P)
    simpa [Zc, Subgroup.mem_subgroupOf] using h
  let f : P → C →* Z := fun a =>
    { toFun := fun c => ⟨⁅a, (c : P)⁆, hcomm a (c : P)⟩
      map_one' := by
        ext
        simp [commutatorElement_def]
      map_mul' := by
        intro c d
        ext
        exact commutator_mul_right Z hZc hcomm a (c : P) (d : P) }
  have hfZ : ∀ a : P, Zc ≤ (f a).ker := by
    intro a c hc
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ⁅a, (c : P)⁆ = 1
    have hcZ : (c : P) ∈ Z := hc
    have hcent : a * (c : P) = (c : P) * a := (hZc (c : P) hcZ a).symm
    rw [commutatorElement_def, hcent, mul_assoc (c : P) a a⁻¹, mul_inv_cancel, mul_one,
      mul_inv_cancel]
  let g : P → C ⧸ Zc →* Z := fun a => QuotientGroup.lift Zc (f a) (hfZ a)
  let secP : P ⧸ C → P := Function.surjInv (QuotientGroup.mk_surjective (s := C))
  have hsecP : ∀ x : P ⧸ C, (QuotientGroup.mk (secP x) : P ⧸ C) = x := fun x =>
    Function.surjInv_eq (QuotientGroup.mk_surjective (s := C)) x
  let : Finite (C ⧸ Zc →* Z) :=
    Finite.of_injective (fun f : C ⧸ Zc →* Z => (f : C ⧸ Zc → Z))
      (fun f g h => MonoidHom.ext (congrFun h))
  let F : P ⧸ C → (C ⧸ Zc →* Z) := fun x =>
    QuotientGroup.lift Zc (f (secP x)) (hfZ (secP x))
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hxy' : QuotientGroup.lift Zc (f (secP x)) (hfZ (secP x)) =
        QuotientGroup.lift Zc (f (secP y)) (hfZ (secP y)) := hxy
    rw [← hsecP x, ← hsecP y, QuotientGroup.eq_iff_div_mem]
    apply hCmax
    intro c hc
    have hval : f (secP x) ⟨c, hc⟩ = f (secP y) ⟨c, hc⟩ := by
      have := congrArg (fun h : C ⧸ Zc →* Z => h (QuotientGroup.mk ⟨c, hc⟩)) hxy'
      simpa using this
    have hcomm_eq : ⁅secP x, c⁆ = ⁅secP y, c⁆ := by
      have := congrArg Subtype.val hval
      simpa [f] using this
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (commutator_div_eq_one_of_eq_left Z hZc hcomm hcomm_eq)
  have hcard1 : Nat.card (P ⧸ C) ≤ Nat.card (C ⧸ Zc) := by
    calc Nat.card (P ⧸ C) ≤ Nat.card (C ⧸ Zc →* Z) :=
          Nat.card_le_card_of_injective F hFinj
      _ ≤ Nat.card (C ⧸ Zc) := card_hom_le_card hZ h3CZ
  let k : C → P →* Z := fun c =>
    { toFun := fun a => ⟨⁅a, (c : P)⁆, hcomm a (c : P)⟩
      map_one' := by
        ext
        simp [commutatorElement_def]
      map_mul' := by
        intro a b
        ext
        exact commutator_mul_left Z hZc hcomm a b (c : P) }
  have hkC : ∀ c : C, C ≤ (k c).ker := by
    intro c a ha
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    change ⁅a, (c : P)⁆ = 1
    exact commutatorElement_eq_one_iff_mul_comm.mpr (hCab a ha c c.property)
  let h : C → P ⧸ C →* Z := fun c => QuotientGroup.lift C (k c) (hkC c)
  let secCZ : C ⧸ Zc → C := Function.surjInv (QuotientGroup.mk_surjective (s := Zc))
  have hsecCZ : ∀ x : C ⧸ Zc, (QuotientGroup.mk (secCZ x) : C ⧸ Zc) = x := fun x =>
    Function.surjInv_eq (QuotientGroup.mk_surjective (s := Zc)) x
  let : Finite (P ⧸ C →* Z) :=
    Finite.of_injective (fun f : P ⧸ C →* Z => (f : P ⧸ C → Z))
      (fun f g h => MonoidHom.ext (congrFun h))
  let G : C ⧸ Zc → (P ⧸ C →* Z) := fun x =>
    QuotientGroup.lift C (k (secCZ x)) (hkC (secCZ x))
  have hGinj : Function.Injective G := by
    intro x y hxy
    have hxy' : QuotientGroup.lift C (k (secCZ x)) (hkC (secCZ x)) =
        QuotientGroup.lift C (k (secCZ y)) (hkC (secCZ y)) := hxy
    rw [← hsecCZ x, ← hsecCZ y, QuotientGroup.eq_iff_div_mem]
    change ((secCZ x / secCZ y : C) : P) ∈ Z
    apply hcen
    intro a
    have hval : k (secCZ x) a = k (secCZ y) a := by
      have := congrArg (fun h : P ⧸ C →* Z => h (QuotientGroup.mk a)) hxy'
      simpa using this
    have hcomm_eq : ⁅a, (secCZ x : P)⁆ = ⁅a, (secCZ y : P)⁆ := by
      have := congrArg Subtype.val hval
      simpa [k] using this
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (commutator_div_eq_one_of_eq_right Z hZc hcomm hcomm_eq)).symm
  have hcard2 : Nat.card (C ⧸ Zc) ≤ Nat.card (P ⧸ C) := by
    calc Nat.card (C ⧸ Zc) ≤ Nat.card (P ⧸ C →* Z) :=
          Nat.card_le_card_of_injective G hGinj
      _ ≤ Nat.card (P ⧸ C) := card_hom_le_card hZ h3PC
  have hcard_eq : Nat.card (P ⧸ C) = Nat.card (C ⧸ Zc) :=
    Nat.le_antisymm hcard1 hcard2
  have hcardC : Nat.card C = Nat.card (C ⧸ Zc) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Zc, hZc_card]
  have hcardP : Nat.card P = Nat.card (C ⧸ Zc) * (Nat.card (C ⧸ Zc) * 3) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup C, hcard_eq, hcardC]
  rw [hcardC, hcardP]
  ring

end CFSG.StandardType.FrameRoute

end
