module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.IsPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality

public section

namespace CFSG.Quasithin

namespace SL2Sylow

open scoped MatrixGroups
open Matrix Matrix.SpecialLinearGroup

variable {F : Type*} [Field F]

def upperElt (t : F) : SL(2, F) := transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t

def lowerElt (t : F) : SL(2, F) := transvection (one_ne_zero : (1 : Fin 2) ≠ 0) t

theorem entries_det (g : SL(2, F)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem ext_entries {g h : SL(2, F)} (h00 : g 0 0 = h 0 0) (h01 : g 0 1 = h 0 1)
    (h10 : g 1 0 = h 1 0) (h11 : g 1 1 = h 1 1) : g = h := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[simp] theorem upperElt_00 (t : F) : upperElt t 0 0 = 1 := by simp [upperElt, transvection_coe]

@[simp] theorem upperElt_01 (t : F) : upperElt t 0 1 = t := by simp [upperElt, transvection_coe]

@[simp] theorem upperElt_10 (t : F) : upperElt t 1 0 = 0 := by simp [upperElt, transvection_coe]

@[simp] theorem upperElt_11 (t : F) : upperElt t 1 1 = 1 := by simp [upperElt, transvection_coe]

@[simp] theorem lowerElt_00 (t : F) : lowerElt t 0 0 = 1 := by simp [lowerElt, transvection_coe]

@[simp] theorem lowerElt_01 (t : F) : lowerElt t 0 1 = 0 := by simp [lowerElt, transvection_coe]

@[simp] theorem lowerElt_10 (t : F) : lowerElt t 1 0 = t := by simp [lowerElt, transvection_coe]

@[simp] theorem lowerElt_11 (t : F) : lowerElt t 1 1 = 1 := by simp [lowerElt, transvection_coe]

theorem mul_00 (g h : SL(2, F)) : (g * h) 0 0 = g 0 0 * h 0 0 + g 0 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_01 (g h : SL(2, F)) : (g * h) 0 1 = g 0 0 * h 0 1 + g 0 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_10 (g h : SL(2, F)) : (g * h) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_11 (g h : SL(2, F)) : (g * h) 1 1 = g 1 0 * h 0 1 + g 1 1 * h 1 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem inv_00 (g : SL(2, F)) : (g⁻¹) 0 0 = g 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_01 (g : SL(2, F)) : (g⁻¹) 0 1 = -g 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_10 (g : SL(2, F)) : (g⁻¹) 1 0 = -g 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem inv_11 (g : SL(2, F)) : (g⁻¹) 1 1 = g 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem upperElt_mul_upperElt (s t : F) : upperElt s * upperElt t = upperElt (s + t) := by
  apply ext_entries <;> simp [mul_00, mul_01, mul_10, mul_11, add_comm]

theorem upperElt_zero : upperElt (0 : F) = 1 := by
  apply ext_entries <;> simp

theorem upperElt_inv (t : F) : (upperElt t)⁻¹ = upperElt (-t) := by
  rw [inv_eq_iff_mul_eq_one, upperElt_mul_upperElt, add_neg_cancel, upperElt_zero]

theorem upperElt_injective : Function.Injective (upperElt : F → SL(2, F)) := by
  intro s t h
  simpa using congrArg (fun g : SL(2, F) => g 0 1) h

theorem conj_upperElt_10 (g : SL(2, F)) (t : F) :
    (g * upperElt t * g⁻¹) 1 0 = -(t * g 1 0 ^ 2) := by
  have hd := entries_det g
  simp only [mul_10, mul_11, inv_00, inv_10, upperElt_00, upperElt_01, upperElt_10, upperElt_11]
  ring

theorem conj_upperElt_of_lower_left_eq_zero (g : SL(2, F)) (hc : g 1 0 = 0) (t : F) :
    g * upperElt t * g⁻¹ = upperElt (t * g 0 0 ^ 2) := by
  have hd := entries_det g
  rw [hc] at hd
  apply ext_entries <;>
  simp only [mul_00, mul_01, mul_10, mul_11, inv_00, inv_01, inv_10, inv_11, upperElt_00,
    upperElt_01, upperElt_10, upperElt_11, hc]
  · linear_combination hd
  · ring
  · ring
  · linear_combination hd

theorem conj_upperElt_conj_eq_lowerElt (g : SL(2, F)) (hc : g 1 0 ≠ 0) (t : F) :
    upperElt (-(g 0 0 / g 1 0)) * (g * upperElt t * g⁻¹) * upperElt (g 0 0 / g 1 0) =
      lowerElt (-(t * g 1 0 ^ 2)) := by
  have hd := entries_det g
  apply ext_entries <;>
  simp only [mul_00, mul_01, mul_10, mul_11, inv_00, inv_01, inv_10, inv_11, upperElt_00,
    upperElt_01, upperElt_10, upperElt_11, lowerElt_00, lowerElt_01, lowerElt_10, lowerElt_11] <;>
  field_simp
  · linear_combination g 1 0 * hd
  · ring
  · ring
  · linear_combination g 1 0 * hd

def stdSylow (F : Type*) [Field F] : Subgroup SL(2, F) where
  carrier := Set.range upperElt
  one_mem' := ⟨0, upperElt_zero⟩
  mul_mem' := by
    rintro _ _ ⟨s, rfl⟩ ⟨t, rfl⟩
    exact ⟨s + t, upperElt_mul_upperElt s t ▸ rfl⟩
  inv_mem' := by
    rintro _ ⟨s, rfl⟩
    exact ⟨-s, (upperElt_inv s).symm⟩

theorem mem_stdSylow {g : SL(2, F)} : g ∈ stdSylow F ↔ ∃ t, upperElt t = g := Iff.rfl

theorem upperElt_mem_stdSylow (t : F) : upperElt t ∈ stdSylow F := ⟨t, rfl⟩

def borel (F : Type*) [Field F] : Subgroup SL(2, F) where
  carrier := {g | g 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change (g * h) 1 0 = 0
    rw [mul_10, show g 1 0 = 0 from hg, show h 1 0 = 0 from hh]
    ring
  inv_mem' := by
    intro g hg
    change (g⁻¹) 1 0 = 0
    rw [inv_10, show g 1 0 = 0 from hg, neg_zero]

theorem mem_borel {g : SL(2, F)} : g ∈ borel F ↔ g 1 0 = 0 := Iff.rfl

theorem stdSylow_le_borel : stdSylow F ≤ borel F := by
  rintro _ ⟨t, rfl⟩
  simp [mem_borel]

theorem borel_le_normalizer_stdSylow :
    borel F ≤ Subgroup.normalizer (stdSylow F : Set SL(2, F)) := by
  intro g hg
  have key : ∀ g ∈ borel F, ∀ n ∈ stdSylow F, g * n * g⁻¹ ∈ stdSylow F := by
    rintro g hg _ ⟨t, rfl⟩
    rw [conj_upperElt_of_lower_left_eq_zero g hg t]
    exact upperElt_mem_stdSylow _
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨key g hg h, fun hh => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hh
  simpa [mul_assoc] using this

theorem normalizer_stdSylow_le_borel :
    Subgroup.normalizer (stdSylow F : Set SL(2, F)) ≤ borel F := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg
  obtain ⟨s, hs⟩ := (hg (upperElt 1)).1 (upperElt_mem_stdSylow 1)
  have h := conj_upperElt_10 g 1
  rw [← hs] at h
  simp only [upperElt_10, one_mul] at h
  exact (pow_eq_zero_iff two_ne_zero).1 (neg_eq_zero.1 h.symm)

theorem normalizer_stdSylow :
    Subgroup.normalizer (stdSylow F : Set SL(2, F)) = borel F :=
  le_antisymm normalizer_stdSylow_le_borel borel_le_normalizer_stdSylow

theorem borel_det {b : SL(2, F)} (hb : b ∈ borel F) : b 0 0 * b 1 1 = 1 := by
  have h := entries_det b
  rw [show b 1 0 = 0 from hb] at h
  linear_combination h

def diagHom (F : Type*) [Field F] : borel F →* Fˣ where
  toFun b := ⟨b.1 0 0, b.1 1 1, borel_det b.2, by rw [mul_comm]; exact borel_det b.2⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' b b' := by
    apply Units.ext
    have h : b'.1 1 0 = 0 := b'.2
    simp [mul_00, h]

theorem stdSylow_mul_comm (a b : stdSylow F) : a * b = b * a := by
  obtain ⟨a, s, rfl⟩ := a
  obtain ⟨b, t, rfl⟩ := b
  apply Subtype.ext
  simp [upperElt_mul_upperElt, add_comm]

instance isSolvable_stdSylow : Group.IsSolvable (stdSylow F) :=
  Group.isSolvable_of_comm stdSylow_mul_comm

instance isSolvable_borel : Group.IsSolvable (borel F) := by
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (stdSylow_le_borel (F := F)))
    (diagHom F) ?_
  intro b hb
  have h00 : b.1 0 0 = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.1 hb)
    simpa [diagHom] using this
  have h11 : b.1 1 1 = 1 := by
    have := borel_det b.2
    rwa [h00, one_mul] at this
  refine ⟨⟨upperElt (b.1 0 1), upperElt_mem_stdSylow _⟩, ?_⟩
  apply Subtype.ext
  show upperElt (b.1 0 1) = b.1
  apply ext_entries <;> simp [h00, h11, show b.1 1 0 = 0 from b.2]

def diagElt (x : Fˣ) : SL(2, F) :=
  ⟨!![(x : F), 0; 0, ((x⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

@[simp] theorem diagElt_00 (x : Fˣ) : diagElt x 0 0 = (x : F) := by simp [diagElt]

@[simp] theorem diagElt_01 (x : Fˣ) : diagElt x 0 1 = 0 := by simp [diagElt]

@[simp] theorem diagElt_10 (x : Fˣ) : diagElt x 1 0 = 0 := by simp [diagElt]

@[simp] theorem diagElt_11 (x : Fˣ) : diagElt x 1 1 = ((x⁻¹ : Fˣ) : F) := by simp [diagElt]

def torusHom (F : Type*) [Field F] : Fˣ →* SL(2, F) where
  toFun := diagElt
  map_one' := by apply ext_entries <;> simp
  map_mul' x y := by
    apply ext_entries <;> simp [mul_00, mul_01, mul_10, mul_11, mul_comm]

theorem torusHom_injective : Function.Injective (torusHom F) := by
  intro x y h
  apply Units.ext
  simpa [torusHom] using congrArg (fun g : SL(2, F) => g 0 0) h

theorem torusHom_mem_borel (x : Fˣ) : torusHom F x ∈ borel F := by
  simp [mem_borel, torusHom]

theorem eq_top_of_unitriangular_mem {A : Subgroup SL(2, F)} (hu : ∀ t, upperElt t ∈ A)
    (hl : ∀ t, lowerElt t ∈ A) : A = ⊤ := by
  rw [eq_top_iff]
  intro g _
  refine SL2.transvection_induction (fun x => x ∈ A) ?_ (fun _ _ => mul_mem) g
  intro i j hij c
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hu c
  · exact hl c
  · exact absurd rfl hij

theorem exists_ne_zero_sq_ne_one [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have : Fintype F := Fintype.ofFinite F
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have h1 : a ^ 2 = 1 := hcon a ha
      have h2 : (a - 1) ^ 2 = 0 := by
        linear_combination h1 + (1 - a) * (CharTwo.two_eq_zero (R := F))
      have h3 : a = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h2)
      simp [h3]
  have := Finset.card_le_card hsub
  have h2 : (({0, 1} : Finset F)).card ≤ 2 := Finset.card_le_two
  rw [Nat.card_eq_fintype_card] at hq
  simp only [Finset.card_univ] at this
  omega

theorem not_isSolvable_sl2 [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    ¬ Group.IsSolvable SL(2, F) := by
  obtain ⟨a, ha, hasq⟩ := exists_ne_zero_sq_ne_one hq
  have : Group.IsPerfect SL(2, F) := ⟨SL2.commutator_eq_top ha hasq⟩
  have : Nontrivial SL(2, F) := ⟨⟨upperElt 1, 1, fun h => by
    simpa using congrArg (fun g : SL(2, F) => g 0 1) h⟩⟩
  exact Group.IsPerfect.not_isSolvable _

theorem le_borel_of_solvable [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F)
    {A : Subgroup SL(2, F)} (hA : stdSylow F ≤ A) (hs : Group.IsSolvable A) : A ≤ borel F := by
  intro g hg
  by_contra hc
  have hc' : g 1 0 ≠ 0 := hc
  have hlo : ∀ s : F, lowerElt s ∈ A := by
    intro s
    have hconj : upperElt (-(g 0 0 / g 1 0)) * (g * upperElt (-(s / g 1 0 ^ 2)) * g⁻¹) *
        upperElt (g 0 0 / g 1 0) = lowerElt s := by
      rw [conj_upperElt_conj_eq_lowerElt g hc']
      congr 1
      field_simp
    rw [← hconj]
    exact mul_mem (mul_mem (hA (upperElt_mem_stdSylow _)) (mul_mem (mul_mem hg
      (hA (upperElt_mem_stdSylow _))) (inv_mem hg))) (hA (upperElt_mem_stdSylow _))
  have htop : A = ⊤ := eq_top_of_unitriangular_mem (fun t => hA (upperElt_mem_stdSylow t)) hlo
  apply not_isSolvable_sl2 hq
  have hsurj : Function.Surjective A.subtype := by
    intro x
    exact ⟨⟨x, htop ▸ Subgroup.mem_top x⟩, rfl⟩
  exact Group.isSolvable_of_surjective hsurj

theorem exists_card_eq_two_pow [Finite F] [CharP F 2] : ∃ n : ℕ, 0 < n ∧ Nat.card F = 2 ^ n := by
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem card_stdSylow : Nat.card (stdSylow F) = Nat.card F :=
  (Nat.card_congr (Equiv.ofInjective upperElt upperElt_injective)).symm

theorem isPGroup_stdSylow [Finite F] [CharP F 2] : IsPGroup 2 (stdSylow F) := by
  obtain ⟨n, -, hn⟩ := exists_card_eq_two_pow (F := F)
  exact IsPGroup.of_card (by rw [card_stdSylow, hn])

theorem index_stdSylow [Finite F] : (stdSylow F).index = Nat.card F ^ 2 - 1 := by
  have h := (stdSylow F).card_mul_index
  rw [card_stdSylow, CFSG.GorensteinWalter.sl2_card_formula] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h

theorem not_two_dvd_index_stdSylow [Finite F] [CharP F 2] : ¬ 2 ∣ (stdSylow F).index := by
  obtain ⟨n, hn0, hn⟩ := exists_card_eq_two_pow (F := F)
  rw [index_stdSylow, hn]
  have h2 : 2 ∣ (2 ^ n) ^ 2 := dvd_pow (dvd_pow_self 2 hn0.ne') two_ne_zero
  have hpos : 0 < (2 ^ n) ^ 2 := by positivity
  omega

theorem exists_mulEquiv_map_eq_stdSylow [Finite F] [CharP F 2] {U : Subgroup SL(2, F)}
    (hU : IsPGroup 2 U) (hU' : ¬ 2 ∣ U.index) :
    ∃ φ : SL(2, F) ≃* SL(2, F), U.map φ.toMonoidHom = stdSylow F := by
  let P : Sylow 2 SL(2, F) := hU.toSylow hU'
  let Q : Sylow 2 SL(2, F) := isPGroup_stdSylow.toSylow not_two_dvd_index_stdSylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F) P Q
  refine ⟨MulAut.conj g, ?_⟩
  exact congrArg (fun S : Sylow 2 SL(2, F) => (S : Subgroup SL(2, F))) hg

variable {L : Type*} [Group L]

theorem exists_equiv_map_eq_stdSylow [Finite F] [CharP F 2] (e : L ≃* SL(2, F))
    {U : Subgroup L} (hU : IsPGroup 2 U) (hU' : ¬ 2 ∣ U.index) :
    ∃ e' : L ≃* SL(2, F), U.map e'.toMonoidHom = stdSylow F := by
  have h1 : IsPGroup 2 (U.map e.toMonoidHom) := hU.map _
  have h2 : ¬ 2 ∣ (U.map e.toMonoidHom).index := by
    rw [show U.map e.toMonoidHom = U.map (e : L →* SL(2, F)) from rfl, Subgroup.index_map_equiv]
    exact hU'
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_map_eq_stdSylow h1 h2
  refine ⟨e.trans φ, ?_⟩
  rw [← hφ, Subgroup.map_map]
  rfl

end SL2Sylow

open SL2Sylow

section Headline

open scoped MatrixGroups

variable {F : Type*} [Field F] {L : Type*} [Group L]

theorem sl2_le_normalizer_of_solvable [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F) (e : L ≃* SL(2, F)) {U A : Subgroup L} (hU : IsPGroup 2 U)
    (hU' : ¬ 2 ∣ U.index) (hUA : U ≤ A) (hA : Group.IsSolvable A) :
    A ≤ Subgroup.normalizer (U : Set L) := by
  obtain ⟨e', he'⟩ := exists_equiv_map_eq_stdSylow e hU hU'
  have : Group.IsSolvable (A.map e'.toMonoidHom) :=
    Group.isSolvable_of_surjective (f := (e'.subgroupMap A).toMonoidHom)
      (e'.subgroupMap A).surjective
  have h1 : stdSylow F ≤ A.map e'.toMonoidHom := he' ▸ Subgroup.map_mono hUA
  have h2 := le_borel_of_solvable hq h1 inferInstance
  rw [← normalizer_stdSylow, ← he', ← Subgroup.map_equiv_normalizer_eq] at h2
  exact (Subgroup.map_le_map_iff_of_injective e'.injective).1 h2

theorem sl2_normalizer_solvable_dvd [Finite F] [CharP F 2]
    (e : L ≃* SL(2, F)) {U : Subgroup L} (hU : IsPGroup 2 U) (hU' : ¬ 2 ∣ U.index) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) ∧
      (Nat.card F - 1) ∣ Nat.card ↥(Subgroup.normalizer (U : Set L)) := by
  obtain ⟨e', he'⟩ := exists_equiv_map_eq_stdSylow e hU hU'
  have key : ∀ x : L, x ∈ Subgroup.normalizer (U : Set L) ↔ e' x ∈ borel F := by
    intro x
    rw [← normalizer_stdSylow, ← he', ← Subgroup.map_equiv_normalizer_eq]
    simp
  let f : Subgroup.normalizer (U : Set L) →* borel F :=
    ((e' : L →* SL(2, F)).comp (Subgroup.normalizer (U : Set L)).subtype).codRestrict (borel F)
      (fun x => (key x.1).1 x.2)
  have hf : Function.Injective f := fun x y h =>
    Subtype.ext (e'.injective (congrArg Subtype.val h))
  refine ⟨Group.isSolvable_of_isSolvable_injective hf, ?_⟩
  let g : Fˣ →* Subgroup.normalizer (U : Set L) :=
    ((e'.symm : SL(2, F) →* L).comp (torusHom F)).codRestrict (Subgroup.normalizer (U : Set L))
      (fun x => (key _).2 (by simpa using torusHom_mem_borel x))
  have hg : Function.Injective g := fun x y h =>
    torusHom_injective (e'.symm.injective (congrArg Subtype.val h))
  have := Subgroup.card_dvd_of_injective g hg
  rwa [Nat.card_units] at this

theorem sl2_exists_order_dvd [Finite F] [CharP F 2] (e : L ≃* SL(2, F))
    {r : ℕ} (hr : r.Prime) (h : r ∣ Nat.card F - 1 ∨ r = 3) : ∃ x : L, orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  have : Finite L := Finite.of_equiv _ e.symm.toEquiv
  apply exists_prime_orderOf_dvd_card' r
  rw [Nat.card_congr e.toEquiv, CFSG.GorensteinWalter.sl2_card_formula]
  obtain ⟨n, -, hn⟩ := exists_card_eq_two_pow (F := F)
  have hdvd : r ∣ Nat.card F ^ 2 - 1 := by
    rcases h with h | rfl
    · refine h.trans ?_
      simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
    · rw [hn, ← pow_mul, mul_comm, pow_mul]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 n
  exact hdvd.mul_left _

end Headline

end CFSG.Quasithin
