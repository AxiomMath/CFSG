module

public import CFSG.Quasithin.EmptyFaithful.S152He11A
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin.He11

open Matrix

variable {F : Type*} [Field F]

@[expose] def uHom : Multiplicative F →* SL2 F where
  toFun t := uMat (Multiplicative.toAdd t)
  map_one' := uMat_zero
  map_mul' _ _ := uMat_add _ _

@[expose] def uSub (F : Type*) [Field F] : Subgroup (SL2 F) := (uHom (F := F)).range

theorem uMat_mem_uSub (t : F) : uMat t ∈ uSub F := ⟨Multiplicative.ofAdd t, rfl⟩

@[expose] def bSub (F : Type*) [Field F] : Subgroup (SL2 F) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}
  mul_mem' := by
    intro a b ha hb
    have ha' : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := ha
    have hb' : (b : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := hb
    show ((a * b : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    rw [coe_mul_apply, ha', hb']
    ring
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    have ha' : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := ha
    show ((a⁻¹ : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [ha']

theorem mem_bSub {g : SL2 F} : g ∈ bSub F ↔ (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := Iff.rfl

theorem diag_ne_zero {g : SL2 F} (hg : g ∈ bSub F) : (g : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  have hdet := g.det_coe
  rw [Matrix.det_fin_two, mem_bSub.mp hg, mul_zero, sub_zero] at hdet
  intro h
  rw [h, zero_mul] at hdet
  exact zero_ne_one hdet

@[expose] noncomputable def bDiag : ↥(bSub F) →* Fˣ where
  toFun g := Units.mk0 (((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0) (diag_ne_zero g.2)
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Units.val_mk0, Units.val_mul]
    show ((a * b : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = _
    rw [coe_mul_apply, mem_bSub.mp b.2]
    simp

theorem isSolvable_bSub : Group.IsSolvable ↥(bSub F) := by
  let f : Multiplicative F →* ↥(bSub F) :=
    (uHom (F := F)).codRestrict (bSub F) (fun t => by
      show (uMat (Multiplicative.toAdd t) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
      simp)
  refine Group.isSolvable_of_ker_le_range f bDiag ?_
  intro g hg
  have h00 : ((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
    simpa [bDiag] using this
  have hdet := (g : SL2 F).det_coe
  rw [Matrix.det_fin_two, mem_bSub.mp g.2, h00, mul_zero, sub_zero, one_mul] at hdet
  refine ⟨Multiplicative.ofAdd (((g : SL2 F) : Matrix (Fin 2) (Fin 2) F) 0 1), ?_⟩
  apply Subtype.ext
  apply ext_SL2 <;> simp [f, uHom, h00, hdet, mem_bSub.mp g.2]

theorem isSolvable_of_le_bSub {H : Subgroup (SL2 F)} (h : H ≤ bSub F) : Group.IsSolvable ↥H := by
  have := isSolvable_bSub (F := F)
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective h)

theorem card_uSub : Nat.card (uSub F) = Nat.card F := by
  have hinj : Function.Injective (uHom (F := F)) := fun s t h => by
    have : uMat (Multiplicative.toAdd s) = uMat (Multiplicative.toAdd t) := h
    exact Multiplicative.toAdd.injective (uMat_injective this)
  rw [uSub, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

section Finite

variable [Finite F] [CharP F 2]

theorem exists_card_eq_two_pow : ∃ n : ℕ, 0 < n ∧ Nat.card F = 2 ^ n := by
  have := Fintype.ofFinite F
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card]; exact hn⟩

omit [CharP F 2] in
theorem card_SL2 : Nat.card (SL2 F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  have := Fintype.ofFinite F
  have h := Matrix.card_SL_field (𝔽 := F) 2
  rw [Fin.prod_univ_two] at h
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h
  rw [← Nat.card_eq_fintype_card] at h
  rw [h]
  have hq : 2 ≤ Nat.card F := by
    have := Finite.one_lt_card (α := F)
    omega
  have hq1 : Nat.card F ^ 2 - Nat.card F = Nat.card F * (Nat.card F - 1) := by
    rw [Nat.mul_sub, mul_one, pow_two]
  rw [hq1]
  apply Nat.div_eq_of_eq_mul_left (by omega : 0 < Nat.card F - 1)
  ring

theorem isPGroup_uSub : IsPGroup 2 (uSub F) := by
  obtain ⟨n, -, hn⟩ := exists_card_eq_two_pow (F := F)
  exact IsPGroup.of_card (by rw [card_uSub, hn])

theorem not_dvd_index_uSub : ¬ 2 ∣ (uSub F).index := by
  obtain ⟨n, hn0, hn⟩ := exists_card_eq_two_pow (F := F)
  have hmul := Subgroup.card_mul_index (uSub F)
  rw [card_uSub, card_SL2] at hmul
  have hq : 0 < Nat.card F := Nat.card_pos
  have hidx : (uSub F).index = Nat.card F ^ 2 - 1 := by
    have := Nat.eq_of_mul_eq_mul_left hq hmul
    exact this
  rw [hidx]
  intro h2
  have h2q : 2 ∣ Nat.card F ^ 2 := by
    rw [hn, ← pow_mul]
    exact dvd_pow_self 2 (by omega)
  have hone : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ hq
  have : 2 ∣ 1 := by
    have h3 : Nat.card F ^ 2 = (Nat.card F ^ 2 - 1) + 1 := by omega
    rw [h3] at h2q
    exact (Nat.dvd_add_right h2).mp h2q
  omega

theorem sup_eq_top_of_not_solvable {H P : Subgroup (SL2 F)} (hH : ¬ Group.IsSolvable ↥H)
    (hP2 : IsPGroup 2 P) (hPi : ¬ 2 ∣ P.index) : H ⊔ P = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let PS : Sylow 2 (SL2 F) := hP2.toSylow hPi
  let US : Sylow 2 (SL2 F) := (isPGroup_uSub (F := F)).toSylow not_dvd_index_uSub
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL2 F) PS US
  set c : SL2 F →* SL2 F := MulDistribMulAction.toMonoidHom (SL2 F) (MulAut.conj g) with hc
  have hmap : P.map c = uSub F := by
    have h1 := congrArg (fun S : Sylow 2 (SL2 F) => (S : Subgroup (SL2 F))) hg
    simpa [PS, US, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] using h1
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hU : ∀ t : F, uMat t ∈ (H ⊔ P).map c := fun t => by
    have : uMat t ∈ P.map c := hmap ▸ uMat_mem_uSub t
    exact Subgroup.map_mono le_sup_right this
  by_cases hex : ∃ h ∈ (H ⊔ P).map c, ((h : SL2 F) : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0
  · obtain ⟨h, hh, hc0⟩ := hex
    have htop := eq_top_of_u_le hU hh hc0
    rw [← Subgroup.comap_map_eq_self_of_injective hcinj (H ⊔ P), htop, Subgroup.comap_top]
  · exfalso
    push Not at hex
    have hle : (H ⊔ P).map c ≤ bSub F := fun h hh => hex h hh
    have hHle : H.map c ≤ bSub F := (Subgroup.map_mono le_sup_left).trans hle
    have : Group.IsSolvable ↥(H.map c) := isSolvable_of_le_bSub hHle
    exact hH (Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective H c hcinj).toMonoidHom)
      (Subgroup.equivMapOfInjective H c hcinj).injective)

end Finite

end CFSG.Quasithin.He11
