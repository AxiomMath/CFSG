module

public import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Frame
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1U3Emb
import CFSG.RankThree.PartTwo.KFacts.K71SU3AutFacts
import CFSG.RankThree.PartTwo.KFacts.K72L3Unitary
import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.KFacts (psuConj psuField psuConj_mk psuField_mk coe_suConj
  coe_suField unitaryIsom3)
open CFSG.PGLModel (projSU)
open CFSG.Assembly.RankThreeEven (projSL)
open scoped MatrixGroups

theorem res1U3_psu_slTwo {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (heven : Even n) {x w : unitaryPSU h 3} (hx : orderOf x = 3) (hwx : w * x = x * w)
    (hw1 : w ≠ 1) {β : MulAut (unitaryPSU h 3)} (hβ2 : β * β = 1) (hβx : β x = x)
    (hβw : β w = w⁻¹) {F : Type} [Field F] (φ : F →+* K) (hφ : ∀ y, h.bar (φ y) = φ y) :
    w ^ (2 ^ n + 1) = 1 ∧ ∃ ι : SL(2, F) →* unitaryPSU h 3, Function.Injective ι ∧
      ∀ B, ι B * w = w * ι B := by
  have hn1 := h.one_le
  have hn2 : 2 ≤ n := by
    obtain ⟨k, rfl⟩ := heven
    omega
  have hq3 : 2 ^ n % 3 = 1 := by
    obtain ⟨k, rfl⟩ := heven
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hq2 : 2 < 2 ^ n :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hπi : Function.Injective (unitaryProj h 3) := KFacts.unitaryProj_three_injective h hq3
  obtain ⟨X, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨W, rfl⟩ := unitaryProj_surjective h 3 w
  obtain ⟨A, s, rfl⟩ := KFacts.exists_psuConj_mul_psuField hq2 β
  have hs2 : s ^ 2 = 1 := by
    obtain ⟨B', hB'⟩ := KFacts.exists_psuConj_mul_psuField_pow h A s 2
    rw [pow_two (psuConj h A * psuField h s), hβ2] at hB'
    exact (KFacts.eq_one_of_psuConj_mul_psuField_eq_one B' (s ^ 2) hB'.symm).1
  have hs := res1U3_eq_one_or_eq_bar h hs2
  have hact : ∀ Y : unitarySU 2 n K 3, (psuConj h A * psuField h s) ((unitaryProj h 3) Y) =
      (unitaryProj h 3) (KFacts.suConj h A (KFacts.suField h s Y)) := fun Y => by
    rw [MulAut.mul_apply]
    exact (congrArg (psuConj h A) (psuField_mk s Y)).trans (psuConj_mk A _)
  set Am : Matrix (Fin 3) (Fin 3) K := ((A : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hAm
  set Xm : Matrix (Fin 3) (Fin 3) K := ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hXm
  set Wm : Matrix (Fin 3) (Fin 3) K := ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hWm
  have hAu : IsUnit Am := (A : GL (Fin 3) K).isUnit
  have hAX : Am * Xm.map s = Xm * Am := by
    have e1 : KFacts.suConj h A (KFacts.suField h s X) = X :=
      hπi ((hact X).symm.trans hβx)
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => (Y : GL (Fin 3) K)) e1
    simp only [coe_suConj, coe_suField, Subgroup.coe_inv] at e2
    have e3 : (A : GL (Fin 3) K) * glAut s (X : GL (Fin 3) K) = X * A := by
      calc (A : GL (Fin 3) K) * glAut s (X : GL (Fin 3) K) =
          ((A : GL (Fin 3) K) * glAut s (X : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹) * A := by
            group
        _ = X * A := by rw [e2]
    have e4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) e3
    simp only [Units.val_mul, coe_glAut] at e4
    exact e4
  have hAW : Wm * Am * Wm.map s = Am := by
    have e1 : KFacts.suConj h A (KFacts.suField h s W) = W⁻¹ :=
      hπi ((hact W).symm.trans (hβw.trans (map_inv (unitaryProj h 3) W).symm))
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => (Y : GL (Fin 3) K)) e1
    simp only [coe_suConj, coe_suField, Subgroup.coe_inv] at e2
    have e3 : (W : GL (Fin 3) K) * A * glAut s (W : GL (Fin 3) K) = A := by
      have e5 : (W : GL (Fin 3) K) * ((A : GL (Fin 3) K) * glAut s (W : GL (Fin 3) K) *
          (A : GL (Fin 3) K)⁻¹) = 1 := by
        rw [e2, mul_inv_cancel]
      calc (W : GL (Fin 3) K) * A * glAut s (W : GL (Fin 3) K) =
          (W : GL (Fin 3) K) * ((A : GL (Fin 3) K) * glAut s (W : GL (Fin 3) K) *
            (A : GL (Fin 3) K)⁻¹) * A := by group
        _ = A := by rw [e5, one_mul]
    have e4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) e3
    simp only [Units.val_mul, coe_glAut] at e4
    exact e4
  have hXmem := (mem_unitarySU_iff h).mp X.2
  have hWmem := (mem_unitarySU_iff h).mp W.2
  have hX3 : Xm ^ 3 = 1 := by
    have e0 : (unitaryProj h 3) X ^ 3 = 1 := by
      have := pow_orderOf_eq_one ((unitaryProj h 3) X)
      rwa [hx] at this
    have e : X ^ 3 = 1 := hπi (by rw [map_pow, map_one]; exact e0)
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) e
    simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using e2
  have hX1 : Xm ≠ 1 := by
    intro e
    have : X = 1 := Subtype.ext (Units.ext e)
    rw [this, map_one, orderOf_one] at hx
    norm_num at hx
  have hW1 : Wm ≠ 1 := by
    intro e
    apply hw1
    have : W = 1 := Subtype.ext (Units.ext e)
    rw [this, map_one]
  have hWX : Wm * Xm = Xm * Wm := by
    have e : W * X = X * W := hπi (by rw [map_mul, map_mul, hwx])
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) e
    simpa only [Subgroup.coe_mul, Units.val_mul] using e2
  obtain ⟨τ, hτ, hτ1, hτb⟩ := res1U3_exists_cubeRoot h heven
  obtain ⟨g, c, hg, hXg, hgram⟩ :=
    res1U3_exists_frame h hτ hτ1 hτb hX3 hXmem.1 hXmem.2 hX1
  obtain ⟨δ, hWg⟩ := res1U3_mul_eq_diagonal hτ hτ1 hg hXg hWX
  obtain ⟨hδ02, hδ⟩ :=
    res1U3_torus_inv h hτ hτ1 hτb hg hAu hgram hXg hWg hWmem.2 hW1 hs hAX hAW
  refine ⟨?_, ?_⟩
  ·
    have e := res1U3_pow_eq_one h hg hWg hδ
    have : W ^ (2 ^ n + 1) = 1 :=
      Subtype.ext (Units.ext (by
        simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
          Units.val_one] using e))
    rw [← map_pow, this, map_one]
  ·
    obtain ⟨ι, hι, hcomm⟩ := res1U3_exists_slTwo_hom h φ hφ hg hgram
    refine ⟨(unitaryProj h 3).comp ι, hπi.comp hι, fun B => ?_⟩
    have e : ι B * W = W * ι B := Subtype.ext (Units.ext (by
      simpa only [Subgroup.coe_mul, Units.val_mul] using hcomm B hδ02 hWg))
    rw [MonoidHom.comp_apply, ← map_mul, e, map_mul]

theorem res1U3_psu_commute {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)
    (heven : Even n) {x a b : unitaryPSU h 3} (hx : orderOf x = 3) (ha : a * x = x * a)
    (hb : b * x = x * b) : a * b = b * a := by
  have hq3 : 2 ^ n % 3 = 1 := by
    obtain ⟨k, rfl⟩ := heven
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  have hπi : Function.Injective (unitaryProj h 3) := KFacts.unitaryProj_three_injective h hq3
  obtain ⟨X, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨Wa, rfl⟩ := unitaryProj_surjective h 3 a
  obtain ⟨Wb, rfl⟩ := unitaryProj_surjective h 3 b
  set Xm : Matrix (Fin 3) (Fin 3) K := ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hXm
  have hXmem := (mem_unitarySU_iff h).mp X.2
  have hX3 : Xm ^ 3 = 1 := by
    have e0 : (unitaryProj h 3) X ^ 3 = 1 := by
      have := pow_orderOf_eq_one ((unitaryProj h 3) X)
      rwa [hx] at this
    have e : X ^ 3 = 1 := hπi (by rw [map_pow, map_one]; exact e0)
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) e
    simpa only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] using e2
  have hX1 : Xm ≠ 1 := by
    intro e
    have : X = 1 := Subtype.ext (Units.ext e)
    rw [this, map_one, orderOf_one] at hx
    norm_num at hx
  have hcomm : ∀ W : unitarySU 2 n K 3,
      (unitaryProj h 3) W * (unitaryProj h 3) X = (unitaryProj h 3) X * (unitaryProj h 3) W →
      ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Xm =
        Xm * ((W : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun W hW => by
    have e : W * X = X * W := hπi (by rw [map_mul, map_mul, hW])
    have e2 := congrArg (fun Y : unitarySU 2 n K 3 => ((Y : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) e
    simpa only [Subgroup.coe_mul, Units.val_mul] using e2
  obtain ⟨τ, hτ, hτ1, hτb⟩ := res1U3_exists_cubeRoot h heven
  obtain ⟨g, c, hg, hXg, -⟩ := res1U3_exists_frame h hτ hτ1 hτb hX3 hXmem.1 hXmem.2 hX1
  obtain ⟨δa, hag⟩ := res1U3_mul_eq_diagonal hτ hτ1 hg hXg (hcomm Wa ha)
  obtain ⟨δb, hbg⟩ := res1U3_mul_eq_diagonal hτ hτ1 hg hXg (hcomm Wb hb)
  set Am : Matrix (Fin 3) (Fin 3) K := ((Wa : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hAm
  set Bm : Matrix (Fin 3) (Fin 3) K := ((Wb : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hBm
  have hd : diagonal δa * diagonal δb = diagonal δb * diagonal δa := by
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hAB : Am * Bm = Bm * Am := by
    refine (hg.mul_left_inj).mp ?_
    calc Am * Bm * g = Am * (g * diagonal δb) := by rw [Matrix.mul_assoc, hbg]
      _ = g * (diagonal δa * diagonal δb) := by
        rw [← Matrix.mul_assoc, hag, Matrix.mul_assoc]
      _ = g * (diagonal δb * diagonal δa) := by rw [hd]
      _ = Bm * (g * diagonal δa) := by rw [← Matrix.mul_assoc, ← hbg, Matrix.mul_assoc]
      _ = Bm * Am * g := by rw [← hag, Matrix.mul_assoc]
  have e : Wa * Wb = Wb * Wa := Subtype.ext (Units.ext (by
    simpa only [Subgroup.coe_mul, Units.val_mul] using hAB))
  rw [← map_mul, ← map_mul, e]

theorem res1U3_commute_of_commute {Y : Type} [Group Y] {n : ℕ} (hn : 0 < n) (heven : Even n)
    (e : Y ≃* projSU 3 2 n) {x a b : Y} (hx : orderOf x = 3) (ha : a * x = x * a)
    (hb : b * x = x * b) : a * b = b * a := by
  set hU := Sec4.unitaryFieldData_galoisField 2 n hn with hhU
  set E : Y ≃* unitaryPSU hU 3 := e.trans (Sec4.projSUEquivUnitaryPSU 2 n hU) with hE
  apply E.injective
  rw [map_mul, map_mul]
  exact res1U3_psu_commute hU heven (x := E x) (by rw [MulEquiv.orderOf_eq]; exact hx)
    (by rw [← map_mul, ← map_mul, ha]) (by rw [← map_mul, ← map_mul, hb])

theorem res1U3_exists_slTwo_le_centralizer {Y : Type} [Group Y] {n : ℕ} (hn : 0 < n)
    (heven : Even n) (e : Y ≃* projSU 3 2 n) {x w : Y} (hx : orderOf x = 3)
    (hwx : w * x = x * w) (hw1 : w ≠ 1) {β : MulAut Y} (hβ2 : β * β = 1) (hβx : β x = x)
    (hβw : β w = w⁻¹) :
    w ^ (2 ^ n + 1) = 1 ∧ ∃ S : Subgroup Y, S ≤ Subgroup.centralizer {w} ∧
      Nonempty (S ≃* projSL 2 (GaloisField 2 n)) := by
  set hU := Sec4.unitaryFieldData_galoisField 2 n hn with hhU
  set E : Y ≃* unitaryPSU hU 3 := e.trans (Sec4.projSUEquivUnitaryPSU 2 n hU) with hE
  let β' : MulAut (unitaryPSU hU 3) := (E.symm.trans β).trans E
  have hβ'a : ∀ y : Y, β' (E y) = E (β y) := fun y => by
    change E (β (E.symm (E y))) = E (β y)
    rw [MulEquiv.symm_apply_apply]
  have hβ'2 : β' * β' = 1 := by
    ext p
    obtain ⟨y, rfl⟩ := E.surjective p
    rw [MulAut.mul_apply, hβ'a, hβ'a, MulAut.one_apply, ← MulAut.mul_apply, hβ2,
      MulAut.one_apply]
  have := hU.finite
  have : Fintype hU.fixedField := Fintype.ofFinite _
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField 2 n) = Fintype.card hU.fixedField := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU.card_fixedField,
      GaloisField.card 2 n hn.ne']
  let ψ : GaloisField 2 n ≃+* hU.fixedField := FiniteField.ringEquivOfCardEq hcard
  let φ : GaloisField 2 n →+* GaloisField 2 (2 * n) :=
    hU.fixedField.subtype.comp (ψ : GaloisField 2 n →+* hU.fixedField)
  have hφ : ∀ y, hU.bar (φ y) = φ y := fun y => (ψ y).2
  obtain ⟨hpow, ι, hι, hcomm⟩ := res1U3_psu_slTwo hU heven
    (x := E x) (w := E w) (by rw [MulEquiv.orderOf_eq]; exact hx)
    (by rw [← map_mul, ← map_mul, hwx]) ((map_ne_one_iff E E.injective).mpr hw1) hβ'2
    (by rw [hβ'a, hβx]) (by rw [hβ'a, hβw, map_inv]) φ hφ
  refine ⟨E.injective (by rw [map_pow, hpow, map_one]), ?_⟩
  set f : SL(2, GaloisField 2 n) →* Y := E.symm.toMonoidHom.comp ι with hf
  have hfi : Function.Injective f := E.symm.injective.comp hι
  refine ⟨f.range, ?_, ⟨(MonoidHom.ofInjective hfi).symm.trans
    (KFacts.KS116Proof.projSLEquiv (GaloisField 2 n))⟩⟩
  rintro _ ⟨B, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply E.injective
  have hEf : E (f B) = ι B := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [map_mul, map_mul, hEf, hcomm B]

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
