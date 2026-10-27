module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic.ProjLine

open Matrix
open scoped LinearAlgebra.Projectivization MatrixGroups

variable (K : Type*) [Field K]

@[expose] def vecSome (x : K) : Fin 2 → K := ![x, 1]

@[expose] def vecNone : Fin 2 → K := ![1, 0]

theorem vecSome_ne (x : K) : vecSome K x ≠ 0 := fun h => by
  have := congrFun h 1
  simp [vecSome] at this

theorem vecNone_ne : vecNone K ≠ 0 := fun h => by
  have := congrFun h 0
  simp [vecNone] at this

@[expose] noncomputable def toLine : Option K → ℙ K (Fin 2 → K)
  | none => Projectivization.mk K (vecNone K) (vecNone_ne K)
  | some x => Projectivization.mk K (vecSome K x) (vecSome_ne K x)

open scoped _root_.Classical in
@[expose] noncomputable def ofVec (v : Fin 2 → K) : Option K :=
  if v 1 = 0 then none else some (v 0 / v 1)

theorem ofVec_smul (v : Fin 2 → K) (c : Kˣ) : ofVec K (c • v) = ofVec K v := by
  have hc : (c : K) ≠ 0 := c.ne_zero
  have h1 : (c • v) 1 = (c : K) * v 1 := by simp [Units.smul_def]
  have h0 : (c • v) 0 = (c : K) * v 0 := by simp [Units.smul_def]
  unfold ofVec
  rw [h0, h1]
  by_cases hv : v 1 = 0
  · simp [hv]
  · simp [hv, hc, mul_div_mul_left _ _ hc]

theorem mk_eq_toLine_ofVec (v : Fin 2 → K) (hv : v ≠ 0) :
    Projectivization.mk K v hv = toLine K (ofVec K v) := by
  unfold ofVec
  split_ifs with h
  · rw [toLine, Projectivization.mk_eq_mk_iff']
    refine ⟨v 0, ?_⟩
    have h0 : v 0 ≠ 0 := by
      intro h0
      apply hv
      ext i
      fin_cases i <;> simp [h0, h]
    ext i
    fin_cases i <;> simp [vecNone, h]
  · rw [toLine, Projectivization.mk_eq_mk_iff']
    refine ⟨v 1, ?_⟩
    ext i
    fin_cases i
    · simp only [vecSome, Fin.zero_eta, Pi.smul_apply, Matrix.cons_val_zero, smul_eq_mul]
      field_simp
    · simp [vecSome]

theorem ofVec_vecSome (x : K) : ofVec K (vecSome K x) = some x := by
  simp [ofVec, vecSome]

theorem ofVec_vecNone : ofVec K (vecNone K) = none := by
  simp [ofVec, vecNone]

theorem ofVec_rep (p : ℙ K (Fin 2 → K)) : toLine K (ofVec K p.rep) = p := by
  rw [← mk_eq_toLine_ofVec K p.rep p.rep_nonzero, Projectivization.mk_rep]

@[expose] noncomputable def lineEquiv : Option K ≃ ℙ K (Fin 2 → K) where
  toFun := toLine K
  invFun p := ofVec K p.rep
  left_inv o := by
    have key : ∀ (v : Fin 2 → K) (hv : v ≠ 0),
        ofVec K (Projectivization.mk K v hv).rep = ofVec K v := by
      intro v hv
      obtain ⟨c, hc⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
      rw [← hc, ofVec_smul K v c]
    cases o with
    | none => exact (key _ _).trans (ofVec_vecNone K)
    | some x => exact (key _ _).trans (ofVec_vecSome K x)
  right_inv p := ofVec_rep K p

@[expose] noncomputable def mobHom : PGL(Fin 2, K) →* Equiv.Perm (Option K) :=
  (Equiv.permCongrHom (lineEquiv K).symm).toMonoidHom.comp
    (MulAction.toPermHom PGL(Fin 2, K) (ℙ K (Fin 2 → K)))

theorem mobHom_apply (g : PGL(Fin 2, K)) (o : Option K) :
    mobHom K g o = (lineEquiv K).symm (g • lineEquiv K o) := rfl

theorem mobHom_mk_apply (g : GL (Fin 2) K) (o : Option K) :
    mobHom K (ProjGenLinGroup.mk g) o =
      ofVec K ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ
        (match o with | none => vecNone K | some x => vecSome K x)) := by
  rw [mobHom_apply]
  cases o with
  | none =>
    change (lineEquiv K).symm (ProjGenLinGroup.mk g • toLine K none) = _
    rw [toLine, Projectivization.PGL.mk_smul_mk, mk_eq_toLine_ofVec]
    exact (lineEquiv K).left_inv _
  | some x =>
    change (lineEquiv K).symm (ProjGenLinGroup.mk g • toLine K (some x)) = _
    rw [toLine, Projectivization.PGL.mk_smul_mk, mk_eq_toLine_ofVec]
    exact (lineEquiv K).left_inv _

theorem mobHom_mk_some [DecidableEq K] (g : GL (Fin 2) K) (x : K) :
    mobHom K (ProjGenLinGroup.mk g) (some x) =
      if (g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0 then none
      else some (((g : Matrix (Fin 2) (Fin 2) K) 0 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 0 1) /
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1)) := by
  rw [mobHom_mk_apply]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 0
  · simp [ofVec, vecSome, mulVec, dotProduct, Fin.sum_univ_two, h]
  · simp [ofVec, vecSome, mulVec, dotProduct, Fin.sum_univ_two, h]

theorem mobHom_mk_none [DecidableEq K] (g : GL (Fin 2) K) :
    mobHom K (ProjGenLinGroup.mk g) none =
      if (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 then none
      else some ((g : Matrix (Fin 2) (Fin 2) K) 0 0 / (g : Matrix (Fin 2) (Fin 2) K) 1 0) := by
  rw [mobHom_mk_apply]
  by_cases h : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · simp [ofVec, vecNone, mulVec, dotProduct, Fin.sum_univ_two, h]
  · simp [ofVec, vecNone, mulVec, dotProduct, Fin.sum_univ_two, h]

theorem mobHom_injective : Function.Injective (mobHom K) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective g
  rw [MonoidHom.mem_ker] at hg
  have hinf := congrArg (fun σ : Equiv.Perm (Option K) => σ none) hg
  have h0 := congrArg (fun σ : Equiv.Perm (Option K) => σ (some 0)) hg
  have h1 := congrArg (fun σ : Equiv.Perm (Option K) => σ (some 1)) hg
  simp only [Equiv.Perm.coe_one, id_eq, mobHom_mk_none, mobHom_mk_some] at hinf h0 h1
  set M := (g : Matrix (Fin 2) (Fin 2) K)
  have hc : M 1 0 = 0 := by
    by_contra hc
    simp [M, hc] at hinf
  simp only [hc, zero_add, mul_zero, mul_one] at h0 h1
  have hd : M 1 1 ≠ 0 := by
    intro hd
    have hdet := g.isUnit.ne_zero
    apply (Matrix.isUnit_iff_isUnit_det M).1 g.isUnit |>.ne_zero
    rw [det_fin_two, hc, hd]
    ring
  simp only [hd, ite_false] at h0 h1
  have hb : M 0 1 = 0 := by
    have := Option.some_injective _ h0
    rwa [div_eq_zero_iff, or_iff_left hd] at this
  have ha : M 0 0 = M 1 1 := by
    have := Option.some_injective _ h1
    rw [hb, add_zero, div_eq_one_iff_eq hd] at this
    exact this
  rw [Subgroup.mem_bot, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar]
  refine ⟨Units.mk0 (M 1 1) hd, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [GeneralLinearGroup.scalar, M, ha, hb, hc]

theorem card_center_GL [Finite K] :
    Nat.card (Subgroup.center (GL (Fin 2) K)) = Nat.card Kˣ := by
  rw [GeneralLinearGroup.center_eq_range_scalar]
  refine Nat.card_congr (MonoidHom.ofInjective ?_).toEquiv.symm
  intro u v huv
  have := congrArg (fun g : GL (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K) 0 0) huv
  simpa [GeneralLinearGroup.scalar] using Units.ext this

theorem card_PGL_two [Fintype K] [DecidableEq K] :
    Nat.card PGL(Fin 2, K) * (Fintype.card K - 1) =
      (Fintype.card K ^ 2 - 1) * (Fintype.card K ^ 2 - Fintype.card K) := by
  have hGL := Matrix.card_GL_field (𝔽 := K) (n := 2)
  rw [Fin.prod_univ_two] at hGL
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one] at hGL
  have h := (Subgroup.center (GL (Fin 2) K)).card_eq_card_quotient_mul_card_subgroup
  rw [card_center_GL, hGL] at h
  have hu : Nat.card Kˣ = Fintype.card K - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [hu] at h
  rw [h]
  rfl


section Congr

variable {K} {L : Type*} [Field L]

@[expose] noncomputable def glCongr (e : K ≃+* L) : GL (Fin 2) K ≃* GL (Fin 2) L where
  toFun := Matrix.GeneralLinearGroup.map e.toRingHom
  invFun := Matrix.GeneralLinearGroup.map e.symm.toRingHom
  left_inv g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  right_inv g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  map_mul' g h := map_mul _ g h

@[expose] noncomputable def pglCongr (e : K ≃+* L) : PGL(Fin 2, K) ≃* PGL(Fin 2, L) :=
  QuotientGroup.congr _ _ (glCongr e) (Subgroup.map_center_eq (glCongr e))

end Congr

end CFSG.RankThree.PartTwo.Sec4.Sporadic.ProjLine
