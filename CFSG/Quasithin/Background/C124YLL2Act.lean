module

public import CFSG.Quasithin.Background.C124YLL2Ctx
public import CFSG.Quasithin.Background.C124YLS2Sem

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.YL

open CFSG.Quasithin CFSG.Open Matrix
open scoped MatrixGroups

namespace L2Ctx

variable {W : Type*} [CommGroup W] [Finite W] {F : Type} [Field F] [Finite F]
  {Xs Ls : Subgroup (MulAut W)} {U Z : Subgroup W} (C : L2Ctx F Xs Ls U Z)

@[expose] noncomputable def indQ (x : ↥Xs) :
    Multiplicative (Fin 2 → F) →* Multiplicative (Fin 2 → F) :=
  indHom C.coord Xs C.hU C.hZ x

theorem indQ_mul (x y : ↥Xs) (q : Multiplicative (Fin 2 → F)) :
    C.indQ (x * y) q = C.indQ x (C.indQ y q) := by
  have := congrArg (fun f : Monoid.End (Multiplicative (Fin 2 → F)) => f q)
    ((indHom C.coord Xs C.hU C.hZ).map_mul x y)
  exact this

theorem indQ_one (q : Multiplicative (Fin 2 → F)) : C.indQ 1 q = q := by
  have := congrArg (fun f : Monoid.End (Multiplicative (Fin 2 → F)) => f q)
    ((indHom C.coord Xs C.hU C.hZ).map_one)
  exact this

@[expose] noncomputable def gOf (x : ↥Xs) : (Fin 2 → F) →+ (Fin 2 → F) :=
  AddMonoidHom.mk' (fun v => Multiplicative.toAdd (C.indQ x (Multiplicative.ofAdd v)))
    (fun a b => by
      rw [ofAdd_add, map_mul, toAdd_mul])

theorem gOf_apply (x : ↥Xs) (v : Fin 2 → F) :
    C.gOf x v = Multiplicative.toAdd (C.indQ x (Multiplicative.ofAdd v)) := rfl

theorem gOf_mul (x y : ↥Xs) (v : Fin 2 → F) : C.gOf (x * y) v = C.gOf x (C.gOf y v) := by
  rw [gOf_apply, gOf_apply, gOf_apply, indQ_mul, ofAdd_toAdd]

theorem gOf_one (v : Fin 2 → F) : C.gOf 1 v = v := by
  rw [gOf_apply, indQ_one]
  rfl

theorem gOf_theta (s : SL(2, F)) (v : Fin 2 → F) :
    C.gOf (C.thetaX s) v = (s : Matrix (Fin 2) (Fin 2) F) *ᵥ v := by
  rw [gOf_apply]
  have := C.ind_theta s (Multiplicative.ofAdd v)
  change Multiplicative.toAdd
    (indHom C.coord Xs C.hU C.hZ (C.thetaX s) (Multiplicative.ofAdd v)) = _
  rw [this]
  rfl

theorem gOf_pow (x : ↥Xs) (n : ℕ) (v : Fin 2 → F) : C.gOf (x ^ n) v = (C.gOf x)^[n] v := by
  induction n generalizing v with
  | zero => simpa using C.gOf_one v
  | succ n ih =>
    rw [pow_succ', gOf_mul, ih, Function.iterate_succ_apply']

theorem eq_of_gOf {x y : ↥Xs} (h : ∀ v, C.gOf x v = C.gOf y v) : x = y := by
  have hq : ∀ q, C.indQ x q = C.indQ y q := fun q => by
    have := h (Multiplicative.toAdd q)
    rw [gOf_apply, gOf_apply] at this
    simpa using congrArg Multiplicative.ofAdd this
  have : y⁻¹ * x = 1 := by
    apply C.faithful
    refine MonoidHom.ext fun q => ?_
    change C.indQ (y⁻¹ * x) q = q
    rw [indQ_mul, hq, ← indQ_mul, inv_mul_cancel, indQ_one]
  exact (inv_mul_eq_one.1 this).symm

theorem thetaX_conj (x : ↥Xs) (s s' : SL(2, F))
    (h : (C.θ s' : MulAut W) = (x : MulAut W) * (C.θ s : MulAut W) * (x : MulAut W)⁻¹) :
    x * C.thetaX s = C.thetaX s' * x := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul, thetaX]
  rw [h]
  group

theorem normSL (x : ↥Xs) : S2.NormSL (C.gOf x) (C.gOf x⁻¹) := by
  refine ⟨fun q => ?_, fun q => ?_, fun s => ?_, fun s' => ?_⟩
  · rw [← gOf_mul, inv_mul_cancel, gOf_one]
  · rw [← gOf_mul, mul_inv_cancel, gOf_one]
  · obtain ⟨s', hs'⟩ := C.θ_surj
      ⟨x * ((C.θ s : ↥Ls) : MulAut W) * (x : MulAut W)⁻¹, by
        have := (Subgroup.mem_normalizer_iff.1 (C.hnorm x x.2) _).1 (C.θ s).2
        exact this⟩
    refine ⟨s', fun v => ?_⟩
    have e := C.thetaX_conj x s s' (congrArg Subtype.val hs')
    rw [← C.gOf_theta s' (C.gOf x v), ← C.gOf_mul, ← e, gOf_mul, gOf_theta]
  · obtain ⟨s, hs⟩ := C.θ_surj
      ⟨(x : MulAut W)⁻¹ * ((C.θ s' : ↥Ls) : MulAut W) * x, by
        have := (Subgroup.mem_normalizer_iff.1 (C.hnorm x⁻¹ (Xs.inv_mem x.2)) _).1 (C.θ s').2
        simpa using this⟩
    refine ⟨s, fun v => ?_⟩
    have e : x * C.thetaX s = C.thetaX s' * x := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, thetaX]
      rw [congrArg Subtype.val hs]
      group
    rw [← C.gOf_theta s' (C.gOf x v), ← C.gOf_mul, ← e, gOf_mul, gOf_theta]

end L2Ctx

end CFSG.Quasithin.C124.YL
