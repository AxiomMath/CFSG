
module

public import CFSG.Monster.B.TwoA.Unitary.Form
public meta import CFSG.Monster.B.TwoA.Unitary.Form
public import CFSG.Monster.B.TwoA.Unitary.PlanesInputs
import all CFSG.Fischer.F4

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix
open CFSG.Monster.B.Classical.UnitarySix (bar bar_add bar_mul bar_bar bar_zero bar_one
  bar_eq_zero_iff)

instance : RingHomSurjective barHom := ⟨fun z => ⟨bar z, bar_bar z⟩⟩

@[expose] def barLin : V6 →ₛₗ[barHom] V6 where
  toFun := barV
  map_add' := barV_add
  map_smul' := barV_smul

theorem barLin_apply (s : V6) : barLin s = barV s := rfl

@[expose] def subBar (P : Submodule F4 V6) : Submodule F4 V6 := P.map barLin

theorem mem_subBar {P : Submodule F4 V6} {x : V6} : x ∈ subBar P ↔ barV x ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [barLin_apply, barV_barV]
    exact hy
  · intro h
    exact ⟨barV x, h, barV_barV x⟩

theorem subBar_subBar (P : Submodule F4 V6) : subBar (subBar P) = P := by
  ext x
  rw [mem_subBar, mem_subBar, barV_barV]

@[expose] def subBarPow (ε : ZMod 2) (P : Submodule F4 V6) : Submodule F4 V6 :=
  if ε = 0 then P else subBar P

theorem subBarPow_zero (P : Submodule F4 V6) : subBarPow 0 P = P := ite_eq_left rfl

theorem subBarPow_one (P : Submodule F4 V6) : subBarPow 1 P = subBar P := ite_eq_right (by decide)

theorem subBarPow_add (a b : ZMod 2) (P : Submodule F4 V6) :
    subBarPow (a + b) P = subBarPow b (subBarPow a P) := by
  rcases zmod2_cases' a with rfl | rfl <;> rcases zmod2_cases' b with rfl | rfl
  · simp [subBarPow_zero]
  · simp [subBarPow_zero, subBarPow_one]
  · simp [subBarPow_zero, subBarPow_one]
  · rw [show (1 : ZMod 2) + 1 = 0 from rfl, subBarPow_zero, subBarPow_one, subBarPow_one,
      subBar_subBar]

theorem subBarPow_subBarPow (ε : ZMod 2) (P : Submodule F4 V6) :
    subBarPow ε (subBarPow ε P) = P := by
  rw [← subBarPow_add, CharTwo.add_self_eq_zero, subBarPow_zero]

@[expose] def subMul (P : Submodule F4 V6) (A : Matrix (Fin 6) (Fin 6) F4) : Submodule F4 V6 :=
  P.map (vecMulLinear A)

theorem mem_subMul_of_mem {P : Submodule F4 V6} {s : V6} (hs : s ∈ P)
    (A : Matrix (Fin 6) (Fin 6) F4) : s ᵥ* A ∈ subMul P A :=
  ⟨s, hs, rfl⟩

theorem subMul_mul (P : Submodule F4 V6) (A B : Matrix (Fin 6) (Fin 6) F4) :
    subMul (subMul P A) B = subMul P (A * B) := by
  rw [subMul, subMul, subMul, ← Submodule.map_comp]
  congr 1
  refine LinearMap.ext fun s => ?_
  change s ᵥ* A ᵥ* B = s ᵥ* (A * B)
  rw [vecMul_vecMul]

theorem subMul_one (P : Submodule F4 V6) : subMul P 1 = P := by
  rw [subMul]
  have : (vecMulLinear (1 : Matrix (Fin 6) (Fin 6) F4)) = LinearMap.id :=
    LinearMap.ext fun s => vecMul_one s
  rw [this, Submodule.map_id]

theorem subMul_scalar (P : Submodule F4 V6) (c : F4ˣ) :
    subMul P (Matrix.scalar (Fin 6) (c : F4)) = P := by
  have hv : ∀ x : V6, x ᵥ* Matrix.scalar (Fin 6) (c : F4) = (c : F4) • x := fun x => by
    funext j
    simp [vecMul_diagonal, Matrix.scalar_apply, mul_comm]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change y ᵥ* _ ∈ P
    rw [hv]
    exact P.smul_mem _ hy
  · intro hx
    refine ⟨(c⁻¹ : F4ˣ) • x, P.smul_mem _ hx, ?_⟩
    change ((c⁻¹ : F4ˣ) • x) ᵥ* _ = x
    rw [hv, Units.smul_def, smul_smul, Units.mul_inv, one_smul]

theorem subBar_subMul (P : Submodule F4 V6) (A : Matrix (Fin 6) (Fin 6) F4) :
    subBar (subMul P A) = subMul (subBar P) (barM A) := by
  ext x
  rw [mem_subBar]
  constructor
  · rintro ⟨y, hy, e⟩
    refine ⟨barV y, (mem_subBar).2 (by rw [barV_barV]; exact hy), ?_⟩
    change barV y ᵥ* barM A = x
    rw [← barV_barV x, ← e]
    change barV y ᵥ* barM A = barV (y ᵥ* A)
    rw [barV_vecMul]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨barV y, (mem_subBar).1 hy, ?_⟩
    change barV y ᵥ* A = barV (y ᵥ* barM A)
    rw [barV_vecMul]
    exact congrArg (barV y ᵥ* ·) (barM_barM A).symm

theorem subBarPow_subMul (ε : ZMod 2) (P : Submodule F4 V6) (A : Matrix (Fin 6) (Fin 6) F4) :
    subBarPow ε (subMul P A) = subMul (subBarPow ε P) (if ε = 0 then A else barM A) := by
  by_cases h : ε = 0
  · rw [subBarPow, ite_eq_left h, subBarPow, ite_eq_left h, ite_eq_left h]
  · rw [subBarPow, ite_eq_right h, subBarPow, ite_eq_right h, ite_eq_right h, subBar_subMul]

@[expose] def quotMul (P : Submodule F4 V6) : SUh ⧸ Zh → Submodule F4 V6 :=
  Quotient.lift (s := QuotientGroup.leftRel Zh)
    (fun g : SUh => subMul P ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4))
    (by
      intro a b hab
      obtain ⟨c, hc⟩ := QuotientGroup.leftRel_apply.1 hab
      have hb : (b : GL (Fin 6) F4) =
          (a : GL (Fin 6) F4) * GeneralLinearGroup.scalar (Fin 6) c := by
        have : (b : GL (Fin 6) F4) = (a : GL (Fin 6) F4) * ((a⁻¹ * b : SUh) : GL (Fin 6) F4) := by
          rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
        rw [this, hc]
      change subMul P _ = subMul P _
      rw [hb, Units.val_mul, ← subMul_mul, GeneralLinearGroup.coe_scalar, subMul_scalar])

theorem quotMul_mk (P : Submodule F4 V6) (g : SUh) :
    quotMul P (g : SUh ⧸ Zh) = subMul P ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := rfl

@[expose] def sigmaAct (P : Submodule F4 V6) (x : SigmaU6) : Submodule F4 V6 :=
  subBarPow (Multiplicative.toAdd x.right) (quotMul P x.left)

theorem sigmaAct_mk (P : Submodule F4 V6) (g : SUh) (ε : ZMod 2) :
    sigmaAct P ⟨(g : SUh ⧸ Zh), Multiplicative.ofAdd ε⟩ =
      subBarPow ε (subMul P ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) := rfl

theorem frobPowQ_mk (ε : ZMod 2) (g : SUh) :
    frobPowQ ε (g : SUh ⧸ Zh) =
      ((if ε = 0 then g else frobSU g : SUh) : SUh ⧸ Zh) := by
  by_cases h : ε = 0
  · rw [frobPowQ, ite_eq_left h, ite_eq_left h]
    rfl
  · rw [frobPowQ, ite_eq_right h, ite_eq_right h, frobQ_mk]

theorem sigmaAct_one (P : Submodule F4 V6) : sigmaAct P 1 = P := by
  change subBarPow 0 (quotMul P ((1 : SUh) : SUh ⧸ Zh)) = P
  rw [subBarPow_zero, quotMul_mk, Subgroup.coe_one, Units.val_one, subMul_one]

theorem sigmaAct_mul (P : Submodule F4 V6) (x y : SigmaU6) :
    sigmaAct P (x * y) = sigmaAct (sigmaAct P x) y := by
  obtain ⟨xl, xr⟩ := x
  obtain ⟨yl, yr⟩ := y
  induction xl using QuotientGroup.induction_on with
  | H g =>
    induction yl using QuotientGroup.induction_on with
    | H h =>
      induction xr using Multiplicative.rec with
      | ofAdd a =>
        induction yr using Multiplicative.rec with
        | ofAdd b =>
          change subBarPow (a + b) (quotMul P ((g : SUh ⧸ Zh) * frobPowQ a (h : SUh ⧸ Zh))) =
            subBarPow b (quotMul (subBarPow a (quotMul P (g : SUh ⧸ Zh))) (h : SUh ⧸ Zh))
          rw [frobPowQ_mk, ← QuotientGroup.mk_mul, quotMul_mk, quotMul_mk, quotMul_mk,
            subBarPow_add, Subgroup.coe_mul, Units.val_mul, ← subMul_mul, subBarPow_subMul]
          congr 2
          by_cases ha : a = 0
          · rw [ite_eq_left ha, ite_eq_left ha]
          · rw [ite_eq_right ha, ite_eq_right ha, coe_frobSU, coe_frobGL, barM_barM]

theorem hU_sum_left (f : Fin 3 → V6) (t : V6) : hU (∑ a, f a) t = ∑ a, hU (f a) t :=
  map_sum (AddMonoidHom.mk' (fun s => hU s t) fun a b => hU_add_left a b t) f Finset.univ

theorem hU_sum_right (s : V6) (f : Fin 3 → V6) : hU s (∑ b, f b) = ∑ b, hU s (f b) :=
  map_sum (AddMonoidHom.mk' (fun t => hU s t) fun a b => hU_add_right s a b) f Finset.univ

theorem hU_sum_sum (c d : Fin 3 → F4) (v : Fin 3 → V6) :
    hU (∑ a, c a • v a) (∑ b, d b • v b) = ∑ a, ∑ b, c a * bar (d b) * hU (v a) (v b) := by
  rw [hU_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hU_smul_left, hU_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hU_smul_right]
  ring

theorem mem_plane_row (j : Fin 891) (a : Fin 3) : planeRow j a ∈ plane j :=
  Submodule.subset_span ⟨a, rfl⟩

theorem plane_coord_eq {j : Fin 891} {t t' : Fin 6} (h : ∀ a, planeRow j a t = planeRow j a t')
    {x : V6} (hx : x ∈ plane j) : x t = x t' := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h]

theorem plane_coord_zero {j : Fin 891} {t : Fin 6} (h : ∀ a, planeRow j a t = 0)
    {x : V6} (hx : x ∈ plane j) : x t = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F4).1 hx
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h, mul_zero, Finset.sum_const_zero]

theorem subBar_span (S : Set V6) :
    subBar (Submodule.span F4 S) = Submodule.span F4 (barV '' S) := by
  rw [subBar, Submodule.map_span]
  rfl

theorem subMul_span (S : Set V6) (A : Matrix (Fin 6) (Fin 6) F4) :
    subMul (Submodule.span F4 S) A = Submodule.span F4 ((· ᵥ* A) '' S) := by
  rw [subMul, Submodule.map_span]
  rfl

theorem subBarPow_span (ε : ZMod 2) (S : Set V6) :
    subBarPow ε (Submodule.span F4 S) = Submodule.span F4 (barPowV ε '' S) := by
  by_cases h : ε = 0
  · rw [subBarPow, ite_eq_left h]
    congr 1
    ext x
    simp [barPowV, h]
  · rw [subBarPow, ite_eq_right h, subBar_span]
    congr 1
    ext x
    simp [barPowV, h]

@[expose] def barPowM (ε : ZMod 2) (A : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  if ε = 0 then A else barM A

@[expose] def b6N (k : Fin 17) : Matrix (Fin 6) (Fin 6) F4 := barPowM (b6Frob k) (b6Mat k)

theorem b6Frob_eq : ∀ k : Fin 17, b6Frob k = if (k : ℕ) = 5 then 1 else 0 := by decide +kernel

theorem linearIndependent_barPowV {v : Fin 3 → V6} (hv : LinearIndependent F4 v) (ε : ZMod 2) :
    LinearIndependent F4 fun a => barPowV ε (v a) := by
  by_cases h : ε = 0
  · simpa [barPowV, h] using hv
  · simp only [barPowV, h, ite_false]
    rw [Fintype.linearIndependent_iff] at hv ⊢
    intro g hg a
    have h1 : ∑ b, bar (g b) • v b = 0 := by
      have := congrArg barV hg
      rw [barV_zero] at this
      rw [← this]
      funext t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, barV, bar_sum', bar_mul, bar_bar]
    have := hv _ h1 a
    exact (bar_eq_zero_iff).1 this

theorem linearIndependent_vecMul {v : Fin 3 → V6} (hv : LinearIndependent F4 v)
    {A : Matrix (Fin 6) (Fin 6) F4} (hA : A.det ≠ 0) :
    LinearIndependent F4 fun a => v a ᵥ* A := by
  have hinj : Function.Injective fun x : V6 => x ᵥ* A :=
    vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA))
  exact hv.map' (vecMulLinear A) (LinearMap.ker_eq_bot.2 hinj)

theorem coord_planes_stable : ∀ j ∈ ([0, 6, 5, 54, 4, 50, 49, 304, 97, 98, 110] : List (Fin 891)),
    ∀ a, barV (planeRow j a) = planeRow j a := by decide +kernel

theorem subBar_plane_of {j : Fin 891} (h : ∀ a, barV (planeRow j a) = planeRow j a) :
    subBar (plane j) = plane j := by
  rw [plane, subBar_span, ← Set.range_comp]
  congr 2
  funext a
  exact h a

@[expose] def coordPlane (i t : Fin 6) : Fin 891 :=
  if i = 0 then (if t = 3 then 0 else if t = 1 ∨ t = 2 then 54 else 0) else
  if i = 1 then (if t = 4 then 0 else if t = 0 ∨ t = 2 then 50 else 0) else
  if i = 2 then (if t = 5 then 0 else if t = 0 ∨ t = 1 then 49 else 0) else
  if i = 3 then (if t = 0 then 4 else if t = 4 ∨ t = 5 then 4 else 304) else
  if i = 4 then (if t = 1 then 5 else if t = 3 ∨ t = 5 then 5 else 304) else
  (if t = 2 then 6 else if t = 3 ∨ t = 4 then 6 else 304)

theorem coordPlane_ok : ∀ i t : Fin 6, i ≠ t →
    (∃ a, planeRow (coordPlane i t) a = Pi.single i 1) ∧
    (∀ a, planeRow (coordPlane i t) a t = 0) ∧
    (∀ a, barV (planeRow (coordPlane i t) a) = planeRow (coordPlane i t) a) := by
  decide +kernel

theorem planeRow_97 : planeRow 97 0 = Pi.single 0 1 + Pi.single 3 1 ∧
    planeRow 97 1 = Pi.single 1 1 + Pi.single 4 1 ∧
    planeRow 97 2 = Pi.single 2 1 + Pi.single 5 1 := by decide +kernel

theorem planeRow_98 : planeRow 98 0 = Pi.single 0 1 + Pi.single 4 1 := by decide +kernel

theorem planeRow_110 : planeRow 110 0 = Pi.single 0 1 + Pi.single 5 1 := by decide +kernel

theorem rows_97 : (∀ a, planeRow 97 a 3 = planeRow 97 a 0) ∧
    (∀ a, planeRow 97 a 4 = planeRow 97 a 1) ∧ (∀ a, planeRow 97 a 5 = planeRow 97 a 2) := by
  decide +kernel

theorem rows_98 : ∀ a, planeRow 98 a 4 = planeRow 98 a 0 := by decide +kernel

theorem rows_110 : ∀ a, planeRow 110 a 5 = planeRow 110 a 0 := by decide +kernel

theorem frob_moves_8 : expand 8 (barV (planeRow 8 0)) ≠ barV (planeRow 8 0) := by decide +kernel

theorem single_vecMul (i : Fin 6) (N : Matrix (Fin 6) (Fin 6) F4) (t : Fin 6) :
    (Pi.single i 1 ᵥ* N) t = N i t := by
  rw [single_one_vecMul]
  rfl

end CFSG.Monster.B.TwoA.Unitary
