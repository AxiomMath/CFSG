module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fin.Tuple.Basic

public section

namespace CFSG.Quasithin.Fan86

namespace PresP1

@[expose] def gx : Fin 13 := 0

@[expose] def gw : Fin 13 := 1

@[expose] def gy (j : Fin 5) : Fin 13 := ⟨2 + j.val, by omega⟩

@[expose] def gz (j : Fin 5) : Fin 13 := ⟨7 + j.val, by omega⟩

@[expose] def gza : Fin 13 := 12

@[expose] def X : FreeGroup (Fin 13) := FreeGroup.of gx

@[expose] def W : FreeGroup (Fin 13) := FreeGroup.of gw

@[expose] def Y (j : Fin 5) : FreeGroup (Fin 13) := FreeGroup.of (gy j)

@[expose] def Z (j : Fin 5) : FreeGroup (Fin 13) := FreeGroup.of (gz j)

@[expose] def ZA : FreeGroup (Fin 13) := FreeGroup.of gza

@[expose] def rels : List (FreeGroup (Fin 13)) :=
  [X ^ 5, W ^ 4, ZA ^ 2, W⁻¹ * X * W * (X ^ 2)⁻¹, fcomm X ZA, fcomm W ZA,
    Y 0 * Y 1 * Y 2 * Y 3 * Y 4, Z 0 * Z 1 * Z 2 * Z 3 * Z 4] ++
  ((List.finRange 5).flatMap fun j =>
    [Y j ^ 2, Z j ^ 2, X⁻¹ * Y j * X * (Y (j + 1))⁻¹, X⁻¹ * Z j * X * (Z (j + 1))⁻¹,
      W⁻¹ * Y j * W * (Y (tauLab j))⁻¹, W⁻¹ * Z j * W * (Z (tauLab j))⁻¹, fcomm (Y j) ZA,
      fcomm (Z j) ZA]) ++
  ((List.finRange 5).flatMap fun k => (List.finRange 5).flatMap fun l =>
    [fcomm (Z k) (Z l), fcomm (Y k) (Z l) * (if k = l then 1 else ZA)⁻¹] ++
    (if k = l then [] else [fcomm (Y k) (Y l) * (Z (kstar k l) * Z (kstar l k))⁻¹]))

@[expose] def gen {H : Type*} (x w za : H) (y z : Fin 5 → H) : Fin 13 → H := fun i =>
  if i.val = 0 then x else if i.val = 1 then w else
  if h : i.val < 7 then y ⟨i.val - 2, by omega⟩ else
  if h : i.val < 12 then z ⟨i.val - 7, by omega⟩ else za

section Gen

variable {H : Type*} {x w za : H} {y z : Fin 5 → H}

@[simp] theorem gen_x : gen x w za y z gx = x := by simp [gen, gx]

@[simp] theorem gen_w : gen x w za y z gw = w := by simp [gen, gw]

@[simp] theorem gen_za : gen x w za y z gza = za := by simp [gen, gza]

@[simp] theorem gen_y (j : Fin 5) : gen x w za y z (gy j) = y j := by
  have hj := j.2
  have h1 : ¬ (gy j).val = 0 := by simp only [gy]; omega
  have h2 : ¬ (gy j).val = 1 := by simp only [gy]; omega
  have h3 : (gy j).val < 7 := by simp only [gy]; omega
  simp only [gen, h1, h2, h3, ite_false, dite_true]
  congr 1
  exact Fin.ext (by simp only [gy]; omega)

@[simp] theorem gen_z (j : Fin 5) : gen x w za y z (gz j) = z j := by
  have hj := j.2
  have h1 : ¬ (gz j).val = 0 := by simp only [gz]; omega
  have h2 : ¬ (gz j).val = 1 := by simp only [gz]; omega
  have h3 : ¬ (gz j).val < 7 := by simp only [gz]; omega
  have h4 : (gz j).val < 12 := by simp only [gz]; omega
  simp only [gen, h1, h2, h3, h4, ite_false, dite_true, dite_false]
  congr 1
  exact Fin.ext (by simp only [gz]; omega)

end Gen

variable {H : Type*} [Group H] {x w za : H} {y z : Fin 5 → H}

theorem lift_rels (h : P1Rel x w za y z) :
    ∀ r ∈ rels, FreeGroup.lift (gen x w za y z) r = 1 := by
  simp only [rels, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_flatMap,
    List.mem_finRange, true_implies, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun j => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩,
    fun k l => ⟨⟨?_, ?_⟩, ?_⟩⟩
  · simpa [X, map_pow] using h.x5
  · simpa [W, map_pow] using h.w4
  · simpa [ZA, map_pow] using h.za2
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, X, W, gen_x, gen_w]
    exact mul_inv_eq_one.2 h.xw
  · simpa [X, ZA, fcomm] using h.cent_x
  · simpa [W, ZA, fcomm] using h.cent_w
  · simpa [Y, prodFive] using h.prod_y
  · simpa [Z, prodFive] using h.prod_z
  · simpa [Y, map_pow] using h.y2 j
  · simpa [Z, map_pow] using h.z2 j
  · simpa [X, Y, mul_inv_eq_one] using h.xy j
  · simpa [X, Z, mul_inv_eq_one] using h.xz j
  · simpa [W, Y, mul_inv_eq_one] using h.wy j
  · simpa [W, Z, mul_inv_eq_one] using h.wz j
  · simpa [Y, ZA, fcomm] using h.cent_y j
  · simpa [Z, ZA, fcomm] using h.cent_z j
  · simpa [Z, fcomm] using h.zz k l
  · by_cases hkl : k = l
    · subst hkl
      simpa [Y, Z, fcomm] using h.yz k k
    · have := h.yz k l
      simp only [hkl, ite_false] at this
      simpa [Y, Z, ZA, fcomm, hkl, mul_inv_eq_one] using this
  · intro r hr
    by_cases hkl : k = l
    · simp [hkl] at hr
    · simp only [hkl, ite_false, List.mem_singleton] at hr
      subst hr
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, Y, Z, fcomm, gen_y, gen_z]
      exact mul_inv_eq_one.2 (h.yy k l hkl)

@[expose] def relsOld : List (FreeGroup (Fin 14)) := rels.map (FreeGroup.map Fin.castSucc)

@[expose] def gc : Fin 14 := Fin.last 13

@[expose] def relsC : List (FreeGroup (Fin 14)) :=
  relsOld ++
    [FreeGroup.of gc ^ 2 * (FreeGroup.of (Fin.castSucc gza))⁻¹,
      fcomm (FreeGroup.of (Fin.castSucc gx)) (FreeGroup.of gc),
      fcomm (FreeGroup.of gc) (FreeGroup.of (Fin.castSucc gza)),
      fcomm (FreeGroup.of (Fin.castSucc gw)) (FreeGroup.of gc)] ++
  ((List.finRange 5).flatMap fun j =>
    [fcomm (FreeGroup.of (Fin.castSucc (gy j))) (FreeGroup.of gc) *
        (FreeGroup.of (Fin.castSucc (gz j)))⁻¹,
      fcomm (FreeGroup.of (Fin.castSucc (gz j))) (FreeGroup.of gc)])

@[expose] def genC (x w za c : H) (y z : Fin 5 → H) : Fin 14 → H :=
  Fin.snoc (α := fun _ => H) (gen x w za y z) c

omit [Group H] in
@[simp] theorem genC_gc {c : H} : genC x w za c y z gc = c := Fin.snoc_last _ _

omit [Group H] in
@[simp] theorem genC_castSucc {c : H} (i : Fin 13) :
    genC x w za c y z (Fin.castSucc i) = gen x w za y z i := Fin.snoc_castSucc _ _ _

theorem lift_map_castSucc (e : Fin 14 → H) (r : FreeGroup (Fin 13)) :
    FreeGroup.lift e (FreeGroup.map Fin.castSucc r) = FreeGroup.lift (e ∘ Fin.castSucc) r := by
  have : (FreeGroup.lift e).comp (FreeGroup.map Fin.castSucc) =
      FreeGroup.lift (e ∘ Fin.castSucc) :=
    FreeGroup.ext_hom _ _ fun i => by simp
  exact congrArg (fun f => f r) this

theorem lift_relsC {c : H} (h : P1Rel x w za y z) (hc : P1cRel x za c y z)
    (hwc : fcomm w c = 1) : ∀ r ∈ relsC, FreeGroup.lift (genC x w za c y z) r = 1 := by
  have hcast : genC x w za c y z ∘ Fin.castSucc = gen x w za y z := by
    funext i; simp
  simp only [relsC, relsOld, List.forall_mem_append, List.forall_mem_cons,
    List.forall_mem_flatMap, List.mem_finRange, true_implies, List.not_mem_nil, false_implies,
    implies_true, and_true, List.forall_mem_map, lift_map_castSucc, hcast]
  refine ⟨⟨lift_rels h, ?_, ?_, ?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_za]
    exact mul_inv_eq_one.2 hc.c2
  · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_x,
      fcomm] using hc.xc
  · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_za,
      fcomm] using hc.cza
  · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_w,
      fcomm] using hwc
  · simp only [map_mul, map_inv, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_y, gen_z,
      fcomm]
    exact mul_inv_eq_one.2 (hc.yc j)
  · simpa only [map_mul, map_inv, FreeGroup.lift_apply_of, genC_gc, genC_castSucc, gen_z,
      fcomm] using hc.zc j

end PresP1

end CFSG.Quasithin.Fan86
