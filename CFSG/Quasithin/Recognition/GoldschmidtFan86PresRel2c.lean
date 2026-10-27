module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86PresRel2b

public section

namespace CFSG.Quasithin.Fan86

namespace PresP2

@[expose] def rels913 : List (FreeGroup (Fin 14)) :=
  [XB⁻¹ * W1 * XB * W2⁻¹,
    XB⁻¹ * W2 * XB * (W1 * W2 * ZM 2 * ZM 0 * YM 2 * UB * ZA 0 ^ (0 + 0 + 1))⁻¹,
    T⁻¹ * W1 * T * (W1 * W2 * ZM 2 * ZM 1 * ZM 0 * YM 0 * UB * ZA 0 * ZA 2 ^ 0 * ZA 0 ^ 0)⁻¹,
    T⁻¹ * W2 * T * (W2 * ZM 0 * YM 0 * UB * ZA 2 * ZA 0 ^ 0)⁻¹,
    fcomm W1 W2 * (ZM 2 * ZM 1 * ZM 0 * YM 2 * ZA 0)⁻¹]

@[expose] def rels : List (FreeGroup (Fin 14)) := rels912 ++ rels913

local macro "lsimp" : tactic =>
  `(tactic| simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, gen_xb, gen_t, gen_w1,
    gen_w2, gen_ub, gen_zm, gen_ym, gen_za, fcomm, XB, T, W1, W2, UB, ZM, YM, ZA])

variable {H : Type*} [Group H] {xb t w1 w2 ub : H} {zm ym za : Fin 3 → H}

theorem lift_rels (h : P2Rel912 xb t w1 w2 ub zm ym za)
    (h' : P2Rel913 0 0 xb t w1 w2 ub zm ym za) :
    ∀ r ∈ rels, FreeGroup.lift (gen xb t w1 w2 ub zm ym za) r = 1 := by
  simp only [rels, List.forall_mem_append, rels913, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  refine ⟨lift_rels912 h, ?_, ?_, ?_, ?_, ?_⟩
  · lsimp; exact mul_inv_eq_one.2 h'.w1x
  · lsimp; exact mul_inv_eq_one.2 h'.w2x
  · lsimp; exact mul_inv_eq_one.2 h'.w1t
  · lsimp; exact mul_inv_eq_one.2 h'.w2t
  · lsimp; exact mul_inv_eq_one.2 h'.w1w2

@[expose] def gc : Fin 15 := Fin.last 14

@[expose] def C : FreeGroup (Fin 15) := FreeGroup.of gc

@[expose] def up : FreeGroup (Fin 14) →* FreeGroup (Fin 15) := FreeGroup.map Fin.castSucc

@[expose] def relsC : List (FreeGroup (Fin 15)) :=
  rels.map up ++
    [C ^ 2 * (up (ZA 0))⁻¹, fcomm C (up (ZM 1)) * (up (UB * ZA 2))⁻¹, fcomm C (up (ZM 0)),
      fcomm C (up (ZM 2)), fcomm C (up (YM 0)), fcomm C (up UB),
      fcomm C (up (YM 1)) * (up (ZA 2))⁻¹, fcomm C (up (YM 2)) * (up (ZA 2))⁻¹,
      (up XB)⁻¹ * C * up XB * (up (ZM 2 * ZM 1 * YM 2) * C * up (ZA 2) ^ (0 + 1))⁻¹,
      (up T)⁻¹ * C * up T * (C * up (ZM 0))⁻¹, fcomm (up W1) C,
      fcomm (up W2) C * (up (YM 0 * ZA 1))⁻¹] ++
  ((List.finRange 3).map fun i => fcomm C (up (ZA i)))

@[expose] def genC (xb t w1 w2 ub c : H) (zm ym za : Fin 3 → H) : Fin 15 → H :=
  Fin.snoc (α := fun _ => H) (gen xb t w1 w2 ub zm ym za) c

omit [Group H] in
@[simp] theorem genC_gc {c : H} : genC xb t w1 w2 ub c zm ym za gc = c := Fin.snoc_last _ _

omit [Group H] in
@[simp] theorem genC_castSucc {c : H} (i : Fin 14) :
    genC xb t w1 w2 ub c zm ym za (Fin.castSucc i) = gen xb t w1 w2 ub zm ym za i :=
  Fin.snoc_castSucc _ _ _

omit [Group H] in
@[simp] theorem genC_comp_castSucc {c : H} :
    genC xb t w1 w2 ub c zm ym za ∘ Fin.castSucc = gen xb t w1 w2 ub zm ym za := by
  funext i; simp

theorem lift_up (e : Fin 15 → H) (r : FreeGroup (Fin 14)) :
    FreeGroup.lift e (up r) = FreeGroup.lift (e ∘ Fin.castSucc) r := by
  have : (FreeGroup.lift e).comp up = FreeGroup.lift (e ∘ Fin.castSucc) :=
    FreeGroup.ext_hom _ _ fun i => by simp [up]
  exact congrArg (fun f => f r) this

local macro "lsimpC" : tactic =>
  `(tactic| simp only [map_mul, map_inv, map_pow, lift_up, genC_comp_castSucc,
    FreeGroup.lift_apply_of, gen_xb, gen_t, gen_w1, gen_w2, gen_ub, gen_zm, gen_ym, gen_za,
    genC_gc, fcomm, XB, T, W1, W2, UB, ZM, YM, ZA, C])

theorem lift_relsC {c : H} (h : P2Rel912 xb t w1 w2 ub zm ym za)
    (h' : P2Rel913 0 0 xb t w1 w2 ub zm ym za) (hc : P2cRel912 ub c zm ym za)
    (hc' : P2cRel913 0 xb t w1 w2 c zm ym za) :
    ∀ r ∈ relsC, FreeGroup.lift (genC xb t w1 w2 ub c zm ym za) r = 1 := by
  simp only [relsC, List.forall_mem_append, List.forall_mem_map, List.forall_mem_cons,
    List.mem_finRange, true_implies, List.not_mem_nil, false_implies, implies_true, and_true,
    lift_up, genC_comp_castSucc]
  refine ⟨⟨lift_rels h h', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, fun i => ?_⟩
  · lsimpC; exact mul_inv_eq_one.2 hc.c2
  · lsimpC; exact mul_inv_eq_one.2 hc.cz2
  · lsimpC; exact hc.cz1
  · lsimpC; exact hc.cz3
  · lsimpC; exact hc.cy1
  · lsimpC; exact hc.cub
  · lsimpC; exact mul_inv_eq_one.2 hc.cy2
  · lsimpC; exact mul_inv_eq_one.2 hc.cy3
  · lsimpC; exact mul_inv_eq_one.2 hc'.cx
  · lsimpC; exact mul_inv_eq_one.2 hc'.ct
  · lsimpC; exact hc'.w1c
  · lsimpC; exact mul_inv_eq_one.2 hc'.w2c
  · lsimpC; exact hc.cza i

end PresP2

end CFSG.Quasithin.Fan86
