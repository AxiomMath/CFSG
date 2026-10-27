module

public import CFSG.Quasithin.H13.A6Model4
public import CFSG.Permutation.FinPackCount
public import CFSG.Permutation.FinPackVec

public section

namespace CFSG.Quasithin.H13.A6.A6L76EK

open Equiv CFSG.Permutation.FinPack CFSG.Quasithin

theorem h16 : 6 ≤ 16 := by norm_num

@[expose] noncomputable def vc6 (x : P6) : ℕ := vcode (Multiplicative.toAdd x)

@[expose] def dec6 (c : ℕ) : P6 := Multiplicative.ofAdd fun i => ((rd c i : ℕ) : ZMod 2)

theorem dec6_vc6 (x : P6) : dec6 (vc6 x) = x := by
  refine Multiplicative.toAdd.injective (funext fun i => ?_)
  change ((rd (vcode (Multiplicative.toAdd x)) i : ℕ) : ZMod 2) = _
  rw [rd_vcode, ZMod.natCast_zmod_val]

theorem vc6_inj {x y : P6} (h : vc6 x = vc6 y) : x = y := by
  rw [← dec6_vc6 x, h, dec6_vc6]

theorem beq_vc6_iff {x y : P6} : Nat.beq (vc6 x) (vc6 y) = true ↔ x = y :=
  ⟨fun h => vc6_inj (Nat.eq_of_beq_eq_true h), fun h => h ▸ Nat.beq_refl _⟩

@[expose] noncomputable def nrmK (a : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) a (Nat.xor a 1118481) (Nat.beq (rd a 5) 1)

theorem vc6_nrm : ∀ y : P6, vc6 (nrm y) = nrmK (vc6 y) := by decide +kernel

theorem vc6_act_inv (τ : Perm (Fin 6)) (x : P6) :
    vc6 (act4f τ⁻¹ x) = nrmK (mulK 6 (vc6 x) (enc τ)) := by
  rw [act4f, vc6_nrm]
  exact congrArg nrmK (vcode_inv_apply h16 (Multiplicative.toAdd x) τ)

@[expose] noncomputable def in3K (a b c z : ℕ) : Bool := Nat.beq z a || Nat.beq z b || Nat.beq z c

theorem in3K_iff {x y w z : P6} :
    in3K (vc6 x) (vc6 y) (vc6 w) (vc6 z) = true ↔ z = x ∨ z = y ∨ z = w := by
  rw [in3K.eq_1, Bool.or_eq_true, Bool.or_eq_true, beq_vc6_iff, beq_vc6_iff, beq_vc6_iff, or_assoc]

@[expose] noncomputable def qS (a b c d : ℕ) : Bool :=
  in3K a b c (nrmK (mulK 6 a d)) && in3K a b c (nrmK (mulK 6 b d)) && evenK 6 d

@[expose] def W4C : List ℕ :=
  [0, 17, 257, 272, 4097, 4112, 4352, 4369, 65537, 65552, 65792, 65809, 69632, 69649, 69889, 69904]

@[expose] def Lsyn : List ℕ :=
  [73014444049, 73299656721, 1103806595089, 1104091807761, 1168231104529, 1168516317201,
    68987912449, 73299656961, 1099780063489, 1104091808001, 1168231104769, 1172542849281,
    68736254224, 73299656976, 1099528405264, 1104091808016, 1168231104784, 1172794507536,
    4563406849, 73299660801, 1099780067329, 1103806599169, 1168516321281, 1172542853121,
    4311748624, 73299660816, 1099528409104, 1103806599184, 1168516321296, 1172794511376,
    285217024, 73299661056, 1099528409344, 1099780067584, 1172542853376, 1172794511616,
    285217041, 4311748881, 4563407121, 68736258321, 68987916561, 73014448401, 4563468289,
    68987977729, 73014509569, 1104091873281, 1168516382721, 1172542914561, 4311810064,
    68736319504, 73014509584, 1104091873296, 1168516382736, 1172794572816, 285278464,
    68736319744, 68987977984, 1104091873536, 1172542914816, 1172794573056, 285278481,
    4311810321, 4563468561, 1099528470801, 1099780129041, 1103806660881, 285282304, 4311814144,
    4563472384, 1168516386816, 1172542918656, 1172794576896, 285282321, 68736323601,
    68987981841, 1099528474641, 1099780132881, 1168231174161, 4311814401, 68736323841,
    73014513921, 1099528474881, 1103806664961, 1168231174401, 4563472656, 68987982096,
    73014513936, 1099780133136, 1103806664976, 1168231174416]

@[expose] def goodC (a b : ℕ) : Bool := !Nat.beq a 0 && !Nat.beq b 0 && !Nat.beq a b

@[expose] def pairC (a b : ℕ) : ℕ := Nat.add a (Nat.shiftLeft b 24)

@[expose] noncomputable def synB : Bool :=
  allK (fun a => allK (fun b => !goodC a b ||
    (!Nat.beq (Nat.mod (cntK 6 (qS a b (Nat.xor a b)) 6 0 0 0) 8) 0 || memK (pairC a b) Lsyn))
    W4C) W4C

theorem synB_check : synB = true := by decide +kernel

theorem vc6_mem : ∀ x : P6, InW4 x → memK (vc6 x) W4C = true := by decide +kernel

@[expose] noncomputable def xorB : Bool :=
  allK (fun a => allK (fun b => Nat.beq (vc6 (dec6 a * dec6 b)) (Nat.xor a b)) W4C) W4C

theorem xorB_check : xorB = true := by decide +kernel

theorem vc6_mul {x y : P6} (hx : InW4 x) (hy : InW4 y) : vc6 (x * y) = Nat.xor (vc6 x) (vc6 y) := by
  have h := allK_iff.1 (allK_iff.1 xorB_check _ (memK_iff.1 (vc6_mem x hx))) _
    (memK_iff.1 (vc6_mem y hy))
  rw [dec6_vc6, dec6_vc6] at h
  exact Nat.eq_of_beq_eq_true h

theorem vc6_one : vc6 1 = 0 := by decide +kernel

theorem goodC_of {x y : P6} (h1 : x ≠ 1) (h2 : y ≠ 1) (h3 : x ≠ y) :
    goodC (vc6 x) (vc6 y) = true := by
  have e : ∀ {u v : P6}, u ≠ v → Nat.beq (vc6 u) (vc6 v) = false := fun h =>
    Bool.eq_false_iff.2 fun e => h (beq_vc6_iff.1 e)
  rw [goodC, ← vc6_one, e h1, e h2, e h3]
  rfl

end CFSG.Quasithin.H13.A6.A6L76EK
