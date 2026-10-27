module

public import CFSG.Quasithin.H13.L32NLem1442k
public import CFSG.Quasithin.H13.L32NO3Model
public import CFSG.Quasithin.H13.L32NG5Model

public section

namespace CFSG.Quasithin.H13.L1442

open CFSG.Fischer Matrix Mat8Cert L1442M

local instance (priority := high) decEqF4' : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

@[expose] def bitA (x : F4) : ZMod 2 := ((x.code.val % 2 : ℕ) : ZMod 2)

@[expose] def ofBits (b₀ b₁ : ZMod 2) : F4 :=
  ⟨⟨b₀.val + 2 * b₁.val, by have h₀ := ZMod.val_lt b₀; have h₁ := ZMod.val_lt b₁; omega⟩⟩

theorem bitA_add (x y : F4) : bitA (x + y) = bitA x + bitA y := by
  revert x y
  decide

theorem ofBits_bits (x : F4) : ofBits (bitA x) (trF4 x) = x := by
  revert x
  decide

theorem bitA_ofBits (b₀ b₁ : ZMod 2) : bitA (ofBits b₀ b₁) = b₀ := by
  revert b₀ b₁
  decide

theorem trF4_ofBits (b₀ b₁ : ZMod 2) : trF4 (ofBits b₀ b₁) = b₁ := by
  revert b₀ b₁
  decide

@[expose] def bitsE : Matrix (Fin 2) (Fin 2) F4 ≃+ (Fin 8 → ZMod 2) where
  toFun X := ![bitA (X 0 0), trF4 (X 0 0), bitA (X 0 1), trF4 (X 0 1), bitA (X 1 0), trF4 (X 1 0),
    bitA (X 1 1), trF4 (X 1 1)]
  invFun v := !![ofBits (v 0) (v 1), ofBits (v 2) (v 3); ofBits (v 4) (v 5), ofBits (v 6) (v 7)]
  left_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ofBits_bits]
  right_inv v := by
    funext k
    fin_cases k <;> simp [bitA_ofBits, trF4_ofBits]
  map_add' X Y := by
    funext k
    fin_cases k <;> simp [bitA_add, trF4_add]

@[expose] def bitsN (X : Matrix (Fin 2) (Fin 2) F4) : ℕ :=
  (X 0 0).code.val + 4 * (X 0 1).code.val + 16 * (X 1 0).code.val + 64 * (X 1 1).code.val

theorem bitsE_entries (a b c d : F4) : bitsE !![a, b; c, d] = vec8 (bitsN !![a, b; c, d]) := by
  revert a b c d
  decide

theorem bitsE_eq (X : Matrix (Fin 2) (Fin 2) F4) : bitsE X = vec8 (bitsN X) := by
  rw [Matrix.eta_fin_two X, bitsE_entries]

theorem bitsE_map_of {f : Matrix (Fin 2) (Fin 2) F4 → Matrix (Fin 2) (Fin 2) F4}
    {g : Matrix (Fin 8) (Fin 8) (ZMod 2)}
    (h : ∀ a b c d : F4, bitsN (f !![a, b; c, d]) = mv8 (colsOf g) (bitsN !![a, b; c, d]))
    (X : Matrix (Fin 2) (Fin 2) F4) : bitsE (f X) = g.mulVec (bitsE X) := by
  rw [bitsE_eq, bitsE_eq, mulVec_vec8, Matrix.eta_fin_two X, h]

theorem quad_bitsE_entries (a b c d : F4) :
    b2z (G5Cert.quadN (bitsN !![a, b; c, d])) =
      trF4 (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) F4).det := by
  rw [Matrix.det_fin_two_of]
  revert a b c d
  decide

theorem quad_bitsE (X : Matrix (Fin 2) (Fin 2) F4) : quadOf q3 (bitsE X) = trF4 X.det := by
  rw [bitsE_eq, O3Cert.q3_eq, ← G5Cert.quadN_spec, Matrix.eta_fin_two X, quad_bitsE_entries]

theorem cols_o3l0 :
    colsOf (o3l0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [1, 2, 4, 8, 17, 34, 68, 136] := by
  decide +kernel

theorem cols_o3l1 :
    colsOf (o3l1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [16, 32, 64, 128, 1, 2, 4, 8] := by
  decide +kernel

theorem cols_o3l2 :
    colsOf (o3l2 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [2, 3, 8, 12, 48, 16, 192, 64] := by
  decide +kernel

theorem cols_o3r0 :
    colsOf (o3r0 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [1, 2, 5, 10, 16, 32, 80, 160] := by
  decide +kernel

theorem cols_o3r1 :
    colsOf (o3r1 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [4, 8, 1, 2, 64, 128, 16, 32] := by
  decide +kernel

theorem cols_o3r2 :
    colsOf (o3r2 : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [2, 3, 12, 4, 32, 48, 192, 64] := by
  decide +kernel

theorem cols_field :
    colsOf (o3field : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [1, 3, 4, 12, 16, 48, 64, 192] := by
  decide +kernel

theorem cols_swap :
    colsOf (o3swap : Matrix (Fin 8) (Fin 8) (ZMod 2)) = [1, 2, 16, 32, 4, 8, 64, 128] := by
  decide +kernel

theorem bitsE_o3l0 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (!![1, 1; 0, 1] * X) = (o3l0 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => !![1, 1; 0, 1] * X) ?_ X
  rw [cols_o3l0]
  decide

theorem bitsE_o3l1 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (!![0, 1; 1, 0] * X) = (o3l1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => !![0, 1; 1, 0] * X) ?_ X
  rw [cols_o3l1]
  decide

theorem bitsE_o3l2 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (!![F4.ω, 0; 0, F4.ω * F4.ω] * X) =
      (o3l2 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => !![F4.ω, 0; 0, F4.ω * F4.ω] * X) ?_ X
  rw [cols_o3l2]
  decide

theorem bitsE_o3r0 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (X * !![1, 0; 1, 1]) = (o3r0 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => X * !![1, 0; 1, 1]) ?_ X
  rw [cols_o3r0]
  decide

theorem bitsE_o3r1 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (X * !![0, 1; 1, 0]) = (o3r1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => X * !![0, 1; 1, 0]) ?_ X
  rw [cols_o3r1]
  decide

theorem bitsE_o3r2 (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (X * !![F4.ω, 0; 0, F4.ω * F4.ω]) =
      (o3r2 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => X * !![F4.ω, 0; 0, F4.ω * F4.ω]) ?_ X
  rw [cols_o3r2]
  decide

theorem bitsE_field (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE (X.map fun x => x * x) =
      (o3field : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => X.map fun x => x * x) ?_ X
  rw [cols_field]
  decide

theorem bitsE_swap (X : Matrix (Fin 2) (Fin 2) F4) :
    bitsE Xᵀ = (o3swap : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (bitsE X) := by
  refine bitsE_map_of (f := fun X => Xᵀ) ?_ X
  rw [cols_swap]
  decide

end CFSG.Quasithin.H13.L1442
