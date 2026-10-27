module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemL43Mat

public section

namespace CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43

open Matrix CFSG.RankThree.PartTwo.Sec4.Item434RemL43
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem val_mul_comm_of_mem_centralizer {M X : SL4}
    (hX : X ∈ Subgroup.centralizer ({M} : Set SL4)) :
    (X : Mat4) * (M : Mat4) = (M : Mat4) * (X : Mat4) :=
  congrArg (fun Y : SL4 => (Y : Mat4)) (Subgroup.mem_centralizer_singleton_iff.mp hX)

theorem mem_centralizer_of_val_mul_comm {M X : SL4}
    (h : (X : Mat4) * (M : Mat4) = (M : Mat4) * (X : Mat4)) :
    X ∈ Subgroup.centralizer ({M} : Set SL4) :=
  Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext h)

theorem card_centralizer_of_param {P : Type*} (M : SL4) (φ : P → Mat4) (read : Mat4 → P)
    (h1 : ∀ p, φ p * (M : Mat4) = (M : Mat4) * φ p)
    (h2 : ∀ X : Mat4, X * (M : Mat4) = (M : Mat4) * X → φ (read X) = X)
    (h3 : ∀ p, read (φ p) = p) :
    Nat.card (Subgroup.centralizer ({M} : Set SL4)) = Nat.card {p : P // (φ p).det = 1} := by
  refine Nat.card_congr
    { toFun := fun X => ⟨read ((X : SL4) : Mat4), by
        rw [h2 _ (val_mul_comm_of_mem_centralizer X.2)]; exact (X : SL4).2⟩
      invFun := fun p => ⟨⟨φ p.1, p.2⟩, mem_centralizer_of_val_mul_comm (h1 p.1)⟩
      left_inv := fun X => Subtype.ext (Subtype.ext (h2 _ (val_mul_comm_of_mem_centralizer X.2)))
      right_inv := fun p => Subtype.ext (h3 p.1) }

theorem card_subtype_fst {Q R : Type*} (f : Q → ZMod 3) :
    Nat.card {p : Q × R // f p.1 = 1} = Nat.card {q : Q // f q = 1} * Nat.card R := by
  rw [Nat.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (p := fun q => f q = 1)),
    Nat.card_prod]

theorem card_subtype_congr {P : Type*} {f g : P → ZMod 3} (h : ∀ p, f p = g p) :
    Nat.card {p : P // f p = 1} = Nat.card {p : P // g p = 1} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun p => by rw [h p])

theorem card_subtype_eq_filter {P : Type*} [Fintype P] (f : P → ZMod 3) :
    Nat.card {p : P // f p = 1} = (Finset.univ.filter fun p => f p = 1).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem card_centralizer_conj {M M' : SL4} {g h : Mat4} (hgh : g * h = 1)
    (hM : g * (M : Mat4) = (M' : Mat4) * g) :
    Nat.card (Subgroup.centralizer ({M} : Set SL4)) =
      Nat.card (Subgroup.centralizer ({M'} : Set SL4)) := by
  have hhg : h * g = 1 := mul_eq_one_comm.mp hgh
  have hdet : g.det * h.det = 1 := by rw [← Matrix.det_mul, hgh, Matrix.det_one]
  have hM' : (M' : Mat4) = g * M * h := by
    calc (M' : Mat4) = M' * (g * h) := by rw [hgh, Matrix.mul_one]
      _ = g * M * h := by rw [← Matrix.mul_assoc, ← hM]
  have hMh : (M : Mat4) * h = h * M' := by
    rw [hM', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hhg, Matrix.one_mul]
  have hF : ∀ X : SL4, (g * X * h).det = 1 := fun X => by
    rw [Matrix.det_mul, Matrix.det_mul, X.2, mul_one, hdet]
  have hG : ∀ Y : SL4, (h * Y * g).det = 1 := fun Y => by
    rw [Matrix.det_mul, Matrix.det_mul, Y.2, mul_one, mul_comm, hdet]
  refine Nat.card_congr
    { toFun := fun X => ⟨⟨g * (X : SL4) * h, hF X⟩, mem_centralizer_of_val_mul_comm ?_⟩
      invFun := fun Y => ⟨⟨h * (Y : SL4) * g, hG Y⟩, mem_centralizer_of_val_mul_comm ?_⟩
      left_inv := fun X => ?_
      right_inv := fun Y => ?_ }
  · have hX := val_mul_comm_of_mem_centralizer X.2
    change g * (X : SL4) * h * (M' : Mat4) = (M' : Mat4) * (g * (X : SL4) * h)
    calc g * (X : SL4) * h * (M' : Mat4) = g * ((X : SL4) * (h * M')) := by
          simp only [Matrix.mul_assoc]
      _ = g * ((X : Mat4) * M * h) := by rw [← hMh, Matrix.mul_assoc]
      _ = g * (M * X * h) := by rw [hX]
      _ = (g * M) * X * h := by simp only [Matrix.mul_assoc]
      _ = (M' : Mat4) * (g * (X : SL4) * h) := by rw [hM]; simp only [Matrix.mul_assoc]
  · have hY := val_mul_comm_of_mem_centralizer Y.2
    change h * (Y : SL4) * g * (M : Mat4) = (M : Mat4) * (h * (Y : SL4) * g)
    calc h * (Y : SL4) * g * (M : Mat4) = h * ((Y : Mat4) * (g * M)) := by
          simp only [Matrix.mul_assoc]
      _ = h * ((Y : Mat4) * M' * g) := by rw [hM, Matrix.mul_assoc]
      _ = h * (M' * Y * g) := by rw [hY]
      _ = (h * M') * Y * g := by simp only [Matrix.mul_assoc]
      _ = (M : Mat4) * (h * (Y : SL4) * g) := by rw [← hMh]; simp only [Matrix.mul_assoc]
  · refine Subtype.ext (Subtype.ext ?_)
    change h * (g * (X : SL4) * h) * g = (X : Mat4)
    calc h * (g * (X : SL4) * h) * g = (h * g) * X * (h * g) := by simp only [Matrix.mul_assoc]
      _ = (X : Mat4) := by rw [hhg, Matrix.one_mul, Matrix.mul_one]
  · refine Subtype.ext (Subtype.ext ?_)
    change g * (h * (Y : SL4) * g) * h = (Y : Mat4)
    calc g * (h * (Y : SL4) * g) * h = (g * h) * Y * (g * h) := by simp only [Matrix.mul_assoc]
      _ = (Y : Mat4) := by rw [hgh, Matrix.one_mul, Matrix.mul_one]

abbrev F5 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

abbrev F4 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

abbrev F2 : Type := ZMod 3 × ZMod 3

abbrev F8 : Type := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

@[expose] def zSL : SL4 := ⟨zMat, det_rMat 0 1 0 0⟩

@[expose] def zShape : F5 × F5 → Mat4
  | ((α, b, c, d, e), (p, q, r, s, t)) => !![α, p, q, r; 0, b, c, s; 0, d, e, t; 0, 0, 0, α]

@[expose] def zRead (X : Mat4) : F5 × F5 :=
  ((X 0 0, X 1 1, X 1 2, X 2 1, X 2 2), (X 0 1, X 0 2, X 0 3, X 1 3, X 2 3))

theorem zShape_comm (p : F5 × F5) : zShape p * zMat = zMat * zShape p := by
  obtain ⟨⟨α, b, c, d, e⟩, ⟨p, q, r, s, t⟩⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zShape, zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four]
  ring

theorem zShape_zRead {X : Mat4} (h : X * zMat = zMat * X) : zShape (zRead X) = X := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e13 := congrFun (congrFun h 1) 3
  have e23 := congrFun (congrFun h 2) 3
  simp [zMat, rMat, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03 e13 e23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [zShape, zRead]
  · exact e13.symm
  · exact e23.symm
  · exact e00.symm
  · exact e01.symm
  · exact e02.symm
  · linear_combination e03

theorem zRead_zShape (p : F5 × F5) : zRead (zShape p) = p := by
  obtain ⟨⟨α, b, c, d, e⟩, ⟨p, q, r, s, t⟩⟩ := p
  rfl

theorem det_zShape (p : F5 × F5) :
    (zShape p).det = p.1.1 ^ 2 * (p.1.2.1 * p.1.2.2.2.2 - p.1.2.2.1 * p.1.2.2.2.1) := by
  obtain ⟨⟨α, b, c, d, e⟩, ⟨p, q, r, s, t⟩⟩ := p
  simp [zShape, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem card_zDet : Nat.card {q : F5 // q.1 ^ 2 * (q.2.1 * q.2.2.2.2 - q.2.2.1 * q.2.2.2.1) = 1} =
    48 := by
  rw [card_subtype_eq_filter]
  decide +kernel

theorem card_centralizer_zSL : Nat.card (Subgroup.centralizer ({zSL} : Set SL4)) = 11664 := by
  rw [card_centralizer_of_param zSL zShape zRead zShape_comm (fun X h => zShape_zRead h)
    zRead_zShape, card_subtype_congr det_zShape,
    card_subtype_fst (fun q : F5 => q.1 ^ 2 * (q.2.1 * q.2.2.2.2 - q.2.2.1 * q.2.2.2.1)),
    card_zDet]
  simp only [Nat.card_prod, Nat.card_zmod]

@[expose] def u2SL : SL4 := ⟨rMat 1 0 0 1, det_rMat 1 0 0 1⟩

@[expose] def u2Shape : F4 × F4 → Mat4
  | ((a₀, a₁, a₂, a₃), (b₀, b₁, b₂, b₃)) =>
    !![a₀, a₁, b₀, b₁; a₂, a₃, b₂, b₃; 0, 0, a₀, a₁; 0, 0, a₂, a₃]

@[expose] def u2Read (X : Mat4) : F4 × F4 :=
  ((X 0 0, X 0 1, X 1 0, X 1 1), (X 0 2, X 0 3, X 1 2, X 1 3))

theorem u2Shape_comm (p : F4 × F4) : u2Shape p * rMat 1 0 0 1 = rMat 1 0 0 1 * u2Shape p := by
  obtain ⟨⟨a₀, a₁, a₂, a₃⟩, ⟨b₀, b₁, b₂, b₃⟩⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u2Shape, rMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem u2Shape_u2Read {X : Mat4} (h : X * rMat 1 0 0 1 = rMat 1 0 0 1 * X) :
    u2Shape (u2Read X) = X := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  have e12 := congrFun (congrFun h 1) 2
  have e13 := congrFun (congrFun h 1) 3
  simp [rMat, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03 e10 e11 e12 e13
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u2Shape, u2Read]
  · exact e00.symm
  · exact e01.symm
  · linear_combination e02
  · linear_combination e03
  · exact e10.symm
  · exact e11.symm
  · linear_combination e12
  · linear_combination e13

theorem u2Read_u2Shape (p : F4 × F4) : u2Read (u2Shape p) = p := by
  obtain ⟨⟨a₀, a₁, a₂, a₃⟩, ⟨b₀, b₁, b₂, b₃⟩⟩ := p
  rfl

theorem det_u2Shape (p : F4 × F4) :
    (u2Shape p).det = (p.1.1 * p.1.2.2.2 - p.1.2.1 * p.1.2.2.1) ^ 2 := by
  obtain ⟨⟨a₀, a₁, a₂, a₃⟩, ⟨b₀, b₁, b₂, b₃⟩⟩ := p
  simp [u2Shape, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem card_u2Det : Nat.card {q : F4 // (q.1 * q.2.2.2 - q.2.1 * q.2.2.1) ^ 2 = 1} = 48 := by
  rw [card_subtype_eq_filter]
  decide +kernel

theorem card_centralizer_u2SL : Nat.card (Subgroup.centralizer ({u2SL} : Set SL4)) = 3888 := by
  rw [card_centralizer_of_param u2SL u2Shape u2Read u2Shape_comm (fun X h => u2Shape_u2Read h)
    u2Read_u2Shape, card_subtype_congr det_u2Shape,
    card_subtype_fst (fun q : F4 => (q.1 * q.2.2.2 - q.2.1 * q.2.2.1) ^ 2), card_u2Det]
  simp only [Nat.card_prod, Nat.card_zmod]

theorem det_one_add_nZero : (1 + nZero : Mat4).det = 1 := by decide

@[expose] def u3SL : SL4 := ⟨1 + nZero, det_one_add_nZero⟩

@[expose] def u3Shape : F2 × F4 → Mat4
  | ((α, μ), (β, γ, δ, ε)) => cMat α β γ δ ε μ

@[expose] def u3Read (X : Mat4) : F2 × F4 := ((X 0 0, X 3 3), (X 0 1, X 0 2, X 0 3, X 3 2))

theorem u3Shape_comm (p : F2 × F4) : u3Shape p * (1 + nZero) = (1 + nZero) * u3Shape p := by
  obtain ⟨⟨α, μ⟩, ⟨β, γ, δ, ε⟩⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u3Shape, cMat, nZero, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring

theorem u3Shape_u3Read {X : Mat4} (h : X * (1 + nZero) = (1 + nZero) * X) :
    u3Shape (u3Read X) = X :=
  (eq_cMat_of_comm h).symm

theorem u3Read_u3Shape (p : F2 × F4) : u3Read (u3Shape p) = p := by
  obtain ⟨⟨α, μ⟩, ⟨β, γ, δ, ε⟩⟩ := p
  rfl

theorem det_cMat (α β γ δ ε μ : ZMod 3) : (cMat α β γ δ ε μ).det = α * α * α * μ := by
  rw [Matrix.det_succ_column_zero]
  simp [cMat, Fin.sum_univ_succ, Fin.succAbove, Matrix.det_succ_column_zero]
  ring

theorem det_u3Shape (p : F2 × F4) : (u3Shape p).det = p.1.1 ^ 3 * p.1.2 := by
  obtain ⟨⟨α, μ⟩, ⟨β, γ, δ, ε⟩⟩ := p
  rw [show u3Shape ((α, μ), (β, γ, δ, ε)) = cMat α β γ δ ε μ from rfl, det_cMat]
  ring

theorem card_u3Det : Nat.card {q : F2 // q.1 ^ 3 * q.2 = 1} = 2 := by
  rw [card_subtype_eq_filter]
  decide +kernel

theorem card_centralizer_u3SL : Nat.card (Subgroup.centralizer ({u3SL} : Set SL4)) = 162 := by
  rw [card_centralizer_of_param u3SL u3Shape u3Read u3Shape_comm (fun X h => u3Shape_u3Read h)
    u3Read_u3Shape, card_subtype_congr det_u3Shape,
    card_subtype_fst (fun q : F2 => q.1 ^ 3 * q.2), card_u3Det]
  simp only [Nat.card_prod, Nat.card_zmod]

@[expose] def dMat : Mat4 := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 2]

theorem det_dMat : dMat.det = 1 := by decide

@[expose] def dSL : SL4 := ⟨dMat, det_dMat⟩

@[expose] def dShape : F8 → Mat4
  | (a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃) =>
    !![a₀, a₁, 0, 0; a₂, a₃, 0, 0; 0, 0, b₀, b₁; 0, 0, b₂, b₃]

@[expose] def dRead (X : Mat4) : F8 :=
  (X 0 0, X 0 1, X 1 0, X 1 1, X 2 2, X 2 3, X 3 2, X 3 3)

theorem dShape_comm (p : F8) : dShape p * dMat = dMat * dShape p := by
  obtain ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dShape, dMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem dShape_dRead {X : Mat4} (h : X * dMat = dMat * X) : dShape (dRead X) = X := by
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e12 := congrFun (congrFun h 1) 2
  have e13 := congrFun (congrFun h 1) 3
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e30 := congrFun (congrFun h 3) 0
  have e31 := congrFun (congrFun h 3) 1
  simp [dMat, Matrix.mul_apply, Fin.sum_univ_four] at e02 e03 e12 e13 e20 e21 e30 e31
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dShape, dRead]
  · linear_combination -e02
  · linear_combination -e03
  · linear_combination -e12
  · linear_combination -e13
  · linear_combination e20
  · linear_combination e21
  · linear_combination e30
  · linear_combination e31

theorem dRead_dShape (p : F8) : dRead (dShape p) = p := by
  obtain ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃⟩ := p
  rfl

theorem det_dShape (p : F8) : (dShape p).det =
    (p.1 * p.2.2.2.1 - p.2.1 * p.2.2.1) * (p.2.2.2.2.1 * p.2.2.2.2.2.2.2 -
      p.2.2.2.2.2.1 * p.2.2.2.2.2.2.1) := by
  obtain ⟨a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃⟩ := p
  simp [dShape, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem card_centralizer_dSL : Nat.card (Subgroup.centralizer ({dSL} : Set SL4)) = 1152 := by
  rw [card_centralizer_of_param dSL dShape dRead dShape_comm (fun X h => dShape_dRead h)
    dRead_dShape, card_subtype_congr det_dShape, card_subtype_eq_filter]
  decide +kernel

@[expose] def jMat : Mat4 := !![0, 2, 0, 0; 1, 0, 0, 0; 0, 0, 0, 2; 0, 0, 1, 0]

theorem det_jMat : jMat.det = 1 := by decide

@[expose] def jSL : SL4 := ⟨jMat, det_jMat⟩

@[expose] def jShape : F8 → Mat4
  | (x₁, y₁, x₂, y₂, x₃, y₃, x₄, y₄) =>
    !![x₁, 2 * y₁, x₂, 2 * y₂; y₁, x₁, y₂, x₂; x₃, 2 * y₃, x₄, 2 * y₄; y₃, x₃, y₄, x₄]

@[expose] def jRead (X : Mat4) : F8 :=
  (X 0 0, X 1 0, X 0 2, X 1 2, X 2 0, X 3 0, X 2 2, X 3 2)

theorem jShape_comm (p : F8) : jShape p * jMat = jMat * jShape p := by
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, x₄, y₄⟩ := p
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jShape, jMat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    ring

theorem eq_of_mul_two_eq {a b : ZMod 3} (h : a * 2 = 2 * b) : a = b := by
  revert a b
  decide

theorem jShape_jRead {X : Mat4} (h : X * jMat = jMat * X) : jShape (jRead X) = X := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e02 := congrFun (congrFun h 0) 2
  have e03 := congrFun (congrFun h 0) 3
  have e20 := congrFun (congrFun h 2) 0
  have e21 := congrFun (congrFun h 2) 1
  have e22 := congrFun (congrFun h 2) 2
  have e23 := congrFun (congrFun h 2) 3
  simp [jMat, Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e02 e03 e20 e21 e22 e23
  ext i j
  fin_cases i <;> fin_cases j <;> simp [jShape, jRead]
  · exact e00.symm
  · exact e02.symm
  · exact eq_of_mul_two_eq e01
  · exact eq_of_mul_two_eq e03
  · exact e20.symm
  · exact e22.symm
  · exact eq_of_mul_two_eq e21
  · exact eq_of_mul_two_eq e23

theorem jRead_jShape (p : F8) : jRead (jShape p) = p := by
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, x₄, y₄⟩ := p
  rfl

theorem det_jShape (p : F8) : (jShape p).det =
    (p.1 * p.2.2.2.2.2.2.1 + 2 * p.2.1 * p.2.2.2.2.2.2.2 - p.2.2.1 * p.2.2.2.2.1 -
        2 * p.2.2.2.1 * p.2.2.2.2.2.1) ^ 2 -
      2 * (p.1 * p.2.2.2.2.2.2.2 + p.2.1 * p.2.2.2.2.2.2.1 - p.2.2.1 * p.2.2.2.2.2.1 -
        p.2.2.2.1 * p.2.2.2.2.1) ^ 2 := by
  obtain ⟨x₁, y₁, x₂, y₂, x₃, y₃, x₄, y₄⟩ := p
  simp [jShape, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

theorem card_centralizer_jSL : Nat.card (Subgroup.centralizer ({jSL} : Set SL4)) = 2880 := by
  rw [card_centralizer_of_param jSL jShape jRead jShape_comm (fun X h => jShape_jRead h)
    jRead_jShape, card_subtype_congr det_jShape, card_subtype_eq_filter]
  decide +kernel

end CFSG.RankThree.PartTwo.Sec6.Res611Res5.L43
