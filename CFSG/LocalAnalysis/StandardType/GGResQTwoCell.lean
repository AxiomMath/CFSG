module

public import CFSG.LocalAnalysis.StandardType.GGResICellBasic
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
public import CFSG.LocalAnalysis.StandardType.GGResICertSound

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

inductive GGResQTwoResidual where
  | A3b0c1w12 | A3b0c1w21 | A3b0c2w12 | A3b0c2w21
  | A3b2c0w12 | A3b2c0w21 | A3b2c1w12 | A3b2c1w21
  | B3b0c2 | B3b2c0 | B3b2c0w12 | B3b2c0w21 | B3b2c1 | B3b2c1w12 | B3b2c1w21
  | C3b0c2 | C3b2c0 | C3b2c0w12 | C3b2c0w21 | C3b2c1 | C3b2c1w12 | C3b2c1w21
  deriving DecidableEq, Repr

@[expose] def ggResQTwoResidualUV : GGResQTwoResidual → ZMod 3 × ZMod 3
  | .A3b0c1w12 => (2, 1)
  | .A3b0c1w21 => (1, 2)
  | .A3b0c2w12 => (2, 1)
  | .A3b0c2w21 => (1, 2)
  | .A3b2c0w12 => (2, 1)
  | .A3b2c0w21 => (1, 2)
  | .A3b2c1w12 => (2, 1)
  | .A3b2c1w21 => (1, 2)
  | .B3b0c2 => (2, 1)
  | .B3b2c0 => (1, 2)
  | .B3b2c0w12 => (2, 2)
  | .B3b2c0w21 => (1, 1)
  | .B3b2c1 => (1, 2)
  | .B3b2c1w12 => (0, 0)
  | .B3b2c1w21 => (0, 0)
  | .C3b0c2 => (1, 2)
  | .C3b2c0 => (2, 1)
  | .C3b2c0w12 => (1, 1)
  | .C3b2c0w21 => (2, 2)
  | .C3b2c1 => (2, 1)
  | .C3b2c1w12 => (0, 0)
  | .C3b2c1w21 => (0, 0)

@[expose] def ggResQTwoResidualCheck (tag : GGResQTwoResidual) (u v : ZMod 3) : Bool :=
  decide (ggResQTwoResidualUV tag = (u, v))

structure GGResQTwoResidualData where
  C : Matrix (Fin 3) (Fin 3) ℤ
  ib : Fin 3
  ic : Fin 3
  e₁ : ℤ
  e₂ : ℤ
  u : ZMod 3
  v : ZMod 3

@[expose] def ggResQTwoResidualData : GGResQTwoResidual → GGResQTwoResidualData
  | .A3b0c1w12 => ⟨CartanMatrix.A 3, 0, 1, -1, -2, 2, 1⟩
  | .A3b0c1w21 => ⟨CartanMatrix.A 3, 0, 1, -2, -1, 1, 2⟩
  | .A3b0c2w12 => ⟨CartanMatrix.A 3, 0, 2, -1, -2, 2, 1⟩
  | .A3b0c2w21 => ⟨CartanMatrix.A 3, 0, 2, -2, -1, 1, 2⟩
  | .A3b2c0w12 => ⟨CartanMatrix.A 3, 2, 0, -1, -2, 2, 1⟩
  | .A3b2c0w21 => ⟨CartanMatrix.A 3, 2, 0, -2, -1, 1, 2⟩
  | .A3b2c1w12 => ⟨CartanMatrix.A 3, 2, 1, -1, -2, 2, 1⟩
  | .A3b2c1w21 => ⟨CartanMatrix.A 3, 2, 1, -2, -1, 1, 2⟩
  | .B3b0c2 => ⟨CartanMatrix.B 3, 0, 2, -1, -1, 2, 1⟩
  | .B3b2c0 => ⟨CartanMatrix.B 3, 2, 0, -1, -1, 1, 2⟩
  | .B3b2c0w12 => ⟨CartanMatrix.B 3, 2, 0, -1, -2, 2, 2⟩
  | .B3b2c0w21 => ⟨CartanMatrix.B 3, 2, 0, -2, -1, 1, 1⟩
  | .B3b2c1 => ⟨CartanMatrix.B 3, 2, 1, -1, -1, 1, 2⟩
  | .B3b2c1w12 => ⟨CartanMatrix.B 3, 2, 1, -1, -2, 0, 0⟩
  | .B3b2c1w21 => ⟨CartanMatrix.B 3, 2, 1, -2, -1, 0, 0⟩
  | .C3b0c2 => ⟨CartanMatrix.C 3, 0, 2, -1, -1, 1, 2⟩
  | .C3b2c0 => ⟨CartanMatrix.C 3, 2, 0, -1, -1, 2, 1⟩
  | .C3b2c0w12 => ⟨CartanMatrix.C 3, 2, 0, -1, -2, 1, 1⟩
  | .C3b2c0w21 => ⟨CartanMatrix.C 3, 2, 0, -2, -1, 2, 2⟩
  | .C3b2c1 => ⟨CartanMatrix.C 3, 2, 1, -1, -1, 2, 1⟩
  | .C3b2c1w12 => ⟨CartanMatrix.C 3, 2, 1, -1, -2, 0, 0⟩
  | .C3b2c1w21 => ⟨CartanMatrix.C 3, 2, 1, -2, -1, 0, 0⟩

@[expose] def GGResQTwoResidualShape (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3) : Prop :=
  match n with
  | 3 =>
      C = (ggResQTwoResidualData tag).C ∧
        ib = (ggResQTwoResidualData tag).ib ∧
        ic = (ggResQTwoResidualData tag).ic ∧
        e₁ = (ggResQTwoResidualData tag).e₁ ∧
        e₂ = (ggResQTwoResidualData tag).e₂ ∧
        u = (ggResQTwoResidualData tag).u ∧
        v = (ggResQTwoResidualData tag).v
  | _ => False

@[expose] def ggResQTwoResidualShapeCheck (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3) : Bool :=
  match n with
  | 3 =>
      decide (C = (ggResQTwoResidualData tag).C ∧
        ib = (ggResQTwoResidualData tag).ib ∧
        ic = (ggResQTwoResidualData tag).ic ∧
        e₁ = (ggResQTwoResidualData tag).e₁ ∧
        e₂ = (ggResQTwoResidualData tag).e₂ ∧
        u = (ggResQTwoResidualData tag).u ∧
        v = (ggResQTwoResidualData tag).v)
  | _ => false

theorem ggResQTwoResidualShapeCheck_spec (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3) :
    ggResQTwoResidualShapeCheck tag n C ib ic e₁ e₂ u v = true ↔
      GGResQTwoResidualShape tag n C ib ic e₁ e₂ u v := by
  unfold ggResQTwoResidualShapeCheck GGResQTwoResidualShape
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          cases n with
          | zero => simp
          | succ n =>
              cases n with
              | zero => simp
              | succ n => simp

theorem ggResQTwoResidualShape_n_eq_three (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h : GGResQTwoResidualShape tag n C ib ic e₁ e₂ u v) : n = 3 := by
  cases n with
  | zero => simp [GGResQTwoResidualShape] at h
  | succ n =>
      cases n with
      | zero => simp [GGResQTwoResidualShape] at h
      | succ n =>
          cases n with
          | zero => simp [GGResQTwoResidualShape] at h
          | succ n =>
              cases n with
              | zero => rfl
              | succ n => simp [GGResQTwoResidualShape] at h

theorem ggResQTwoResidualShape_three (tag : GGResQTwoResidual)
    (C : Matrix (Fin 3) (Fin 3) ℤ) (ib ic : Fin 3) (e₁ e₂ : ℤ) (u v : ZMod 3) :
    GGResQTwoResidualShape tag 3 C ib ic e₁ e₂ u v ↔
      C = (ggResQTwoResidualData tag).C ∧
        ib = (ggResQTwoResidualData tag).ib ∧
        ic = (ggResQTwoResidualData tag).ic ∧
        e₁ = (ggResQTwoResidualData tag).e₁ ∧
        e₂ = (ggResQTwoResidualData tag).e₂ ∧
        u = (ggResQTwoResidualData tag).u ∧
        v = (ggResQTwoResidualData tag).v :=
  Iff.rfl

theorem ggResQTwoResidualShapeCheck_n_eq_three (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h : ggResQTwoResidualShapeCheck tag n C ib ic e₁ e₂ u v = true) : n = 3 :=
  ggResQTwoResidualShape_n_eq_three tag n C ib ic e₁ e₂ u v
    ((ggResQTwoResidualShapeCheck_spec tag n C ib ic e₁ e₂ u v).mp h)

theorem ggResQTwoResidualShapeCheck_three (tag : GGResQTwoResidual)
    (C : Matrix (Fin 3) (Fin 3) ℤ) (ib ic : Fin 3) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h : ggResQTwoResidualShapeCheck tag 3 C ib ic e₁ e₂ u v = true) :
    C = (ggResQTwoResidualData tag).C ∧
      ib = (ggResQTwoResidualData tag).ib ∧
      ic = (ggResQTwoResidualData tag).ic ∧
      e₁ = (ggResQTwoResidualData tag).e₁ ∧
      e₂ = (ggResQTwoResidualData tag).e₂ ∧
      u = (ggResQTwoResidualData tag).u ∧
      v = (ggResQTwoResidualData tag).v := by
  simpa [ggResQTwoResidualShape_three] using
    (ggResQTwoResidualShapeCheck_spec tag 3 C ib ic e₁ e₂ u v).mp h

theorem ggResQTwoResidualShapeCheck_imp_residualCheck (tag : GGResQTwoResidual) (n : ℕ)
    (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ) (u v : ZMod 3)
    (h : ggResQTwoResidualShapeCheck tag n C ib ic e₁ e₂ u v = true) :
    ggResQTwoResidualCheck tag u v = true := by
  rw [ggResQTwoResidualShapeCheck_spec] at h
  have hn := ggResQTwoResidualShape_n_eq_three tag n C ib ic e₁ e₂ u v h
  subst hn
  rw [ggResQTwoResidualShape_three] at h
  obtain ⟨-, -, -, -, -, hu, hv⟩ := h
  rw [ggResQTwoResidualCheck]
  rw [hu, hv]
  cases tag <;> rfl

theorem ggResQTwoResidualShapeCheck_literal (tag : GGResQTwoResidual) :
    ggResQTwoResidualShapeCheck tag 3 (ggResQTwoResidualData tag).C
      (ggResQTwoResidualData tag).ib (ggResQTwoResidualData tag).ic
      (ggResQTwoResidualData tag).e₁ (ggResQTwoResidualData tag).e₂
      (ggResQTwoResidualData tag).u (ggResQTwoResidualData tag).v = true := by
  cases tag <;> decide +kernel

@[expose] def ggResQTwoReuseOk {n : ℕ} : GGCellWitI n → Bool
  | .tv _ _ _ _ => true
  | .tvk _ _ _ _ => true
  | .wstar _ _ _ _ _ => true
  | .std _ _ => true
  | .nospan _ _ _ _ => true
  | .o2b => true
  | _ => false

inductive GGResQTwoCell (n : ℕ) where
  | reuse (w : GGCellWitI n)
  | commonKernel (z : List ℕ)
  | norm (side : List (Fin (n + 1))) (x₀ : List ℕ)
      (R : List (Fin (n + 1) × List (Fin (n + 1)))) (τ : List (Fin (n + 1))) (k : Fin (n + 1))
  | residual (tag : GGResQTwoResidual)

@[expose] def ggResQTwoLSide (n : ℕ) : List (Fin (n + 1)) :=
  (List.finRange n).map Fin.castSucc

@[expose] def ggResQTwoKSide (n : ℕ) (ib : Fin n) : List (Fin (n + 1)) :=
  (List.finRange (n + 1)).filter (fun i => i ≠ ib.castSucc)

@[expose] def ggResQTwoCellSideOK {n : ℕ} (ib : Fin n) : GGResQTwoCell n → Prop
  | .norm side _ _ _ _ => side = ggResQTwoLSide n ∨ side = ggResQTwoKSide n ib
  | _ => True

@[expose] def ggResQTwoCellSideOKB {n : ℕ} (ib : Fin n) : GGResQTwoCell n → Bool
  | .norm side _ _ _ _ => decide (side = ggResQTwoLSide n ∨ side = ggResQTwoKSide n ib)
  | _ => true

theorem ggResQTwoCellSideOKB_iff {n : ℕ} (ib : Fin n) (w : GGResQTwoCell n) :
    ggResQTwoCellSideOKB ib w = true ↔ ggResQTwoCellSideOK ib w := by
  cases w <;> simp [ggResQTwoCellSideOKB, ggResQTwoCellSideOK]

abbrev GGResQTwoCommonKernelOK {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (z : List ℕ) : Prop :=
  (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)) ≠ 0 ∧
    z.getD (n + 1) 0 = 0 ∧
    ∀ i : Fin (n + 1), ggFDot (T i) (ggFVec z) = 0

@[expose] def ggResQTwoCommonKernelCheck {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (z : List ℕ) : Bool :=
  decide (GGResQTwoCommonKernelOK T z)

theorem ggResQTwoCommonKernelCheck_spec {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (z : List ℕ) :
    ggResQTwoCommonKernelCheck T z = true ↔ GGResQTwoCommonKernelOK T z := by
  simp [ggResQTwoCommonKernelCheck]

theorem ggResQTwo_fvec_eq_zero {p : ℕ} {n : ℕ} {z : List ℕ}
    (hcoord : ∀ l : Fin (n + 1),
      (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)).get l.castSucc = 0)
    (hlast : z.getD (n + 1) 0 = 0) :
    (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)) = 0 := by
  apply Vector.ext
  intro l hl
  by_cases hlt : l < n + 1
  · have hz0 : (0 : Vector (ZMod p) (n + 2))[l] = 0 := by simp
    rw [hz0]
    change (ggFVec z).get (⟨l, hl⟩ : Fin (n + 2)) = 0
    have hidx : (⟨l, hl⟩ : Fin (n + 2)) = Fin.castSucc ⟨l, hlt⟩ := Fin.ext rfl
    rw [hidx]
    exact hcoord ⟨l, hlt⟩
  · have hlast' : l = n + 1 := by omega
    subst hlast'
    have hz0 : (0 : Vector (ZMod p) (n + 2))[n + 1] = 0 := by simp
    rw [hz0]
    change (ggFVec z).get (⟨n + 1, hl⟩ : Fin (n + 2)) = 0
    have hidx : (⟨n + 1, hl⟩ : Fin (n + 2)) = Fin.last (n + 1) := Fin.ext rfl
    rw [hidx]
    simp only [ggFVec, Vector.get_ofFn, List.getD]
    change ((z.getD (n + 1) 0 : ℕ) : ZMod p) = 0
    rw [hlast]
    norm_num

theorem ggResQTwo_commonKernel_false {p : ℕ} [Fact p.Prime] {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {T : Fin (n + 1) → Vector (ZMod p) (n + 2)}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod p) V}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α)
    (hind : LinearIndependent (ZMod p) h)
    (hker : ∀ v : V, (∀ i : Fin (n + 1), α i v = 0) → v = 0)
    {z : List ℕ} (hcheck : ggResQTwoCommonKernelCheck T z = true) : False := by
  classical
  rcases (ggResQTwoCommonKernelCheck_spec T z).mp hcheck with ⟨hz0, hzlast, hzroot⟩
  have hπ0 : ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (R := ZMod p) z) = 0 := by
    apply hker
    intro i
    rw [ggFPi_root hT i]
    simpa using hzroot i
  have hsum : (∑ l : Fin (n + 1),
      (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)).get l.castSucc • h l) = 0 := by
    simpa [ggFPi] using hπ0
  have hcoord : ∀ l : Fin (n + 1),
      (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)).get l.castSucc = 0 := by
    intro l
    exact (Fintype.linearIndependent_iff.mp hind) _ hsum l
  exact hz0 (ggResQTwo_fvec_eq_zero hcoord hzlast)

abbrev GGResQTwoListOK {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1)))) : Prop :=
  (∀ j ∈ side, ∃ r ∈ R, ggFMat T (ggConjWord r) = ggFMat T [j]) ∧
    (∀ j ∈ side, ∀ r ∈ R, ∃ r' ∈ R,
      ggFMat T (ggConjWord r') = ggFMat T ([j] ++ ggConjWord r ++ [j])) ∧
    ∀ r ∈ R, r.1 ∈ side ∧ ∀ i ∈ r.2, i ∈ side

abbrev GGResQTwoNormOK {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1))))
    (x₀ : List ℕ) (τ : List (Fin (n + 1))) (k : Fin (n + 1)) : Prop :=
  k ∈ side ∧
    GGResQTwoListOK T side R ∧
    (ggFVec (R := ZMod p) x₀ : Vector (ZMod p) (n + 2)) ≠ 0 ∧
    x₀.getD (n + 1) 0 = 0 ∧
    (∀ i ∈ side, ggFDot (T i) (ggFVec x₀) = 0) ∧
    ggFWord T τ (ggFVec x₀) = ggFVec x₀ ∧
    ∀ r ∈ R, ggFMat T (ggConjWord (k, τ)) ≠ ggFMat T (ggConjWord r)

@[expose] def ggResQTwoNormCheck {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1))))
    (x₀ : List ℕ) (τ : List (Fin (n + 1))) (k : Fin (n + 1)) : Bool :=
  decide (GGResQTwoNormOK T side R x₀ τ k)

theorem ggResQTwoNormCheck_spec {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1))))
    (x₀ : List ℕ) (τ : List (Fin (n + 1))) (k : Fin (n + 1)) :
    ggResQTwoNormCheck T side R x₀ τ k = true ↔ GGResQTwoNormOK T side R x₀ τ k := by
  simp [ggResQTwoNormCheck]

theorem ggResQTwo_refl_mul_self {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {s : V ≃ₗ[ZMod p] V} {h : V}
    {α : Module.Dual (ZMod p) V} (hα : α h = 2) (hs : ∀ w, s w = w - α w • h) :
    s * s = 1 := by
  refine LinearEquiv.ext fun w => ?_
  rw [LinearEquiv.mul_apply, hs (s w), hs w, map_sub, map_smul, hα]
  change _ = w
  simp only [smul_eq_mul]
  module

theorem ggResQTwo_conj_mem_list {Y : Type} [Group Y] {ι : Type}
    {s : ι → Y} {R : List Y} (hsq : ∀ i, s i * s i = 1)
    (hseed : ∀ i, s i ∈ R)
    (hcl : ∀ i r, r ∈ R → s i * r * s i ∈ R) :
    ∀ u ∈ Subgroup.closure (Set.range s), ∀ i, u * s i * u⁻¹ ∈ R := by
  intro u hu
  induction hu using Subgroup.closure_induction_left with
  | one =>
      intro i
      simpa using hseed i
  | mul_left x hx u _ ih =>
      intro i
      obtain ⟨j, rfl⟩ := hx
      have hmul := hcl j (u * s i * u⁻¹) (ih i)
      have hinvj : (s j)⁻¹ = s j := inv_eq_of_mul_eq_one_right (hsq j)
      have hEq : (s j * u) * s i * (s j * u)⁻¹ = s j * (u * s i * u⁻¹) * s j := by
        rw [mul_inv_rev, hinvj]
        group
      rw [hEq]
      exact hmul
  | inv_mul_cancel x hx u _ ih =>
      intro i
      obtain ⟨j, rfl⟩ := hx
      have hinv : (s j)⁻¹ = s j := inv_eq_of_mul_eq_one_right (hsq j)
      have hmul := hcl j (u * s i * u⁻¹) (ih i)
      have hEq : ((s j)⁻¹ * u) * s i * ((s j)⁻¹ * u)⁻¹ =
          s j * (u * s i * u⁻¹) * s j := by
        rw [hinv, mul_inv_rev]
        group
        simp [hinv]
      rw [hEq]
      exact hmul

theorem ggResQTwo_norm_core {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Type}
    {s : ι → V ≃ₗ[ZMod p] V} {R : List (V ≃ₗ[ZMod p] V)}
    (hsq : ∀ i, s i * s i = 1)
    (hseed : ∀ i, s i ∈ R)
    (hcl : ∀ i r, r ∈ R → s i * r * s i ∈ R)
    (hRC : GGReflClosed s) {k : ι}
    (hk : ∃ (v : V) (f : Module.Dual (ZMod p) V), f v = 2 ∧ ∀ w, s k w = w - f w • v)
    {t : V ≃ₗ[ZMod p] V}
    (hnorm : t ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range s) : Set (V ≃ₗ[ZMod p] V)))
    (hnot : t * s k * t⁻¹ ∉ R) : False := by
  classical
  let W : Subgroup (V ≃ₗ[ZMod p] V) := Subgroup.closure (Set.range s)
  let r0 : V ≃ₗ[ZMod p] V := t * s k * t⁻¹
  have hr0W : r0 ∈ W := by
    have h0 := (Subgroup.mem_normalizer_iff.mp hnorm (s k)).mp
      (Subgroup.subset_closure ⟨k, rfl⟩)
    simpa [W, r0] using h0
  have hr02 : r0 ^ 2 = 1 := by
    rw [pow_two]
    calc r0 * r0 = t * (s k * s k) * t⁻¹ := by
          simp only [r0]
          group
      _ = 1 := by rw [hsq k]; group
  have hr0ne : r0 ≠ 1 := by
    rintro h1
    have hsk1 : s k = 1 := by
      calc s k = t⁻¹ * r0 * t := by
            simp only [r0]
            group
        _ = 1 := by rw [h1]; group
    obtain ⟨v, f, hfv, hsv⟩ := hk
    have hv2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero hp2
    have hv0 : v ≠ 0 := by
      intro hv
      exact hv2 (by rw [hv, map_zero] at hfv; exact hfv.symm)
    have h2 := hsv v
    rw [hfv] at h2
    have h3 : s k v = v := by
      simpa using congrArg (fun T : V ≃ₗ[ZMod p] V => T v) hsk1
    rw [h3] at h2
    have hz : (2 : ZMod p) • v = 0 := sub_eq_self.mp h2.symm
    exact hv0 ((smul_eq_zero.mp hz).resolve_left hv2)
  have hform : ∃ (v : V) (f : Module.Dual (ZMod p) V), ∀ w, r0 w = w - f w • v := by
    obtain ⟨v, f, -, hsv⟩ := hk
    refine ⟨t v, f.comp t.symm.toLinearMap, fun w => ?_⟩
    change t (s k (t.symm w)) = w - f (t.symm w) • t v
    rw [hsv, map_sub, map_smul, t.apply_symm_apply]
  obtain ⟨u, hu, i, hui⟩ := hRC r0 hr0W hr02 hr0ne hform
  have hmem : r0 ∈ R := by
    rw [hui]
    exact ggResQTwo_conj_mem_list hsq hseed hcl u hu i
  exact hnot hmem

theorem ggResQTwo_norm_check_false {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {n : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {T : Fin (n + 1) → Vector (ZMod p) (n + 2)}
    {g : Fin (n + 1) → V ≃ₗ[ZMod p] V} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod p) V} {x : V}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod p) h)
    (hα2 : ∀ k, α k (h k) = 2)
    {side : List (Fin (n + 1))} {R : List (Fin (n + 1) × List (Fin (n + 1)))}
    {x₀ : List ℕ} {τ : List (Fin (n + 1))} {k : Fin (n + 1)}
    (hxline : ∀ w : V, (∀ i, i ∈ side → α i w = 0) →
      w ∈ Submodule.span (ZMod p) ({x} : Set V))
    (hRC : GGReflClosed (fun i : {i : Fin (n + 1) // i ∈ side} => g i.1))
    (hfixnorm : ∀ t : V ≃ₗ[ZMod p] V, t ∈ Subgroup.closure (Set.range g) → t x = x →
      t ∈ Subgroup.normalizer (Subgroup.closure
        (Set.range fun i : {i : Fin (n + 1) // i ∈ side} => g i.1) :
          Set (V ≃ₗ[ZMod p] V)))
    (hcheck : ggResQTwoNormCheck T side R x₀ τ k = true) : False := by
  classical
  rcases (ggResQTwoNormCheck_spec T side R x₀ τ k).mp hcheck with
    ⟨hk, hlist, hx0ne, hx0last, hx0kill, hx0fix, hnotF⟩
  rcases hlist with ⟨hseedF, hclF, -⟩
  have hx0coord : ∃ l : Fin (n + 1),
      (ggFVec (R := ZMod p) x₀ : Vector (ZMod p) (n + 2)).get l.castSucc ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0ne (ggResQTwo_fvec_eq_zero h hx0last)
  obtain ⟨l, hl⟩ := hx0coord
  have hπne : ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (R := ZMod p) x₀) ≠ 0 :=
    ggFPi_ne_zero (φ := RingHom.id (ZMod p)) (h := h) hind hl
  have hπkill : ∀ i, i ∈ side →
      α i (ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (R := ZMod p) x₀)) = 0 := by
    intro i hi
    rw [ggFPi_root hT i]
    simpa using hx0kill i hi
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hxline _ hπkill)
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hπne
    rw [← hc, hc0, zero_smul]
  have hfix : (τ.map g).prod x = x := by
    have hword := ggFPi_word hT hg τ (ggFVec (R := ZMod p) x₀)
    rw [hx0fix] at hword
    have hsmul : c • ((τ.map g).prod x) = c • x := by
      calc c • (τ.map g).prod x = (τ.map g).prod (c • x) := by rw [map_smul]
        _ = (τ.map g).prod (ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (R := ZMod p) x₀)) := by
              rw [← hc]
        _ = ggFPi (RingHom.id (ZMod p)) h 0 (ggFVec (R := ZMod p) x₀) := hword
        _ = c • x := hc.symm
    have := congrArg (fun z => c⁻¹ • z) hsmul
    simpa [smul_smul, inv_mul_cancel₀ hc0] using this
  have ht_mem : (τ.map g).prod ∈ Subgroup.closure (Set.range g) :=
    ggResI_word_mem (g := g) τ
  have hnorm := hfixnorm (τ.map g).prod ht_mem hfix
  let R' : List (V ≃ₗ[ZMod p] V) :=
    R.map fun r => (r.2.map g).prod * g r.1 * ((r.2.map g).prod)⁻¹
  have hseed' : ∀ i : {i : Fin (n + 1) // i ∈ side}, g i.1 ∈ R' := by
    rintro ⟨j, hj⟩
    obtain ⟨r, hrR, hrM⟩ := hseedF j hj
    refine List.mem_map.mpr ⟨r, hrR, ?_⟩
    have hactual := (ggFMat_eq_iff hT hg hspan hind).mp hrM
    rw [ggF_conjWord_prod hg hα2 r] at hactual
    simpa using hactual
  have hcl' : ∀ i : {i : Fin (n + 1) // i ∈ side}, ∀ r ∈ R',
      g i.1 * r * g i.1 ∈ R' := by
    rintro ⟨j, hj⟩ r hr
    obtain ⟨e, heR, rfl⟩ := List.mem_map.mp hr
    obtain ⟨e', he'R, he'M⟩ := hclF j hj e heR
    refine List.mem_map.mpr ⟨e', he'R, ?_⟩
    have hactual := (ggFMat_eq_iff hT hg hspan hind).mp he'M
    rw [ggF_conjWord_prod hg hα2 e'] at hactual
    have hsimple : (([j] ++ ggConjWord e ++ [j]).map g).prod =
        g j * ((ggConjWord e).map g).prod * g j := by
      simp [List.map_append, List.prod_append]
      group
    rw [hactual, hsimple, ggF_conjWord_prod hg hα2 e]
  have hnot' : (τ.map g).prod * g k * ((τ.map g).prod)⁻¹ ∉ R' := by
    intro hmem
    obtain ⟨e, heR, heq⟩ := List.mem_map.mp hmem
    have hformal : ggFMat T (ggConjWord (k, τ)) = ggFMat T (ggConjWord e) := by
      refine (ggFMat_eq_iff hT hg hspan hind).mpr ?_
      rw [ggF_conjWord_prod hg hα2 (k, τ), ggF_conjWord_prod hg hα2 e]
      simpa using heq.symm
    exact hnotF e heR hformal
  exact ggResQTwo_norm_core (s := fun i : {i : Fin (n + 1) // i ∈ side} => g i.1)
    (R := R') (k := ⟨k, hk⟩) hp2
    (fun i : {i : Fin (n + 1) // i ∈ side} => ggResQTwo_refl_mul_self (hα2 i.1) (hg i.1))
    hseed' hcl' hRC ⟨h k, α k, hα2 k, hg k⟩ hnorm hnot'

@[expose] def ggResQTwoCellCheck {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (u v : ZMod 3) : GGResQTwoCell n → Bool
  | .reuse w => ggResQTwoReuseOk w && ggCellWitCheckI 3 C ib ic e₁ e₂ u v w
  | .commonKernel z =>
      ggResQTwoCommonKernelCheck (p := 3) (n := n)
        (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) z
  | .norm side x₀ R τ k =>
      ggResQTwoNormCheck (p := 3) (n := n)
        (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) side R x₀ τ k
  | .residual tag => ggResQTwoResidualShapeCheck tag n C ib ic e₁ e₂ u v

theorem ggResQTwoCell_commonKernel_false {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    {ib ic : Fin n} {e₁ e₂ : ℤ} {u v : ZMod 3}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod 3) V}
    (hT : GGFTable (RingHom.id (ZMod 3))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hind : LinearIndependent (ZMod 3) h)
    (hker : ∀ w : V, (∀ i : Fin (n + 1), α i w = 0) → w = 0)
    {z : List ℕ} (hcheck : ggResQTwoCellCheck C ib ic e₁ e₂ u v (.commonKernel z) = true) :
    False := by
  simpa only [ggResQTwoCellCheck] using
    ggResQTwo_commonKernel_false hT hind hker hcheck

theorem ggResQTwoCell_norm_false {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ}
    {ib ic : Fin n} {e₁ e₂ : ℤ} {u v : ZMod 3}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {g : Fin (n + 1) → V ≃ₗ[ZMod 3] V} {h : Fin (n + 1) → V}
    {α : Fin (n + 1) → Module.Dual (ZMod 3) V} {x : V}
    (hT : GGFTable (RingHom.id (ZMod 3))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod 3) h)
    (hα2 : ∀ k, α k (h k) = 2)
    {side : List (Fin (n + 1))} {R : List (Fin (n + 1) × List (Fin (n + 1)))}
    {x₀ : List ℕ} {τ : List (Fin (n + 1))} {k : Fin (n + 1)}
    (hxline : ∀ w : V, (∀ i, i ∈ side → α i w = 0) →
      w ∈ Submodule.span (ZMod 3) ({x} : Set V))
    (hRC : GGReflClosed (fun i : {i : Fin (n + 1) // i ∈ side} => g i.1))
    (hfixnorm : ∀ t : V ≃ₗ[ZMod 3] V, t ∈ Subgroup.closure (Set.range g) → t x = x →
      t ∈ Subgroup.normalizer (Subgroup.closure
        (Set.range fun i : {i : Fin (n + 1) // i ∈ side} => g i.1) :
          Set (V ≃ₗ[ZMod 3] V)))
    (hcheck : ggResQTwoCellCheck C ib ic e₁ e₂ u v (.norm side x₀ R τ k) = true) :
    False := by
  simpa only [ggResQTwoCellCheck] using
    ggResQTwo_norm_check_false (by decide : (3 : ℕ) ≠ 2) hT hg hspan hind hα2
      hxline hRC hfixnorm hcheck

end CFSG.StandardType
