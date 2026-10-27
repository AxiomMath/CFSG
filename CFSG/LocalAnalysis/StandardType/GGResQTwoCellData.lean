module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoCell
public import CFSG.LocalAnalysis.StandardType.GGResRefMatBridge
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def ggResQTwoCellAt {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (wits : List (ℕ × ℕ × GGResQTwoCell n)) (u v : ZMod 3) : Bool :=
  match wits.find? (fun w => w.1 == u.val && w.2.1 == v.val) with
  | some w => ggResQTwoCellCheck C ib ic e₁ e₂ u v w.2.2
  | none => false

abbrev GGResQTwoCellCheckAll {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (wits : List (ℕ × ℕ × GGResQTwoCell n)) : Prop :=
  ∀ u v : ZMod 3, ggResQTwoCellAt C ib ic e₁ e₂ wits u v = true

abbrev GGResQTwoShapeCoverage {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib : Fin n)
    (shapes : List (Fin n × ℤ × ℤ))
    (wits : Fin n × ℤ × ℤ → List (ℕ × ℕ × GGResQTwoCell n)) : Prop :=
  ∀ s ∈ shapes, GGResQTwoCellCheckAll C ib s.1 s.2.1 s.2.2 (wits s)

abbrev ggResQTwoVecNeZero {p n : ℕ} (z : List ℕ) : Prop :=
  ∃ l : Fin (n + 2), (ggFVec (R := ZMod p) z).get l ≠ 0

abbrev ggResQTwoVecEqV {p n : ℕ} (v w : Vector (ZMod p) (n + 2)) : Prop :=
  ∀ l : Fin (n + 2), v.get l = w.get l

theorem ggResQTwoVecNeZero_iff {p n : ℕ} (z : List ℕ) :
    ggResQTwoVecNeZero (p := p) (n := n) z ↔
      (ggFVec (R := ZMod p) z : Vector (ZMod p) (n + 2)) ≠ 0 := by
  constructor
  · rintro ⟨l, hl⟩ h0
    exact hl (by rw [h0, Vector.get_eq_getElem, Vector.getElem_zero])
  · intro h0
    by_contra h
    apply h0
    apply Vector.ext
    intro l hl
    have hz : (0 : Vector (ZMod p) (n + 2))[l] = 0 := Vector.getElem_zero l hl
    rw [hz]
    by_contra hl0
    exact h ⟨⟨l, hl⟩, by simpa [Vector.get_eq_getElem] using hl0⟩

theorem ggResQTwoVecEqV_iff {p n : ℕ} (v w : Vector (ZMod p) (n + 2)) :
    ggResQTwoVecEqV v w ↔ v = w := by
  constructor
  · intro h
    apply Vector.ext
    intro l hl
    exact h ⟨l, hl⟩
  · intro h l
    rw [h]

abbrev GGResQTwoCommonKernelOKK {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (z : List ℕ) : Prop :=
  ggResQTwoVecNeZero (p := p) (n := n) z ∧
    z.getD (n + 1) 0 = 0 ∧
    ∀ i : Fin (n + 1), ggFDot (T i) (ggFVec z) = 0

theorem GGResQTwoCommonKernelOKK_iff {p n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (z : List ℕ) :
    GGResQTwoCommonKernelOKK T z ↔ GGResQTwoCommonKernelOK T z := by
  unfold GGResQTwoCommonKernelOKK GGResQTwoCommonKernelOK
  rw [ggResQTwoVecNeZero_iff]

abbrev GGResQTwoNormOKK {p : ℕ} {n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1))))
    (x₀ : List ℕ) (τ : List (Fin (n + 1))) (k : Fin (n + 1)) : Prop :=
  k ∈ side ∧
    GGResQTwoListOK T side R ∧
    ggResQTwoVecNeZero (p := p) (n := n) x₀ ∧
    x₀.getD (n + 1) 0 = 0 ∧
    (∀ i ∈ side, ggFDot (T i) (ggFVec x₀) = 0) ∧
    ggResQTwoVecEqV (ggFWord T τ (ggFVec x₀)) (ggFVec x₀) ∧
    ∀ r ∈ R, ggFMat T (ggConjWord (k, τ)) ≠ ggFMat T (ggConjWord r)

theorem GGResQTwoNormOKK_iff {p n : ℕ}
    (T : Fin (n + 1) → Vector (ZMod p) (n + 2)) (side : List (Fin (n + 1)))
    (R : List (Fin (n + 1) × List (Fin (n + 1))))
    (x₀ : List ℕ) (τ : List (Fin (n + 1))) (k : Fin (n + 1)) :
    GGResQTwoNormOKK T side R x₀ τ k ↔ GGResQTwoNormOK T side R x₀ τ k := by
  unfold GGResQTwoNormOKK GGResQTwoNormOK
  rw [ggResQTwoVecNeZero_iff, ggResQTwoVecEqV_iff]

@[expose] def ggResQTwoCellCheckK {n : ℕ} (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n)
    (e₁ e₂ : ℤ) (u v : ZMod 3) : GGResQTwoCell n → Bool
  | .reuse w => ggResQTwoReuseOk w && ggCellWitCheckI 3 C ib ic e₁ e₂ u v w
  | .commonKernel z =>
      decide (GGResQTwoCommonKernelOKK
        (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) z)
  | .norm side x₀ R τ k =>
      decide (GGResQTwoNormOKK
        (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) side R x₀ τ k)
  | .residual tag => ggResQTwoResidualShapeCheck tag n C ib ic e₁ e₂ u v

theorem ggResQTwoCellCheckK_imp {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} {u v : ZMod 3} (w : GGResQTwoCell n)
    (h : ggResQTwoCellCheckK C ib ic e₁ e₂ u v w = true) :
    ggResQTwoCellCheck C ib ic e₁ e₂ u v w = true := by
  cases w with
  | reuse w => simpa [ggResQTwoCellCheckK, ggResQTwoCellCheck] using h
  | commonKernel z =>
      have hK : GGResQTwoCommonKernelOKK
          (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) z :=
        of_decide_eq_true (by simpa [ggResQTwoCellCheckK] using h)
      rw [show ggResQTwoCellCheck C ib ic e₁ e₂ u v (.commonKernel z) =
          ggResQTwoCommonKernelCheck
            (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) z from rfl]
      rw [ggResQTwoCommonKernelCheck_spec]
      exact (GGResQTwoCommonKernelOKK_iff _ _).mp hK
  | norm side x₀ R τ k =>
      have hK : GGResQTwoNormOKK
          (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) side R x₀ τ k :=
        of_decide_eq_true (by simpa [ggResQTwoCellCheckK] using h)
      rw [show ggResQTwoCellCheck C ib ic e₁ e₂ u v (.norm side x₀ R τ k) =
          ggResQTwoNormCheck
            (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) side R x₀ τ k from rfl]
      rw [ggResQTwoNormCheck_spec]
      exact (GGResQTwoNormOKK_iff _ _ _ _ _ _).mp hK
  | residual tag => simpa [ggResQTwoCellCheckK, ggResQTwoCellCheck] using h

theorem ggResQTwoCellCheck_reuse_of_cellCheck {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ} {u v : ZMod 3}
    {w : GGCellWitI n} (hok : ggResQTwoReuseOk w = true)
    (hcell : ggCellWitCheckI 3 C ib ic e₁ e₂ u v w = true) :
    ggResQTwoCellCheck C ib ic e₁ e₂ u v (.reuse w) = true := by
  simp [ggResQTwoCellCheck, hok, hcell]

theorem ggResQTwoCellAt_of_find {n : ℕ}
    {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n} {e₁ e₂ : ℤ}
    {wits : List (ℕ × ℕ × GGResQTwoCell n)} {u v : ZMod 3} {w : GGResQTwoCell n}
    (hfind : wits.find? (fun x => x.1 == u.val && x.2.1 == v.val) =
      some (u.val, v.val, w)) :
    ggResQTwoCellAt C ib ic e₁ e₂ wits u v =
      ggResQTwoCellCheck C ib ic e₁ e₂ u v w := by
  simp [ggResQTwoCellAt, hfind]

theorem ggResQTwoZMod3_cases (u : ZMod 3) : u = 0 ∨ u = 1 ∨ u = 2 := by
  have h : u.val = 0 ∨ u.val = 1 ∨ u.val = 2 := by
    have := ZMod.val_lt u
    omega
  rcases h with h | h | h
  · left
    rw [← ZMod.natCast_zmod_val u, h]
    rfl
  · right; left
    rw [← ZMod.natCast_zmod_val u, h]
    rfl
  · right; right
    rw [← ZMod.natCast_zmod_val u, h]
    rfl

end CFSG.StandardType
