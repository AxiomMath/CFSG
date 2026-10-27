module

public import CFSG.Models
public import CFSG.Open.PGLModelStated

public section

namespace CFSG.PGLModel

open CFSG.Open CFSG.Models

theorem statedClassicalModel_of_mulEquiv_projSL {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSL n p f) (e : G ≃* projSL n (GaloisField p f)) :
    StatedClassicalModel G .PSL n p f :=
  ⟨hadm, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by have := hadm.2.1; omega), ⟨e.trans (projSLEquivStatedProj n _)⟩⟩

theorem statedClassicalModel_of_mulEquiv_projSU {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSU n p f) (e : G ≃* projSU n p f) :
    StatedClassicalModel G .PSU n p f := by
  refine ⟨hadm, GaloisField p (2 * f), inferInstance, inferInstance, ?_,
    ⟨e.trans (projSUEquivStatedProj n p f)⟩⟩
  rw [GaloisField.card p (2 * f) (by have := hadm.2.1; omega), ← pow_mul, mul_comm]

theorem statedClassicalModel_of_mulEquiv_projSp {G : Type} [Group G] {n p f : ℕ} [Fact p.Prime]
    (hadm : StatedLieAdmissible .PSp n p f) (e : G ≃* projSp n (GaloisField p f)) :
    StatedClassicalModel G .PSp n p f :=
  ⟨hadm, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by have := hadm.2.1; omega), ⟨e.trans (projSpEquivStatedProj n _)⟩⟩

theorem statedClassicalModel_of_mulEquiv_projOmegaPlus {G : Type} [Group G] {n p f : ℕ}
    [Fact p.Prime] (hadm : StatedLieAdmissible .POmegaPlus n p f)
    (e : G ≃* projOmegaPlus n (GaloisField p f)) : StatedClassicalModel G .POmegaPlus n p f :=
  ⟨hadm, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by have := hadm.2.1; omega),
    ⟨e.trans (StatedAPI.mapMkEquivStatedProj (StatedOmega (StatedQuadPlus n (GaloisField p f))))⟩⟩

theorem statedClassicalModel_of_mulEquiv_projOmegaMinus {G : Type} [Group G] {m p f : ℕ}
    [Fact p.Prime] (hadm : StatedLieAdmissible .POmegaMinus (m + 1) p f) {b c : GaloisField p f}
    (hbc : ∀ s : GaloisField p f, s ^ 2 + b * s + c ≠ 0)
    (e : G ≃* projOmegaMinus m (GaloisField p f) b c) :
    StatedClassicalModel G .POmegaMinus (m + 1) p f :=
  ⟨hadm, GaloisField p f, inferInstance, inferInstance,
    GaloisField.card p f (by have := hadm.2.1; omega), b, c, hbc,
    ⟨e.trans (StatedAPI.mapMkEquivStatedProj
      (StatedOmega (StatedQuadMinus (m + 1) (GaloisField p f) b c)))⟩⟩

theorem lieModel_projSL {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSL n p e) :
    LieModel (projSL n (GaloisField p e)) .PSL n p e :=
  ⟨h, .inl ⟨h, GaloisField p e, inferInstance, inferInstance,
    GaloisField.card p e (by have := h.2.1; omega), ⟨projSLEquivStatedProj n _⟩⟩⟩

theorem lieModel_projSU {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSU n p e) :
    LieModel (projSU n p e) .PSU n p e := by
  refine ⟨h, .inl ⟨h, GaloisField p (2 * e), inferInstance, inferInstance, ?_,
    ⟨projSUEquivStatedProj n p e⟩⟩⟩
  rw [GaloisField.card p (2 * e) (by have := h.2.1; omega), ← pow_mul, mul_comm]

theorem lieModel_projSp {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSp n p e) :
    LieModel (projSp n (GaloisField p e)) .PSp n p e :=
  ⟨h, .inl ⟨h, GaloisField p e, inferInstance, inferInstance,
    GaloisField.card p e (by have := h.2.1; omega), ⟨projSpEquivStatedProj n _⟩⟩⟩

theorem lieModel_projOmegaPlus {n p e : ℕ} [Fact p.Prime]
    (h : StatedLieAdmissible .POmegaPlus n p e) :
    LieModel (projOmegaPlus n (GaloisField p e)) .POmegaPlus n p e :=
  ⟨h, .inl ⟨h, GaloisField p e, inferInstance, inferInstance,
    GaloisField.card p e (by have := h.2.1; omega),
    ⟨(StatedAPI.mapMkEquivStatedProj (StatedOmega (StatedQuadPlus n (GaloisField p e))))⟩⟩⟩

theorem lieModel_projOmegaMinus {n p e : ℕ} [Fact p.Prime]
    (h : StatedLieAdmissible .POmegaMinus n p e) {b c : GaloisField p e}
    (hbc : ∀ s : GaloisField p e, s ^ 2 + b * s + c ≠ 0) :
    LieModel (projOmegaMinus (n - 1) (GaloisField p e) b c) .POmegaMinus n p e :=
  ⟨h, .inl ⟨h, GaloisField p e, inferInstance, inferInstance,
    GaloisField.card p e (by have := h.2.1; omega), b, c, hbc,
    ⟨(StatedAPI.mapMkEquivStatedProj (StatedOmega (StatedQuadMinus n (GaloisField p e) b c)))⟩⟩⟩

end CFSG.PGLModel
