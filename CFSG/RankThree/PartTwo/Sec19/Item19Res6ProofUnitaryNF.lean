module

public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p f e : ℕ} {K : Type} [Field K] {k : Subfield K}

section Gram

variable {F : Type} [Field F] (h₀ : UnitaryFieldData p e F)

@[expose] noncomputable def gram (P : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (P.map h₀.bar)ᵀ * P

theorem gram_mul (P M : Matrix (Fin 3) (Fin 3) F) :
    gram h₀ (P * M) = (M.map h₀.bar)ᵀ * gram h₀ P * M := by
  rw [gram, gram, Matrix.map_mul, transpose_mul]
  simp only [Matrix.mul_assoc]

theorem diagonal_mul_mul_diagonal_apply (a b : Fin 3 → F) (G : Matrix (Fin 3) (Fin 3) F)
    (i j : Fin 3) : (diagonal a * G * diagonal b) i j = a i * G i j * b j := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem map_bar_diagonal_transpose (d : Fin 3 → F) :
    ((diagonal d).map h₀.bar)ᵀ = diagonal (fun i => h₀.bar (d i)) := by
  rw [diagonal_map (map_zero h₀.bar), diagonal_transpose]

theorem gram_eq_zero_of_eigen {w : GL (Fin 3) F} (hw : w ∈ unitaryIsom3 h₀) {P : GL (Fin 3) F}
    {d : Fin 3 → F}
    (hwP : (w : Matrix (Fin 3) (Fin 3) F) * P = (P : Matrix (Fin 3) (Fin 3) F) * diagonal d)
    {i j : Fin 3} (hij : h₀.bar (d i) * d j ≠ 1) :
    gram h₀ (P : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hwu : ((w : Matrix (Fin 3) (Fin 3) F).map h₀.bar)ᵀ * w = 1 := hw
  have key : diagonal (fun i => h₀.bar (d i)) * gram h₀ (P : Matrix (Fin 3) (Fin 3) F) *
      diagonal d = gram h₀ (P : Matrix (Fin 3) (Fin 3) F) := by
    calc diagonal (fun i => h₀.bar (d i)) * gram h₀ (P : Matrix (Fin 3) (Fin 3) F) * diagonal d
        = gram h₀ ((P : Matrix (Fin 3) (Fin 3) F) * diagonal d) := by
          rw [gram_mul, map_bar_diagonal_transpose]
      _ = gram h₀ ((w : Matrix (Fin 3) (Fin 3) F) * P) := by rw [hwP]
      _ = gram h₀ (P : Matrix (Fin 3) (Fin 3) F) := by
          rw [gram, gram, Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _
            (P : Matrix (Fin 3) (Fin 3) F), hwu, Matrix.one_mul]
  have h1 := congrFun (congrFun key i) j
  rw [diagonal_mul_mul_diagonal_apply] at h1
  have h2 : gram h₀ (P : Matrix (Fin 3) (Fin 3) F) i j * (h₀.bar (d i) * d j - 1) = 0 := by
    linear_combination h1
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hij)

theorem bar_gram_apply_self (P : Matrix (Fin 3) (Fin 3) F) (i : Fin 3) :
    h₀.bar (gram h₀ P i i) = gram h₀ P i i := by
  simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    h₀.bar_bar]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem exists_unitary_rescale {P : GL (Fin 3) F}
    (hG : ∀ i j, i ≠ j → gram h₀ (P : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    ∃ (Q : GL (Fin 3) F) (s : Fin 3 → F), (∀ i, s i ≠ 0) ∧
      (Q : Matrix (Fin 3) (Fin 3) F) = (P : Matrix (Fin 3) (Fin 3) F) * diagonal s ∧
      Q ∈ unitaryIsom3 h₀ := by
  classical
  set G := gram h₀ (P : Matrix (Fin 3) (Fin 3) F) with hGdef
  have hGdiag : G = diagonal (fun i => G i i) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      exact hG i j hij
  have hdetP : (P : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
  have hdetG : G.det ≠ 0 := by
    rw [hGdef, gram, det_mul, det_transpose]
    refine mul_ne_zero ?_ hdetP
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero h₀.bar).2 hdetP
  have hGii : ∀ i, G i i ≠ 0 := by
    intro i h0
    apply hdetG
    rw [hGdiag, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hs : ∀ i, ∃ s : F, h₀.norm s = (G i i)⁻¹ := fun i =>
    UnitaryHigher.exists_norm_eq h₀ (by rw [map_inv₀, bar_gram_apply_self])
  choose s hsN using hs
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i h0
    have := hsN i
    rw [h0, UnitaryFieldData.norm, zero_mul] at this
    exact inv_ne_zero (hGii i) this.symm
  have hdet : ((P : Matrix (Fin 3) (Fin 3) F) * diagonal s).det ≠ 0 := by
    rw [det_mul, det_diagonal]
    exact mul_ne_zero hdetP (Finset.prod_ne_zero_iff.2 fun i _ => hs0 i)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, s, hs0, rfl, ?_⟩
  change gram h₀ ((P : Matrix (Fin 3) (Fin 3) F) * diagonal s) = 1
  rw [gram_mul, map_bar_diagonal_transpose, ← hGdef, hGdiag, diagonal_mul_diagonal,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  have := hsN i
  rw [UnitaryFieldData.norm] at this
  rw [show h₀.bar (s i) * G i i * s i = (s i * h₀.bar (s i)) * G i i by ring, this,
    inv_mul_cancel₀ (hGii i)]

end Gram

section Incl

variable (h : UnitaryFieldData p f K) (h₀ : UnitaryFieldData p e k)
  (hbar : ∀ x : k, h.bar (x : K) = ((h₀.bar x : k) : K))

include hbar in
theorem mem_unitaryIsom3_map_iff (z : GL (Fin 3) k) :
    GeneralLinearGroup.map k.subtype z ∈ unitaryIsom3 h ↔ z ∈ unitaryIsom3 h₀ := by
  have hcoe : ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (z : Matrix (Fin 3) (Fin 3) k).map k.subtype := by
    ext i j
    rw [GeneralLinearGroup.map_apply, Matrix.map_apply]
  have hkey : (((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map
      h.bar)ᵀ * ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((((z : Matrix (Fin 3) (Fin 3) k).map h₀.bar)ᵀ) * z).map k.subtype := by
    rw [hcoe, Matrix.map_mul, Matrix.transpose_map]
    congr 2
    ext i j
    exact hbar _
  change (((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map
      h.bar)ᵀ * ((GeneralLinearGroup.map k.subtype z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 ↔ (((z : Matrix (Fin 3) (Fin 3) k).map h₀.bar)ᵀ) * z = 1
  rw [hkey]
  constructor
  · intro h1
    exact Matrix.map_injective k.subtype_injective
      (h1.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  · intro h1
    rw [h1, Matrix.map_one _ (map_zero _) (map_one _)]

@[expose] noncomputable def subIsom : unitaryIsom3 h₀ →* unitaryIsom3 h :=
  ((GeneralLinearGroup.map k.subtype).comp (unitaryIsom3 h₀).subtype).codRestrict _
    fun z => (mem_unitaryIsom3_map_iff h h₀ hbar z).2 z.2

theorem coe_subIsom (z : unitaryIsom3 h₀) :
    ((subIsom h h₀ hbar z : unitaryIsom3 h) : GL (Fin 3) K) =
      GeneralLinearGroup.map k.subtype (z : GL (Fin 3) k) :=
  rfl

@[expose] noncomputable def scalarLift (A : Subgroup (MulAut (unitaryPSU h 3))) :
    Subgroup (GL (Fin 3) k) where
  carrier := {z | ∃ (c : kˣ) (w : unitaryIsom3 h₀), psuConj h (subIsom h h₀ hbar w) ∈ A ∧
    z = GeneralLinearGroup.scalar (Fin 3) c * (w : GL (Fin 3) k)}
  one_mem' := ⟨1, 1, by rw [map_one, map_one]; exact A.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨c, w, hw, rfl⟩ ⟨c', w', hw', rfl⟩
    refine ⟨c * c', w * w', by rw [map_mul, map_mul]; exact A.mul_mem hw hw', ?_⟩
    rw [map_mul, Subgroup.coe_mul]
    calc GeneralLinearGroup.scalar (Fin 3) c * (w : GL (Fin 3) k) *
          (GeneralLinearGroup.scalar (Fin 3) c' * (w' : GL (Fin 3) k))
        = GeneralLinearGroup.scalar (Fin 3) c * ((w : GL (Fin 3) k) *
          GeneralLinearGroup.scalar (Fin 3) c') * (w' : GL (Fin 3) k) := by group
      _ = GeneralLinearGroup.scalar (Fin 3) c * (GeneralLinearGroup.scalar (Fin 3) c' *
          (w : GL (Fin 3) k)) * (w' : GL (Fin 3) k) := by
          rw [(commute_scalar c' (w : GL (Fin 3) k)).eq]
      _ = GeneralLinearGroup.scalar (Fin 3) c * GeneralLinearGroup.scalar (Fin 3) c' *
          ((w : GL (Fin 3) k) * (w' : GL (Fin 3) k)) := by group
  inv_mem' := by
    rintro _ ⟨c, w, hw, rfl⟩
    refine ⟨c⁻¹, w⁻¹, by rw [map_inv, map_inv]; exact A.inv_mem hw, ?_⟩
    rw [_root_.mul_inv_rev, map_inv, Subgroup.coe_inv]
    exact ((commute_scalar c (w : GL (Fin 3) k)).inv_inv).eq

theorem mem_scalarLift {A : Subgroup (MulAut (unitaryPSU h 3))} {z : GL (Fin 3) k} :
    z ∈ scalarLift h h₀ hbar A ↔ ∃ (c : kˣ) (w : unitaryIsom3 h₀),
      psuConj h (subIsom h h₀ hbar w) ∈ A ∧
        z = GeneralLinearGroup.scalar (Fin 3) c * (w : GL (Fin 3) k) :=
  Iff.rfl

theorem scalar_mem_scalarLift (A : Subgroup (MulAut (unitaryPSU h 3))) (c : kˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ scalarLift h h₀ hbar A :=
  ⟨c, 1, by rw [map_one, map_one]; exact A.one_mem, by simp⟩

theorem mem_scalarLift_of_mem {A : Subgroup (MulAut (unitaryPSU h 3))} (w : unitaryIsom3 h₀)
    (hw : psuConj h (subIsom h h₀ hbar w) ∈ A) : (w : GL (Fin 3) k) ∈ scalarLift h h₀ hbar A :=
  ⟨1, w, hw, by simp⟩

end Incl

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
