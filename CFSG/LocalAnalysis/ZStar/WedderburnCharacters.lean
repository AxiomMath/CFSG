module

public import CFSG.LocalAnalysis.ZStar.WedderburnBlock
public import CFSG.LocalAnalysis.ZStar.ClassProductValue

public section

namespace CFSG

namespace ZStar.WedderburnCharacters

open ZStar.ClassSums ZStar.ClassProductValue
  ZStar.WedderburnBlock

noncomputable section

universe u v

variable {K : Type u} {G : Type v}

local instance [Group G] : DecidableEq G := Classical.decEq G

@[expose] noncomputable def componentCharacter [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) (g : G) : K :=
  Matrix.trace (phi (MonoidAlgebra.single g 1) i)

theorem componentCharacter_eq_of_isConj [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) {a b : G} (hab : IsConj a b) :
    componentCharacter phi i a = componentCharacter phi i b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hab
  let A := phi (MonoidAlgebra.single g 1) i
  let B := phi (MonoidAlgebra.single a 1) i
  let C := phi (MonoidAlgebra.single g⁻¹ 1) i
  have hconj :
      phi (MonoidAlgebra.single (g * a * g⁻¹) 1) i = A * B * C := by
    change phi (MonoidAlgebra.single (g * a * g⁻¹) 1) i =
      phi (MonoidAlgebra.single g 1) i *
        phi (MonoidAlgebra.single a 1) i *
          phi (MonoidAlgebra.single g⁻¹ 1) i
    rw [← Pi.mul_apply, ← map_mul, ← Pi.mul_apply, ← map_mul]
    simp
  unfold componentCharacter
  rw [hconj]
  symm
  calc
    Matrix.trace (A * B * C) = Matrix.trace (C * (A * B)) :=
      Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((C * A) * B) := by rw [mul_assoc]
    _ = Matrix.trace (B * (C * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (B * 1) := by
      have hCA : C * A = 1 := by
        change phi (MonoidAlgebra.single g⁻¹ 1) i *
            phi (MonoidAlgebra.single g 1) i = 1
        rw [← Pi.mul_apply, ← map_mul]
        rw [MonoidAlgebra.single_mul_single]
        simp only [inv_mul_cancel, one_mul]
        rw [← MonoidAlgebra.one_def, map_one]
        rfl
      rw [hCA]
    _ = Matrix.trace B := by rw [mul_one]

private theorem central_component_eq_scalar [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    {z : MonoidAlgebra K G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra K G))
    (i : Fin n) :
    ∃ c : K, phi z i = Matrix.scalar (Fin (d i)) c := by
  have hcomm (p q : Fin (d i)) :
      Commute (Matrix.single p q (1 : K)) (phi z i) := by
    let y : BlockProduct K d := Pi.single i (Matrix.single p q (1 : K))
    let x : MonoidAlgebra K G := phi.symm y
    have hc := (Submonoid.mem_center_iff.mp hz) x
    have hc' := congrArg (fun a : BlockProduct K d ↦ a i)
      (congrArg phi hc)
    rw [commute_iff_eq]
    simpa [x, y] using hc'
  have hrange : phi z i ∈ Set.range (Matrix.scalar (Fin (d i))) := by
    apply Matrix.mem_range_scalar_of_commute_single
    intro p q hpq
    exact hcomm p q
  obtain ⟨c, hc⟩ := hrange
  exact ⟨c, hc.symm⟩

private theorem trace_scalar_fin [Field K] (m : ℕ) (c : K) :
    Matrix.trace (Matrix.scalar (Fin m) c) = (m : K) * c := by
  simp [Matrix.trace, Matrix.scalar_apply, Matrix.diagonal]

private theorem scalar_mul_scalar_fin [Field K] (m : ℕ) (a b : K) :
    Matrix.scalar (Fin m) a * Matrix.scalar (Fin m) b =
      Matrix.scalar (Fin m) (a * b) := by
  ext p q
  simp [Matrix.scalar_apply, Matrix.diagonal, Matrix.mul_apply]

@[simp]
theorem componentCharacter_one [Field K] [Group G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) :
    componentCharacter phi i 1 = (d i : K) := by
  rw [componentCharacter, ← MonoidAlgebra.one_def, map_one]
  simpa using trace_scalar_fin (K := K) (d i) 1

private theorem trace_component_classSum [Field K] [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) (C : ConjClasses G) :
    Matrix.trace (phi (classSum K C) i) =
      (classSize C : K) * componentCharacter phi i (classRep C) := by
  classical
  rw [classSum, map_sum]
  calc
    Matrix.trace
        ((∑ x ∈ classFinset C, phi (MonoidAlgebra.single x 1)) i) =
        ∑ x ∈ classFinset C,
          Matrix.trace (phi (MonoidAlgebra.single x 1) i) := by
      simp
    _ = ∑ _x ∈ classFinset C,
          componentCharacter phi i (classRep C) := by
      apply Finset.sum_congr rfl
      intro x hx
      unfold componentCharacter
      apply componentCharacter_eq_of_isConj phi i
      apply ConjClasses.mk_eq_mk_iff_isConj.mp
      simpa only [mem_classFinset, mk_classRep] using hx
    _ = (classSize C : K) * componentCharacter phi i (classRep C) := by
      simp [classSize, nsmul_eq_mul]

private theorem component_classProduct_identity [Field K] [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) (C D : ConjClasses G) :
    (classSize C : K) * (classSize D : K) *
        (componentCharacter phi i (classRep C) *
          componentCharacter phi i (classRep D)) =
      (d i : K) * ∑ E : ConjClasses G,
        (structureConstant C D E : K) * (classSize E : K) *
          componentCharacter phi i (classRep E) := by
  classical
  obtain ⟨c, hc⟩ := central_component_eq_scalar phi
    (classSum_mem_center K C) i
  obtain ⟨e, he⟩ := central_component_eq_scalar phi
    (classSum_mem_center K D) i
  have hc_trace := trace_component_classSum phi i C
  have he_trace := trace_component_classSum phi i D
  rw [hc, trace_scalar_fin] at hc_trace
  rw [he, trace_scalar_fin] at he_trace
  have hproduct := congrArg
    (fun z : MonoidAlgebra K G ↦ Matrix.trace (phi z i))
    (classSum_mul K C D)
  have hleft :
      Matrix.trace (phi (classSum K C * classSum K D) i) =
        (d i : K) * (c * e) := by
    rw [map_mul, Pi.mul_apply, hc, he,
      scalar_mul_scalar_fin, trace_scalar_fin]
  have hright :
      Matrix.trace
          (phi (∑ E : ConjClasses G,
            (structureConstant C D E : K) • classSum K E) i) =
        ∑ E : ConjClasses G,
          (structureConstant C D E : K) * (classSize E : K) *
            componentCharacter phi i (classRep E) := by
    rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_apply]
    change Matrix.trace
      (∑ E : ConjClasses G,
        (structureConstant C D E : K) • phi (classSum K E) i) = _
    rw [Matrix.trace_sum]
    apply Finset.sum_congr rfl
    intro E hE
    rw [Matrix.trace_smul, trace_component_classSum]
    simp only [smul_eq_mul]
    ring
  have hproduct' :
      (d i : K) * (c * e) =
        ∑ E : ConjClasses G,
          (structureConstant C D E : K) * (classSize E : K) *
            componentCharacter phi i (classRep E) :=
    hleft.symm.trans (hproduct.trans hright)
  calc
    (classSize C : K) * (classSize D : K) *
        (componentCharacter phi i (classRep C) *
          componentCharacter phi i (classRep D)) =
        ((classSize C : K) * componentCharacter phi i (classRep C)) *
          ((classSize D : K) * componentCharacter phi i (classRep D)) := by
      ring
    _ = ((d i : K) * c) * ((d i : K) * e) := by
      rw [← hc_trace, ← he_trace]
    _ = (d i : K) * ((d i : K) * (c * e)) := by ring
    _ = (d i : K) * ∑ E : ConjClasses G,
        (structureConstant C D E : K) * (classSize E : K) *
          componentCharacter phi i (classRep E) := by
      rw [hproduct']

private theorem componentCharacter_mul_eq_degree_mul_of_constant_on_product
    [Field K] [CharZero K] [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) (C D : ConjClasses G) (a : K)
    (hchar : ∀ E : ConjClasses G, structureConstant C D E ≠ 0 →
      componentCharacter phi i (classRep E) = a) :
    componentCharacter phi i (classRep C) *
        componentCharacter phi i (classRep D) =
      (d i : K) * a := by
  classical
  have hmassCast :
      (∑ E : ConjClasses G,
        (structureConstant C D E : K) * (classSize E : K)) =
          (classSize C : K) * (classSize D : K) := by
    exact_mod_cast sum_structureConstant_mul_classSize (G := G) C D
  have hsum :
      (∑ E : ConjClasses G,
        (structureConstant C D E : K) * (classSize E : K) *
          componentCharacter phi i (classRep E)) =
        (classSize C : K) * (classSize D : K) * a := by
    calc
      (∑ E : ConjClasses G,
        (structureConstant C D E : K) * (classSize E : K) *
          componentCharacter phi i (classRep E)) =
          ∑ E : ConjClasses G,
            (structureConstant C D E : K) * (classSize E : K) * a := by
        apply Finset.sum_congr rfl
        intro E hE
        by_cases hzero : structureConstant C D E = 0
        · simp [hzero]
        · rw [hchar E hzero]
      _ = (∑ E : ConjClasses G,
          (structureConstant C D E : K) * (classSize E : K)) * a := by
        rw [Finset.sum_mul]
      _ = (classSize C : K) * (classSize D : K) * a := by
        rw [hmassCast]
  have hid := component_classProduct_identity phi i C D
  rw [hsum] at hid
  have hCpos : 0 < classSize C :=
    Finset.card_pos.mpr ⟨classRep C, classRep_mem_classFinset C⟩
  have hDpos : 0 < classSize D :=
    Finset.card_pos.mpr ⟨classRep D, classRep_mem_classFinset D⟩
  have hCne : (classSize C : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCpos)
  have hDne : (classSize D : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hDpos)
  apply mul_left_cancel₀ (mul_ne_zero hCne hDne)
  calc
    ((classSize C : K) * (classSize D : K)) *
        (componentCharacter phi i (classRep C) *
          componentCharacter phi i (classRep D)) =
      (d i : K) * ((classSize C : K) * (classSize D : K) * a) := hid
    _ = ((classSize C : K) * (classSize D : K)) * ((d i : K) * a) := by
      ring

private theorem exists_class_product_witness
    [Group G] [Fintype G]
    {C D E : ConjClasses G}
    (h : structureConstant C D E ≠ 0) :
    ∃ x : G, x ∈ classFinset C ∧
      ∃ y : G, y ∈ classFinset D ∧ x * y = classRep E := by
  classical
  unfold structureConstant at h
  obtain ⟨⟨x, y⟩, hxy⟩ :=
    Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter, Finset.mem_product] at hxy
  exact ⟨x, hxy.1.1, y, hxy.1.2, hxy.2⟩

theorem componentCharacter_mul_eq_degree_mul_of_product_constancy
    [Field K] [CharZero K] [Group G] [Fintype G]
    {n : ℕ} {d : Fin n → ℕ}
    (phi : MonoidAlgebra K G ≃ₐ[K] BlockProduct K d)
    (i : Fin n) (t sigma : G)
    (hconst : ∀ t' sigma' : G, IsConj t t' → IsConj sigma sigma' →
      componentCharacter phi i (t' * sigma') =
        componentCharacter phi i (t * sigma)) :
    componentCharacter phi i t * componentCharacter phi i sigma =
      (d i : K) * componentCharacter phi i (t * sigma) := by
  let C : ConjClasses G := ConjClasses.mk t
  let D : ConjClasses G := ConjClasses.mk sigma
  have hformula :=
    componentCharacter_mul_eq_degree_mul_of_constant_on_product
      phi i C D (componentCharacter phi i (t * sigma)) (by
        intro E hE
        obtain ⟨x, hxC, y, hyD, hxy⟩ := exists_class_product_witness hE
        have htx : IsConj t x :=
          ConjClasses.mk_eq_mk_iff_isConj.mp (by
            simpa only [C] using (mem_classFinset.mp hxC).symm)
        have hsigmay : IsConj sigma y :=
          ConjClasses.mk_eq_mk_iff_isConj.mp (by
            simpa only [D] using (mem_classFinset.mp hyD).symm)
        calc
          componentCharacter phi i (classRep E) =
              componentCharacter phi i (x * y) := by rw [hxy]
          _ = componentCharacter phi i (t * sigma) :=
            hconst x y htx hsigmay)
  have htC : IsConj t (classRep C) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (by simp [C])
  have hsigmaD : IsConj sigma (classRep D) :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (by simp [D])
  simpa only [componentCharacter_eq_of_isConj phi i htC,
    componentCharacter_eq_of_isConj phi i hsigmaD] using hformula

end

end ZStar.WedderburnCharacters

end CFSG
