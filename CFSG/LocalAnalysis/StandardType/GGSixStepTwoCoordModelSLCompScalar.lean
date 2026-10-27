module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLCompBlock

public section

open Polynomial Module Matrix CFSG.RankThree.CALinearPlane

namespace CFSG.StandardType

namespace CoordSL

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ}
  [Fact p.Prime] {hζ : AdjoinRoot.root g ^ p = 1}
  (hprim : IsPrimitiveRoot (AdjoinRoot.root g) p) {β : Fin s → ZMod p}
  {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r} {hC : (rootMat g).det = 1}

include hprim in
theorem col_of_mem_zeroCoords (hal : Aligned hζ β) {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u)
    (hZ : ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε β → y ∈ zeroCoords ε β →
      u * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
        Matrix.SpecialLinearGroup.transvection hxy 1 * u)
    {x : Fin n} (hx : x ∈ zeroCoords ε β) (z : Fin n) :
    (u : Matrix (Fin n) (Fin n) K) z x =
      if z = x then (u : Matrix (Fin n) (Fin n) K) x x else 0 := by
  by_cases hy : ∃ y ∈ zeroCoords ε β, y ≠ x
  · obtain ⟨y, hyJ, hyx⟩ := hy
    have hcomm : ∀ (a b : Fin n) (hab : a ≠ b), a ∈ zeroCoords ε β → b ∈ zeroCoords ε β →
        (u : Matrix (Fin n) (Fin n) K) * single a b (1 : K) =
          single a b 1 * (u : Matrix (Fin n) (Fin n) K) := by
      intro a b hab ha hb
      have h1 := congrArg (fun t : Matrix.SpecialLinearGroup (Fin n) K =>
        (t : Matrix (Fin n) (Fin n) K)) (hZ a b hab ha hb)
      simp only [Matrix.SpecialLinearGroup.coe_mul,
        Matrix.SpecialLinearGroup.transvection_coe] at h1
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h1
      exact add_left_cancel h1
    have h1 := SLNS.col_of_comm_single (hcomm x y (Ne.symm hyx) hx hyJ) z
    have h2 := SLNS.col_of_comm_single (hcomm y x hyx hyJ hx) x
    rw [ite_eq_right (Ne.symm hyx)] at h2
    have h3 := SLNS.col_of_comm_single (hcomm x y (Ne.symm hyx) hx hyJ) x
    rw [ite_eq_left rfl] at h3
    rw [h1, ← h3]
  · push Not at hy
    have hP := compIndicator_comm_of_mem hprim hal hu
    have h1 := congrFun (congrFun hP z) x
    rw [compIndicator_mul_apply, mul_compIndicator_apply, ite_eq_left hx] at h1
    by_cases hz : z = x
    · subst hz
      simp
    · have hzJ : z ∉ zeroCoords ε β := fun h => hz (hy z h)
      rw [ite_eq_right hzJ] at h1
      rw [ite_eq_right hz, h1]

omit [Finite K] [Fact p.Prime] in
theorem transvection_mulVec {R : Type*} [CommRing R] {i j : Fin s} (hij : i ≠ j) (c : R)
    (v : Fin s → R) :
    ((Matrix.SpecialLinearGroup.transvection hij c : Matrix.SpecialLinearGroup (Fin s) R) :
      Matrix (Fin s) (Fin s) R) *ᵥ v = v + Pi.single i (c * v j) := by
  rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.single_mulVec]
  rfl

include hprim in
theorem apply_single_eq_of_comm_theta (hal : Aligned hζ β)
    {u : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u)
    (hcls : ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 → ∀ c : AdjoinRoot g,
      u * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
        theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * u)
    {i : Fin s} (hi : β i ≠ 0) (ξ : AdjoinRoot g) :
    frameForm g ε (u : Matrix (Fin n) (Fin n) K) (Pi.single i ξ, 0) =
      (Pi.single i (ξ * (frameForm g ε (u : Matrix (Fin n) (Fin n) K) (Pi.single i 1, 0)).1 i),
        0) := by
  obtain ⟨hφ, -, -⟩ := frameForm_comm_of_mem (hC := hC) hu
  set φ := frameForm g ε (u : Matrix (Fin n) (Fin n) K) with hφdef
  by_cases hj : ∃ j, j ≠ i ∧ β j = β i
  · obtain ⟨j, hji, hβ⟩ := hj
    have hij : i ≠ j := Ne.symm hji
    have key : ∀ c η : AdjoinRoot g, φ (Pi.single i (c * η), 0) =
        (Pi.single i (c * (φ (Pi.single j η, 0)).1 j), 0) := by
      intro c η
      have h1 := hcls i j hij hβ.symm hi c
      have h2 := congrArg (fun t : Matrix.SpecialLinearGroup (Fin n) K =>
        frameForm g ε (t : Matrix (Fin n) (Fin n) K) ((Pi.single j η : Fin s → AdjoinRoot g),
          (0 : Fin r → K))) h1
      simp only [Matrix.SpecialLinearGroup.coe_mul, frameForm_mul, LinearMap.comp_apply,
        coe_theta, frameForm_thetaMat, blockAct_apply, ← hφdef] at h2
      rw [transvection_mulVec, transvection_mulVec, Pi.single_eq_same] at h2
      have h3 : φ ((Pi.single j η : Fin s → AdjoinRoot g) + Pi.single i (c * η),
          (0 : Fin r → K)) = φ (Pi.single j η, 0) + φ (Pi.single i (c * η), 0) := by
        rw [← map_add, Prod.mk_add_mk, add_zero]
      rw [h3] at h2
      refine Prod.ext ?_ ?_
      · have h4 := congrArg Prod.fst h2
        simp only [Prod.fst_add] at h4
        exact add_left_cancel h4
      · have h4 := congrArg Prod.snd h2
        simp only [Prod.snd_add] at h4
        exact add_eq_left.mp h4
    have hμ : (φ (Pi.single i 1, 0)).1 i = (φ (Pi.single j 1, 0)).1 j := by
      have h1 := key 1 1
      rw [one_mul, one_mul] at h1
      rw [h1]
      exact Pi.single_eq_same _ _
    have h1 := key ξ 1
    rw [mul_one] at h1
    rw [h1, hμ]
  · push Not at hj
    rw [apply_single_of_comm hprim hal hφ hi ξ]
    refine Prod.ext (funext fun k => ?_) rfl
    by_cases hk : k = i
    · subst hk
      simp
    · have hβk : β k ≠ β i := fun h => hj k hk h |>.elim
      simp [hk, hβk]

include hprim in
theorem commute_of_comm_blocks (hal : Aligned hζ β) {u v : Matrix.SpecialLinearGroup (Fin n) K}
    (hu : u * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * u)
    (hv : v * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * v)
    (hZu : ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε β → y ∈ zeroCoords ε β →
      u * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
        Matrix.SpecialLinearGroup.transvection hxy 1 * u)
    (hZv : ∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε β → y ∈ zeroCoords ε β →
      v * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
        Matrix.SpecialLinearGroup.transvection hxy 1 * v)
    (hcu : ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 → ∀ c : AdjoinRoot g,
      u * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
        theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * u)
    (hcv : ∀ i j (hij : i ≠ j), β i = β j → β i ≠ 0 → ∀ c : AdjoinRoot g,
      v * theta g ε (Matrix.SpecialLinearGroup.transvection hij c) =
        theta g ε (Matrix.SpecialLinearGroup.transvection hij c) * v) :
    u * v = v * u := by
  set U := (u : Matrix (Fin n) (Fin n) K) with hU
  set V := (v : Matrix (Fin n) (Fin n) K) with hV
  have hcolJ : ∀ (w : Matrix.SpecialLinearGroup (Fin n) K),
      w * SLNS.nsSL ε hC (fun i => (β i).val) = SLNS.nsSL ε hC (fun i => (β i).val) * w →
      (∀ x y (hxy : x ≠ y), x ∈ zeroCoords ε β → y ∈ zeroCoords ε β →
        w * Matrix.SpecialLinearGroup.transvection hxy (1 : K) =
          Matrix.SpecialLinearGroup.transvection hxy 1 * w) →
      ∀ x ∈ zeroCoords ε β, (w : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single x 1 =
        (w : Matrix (Fin n) (Fin n) K) x x • Pi.single x 1 := by
    intro w hw hZw x hx
    funext z
    rw [Matrix.mulVec_single_one, Matrix.col_apply, col_of_mem_zeroCoords hprim hal hw hZw hx z,
      Pi.smul_apply, Pi.single_apply, smul_eq_mul]
    split_ifs <;> simp
  have key : ∀ x, (U * V) *ᵥ Pi.single x 1 = (V * U) *ᵥ Pi.single x 1 := by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    by_cases hx : x ∈ zeroCoords ε β
    · rw [hcolJ v hv hZv x hx, hcolJ u hu hZu x hx, Matrix.mulVec_smul, Matrix.mulVec_smul,
        hcolJ v hv hZv x hx, hcolJ u hu hZu x hx, smul_smul, smul_smul, mul_comm]
    · rcases hεx : ε x with ⟨a, i⟩ | j
      · have hi : β i ≠ 0 := fun h => hx ((mem_zeroCoords_inl hεx).mpr h)
        have hxe : x = ε.symm (Sum.inl (a, i)) := by rw [← hεx, Equiv.symm_apply_apply]
        have hsu := apply_single_eq_of_comm_theta hprim hal hu hcu hi
        have hsv := apply_single_eq_of_comm_theta hprim hal hv hcv hi
        set μu := (frameForm g ε U (Pi.single i 1, 0)).1 i with hμu
        set μv := (frameForm g ε V (Pi.single i 1, 0)).1 i with hμv
        rw [hxe, ← frameCoords_single_basis, ← frameCoords_frameForm, ← frameCoords_frameForm,
          ← frameCoords_frameForm, ← frameCoords_frameForm, hsu, hsv, hsu, hsv, mul_right_comm]
      · exact absurd (mem_zeroCoords_inr hεx) hx
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext z x
  have h1 := congrFun (key x) z
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.col_apply] at h1

end CoordSL

end CFSG.StandardType
