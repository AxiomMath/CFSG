module

public import CFSG.LocalAnalysis.StandardType.FS81.D6ModelGen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowX1OmCFrame
public import CFSG.Monster.B.Recog.GenericTrianglePresentation

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81.D6M

open CFSG.SeitzReduction.OmegaPilot CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC
open QuadraticMap
open scoped Matrix

@[expose] def pol (u v : V12) : ZMod 2 :=
  ∑ k, (u (Sum.inl k) * v (Sum.inr k) + v (Sum.inl k) * u (Sum.inr k))

theorem Q12_eq_sum (v : V12) : Q12 v = ∑ i, v (Sum.inl i) * v (Sum.inr i) :=
  CFSG.LieType.Universal.Spin.quadPlus_apply 6 (ZMod 2) v

theorem polar_Q12_eq (u v : V12) : polar Q12 u v = pol u v := by
  rw [CFSG.LieType.Universal.Spin.polar_quadPlus]
  rfl

@[expose] def rotMat (i : Fin 6) : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2) :=
  Matrix.of fun y x =>
    (Pi.single x 1 : V12) y
      + (pol (Pi.single x 1) (framePair i).1 + pol (Pi.single x 1) (framePair i).2)
        * (framePair i).1 y
      + pol (Pi.single x 1) (framePair i).2 * (framePair i).2 y

@[expose] def rotGL (i : Fin 6) : GL (Fin 6 ⊕ Fin 6) (ZMod 2) :=
  ⟨rotMat i, rotMat i * rotMat i, by revert i; decide +kernel,
    by revert i; decide +kernel⟩

theorem coe_rotGL (i : Fin 6) :
    ((rotGL i : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))
      = rotMat i := rfl

theorem coe_rotGL_inv (i : Fin 6) :
    (((rotGL i)⁻¹ : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :
      Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) = rotMat i * rotMat i := rfl

theorem coe_conj_rotGL_genGL (i : Fin 6) {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    ((rotGL i * genGL hab P * (rotGL i)⁻¹ : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :
      Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))
      = rotMat i * genMat a b P * (rotMat i * rotMat i) := by
  rw [Units.val_mul, Units.val_mul, coe_genGL, coe_rotGL_inv, coe_rotGL]

theorem lin_injective : Function.Injective lin :=
  (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 6 ⊕ Fin 6) (ZMod 2)).injective

theorem frameRot_eq_lin_rotGL (i : Fin 6) : frameRot i = lin (rotGL i) := by
  have hp : MinusPair Q12 (framePair i).1 (framePair i).2 :=
    ⟨by rw [Q12_eq_sum]; revert i; decide +kernel,
     by rw [Q12_eq_sum]; revert i; decide +kernel,
     by rw [polar_Q12_eq]; revert i; decide +kernel⟩
  refine LinearEquiv.toLinearMap_injective ?_
  refine (Pi.basisFun (ZMod 2) (Fin 6 ⊕ Fin 6)).ext fun j => ?_
  rw [Pi.basisFun_apply]
  show rot Q12 (framePair i).1 (framePair i).2 (Pi.single j 1) = lin (rotGL i) (Pi.single j 1)
  rw [rot_apply hp]
  simp only [lin, MulEquiv.coe_toMonoidHom,
    CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply, Matrix.mulVec_single_one]
  funext y
  rw [Matrix.col_apply, coe_rotGL]
  simp only [rotMat, Matrix.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, polar_Q12_eq]

theorem minusPair_framePair (i : Fin 6) : MinusPair Q12 (framePair i).1 (framePair i).2 :=
  ⟨by rw [Q12_eq_sum]; revert i; decide +kernel,
   by rw [Q12_eq_sum]; revert i; decide +kernel,
   by rw [polar_Q12_eq]; revert i; decide +kernel⟩

theorem pairPerp_framePair {i j : Fin 6} (hij : i ≠ j) :
    PairPerp Q12 (framePair i) (framePair j) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [polar_Q12_eq] <;> revert i j <;> decide +kernel

theorem pairPerp_of_mem_map {i : Fin 6} {l : List (Fin 6)} (h : ∀ j ∈ l, i ≠ j) :
    ∀ q ∈ l.map framePair, PairPerp Q12 (framePair i) q := by
  intro q hq
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hq
  exact pairPerp_framePair (h j hj)

theorem framePair_mem_frameList (i : Fin 6) : framePair i ∈ frameList := by
  rw [frameList]
  exact List.mem_ofFn.2 ⟨i, rfl⟩

theorem lin_mul_self {u : GL (Fin 6 ⊕ Fin 6) (ZMod 2)}
    (h : (u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))
      * (u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) = 1) :
    lin u * lin u = 1 := by
  have hu : u * u = 1 := Units.ext (by rw [Units.val_mul, Units.val_one]; exact h)
  calc lin u * lin u = lin (u * u) := (map_mul lin u u).symm
    _ = 1 := by rw [hu, map_one]

theorem lin_pow_three {u v : GL (Fin 6 ⊕ Fin 6) (ZMod 2)}
    (h : ((u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))
      * (v : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2))) ^ 3 = 1) :
    (lin u * lin v) ^ 3 = 1 := by
  have huv : (u * v) ^ 3 = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
    exact h
  calc (lin u * lin v) ^ 3 = (lin (u * v)) ^ 3 := by rw [map_mul]
    _ = lin ((u * v) ^ 3) := (map_pow lin (u * v) 3).symm
    _ = 1 := by rw [huv, map_one]

theorem lin_ne_one {u : GL (Fin 6 ⊕ Fin 6) (ZMod 2)} (h : u ≠ 1) : lin u ≠ 1 := by
  intro hu
  rw [← map_one lin] at hu
  exact h (lin_injective hu)

theorem genMat_word_mul {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) :
    ((genGL hab P : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :
        Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) *
      ((genGL hab.symm P : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :
        Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) *
      ((genGL hab P : GL (Fin 6 ⊕ Fin 6) (ZMod 2)) :
        Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) =
      genMat a b P * genMat b a P * genMat a b P := by
  simp only [coe_genGL]

theorem lin_mem_closure_of_mat {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6))
    {M : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)}
    (hM : M = 1 ∨ M = genMat a b P ∨ M = genMat b a P ∨
      M = genMat a b P * genMat b a P ∨ M = genMat b a P * genMat a b P ∨
      M = genMat a b P * genMat b a P * genMat a b P)
    {u : GL (Fin 6 ⊕ Fin 6) (ZMod 2)}
    (hu : (u : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) (ZMod 2)) = M) :
    lin u ∈ Subgroup.closure {lin (genGL hab P), lin (genGL hab.symm P)} := by
  rcases hM with h | h | h | h | h | h
  · have hu1 : u = 1 := Units.ext (by simp only [hu, h, Units.val_one])
    rw [hu1, map_one]
    exact Subgroup.one_mem _
  · have hu1 : u = genGL hab P := Units.ext (by simp only [hu, h, coe_genGL])
    rw [hu1]
    exact Subgroup.subset_closure (Set.mem_insert _ _)
  · have hu1 : u = genGL hab.symm P := Units.ext (by simp only [hu, h, coe_genGL])
    rw [hu1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · have hu1 : u = genGL hab P * genGL hab.symm P :=
      Units.ext (by simp only [hu, h, Units.val_mul, coe_genGL])
    rw [hu1, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  · have hu1 : u = genGL hab.symm P * genGL hab P :=
      Units.ext (by simp only [hu, h, Units.val_mul, coe_genGL])
    rw [hu1, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
      (Subgroup.subset_closure (Set.mem_insert _ _))
  · have hu1 : u = genGL hab P * genGL hab.symm P * genGL hab P :=
      Units.ext (by simp only [hu, h, Units.val_mul, genMat_word_mul])
    rw [hu1, map_mul, map_mul]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)))
      (Subgroup.subset_closure (Set.mem_insert _ _))

theorem conj_rootL_mem {a b : Fin 6} (hab : a ≠ b) (P : Finset (Fin 6)) (i : Fin 6)
    (h1 : rotMat i * genMat a b P * (rotMat i * rotMat i) = 1 ∨
      rotMat i * genMat a b P * (rotMat i * rotMat i) = genMat a b P ∨
      rotMat i * genMat a b P * (rotMat i * rotMat i) = genMat b a P ∨
      rotMat i * genMat a b P * (rotMat i * rotMat i) = genMat a b P * genMat b a P ∨
      rotMat i * genMat a b P * (rotMat i * rotMat i) = genMat b a P * genMat a b P ∨
      rotMat i * genMat a b P * (rotMat i * rotMat i) =
        genMat a b P * genMat b a P * genMat a b P)
    (h2 : rotMat i * genMat b a P * (rotMat i * rotMat i) = 1 ∨
      rotMat i * genMat b a P * (rotMat i * rotMat i) = genMat a b P ∨
      rotMat i * genMat b a P * (rotMat i * rotMat i) = genMat b a P ∨
      rotMat i * genMat b a P * (rotMat i * rotMat i) = genMat a b P * genMat b a P ∨
      rotMat i * genMat b a P * (rotMat i * rotMat i) = genMat b a P * genMat a b P ∨
      rotMat i * genMat b a P * (rotMat i * rotMat i) =
        genMat a b P * genMat b a P * genMat a b P) :
    ∀ z ∈ rootL {a, b} P, frameRot i * z * (frameRot i)⁻¹ ∈ rootL {a, b} P := by
  intro z hz
  rw [rootL_eq_closure hab P] at hz ⊢
  refine CFSG.Glauberman.conj_mem_closure (frameRot i) z hz ?_
  intro w hw
  rcases hw with rfl | rfl
  · rw [frameRot_eq_lin_rotGL i, ← map_inv, ← map_mul, ← map_mul]
    exact lin_mem_closure_of_mat hab P h1 (coe_conj_rotGL_genGL i hab P)
  · rw [frameRot_eq_lin_rotGL i, ← map_inv, ← map_mul, ← map_mul]
    exact lin_mem_closure_of_mat hab P h2 (coe_conj_rotGL_genGL i hab.symm P)

theorem node_zero : node 0 = rootL ({0, 1} : Finset (Fin 6)) ∅ := by
  unfold node
  rw [show plusNodeSet 6 0 = ({0, 1} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 0 = (∅ : Finset (Fin 6)) from by decide]

theorem node_two : node 2 = rootL ({2, 3} : Finset (Fin 6)) ∅ := by
  unfold node
  rw [show plusNodeSet 6 2 = ({2, 3} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 2 = (∅ : Finset (Fin 6)) from by decide]

theorem node_four : node 4 = rootL ({4, 5} : Finset (Fin 6)) ∅ := by
  unfold node
  rw [show plusNodeSet 6 4 = ({4, 5} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 4 = (∅ : Finset (Fin 6)) from by decide]

theorem node_five : node 5 = rootL ({4, 5} : Finset (Fin 6)) {5} := by
  unfold node
  rw [show plusNodeSet 6 5 = ({4, 5} : Finset (Fin 6)) from by decide,
    show plusNodeFlip 6 5 = ({5} : Finset (Fin 6)) from by decide]

theorem frameRot_conj_node0 (i : Fin 6) :
    ∀ z ∈ node 0, frameRot i * z * (frameRot i)⁻¹ ∈ node 0 := by
  rw [node_zero]
  exact conj_rootL_mem (by decide) ∅ i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem frameRot_conj_node2 (i : Fin 6) :
    ∀ z ∈ node 2, frameRot i * z * (frameRot i)⁻¹ ∈ node 2 := by
  rw [node_two]
  exact conj_rootL_mem (by decide) ∅ i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem frameRot_conj_node4 (i : Fin 6) :
    ∀ z ∈ node 4, frameRot i * z * (frameRot i)⁻¹ ∈ node 4 := by
  rw [node_four]
  exact conj_rootL_mem (by decide) ∅ i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem frameRot_conj_node5 (i : Fin 6) :
    ∀ z ∈ node 5, frameRot i * z * (frameRot i)⁻¹ ∈ node 5 := by
  rw [node_five]
  exact conj_rootL_mem (by decide) {5} i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem frameRot_conj_flip0 (i : Fin 6) :
    ∀ z ∈ flip0, frameRot i * z * (frameRot i)⁻¹ ∈ flip0 := by
  exact conj_rootL_mem (by decide) {1} i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem frameRot_conj_flip2 (i : Fin 6) :
    ∀ z ∈ flip2, frameRot i * z * (frameRot i)⁻¹ ∈ flip2 := by
  exact conj_rootL_mem (by decide) {3} i (by revert i; decide +kernel)
    (by revert i; decide +kernel)

theorem exists_inv_of_mem_closure_pair {G : Type*} [Group G] {g₁ g₂ : G}
    (h₁ : g₁ * g₁ = 1) (h₂ : g₂ * g₂ = 1) (h₃ : (g₁ * g₂) ^ 3 = 1)
    (hne : g₁ * g₂ ≠ 1) {h : G} (hh : h ∈ Subgroup.closure ({g₁, g₂} : Set G))
    (hh1 : h ≠ 1) (hh3 : h ^ 3 = 1) :
    ∃ s ∈ Subgroup.closure ({g₁, g₂} : Set G), s * s = 1 ∧ s * h * s⁻¹ = h⁻¹ ∧
      Subgroup.closure ({g₁, g₂} : Set G) = Subgroup.closure ({h, s} : Set G) := by
  have hinv₁ : g₁⁻¹ = g₁ := inv_eq_of_mul_eq_one_right h₁
  have hinv₂ : g₂⁻¹ = g₂ := inv_eq_of_mul_eq_one_right h₂
  have key : ∀ x : G, x * x = 1 → x ^ 3 = 1 → x = 1 := by
    intro x hx2 hx3
    have hx : x ^ 3 = x := by simp [pow_succ, pow_two, hx2]
    rwa [hx] at hx3
  obtain ⟨k, hk⟩ := CFSG.Monster.B.Recog.mem_range_six
    (by rw [pow_two]; exact h₁) (by rw [pow_two]; exact h₂) h₃ hh
  fin_cases k
  · simp at hk
    exact absurd hk.symm hh1
  · simp at hk
    exact absurd (key h (by rw [← hk]; exact h₁) hh3) hh1
  · simp at hk
    exact absurd (key h (by rw [← hk]; exact h₂) hh3) hh1
  ·
    simp at hk
    have hh_eq : h = g₁ * g₂ := hk.symm
    refine ⟨g₁, Subgroup.subset_closure (Set.mem_insert _ _), h₁, ?_, ?_⟩
    · rw [hh_eq]
      have hl : g₁ * (g₁ * g₂) * g₁⁻¹ = g₂ * g₁ := by
        rw [hinv₁]
        calc g₁ * (g₁ * g₂) * g₁ = (g₁ * g₁) * (g₂ * g₁) := by group
          _ = g₂ * g₁ := by rw [h₁, one_mul]
      have hr : (g₁ * g₂)⁻¹ = g₂ * g₁ := by rw [mul_inv_rev, hinv₁, hinv₂]
      rw [hl, hr]
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx]
          exact Subgroup.subset_closure (by simp)
        · rw [hx]
          have hg : g₂ = g₁ * h := by
            rw [hh_eq]
            symm
            calc g₁ * (g₁ * g₂) = (g₁ * g₁) * g₂ := by group
              _ = g₂ := by rw [h₁, one_mul]
          rw [hg]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx]
          exact hh
        · rw [hx]
          exact Subgroup.subset_closure (by simp)
  ·
    simp at hk
    have hh_eq : h = g₂ * g₁ := hk.symm
    refine ⟨g₁, Subgroup.subset_closure (Set.mem_insert _ _), h₁, ?_, ?_⟩
    · rw [hh_eq]
      have hl : g₁ * (g₂ * g₁) * g₁⁻¹ = g₁ * g₂ := by
        rw [hinv₁]
        calc g₁ * (g₂ * g₁) * g₁ = g₁ * g₂ * (g₁ * g₁) := by group
          _ = g₁ * g₂ := by rw [h₁, mul_one]
      have hr : (g₂ * g₁)⁻¹ = g₁ * g₂ := by rw [mul_inv_rev, hinv₁, hinv₂]
      rw [hl, hr]
    · apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx]
          exact Subgroup.subset_closure (by simp)
        · rw [hx]
          have hg : g₂ = h * g₁ := by
            rw [hh_eq]
            symm
            calc (g₂ * g₁) * g₁ = g₂ * (g₁ * g₁) := by group
              _ = g₂ := by rw [h₁, mul_one]
          rw [hg]
          exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
      · rw [Subgroup.closure_le]
        rintro x (hx | hx)
        · rw [hx]
          exact hh
        · rw [hx]
          exact Subgroup.subset_closure (by simp)
  ·
    simp at hk
    have hinv : (g₁ * g₂ * g₁) * (g₁ * g₂ * g₁) = 1 := by
      calc (g₁ * g₂ * g₁) * (g₁ * g₂ * g₁) = g₁ * g₂ * (g₁ * g₁) * g₂ * g₁ := by group
        _ = g₁ * g₂ * g₂ * g₁ := by rw [h₁, mul_one]
        _ = g₁ * (g₂ * g₂) * g₁ := by group
        _ = 1 := by rw [h₂, mul_one, h₁]
    exact absurd (key h (by rw [← hk]; exact hinv) hh3) hh1

end CFSG.StandardType.FrameRoute.FS81.D6M
