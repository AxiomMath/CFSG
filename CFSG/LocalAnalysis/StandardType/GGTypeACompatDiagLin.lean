module

public import CFSG.LocalAnalysis.StandardType.GGTypeAFarActsVec
public import CFSG.LocalAnalysis.StandardType.GGLinearFusionCyclic
public import CFSG.LocalAnalysis.StandardType.GGTypeAEndNodeBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix

private theorem ggDiagConj_eq_conjSL_diagGL {F : Type} [Field F] {m : ℕ} (h : Fin (m + 1) → Fˣ)
    (s : SpecialLinearGroup (Fin (m + 1)) F) :
    ggDiagConj h s = InnerDiagA.conjSL (InnerDiagA.diagGL h) s := by
  apply Subtype.ext
  rw [coe_ggDiagConj, InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]

theorem ggActsVec_iff_mem_ggInducedPairs {X : Type} [Group X] {F : Type} [Field F] {m : ℕ}
    {φ : SpecialLinearGroup (Fin (m + 1)) F →* X} {g : X} {h : Fin (m + 1) → Fˣ} :
    GGActsVec φ g h ↔ (g, InnerDiagA.diagGL h) ∈ LinFusion.ggInducedPairs φ := by
  rw [LinFusion.mem_ggInducedPairs]
  constructor
  · intro hg u
    rw [← ggDiagConj_eq_conjSL_diagGL]
    exact hg u
  · intro hg s
    rw [ggDiagConj_eq_conjSL_diagGL]
    exact hg s


theorem range_slLowerBlockHom (n : ℕ) (F : Type) [Field F] :
    (slLowerBlockHom n F).range =
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase (0 : Fin (n + 1))) := by
  apply le_antisymm
  · rintro A ⟨g, rfl⟩
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    intro i j hij
    rw [coe_slLowerBlockHom]
    obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective i
    obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective j
    rw [slLowerBlockMat_apply]
    rcases p with p | p <;> rcases q with q | q
    · obtain rfl : p = q := Subsingleton.elim p q
      rw [Matrix.fromBlocks_apply₁₁, slLowerBlockEquiv_inl]
      simp [Matrix.one_apply_eq]
    · rw [Matrix.fromBlocks_apply₁₂, slLowerBlockEquiv_inl, slLowerBlockEquiv_inr]
      simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
    · rw [Matrix.fromBlocks_apply₂₁, slLowerBlockEquiv_inr, slLowerBlockEquiv_inl]
      simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
    · exfalso
      rcases hij with h | h
      · rw [slLowerBlockEquiv_inr] at h
        exact h (by simp [Fin.succ_ne_zero])
      · rw [slLowerBlockEquiv_inr] at h
        exact h (by simp [Fin.succ_ne_zero])
  · intro A hA
    set s : Matrix (Fin n) (Fin n) F := A.val.submatrix Fin.succ Fin.succ with hs
    have hmat : slLowerBlockMat n F s = A.val := by
      ext i j
      obtain ⟨p, rfl⟩ := (slLowerBlockEquiv n).surjective i
      obtain ⟨q, rfl⟩ := (slLowerBlockEquiv n).surjective j
      rw [slLowerBlockMat_apply]
      have hA' := CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hA
      rcases p with p | p <;> rcases q with q | q
      · obtain rfl : p = q := Subsingleton.elim p q
        rw [Matrix.fromBlocks_apply₁₁, slLowerBlockEquiv_inl,
          hA' 0 0 (Or.inl (by simp))]
        simp [Matrix.one_apply_eq]
      · rw [Matrix.fromBlocks_apply₁₂, slLowerBlockEquiv_inl, slLowerBlockEquiv_inr,
          hA' 0 q.succ (Or.inl (by simp))]
        simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
      · rw [Matrix.fromBlocks_apply₂₁, slLowerBlockEquiv_inr, slLowerBlockEquiv_inl,
          hA' p.succ 0 (Or.inr (by simp))]
        simp [Matrix.one_apply, Fin.succ_ne_zero, eq_comm]
      · rw [Matrix.fromBlocks_apply₂₂, slLowerBlockEquiv_inr, slLowerBlockEquiv_inr, hs,
          Matrix.submatrix_apply]
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [← det_slLowerBlockMat, hmat]
      exact A.2
    · exact Subtype.ext hmat


theorem range_slUpperBlockHom (n : ℕ) (F : Type) [Field F] :
    (slUpperBlockHom n F).range =
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase (Fin.last n)) := by
  have hl : ∀ p : Fin n, finSumFinEquiv (Sum.inl p) = p.castSucc := by
    intro p; rw [finSumFinEquiv_apply_left]; rfl
  have hr : ∀ q : Fin 1, finSumFinEquiv (Sum.inr q) = Fin.last n := by
    intro q; obtain rfl : q = 0 := Subsingleton.elim q 0
    rw [finSumFinEquiv_apply_right]; exact slBlock_natAdd_zero_eq_last
  apply le_antisymm
  · rintro A ⟨g, rfl⟩
    rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
    intro i j hij
    rw [coe_slUpperBlockHom]
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
    rw [slUpperBlockMat_apply]
    rcases p with p | p <;> rcases q with q | q
    · exfalso
      rcases hij with h | h
      · rw [hl p] at h
        exact h (Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last p, Finset.mem_univ _⟩)
      · rw [hl q] at h
        exact h (Finset.mem_erase.mpr ⟨Fin.castSucc_ne_last q, Finset.mem_univ _⟩)
    · rw [Matrix.fromBlocks_apply₁₂, hl p, hr q]
      simp [Matrix.one_apply, Fin.castSucc_ne_last, eq_comm]
    · rw [Matrix.fromBlocks_apply₂₁, hr p, hl q]
      simp [Matrix.one_apply, Fin.castSucc_ne_last, eq_comm]
    · obtain rfl : p = q := Subsingleton.elim p q
      rw [Matrix.fromBlocks_apply₂₂, hr p]
      simp [Matrix.one_apply]
  · intro A hA
    set s : Matrix (Fin n) (Fin n) F := A.val.submatrix Fin.castSucc Fin.castSucc with hs
    have hmat : slUpperBlockMat n F s = A.val := by
      ext i j
      obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
      obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
      rw [slUpperBlockMat_apply]
      have hA' := CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hA
      rcases p with p | p <;> rcases q with q | q
      · rw [Matrix.fromBlocks_apply₁₁, hl p, hl q, hs, Matrix.submatrix_apply]
      · rw [Matrix.fromBlocks_apply₁₂, hl p, hr q,
          hA' p.castSucc (Fin.last n) (Or.inr (by simp))]
        simp [Matrix.one_apply, Fin.castSucc_ne_last, eq_comm]
      · rw [Matrix.fromBlocks_apply₂₁, hr p, hl q,
          hA' (Fin.last n) q.castSucc (Or.inl (by simp))]
        simp [Matrix.one_apply, Fin.castSucc_ne_last, eq_comm]
      · obtain rfl : p = q := Subsingleton.elim p q
        rw [Matrix.fromBlocks_apply₂₂, hr p,
          hA' (Fin.last n) (Fin.last n) (Or.inr (by simp))]
        simp [Matrix.one_apply]
    refine ⟨⟨s, ?_⟩, ?_⟩
    · rw [← det_slUpperBlockMat, hmat]
      exact A.2
    · exact Subtype.ext hmat


private theorem ggDiagConj_conj_slPerm {F : Type} [Field F] (h2 : (2 : F) = 0) {m : ℕ}
    (π : Equiv.Perm (Fin m)) (h : Fin m → Fˣ) (s : SpecialLinearGroup (Fin m) F) :
    ggDiagConj h (slPerm h2 π * s * (slPerm h2 π)⁻¹) =
      slPerm h2 π * ggDiagConj (h ∘ π) s * (slPerm h2 π)⁻¹ := by
  have key := slPerm_mul_ggDiagConj h2 π (h ∘ π) s
  have hcomp : (h ∘ π) ∘ π.symm = h := by funext k; simp
  rw [hcomp] at key
  exact key.symm

private theorem blockComplProj_slPerm_swap {F : Type} [Field F] (h2 : (2 : F) = 0) {n : ℕ}
    (a r : Fin (n + 1)) :
    CFSG.SeitzReduction.LinearPilot.blockComplProj (Finset.univ.erase r) *
        ((slPerm h2 (Equiv.swap a r) : SpecialLinearGroup (Fin (n + 1)) F) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      ((slPerm h2 (Equiv.swap a r) : SpecialLinearGroup (Fin (n + 1)) F) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
        CFSG.SeitzReduction.LinearPilot.blockComplProj (Finset.univ.erase a) := by
  rw [coe_slPerm]
  ext i j
  rw [CFSG.SeitzReduction.LinearPilot.blockComplProj,
    CFSG.SeitzReduction.LinearPilot.blockComplProj, diagonal_mul, mul_diagonal,
    signedPerm_apply]
  by_cases h : i = Equiv.swap a r j
  · simp only [if_pos h, Pi.one_apply, mul_one, one_mul]
    congr 1
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    rw [h]
    apply propext
    constructor
    · intro h1 h2
      exact h1 (by rw [h2, Equiv.swap_apply_left])
    · intro h1 h2
      have := congrArg (Equiv.swap a r) h2
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      exact h1 this
  · simp only [if_neg h, Pi.one_apply, mul_zero, zero_mul]

theorem exists_lift_lowerBlock_eq {X : Type} [Group X] {F : Type} [Field F] (h2 : (2 : F) = 0)
    {n : ℕ} {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) {Bs : Subgroup X}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) (r : Fin (n + 1)) :
    ∃ φ' : SpecialLinearGroup (Fin (n + 1)) F →* X, φ'.range = φ.range ∧
      φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      (∀ b ∈ Bs, GGActsDiag φ' b) ∧
      (φ'.comp (slLowerBlockHom n F)).range =
        (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase r)).map φ := by
  set P : SpecialLinearGroup (Fin (n + 1)) F := slPerm h2 (Equiv.swap 0 r) with hP
  have hφ' : ∀ s, (φ.comp (MulAut.conj P).toMonoidHom) s = φ (P * s * P⁻¹) := by
    intro s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨φ.comp (MulAut.conj P).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨s, rfl⟩
      exact ⟨P * s * P⁻¹, (hφ' s).symm⟩
    · rintro x ⟨t, rfl⟩
      refine ⟨P⁻¹ * t * P, ?_⟩
      rw [hφ']
      congr 1
      group
  · intro s hs
    rw [Subgroup.mem_center_iff]
    intro t
    have hz : P * s * P⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := by
      apply hker
      rw [MonoidHom.mem_ker, ← hφ' s]
      exact hs
    have hzc : ∀ g, g * (P * s * P⁻¹) = (P * s * P⁻¹) * g :=
      Subgroup.mem_center_iff.mp hz
    have hs_eq : s = P * s * P⁻¹ := by
      calc s = P⁻¹ * (P * s * P⁻¹) * P := by group
        _ = (P⁻¹ * (P * s * P⁻¹)) * P := by group
        _ = ((P * s * P⁻¹) * P⁻¹) * P := by rw [hzc P⁻¹]
        _ = P * s * P⁻¹ := by group
    rw [hs_eq]
    exact hzc t
  · intro b hb
    obtain ⟨h, hh⟩ := hdiag b hb
    refine ⟨h ∘ Equiv.swap 0 r, ?_⟩
    intro s
    rw [hφ' s, hφ' (ggDiagConj (h ∘ Equiv.swap 0 r) s), hh (P * s * P⁻¹),
      ggDiagConj_conj_slPerm h2 (Equiv.swap 0 r) h s]
  · have hproj : CFSG.SeitzReduction.LinearPilot.blockComplProj (Finset.univ.erase r) *
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          CFSG.SeitzReduction.LinearPilot.blockComplProj
            (Finset.univ.erase (0 : Fin (n + 1))) := by
      rw [hP]
      exact blockComplProj_slPerm_swap h2 (0 : Fin (n + 1)) r
    have hblock : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
          (Finset.univ.erase (0 : Fin (n + 1)))).map (MulAut.conj P).toMonoidHom =
        CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase r) :=
      CFSG.SeitzReduction.LinearPilot.map_conj_blockSpecialLinear_of_mul_eq P hproj
    rw [show (φ.comp (MulAut.conj P).toMonoidHom).comp (slLowerBlockHom n F) =
          φ.comp ((MulAut.conj P).toMonoidHom.comp (slLowerBlockHom n F)) from rfl,
      MonoidHom.range_comp, MonoidHom.range_comp, range_slLowerBlockHom, hblock]


theorem exists_lift_upperBlock_eq {X : Type} [Group X] {F : Type} [Field F] (h2 : (2 : F) = 0)
    {n : ℕ} {φ : SpecialLinearGroup (Fin (n + 1)) F →* X}
    (hker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F)) {Bs : Subgroup X}
    (hdiag : ∀ b ∈ Bs, GGActsDiag φ b) (r : Fin (n + 1)) :
    ∃ φ' : SpecialLinearGroup (Fin (n + 1)) F →* X, φ'.range = φ.range ∧
      φ'.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) ∧
      (∀ b ∈ Bs, GGActsDiag φ' b) ∧
      (φ'.comp (slUpperBlockHom n F)).range =
        (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase r)).map φ := by
  set P : SpecialLinearGroup (Fin (n + 1)) F := slPerm h2 (Equiv.swap (Fin.last n) r) with hP
  have hφ' : ∀ s, (φ.comp (MulAut.conj P).toMonoidHom) s = φ (P * s * P⁻¹) := by
    intro s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨φ.comp (MulAut.conj P).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rintro x ⟨s, rfl⟩
      exact ⟨P * s * P⁻¹, (hφ' s).symm⟩
    · rintro x ⟨t, rfl⟩
      refine ⟨P⁻¹ * t * P, ?_⟩
      rw [hφ']
      congr 1
      group
  · intro s hs
    rw [Subgroup.mem_center_iff]
    intro t
    have hz : P * s * P⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) F) := by
      apply hker
      rw [MonoidHom.mem_ker, ← hφ' s]
      exact hs
    have hzc : ∀ g, g * (P * s * P⁻¹) = (P * s * P⁻¹) * g :=
      Subgroup.mem_center_iff.mp hz
    have hs_eq : s = P * s * P⁻¹ := by
      calc s = P⁻¹ * (P * s * P⁻¹) * P := by group
        _ = (P⁻¹ * (P * s * P⁻¹)) * P := by group
        _ = ((P * s * P⁻¹) * P⁻¹) * P := by rw [hzc P⁻¹]
        _ = P * s * P⁻¹ := by group
    rw [hs_eq]
    exact hzc t
  · intro b hb
    obtain ⟨h, hh⟩ := hdiag b hb
    refine ⟨h ∘ Equiv.swap (Fin.last n) r, ?_⟩
    intro s
    rw [hφ' s, hφ' (ggDiagConj (h ∘ Equiv.swap (Fin.last n) r) s), hh (P * s * P⁻¹),
      ggDiagConj_conj_slPerm h2 (Equiv.swap (Fin.last n) r) h s]
  · have hproj : CFSG.SeitzReduction.LinearPilot.blockComplProj (Finset.univ.erase r) *
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
        (P : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
          CFSG.SeitzReduction.LinearPilot.blockComplProj
            (Finset.univ.erase (Fin.last n)) := by
      rw [hP]
      exact blockComplProj_slPerm_swap h2 (Fin.last n) r
    have hblock : (CFSG.SeitzReduction.LinearPilot.blockSpecialLinear
          (Finset.univ.erase (Fin.last n))).map (MulAut.conj P).toMonoidHom =
        CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (Finset.univ.erase r) :=
      CFSG.SeitzReduction.LinearPilot.map_conj_blockSpecialLinear_of_mul_eq P hproj
    rw [show (φ.comp (MulAut.conj P).toMonoidHom).comp (slUpperBlockHom n F) =
          φ.comp ((MulAut.conj P).toMonoidHom.comp (slUpperBlockHom n F)) from rfl,
      MonoidHom.range_comp, MonoidHom.range_comp, range_slUpperBlockHom, hblock]

end CFSG.StandardType

end
