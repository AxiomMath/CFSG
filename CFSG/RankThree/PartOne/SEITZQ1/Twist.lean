module

public import CFSG.RankThree.PartOne.SEITZQ1.Roots
public import CFSG.RankThree.PartOne.KLR.TwistClosure
public import CFSG.RankThree.PartOne.KLR.A1Swap

public noncomputable section

namespace CFSG.RankThree.PartOne.SEITZQ1

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR
open CFSG.LieType.Steinberg.Adjoint (iform iform_add_left iform_add_right iform_smul_left iform_comm)

open scoped MatrixGroups

variable {L : Type} [Field L]

section Transvections

theorem transpose_transvection {i j : Fin 3} (hij : i ≠ j) (c : L) :
    (Matrix.SpecialLinearGroup.transvection hij c).transpose =
      Matrix.SpecialLinearGroup.transvection hij.symm c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single]

theorem inv_transvection {i j : Fin 3} (hij : i ≠ j) (c : L) :
    (Matrix.SpecialLinearGroup.transvection hij c)⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij (-c) := by
  rw [inv_eq_iff_mul_eq_one]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection,
    (CFSG.LinearGroups.elementary_matrix_identities hij).2.1, add_neg_cancel]
  simp

theorem map_transvection {i j : Fin 3} (hij : i ≠ j) (f : L →+* L) (c : L) :
    Matrix.SpecialLinearGroup.map f (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij (f c) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection, RingHom.mapMatrix_apply]
  ext k l
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

@[expose] def q1Tr (Fr : L →+* L) : SL(3, L) →* SL(3, L) where
  toFun g := ((Matrix.SpecialLinearGroup.map Fr g).transpose)⁻¹
  map_one' := by
    rw [map_one, inv_eq_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_one,
      Matrix.transpose_one]
  map_mul' g h := by
    rw [map_mul, ← _root_.mul_inv_rev]
    congr 1
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul,
      Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose]

theorem q1Tr_apply (Fr : L →+* L) (g : SL(3, L)) :
    q1Tr Fr g = ((Matrix.SpecialLinearGroup.map Fr g).transpose)⁻¹ :=
  rfl

theorem q1Tr_transvection [CharP L 2] (Fr : L →+* L) {i j : Fin 3} (hij : i ≠ j) (c : L) :
    q1Tr Fr (Matrix.SpecialLinearGroup.transvection hij c) =
      Matrix.SpecialLinearGroup.transvection hij.symm (Fr c) := by
  rw [q1Tr_apply, map_transvection, transpose_transvection, inv_transvection, CharTwo.neg_eq]

theorem mem_closure_image_elementary {M : Type*} [Group M] (f : SL(3, L) →* M) (g : SL(3, L)) :
    f g ∈ Subgroup.closure (f '' CFSG.LinearGroups.elementarySet 3 L) := by
  rw [← MonoidHom.map_closure, CFSG.LinearGroups.special_linear_elementary_generation]
  exact ⟨g, Subgroup.mem_top g, rfl⟩

end Transvections

section Twist

variable [CharP L 2] {a : ℕ} {F : MulAut (adjointGroup ReeTag.F4.tag L)}

@[expose] def q1N (L : Type) [Field L] (a : ℕ) : ModGL ReeTag.F4.tag L :=
  canonicalRep (coxeterSystem ReeTag.F4.tag) L (q1W (q1Par a))

omit [CharP L 2] in
theorem q1N_mem_adjoint : q1N L a ∈ adjointGroup ReeTag.F4.tag L :=
  canonicalRep_mem_adjointGroup _ L _

theorem q1N_permAct : PermAct (q1N L a) (q1W (q1Par a)) :=
  permAct_canonicalRep _

theorem rootExp_q1Sig (a : ℕ) {i j : Fin 3} (hij : i ≠ j) : rootExp a (q1Sig i j) = 2 ^ a := by
  rw [rootExp, quadForm_q1Sig i j hij]
  norm_num

theorem rootExp_q1Tau (a : ℕ) {i j : Fin 3} (hij : i ≠ j) :
    rootExp a (q1Tau (q1Par a) i j) = 2 ^ (a + 1) := by
  rw [rootExp, quadForm_q1Tau (q1Par_cases a) i j hij]
  simp

theorem isRoot_q1Tau {s : Fin ReeTag.F4.tag.rank} {i j : Fin 3} (hij : i ≠ j) :
    IsRoot ReeTag.F4.tag (q1Tau s i j) :=
  IsRoot.smul (ReeTag.isRoot_dualRoot (isRoot_q1Sig hij)) (q1W s)

theorem q1Psi_sig (hF : IsReeFrob a F) {i j : Fin 3} (hij : i ≠ j) (t : L) :
    twistMap F (q1N L a) (pinnedX ReeTag.F4.tag L (q1Sig i j) t) =
      pinnedX ReeTag.F4.tag L (q1Tau (q1Par a) i j) (t ^ 2 ^ a) := by
  unfold twistMap
  rw [hF.twist_pinnedX q1N_permAct (isRoot_q1Sig hij) t, rootExp_q1Sig a hij]
  rfl

theorem q1Psi_tau (hF : IsReeFrob a F) {i j : Fin 3} (hij : i ≠ j) (t : L) :
    twistMap F (q1N L a) (pinnedX ReeTag.F4.tag L (q1Tau (q1Par a) i j) t) =
      pinnedX ReeTag.F4.tag L (q1Sig j i) (t ^ 2 ^ (a + 1)) := by
  unfold twistMap
  rw [hF.twist_pinnedX q1N_permAct (isRoot_q1Tau hij) t, rootExp_q1Tau a hij,
    q1W_dualRoot_q1Tau (q1Par_cases a) i j hij]

omit [CharP L 2] in
theorem q1Rho_mem_adjoint (g : SL(3, L)) : q1Rho L g ∈ adjointGroup ReeTag.F4.tag L := by
  have hsub : subsystemGroup Tag.F4 L f4LongSupport ≤ adjointGroup Tag.F4 L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, -, c, rfl | rfl⟩
    exacts [xUnit_mem_adjointGroup i c, yUnit_mem_adjointGroup i c]
  have h1 : f4rhoLongR L g ∈ adjointGroup ReeTag.F4.tag L := hsub (f4rhoLong_mem g)
  exact mul_mem (mul_mem (canonicalRep_mem_adjointGroup _ L _) h1)
    (inv_mem (canonicalRep_mem_adjointGroup _ L _))

@[expose] def q1PsiRho (F : MulAut (adjointGroup ReeTag.F4.tag L)) (a : ℕ) :
    SL(3, L) →* ModGL ReeTag.F4.tag L where
  toFun g := twistMap F (q1N L a) (q1Rho L g)
  map_one' := by rw [map_one, twistMap_one]
  map_mul' g h := by rw [map_mul, twistMap_mul _ (q1Rho_mem_adjoint g) (q1Rho_mem_adjoint h)]

omit [CharP L 2] in
theorem q1PsiRho_apply (g : SL(3, L)) : q1PsiRho F a g = twistMap F (q1N L a) (q1Rho L g) :=
  rfl

omit [CharP L 2] in
theorem q1PsiRho_mem_adjoint (g : SL(3, L)) : q1PsiRho F a g ∈ adjointGroup ReeTag.F4.tag L :=
  twistMap_mem_adjoint q1N_mem_adjoint (q1Rho_mem_adjoint g)

theorem q1PsiRho_transvection (hF : IsReeFrob a F) {i j : Fin 3} (hij : i ≠ j) (t : L) :
    q1PsiRho F a (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX ReeTag.F4.tag L (q1Tau (q1Par a) i j) (t ^ 2 ^ a) := by
  rw [q1PsiRho_apply, q1Rho_transvection i j hij, q1Psi_sig hF hij]

omit [CharP L 2] in
theorem commute_pinnedX_of_long_orthogonal {α β : Fin ReeTag.F4.tag.rank → ℤ}
    (hα : IsRoot ReeTag.F4.tag α) (hβ : IsRoot ReeTag.F4.tag β)
    (hαl : ReeTag.F4.quadForm α = 4) (hαβ : iform (τ := ReeTag.F4.tag) α β = 0) (c d : L) :
    Commute (pinnedX ReeTag.F4.tag L α c) (pinnedX ReeTag.F4.tag L β d) := by
  have hq : ∀ γ : Fin ReeTag.F4.tag.rank → ℤ, ReeTag.F4.quadForm γ = iform γ γ := by
    intro γ
    simp only [ReeTag.quadForm, iform, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hG : CFSG.LieType.Steinberg.Adjoint.NoG2 ReeTag.F4.tag :=
    CFSG.LieType.Steinberg.Adjoint.noG2_F4
  have hβq := CFSG.LieType.Steinberg.Adjoint.iform_self_cases hG hβ
  have hαq : iform (τ := ReeTag.F4.tag) α α = 4 := by rw [← hq]; exact hαl
  have hneg : iform (τ := ReeTag.F4.tag) (-β) β = -iform (τ := ReeTag.F4.tag) β β := by
    rw [show -β = (-1 : ℤ) • β by simp, iform_smul_left]
    ring
  refine commute_pinnedX_of_forall_not_isRoot L hα hβ ?_ ?_ ?_ c d
  · rintro rfl
    rw [hαq] at hαβ
    norm_num at hαβ
  · rintro rfl
    rw [hneg] at hαβ
    rcases hβq with h | h <;> rw [h] at hαβ <;> norm_num at hαβ
  · intro x y hx hy hr
    have h := CFSG.LieType.Steinberg.Adjoint.iform_self_cases hG hr
    rw [CFSG.LieType.Steinberg.Adjoint.iform_nsmul_add_nsmul, hαq, hαβ] at h
    have hx1 : (1 : ℤ) ≤ x := by exact_mod_cast hx
    have hy1 : (1 : ℤ) ≤ y := by exact_mod_cast hy
    rcases hβq with hb | hb <;> rw [hb] at h <;> rcases h with h | h <;> nlinarith

theorem q1PsiRho_commute (hF : IsReeFrob a F) (g h : SL(3, L)) :
    q1Rho L g * q1PsiRho F a h = q1PsiRho F a h * q1Rho L g := by
  refine commute_of_closure ?_ _ (mem_closure_image_elementary _ g) _
    (mem_closure_image_elementary _ h)
  rintro _ ⟨_, ⟨i, j, hij, c, rfl⟩, rfl⟩ _ ⟨_, ⟨k, l, hkl, d, rfl⟩, rfl⟩
  rw [q1Rho_transvection i j hij, q1PsiRho_transvection hF hkl]
  exact (commute_pinnedX_of_long_orthogonal (isRoot_q1Sig hij) (isRoot_q1Tau hkl)
    (quadForm_q1Sig i j hij) (iform_q1Sig_q1Tau (q1Par_cases a) i j k l hij hkl) _ _).eq

@[expose] def q1PsiPsiRho (F : MulAut (adjointGroup ReeTag.F4.tag L)) (a : ℕ) :
    SL(3, L) →* ModGL ReeTag.F4.tag L where
  toFun g := twistMap F (q1N L a) (q1PsiRho F a g)
  map_one' := by rw [map_one, twistMap_one]
  map_mul' g h := by
    rw [map_mul, twistMap_mul _ (q1PsiRho_mem_adjoint g) (q1PsiRho_mem_adjoint h)]

theorem q1Psi_psiRho (hF : IsReeFrob a F) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ (2 * a + 1))
    (g : SL(3, L)) :
    twistMap F (q1N L a) (q1PsiRho F a g) = q1Rho L (q1Tr Fr g) := by
  have h : q1PsiPsiRho F a = (q1Rho L).comp (q1Tr Fr) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    show twistMap F (q1N L a) (q1PsiRho F a _) = q1Rho L (q1Tr Fr _)
    rw [q1PsiRho_transvection hF hij, q1Psi_tau hF hij, q1Tr_transvection Fr hij,
      q1Rho_transvection j i hij.symm, hFr, ← pow_mul, ← pow_add]
    congr 2
    ring
  exact DFunLike.congr_fun h g

@[expose] def q1Psi0 (hF : IsReeFrob a F) : SL(3, L) →* ModGL ReeTag.F4.tag L where
  toFun g := q1Rho L g * q1PsiRho F a g
  map_one' := by rw [map_one, map_one, one_mul]
  map_mul' g h := by
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (q1Rho L h), q1PsiRho_commute hF h g, mul_assoc]

theorem q1Psi0_apply (hF : IsReeFrob a F) (g : SL(3, L)) :
    q1Psi0 hF g = q1Rho L g * q1PsiRho F a g :=
  rfl

theorem q1Psi0_mem_adjoint (hF : IsReeFrob a F) (g : SL(3, L)) :
    q1Psi0 hF g ∈ adjointGroup ReeTag.F4.tag L :=
  mul_mem (q1Rho_mem_adjoint g) (q1PsiRho_mem_adjoint g)

theorem q1Psi0_fixed (hF : IsReeFrob a F) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ 2 ^ (2 * a + 1))
    {g : SL(3, L)} (hg : q1Tr Fr g = g) :
    twistMap F (q1N L a) (q1Psi0 hF g) = q1Psi0 hF g := by
  rw [q1Psi0_apply, twistMap_mul _ (q1Rho_mem_adjoint g) (q1PsiRho_mem_adjoint g),
    q1Psi_psiRho hF Fr hFr, hg, ← q1PsiRho_apply, q1PsiRho_commute hF g g]

theorem q1Psi0_mem_twistedFixed (hF : IsReeFrob a F) (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ 2 ^ (2 * a + 1)) {g : SL(3, L)} (hg : q1Tr Fr g = g) :
    q1Psi0 hF g ∈ twistedFixed F (q1N L a) :=
  ⟨q1Psi0_mem_adjoint hF g, q1Psi0_fixed hF Fr hFr hg⟩

end Twist

end CFSG.RankThree.PartOne.SEITZQ1
