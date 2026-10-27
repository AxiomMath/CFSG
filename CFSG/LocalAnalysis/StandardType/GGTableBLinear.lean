module

public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace TableB

section Linear

variable (ι : Type) [Fintype ι] [DecidableEq ι] (K : Type) [Field K]

instance largeEvenSLGroup_normal : (LargeEvenSLGroup ι K).Normal := by
  unfold LargeEvenSLGroup
  infer_instance

variable {ι K} in
theorem map_eq_self_of_forall_eq {H : Type*} [Group H] (f : H ≃* H) {N : Subgroup H}
    (hf : ∀ n ∈ N, f n = n) : N.map f.toMonoidHom = N := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    show f n ∈ N
    rw [hf n hn]
    exact hn
  · intro hy
    exact ⟨y, hy, hf y hy⟩

theorem conjNormal_scalar_eq (A : GL ι K)
    (z : LargeEvenSLGroup ι K) (hz : z ∈ (LargeEvenScalars ι K).subgroupOf (LargeEvenSLGroup ι K)) :
    MulAut.conjNormal A z = z := by
  apply Subtype.ext
  rw [MulAut.conjNormal_apply]
  have hc : (z : GL ι K) ∈ Subgroup.center (GL ι K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact hz
  rw [(Subgroup.mem_center_iff.mp hc) A]
  group

@[expose] noncomputable def linConjAut :
    GL ι K →* MulAut (LargeEvenProj (LargeEvenSLGroup ι K)) where
  toFun A := QuotientGroup.congr _ _ (MulAut.conjNormal A)
    (map_eq_self_of_forall_eq _ (conjNormal_scalar_eq ι K A))
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    simp
  map_mul' A B := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H h =>
      show ((MulAut.conjNormal (A * B) h : LargeEvenSLGroup ι K) : LargeEvenProj _) =
        ((MulAut.conjNormal A (MulAut.conjNormal B h) : LargeEvenSLGroup ι K) :
          LargeEvenProj (LargeEvenSLGroup ι K))
      rw [map_mul, MulAut.mul_apply]

variable {ι K}

theorem linConjAut_mk (A : GL ι K) (h : LargeEvenSLGroup ι K) :
    linConjAut ι K A (h : LargeEvenProj (LargeEvenSLGroup ι K)) =
      ((MulAut.conjNormal A h : LargeEvenSLGroup ι K) : LargeEvenProj (LargeEvenSLGroup ι K)) :=
  rfl

theorem linConjAut_of_mem (S : GL ι K) (hS : S ∈ LargeEvenSLGroup ι K) :
    linConjAut ι K S =
      MulAut.conj ((⟨S, hS⟩ : LargeEvenSLGroup ι K) : LargeEvenProj (LargeEvenSLGroup ι K)) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [linConjAut_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    rfl

theorem exists_eq_linConjAut {φ : MulAut (LargeEvenProj (LargeEvenSLGroup ι K))}
    (hφ : φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup ι K)) Set.univ) :
    ∃ A : GL ι K, φ = linConjAut ι K A := by
  obtain ⟨A, -, hA⟩ := hφ
  refine ⟨A, ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    exact hA h (MulAut.conjNormal A h) (by simp [MulAut.conjNormal_apply])

theorem ggOutdiagCyclic_linear [Finite K] [Nonempty ι] :
    GGOutdiagCyclic (LargeEvenProj (LargeEvenSLGroup ι K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup ι K)) Set.univ) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨A₀, hA₀⟩ := Matrix.GeneralLinearGroup.det_surjective (n := ι) (R := K) g
  refine ⟨linConjAut ι K A₀, ?_⟩
  intro φ hφ
  obtain ⟨A, rfl⟩ := exists_eq_linConjAut hφ
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (Matrix.GeneralLinearGroup.det A))
  have hS : A * A₀ ^ (-k) ∈ LargeEvenSLGroup ι K := by
    rw [LargeEvenSLGroup, MonoidHom.mem_ker, map_mul, map_zpow, hA₀, ← hk, zpow_neg,
      mul_inv_cancel]
  have hA : A = (A * A₀ ^ (-k)) * A₀ ^ k := by group
  rw [hA, map_mul, map_zpow, linConjAut_of_mem _ hS]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, rfl⟩)
    (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ _))

end Linear

section Symplectic

variable {K : Type} [Field K]

theorem exists_scalar_mul_mem_sp {m : ℕ} {A : GL (Fin m ⊕ Fin m) K} {μ : K}
    (hA : Matrix.transpose (A : Matrix _ _ K) * LargeEvenSpForm K m * (A : Matrix _ _ K) =
      μ • LargeEvenSpForm K m) {l : K} (hl : l ≠ 0) (hμ : μ = l * l) :
    Matrix.transpose ((Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl)) * A :
        GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) * LargeEvenSpForm K m *
      ((Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl)) * A :
        GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) = LargeEvenSpForm K m := by
  have h1 : ((Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl)) * A :
      GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        l⁻¹ • (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_eq_diagonal_mul]
    rfl
  rw [h1, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, hA, hμ,
    smul_smul, smul_smul]
  have : l⁻¹ * l⁻¹ * (l * l) = 1 := by field_simp
  rw [this, one_smul]

theorem scalar_mem_center {ι : Type} [Fintype ι] [DecidableEq ι] (u : Kˣ) :
    Matrix.GeneralLinearGroup.scalar ι u ∈ Subgroup.center (GL ι K) := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨u, rfl⟩

theorem ggOutdiagCyclic_symplectic [Finite K] [CharP K 2] (m : ℕ) :
    GGOutdiagCyclic (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K m)) (LargeEvenGSpSet K m)) := by
  apply ggOutdiagCyclic_of_subset_inn
  rintro φ ⟨A, ⟨μ, hμ0, hA⟩, hφ⟩
  have := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) μ
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hμ0 (by rw [hl, zero_mul])
  set A' := Matrix.GeneralLinearGroup.scalar _ (Units.mk0 l⁻¹ (inv_ne_zero hl0)) * A with hA'
  have hA'Sp : A' ∈ LargeEvenSpGroup K m :=
    Subgroup.subset_closure (exists_scalar_mul_mem_sp hA hl0 hl)
  have hconj : ∀ h : GL (Fin m ⊕ Fin m) K, A' * h * A'⁻¹ = A * h * A⁻¹ := by
    intro h
    have hc := Subgroup.mem_center_iff.mp
      (scalar_mem_center (ι := Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0)))
    rw [hA', mul_inv_rev]
    set s := Matrix.GeneralLinearGroup.scalar (Fin m ⊕ Fin m) (Units.mk0 l⁻¹ (inv_ne_zero hl0))
    calc s * A * h * (A⁻¹ * s⁻¹) = s * (A * h * A⁻¹) * s⁻¹ := by group
      _ = (A * h * A⁻¹) * s * s⁻¹ := by rw [hc (A * h * A⁻¹)]
      _ = A * h * A⁻¹ := by group
  obtain ⟨a, ha⟩ : ∃ a : LargeEvenSpGroup K m, (a : GL (Fin m ⊕ Fin m) K) = A' :=
    ⟨⟨A', hA'Sp⟩, rfl⟩
  refine ⟨(a : LargeEvenProj (LargeEvenSpGroup K m)), ?_⟩
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    have hrel : ((a * h * a⁻¹ : LargeEvenSpGroup K m) : GL (Fin m ⊕ Fin m) K) = A * h * A⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ha]
      exact hconj h
    exact (hφ h (a * h * a⁻¹) hrel).symm

end Symplectic

end TableB

section Labels

theorem recipeLinear_outdiag {d N : ℕ} (hd : 1 ≤ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableB.ggOutdiagCyclic_linear⟩

theorem recipeOmegaPlus_outdiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggOutdiagCyclic_of_subset_inn fun _ ⟨r, hr⟩ => ⟨r, hr⟩⟩

theorem recipeOmegaMinus_outdiag {m q : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeOmegaMinus m q Q) :
    LargeEvenRecipeOmegaMinus m q fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ,
    ggOutdiagCyclic_of_subset_inn fun _ ⟨r, hr⟩ => ⟨r, hr⟩⟩

theorem recipeSuzuki_outdiag {a : ℕ} {Q : LargeEvenRawCont} (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggOutdiagCyclic_of_subset_inn fun _ ⟨r, hr⟩ => ⟨r, hr⟩⟩

theorem recipeSymplectic_outdiag {m n : ℕ} {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F => Q R I F ∧ GGOutdiagCyclic R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, TableB.ggOutdiagCyclic_symplectic m⟩

@[expose] def GGOutdiagPilotLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨
    (lab.tag = .twD ∧ lab.rank ≠ 3) ∨ lab.tag = .twB2

theorem largeEvenLabelAll_outdiag_pilot {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGOutdiagPilotLabel lab) : LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  rcases h with h | h | h | h | ⟨h, hl⟩ | h
  · dsimp only at h
    subst h
    exact recipeLinear_outdiag (by omega) hQ
  · dsimp only at h
    subst h
    exact recipeSymplectic_outdiag hQ
  · dsimp only at h
    subst h
    exact recipeSymplectic_outdiag hQ
  · dsimp only at h
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢
    · exact recipeLinear_outdiag (by omega) hQ
    · exact recipeOmegaPlus_outdiag hQ
  · dsimp only at h hl
    subst h
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ <;> first
      | exact recipeLinear_outdiag (by omega) hQ
      | exact recipeOmegaMinus_outdiag hQ
  · dsimp only at h
    subst h
    exact recipeSuzuki_outdiag hQ

theorem ggLNoncyclicInputOn_pilot : GGLNoncyclicInputOn GGOutdiagPilotLabel :=
  ggLNoncyclicInputOn_of_labels fun _ hlab h => largeEvenLabelAll_outdiag_pilot hlab h

theorem ggLNoncyclicInput_of_remaining
    (h : ∀ lab, LargeEvenInLambda2 lab → ¬ GGOutdiagPilotLabel lab →
      LargeEvenLabelAll lab fun R _ I _ => GGOutdiagCyclic R I) : GGLNoncyclicInput :=
  ggLNoncyclicInput_of_labels fun lab hlab => by
    by_cases hp : GGOutdiagPilotLabel lab
    · exact largeEvenLabelAll_outdiag_pilot hlab hp
    · exact h lab hlab hp

end Labels

end CFSG.StandardType
