module

public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionSp
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.LieKnownR2.Geo

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.StandardType CFSG.StandardType.ClassicalPosition
  TauCeti.GLSymplecticFin

private theorem J_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem J_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      fromBlocks 0 1 (-1) 0 = 1 := by
  rw [fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem J_mulVec_single {n : ℕ} {F : Type} [Field F] [CharP F 2] (b : Fin n ⊕ Fin n) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single b 1 =
      Pi.single b.swap 1 := by
  ext k
  rcases b with i | i <;> rcases k with k | k <;>
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem vecMul_J {n : ℕ} {F : Type} [Field F] [CharP F 2] (v : Fin n ⊕ Fin n → F) :
    v ᵥ* (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v := by
  have h := Matrix.vecMul_transpose
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v
  rwa [J_transpose] at h

private theorem mat_isSp {n : ℕ} {F : Type} [Field F] (u : StatedSp n F) :
    (mat n F u)ᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      mat n F u = fromBlocks 0 1 (-1) 0 :=
  (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2

private theorem mat_inv_eq {n : ℕ} {F : Type} [Field F] [CharP F 2] (u : StatedSp n F) :
    mat n F u⁻¹ = (fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (mat n F u)ᵀ * fromBlocks 0 1 (-1) 0 := by
  have h1 : mat n F u * mat n F u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have h2 : ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (mat n F u)ᵀ * fromBlocks 0 1 (-1) 0) * mat n F u = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ (fromBlocks 0 1 (-1) 0),
      mat_isSp, J_mul_self]
  exact (left_inv_eq_right_inv h2 h1).symm

private theorem conj_single {n : ℕ} {F : Type} [Field F] [CharP F 2] (u : StatedSp n F)
    (a b : Fin n ⊕ Fin n) (c : F) :
    mat n F u * (c • Matrix.single a b (1 : F)) * mat n F u⁻¹ =
      c • vecMulVec (mat n F u *ᵥ Pi.single a 1)
        ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          (mat n F u *ᵥ Pi.single b.swap 1)) := by
  rw [mat_inv_eq, Matrix.mul_smul, Matrix.smul_mul, single_eq_single_vecMulVec_single,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  congr 2
  rw [← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, vecMul_J (Pi.single b 1), J_mulVec_single,
    Matrix.vecMul_transpose, vecMul_J]

private theorem conj_single_add {n : ℕ} {F : Type} [Field F] [CharP F 2] (u : StatedSp n F)
    (a b a' b' : Fin n ⊕ Fin n) (c : F) :
    mat n F u * (c • (Matrix.single a b (1 : F) + Matrix.single a' b' 1)) * mat n F u⁻¹ =
      c • (vecMulVec (mat n F u *ᵥ Pi.single a 1)
          ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
            (mat n F u *ᵥ Pi.single b.swap 1)) +
        vecMulVec (mat n F u *ᵥ Pi.single a' 1)
          ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
            (mat n F u *ᵥ Pi.single b'.swap 1))) := by
  rw [smul_add, Matrix.mul_add, Matrix.add_mul, conj_single, conj_single, smul_add]

private theorem pairing {n : ℕ} {F : Type} [Field F] (u : StatedSp n F)
    (x y : Fin n ⊕ Fin n → F) :
    (mat n F u *ᵥ x) ⬝ᵥ ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
      (mat n F u *ᵥ y)) =
        x ⬝ᵥ ((fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, mat_isSp, dotProduct_comm]

private theorem single_dot_J_single {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (a b : Fin n ⊕ Fin n) :
    (Pi.single a 1 : Fin n ⊕ Fin n → F) ⬝ᵥ ((fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single b 1) =
        if a = b.swap then 1 else 0 := by
  rw [J_mulVec_single, dotProduct_single, Pi.single_apply]
  simp [eq_comm]

private theorem map_conj_rootGroup {n : ℕ} {F : Type} [Field F] {γ : Fin n → ℤ}
    {r : RootSubgroupIndex n} (hr : stdVec r = toStd n γ) (u : StatedSp n F)
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    (h : ∀ c : F, mat n F u * (c • E F r) * mat n F u⁻¹ = c • M) :
    ((rootGroup n F γ).map (MulAut.conj u).toMonoidHom).map (StatedSp n F).subtype =
      Subgroup.closure {g : GL (Fin n ⊕ Fin n) F |
        ∃ c : F, (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • M} := by
  have key : ∀ c : F, mat n F (u * elt r c * u⁻¹) = 1 + c • M := by
    intro c
    have h1 : mat n F u * mat n F u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    rw [map_mul, map_mul, mat_elt, mul_add, add_mul, Matrix.mul_one, h1, h c]
  apply le_antisymm
  · rintro g ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hr).1 hx
    exact Subgroup.subset_closure ⟨c, key c⟩
  · rw [Subgroup.closure_le]
    rintro g ⟨c, hc⟩
    exact ⟨u * elt r c * u⁻¹, ⟨elt r c, (mem_rootGroup_iff hr).2 ⟨c, rfl⟩, rfl⟩,
      Units.ext ((key c).trans hc.symm)⟩

private theorem allEven_stdVec_positiveLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.positiveLong i)) := by
  intro a
  simp only [stdVec, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem allEven_stdVec_negativeLong {n : ℕ} (i : Fin n) :
    GGRootSp.AllEven (stdVec (.negativeLong i)) := by
  intro a
  simp only [stdVec, Pi.neg_apply, Pi.smul_apply, Pi.single_apply]
  split_ifs <;> simp

private theorem allEven_of_ggLongRoot {n : ℕ} {F : Type} [Field F]
    {β : Fin (rootDatum n F).rank → ℤ} (hl : GGLongRoot (rootDatum n F) β) :
    GGRootSp.AllEven (toStd n β) := by
  obtain ⟨w, γ₀, hγ₀, hmax, rfl⟩ := hl
  refine (GGRootSp.allEven_toStd_weylAction_iff w γ₀).2 ?_
  obtain ⟨r₀, hr₀⟩ := exists_stdVec_of_mem_roots hγ₀
  change GGRootSp.AllEven (toStd n γ₀)
  rw [← hr₀]
  have hn0 : 0 < n := by
    rcases r₀ with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hle : ht (ι := Fin n) θ ≤ ht (ι := Fin n) γ₀ := hmax θ hθ
  have hγ2 := two_mul_ht (n := n) γ₀
  rw [← hr₀] at hγ2
  have h4 : 4 * (n : ℤ) - 4 < lv n (stdVec r₀) := by omega
  by_cases hn2 : 2 ≤ n
  · rw [GGRootSp.stdVec_eq_of_lv_lt hn2 r₀ h4]
    exact allEven_stdVec_positiveLong _
  · rcases r₀ with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
    · exact allEven_stdVec_positiveLong i
    · exact allEven_stdVec_negativeLong i
    · exact absurd (Fin.ext (by have := i.isLt; have := j.isLt; omega)) hij
    all_goals
      exact absurd (Fin.lt_def.1 hij) (by have := i.isLt; have := j.isLt; omega)

private theorem exists_long_index {n : ℕ} {F : Type} [Field F]
    {β : Fin (rootDatum n F).rank → ℤ} (hβ : β ∈ (rootDatum n F).roots)
    (hl : GGLongRoot (rootDatum n F) β) :
    ∃ i : Fin n, stdVec (.positiveLong i) = toStd n β ∨ stdVec (.negativeLong i) = toStd n β := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  have hev := allEven_of_ggLongRoot hl
  change GGRootSp.AllEven (toStd n β) at hev
  rw [← hr] at hev
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact ⟨i, Or.inl hr⟩
  · exact ⟨i, Or.inr hr⟩
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij] at h
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij.ne] at h
  · have h := hev i
    simp [stdVec, Pi.single_apply, hij.ne] at h

theorem ggLongRoot_of_allEven {n : ℕ} {F : Type} [Field F]
    {β : Fin (rootDatum n F).rank → ℤ} (hβ : β ∈ (rootDatum n F).roots)
    (hev : GGRootSp.AllEven (toStd n β)) : GGLongRoot (rootDatum n F) β := by
  have hn0 : 0 < n := by
    obtain ⟨r, -⟩ := exists_stdVec_of_mem_roots hβ
    rcases r with i | i | ⟨i, _, _⟩ | ⟨i, _, _⟩ | ⟨i, _, _⟩ <;> exact i.pos
  obtain ⟨θ, hθ, hθstd⟩ := GGRootSp.exists_root_toStd_eq (n := n) (.positiveLong ⟨0, hn0⟩)
  have hθe : GGRootSp.AllEven (toStd n θ) := by
    rw [hθstd]
    exact allEven_stdVec_positiveLong _
  have hθ2 : 2 * ht θ = 2 * (2 * n - 1) := by
    rw [two_mul_ht, hθstd, stdVec, map_nsmul, lv_single, nsmul_eq_mul]
    push_cast
    ring_nf
  have hmax : ∀ δ ∈ (rootDatum n F).roots, ∑ i, δ i ≤ ∑ i, θ i := by
    intro δ hδ
    obtain ⟨r, hr'⟩ := exists_stdVec_of_mem_roots hδ
    have h1 := two_mul_ht (n := n) δ
    rw [← hr'] at h1
    have h2 := GGRootSp.lv_stdVec_le r
    change ht (ι := Fin n) δ ≤ ht (ι := Fin n) θ
    omega
  have hθ' := hθ
  rcases hθ' with ⟨wθ, kθ, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hβ' : β ∈ roots (isFiniteType_cartanC n) ∅ := hβ
  rcases hβ' with ⟨w, k, rfl⟩ | ⟨_, _, hk, -⟩
  swap
  · exact hk.elim
  have hkθ : ¬ kθ.val + 1 < n :=
    (GGRootSp.allEven_toStd_single_iff kθ).1 ((GGRootSp.allEven_toStd_weylAction_iff wθ _).1 hθe)
  have hk : ¬ k.val + 1 < n :=
    (GGRootSp.allEven_toStd_single_iff k).1 ((GGRootSp.allEven_toStd_weylAction_iff w _).1 hev)
  obtain rfl : k = kθ := Fin.ext (by have := k.isLt; have := kθ.isLt; omega)
  refine ⟨w * wθ⁻¹, _, hθ, hmax, ?_⟩
  exact (by rw [weylAction_mul_apply, weylAction_inv_apply_apply] :
    weylAction (isFiniteType_cartanC n) (w * wθ⁻¹)
      (weylAction (isFiniteType_cartanC n) wθ (Pi.single k 1)) =
        weylAction (isFiniteType_cartanC n) w (Pi.single k 1)).symm

theorem exists_matTransvGroup_eq_conj_rootGroup_Sp (n : ℕ) (F : Type) [Field F] [CharP F 2]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hl : GGLongRoot (Symplectic.rootDatum n F) β) (u : ↥(CFSG.Open.StatedSp n F)) :
    ∃ v w : Fin n ⊕ Fin n → F,
      v ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w = 1 ∧
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v) ∧
      (((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          matTransvGroup w (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w) := by
  obtain ⟨i, h | h⟩ := exists_long_index hβ hl
  · have h' : stdVec (.negativeLong i) = toStd n (-β : Fin n → ℤ) := by
      have e : toStd n (-β : Fin n → ℤ) = -toStd n β := toStd_neg' β
      rw [e, ← h]
      simp [stdVec]
    refine ⟨mat n F u *ᵥ Pi.single (Sum.inl i) 1, mat n F u *ᵥ Pi.single (Sum.inr i) 1, ?_, ?_, ?_⟩
    · rw [pairing, single_dot_J_single]
      simp
    · exact map_conj_rootGroup h u _ fun c => conj_single u (.inl i) (.inr i) c
    · exact map_conj_rootGroup h' u _ fun c => conj_single u (.inr i) (.inl i) c
  · have h' : stdVec (.positiveLong i) = toStd n (-β : Fin n → ℤ) := by
      have e : toStd n (-β : Fin n → ℤ) = -toStd n β := toStd_neg' β
      rw [e, ← h]
      simp [stdVec]
    refine ⟨mat n F u *ᵥ Pi.single (Sum.inr i) 1, mat n F u *ᵥ Pi.single (Sum.inl i) 1, ?_, ?_, ?_⟩
    · rw [pairing, single_dot_J_single]
      simp
    · exact map_conj_rootGroup h u _ fun c => conj_single u (.inr i) (.inl i) c
    · exact map_conj_rootGroup h' u _ fun c => conj_single u (.inl i) (.inr i) c

theorem exists_altSiegelGroup_eq_conj_rootGroup_Sp (n : ℕ) (F : Type) [Field F] [CharP F 2]
    {β : Fin (Symplectic.rootDatum n F).rank → ℤ} (hβ : β ∈ (Symplectic.rootDatum n F).roots)
    (hs : ¬ GGLongRoot (Symplectic.rootDatum n F) β) (u : ↥(CFSG.Open.StatedSp n F)) :
    ∃ a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F,
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 1 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 1 ∧
      (a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₂ = 0 ∧
        b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 0 ∧
        a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 0 ∧
        a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 0) ∧
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₁ a₂ ∧
      (((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ b₂ := by
  obtain ⟨r, hr⟩ := exists_stdVec_of_mem_roots hβ
  have hnl : ¬ GGRootSp.AllEven (toStd n β) := fun hev => hs (ggLongRoot_of_allEven hβ hev)
  have e : toStd n (-β : Fin n → ℤ) = -toStd n β := toStd_neg' β
  rw [← hr] at hnl
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩
  · exact absurd (allEven_stdVec_positiveLong i) hnl
  · exact absurd (allEven_stdVec_negativeLong i) hnl
  ·
    have h' : stdVec (.difference j i hij.symm) = toStd n (-β : Fin n → ℤ) := by
      rw [e, ← hr]
      simp only [stdVec]
      abel
    refine ⟨mat n F u *ᵥ Pi.single (Sum.inl i) 1, mat n F u *ᵥ Pi.single (Sum.inr j) 1,
      mat n F u *ᵥ Pi.single (Sum.inr i) 1, mat n F u *ᵥ Pi.single (Sum.inl j) 1, ?_, ?_,
      ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp [hij]
    · rw [pairing, single_dot_J_single]
      simp [hij]
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · refine map_conj_rootGroup hr u _ fun c => ?_
      have hE : E F (.difference i j hij) = Matrix.single (Sum.inl i) (Sum.inl j) 1 +
          Matrix.single (Sum.inr j) (Sum.inr i) 1 := by
        ext a b
        simp [E, CharTwo.sub_eq_add]
      rw [hE, conj_single_add]
      rfl
    · refine map_conj_rootGroup h' u _ fun c => ?_
      have hE : E F (.difference j i hij.symm) = Matrix.single (Sum.inl j) (Sum.inl i) 1 +
          Matrix.single (Sum.inr i) (Sum.inr j) 1 := by
        ext a b
        simp [E, CharTwo.sub_eq_add]
      rw [hE, conj_single_add, add_comm]
      rfl
  ·
    have h' : stdVec (.negativeSum i j hij) = toStd n (-β : Fin n → ℤ) := by
      rw [e, ← hr]
      rfl
    have hij' : i ≠ j := hij.ne
    refine ⟨mat n F u *ᵥ Pi.single (Sum.inl i) 1, mat n F u *ᵥ Pi.single (Sum.inl j) 1,
      mat n F u *ᵥ Pi.single (Sum.inr i) 1, mat n F u *ᵥ Pi.single (Sum.inr j) 1, ?_, ?_,
      ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp [hij', hij'.symm]
    · rw [pairing, single_dot_J_single]
      simp [hij', hij'.symm]
    · refine map_conj_rootGroup hr u _ fun c => ?_
      change mat n F u * (c • (Matrix.single (Sum.inl i) (Sum.inr j) 1 +
        Matrix.single (Sum.inl j) (Sum.inr i) 1)) * mat n F u⁻¹ = _
      rw [conj_single_add]
      rfl
    · refine map_conj_rootGroup h' u _ fun c => ?_
      change mat n F u * (c • (Matrix.single (Sum.inr i) (Sum.inl j) 1 +
        Matrix.single (Sum.inr j) (Sum.inl i) 1)) * mat n F u⁻¹ = _
      rw [conj_single_add]
      rfl
  ·
    have h' : stdVec (.positiveSum i j hij) = toStd n (-β : Fin n → ℤ) := by
      rw [e, ← hr]
      simp [stdVec]
    have hij' : i ≠ j := hij.ne
    refine ⟨mat n F u *ᵥ Pi.single (Sum.inr i) 1, mat n F u *ᵥ Pi.single (Sum.inr j) 1,
      mat n F u *ᵥ Pi.single (Sum.inl i) 1, mat n F u *ᵥ Pi.single (Sum.inl j) 1, ?_, ?_,
      ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp
    · rw [pairing, single_dot_J_single]
      simp [hij', hij'.symm]
    · rw [pairing, single_dot_J_single]
      simp [hij', hij'.symm]
    · refine map_conj_rootGroup hr u _ fun c => ?_
      change mat n F u * (c • (Matrix.single (Sum.inr i) (Sum.inl j) 1 +
        Matrix.single (Sum.inr j) (Sum.inl i) 1)) * mat n F u⁻¹ = _
      rw [conj_single_add]
      rfl
    · refine map_conj_rootGroup h' u _ fun c => ?_
      change mat n F u * (c • (Matrix.single (Sum.inl i) (Sum.inr j) 1 +
        Matrix.single (Sum.inl j) (Sum.inr i) 1)) * mat n F u⁻¹ = _
      rw [conj_single_add]
      rfl

end CFSG.StandardType.LieKnownR2.Geo
