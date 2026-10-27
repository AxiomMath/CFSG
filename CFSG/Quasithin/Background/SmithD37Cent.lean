module

public import CFSG.Quasithin.Background.SmithD37Flip
public import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin.SmithD37

open Matrix

variable {U : Type} [CommGroup U] {L₁ L₂ : Subgroup (MulAut U)} {F : Type} [Field F] {d : ℕ}

@[expose] noncomputable def MatModel.swap (Mm : MatModel L₁ L₂ F d) : MatModel L₂ L₁ F d where
  β := Mm.β.trans (Matrix.transposeAddEquiv (Fin d) (Fin d) F).toMultiplicative
  R₁ := Mm.R₂
  R₂ := Mm.R₁
  act₁ k u := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (Mm.β ((k : MulAut U) u)))ᵀ = _
    rw [Mm.act₂, toAdd_ofAdd, Matrix.transpose_mul, Matrix.transpose_transpose]
    rfl
  act₂ l u := by
    show Multiplicative.ofAdd (Multiplicative.toAdd (Mm.β ((l : MulAut U) u)))ᵀ = _
    rw [Mm.act₁, toAdd_ofAdd, Matrix.transpose_mul]
    rfl
  inj₁ := Mm.inj₂
  span₁ := Mm.span₂
  span₂ := Mm.span₁
  inj₂ := Mm.inj₁
  irr₁ := Mm.irr₂
  end₁ := Mm.end₂
  irr₂ := Mm.irr₁
  end₂ := Mm.end₁

@[simp]
theorem MatModel.swap_β (Mm : MatModel L₁ L₂ F d) (u : U) :
    Multiplicative.toAdd (Mm.swap.β u) = (Multiplicative.toAdd (Mm.β u))ᵀ :=
  rfl

@[simp]
theorem MatModel.swap_R₁ (Mm : MatModel L₁ L₂ F d) : Mm.swap.R₁ = Mm.R₂ :=
  rfl

@[simp]
theorem MatModel.swap_R₂ (Mm : MatModel L₁ L₂ F d) : Mm.swap.R₂ = Mm.R₁ :=
  rfl

private theorem sum_vecMulVec_col' (X : Matrix (Fin d) (Fin d) F) :
    ∑ i, vecMulVec (fun m => X m i) (Pi.single i 1) = X := by
  ext m n
  simp [Matrix.sum_apply, vecMulVec_apply, Pi.single_apply]

private theorem exists_mul_of_comm₁ (Mm : MatModel L₁ L₂ F d)
    (S : Matrix (Fin d) (Fin d) F →+ Matrix (Fin d) (Fin d) F)
    (h₁ : ∀ (l : ↥L₁) X, S ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X) =
      (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * S X) :
    ∃ C : Matrix (Fin d) (Fin d) F, ∀ X, S X = X * C := by
  classical
  have hcol : ∀ i j : Fin d, ∃ c : F, ∀ v : Fin d → F,
      (fun m => S (vecMulVec v (Pi.single i 1)) m j) = c • v := by
    intro i j
    let φ : (Fin d → F) →+ (Fin d → F) :=
      { toFun := fun v m => S (vecMulVec v (Pi.single i 1)) m j
        map_zero' := by ext m; simp
        map_add' := by intro v w; ext m; simp [add_vecMulVec] }
    refine Mm.end₁ φ fun l v => ?_
    ext m
    show S (vecMulVec (_ *ᵥ v) _) m j = _
    rw [← mul_vecMulVec, h₁]
    simp [φ, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  choose c hc using hcol
  refine ⟨Matrix.of c, fun X => ?_⟩
  ext m j
  conv_lhs => rw [← sum_vecMulVec_col' X]
  rw [map_sum, Matrix.sum_apply]
  have h := fun i => congrFun (hc i j (fun m => X m i)) m
  simp only [Pi.smul_apply, smul_eq_mul] at h
  simp only [h, Matrix.mul_apply, Matrix.of_apply, mul_comm]

private theorem coordAut_comm₁ (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (ha : ∀ l ∈ L₁, a * l = l * a) (l : ↥L₁) (X : Matrix (Fin d) (Fin d) F) :
    coordAut Mm a ((Mm.R₁ l : Matrix (Fin d) (Fin d) F) * X) =
      (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * coordAut Mm a X := by
  obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (Mm.β u) = X :=
    ⟨Mm.β.symm (Multiplicative.ofAdd X), by simp⟩
  have h : a ((l : MulAut U) u) = (l : MulAut U) (a u) := by
    rw [← MulAut.mul_apply, ha l l.2, MulAut.mul_apply]
  have e : (Mm.R₁ l : Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (Mm.β u) =
      Multiplicative.toAdd (Mm.β ((l : MulAut U) u)) := by
    rw [Mm.act₁, toAdd_ofAdd]
  rw [e, coordAut_β, coordAut_β, h, Mm.act₁, toAdd_ofAdd]

private theorem coordAut_comm₂ (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (ha : ∀ k ∈ L₂, a * k = k * a) (k : ↥L₂) (X : Matrix (Fin d) (Fin d) F) :
    coordAut Mm a (X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ) =
      coordAut Mm a X * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ := by
  obtain ⟨u, rfl⟩ : ∃ u, Multiplicative.toAdd (Mm.β u) = X :=
    ⟨Mm.β.symm (Multiplicative.ofAdd X), by simp⟩
  have h : a ((k : MulAut U) u) = (k : MulAut U) (a u) := by
    rw [← MulAut.mul_apply, ha k k.2, MulAut.mul_apply]
  have e : Multiplicative.toAdd (Mm.β u) * (Mm.R₂ k : Matrix (Fin d) (Fin d) F)ᵀ =
      Multiplicative.toAdd (Mm.β ((k : MulAut U) u)) := by
    rw [Mm.act₂, toAdd_ofAdd]
  rw [e, coordAut_β, coordAut_β, h, Mm.act₂, toAdd_ofAdd]

theorem exists_right_mul (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (ha : ∀ l ∈ L₁, a * l = l * a) :
    ∃ C : Matrix (Fin d) (Fin d) F, ∀ u,
      Multiplicative.toAdd (Mm.β (a u)) = Multiplicative.toAdd (Mm.β u) * C := by
  obtain ⟨C, hC⟩ := exists_mul_of_comm₁ Mm (coordAut Mm a) (coordAut_comm₁ Mm ha)
  exact ⟨C, fun u => by rw [← coordAut_β, hC]⟩

theorem exists_left_mul (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (ha : ∀ k ∈ L₂, a * k = k * a) :
    ∃ C : Matrix (Fin d) (Fin d) F, ∀ u,
      Multiplicative.toAdd (Mm.β (a u)) = C * Multiplicative.toAdd (Mm.β u) := by
  obtain ⟨C, hC⟩ := exists_right_mul Mm.swap ha
  refine ⟨Cᵀ, fun u => ?_⟩
  have h := congrArg Matrix.transpose (hC u)
  simpa [Matrix.transpose_mul] using h

theorem eq_one_of_comm [Fintype F] [CharP F 2] (Mm : MatModel L₁ L₂ F d) {a : MulAut U}
    (h₁ : ∀ l ∈ L₁, a * l = l * a) (h₂ : ∀ k ∈ L₂, a * k = k * a) {e : ℕ}
    (he : a ^ 2 ^ e = 1) : a = 1 := by
  obtain ⟨c, hc⟩ := exists_smul_of_comm Mm (coordAut Mm a) (coordAut_comm₁ Mm h₁)
    (coordAut_comm₂ Mm h₂)
  have hc' : ∀ u, Multiplicative.toAdd (Mm.β (a u)) = c • Multiplicative.toAdd (Mm.β u) :=
    fun u => by rw [← coordAut_β, hc]
  have hpow : ∀ (n : ℕ) u,
      Multiplicative.toAdd (Mm.β ((a ^ n) u)) = c ^ n • Multiplicative.toAdd (Mm.β u) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih => intro u; rw [pow_succ, MulAut.mul_apply, ih, hc', smul_smul, pow_succ]
  refine MulEquiv.ext fun u => ?_
  rw [MulAut.one_apply]
  apply Mm.β.injective
  apply Multiplicative.toAdd.injective
  rw [hc']
  set X := Multiplicative.toAdd (Mm.β u)
  have h1 : c ^ 2 ^ e • X = X := by rw [← hpow, he, MulAut.one_apply]
  have h2 : (c - 1) ^ 2 ^ e • X = 0 := by
    rw [sub_pow_char_pow, one_pow, sub_smul, one_smul, h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · rw [sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero e two_ne_zero) |>.mp h3), one_smul]
  · rw [h3, smul_zero]

@[expose] noncomputable def Core.equiv [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U}
    (h : Core X L₁ L₂ s) : ↥L₁ ≃* ↥L₂ :=
  (Subgroup.equivMapOfInjective L₁ (MulAut.conj s).toMonoidHom (MulAut.conj s).injective).trans
    (MulEquiv.subgroupCongr h.swap₁)

private theorem sqtkGroup_congr {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : SQTKGroup A) : SQTKGroup B := by
  refine ⟨fun p hp hp2 => ?_, h.2.of_mulEquiv e.symm⟩
  show CFSG.Open.pRank p (⊤ : Subgroup B) ≤ 2
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact h.1 p hp hp2

theorem Core.swap [Finite U] {X : Subgroup (MulAut U)} {s : MulAut U}
    (h : Core X L₁ L₂ s) : Core X L₂ L₁ s where
  exp := h.exp
  nt := h.nt
  a38 := a38Types_congr h.equiv h.a38
  simple := @MulEquiv.isSimpleGroup _ _ _ _ h.simple h.equiv.symm
  sqtk := sqtkGroup_congr h.equiv h.sqtk
  comm x hx y hy := (h.comm y hy x hx).symm
  inf := by rw [inf_comm]; exact h.inf
  le₁ := h.le₂
  le₂ := h.le₁
  mem := h.mem
  swap₁ := h.swap₂
  swap₂ := h.swap₁
  perm x hx := (h.perm x hx).imp And.symm And.symm
  two := by rw [sup_comm]; exact h.two
  o2 := h.o2
  irr := by rw [sup_comm]; exact h.irr
  qhat := h.qhat

end CFSG.Quasithin.SmithD37
