module

public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LieType.SteinbergBRBlockParabolicResidual
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphAction
public import CFSG.Quasithin.Vol2.Ch12Sec1Q

public section

namespace CFSG.Quasithin.H13

open Matrix CFSG.LieType.SteinbergBR CFSG.LieType.SteinbergBR.BlockPar
open scoped Matrix

namespace VecStab

variable {n : ℕ}

@[expose] def vecStab {ι : Type} [Fintype ι] [DecidableEq ι] (x₀ : ι → ZMod 2) :
    Subgroup (SpecialLinearGroup ι (ZMod 2)) where
  carrier := {g | (g : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀}
  mul_mem' {a b} ha hb := by
    change ((a * b : SpecialLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀
    rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
    rw [show (b : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀ from hb]
    exact ha
  one_mem' := by
    change ((1 : SpecialLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀
    rw [Matrix.SpecialLinearGroup.coe_one, one_mulVec]
  inv_mem' {a} ha := by
    change ((a⁻¹ : SpecialLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀
    have ha' : (a : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀ := ha
    conv_lhs => rw [← ha']
    rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem mem_vecStab {ι : Type} [Fintype ι] [DecidableEq ι] {x₀ : ι → ZMod 2}
    {g : SpecialLinearGroup ι (ZMod 2)} :
    g ∈ vecStab x₀ ↔ (g : Matrix ι ι (ZMod 2)) *ᵥ x₀ = x₀ :=
  Iff.rfl

theorem parJR_eq_vecStab (m : ℕ) :
    parJR (ZMod 2) (Fin 1) (Fin m) = vecStab (Pi.single (Sum.inl 0) 1) := by
  ext g
  rw [mem_parJR, mem_parQ, mem_vecStab]
  constructor
  · rintro ⟨h21, h11⟩
    funext k
    rw [mulVec_single_one]
    rcases k with i | j
    · have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have := congrFun (congrFun h11 0) 0
      simp only [toBlocks₁₁, of_apply, one_apply_eq] at this
      simpa using this
    · have := congrFun (congrFun h21 j) 0
      simp only [toBlocks₂₁, of_apply, Matrix.zero_apply] at this
      simpa using this
  · intro h
    refine ⟨?_, ?_⟩
    · funext j i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have := congrFun h (Sum.inr j)
      rw [mulVec_single_one] at this
      simpa [toBlocks₂₁] using this
    · funext i k
      have hi : i = 0 := Subsingleton.elim i 0
      have hk : k = 0 := Subsingleton.elim k 0
      subst hi hk
      have := congrFun h (Sum.inl 0)
      rw [mulVec_single_one] at this
      simpa [toBlocks₁₁] using this

@[expose] def e0 {m : ℕ} (h : 1 + m = n) : Fin n → ZMod 2 := Pi.single (sumEquiv h (Sum.inl 0)) 1

theorem e0_eq {m : ℕ} (h : 1 + m = n) :
    e0 h = (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) ∘ (sumEquiv h).symm := by
  funext k
  simp only [e0, Function.comp_apply]
  by_cases hk : k = sumEquiv h (Sum.inl 0)
  · subst hk
    simp
  · have hk' : (sumEquiv h).symm k ≠ Sum.inl 0 := fun h' => hk (by rw [← h']; simp)
    rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk']

theorem map_reindexSL {m : ℕ} (h : 1 + m = n) :
    (vecStab (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2)).map
      (reindexSL (ZMod 2) h).toMonoidHom = vecStab (e0 h) := by
  have key : ∀ M : SpecialLinearGroup (Fin 1 ⊕ Fin m) (ZMod 2),
      ((reindexSL (ZMod 2) h M : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e0 h =
      (((M : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (ZMod 2)) *ᵥ
        Pi.single (Sum.inl 0) 1) ∘ (sumEquiv h).symm) := by
    intro M
    have he : e0 h = (Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) ∘ (sumEquiv h).symm :=
      e0_eq h
    have hx : ((Pi.single (Sum.inl 0) 1 : Fin 1 ⊕ Fin m → ZMod 2) ∘ (sumEquiv h).symm) ∘
        ⇑(sumEquiv h).symm.symm = Pi.single (Sum.inl 0) 1 := by
      funext k
      simp
    rw [he, reindexSL_val, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, hx]
  ext g
  constructor
  · rintro ⟨M, hM, rfl⟩
    rw [mem_vecStab]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [key, show (M : Matrix (Fin 1 ⊕ Fin m) (Fin 1 ⊕ Fin m) (ZMod 2)) *ᵥ
      Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 from hM, e0_eq]
  · intro hg
    refine ⟨(reindexSL (ZMod 2) h).symm g, ?_, by simp⟩
    rw [SetLike.mem_coe, mem_vecStab]
    have h1 := key ((reindexSL (ZMod 2) h).symm g)
    rw [MulEquiv.apply_symm_apply, show (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e0 h = e0 h
      from hg] at h1
    funext k
    have := congrFun h1 (sumEquiv h k)
    simp only [Function.comp_apply, Equiv.symm_apply_apply] at this
    rw [← this, e0_eq]
    simp

theorem inv_mulVec_mulVec (s : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = x := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem mulVec_inv_mulVec (s : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      (((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
      x := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, one_mulVec]

theorem map_conj_vecStab (s : SpecialLinearGroup (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    (vecStab x).map (MulAut.conj s).toMonoidHom =
      vecStab ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' : (a : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x = x := ha
    rw [mem_vecStab]
    change ((s * a * s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) = _
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec,
      inv_mulVec_mulVec, ← mulVec_mulVec, ha']
  · intro hg
    have hg' : (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
        ((s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x) =
        (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ x := hg
    refine ⟨s⁻¹ * g * s, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    rw [SetLike.mem_coe, mem_vecStab, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, hg',
      inv_mulVec_mulVec]

theorem map_parJR {m : ℕ} (h : 1 + m = n) {s : SpecialLinearGroup (Fin n) (ZMod 2)}
    {x₀ : Fin n → ZMod 2} (hs : (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e0 h = x₀) :
    (parJR (ZMod 2) (Fin 1) (Fin m)).map (transportSL (ZMod 2) h s).toMonoidHom = vecStab x₀ := by
  rw [parJR_eq_vecStab, show (transportSL (ZMod 2) h s).toMonoidHom =
    (MulAut.conj s).toMonoidHom.comp (reindexSL (ZMod 2) h).toMonoidHom from rfl,
    ← Subgroup.map_map, map_reindexSL, map_conj_vecStab, hs]

theorem exists_mulVec_e0 {m : ℕ} (h : 1 + m = n) {x₀ : Fin n → ZMod 2} (hx₀ : x₀ ≠ 0) :
    ∃ s : SpecialLinearGroup (Fin n) (ZMod 2),
      (s : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ e0 h = x₀ := by
  refine Sec121Q.exists_sl_mulVec_eq ?_ hx₀
  intro h0
  have := congrFun h0 (sumEquiv h (Sum.inl 0))
  simp [e0] at this

theorem commutator_sl_eq_top {m : ℕ} (hm : 3 ≤ m) :
    commutator (SpecialLinearGroup (Fin m) (ZMod 2)) = ⊤ :=
  CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le hm

theorem commutator_eq {m : ℕ} (hm : 3 ≤ m) (h : 1 + m = n) {x₀ : Fin n → ZMod 2}
    (hx₀ : x₀ ≠ 0) : ⁅vecStab x₀, vecStab x₀⁆ = vecStab x₀ := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨s, hs⟩ := exists_mulVec_e0 h hx₀
  rw [← map_parJR h hs, ← Subgroup.map_commutator, commutator_parJR (commutator_sl_eq_top hm)]

theorem exists_levi {m : ℕ} (h : 1 + m = n) {x₀ : Fin n → ZMod 2} (hx₀ : x₀ ≠ 0) :
    ∃ ψ : ↥(vecStab x₀) →* SpecialLinearGroup (Fin m) (ZMod 2),
      Function.Surjective ψ ∧ IsPGroup 2 ψ.ker := by
  obtain ⟨s, hs⟩ := exists_mulVec_e0 h hx₀
  have hP := map_parJR h hs
  let e₁ : Multiplicative (Matrix (Fin 1) (Fin m) (ZMod 2)) ⋊[phiR (ZMod 2) (Fin 1)]
      SpecialLinearGroup (Fin m) (ZMod 2) ≃* ↥(parJR (ZMod 2) (Fin 1) (Fin m)) :=
    MonoidHom.ofInjective thetaR_injective
  let e₂ : ↥(parJR (ZMod 2) (Fin 1) (Fin m)) ≃* ↥(vecStab x₀) :=
    (Subgroup.equivMapOfInjective _ _ (transportSL (ZMod 2) h s).injective).trans
      (MulEquiv.subgroupCongr hP)
  refine ⟨SemidirectProduct.rightHom.comp (e₁.symm.toMonoidHom.comp e₂.symm.toMonoidHom),
    ?_, ?_⟩
  · exact SemidirectProduct.rightHom_surjective.comp
      (e₁.symm.surjective.comp e₂.symm.surjective)
  · intro x
    refine ⟨1, ?_⟩
    have hx := x.2
    rw [MonoidHom.mem_ker] at hx
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    set y := e₁.symm (e₂.symm (x : ↥(vecStab x₀))) with hy
    have hyr : y.right = 1 := hx
    have hy2 : y ^ 2 = 1 := by
      refine SemidirectProduct.ext ?_ ?_
      · rw [pow_two, SemidirectProduct.mul_left, hyr, map_one, MulAut.one_apply,
          SemidirectProduct.one_left]
        apply Multiplicative.toAdd.injective
        rw [toAdd_mul, toAdd_one]
        funext i j
        simp only [Matrix.add_apply, Matrix.zero_apply]
        rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
      · rw [pow_two, SemidirectProduct.mul_right, hyr, mul_one]
        rfl
    have : (x : ↥(vecStab x₀)) ^ 2 = 1 := by
      have h1 : e₂ (e₁ (y ^ 2)) = (x : ↥(vecStab x₀)) ^ 2 := by
        rw [map_pow, map_pow, hy, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      rw [← h1, hy2, map_one, map_one]
    exact this

theorem slGraphAut_slGraphAut (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) g) = g :=
  (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2)).left_inv g

theorem inv_transpose_mulVec_of {h : SpecialLinearGroup (Fin n) (ZMod 2)} {x : Fin n → ZMod 2}
    (hx : ((h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ x = x) :
    (((h⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ x =
      x := by
  conv_lhs => rw [← hx]
  rw [mulVec_mulVec, ← transpose_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, transpose_one, one_mulVec]

@[expose] def colSL (i : Fin n) (u : Fin n → ZMod 2) (hu : u i = 1) :
    SpecialLinearGroup (Fin n) (ZMod 2) :=
  ⟨(1 : Matrix (Fin n) (Fin n) (ZMod 2)).updateCol i u, by rw [Sec121Q.det_updateCol_one, hu]⟩

theorem colSL_mulVec (i : Fin n) (u : Fin n → ZMod 2) (hu : u i = 1) :
    ((colSL i u hu : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
      Pi.single i 1 = u := by
  funext k
  simp [colSL, Matrix.mulVec, dotProduct, Matrix.updateCol_apply, Pi.single_apply]

theorem colSL_transpose_mulVec {i k : Fin n} (hik : i ≠ k) (u : Fin n → ZMod 2) (hu : u i = 1)
    (huk : u k = 0) :
    ((colSL i u hu : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *ᵥ
      Pi.single k 1 = Pi.single k 1 := by
  funext j
  simp only [colSL, mulVec_single_one]
  by_cases hj : j = i
  · subst hj
    simp [huk, hik]
  · simp [hj, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem exists_dual_of_coord {i k : Fin n} (hik : i ≠ k) {w w' : Fin n → ZMod 2} (hw : w i = 1)
    (hw' : w' i = 1) (hwk : w k = 0) (hw'k : w' k = 0) :
    ∃ h : SpecialLinearGroup (Fin n) (ZMod 2),
      ((h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ Pi.single k 1 = Pi.single k 1 ∧
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  refine ⟨colSL i w' hw' * (colSL i w hw)⁻¹, ?_, ?_⟩
  · rw [Matrix.SpecialLinearGroup.coe_mul, transpose_mul, ← mulVec_mulVec,
      colSL_transpose_mulVec hik w' hw' hw'k]
    exact inv_transpose_mulVec_of (colSL_transpose_mulVec hik w hw hwk)
  · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec]
    have h1 : (((colSL i w hw)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = Pi.single i 1 := by
      have h2 := inv_mulVec_mulVec (colSL i w hw) (Pi.single i 1)
      rwa [colSL_mulVec] at h2
    rw [h1, colSL_mulVec]

theorem exists_dual {k : Fin n} {w w' : Fin n → ZMod 2} (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hwk : w k = 0) (hw'k : w' k = 0) :
    ∃ g ∈ vecStab (Pi.single k 1 : Fin n → ZMod 2),
      ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) g :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hw'
  have hik : i ≠ k := fun h => hi (h ▸ hwk)
  have hjk : j ≠ k := fun h => hj (h ▸ hw'k)
  have hwi : w i = 1 := h01 _ hi
  have hw'j : w' j = 1 := h01 _ hj
  obtain ⟨h, hT, hww⟩ : ∃ h : SpecialLinearGroup (Fin n) (ZMod 2),
      ((h : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ) *ᵥ Pi.single k 1 = Pi.single k 1 ∧
        (h : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
    by_cases hw'i : w' i = 1
    · exact exists_dual_of_coord hik hwi hw'i hwk hw'k
    · have hij : i ≠ j := fun h => hw'i (h ▸ hw'j)
      set z : Fin n → ZMod 2 := Pi.single i 1 + Pi.single j 1 with hz
      have hzi : z i = 1 := by simp [z, hij]
      have hzj : z j = 1 := by simp [z, hij.symm]
      have hzk : z k = 0 := by simp [z, hik.symm, hjk.symm]
      obtain ⟨h₁, hT₁, h₁w⟩ := exists_dual_of_coord hik hwi hzi hwk hzk
      obtain ⟨h₂, hT₂, h₂w⟩ := exists_dual_of_coord hjk hzj hw'j hzk hw'k
      refine ⟨h₂ * h₁, ?_, ?_⟩
      · rw [Matrix.SpecialLinearGroup.coe_mul, transpose_mul, ← mulVec_mulVec, hT₂, hT₁]
      · rw [Matrix.SpecialLinearGroup.coe_mul, ← mulVec_mulVec, h₁w, h₂w]
  refine ⟨CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) h, ?_, ?_⟩
  · rw [mem_vecStab, CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix]
    exact inv_transpose_mulVec_of hT
  · rw [slGraphAut_slGraphAut]
    exact hww

theorem exists_dual' {x₀ w w' : Fin n → ZMod 2} (hx₀ : x₀ ≠ 0) (hw : w ≠ 0) (hw' : w' ≠ 0)
    (hxw : x₀ ⬝ᵥ w = 0) (hxw' : x₀ ⬝ᵥ w' = 0) :
    ∃ g ∈ vecStab x₀,
      ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) g :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w' := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (Subsingleton.elim x₀ 0) hx₀
    · exact h
  set k : Fin n := ⟨0, hn⟩
  have hk0 : (Pi.single k 1 : Fin n → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h k
    simp at this
  obtain ⟨s, hs⟩ := Sec121Q.exists_sl_mulVec_eq hk0 hx₀
  set S : Matrix (Fin n) (Fin n) (ZMod 2) := (s : Matrix (Fin n) (Fin n) (ZMod 2)) with hS
  set Si : Matrix (Fin n) (Fin n) (ZMod 2) :=
    ((s⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) with hSi
  have hSSi : S * Si = 1 := by
    rw [hS, hSi, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have hSiS : Si * S = 1 := by
    rw [hS, hSi, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  set u := Sᵀ *ᵥ w with hu
  set u' := Sᵀ *ᵥ w' with hu'
  have hinj : ∀ y : Fin n → ZMod 2, Sᵀ *ᵥ y = 0 → y = 0 := by
    intro y hy
    have : Siᵀ *ᵥ (Sᵀ *ᵥ y) = y := by
      rw [mulVec_mulVec, ← transpose_mul, hSSi, transpose_one, one_mulVec]
    rw [← this, hy, mulVec_zero]
  have hdot : ∀ y : Fin n → ZMod 2, (Sᵀ *ᵥ y) k = x₀ ⬝ᵥ y := by
    intro y
    rw [← hs, ← single_one_dotProduct k (Sᵀ *ᵥ y), dotProduct_mulVec, vecMul_transpose]
  obtain ⟨g', hg', hg'u⟩ := exists_dual (k := k) (w := u) (w' := u')
    (fun h => hw (hinj w h)) (fun h => hw' (hinj w' h)) (by rw [hu, hdot, hxw])
    (by rw [hu', hdot, hxw'])
  refine ⟨s * g' * s⁻¹, ?_, ?_⟩
  · rw [← hs, ← map_conj_vecStab]
    exact ⟨g', hg', rfl⟩
  · rw [map_mul, map_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← mulVec_mulVec, ← mulVec_mulVec]
    have h1 : ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut n (ZMod 2) s⁻¹ :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = Sᵀ := by
      rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, inv_inv]
    rw [h1, ← hu, hg'u, hu',
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, ← hSi, mulVec_mulVec,
      ← transpose_mul, hSSi, transpose_one, one_mulVec]

theorem add_self (x : Fin n → ZMod 2) : x + x = 0 := by
  funext k
  show x k + x k = 0
  generalize x k = c
  revert c
  decide

theorem eq_of_add_eq_zero {x y : Fin n → ZMod 2} (h : x + y = 0) : x = y := by
  have e : x = x + (y + y) := by rw [add_self, add_zero]
  rw [e, ← add_assoc, h, zero_add]

theorem exists_not_mem_finset (s : Finset (Fin n → ZMod 2)) (h : s.card < 2 ^ n) :
    ∃ x, x ∉ s := by
  by_contra hcon
  push Not at hcon
  have h1 := Finset.card_le_card (fun x (_ : x ∈ (Finset.univ : Finset (Fin n → ZMod 2))) =>
    hcon x)
  rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin] at h1
  omega

theorem exists_perp_ne (hn : 3 ≤ n) {x₀ : Fin n → ZMod 2} (hx₀ : x₀ ≠ 0) (w : Fin n → ZMod 2) :
    ∃ y, x₀ ⬝ᵥ y = 0 ∧ y ≠ 0 ∧ y ≠ w := by
  have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx₀
  have hk1 : x₀ k = 1 := h01 _ hk
  obtain ⟨j₁, hj₁, j₂, hj₂, hj⟩ : ∃ j₁, j₁ ≠ k ∧ ∃ j₂, j₂ ≠ k ∧ j₁ ≠ j₂ := by
    have hcard : 2 ≤ (Finset.univ.erase k : Finset (Fin n)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    exact ⟨a, Finset.ne_of_mem_erase ha, b, Finset.ne_of_mem_erase hb, hab⟩
  set y : Fin n → Fin n → ZMod 2 := fun j => Pi.single j 1 + Pi.single k (x₀ j) with hy
  have hperp : ∀ j, x₀ ⬝ᵥ y j = 0 := by
    intro j
    simp only [hy, dotProduct_add, dotProduct_single, mul_one, hk1, one_mul]
    exact CharTwo.add_self_eq_zero _
  have hyj : ∀ j, j ≠ k → y j j = 1 := by
    intro j hjk
    simp [hy, hjk]
  have hy₁ : y j₁ ≠ 0 := fun h => by
    have := hyj j₁ hj₁
    rw [h, Pi.zero_apply] at this
    exact absurd this (by decide)
  have hy₂ : y j₂ ≠ 0 := fun h => by
    have := hyj j₂ hj₂
    rw [h, Pi.zero_apply] at this
    exact absurd this (by decide)
  have hy₁₂ : y j₁ ≠ y j₂ := fun h => by
    have h1 := hyj j₁ hj₁
    rw [h] at h1
    simp [hy, hj, hj₁] at h1
  by_cases hw : y j₁ = w
  · exact ⟨y j₂, hperp j₂, hy₂, fun h => hy₁₂ (hw.trans h.symm)⟩
  · exact ⟨y j₁, hperp j₁, hy₁, hw⟩

theorem seven_dvd_card {m : ℕ} (hm : m = 3 ∨ m = 4) :
    7 ∣ Nat.card (SpecialLinearGroup (Fin m) (ZMod 2)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by omega), Nat.card_zmod]
  rcases hm with rfl | rfl <;> decide

end VecStab

end CFSG.Quasithin.H13
