module

public import CFSG.RankThree.PartOne.U5K.Hyp.Dlin

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] {hK : UnitaryFieldData 2 f K}

@[expose] def IsPara (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) : Prop :=
  (∀ i, A (.inr (.inl 0)) (.inl i) = 0) ∧ (∀ i j, A (.inr (.inr j)) (.inl i) = 0) ∧
    ∀ j, A (.inr (.inr j)) (.inr (.inl 0)) = 0

theorem eq_blk3_of_para {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} (hA : IsPara A) :
    A = blk3 (blkA A) (blkX A) (blkY A) (blkP A) (blkQ A) (blkD A) := by
  ext a b
  rcases a with i | k | j <;> rcases b with i' | k' | j'
  · rfl
  · rfl
  · rfl
  · fin_cases k
    exact hA.1 i'
  · fin_cases k
    fin_cases k'
    rfl
  · fin_cases k
    rfl
  · exact hA.2.1 i' j
  · fin_cases k'
    exact hA.2.2 j
  · rfl

theorem isPara_of_paraW {x : Gam hK} (hP : IsParaW (lmat x)) : IsPara (lmat x) := by
  refine ⟨hP.1, hP.2, fun j => ?_⟩
  obtain ⟨μ, hμ0, hμ, hgram⟩ := x.2
  have hdet := det_blkEE_ne_zero hP
  set w : Fin 2 → K := fun k => lmat x (.inr (.inr k)) (.inr (.inl 0)) with hw
  have key : ((blkEE x).map hK.bar)ᵀ *ᵥ w = 0 := by
    funext i
    have := congrFun (congrFun hgram (.inl i)) (.inr (.inl 0))
    rw [conjTranspose_hypGram_mul_apply] at this
    simp [Fintype.sum_sum_type, Fin.sum_univ_two] at this
    have h1 := hP.1
    have h2 := hP.2
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, hw, blkEE]
    have e1 : lmat x (Sum.inr (Sum.inl 0)) (Sum.inl i) = 0 := h1 i
    have e2 : ∀ j, lmat x (Sum.inr (Sum.inr j)) (Sum.inl i) = 0 := fun j => h2 i j
    unfold lmat at e1 e2 ⊢
    simp only [e1, e2, map_zero, zero_mul, add_zero] at this
    exact this
  have hdet' : ((blkEE x).map hK.bar)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    have : ((blkEE x).map hK.bar).det = hK.bar (blkEE x).det := by
      simpa using (RingHom.map_det hK.bar (blkEE x)).symm
    rw [this]
    exact (map_ne_zero hK.bar).mpr hdet
  have hw0 : w = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet' key
  exact congrFun hw0 j

section LamDef

theorem finite_Gam (hK : UnitaryFieldData 2 f K) : Finite (Gam hK) := by
  have : Finite K := hK.finite
  have h1 : Finite (GL (HypIndex 2 1) K) := inferInstance
  have h2 : Finite (K ≃+* K) :=
    Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective
  refine Finite.of_injective (fun x : Gam hK => (x.1.left, x.1.right)) ?_
  intro x y h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  exact Subtype.ext (SemidirectProduct.ext h1 h2)

variable {A B : Matrix (HypIndex 2 1) (HypIndex 2 1) K}

theorem isPara_blk3 (A : Matrix (Fin 2) (Fin 2) K) (X : Matrix (Fin 2) (Fin 1) K)
    (Y : Matrix (Fin 2) (Fin 2) K) (P : Matrix (Fin 1) (Fin 1) K) (Q : Matrix (Fin 1) (Fin 2) K)
    (D : Matrix (Fin 2) (Fin 2) K) : IsPara (blk3 A X Y P Q D) := by
  refine ⟨fun i => ?_, fun i j => ?_, fun j => ?_⟩ <;> simp

theorem mul_para (hA : IsPara A) (hB : IsPara B) :
    IsPara (A * B) ∧ blkA (A * B) = blkA A * blkA B ∧ blkP (A * B) = blkP A * blkP B ∧
      blkD (A * B) = blkD A * blkD B := by
  rw [eq_blk3_of_para hA, eq_blk3_of_para hB, blk3_mul]
  refine ⟨isPara_blk3 _ _ _ _ _ _, ?_, ?_, ?_⟩
  · ext i j; simp [blkA]
  · ext i j; simp [blkP]
  · ext i j; simp [blkD]

theorem lmat_mul_of_right_one {x y : Gam hK} (hx : x.1.right = 1) :
    lmat (x * y) = lmat x * lmat y := by
  change ((((x * y : Gam hK) : SemiGL (HypIndex 2 1) K).left : GL (HypIndex 2 1) K) :
    Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
  rw [Subgroup.coe_mul, SemidirectProduct.mul_left, hx, map_one, MulAut.one_apply, Units.val_mul]
  rfl

@[expose] def LamM (hK : UnitaryFieldData 2 f K) : Submonoid (Gam hK) where
  carrier := {x | x.1.right = 1 ∧ IsPara (lmat x) ∧ (blkEE x).det = 1}
  one_mem' := by
    refine ⟨by simp, ?_, ?_⟩
    · have : lmat (1 : Gam hK) = 1 := rfl
      rw [this]
      refine ⟨fun i => ?_, fun i j => ?_, fun j => ?_⟩ <;> simp
    · have : blkEE (1 : Gam hK) = 1 := by
        ext i j
        simp [blkEE, lmat, Matrix.one_apply]
      rw [this, Matrix.det_one]
  mul_mem' := by
    rintro x y ⟨hxr, hxP, hxd⟩ ⟨hyr, hyP, hyd⟩
    have hr : (x * y).1.right = 1 := by
      rw [Subgroup.coe_mul, SemidirectProduct.mul_right, hxr, hyr, mul_one]
    have hm := lmat_mul_of_right_one (y := y) hxr
    obtain ⟨hP, hA, -, -⟩ := mul_para hxP hyP
    refine ⟨hr, by rw [hm]; exact hP, ?_⟩
    have : blkEE (x * y) = blkEE x * blkEE y := by
      calc blkEE (x * y) = blkA (lmat (x * y)) := rfl
        _ = blkA (lmat x * lmat y) := by rw [hm]
        _ = blkA (lmat x) * blkA (lmat y) := hA
        _ = blkEE x * blkEE y := rfl
    rw [this, Matrix.det_mul, hxd, hyd, mul_one]

@[expose] def Lam (hK : UnitaryFieldData 2 f K) : Subgroup (Gam hK) :=
  { LamM hK with
    inv_mem' := fun {x} hx => by
      have := finite_Gam hK
      have h1 : x⁻¹ = x ^ (orderOf x - 1) := by
        apply inv_eq_of_mul_eq_one_right
        rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [h1]
      exact (LamM hK).pow_mem hx _ }

theorem mem_Lam {x : Gam hK} :
    x ∈ Lam hK ↔ x.1.right = 1 ∧ IsPara (lmat x) ∧ (blkEE x).det = 1 := Iff.rfl

@[expose] def scalG (c : Kˣ) : Gam hK :=
  ⟨SemidirectProduct.inl (GeneralLinearGroup.scalar (HypIndex 2 1) c), scalarSim_mem hK c⟩

theorem Phi_scalG (c : Kˣ) : Phi hK (scalG c) = 1 :=
  Phi_eq_one_iff.2 ⟨by simp [scalG], c, by simp [scalG]⟩

theorem lmat_scalG (c : Kˣ) : lmat (scalG c : Gam hK) = Matrix.scalar (HypIndex 2 1) (c : K) := by
  simp [lmat, scalG]

theorem isPara_scalar (c : K) : IsPara (Matrix.scalar (HypIndex 2 1) c) := by
  refine ⟨fun i => ?_, fun i j => ?_, fun j => ?_⟩ <;>
    simp [Matrix.scalar_apply]

theorem Phi_injOn_Lam {x y : Gam hK} (hx : x ∈ Lam hK) (hy : y ∈ Lam hK)
    (h : Phi hK x = Phi hK y) : x = y := by
  have hxy : x⁻¹ * y ∈ Lam hK := mul_mem (inv_mem hx) hy
  have h1 : Phi hK (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 h1
  have hdet := hxy.2.2
  have hm : lmat (x⁻¹ * y) = Matrix.scalar (HypIndex 2 1) (c : K) := by
    change ((((x⁻¹ * y : Gam hK) : SemiGL (HypIndex 2 1) K).left : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
    rw [hc]
    rfl
  have hE : blkEE (x⁻¹ * y) = Matrix.scalar (Fin 2) (c : K) := by
    ext i j
    simp [blkEE, hm, Matrix.scalar_apply, Matrix.diagonal_apply]
  rw [hE] at hdet
  have hcc : (c : K) = 1 ∨ (c : K) = -1 := by
    simpa [Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply] using hdet
  have hc1 : c = 1 := by
    have := hK.charP
    apply Units.ext
    rcases hcc with h | h
    · exact h
    · rw [h, CharTwo.neg_eq, Units.val_one]
  have hone : x⁻¹ * y = 1 := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rw [hc, hc1]
      simp
    · exact (Phi_eq_one_iff.1 h1).1
  exact inv_mul_eq_one.1 hone

theorem exists_lam_lift (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {ρ : MulAut (hypPSU hK 2 1)}
    (hρD : ρ ∈ Dlin hK)
    (hρN : ρ ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1)))) :
    ∃ x ∈ Lam hK, Phi hK x = ρ := by
  obtain ⟨x, hx⟩ := Phi_surjective hK ρ
  have hr : x.1.right = 1 := (mem_Dlin_iff hx).1 hρD
  have hρ' : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))) := by
    rw [hx]; exact hρN
  have hPW := isParaW_of_act_mem (fun v hv => act_mem_Vsub hZ hρ' hv)
  have hP := isPara_of_paraW hPW
  have hd : (blkEE x).det ≠ 0 := det_blkEE_ne_zero hPW
  have : Finite K := hK.finite
  have hchar : ringChar K = 2 := by
    have := hK.charP
    exact ringChar.eq K 2
  obtain ⟨c, hc⟩ := FiniteField.isSquare_of_char_two hchar (blkEE x).det⁻¹
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
    exact hd hc
  refine ⟨x * scalG (Units.mk0 c hc0), ?_, ?_⟩
  · have hmul := lmat_mul_of_right_one (y := scalG (Units.mk0 c hc0)) hr
    rw [lmat_scalG] at hmul
    simp only [Units.val_mk0] at hmul
    obtain ⟨hP', hA, -, -⟩ := mul_para hP (isPara_scalar c)
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.coe_mul, SemidirectProduct.mul_right, hr]
      simp [scalG]
    · rw [hmul]
      exact hP'
    · have hE : blkEE (x * scalG (Units.mk0 c hc0)) = blkEE x * Matrix.scalar (Fin 2) c := by
        calc blkEE (x * scalG (Units.mk0 c hc0)) = blkA (lmat (x * scalG (Units.mk0 c hc0))) :=
              rfl
          _ = blkA (lmat x * Matrix.scalar (HypIndex 2 1) c) := by rw [hmul]
          _ = blkA (lmat x) * blkA (Matrix.scalar (HypIndex 2 1) c) := hA
          _ = blkEE x * Matrix.scalar (Fin 2) c := by
              congr 1
              ext i j
              simp [blkA, Matrix.scalar_apply, Matrix.diagonal_apply]
      rw [hE, Matrix.det_mul]
      simp [Matrix.scalar_apply, Matrix.det_diagonal]
      rw [pow_two, ← hc]
      exact mul_inv_cancel₀ hd
  · rw [map_mul, Phi_scalG, mul_one, hx]

end LamDef

end CFSG.RankThree.PartOne.U5K.Hyp
