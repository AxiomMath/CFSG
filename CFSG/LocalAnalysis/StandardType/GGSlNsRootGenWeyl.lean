module

public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenTypeABlock
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerTypeADvdModel
import CFSG.CGT.Timmesfeld75.ListWCLinBasic
public import CFSG.Sporadic.Th.Max3.Core

public section

namespace CFSG.StandardType.SlNsRootGen

open Matrix Polynomial CoordSL CFSG.RankThree.CALinearPlane CFSG.Assembly TableB Multiplicative

theorem root_pow_neg_val {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}
    [NeZero p] (hζ : AdjoinRoot.root g ^ p = 1) (a : ZMod p) :
    AdjoinRoot.root g ^ (-a).val = (AdjoinRoot.root g ^ a.val)⁻¹ := by
  have hζ0 : AdjoinRoot.root g ≠ 0 := by
    intro h0
    rw [h0, zero_pow (NeZero.ne p)] at hζ
    exact zero_ne_one hζ
  by_cases ha : a = 0
  · subst ha
    simp
  · rw [ZMod.neg_val, if_neg ha]
    rw [pow_sub₀ (AdjoinRoot.root g) hζ0 (le_of_lt (ZMod.val_lt a)), hζ, one_mul]

section Swap

variable {K : Type} [Field K] (g : K[X]) [Fact (Irreducible g)] {n s r : ℕ}
  (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)

@[expose] noncomputable def swapSL [CharP (AdjoinRoot g) 2] (i j : Fin s) :
    SpecialLinearGroup (Fin n) K :=
  theta g ε (TypeA.permSL (Equiv.swap i j))

theorem swapSL_mem_pairBlock [CharP (AdjoinRoot g) 2] (i j : Fin s) :
    swapSL g ε i j ∈ pairBlock g ε i j := by
  rw [pairBlock, swapSL]
  exact Subgroup.mem_map_of_mem (theta g ε) TypeA.permSL_mem_coordBlockSL

variable {hC : (rootMat g).det = 1} {p : ℕ} [NeZero p]

theorem swapSL_conj [CharP (AdjoinRoot g) 2] (hCp : rootMat g ^ p = 1) (i j : Fin s)
    (t : Fin s → ZMod p) :
    swapSL g ε i j * torusSL ε hC hCp (ofAdd t) * (swapSL g ε i j)⁻¹ =
      torusSL ε hC hCp (ofAdd (swapMap i j t)) := by
  classical
  set P : SpecialLinearGroup (Fin s) (AdjoinRoot g) :=
    TypeA.permSL (Equiv.swap i j) with hP
  set D : Matrix (Fin s) (Fin s) (AdjoinRoot g) :=
    diagonal fun m => AdjoinRoot.root g ^ (t m).val with hD
  have hPmat : (P : Matrix (Fin s) (Fin s) (AdjoinRoot g)) =
      (Equiv.swap i j).permMatrix (AdjoinRoot g) := TypeA.coe_permSL _
  have hPinv : ((P⁻¹ : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
      Matrix (Fin s) (Fin s) (AdjoinRoot g)) =
      ((Equiv.swap i j)⁻¹).permMatrix (AdjoinRoot g) := by
    rw [TypeA.permSL_inv]
    exact TypeA.coe_permSL _
  have hraw : (P : Matrix (Fin s) (Fin s) (AdjoinRoot g)) * D *
      ((P⁻¹ : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
        Matrix (Fin s) (Fin s) (AdjoinRoot g)) =
      diagonal (fun m => AdjoinRoot.root g ^ (t (Equiv.swap i j m)).val) := by
    rw [hPmat, hPinv]
    exact TypeANbrDvd.permMatrix_mul_diagonal_mul_inv (Equiv.swap i j)
      (fun m => AdjoinRoot.root g ^ (t m).val)
  have hcoe : ((swapSL g ε i j : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = thetaMat g ε (P : Matrix (Fin s) (Fin s) (AdjoinRoot g)) := by
    rw [swapSL, coe_theta]
  have hcoeinv : (((swapSL g ε i j)⁻¹ : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
      thetaMat g ε ((P⁻¹ : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
        Matrix (Fin s) (Fin s) (AdjoinRoot g)) := by
    rw [swapSL, ← map_inv, coe_theta]
  rw [torusSL_apply, torusSL_apply]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe, hcoeinv]
  change thetaMat g ε (P : Matrix (Fin s) (Fin s) (AdjoinRoot g)) *
      SLNS.nsMat ε (rootMat g) (fun m => (t m).val) *
      thetaMat g ε ((P⁻¹ : SpecialLinearGroup (Fin s) (AdjoinRoot g)) :
        Matrix (Fin s) (Fin s) (AdjoinRoot g)) =
      SLNS.nsMat ε (rootMat g) (fun m => (swapMap i j t m).val)
  rw [← thetaMat_diagonal (g := g) (ε := ε) (k := fun m => (t m).val)]
  rw [← thetaMat_mul, ← thetaMat_mul, hraw]
  rw [thetaMat_diagonal]
  rfl

end Swap

section ResultSwap

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [NeZero p]

theorem exists_swap_mem_pairBlock [CharP K 2] (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1) (i j : Fin s) :
    ∃ w ∈ pairBlock g ε i j, ∀ t : Fin s → ZMod p,
      w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (swapMap i j t)) := by
  haveI : CharP (AdjoinRoot g) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot g)).injective 2
  exact ⟨swapSL g ε i j, swapSL_mem_pairBlock g ε i j, fun t => swapSL_conj g ε hCp i j t⟩

end ResultSwap

section Frobenius

variable {K : Type} [Field K] [Fintype K] (g : K[X]) [Fact (Irreducible g)]

@[expose] noncomputable def frobAlgEquiv : AdjoinRoot g ≃ₐ[K] AdjoinRoot g :=
  letI : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g)

theorem frobAlgEquiv_apply (x : AdjoinRoot g) :
    frobAlgEquiv g x = x ^ Nat.card K := by
  rw [frobAlgEquiv, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]

variable {p : ℕ} [NeZero p] [Fact p.Prime]

theorem frobAlgEquiv_root (hζ : AdjoinRoot.root g ^ p = 1) (hpK : p ∣ Nat.card K + 1) :
    frobAlgEquiv g (AdjoinRoot.root g) = (AdjoinRoot.root g)⁻¹ := by
  rw [frobAlgEquiv_apply]
  obtain ⟨m, hm⟩ := hpK
  have h1 : AdjoinRoot.root g ^ (Nat.card K + 1) = 1 := by
    rw [hm, pow_mul, hζ, one_pow]
  have h2 : AdjoinRoot.root g ^ Nat.card K * AdjoinRoot.root g = 1 := by
    rwa [pow_succ] at h1
  exact eq_inv_of_mul_eq_one_right (by rw [mul_comm]; exact h2)

theorem frobAlgEquiv_apply_apply (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (x : AdjoinRoot g) :
    frobAlgEquiv g (frobAlgEquiv g x) = x := by
  have hroot : frobAlgEquiv g (frobAlgEquiv g (AdjoinRoot.root g)) = AdjoinRoot.root g := by
    rw [frobAlgEquiv_root g hζ hpK, map_inv₀, frobAlgEquiv_root g hζ hpK, inv_inv]
  have hcomp : (frobAlgEquiv g).toAlgHom.comp (frobAlgEquiv g).toAlgHom =
      AlgHom.id K (AdjoinRoot g) := by
    apply AdjoinRoot.algHom_ext
    simpa using hroot
  exact congrArg (fun f : AdjoinRoot g →ₐ[K] AdjoinRoot g => f x) hcomp

end Frobenius

section Neg

variable {K : Type} [Field K] [Fintype K] (g : K[X]) [Fact (Irreducible g)] {n s r p : ℕ}
  [NeZero p] [Fact p.Prime] {ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r}

@[expose] noncomputable def negTau (i : Fin s) :
    Fin s → (AdjoinRoot g ≃ₐ[K] AdjoinRoot g) :=
  Function.update (fun _ => AlgEquiv.refl) i (frobAlgEquiv g)

theorem negTau_apply_self (i : Fin s) :
    negTau g i i = frobAlgEquiv g := by
  rw [negTau, Function.update_apply, if_pos rfl]

theorem negTau_apply_of_ne {i m : Fin s} (hm : m ≠ i) :
    negTau g i m = AlgEquiv.refl := by
  rw [negTau, Function.update_apply, if_neg hm]

theorem negTau_apply_apply (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (i m : Fin s) (x : AdjoinRoot g) :
    negTau g i m (negTau g i m x) = x := by
  by_cases hm : m = i
  · subst m
    rw [negTau_apply_self]
    exact frobAlgEquiv_apply_apply g hζ hpK x
  · rw [negTau_apply_of_ne g hm]
    rfl

@[expose] noncomputable def negMove (i : Fin s) :
    ((Fin s → AdjoinRoot g) × (Fin r → K)) ≃ₗ[K]
      ((Fin s → AdjoinRoot g) × (Fin r → K)) :=
  moveEquiv g (Equiv.refl (Fin s)) (negTau g i)

theorem negMove_apply (i : Fin s)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    negMove g i x = (fun m => negTau g i m (x.1 m), x.2) :=
  rfl

theorem negMove_negMove (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (i : Fin s)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    negMove g i (negMove g i x) = x := by
  refine Prod.ext (funext fun m => ?_) rfl
  rw [negMove_apply, negMove_apply]
  exact negTau_apply_apply g hζ hpK i m (x.1 m)

@[expose] noncomputable def negMat (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : Matrix (Fin n) (Fin n) K :=
  LinearMap.toMatrix' ((frameCoords g ε).toLinearMap ∘ₗ (negMove g i).toLinearMap ∘ₗ
    (frameCoords g ε).symm.toLinearMap)

theorem frameForm_negMat (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s) :
    frameForm g ε (negMat g ε i) = (negMove g i).toLinearMap := by
  refine LinearMap.ext fun x => ?_
  rw [frameForm_apply, negMat, LinearMap.toMatrix'_mulVec]
  simp

theorem negMat_mul_self (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : negMat g ε i * negMat g ε i = 1 := by
  apply frameForm_injective g ε
  rw [frameForm_mul, frameForm_one]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, frameForm_negMat]
  exact negMove_negMove g hζ hpK i x

theorem negMat_det [CharP K 2] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : (negMat g ε i).det = 1 :=
  CFSG.CGT.Timmesfeld75.det_eq_one_of_mul_self (negMat_mul_self g hζ hpK ε i)

@[expose] noncomputable def negSL [CharP K 2] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : SpecialLinearGroup (Fin n) K :=
  ⟨negMat g ε i, negMat_det g hζ hpK ε i⟩

theorem frameCoords_negMove_of_notMem (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) {a : Fin n} (ha : a ∉ blockCoords ε i)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    frameCoords g ε (negMove g i x) a = frameCoords g ε x a := by
  rcases ha' : ε a with ⟨c, m⟩ | j
  · have hm : m ≠ i := by
      intro h
      exact ha (by rw [mem_blockCoords_inl ha']; exact h)
    rw [frameCoords_apply, frameCoords_apply, negMove_apply]
    simp [ha', negTau_apply_of_ne g hm]
  · rw [frameCoords_apply, frameCoords_apply, negMove_apply]
    simp [ha']

theorem negMove_single_basis (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) {c : Fin (rootPB g).dim} {m : Fin s} (hm : m ≠ i) :
    negMove g i ((Pi.single m ((rootPB g).basis c), 0) :
      (Fin s → AdjoinRoot g) × (Fin r → K)) =
      ((Pi.single m ((rootPB g).basis c), 0) :
        (Fin s → AdjoinRoot g) × (Fin r → K)) := by
  refine Prod.ext (funext fun l => ?_) rfl
  change negTau g i l (((Pi.single m ((rootPB g).basis c), 0) :
      (Fin s → AdjoinRoot g) × (Fin r → K)).1 l) =
    ((Pi.single m ((rootPB g).basis c), 0) :
      (Fin s → AdjoinRoot g) × (Fin r → K)).1 l
  by_cases hl : l = m
  · rw [hl, negTau_apply_of_ne g hm]
    simp
  · simp [hl]

theorem negMat_mulVec_single_of_notMem
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s) {b : Fin n}
    (hb : b ∉ blockCoords ε i) :
    negMat g ε i *ᵥ Pi.single b 1 = Pi.single b 1 := by
  classical
  rcases hb' : ε b with ⟨c, m⟩ | j
  · have hm : m ≠ i := by
      intro h
      exact hb (by rw [mem_blockCoords_inl hb']; exact h)
    have hy : (frameCoords g ε).symm (Pi.single b 1) =
        ((Pi.single m ((rootPB g).basis c), 0) :
          (Fin s → AdjoinRoot g) × (Fin r → K)) := by
      rw [LinearEquiv.symm_apply_eq]
      rw [frameCoords_single_basis]
      congr 1
      exact ((Equiv.symm_apply_eq ε).mpr hb'.symm).symm
    have hstep : negMat g ε i *ᵥ Pi.single b 1 =
        frameCoords g ε (frameForm g ε (negMat g ε i)
          ((frameCoords g ε).symm (Pi.single b 1))) := by
      rw [frameCoords_frameForm, LinearEquiv.apply_symm_apply]
    rw [hstep, frameForm_negMat, hy]
    change frameCoords g ε (negMove g i ((Pi.single m ((rootPB g).basis c), 0) :
      (Fin s → AdjoinRoot g) × (Fin r → K))) = Pi.single b 1
    rw [negMove_single_basis g ε i hm, ← hy, LinearEquiv.apply_symm_apply]
  · exact absurd (mem_blockCoords_inr hb') hb

theorem negMat_apply_of_notMem
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s) {a b : Fin n}
    (ha : a ∉ blockCoords ε i) :
    negMat g ε i a b = if a = b then 1 else 0 := by
  classical
  set y : (Fin s → AdjoinRoot g) × (Fin r → K) :=
    (frameCoords g ε).symm (Pi.single b 1) with hy
  have h1 : frameCoords g ε (negMove g i y) a = negMat g ε i a b := by
    have h := congrFun (frameCoords_frameForm (g := g) (ε := ε)
      (u := negMat g ε i) (x := y)) a
    rw [frameForm_negMat, hy, LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one,
      Matrix.col_apply] at h
    exact h.symm
  rw [← h1, frameCoords_negMove_of_notMem g ε i ha, hy, LinearEquiv.apply_symm_apply]
  simp [Pi.single_apply]

theorem negSL_mul_self [CharP K 2] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : negSL g hζ hpK ε i * negSL g hζ hpK ε i = 1 :=
  Subtype.ext (negMat_mul_self g hζ hpK ε i)

theorem negSL_mem_zeroBlock [CharP K 2] (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) : negSL g hζ hpK ε i ∈ zeroBlock g ε i := by
  rw [zeroBlock, mem_coordBlockSL_iff]
  intro a b hab
  have hcoe : ((negSL g hζ hpK ε i : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = negMat g ε i := rfl
  rw [hcoe]
  rcases hab with ha | hb
  · exact negMat_apply_of_notMem g ε i ha
  · have hcol : negMat g ε i *ᵥ Pi.single b 1 = Pi.single b 1 :=
      negMat_mulVec_single_of_notMem g ε i hb
    have h2 := congrFun hcol a
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at h2
    rw [h2]
    simp [Pi.single_apply]

theorem negMove_torusAct (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (i : Fin s) (t : Fin s → ZMod p)
    (x : (Fin s → AdjoinRoot g) × (Fin r → K)) :
    negMove g i (torusAct g (fun m => (t m).val) x) =
      torusAct g (fun m => (negMap i t m).val) (negMove g i x) := by
  refine Prod.ext (funext fun m => ?_) rfl
  rw [negMove_apply, negMove_apply]
  change negTau g i m (AdjoinRoot.root g ^ (t m).val * x.1 m) =
    AdjoinRoot.root g ^ ((negMap i t m).val) * negTau g i m (x.1 m)
  by_cases hm : m = i
  · subst m
    have hneg : AdjoinRoot.root g ^ ((negMap i t i).val) =
        (AdjoinRoot.root g ^ (t i).val)⁻¹ := by
      rw [negMap, Function.update_self]
      exact root_pow_neg_val hζ (t i)
    rw [negTau_apply_self]
    rw [map_mul, map_pow, frobAlgEquiv_root g hζ hpK, inv_pow, hneg]
  · rw [negTau_apply_of_ne g hm, negMap, Function.update_apply, if_neg hm]
    rfl

theorem negMat_mul_nsMat (hζ : AdjoinRoot.root g ^ p = 1)
    (hpK : p ∣ Nat.card K + 1) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
    (i : Fin s) (t : Fin s → ZMod p) :
    negMat g ε i * SLNS.nsMat ε (rootMat g) (fun m => (t m).val) * negMat g ε i =
      SLNS.nsMat ε (rootMat g) (fun m => (negMap i t m).val) := by
  apply frameForm_injective g ε
  rw [frameForm_mul, frameForm_mul, frameForm_negMat]
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, frameForm_nsMat, frameForm_nsMat]
  change negMove g i (torusAct g (fun m => (t m).val) (negMove g i x)) =
    torusAct g (fun m => (negMap i t m).val) x
  rw [negMove_torusAct g hζ hpK, negMove_negMove g hζ hpK]

theorem negSL_conj [CharP K 2] (hC : (rootMat g).det = 1) (hCp : rootMat g ^ p = 1)
    (hζ : AdjoinRoot.root g ^ p = 1) (hpK : p ∣ Nat.card K + 1)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (i : Fin s)
    (t : Fin s → ZMod p) :
    negSL g hζ hpK ε i * torusSL ε hC hCp (ofAdd t) * (negSL g hζ hpK ε i)⁻¹ =
      torusSL ε hC hCp (ofAdd (negMap i t)) := by
  have hw : negSL g hζ hpK ε i * negSL g hζ hpK ε i = 1 :=
    negSL_mul_self g hζ hpK ε i
  have hwinv : (negSL g hζ hpK ε i)⁻¹ = negSL g hζ hpK ε i :=
    inv_eq_of_mul_eq_one_right hw
  rw [torusSL_apply, torusSL_apply, hwinv]
  apply Subtype.ext
  change negMat g ε i * SLNS.nsMat ε (rootMat g) (fun m => (t m).val) * negMat g ε i =
    SLNS.nsMat ε (rootMat g) (fun m => (negMap i t m).val)
  exact negMat_mul_nsMat g hζ hpK ε i t

end Neg

section ResultNeg

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [NeZero p]

theorem exists_neg_mem_zeroBlock [Finite K] [CharP K 2] [Fact p.Prime]
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1)
    (hζ : AdjoinRoot.root g ^ p = 1) (hpK : p ∣ Nat.card K + 1) (i : Fin s) :
    ∃ w ∈ zeroBlock g ε i, ∀ t : Fin s → ZMod p,
      w * torusSL ε hC hCp (ofAdd t) * w⁻¹ = torusSL ε hC hCp (ofAdd (negMap i t)) := by
  haveI : Fintype K := Fintype.ofFinite K
  exact ⟨negSL g hζ hpK ε i, negSL_mem_zeroBlock g hζ hpK ε i,
    fun t => negSL_conj g hC hCp hζ hpK ε i t⟩

end ResultNeg

end CFSG.StandardType.SlNsRootGen

end
