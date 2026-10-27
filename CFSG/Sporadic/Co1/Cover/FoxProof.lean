module

public import CFSG.Sporadic.Co1.Cover.CertChecks

public section

namespace CFSG.Sporadic.Co1.Cover

open CFSG.Sporadic.SmallF2 Matrix

theorem hl_proof
    (l : Fin 11 → ZMod 2) (hA : Amatᵀ *ᵥ l = l) (hB : Bmatᵀ *ᵥ l = l) : l = 0 := by
  have h := congrArg (fun M => M *ᵥ l) hl_cert
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, hA, hB,
    Matrix.one_mulVec, sub_self, Matrix.mulVec_zero, add_zero] at h
  exact h.symm

theorem Rsym_mulVec (c : Matrix (Fin 11) (Fin 11) (ZMod 2)) (hs : cᵀ = c) :
    Rsym *ᵥ (fun ij : I2 => c ij.1 ij.2) = 0 := by
  funext ij
  have hc : c ij.2 ij.1 = c ij.1 ij.2 := by
    have := congrFun (congrFun hs ij.1) ij.2
    simpa using this
  simp only [Matrix.mulVec, dotProduct, Rsym, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Pi.zero_apply]
  rw [hc]
  exact CharTwo.add_self_eq_zero _

theorem Rdiag_mulVec (c : Matrix (Fin 11) (Fin 11) (ZMod 2)) (hd : ∀ i, c i i = 0) :
    Rdiag *ᵥ (fun ij : I2 => c ij.1 ij.2) = 0 := by
  funext ij
  simp only [Matrix.mulVec, dotProduct, Rdiag, Pi.zero_apply]
  rw [Finset.sum_eq_zero]
  intro kl _
  by_cases h : ij = kl ∧ ij.1 = ij.2
  · obtain ⟨rfl, h2⟩ := h
    simp [h2, hd]
  · simp [h]

theorem Rinv_mulVec (M c : Matrix (Fin 11) (Fin 11) (ZMod 2)) (h : Mᵀ * c * M = c) :
    Rinv M *ᵥ (fun ij : I2 => c ij.1 ij.2) = 0 := by
  funext ij
  have h1 : ∑ kl : I2, M kl.1 ij.1 * M kl.2 ij.2 * c kl.1 kl.2 = c ij.1 ij.2 := by
    have := congrFun (congrFun h ij.1) ij.2
    rw [Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul] at this
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm] at this
    refine Eq.trans ?_ this
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  simp only [Matrix.mulVec, dotProduct, Rinv, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply]
  rw [h1]
  exact CharTwo.add_self_eq_zero _

theorem hC_proof
    (c : Matrix (Fin 11) (Fin 11) (ZMod 2)) (hs : cᵀ = c) (hd : ∀ i, c i i = 0)
    (hA : Amatᵀ * c * Amat = c) (hB : Bmatᵀ * c * Bmat = c) : c = 0 := by
  have h := congrArg (fun M => M *ᵥ (fun ij : I2 => c ij.1 ij.2)) hC_cert
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Rsym_mulVec c hs, Rdiag_mulVec c hd,
    Rinv_mulVec Amat c hA, Rinv_mulVec Bmat c hB, Matrix.mulVec_zero, add_zero,
    Matrix.one_mulVec] at h
  ext i j
  exact (congrFun h (i, j)).symm

section Fox

variable {P : Type*} [Group P] (a b : P)

@[expose] def eltPos (w : List Bool) : P := (w.map fun c => if c then b else a).prod

theorem eltPos_cons (c : Bool) (w : List Bool) :
    eltPos a b (c :: w) = (if c then b else a) * eltPos a b w := by
  simp [eltPos]

variable (ρ : P →* ((Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)))
  (A B : Matrix (Fin 11) (Fin 11) (ZMod 2)) (hA : ∀ v, ρ a v = A *ᵥ v) (hB : ∀ v, ρ b v = B *ᵥ v)

include hA hB in
theorem rho_eltPos (w : List Bool) (x : Fin 11 → ZMod 2) :
    ρ (eltPos a b w) x = actPos A B w x := by
  induction w with
  | nil =>
    have : eltPos a b [] = 1 := by simp [eltPos]
    rw [this, map_one]
    rfl
  | cons c w ih =>
    rw [eltPos_cons, map_mul, LinearEquiv.mul_apply, ih]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, actPos]
      exact hA _
    · simp only [↓reduceIte, actPos]
      exact hB _

include hA hB in
theorem fox_sound (l : P → Fin 11 → ZMod 2)
    (hl : ∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x) :
    ∀ (w : List Bool) (x : Fin 11 → ZMod 2), l (eltPos a b w) ⬝ᵥ x =
      (foxVec A B w x).1 ⬝ᵥ l a + (foxVec A B w x).2 ⬝ᵥ l b
  | [], x => by
    have h := hl 1 1 x
    rw [mul_one, map_one] at h
    have h0 : l 1 ⬝ᵥ x = 0 := by
      have : l 1 ⬝ᵥ x = l 1 ⬝ᵥ x + l 1 ⬝ᵥ x := by simpa using h
      exact left_eq_add.1 this
    have : eltPos a b [] = 1 := by simp [eltPos]
    simp [this, h0, foxVec]
  | c :: w, x => by
    rw [eltPos_cons, hl, rho_eltPos a b ρ A B hA hB, fox_sound l hl w x]
    cases c
    · simp only [Bool.false_eq_true, ↓reduceIte, foxVec, Prod.fst_add, Prod.snd_add, add_dotProduct,
        zero_dotProduct]
      rw [dotProduct_comm (l a)]
      ring
    · simp only [↓reduceIte, foxVec, Prod.fst_add, Prod.snd_add, add_dotProduct, zero_dotProduct]
      rw [dotProduct_comm (l b)]
      ring


theorem l_one_dot {P : Type*} [Group P] (ρ : P →* ((Fin 11 → ZMod 2) ≃ₗ[ZMod 2] (Fin 11 → ZMod 2)))
    (l : P → Fin 11 → ZMod 2) (hl : ∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x)
    (x : Fin 11 → ZMod 2) : l 1 ⬝ᵥ x = 0 := by
  have h := hl 1 1 x
  rw [mul_one, map_one] at h
  have : l 1 ⬝ᵥ x = l 1 ⬝ᵥ x + l 1 ⬝ᵥ x := by simpa using h
  exact left_eq_add.1 this

theorem flat_dot (p : (Fin 11 → ZMod 2) × (Fin 11 → ZMod 2)) (x y : Fin 11 → ZMod 2) :
    flat p ⬝ᵥ Fin.append x y = p.1 ⬝ᵥ x + p.2 ⬝ᵥ y := by
  simp only [dotProduct, flat]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem deltaMat_mulVec_left (A B : Matrix (Fin 11) (Fin 11) (ZMod 2)) (φ : Fin 11 → ZMod 2)
    (j : Fin 11) : (deltaMat A B *ᵥ φ) (Fin.castAdd 11 j) = ((Aᵀ + 1) *ᵥ φ) j := by
  simp only [Matrix.mulVec, dotProduct, deltaMat, Fin.append_left]

theorem deltaMat_mulVec_right (A B : Matrix (Fin 11) (Fin 11) (ZMod 2)) (φ : Fin 11 → ZMod 2)
    (j : Fin 11) : (deltaMat A B *ᵥ φ) (Fin.natAdd 11 j) = ((Bᵀ + 1) *ᵥ φ) j := by
  simp only [Matrix.mulVec, dotProduct, deltaMat, Fin.append_right]

theorem dot_coboundary (A : Matrix (Fin 11) (Fin 11) (ZMod 2)) (φ l : Fin 11 → ZMod 2)
    (h : l = (Aᵀ + 1) *ᵥ φ) (x : Fin 11 → ZMod 2) : l ⬝ᵥ x = φ ⬝ᵥ A *ᵥ x + φ ⬝ᵥ x := by
  rw [h, Matrix.add_mulVec, Matrix.one_mulVec, add_dotProduct, Matrix.mulVec_transpose,
    Matrix.dotProduct_mulVec]

include hA hB in
theorem hfox_proof (hrel : ∀ i, eltPos a b (wordsPos i) = 1)
    (hAm : A = Amat) (hBm : B = Bmat)
    (l : P → Fin 11 → ZMod 2) (hl : ∀ p q x, l (p * q) ⬝ᵥ x = l p ⬝ᵥ ρ q x + l q ⬝ᵥ x)
    (h0 : l a ⬝ᵥ toVecD 11 x0mask = 0) :
    ∃ φ : Fin 11 → ZMod 2, (∀ x, l a ⬝ᵥ x = φ ⬝ᵥ ρ a x + φ ⬝ᵥ x) ∧
      (∀ x, l b ⬝ᵥ x = φ ⬝ᵥ ρ b x + φ ⬝ᵥ x) := by
  subst hAm hBm
  set u : Fin (11 + 11) → ZMod 2 := Fin.append (l a) (l b) with hu
  have hR : foxMatC *ᵥ u = 0 := by
    funext r
    show (fun c => foxMatC r c) ⬝ᵥ u = 0
    have e : (fun c => foxMatC r c) =
        flat (foxVec Amat Bmat (wordsPos r.1) (Pi.single r.2 1)) :=
      funext (foxMatC_apply r)
    rw [e, hu, flat_dot, ← fox_sound a b ρ Amat Bmat hA hB l hl (wordsPos r.1) (Pi.single r.2 1),
      hrel]
    exact l_one_dot ρ l hl _
  have hL : lamMat (toVecD 11 x0mask) *ᵥ u = 0 := by
    funext i
    show (fun c => lamMat (toVecD 11 x0mask) i c) ⬝ᵥ u = 0
    have e : (fun c => lamMat (toVecD 11 x0mask) i c) = flat (toVecD 11 x0mask, 0) := rfl
    rw [e, hu, flat_dot, zero_dotProduct, add_zero, dotProduct_comm]
    exact h0
  have key : u = deltaMat Amat Bmat *ᵥ (listMat foxXrows 11 (11 + 11) *ᵥ u) := by
    have h := congrArg (fun M => M *ᵥ u) fox_cert
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hR, hL, Matrix.mulVec_zero, add_zero,
      Matrix.one_mulVec] at h
    exact h.symm
  set φ := listMat foxXrows 11 (11 + 11) *ᵥ u with hφ
  have hla : l a = (Amatᵀ + 1) *ᵥ φ := by
    funext j
    have h1 := congrFun key (Fin.castAdd 11 j)
    rw [deltaMat_mulVec_left] at h1
    rw [hu, Fin.append_left] at h1
    exact h1
  have hlb : l b = (Bmatᵀ + 1) *ᵥ φ := by
    funext j
    have h1 := congrFun key (Fin.natAdd 11 j)
    rw [deltaMat_mulVec_right] at h1
    rw [hu, Fin.append_right] at h1
    exact h1
  exact ⟨φ, fun x => by rw [hA x]; exact dot_coboundary Amat φ (l a) hla x,
    fun x => by rw [hB x]; exact dot_coboundary Bmat φ (l b) hlb x⟩

end Fox

end CFSG.Sporadic.Co1.Cover
