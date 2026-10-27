module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeModelII
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSpRoot
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPSURoot

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open scoped Matrix

private theorem rckRPrsg_altSiegel_one {F : Type} [Field F]
    {a₁ a₂ b₁ b₂ : Fin 1 ⊕ Fin 1 → F}
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) b₂ = 1)
    (h₀ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) F) b₁ = 0) : False := by
  obtain ⟨h0a, -, -, h0ba⟩ := h₀
  let i0 : Fin 1 := 0
  have h1' : a₁ (Sum.inl i0) * b₁ (Sum.inr i0) -
      a₁ (Sum.inr i0) * b₁ (Sum.inl i0) = 1 := by
    rw [sub_eq_add_neg]
    simpa [i0, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_one] using h₁
  have h0a' : a₁ (Sum.inl i0) * a₂ (Sum.inr i0) -
      a₁ (Sum.inr i0) * a₂ (Sum.inl i0) = 0 := by
    rw [sub_eq_add_neg]
    simpa [i0, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_one] using h0a
  have h0ba' : a₂ (Sum.inl i0) * b₁ (Sum.inr i0) -
      a₂ (Sum.inr i0) * b₁ (Sum.inl i0) = 0 := by
    rw [sub_eq_add_neg]
    simpa [i0, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type,
      Fin.sum_univ_one] using h0ba
  have ht : a₂ (Sum.inl i0) = 0 := by
    have h : a₂ (Sum.inl i0) =
        -a₂ (Sum.inl i0) * (a₁ (Sum.inl i0) * b₁ (Sum.inr i0) -
          a₁ (Sum.inr i0) * b₁ (Sum.inl i0) - 1) +
        b₁ (Sum.inl i0) * (a₁ (Sum.inl i0) * a₂ (Sum.inr i0) -
          a₁ (Sum.inr i0) * a₂ (Sum.inl i0)) +
        a₁ (Sum.inl i0) * (a₂ (Sum.inl i0) * b₁ (Sum.inr i0) -
          a₂ (Sum.inr i0) * b₁ (Sum.inl i0)) := by
      ring
    rw [h1', h0a', h0ba'] at h
    simpa using h
  have hu : a₂ (Sum.inr i0) = 0 := by
    have h : a₂ (Sum.inr i0) =
        -a₂ (Sum.inr i0) * (a₁ (Sum.inl i0) * b₁ (Sum.inr i0) -
          a₁ (Sum.inr i0) * b₁ (Sum.inl i0) - 1) +
        b₁ (Sum.inr i0) * (a₁ (Sum.inl i0) * a₂ (Sum.inr i0) -
          a₁ (Sum.inr i0) * a₂ (Sum.inl i0)) +
        a₁ (Sum.inr i0) * (a₂ (Sum.inl i0) * b₁ (Sum.inr i0) -
          a₂ (Sum.inr i0) * b₁ (Sum.inl i0)) := by
      ring
    rw [h1', h0a', h0ba'] at h
    simpa using h
  have ha2 : a₂ = 0 := by
    funext i
    rcases i with i | i
    · have hi : i = i0 := Subsingleton.elim i i0
      rw [hi]
      exact ht
    · have hi : i = i0 := Subsingleton.elim i i0
      rw [hi]
      exact hu
  have h : (0 : F) = 1 := by
    simpa [ha2, dotProduct, Matrix.mulVec] using h₂
  exact zero_ne_one h

private theorem rckRPrsg_two_le_n_of_altSiegel {F : Type} [Field F] {n : ℕ}
    {a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F}
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 1)
    (h₀ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 0) :
    2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exfalso
      have h : (0 : F) = 1 := by
        simpa [dotProduct, Matrix.mulVec, Matrix.fromBlocks] using h₁
      exact zero_ne_one h
    · exfalso
      exact rckRPrsg_altSiegel_one h₁ h₂ h₀
  · exact hn

private theorem rckRPrsg_two_le_n_of_unitTransv {F : Type} [Field F]
    (σ : F ≃+* F) {n : ℕ} {v w : Fin n → F}
    (hv : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hvw : Matrix.vecMul (fun i => σ (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1) :
    2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hn01 : n = 0 ∨ n = 1 := by omega
    rcases hn01 with rfl | rfl
    · exfalso
      have h : (0 : F) = 1 := by
        simpa [dotProduct] using hvw
      exact zero_ne_one h
    · exfalso
      have hv' : σ (v 0) * v 0 = 0 := by
        simpa [dotProduct, Matrix.vecMul, Unitary.antidiag, Fin.sum_univ_one] using hv
      have hv0 : v 0 = 0 := by
        rcases mul_eq_zero.mp hv' with h | h
        · exact σ.injective (by simpa using h)
        · exact h
      have h : σ (v 0) * w 0 = 1 := by
        simpa [dotProduct, Matrix.vecMul, Unitary.antidiag, Fin.sum_univ_one] using hvw
      rw [hv0, map_zero, zero_mul] at h
      exact zero_ne_one h
  · exact hn

theorem rckRPRootSubOf_PSp_of_matTransv
    {n f : ℕ} {R' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {v : (Fin n ⊕ Fin n) → GaloisField 2 f} (hv : v ≠ 0)
    (hR : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)) :
    RCKRPRootSubOf (ggU .PSp n f) R' := by
  classical
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      exfalso
      apply hv
      funext i
      rcases i with i | i <;> exact Fin.elim0 i
    · exact hn
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  let x : (Fin n ⊕ Fin n) → GaloisField 2 f := Pi.single i (v i)⁻¹
  let J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f) :=
    Matrix.fromBlocks 0 1 (-1) 0
  let w : (Fin n ⊕ Fin n) → GaloisField 2 f := -(J *ᵥ x)
  have hJ : J * J = -1 := by
    simpa [J, CFSG.Timmesfeld.ARS.CaseM.spGram] using
      (CFSG.Timmesfeld.ARS.CaseM.spGram_mul_self (n := n) (F := GaloisField 2 f))
  have hJw : J *ᵥ w = x := by
    simp only [w, Matrix.mulVec_neg, Matrix.mulVec_mulVec, hJ, Matrix.neg_mulVec,
      Matrix.one_mulVec, neg_neg]
  have hx : v ⬝ᵥ x = 1 := by
    simp only [x, dotProduct_single]
    exact mul_inv_cancel₀ hi
  have hvw : v ⬝ᵥ J *ᵥ w = 1 := by
    rw [hJw, hx]
  obtain ⟨β, hβ, hlong, u, h1, -⟩ :=
    exists_conj_rootGroup_eq_matTransvGroup_PSp n (GaloisField 2 f) hn v w hvw
  change ∃ γ ∈ (Symplectic.rootDatum n (GaloisField 2 f)).roots,
    (GGLongRoot (Symplectic.rootDatum n (GaloisField 2 f)) γ ∨
      2 • γ ∉ (Symplectic.rootDatum n (GaloisField 2 f)).roots) ∧
    ∃ u' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      R' = ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup γ).map
        (MulAut.conj u').toMonoidHom
  exact ⟨β, hβ, Or.inl hlong, u,
    Subgroup.map_injective (Subgroup.subtype_injective _) (hR.trans h1.symm)⟩

theorem rckRPRootSubOf_PSp_of_altSiegel
    {n f : ℕ} {R' : Subgroup ↥(CFSG.Open.StatedSp n (GaloisField 2 f))}
    {a₁ a₂ b₁ b₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 1)
    (h₀ : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      b₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂ = 0 ∧
      a₂ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁ = 0)
    (hR : R'.map (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂) :
    RCKRPRootSubOf (ggU .PSp n f) R' := by
  have hn : 2 ≤ n := rckRPrsg_two_le_n_of_altSiegel h₁ h₂ h₀
  obtain ⟨β, hβ, h2β, u, h1, -⟩ :=
    exists_conj_rootGroup_eq_altSiegelGroup_PSp n (GaloisField 2 f) hn
      a₁ a₂ b₁ b₂ h₁ h₂ h₀
  change ∃ γ ∈ (Symplectic.rootDatum n (GaloisField 2 f)).roots,
    (GGLongRoot (Symplectic.rootDatum n (GaloisField 2 f)) γ ∨
      2 • γ ∉ (Symplectic.rootDatum n (GaloisField 2 f)).roots) ∧
    ∃ u' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)),
      R' = ((Symplectic.rootDatum n (GaloisField 2 f)).rootGroup γ).map
        (MulAut.conj u').toMonoidHom
  exact ⟨β, hβ, Or.inr h2β, u,
    Subgroup.map_injective (Subgroup.subtype_injective _) (hR.trans h1.symm)⟩

theorem rckRPRootSubOf_PSU_of_unitTransv
    {n g : ℕ} {R' : Subgroup ↥(Unitary.SU
      (CFSG.LieType.BorelTits.unitaryInvolution (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n)}
    {v w : Fin n → GaloisField 2 (2 * (g + 1))}
    (hv : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i)) (Unitary.antidiag n) ⬝ᵥ v = 0)
    (hw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (w i)) (Unitary.antidiag n) ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => (CFSG.LieType.BorelTits.unitaryInvolution
      (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) (v i)) (Unitary.antidiag n) ⬝ᵥ w = 1)
    (hR : R'.map (Unitary.SU (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)) n).subtype =
      unitTransvGroup (CFSG.LieType.BorelTits.unitaryInvolution
        (GaloisField 2 (2 * (g + 1))) 2 (g + 1)).toRingHom (Unitary.antidiag n) v) :
    RCKRPRootSubOf (ggU .PSU n (g + 1)) R' := by
  let F₀ := GaloisField 2 (2 * (g + 1))
  let σ := CFSG.LieType.BorelTits.unitaryInvolution F₀ 2 (g + 1)
  have hc : Nat.card F₀ = (2 ^ (g + 1)) ^ 2 := by
    dsimp only [F₀]
    exact CFSG.LieType.Universal.card_galoisField_two_mul 2 (g + 1) (by omega)
  have hn : 2 ≤ n := rckRPrsg_two_le_n_of_unitTransv σ hv hvw
  obtain ⟨β, hβ, hlong, u, h1, -⟩ :=
    exists_conj_rootGroup_eq_unitTransvGroup_PSU (F := F₀) (f := g + 1) hc n hn
      v w hv hw hvw
  change ∃ γ ∈ (Unitary.rootDatum hc n).roots,
    (GGLongRoot (Unitary.rootDatum hc n) γ ∨
      2 • γ ∉ (Unitary.rootDatum hc n).roots) ∧
    ∃ u' : ↥(Unitary.SU σ n),
      R' = ((Unitary.rootDatum hc n).rootGroup γ).map
        (MulAut.conj u').toMonoidHom
  exact ⟨β, hβ, Or.inl hlong, u,
    Subgroup.map_injective (Subgroup.subtype_injective _) (hR.trans h1.symm)⟩

end CFSG.StandardType.RCKRP
