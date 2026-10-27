module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestBlock
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionSLRestNonsplit
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace NSFrame

section Coords

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] {e s r : ℕ} {ι κ : Type}

@[expose] noncomputable def coords (β : Basis (Fin e) K L) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r) :
    ((ι → L) × (κ → K)) ≃ₗ[K] ((Fin e × Fin s) ⊕ Fin r → K) where
  toFun uw := Sum.elim (fun p => β.repr (uw.1 (eι.symm p.2)) p.1) (fun j => uw.2 (eκ.symm j))
  map_add' uw uw' := by
    funext x
    rcases x with ⟨a, i⟩ | j <;> simp
  map_smul' c uw := by
    funext x
    rcases x with ⟨a, i⟩ | j <;> simp
  invFun v := (fun i => ∑ a, v (Sum.inl (a, eι i)) • β a, fun j => v (Sum.inr (eκ j)))
  left_inv uw := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [Sum.elim_inl, Equiv.symm_apply_apply]
      exact β.sum_repr (uw.1 i)
    · simp
  right_inv v := by
    funext x
    rcases x with ⟨a, i⟩ | j
    · simp only [Sum.elim_inl, Equiv.apply_symm_apply, Basis.repr_sum_self]
    · simp

theorem coords_apply_inl (β : Basis (Fin e) K L) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r)
    (u : ι → L) (w : κ → K) (a : Fin e) (i : Fin s) :
    coords β eι eκ (u, w) (Sum.inl (a, i)) = β.repr (u (eι.symm i)) a := rfl

theorem coords_apply_inr (β : Basis (Fin e) K L) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r)
    (u : ι → L) (w : κ → K) (j : Fin r) :
    coords β eι eκ (u, w) (Sum.inr j) = w (eκ.symm j) := rfl

omit [Field L] [Algebra K L] in
theorem blockDiagonal_mulVec_apply (M : Fin s → Matrix (Fin e) (Fin e) K)
    (v : Fin e × Fin s → K) (a : Fin e) (i : Fin s) :
    (blockDiagonal M *ᵥ v) (a, i) = (M i *ᵥ fun b => v (b, i)) a := by
  simp only [mulVec, dotProduct, blockDiagonal_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem coords_mul (β : Basis (Fin e) K L) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r) (ζ : L)
    (k : ι → ℕ) (u : ι → L) (w : κ → K) :
    coords β eι eκ (fun i => ζ ^ k i * u i, w) =
      SLNS.nsCore (r := r) (Algebra.leftMulMatrix β ζ) (k ∘ eι.symm) *ᵥ
        coords β eι eκ (u, w) := by
  funext x
  rcases x with ⟨a, i⟩ | j
  · rw [coords_apply_inl, SLNS.nsCore, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply,
      zero_mulVec, Pi.zero_apply, add_zero, blockDiagonal_mulVec_apply, Function.comp_apply,
      ← map_pow, ← Algebra.leftMulMatrix_mulVec_repr]
    rfl
  · rw [coords_apply_inr, SLNS.nsCore, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply,
      zero_mulVec, Pi.zero_apply, zero_add, one_mulVec]
    rfl

end Coords

section Det

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L] [Finite L] {e s r n : ℕ}

theorem exists_det_comm (β : Basis (Fin e) K L) (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (ζ : L) (i₀ : Fin s) (d : K) :
    ∃ E : Matrix (Fin n) (Fin n) K, E.det = d ∧ ∀ k : Fin s → ℕ,
      E * SLNS.nsMat ε (Algebra.leftMulMatrix β ζ) k =
        SLNS.nsMat ε (Algebra.leftMulMatrix β ζ) k * E := by
  classical
  obtain ⟨c, hc⟩ := FiniteField.norm_surjective K L d
  set M := Algebra.leftMulMatrix β c with hM
  set f : Fin s → Matrix (Fin e) (Fin e) K := fun i => if i = i₀ then M else 1 with hf
  set E₀ : Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) K :=
    fromBlocks (blockDiagonal f) 0 0 1 with hE₀
  refine ⟨E₀.submatrix ε ε, ?_, fun k => ?_⟩
  · rw [det_submatrix_equiv_self, hE₀, det_fromBlocks_zero₂₁, det_blockDiagonal, det_one, mul_one,
      ← hc, Algebra.norm_eq_matrix_det β]
    rw [Finset.prod_eq_single i₀]
    · rw [hf]
      simp only [↓reduceIte, hM]
    · intro i _ hi
      rw [hf]
      simp only [hi, ↓reduceIte, det_one]
    · intro h
      exact absurd (Finset.mem_univ i₀) h
  · have hcomm : ∀ i, f i * (Algebra.leftMulMatrix β ζ) ^ k i =
        (Algebra.leftMulMatrix β ζ) ^ k i * f i := by
      intro i
      by_cases hi : i = i₀
      · rw [hf]
        simp only [hi, ↓reduceIte]
        rw [hM, ← map_pow, ← map_mul, ← map_mul, mul_comm]
      · rw [hf]
        simp only [hi, ↓reduceIte, one_mul, mul_one]
    rw [SLNS.nsMat, submatrix_mul_equiv, submatrix_mul_equiv, hE₀, SLNS.nsCore, fromBlocks_multiply,
      fromBlocks_multiply, ← blockDiagonal_mul, ← blockDiagonal_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, hcomm]

end Det

section Frame

variable {K : Type} [Field K] [Finite K] {ℓ n : ℕ}

omit [Finite K] in
theorem nsMat_eq_one_of_isEmpty {e s r : ℕ} (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r)
    (C : Matrix (Fin e) (Fin e) K) (k : Fin s → ℕ) (hs : s = 0) : SLNS.nsMat ε C k = 1 := by
  subst hs
  ext x y
  rw [SLNS.nsMat, submatrix_apply]
  rcases hx : ε x with ⟨a, i⟩ | u
  · exact i.elim0
  · rcases hy : ε y with ⟨b, j⟩ | v
    · exact j.elim0
    · rw [SLNS.nsCore, fromBlocks_apply₂₂, one_apply, one_apply]
      congr 1
      apply propext
      constructor
      · rintro rfl
        exact ε.injective (hx.trans hy.symm)
      · rintro rfl
        exact Sum.inr_injective (hx.symm.trans hy)

theorem exists_nsFrame (hℓ : ℓ.Prime) (hK : ¬ ℓ ∣ Nat.card K - 1) (hℓK : (ℓ : K) ≠ 0)
    (S : Set (Matrix (Fin n) (Fin n) K)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) :
    ∃ (e s r : ℕ) (C : Matrix (Fin e) (Fin e) K) (_ : C.det = 1)
      (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (A₀ : Matrix.SpecialLinearGroup (Fin n) K),
      C ^ ℓ = 1 ∧ (∀ j : ℕ, ¬ ℓ ∣ j → ∀ c : K, IsUnit (C ^ j - c • 1)) ∧
        ∀ x ∈ S, ∃ k : Fin s → ℕ, x * (A₀ : Matrix (Fin n) (Fin n) K) =
          (A₀ : Matrix (Fin n) (Fin n) K) * SLNS.nsMat ε C k := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hne : ¬ IsUnit (cyclotomic ℓ K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero ℓ K),
      natDegree_cyclotomic, Nat.totient_prime hℓ]
    have := hℓ.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero ℓ K)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hg0 : g ≠ 0 := hg.ne_zero
  have hζ : IsPrimitiveRoot (AdjoinRoot.root g) ℓ := root_isPrimitiveRoot hℓ hℓK hgd
  set pb := AdjoinRoot.powerBasis hg0 with hpb
  have : Module.Finite K (AdjoinRoot g) := pb.finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  set β := pb.basis with hβ
  set C := Algebra.leftMulMatrix β (AdjoinRoot.root g) with hCdef
  have hCp : C ^ ℓ = 1 := by rw [hCdef, ← map_pow, hζ.pow_eq_one, map_one]
  have hnorm : Algebra.norm K (AdjoinRoot.root g) = 1 := by
    refine OrdPNS.eq_one_of_pow_eq_one hℓ hK ?_
    rw [← map_pow, hζ.pow_eq_one, map_one]
  have hCdet : C.det = 1 := by rw [hCdef, ← Algebra.norm_eq_matrix_det, hnorm]
  have hCunit : ∀ j : ℕ, ¬ ℓ ∣ j → ∀ c : K, IsUnit (C ^ j - c • 1) := by
    intro j hj c
    have hne : AdjoinRoot.root g ^ j - algebraMap K (AdjoinRoot g) c ≠ 0 := by
      intro h0
      have h1 : AdjoinRoot.root g ^ j = algebraMap K (AdjoinRoot g) c := sub_eq_zero.mp h0
      have hc : c ^ ℓ = 1 := by
        apply (algebraMap K (AdjoinRoot g)).injective
        rw [map_pow, ← h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, map_one]
      have hc1 := OrdPNS.eq_one_of_pow_eq_one hℓ hK hc
      rw [hc1, map_one] at h1
      exact hj (hζ.dvd_of_pow_eq_one j h1)
    have h2 : C ^ j - c • 1 =
        Algebra.leftMulMatrix β (AdjoinRoot.root g ^ j - algebraMap K (AdjoinRoot g) c) := by
      rw [map_sub, map_pow, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    rw [h2]
    exact (IsUnit.mk0 _ hne).map (Algebra.leftMulMatrix β)
  obtain ⟨ι, κ, _, _, Φ, hΦ⟩ := exists_blockFrame (g := g) hℓ hℓK hgd (V := Fin n → K)
    (Matrix.toLinAlgEquiv' '' S)
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hSc x hx y hy).map _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hSp x hx, map_one])
  set eι := Fintype.equivFin ι with heι
  set eκ := Fintype.equivFin κ with heκ
  set Ψ := (coords β eι eκ).symm.trans Φ with hΨ
  have hcard : Fintype.card ((Fin pb.dim × Fin (Fintype.card ι)) ⊕ Fin (Fintype.card κ)) = n := by
    have h1 := Ψ.finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at h1
  set ε := (Fintype.equivFinOfCardEq hcard).symm with hε
  set Ψ' := (LinearEquiv.funCongrLeft K K ε).symm.trans Ψ with hΨ'
  set Q := LinearMap.toMatrix' (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K)) with hQ
  set Q' := LinearMap.toMatrix' (Ψ'.symm : (Fin n → K) →ₗ[K] (Fin n → K)) with hQ'
  have hQQ' : Q * Q' = 1 := by
    rw [hQ, hQ', ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hQ'Q : Q' * Q = 1 := by
    rw [hQ, hQ', ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hrel : ∀ x ∈ S, ∃ k : Fin (Fintype.card ι) → ℕ, x * Q = Q * SLNS.nsMat ε C k := by
    intro x hx
    obtain ⟨k, hk⟩ := hΦ (Matrix.toLinAlgEquiv' x) ⟨x, hx, rfl⟩
    refine ⟨k ∘ eι.symm, Matrix.toLin'.injective ?_⟩
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, hQ, Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun w => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply, Matrix.toLin'_apply]
    set uw := (coords β eι eκ).symm (w ∘ ε.symm) with huw
    have hw : w ∘ ε.symm = coords β eι eκ uw := (LinearEquiv.apply_symm_apply _ _).symm
    have h1 : (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K)) w = Φ uw := rfl
    have h2 : (Ψ' : (Fin n → K) →ₗ[K] (Fin n → K)) (SLNS.nsMat ε C (k ∘ eι.symm) *ᵥ w) =
        Φ ((coords β eι eκ).symm ((SLNS.nsMat ε C (k ∘ eι.symm) *ᵥ w) ∘ ε.symm)) := rfl
    have h3 : (SLNS.nsMat ε C (k ∘ eι.symm) *ᵥ w) ∘ ε.symm =
        coords β eι eκ (fun i => AdjoinRoot.root g ^ k i * uw.1 i, uw.2) := by
      rw [coords_mul, ← hw, SLNS.nsMat, submatrix_mulVec_equiv, Function.comp_assoc,
        Equiv.self_comp_symm, Function.comp_id]
    rw [h1, h2, h3, LinearEquiv.symm_apply_apply]
    have h4 := hk uw.1 uw.2
    rw [Matrix.toLinAlgEquiv'_apply] at h4
    exact h4
  have hdetQ : Q.det * Q'.det = 1 := by rw [← det_mul, hQQ', det_one]
  have hQ0 : Q.det ≠ 0 := left_ne_zero_of_mul_eq_one hdetQ
  by_cases hs : Fintype.card ι = 0
  ·
    refine ⟨pb.dim, Fintype.card ι, Fintype.card κ, C, hCdet, ε, 1, hCp, hCunit,
      fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hrel x hx
    refine ⟨k, ?_⟩
    rw [nsMat_eq_one_of_isEmpty ε C k hs, Matrix.mul_one] at hk
    have hx1 : x = 1 := by
      calc x = x * Q * Q' := by rw [Matrix.mul_assoc, hQQ', Matrix.mul_one]
        _ = 1 := by rw [hk, hQQ']
    rw [hx1, nsMat_eq_one_of_isEmpty ε C k hs, Matrix.SpecialLinearGroup.coe_one,
      Matrix.mul_one]
  · obtain ⟨E, hEdet, hEcomm⟩ := exists_det_comm β ε (AdjoinRoot.root g)
      (⟨0, Nat.pos_of_ne_zero hs⟩ : Fin (Fintype.card ι)) Q.det⁻¹
    have hA₀ : (Q * E).det = 1 := by rw [det_mul, hEdet, mul_inv_cancel₀ hQ0]
    refine ⟨pb.dim, Fintype.card ι, Fintype.card κ, C, hCdet, ε, ⟨Q * E, hA₀⟩, hCp, hCunit,
      fun x hx => ?_⟩
    obtain ⟨k, hk⟩ := hrel x hx
    refine ⟨k, ?_⟩
    change x * (Q * E) = Q * E * SLNS.nsMat ε C k
    rw [← Matrix.mul_assoc, hk, Matrix.mul_assoc, Matrix.mul_assoc, hEcomm k]

end Frame


end NSFrame

end CFSG.StandardType
