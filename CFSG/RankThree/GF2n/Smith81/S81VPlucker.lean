module

public import CFSG.RankThree.GF2n.Smith81.S81VModelSwap
public import CFSG.RankThree.GF2n.Smith81.S81UFrame

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube
  CFSG.RankThree.GF2n.Smith81.A5Cube Module Matrix

private theorem pl1_swapM_apply {F : Type} [Field F] (p q : Fin 3 ⊕ Fin 3) :
    swapM F p q = if q = Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p then 1 else 0 := by
  simp only [swapM, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply]

private theorem pl1_alt3_columns {R : Type*} [CommRing R] {V W : Type*} [AddCommGroup V] [Module R V]
    [AddCommGroup W] [Module R W] (ω : V [⋀^Fin 3]→ₗ[R] W) (a : Fin 3 → V)
    (A : Matrix (Fin 3) (Fin 3) R) :
    ω (fun j => ∑ i, A i j • a i) = A.det • ω a := by
  let Lc : (Fin 3 → R) →ₗ[R] V :=
    { toFun := fun c => ∑ i, c i • a i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  let Ψ : (Fin 3 → R) [⋀^Fin 3]→ₗ[R] W := ω.compLinearMap Lc
  let E : Basis (Fin 3) R (Fin 3 → R) := Pi.basisFun R (Fin 3)
  have hΨE : Ψ E = ω a := by
    show ω (fun j => ∑ i, E j i • a i) = ω a
    congr 1
    funext j
    simp [E, Pi.basisFun_apply, Pi.single_apply]
  have hΨ : Ψ = E.det.smulRight (Ψ E) := by
    refine Module.Basis.ext_alternating E fun v hv => ?_
    let s : Equiv.Perm (Fin 3) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    change Ψ (E ∘ s) = (E.det.smulRight (Ψ E)) (E ∘ s)
    rw [AlternatingMap.smulRight_apply, AlternatingMap.map_perm, AlternatingMap.map_perm,
      Module.Basis.det_self]
    simp
  have hM : E.toMatrix (fun j i => A i j) = A := by
    ext i j
    simp [E, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hdet : E.det (fun j i => A i j) = A.det := by
    rw [Module.Basis.det_apply, hM]
  have hv := DFunLike.congr_fun hΨ (fun j i => A i j)
  rw [AlternatingMap.smulRight_apply, hdet, hΨE] at hv
  exact hv

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {b : Fin 3 → Fin 6 → F} {K : Type} [Field K]
  (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ e3uT0Vec b) (e₀ : K ≃+* Fσ σ)

include hσ hf

private theorem pl1_sU_smul_fam (p : Fin 3 ⊕ Fin 3) :
    sU hσ hf • fam e3uT0Vec b p =
      fam e3uT0Vec b (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p) := by
  rw [smul_fam hσ hf, gm_sU hσ hf,
    Fintype.sum_eq_single (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) p)]
  · rw [pl1_swapM_apply, Equiv.swap_apply_self, if_pos rfl, one_smul]
  · intro q hq
    have hne : p ≠ Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) q := by
      intro h
      apply hq
      rw [h, Equiv.swap_apply_self]
    rw [pl1_swapM_apply, if_neg hne, zero_smul]

private theorem pl1_uK_inl (H : HermK σ e₀) (j : Fin 3) :
    uK hσ hf H • fam e3uT0Vec b (Sum.inl j) = fam e3uT0Vec b (Sum.inl j) := by
  rw [smul_fam hσ hf, gm_uK hσ hf, Fintype.sum_sum_type]
  simp [fam, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.one_apply]

private theorem pl1_uK_inr (H : HermK σ e₀) (j : Fin 3) :
    uK hσ hf H • fam e3uT0Vec b (Sum.inr j) =
      fam e3uT0Vec b (Sum.inr j) + ∑ i, H.mat i j • fam e3uT0Vec b (Sum.inl i) := by
  rw [smul_fam hσ hf, gm_uK hσ hf, Fintype.sum_sum_type]
  simp [fam, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.one_apply] <;> abel

theorem rho_sU_pt0 :
    rho F ((sU hσ hf : SUid σ 6) : GL (Fin 6) F) (pt0 F) =
      exteriorPower.ιMulti F 3 ![b 0, e3uT0Vec 1, e3uT0Vec 2] := by
  have hi : ∀ i : Fin 3,
      (((sU hσ hf : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec i) =
        fam e3uT0Vec b (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) (Sum.inl i)) :=
    fun i => pl1_sU_smul_fam hσ hf (Sum.inl i)
  have h0 : fam e3uT0Vec b (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) (Sum.inl 0)) =
      b 0 := by
    rw [Equiv.swap_apply_left]
    rfl
  have h1 : fam e3uT0Vec b (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) (Sum.inl 1)) =
      e3uT0Vec 1 := by
    simp [Equiv.swap_apply_def, fam]
  have h2 : fam e3uT0Vec b (Equiv.swap (Sum.inl (0 : Fin 3)) (Sum.inr (0 : Fin 3)) (Sum.inl 2)) =
      e3uT0Vec 2 := by
    simp [Equiv.swap_apply_def, fam]
  rw [pt0_eq_ιMulti_T0, rho_ιMulti]
  congr 1
  funext i
  fin_cases i
  · exact (hi 0).trans h0
  · exact (hi 1).trans h1
  · exact (hi 2).trans h2

theorem rho_uK_sU_pt0 (t : K) :
    rho F ((uK hσ hf (t • n1K σ e₀) : SUid σ 6) : GL (Fin 6) F)
        (rho F ((sU hσ hf : SUid σ 6) : GL (Fin 6) F) (pt0 F)) =
      rho F ((sU hσ hf : SUid σ 6) : GL (Fin 6) F) (pt0 F) + ((e₀ t : Fσ σ) : F) • pt0 F := by
  have hH : (t • n1K σ e₀).mat = ((e₀ t : Fσ σ) : F) • Matrix.single 0 0 1 := by
    rw [HermK.mat_smul, n1K_mat]
  have hsumc : ∑ i, (t • n1K σ e₀).mat i 0 • fam e3uT0Vec b (Sum.inl i) =
      ((e₀ t : Fσ σ) : F) • e3uT0Vec 0 := by
    rw [hH, Fintype.sum_eq_single 0]
    · simp [Matrix.smul_apply, Matrix.single_apply, fam]
    · intro i hi
      simp [Matrix.smul_apply, Matrix.single_apply, hi, Ne.symm hi]
  have hu0 : (((uK hσ hf (t • n1K σ e₀) : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
      (b 0) = b 0 + ((e₀ t : Fσ σ) : F) • e3uT0Vec 0 := by
    have h := pl1_uK_inr hσ hf e₀ (t • n1K σ e₀) 0
    rw [hsumc] at h
    exact h
  have hu1 : (((uK hσ hf (t • n1K σ e₀) : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
      (e3uT0Vec 1) = e3uT0Vec 1 :=
    pl1_uK_inl hσ hf e₀ (t • n1K σ e₀) 1
  have hu2 : (((uK hσ hf (t • n1K σ e₀) : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
      (e3uT0Vec 2) = e3uT0Vec 2 :=
    pl1_uK_inl hσ hf e₀ (t • n1K σ e₀) 2
  have hA : (![e3uT0Vec 0, e3uT0Vec 1, e3uT0Vec 2] : Fin 3 → Fin 6 → F) = e3uT0Vec := by
    funext i
    fin_cases i <;> rfl
  have hvec : exteriorPower.ιMulti F 3
      (fun i => (((uK hσ hf (t • n1K σ e₀) : SUid σ 6) : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
        (![b 0, e3uT0Vec 1, e3uT0Vec 2] i)) =
      exteriorPower.ιMulti F 3 ![b 0 + ((e₀ t : Fσ σ) : F) • e3uT0Vec 0, e3uT0Vec 1, e3uT0Vec 2] := by
    congr 1
    funext i
    fin_cases i
    · exact hu0
    · exact hu1
    · exact hu2
  rw [rho_sU_pt0 hσ hf, rho_ιMulti, hvec, ι3_add_fst, ι3_smul_fst, hA, pt0_eq_ιMulti_T0]

theorem rho_pt0_of_mem_Pstab {g : SUid σ 6} (hg : g ∈ Pstab σ (Wa e3uT0Vec)) :
    rho F (g : GL (Fin 6) F) (pt0 F) = (blkA hσ hf g).det • pt0 F := by
  have hcol : ∀ j : Fin 3,
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (e3uT0Vec j) =
        ∑ i, blkA hσ hf g i j • e3uT0Vec i := by
    intro j
    obtain ⟨H, hgH⟩ := Pstab_decomp hσ hf (RingEquiv.refl (Fσ σ)) g hg
    have hL : levi hσ hf (blkA hσ hf g) (blkA_det_ne hσ hf hg) (blkA_det_fixed hσ hf hg) •
        fam e3uT0Vec b (Sum.inl j) = ∑ i, blkA hσ hf g i j • fam e3uT0Vec b (Sum.inl i) := by
      rw [smul_fam hσ hf, Fintype.sum_sum_type, gm_levi hσ hf]
      simp [fam, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
    have hfix : uK hσ hf H • ∑ i, blkA hσ hf g i j • fam e3uT0Vec b (Sum.inl i) =
        ∑ i, blkA hσ hf g i j • fam e3uT0Vec b (Sum.inl i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [smul_comm, pl1_uK_inl hσ hf (RingEquiv.refl (Fσ σ)) H i]
    have hg' : g • fam e3uT0Vec b (Sum.inl j) =
        ∑ i, blkA hσ hf g i j • fam e3uT0Vec b (Sum.inl i) := by
      conv_lhs => rw [hgH]
      rw [mul_smul, hL, hfix]
    exact hg'
  rw [pt0_eq_ιMulti_T0, rho_ιMulti]
  simp only [hcol]
  exact pl1_alt3_columns (exteriorPower.ιMulti F 3) (e3uT0Vec : Fin 3 → Fin 6 → F) (blkA hσ hf g)

end CFSG.RankThree.GF2n.Smith81.S81V
