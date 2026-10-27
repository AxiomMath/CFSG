module

public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7TvSwapped
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7WittTriple
public import CFSG.LocalAnalysis.StandardType.ExcPos.ExcU7WittBridge

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos.ExcU7

open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.RankThree.Classical2
open scoped MatrixGroups Matrix

variable {L : Type} [Field L]

private theorem u7wp_inv_transpose_eq_map_of_fix (σ : L ≃+* L) {k : SL(6, L)}
    (hk : stdUnitary σ.toRingHom k = k) :
    (((k : Matrix (Fin 6) (Fin 6) L))⁻¹)ᵀ =
      (k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom := by
  have h1 : (k : Matrix (Fin 6) (Fin 6) L) =
      (((k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom)⁻¹)ᵀ := by
    have := coe_stdUnitary σ.toRingHom k
    rw [hk] at this
    exact this
  have hdet : IsUnit ((k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom).det := by
    change IsUnit (σ.toRingHom.mapMatrix (k : Matrix (Fin 6) (Fin 6) L)).det
    rw [← RingHom.map_det, k.2, map_one]
    exact isUnit_one
  have h1T : ((k : Matrix (Fin 6) (Fin 6) L))ᵀ =
      (((k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom))⁻¹ := by
    have := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_transpose] at this
  have h2 : ((k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom) *
      ((k : Matrix (Fin 6) (Fin 6) L))ᵀ = 1 := by
    rw [h1T, Matrix.mul_nonsing_inv _ hdet]
  have h3 : (((k : Matrix (Fin 6) (Fin 6) L))ᵀ)⁻¹ =
      (k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom := Matrix.inv_eq_left_inv h2
  rw [Matrix.transpose_nonsing_inv]
  exact h3

private theorem u7wp_sum_swap (σ : L ≃+* L) {x y : Fin 6 → L}
    (hx : ∀ i, σ (σ (x i)) = x i) (h : ∑ i, σ (x i) * y i = 0) :
    ∑ i, σ (y i) * x i = 0 := by
  have h' : ∑ i, x i * σ (y i) = 0 := by
    have := congrArg σ h
    simpa only [map_sum, map_mul, hx, map_zero] using this
  calc ∑ i, σ (y i) * x i = ∑ i, x i * σ (y i) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = 0 := h'

private theorem u7wp_sigma_ne_zero (σ : L ≃+* L) {b : L} (hb : b ≠ 0) : σ b ≠ 0 :=
  fun h => hb (σ.injective (by rw [h, map_zero]))

theorem exists_fixed_witt_pair [IsAlgClosed L] [CharP L 2] (σ : L ≃+* L) {f : ℕ} (hf : 1 ≤ f)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {v u v' u' : Fin 6 → L}
    (hv : ∀ i, σ (σ (v i)) = v i) (hu : ∀ i, σ (σ (u i)) = u i)
    (hv' : ∀ i, σ (σ (v' i)) = v' i) (hu' : ∀ i, σ (σ (u' i)) = u' i)
    (hind : LinearIndependent L ![v, u]) (hind' : LinearIndependent L ![v', u'])
    (hvv : ∑ i, σ (v i) * v i = 0) (huu : ∑ i, σ (u i) * u i = 0)
    (hvu : ∑ i, σ (v i) * u i = 0)
    (hvv' : ∑ i, σ (v' i) * v' i = 0) (huu' : ∑ i, σ (u' i) * u' i = 0)
    (hvu' : ∑ i, σ (v' i) * u' i = 0) :
    ∃ k : SL(6, L), stdUnitary σ.toRingHom k = k ∧
      (∃ a : L, a ≠ 0 ∧ (k : Matrix (Fin 6) (Fin 6) L).mulVec v = a • v') ∧
      ∃ b : L, b ≠ 0 ∧ (k : Matrix (Fin 6) (Fin 6) L).mulVec u = b • u' := by
  obtain ⟨w, hw, hli, hww, hvw, huw⟩ :=
    exists_isotropic_third σ hf hσ hv hu hind hvv huu hvu
  obtain ⟨w', hw', hli', hww', hvw', huw'⟩ :=
    exists_isotropic_third σ hf hσ hv' hu' hind' hvv' huu' hvu'
  obtain ⟨k, hk, l, hl, h0, h1, -⟩ :=
    exists_fixed_witt_two σ hf hσ (u := ![v, u, w]) (u' := ![v', u', w'])
      (by
        intro j i
        fin_cases j <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
            Matrix.head_cons] <;>
          first | exact hv i | exact hu i | exact hw i)
      (by
        intro j i
        fin_cases j <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
            Matrix.head_cons] <;>
          first | exact hv' i | exact hu' i | exact hw' i)
      hli hli'
      (by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
            Matrix.head_cons]
        · exact hvv
        · exact hvu
        · exact hvw
        · exact u7wp_sum_swap σ hv hvu
        · exact huu
        · exact huw
        · exact u7wp_sum_swap σ hv hvw
        · exact u7wp_sum_swap σ hu huw
        · exact hww)
      (by
        intro i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
            Matrix.head_cons]
        · exact hvv'
        · exact hvu'
        · exact hvw'
        · exact u7wp_sum_swap σ hv' hvu'
        · exact huu'
        · exact huw'
        · exact u7wp_sum_swap σ hv' hvw'
        · exact u7wp_sum_swap σ hu' huw'
        · exact hww')
  exact ⟨k, hk, ⟨l, hl, by simpa using h0⟩, ⟨1, one_ne_zero, by simpa using h1⟩⟩

theorem exists_fixed_conj_swapped [IsAlgClosed L] [CharP L 2] (σ : L ≃+* L) {f : ℕ} (hf : 1 ≤ f)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {T T' : Subgroup SL(6, L)} (hT : IsTvGroup T)
    (hT' : IsTvGroup T') (hs : IsSwappedTv (stdUnitary σ.toRingHom) T)
    (hs' : IsSwappedTv (stdUnitary σ.toRingHom) T') :
    ∃ k : SL(6, L), stdUnitary σ.toRingHom k = k ∧ T.map (MulAut.conj k).toMonoidHom = T' := by
  obtain ⟨v, φ, hv, hφ, hv0, hφ0, h, hTv⟩ := exists_rational_of_stable σ hT hs.1
  obtain ⟨v', φ', hv', hφ', hv0', hφ0', h', hT'v⟩ := exists_rational_of_stable σ hT' hs'.1
  obtain ⟨hvv, hφφ, hnot⟩ := swapped_isotropic σ hv hφ hv0 hφ0 h (hTv ▸ hs)
  obtain ⟨hvv', hφ'φ', hnot'⟩ := swapped_isotropic σ hv' hφ' hv0' hφ0' h' (hT'v ▸ hs')
  set u : Fin 6 → L := fun i => σ (φ i) with hu_def
  set u' : Fin 6 → L := fun i => σ (φ' i) with hu'_def
  have hu : ∀ i, σ (σ (u i)) = u i := fun i => by simp only [hu_def, hφ i]
  have hu' : ∀ i, σ (σ (u' i)) = u' i := fun i => by simp only [hu'_def, hφ' i]
  have hu'_val : ∀ i, σ (u' i) = φ' i := fun i => by simp only [hu'_def, hφ' i]
  have hvu : ∑ i, σ (v i) * u i = 0 := by
    have hσh : ∑ i, σ (φ i) * σ (v i) = 0 := by
      have := congrArg σ h
      simpa only [dotProduct, map_sum, map_mul, map_zero] using this
    calc ∑ i, σ (v i) * u i = ∑ i, σ (v i) * σ (φ i) := by simp only [hu_def]
      _ = ∑ i, σ (φ i) * σ (v i) := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hσh
  have huu : ∑ i, σ (u i) * u i = 0 := by
    calc ∑ i, σ (u i) * u i = ∑ i, σ (σ (φ i)) * σ (φ i) := by simp only [hu_def]
      _ = ∑ i, φ i * σ (φ i) := Finset.sum_congr rfl fun i _ => by rw [hφ i]
      _ = ∑ i, σ (φ i) * φ i := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hφφ
  have hvu' : ∑ i, σ (v' i) * u' i = 0 := by
    have hσh : ∑ i, σ (φ' i) * σ (v' i) = 0 := by
      have := congrArg σ h'
      simpa only [dotProduct, map_sum, map_mul, map_zero] using this
    calc ∑ i, σ (v' i) * u' i = ∑ i, σ (v' i) * σ (φ' i) := by simp only [hu'_def]
      _ = ∑ i, σ (φ' i) * σ (v' i) := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hσh
  have huu' : ∑ i, σ (u' i) * u' i = 0 := by
    calc ∑ i, σ (u' i) * u' i = ∑ i, σ (σ (φ' i)) * σ (φ' i) := by simp only [hu'_def]
      _ = ∑ i, φ' i * σ (φ' i) := Finset.sum_congr rfl fun i _ => by rw [hφ' i]
      _ = ∑ i, σ (φ' i) * φ' i := Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hφ'φ'
  have hind : LinearIndependent L ![v, u] :=
    (LinearIndependent.pair_iff' hv0).mpr fun a ha => hnot ⟨a, ha.symm⟩
  have hind' : LinearIndependent L ![v', u'] :=
    (LinearIndependent.pair_iff' hv0').mpr fun a ha => hnot' ⟨a, ha.symm⟩
  obtain ⟨k, hk, ⟨a, ha, hkv⟩, ⟨b, hb, hku⟩⟩ :=
    exists_fixed_witt_pair σ hf hσ hv hu hv' hu' hind hind' hvv huu hvu hvv' huu' hvu'
  refine ⟨k, hk, ?_⟩
  rw [hTv, hT'v, tvGroup_map_conj h k]
  have hkey : (((k : Matrix (Fin 6) (Fin 6) L))⁻¹)ᵀ =
      (k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom := u7wp_inv_transpose_eq_map_of_fix σ hk
  have hσu : σ.toRingHom ∘ u = φ := by
    funext i
    rw [Function.comp_apply, hu_def]
    exact hφ i
  have hmat : ((k : Matrix (Fin 6) (Fin 6) L).map σ.toRingHom) *ᵥ φ =
      σ ∘ ((k : Matrix (Fin 6) (Fin 6) L) *ᵥ u) := by
    funext i
    have := RingHom.map_mulVec σ.toRingHom (k : Matrix (Fin 6) (Fin 6) L) u i
    rw [hσu] at this
    exact this.symm
  have hsec : Matrix.vecMul φ ((k⁻¹ : SL(6, L)) : Matrix (Fin 6) (Fin 6) L) = σ b • φ' := by
    rw [coe_inv_eq_nonsing_inv k, ← Matrix.mulVec_transpose, hkey, hmat, hku]
    funext i
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, map_mul, hu'_val]
  rw [hkv, hsec]
  have hsm : (σ b • φ') ⬝ᵥ (a • v') = 0 := by
    rw [smul_dotProduct, dotProduct_smul, h', smul_zero, smul_zero]
  rw [tvGroup_eq_iff (smul_ne_zero ha hv0') (smul_ne_zero (u7wp_sigma_ne_zero σ hb) hφ0')
    hv0' hφ0' hsm h']
  exact ⟨a⁻¹, (σ b)⁻¹, inv_ne_zero ha, inv_ne_zero (u7wp_sigma_ne_zero σ hb),
    by rw [smul_smul, inv_mul_cancel₀ ha, one_smul],
    by rw [smul_smul, inv_mul_cancel₀ (u7wp_sigma_ne_zero σ hb), one_smul]⟩

end CFSG.StandardType.LieKnownR2.ExcPos.ExcU7
