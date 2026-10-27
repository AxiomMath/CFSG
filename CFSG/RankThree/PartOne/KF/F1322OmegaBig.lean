module

public import CFSG.RankThree.PartOne.KF.F1322OmegaEmbed
public import CFSG.RankThree.PartOne.KF.F1322OmegaRot
public import CFSG.RankThree.PartOne.KF.F1322OmegaRep
public import CFSG.RankThree.PartOne.KF.F1322OmegaRefl
public import CFSG.RankThree.PartOne.KF.F1322OmegaIdx
public import CFSG.RankThree.PartOne.KF.F1322OmegaInv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.KF1322

open Matrix CFSG.RankThree.SubgroupLists CFSG.RepresentationTheory

section EmbGL

variable {K : Type*} [Field K] {ι : Matrix (Fin 3) (Fin 2) K} {π : Matrix (Fin 2) (Fin 3) K}

@[expose] def embMat (h1 : π * ι = 1) : Matrix (Fin 2) (Fin 2) K →* Matrix (Fin 3) (Fin 3) K where
  toFun := emb ι π
  map_one' := emb_one
  map_mul' R R' := (emb_mul h1 R R').symm

@[expose] def embGL (h1 : π * ι = 1) : GL (Fin 2) K →* GL (Fin 3) K :=
  Units.map (embMat h1)

theorem coe_embGL (h1 : π * ι = 1) (y : GL (Fin 2) K) :
    ((embGL h1 y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      emb ι π (y : Matrix (Fin 2) (Fin 2) K) := rfl

theorem embGL_injective (h1 : π * ι = 1) : Function.Injective (embGL h1) :=
  Units.map_injective (emb_injective h1)

theorem embGL_mem_soGL {M : Matrix (Fin 3) (Fin 3) K} {Δ : Matrix (Fin 2) (Fin 2) K}
    (hMt : Mᵀ = M) (hΔ : Δᵀ = Δ) (h1 : π * ι = 1) (h2 : M * ι = πᵀ * Δ)
    {y : GL (Fin 2) K} (hy : y ∈ soGL Δ) : embGL h1 y ∈ soGL M := by
  rw [mem_soGL] at hy ⊢
  refine ⟨?_, ?_⟩
  · rw [coe_embGL]
    exact emb_isometry hMt hΔ h1 h2 hy.1
  · rw [coe_embGL, det_emb h1]
    exact hy.2

theorem conj_embGL (h1 : π * ι = 1) {T : GL (Fin 3) K} {D : GL (Fin 2) K}
    (hT : (T : Matrix (Fin 3) (Fin 3) K) * ι = ι * (D : Matrix (Fin 2) (Fin 2) K))
    (hT' : π * (T : Matrix (Fin 3) (Fin 3) K) = (D : Matrix (Fin 2) (Fin 2) K) * π)
    (hDD : D * D = 1) (hTT : T * T = 1) (y : GL (Fin 2) K) :
    T * embGL h1 y * T = embGL h1 (D * y * D) := by
  apply Units.ext
  have hDD' : (D : Matrix (Fin 2) (Fin 2) K) * D = 1 := by
    have := congrArg (fun x : GL (Fin 2) K => (x : Matrix (Fin 2) (Fin 2) K)) hDD
    simpa using this
  have hTT' : (T : Matrix (Fin 3) (Fin 3) K) * T = 1 := by
    have := congrArg (fun x : GL (Fin 3) K => (x : Matrix (Fin 3) (Fin 3) K)) hTT
    simpa using this
  rw [Units.val_mul, Units.val_mul, coe_embGL, coe_embGL, Units.val_mul, Units.val_mul]
  exact conj_emb hT hT' hDD' hTT' _

end EmbGL

@[expose] noncomputable def dmGL (K : Type*) [Field K] : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero (dmat2 K) (by simp [dmat2, Matrix.det_fin_two])

theorem coe_dmGL (K : Type*) [Field K] :
    ((dmGL K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = dmat2 K := rfl

theorem dmGL_mul_self (K : Type*) [Field K] : dmGL K * dmGL K = 1 := by
  apply Units.ext
  rw [Units.val_mul, coe_dmGL, dmat2_mul_self, Units.val_one]

variable {p : ℕ} [Fact p.Prime]

theorem dmGL_mul_mul_dmGL {a b : ZMod p} (ha : a ≠ 0) {y : GL (Fin 2) (ZMod p)}
    (hy : y ∈ soGL (Matrix.diagonal ![a, b])) :
    (dmGL (ZMod p) * y * dmGL (ZMod p)) * y = 1 := by
  obtain ⟨α, γ, h, hyrot⟩ := (mem_soGL_two_iff ha y).mp hy
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_dmGL, hyrot]
  have e : dmat2 (ZMod p) = dmat := rfl
  rw [e, dmat_mul_rot_mul_dmat, rot_mul, Units.val_one, ← rot_zero_zero a b]
  congr 1
  · linear_combination h
  · ring

theorem exists_class_unit (hp2 : p ≠ 2) :
    ∃ u : ZMod p, u ≠ 0 ∧ ∃ k : ℕ, Odd k ∧ (if IsSquare u then p - 1 else p + 1) = 2 * k := by
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp ((Fact.out : p.Prime).odd_of_ne_two hp2)
  by_cases h3 : p % 4 = 3
  · refine ⟨1, one_ne_zero, (p - 1) / 2, ?_, ?_⟩
    · rw [Nat.odd_iff]
      omega
    · have hsq : IsSquare (1 : ZMod p) := ⟨1, (mul_one 1).symm⟩
      simp only [hsq, ↓reduceIte]
      omega
  · have h1 : p % 4 = 1 := by omega
    obtain ⟨ν, hν⟩ := FiniteField.exists_nonsquare (ringChar_zmod_ne_two (p := p) hp2)
    refine ⟨ν, ?_, (p + 1) / 2, ?_, ?_⟩
    · intro h0
      apply hν
      rw [h0]
      exact ⟨0, by simp⟩
    · rw [Nat.odd_iff]
      omega
    · simp only [hν, ↓reduceIte]
      omega

theorem big_false (hp : 11 ≤ p) {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M)
    (hdet : M.det ≠ 0) (hirr : IsIrreducibleMatrixRep (omegaGL M).subtype)
    {D : Set (GL (Fin 3) (ZMod p))} (hDconj : ∀ x ∈ omegaGL M, ∀ g ∈ D, x * g * x⁻¹ ∈ D)
    (hodd : ∀ s ∈ D, ∀ t ∈ D, Odd (orderOf (s * t)) → orderOf (s * t) = 1 ∨ orderOf (s * t) = 3)
    {t : GL (Fin 3) (ZMod p)} (htD : t ∈ D) (ht : N1322.IsRefl t)
    (hnorm : ∀ x ∈ omegaGL M, t * x * t⁻¹ ∈ omegaGL M) : False := by
  have hp5 : 5 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  have hiso := refl_isometry hp5 hMt hdet hirr ht hnorm
  have htt : t * t = 1 := ht.sq
  obtain ⟨r, φ, hr, hφ, htm⟩ := ht
  obtain ⟨ha, htr, htv⟩ := refl_geom h2 hMt hdet hiso hr hφ htm
  obtain ⟨u, hu0, k, hk, hcard⟩ := exists_class_unit hp2
  obtain ⟨a, hadef⟩ : ∃ a : ZMod p, a = r ⬝ᵥ (M *ᵥ r) := ⟨_, rfl⟩
  rw [← hadef] at ha
  obtain ⟨b, hbdef⟩ : ∃ b : ZMod p, b = -u * a⁻¹ := ⟨_, rfl⟩
  have hb : b ≠ 0 := by
    rw [hbdef]
    exact mul_ne_zero (neg_ne_zero.mpr hu0) (inv_ne_zero ha)
  have hab : -(a * b) = u := by
    rw [hbdef]
    field_simp
  obtain ⟨f, hrf, hff⟩ := exists_orth_vec_of_value hp2 hMt hdet (r := r) (hadef ▸ ha) b
  have htf : (t : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ f = f := htv f hrf
  have hTM : (t : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M = M * (t : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    have htt' : (t : Matrix (Fin 3) (Fin 3) (ZMod p)) * t = 1 := by
      have := congrArg (fun x : GL (Fin 3) (ZMod p) => (x : Matrix (Fin 3) (Fin 3) (ZMod p))) htt
      simpa using this
    calc (t : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M
        = (t : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M * ((t : Matrix (Fin 3) (Fin 3) (ZMod p)) * t) := by
          rw [htt', Matrix.mul_one]
      _ = ((t : Matrix (Fin 3) (Fin 3) (ZMod p))ᵀ * M * (t : Matrix (Fin 3) (Fin 3) (ZMod p))) * t :=
          (Matrix.mul_assoc _ _ _).symm
      _ = M * t := by rw [hiso]
  have h1 : planeπ M r f a b * planeι r f = 1 :=
    planeπ_mul_planeι hMt ha hb hadef.symm hff hrf
  have h2' : M * planeι r f = (planeπ M r f a b)ᵀ * Matrix.diagonal ![a, b] := mul_planeι ha hb
  have hT : (t : Matrix (Fin 3) (Fin 3) (ZMod p)) * planeι r f =
      planeι r f * ((dmGL (ZMod p) : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) :=
    mul_planeι_T htr htf
  have hT' : planeπ M r f a b * (t : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      ((dmGL (ZMod p) : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *
        planeπ M r f a b :=
    planeπ_mul_T hTM htr htf
  have hΔ : (Matrix.diagonal ![a, b])ᵀ = Matrix.diagonal ![a, b] := Matrix.diagonal_transpose _
  have hcardC : Nat.card (soGL (Matrix.diagonal ![a, b])) = if IsSquare u then p - 1 else p + 1 := by
    rw [natCard_soGL_two ha hb hp2, hab]
  have h6 : ∀ y ∈ soGL (Matrix.diagonal ![a, b]), y ^ 6 = 1 := by
    intro y hy
    have hE : embGL h1 y ∈ soGL M := embGL_mem_soGL hMt hΔ h1 h2' hy
    have htE : t * embGL h1 y * t = (embGL h1 y)⁻¹ := by
      rw [conj_embGL h1 hT hT' (dmGL_mul_self _) htt y]
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, dmGL_mul_mul_dmGL ha hy, map_one]
    have hxΩ : embGL h1 y * embGL h1 y ∈ omegaGL M := sq_mem_omegaGL hp5 hMt hdet hE
    have htx : t * (embGL h1 y * embGL h1 y) * t = (embGL h1 y * embGL h1 y)⁻¹ := by
      calc t * (embGL h1 y * embGL h1 y) * t
          = (t * embGL h1 y * t) * (t * embGL h1 y * t) := by
            simp only [mul_assoc]
            rw [← mul_assoc t t, htt, one_mul]
        _ = (embGL h1 y * embGL h1 y)⁻¹ := by rw [htE, _root_.mul_inv_rev]
    have hyk : y ^ (2 * k) = 1 := by
      have := pow_card_eq_one' (G := soGL (Matrix.diagonal ![a, b])) (x := ⟨y, hy⟩)
      have h3 := congrArg (fun z : soGL (Matrix.diagonal ![a, b]) => (z : GL (Fin 2) (ZMod p))) this
      simpa [hcardC, hcard] using h3
    have hxk : (embGL h1 y * embGL h1 y) ^ k = 1 := by
      rw [← sq, ← pow_mul, ← map_pow, hyk, map_one]
    have hxodd : Odd (orderOf (embGL h1 y * embGL h1 y)) :=
      Odd.of_dvd_nat hk (orderOf_dvd_of_pow_eq_one hxk)
    have hx3 := pow_three_of_inverted (H := omegaGL M) hDconj hodd htD htt hxΩ htx hxodd
    apply embGL_injective h1
    rw [map_pow, map_one]
    calc embGL h1 y ^ 6 = (embGL h1 y * embGL h1 y) ^ 3 := by
          rw [← sq, ← pow_mul]
      _ = 1 := hx3
  have hle := natCard_soGL_two_le_six ha hb hp2 h6
  rw [hcardC] at hle
  split_ifs at hle <;> omega

end CFSG.RankThree.PartOne.KF1322
