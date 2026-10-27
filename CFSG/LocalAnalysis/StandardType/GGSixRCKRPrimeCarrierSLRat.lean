module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Subfield.Basic

public section

namespace CFSG.StandardType.RCKRP

open Matrix
open scoped MatrixGroups

theorem exists_rational_scalar_mul_fin {k Ω : Type} [Field k] [Field Ω] [IsAlgClosed Ω]
    [Algebra k Ω] {n q : ℕ} (hq : 2 ≤ q) (Fr : Ω →+* Ω) (hFr : ∀ z, Fr z = z ^ q)
    (hk : ∀ c : k, Fr (algebraMap k Ω c) = algebraMap k Ω c)
    (hfix : ∀ z : Ω, Fr z = z → ∃ c : k, algebraMap k Ω c = z)
    (N : GL (Fin n) Ω)
    (hN : ∀ i j : Fin n, i ≠ j → ∀ a b : Fin n, ∃ c : k, algebraMap k Ω c =
      ((N : Matrix (Fin n) (Fin n) Ω) * (1 + Matrix.single i j (1 : Ω)) *
        ((N⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω)) a b) :
    ∃ (M : GL (Fin n) k) (c : Ω), c ≠ 0 ∧
      (N : Matrix (Fin n) (Fin n) Ω) =
        c • ((M : Matrix (Fin n) (Fin n) k).map (algebraMap k Ω)) := by
  classical
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · exact ⟨1, 1, one_ne_zero, Matrix.ext fun i j => i.elim0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set A : Matrix (Fin n) (Fin n) Ω := (N : Matrix (Fin n) (Fin n) Ω) with hA
  set A' : Matrix (Fin n) (Fin n) Ω := ((N⁻¹ : GL (Fin n) Ω) : Matrix (Fin n) (Fin n) Ω) with hA'
  have hAA' : A * A' = 1 := by rw [hA, hA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hA'A : A' * A = 1 := by rw [hA, hA', ← Units.val_mul, inv_mul_cancel, Units.val_one]
  set φ : Matrix (Fin n) (Fin n) Ω →+* Matrix (Fin n) (Fin n) Ω := Fr.mapMatrix with hφ
  have hφapp : ∀ B : Matrix (Fin n) (Fin n) Ω, φ B = B.map Fr := fun B => rfl
  set P : Matrix (Fin n) (Fin n) Ω := A' * φ A with hP
  have e2 : φ A' * φ A = 1 := by rw [← map_mul, hA'A, map_one]
  have hcomm : ∀ i j : Fin n, i ≠ j → Commute (Matrix.single i j (1 : Ω)) P := by
    intro i j hij
    set T : Matrix (Fin n) (Fin n) Ω := 1 + Matrix.single i j 1 with hT
    have hφT : φ T = T := by
      rw [hT, map_add, map_one, hφapp]
      congr 1
      ext a b
      simp only [Matrix.map_apply, Matrix.single_apply]
      split_ifs <;> simp
    have hB : φ (A * T * A') = A * T * A' := by
      ext a b
      obtain ⟨c, hc⟩ := hN i j hij a b
      show Fr ((A * T * A') a b) = (A * T * A') a b
      rw [← hc]
      exact hk c
    have h1 : φ A * T * φ A' = A * T * A' := by
      calc φ A * T * φ A' = φ A * φ T * φ A' := by rw [hφT]
        _ = φ (A * T * A') := by rw [map_mul, map_mul]
        _ = A * T * A' := hB
    have e1 : T * A' = A' * (φ A * T * φ A') := by
      rw [h1]
      calc T * A' = (A' * A) * T * A' := by rw [hA'A, Matrix.one_mul]
        _ = A' * (A * T * A') := by simp only [Matrix.mul_assoc]
    have h2 : T * P = P * T := by
      calc T * P = T * A' * φ A := by rw [hP, Matrix.mul_assoc]
        _ = A' * (φ A * T * φ A') * φ A := by rw [e1]
        _ = A' * φ A * T * (φ A' * φ A) := by simp only [Matrix.mul_assoc]
        _ = P * T := by rw [e2, Matrix.mul_one]
    have h3 : (1 + Matrix.single i j (1 : Ω)) * P = P * (1 + Matrix.single i j (1 : Ω)) := h2
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one] at h3
    exact add_left_cancel h3
  obtain ⟨lam, hlam⟩ := Matrix.mem_range_scalar_of_commute_single (fun i j hij => hcomm i j hij)
  have hφA : φ A = lam • A := by
    have h1 : A * P = φ A := by
      rw [hP, ← Matrix.mul_assoc, hAA', Matrix.one_mul]
    rw [← h1, ← hlam, Matrix.scalar_apply]
    ext a b
    simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]
  have hlam0 : lam ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hφA
    have : (1 : Matrix (Fin n) (Fin n) Ω) = 0 := by
      rw [← map_one φ, ← hAA', map_mul, hφA, zero_mul]
    exact one_ne_zero this
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k := Ω) lam⁻¹ (n := q - 1) (by omega)
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at hc
    exact inv_ne_zero hlam0 hc.symm
  have hcq : c ^ q * lam = c := by
    have : q = (q - 1) + 1 := by omega
    calc c ^ q * lam = c * (c ^ (q - 1) * lam) := by
          conv_lhs => rw [this, pow_succ]
          ring
      _ = c := by rw [hc, inv_mul_cancel₀ hlam0, mul_one]
  have hM₀ : ∀ a b : Fin n, Fr ((c • A) a b) = (c • A) a b := by
    intro a b
    have h1 := congrFun (congrFun hφA a) b
    rw [hφapp, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at h1
    rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1, hFr c]
    calc c ^ q * (lam * A a b) = (c ^ q * lam) * A a b := by ring
      _ = c * A a b := by rw [hcq]
  choose m hm using fun a b => hfix _ (hM₀ a b)
  set M₁ : Matrix (Fin n) (Fin n) k := Matrix.of fun a b => m a b with hM₁
  have hM₁map : M₁.map (algebraMap k Ω) = c • A := by
    ext a b
    exact hm a b
  have hdetA : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 ⟨N, rfl⟩
  have hdet : M₁.det ≠ 0 := by
    intro h0
    have h1 : (M₁.map (algebraMap k Ω)).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    rw [hM₁map, Matrix.det_smul, Fintype.card_fin] at h1
    exact mul_ne_zero (pow_ne_zero n hc0) hdetA.ne_zero h1
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M₁ hdet, c⁻¹, inv_ne_zero hc0, ?_⟩
  rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hM₁map, smul_smul, inv_mul_cancel₀ hc0,
    one_smul]

theorem exists_smul_map_of_conj_char_two {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {Q : ℕ} (hQ2 : 2 ≤ Q) (σQ : L →+* L) (hσ : ∀ c, σQ c = c ^ Q) (K : Subfield L)
    (hK : ∀ c : L, c ∈ K ↔ σQ c = c) {ν : ℕ} (C : GL (Fin ν) L)
    (hC : ∀ X : SL(ν, ↥K), ∃ (X' : SL(ν, ↥K)) (ζ : L),
      (C : Matrix (Fin ν) (Fin ν) L) *
          (Matrix.SpecialLinearGroup.map K.subtype X : Matrix (Fin ν) (Fin ν) L) *
          ((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) =
        ζ • (Matrix.SpecialLinearGroup.map K.subtype X' : Matrix (Fin ν) (Fin ν) L)) :
    ∃ (M : GL (Fin ν) ↥K) (c : L), c ≠ 0 ∧
      (C : Matrix (Fin ν) (Fin ν) L) = c • (M : Matrix (Fin ν) (Fin ν) ↥K).map K.subtype := by
  classical
  refine exists_rational_scalar_mul_fin (k := ↥K) (Ω := L) (q := Q) hQ2 σQ hσ ?_ ?_ C ?_
  · intro c
    rw [Subfield.algebraMap_ofSubfield]
    exact (hK _).mp c.2
  · intro z hz
    exact ⟨⟨z, (hK z).mpr hz⟩, rfl⟩
  · intro i j hij a b
    obtain ⟨X', ζ, hζeq⟩ := hC (Matrix.SpecialLinearGroup.transvection hij (1 : ↥K))
    set Xm : Matrix (Fin ν) (Fin ν) L :=
      (Matrix.SpecialLinearGroup.map K.subtype X' : Matrix (Fin ν) (Fin ν) L) with hXm
    set D : Matrix (Fin ν) (Fin ν) L := 1 + Matrix.single i j (1 : L) with hD
    set Ci : Matrix (Fin ν) (Fin ν) L :=
      ((C⁻¹ : GL (Fin ν) L) : Matrix (Fin ν) (Fin ν) L) with hCi
    have hX0 : (Matrix.SpecialLinearGroup.map K.subtype
        (Matrix.SpecialLinearGroup.transvection hij (1 : ↥K)) :
          Matrix (Fin ν) (Fin ν) L) = D := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe, hD]
      ext p q
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
        Matrix.single_apply]
      split_ifs <;> simp
    have hζeq' : (C : Matrix (Fin ν) (Fin ν) L) * D * Ci = ζ • Xm := by
      rw [← hX0]
      exact hζeq
    have hCCinv : (C : Matrix (Fin ν) (Fin ν) L) * Ci = 1 := by
      rw [hCi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hCinvC : Ci * (C : Matrix (Fin ν) (Fin ν) L) = 1 := by
      rw [hCi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hsq : D * D = 1 := by
      have h := Matrix.transvection_mul_transvection_same (i := i) (j := j) hij (1 : L) (1 : L)
      rw [CharTwo.add_self_eq_zero, Matrix.transvection_zero] at h
      rw [hD]
      simpa only [Matrix.transvection] using h
    have hPP : ((C : Matrix (Fin ν) (Fin ν) L) * D * Ci) *
        ((C : Matrix (Fin ν) (Fin ν) L) * D * Ci) = 1 := by
      calc ((C : Matrix (Fin ν) (Fin ν) L) * D * Ci) *
            ((C : Matrix (Fin ν) (Fin ν) L) * D * Ci)
          = (C : Matrix (Fin ν) (Fin ν) L) * D * (Ci * (C : Matrix (Fin ν) (Fin ν) L)) *
              D * Ci := by simp only [Matrix.mul_assoc]
        _ = (C : Matrix (Fin ν) (Fin ν) L) * D * 1 * D * Ci := by rw [hCinvC]
        _ = (C : Matrix (Fin ν) (Fin ν) L) * (D * D) * Ci := by
              simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = (C : Matrix (Fin ν) (Fin ν) L) * 1 * Ci := by rw [hsq]
        _ = 1 := by rw [Matrix.mul_one, hCCinv]
    have hZZ : (ζ • Xm) * (ζ • Xm) = 1 := by
      rw [← hζeq']
      exact hPP
    have hZZ2 : ζ ^ 2 • (Xm * Xm) = 1 := by
      simpa only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq] using hZZ
    have hentry : ζ ^ 2 * (Xm * Xm) i i = 1 := by
      have h := congrFun (congrFun hZZ2 i) i
      simpa [Matrix.smul_apply, smul_eq_mul] using h
    have hmem : ∀ p q : Fin ν, Xm p q ∈ K := by
      intro p q
      rw [hXm]
      exact ((X' : Matrix (Fin ν) (Fin ν) ↥K) p q).2
    have hentryK : (Xm * Xm) i i ∈ K := by
      rw [Matrix.mul_apply]
      exact K.sum_mem fun k _ => K.mul_mem (hmem i k) (hmem k i)
    have hζ2K : ζ ^ 2 ∈ K := by
      rw [eq_inv_of_mul_eq_one_left hentry]
      exact K.inv_mem hentryK
    have hσζ : σQ ζ = ζ := by
      refine CharTwo.sq_inj.mp ?_
      rw [← map_pow]
      exact (hK (ζ ^ 2)).mp hζ2K
    have hζK : ζ ∈ K := (hK ζ).mpr hσζ
    have hkey : ((C : Matrix (Fin ν) (Fin ν) L) * D * Ci) a b =
        ζ * (((X' : Matrix (Fin ν) (Fin ν) ↥K) a b : ↥K) : L) := by
      rw [← hX0, hζeq]
      simp only [Matrix.smul_apply, smul_eq_mul]
      congr 1
    refine ⟨⟨ζ, hζK⟩ * (X' : Matrix (Fin ν) (Fin ν) ↥K) a b, ?_⟩
    rw [Subfield.algebraMap_ofSubfield, Subfield.subtype_apply, Subfield.coe_mul]
    exact hkey.symm

end CFSG.StandardType.RCKRP

end
