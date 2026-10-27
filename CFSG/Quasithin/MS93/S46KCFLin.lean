module

public import CFSG.Quasithin.MS93.S46KC2Lin

public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CFSG.Quasithin.MS93.S46.KCF

open CFSG.Quasithin.MS93.S46.KC2

variable {F : Type} [Field F]

theorem exists_rows (l : Fin 3 → F) (hl : ¬ (l 1 = 0 ∧ l 2 = 0)) :
    ∃ A : SL3 F, (A : Matrix (Fin 3) (Fin 3) F) 0 = l ∧
      (A : Matrix (Fin 3) (Fin 3) F) 1 = Pi.single 0 1 := by
  by_cases h2 : l 2 = 0
  · have h1 : l 1 ≠ 0 := fun h => hl ⟨h, h2⟩
    refine ⟨⟨Matrix.of ![l, Pi.single 0 1, ![0, 0, -(l 1)⁻¹]], ?_⟩, rfl, rfl⟩
    rw [Matrix.det_fin_three]
    simp [h2, h1]
  · refine ⟨⟨Matrix.of ![l, Pi.single 0 1, ![0, (l 2)⁻¹, 0]], ?_⟩, rfl, rfl⟩
    rw [Matrix.det_fin_three]
    simp [h2]

theorem exists_stab_mulVec (u : Fin 3 → F) (h0 : u 0 = 0) (hu : u ≠ 0) :
    ∃ A : SL3 F, (A : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 = u := by
  by_cases h1 : u 1 = 0
  · have h2 : u 2 ≠ 0 := by
      intro h2
      apply hu
      funext k
      fin_cases k
      · exact h0
      · exact h1
      · exact h2
    refine ⟨⟨Matrix.of ![Pi.single 0 1, ![0, 0, -(u 2)⁻¹], ![0, u 2, 0]], ?_⟩, rfl, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h2]
    · rw [Matrix.mulVec_single_one]
      funext k
      fin_cases k
      · simp [h0]
      · simp [h1]
      · simp
  · refine ⟨⟨Matrix.of ![Pi.single 0 1, ![0, u 1, 0], ![0, u 2, (u 1)⁻¹]], ?_⟩, rfl, ?_⟩
    · rw [Matrix.det_fin_three]
      simp [h1]
    · rw [Matrix.mulVec_single_one]
      funext k
      fin_cases k
      · simp [h0]
      · simp
      · simp

theorem rootElt_row_zero {i j : Fin 3} (hi : i ≠ 0) (c : F) :
    ((rootElt i j c : SL3 F) : Matrix (Fin 3) (Fin 3) F) 0 = Pi.single 0 1 := by
  funext k
  by_cases hij : i = j
  · rw [hij, rootElt_self, row_one]
  · rw [coe_rootElt hij]
    simp [Matrix.one_apply, Pi.single_apply, hi, eq_comm]

private theorem matN_mulVec_aux : ∀ l m : Fin 3 → ZMod 2, l ≠ 0 → m ≠ 0 → l ≠ m →
    (fun i => matN l m i 0 * cr l m 0 + matN l m i 1 * cr l m 1 + matN l m i 2 * cr l m 2) =
      Pi.single 2 1 := by
  decide

theorem matN_mulVec_cr {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    matN l m *ᵥ cr l m = Pi.single 2 1 := by
  rw [← matN_mulVec_aux l m hl hm hlm]
  funext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]

section Two

variable [CharP F 2]

theorem matF_mulVec_embv {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m)
    (v : Fin 3 → ZMod 2) :
    (matF (F := F) hl hm hlm : Matrix (Fin 3) (Fin 3) F) *ᵥ embv v = embv (matN l m *ᵥ v) := by
  funext i
  show _ = iota F ((matN l m *ᵥ v) i)
  rw [RingHom.map_mulVec]
  rfl

theorem matF_inv_mulVec {l m : Fin 3 → ZMod 2} (hl : l ≠ 0) (hm : m ≠ 0) (hlm : l ≠ m) :
    (((matF (F := F) hl hm hlm)⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1 =
      embv (cr l m) := by
  have h := matF_mulVec_embv (F := F) hl hm hlm (cr l m)
  rw [matN_mulVec_cr hl hm hlm, embv_single] at h
  rw [← h, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] noncomputable def bsumF (s : Fin 6 → F) (L : List (Fin 6)) (j : Fin 6) : Fin 3 → F :=
  (L.map fun i => s i • embv (tab i j)).sum

@[expose] noncomputable def qsumF (s : Fin 6 → F) : List (Fin 6) → Fin 3 → F
  | [] => 0
  | i :: L => s i • bsumF s L i + qsumF s L

theorem bsumF_nil (s : Fin 6 → F) (j : Fin 6) : bsumF s [] j = 0 := rfl

theorem bsumF_cons (s : Fin 6 → F) (i : Fin 6) (L : List (Fin 6)) (j : Fin 6) :
    bsumF s (i :: L) j = s i • embv (tab i j) + bsumF s L j := by
  simp [bsumF]

theorem qsumF_nil (s : Fin 6 → F) : qsumF s [] = 0 := rfl

theorem qsumF_cons (s : Fin 6 → F) (i : Fin 6) (L : List (Fin 6)) :
    qsumF s (i :: L) = s i • bsumF s L i + qsumF s L := rfl

theorem bsumF_ind (c : Fin 6 → Bool) (L : List (Fin 6)) (j : Fin 6) :
    bsumF (fun i => if c i then (1 : F) else 0) L j = embv (bsum c L j) := by
  induction L with
  | nil => rw [bsumF_nil, bsum_nil, embv_zero]
  | cons i L ih =>
    rw [bsumF_cons, bsum_cons, embv_add, ih]
    by_cases hc : c i
    · simp [hc]
    · simp [hc, embv_zero]

theorem qsumF_ind (c : Fin 6 → Bool) (L : List (Fin 6)) :
    qsumF (fun i => if c i then (1 : F) else 0) L = embv (qsum c L) := by
  induction L with
  | nil => rw [qsumF_nil, qsum_nil, embv_zero]
  | cons i L ih =>
    rw [qsumF_cons, qsum_cons, embv_add, ih, bsumF_ind]
    by_cases hc : c i
    · simp [hc]
    · simp [hc, embv_zero]

end Two

end CFSG.Quasithin.MS93.S46.KCF
