module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

open CFSG CFSG.RankThree.PartTwo.Sec4

@[expose] def glTwoCentWeyl (K : Type) [Field K] : GL (Fin 2) K :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem glTwoCentWeyl_val (K : Type) [Field K] :
    (glTwoCentWeyl K : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] :=
  rfl

@[expose] def glTwoCentDiag {K : Type} [Field K] {t : K} (ht : t ≠ 0) : GL (Fin 2) K :=
  ⟨!![t, 0; 0, t⁻¹], !![t⁻¹, 0; 0, t],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht],
    by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht]⟩

theorem glTwoCentDiag_val {K : Type} [Field K] {t : K} {ht : t ≠ 0} :
    (glTwoCentDiag ht : Matrix (Fin 2) (Fin 2) K) = !![t, 0; 0, t⁻¹] :=
  rfl

theorem glTwoCentWeyl_mem {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K) :
    glTwoCentWeyl K ∈ slPi π 2 (p ^ f) K := by
  cases π with
  | false =>
    rw [mem_slPi_false hK.unitary, glTwoCentWeyl_val]
    refine ⟨by simp [Matrix.det_fin_two], ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.map_apply]
  | true =>
    rw [mem_slPi_true, glTwoCentWeyl_val]
    simp [Matrix.det_fin_two]

theorem diag_unitary_fin_two {K : Type} [Field K] (b : K →+* K) {x y : K}
    (hx : b x * x = 1) (hy : b y * y = 1) :
    Matrix.transpose ((!![x, 0; 0, y] : Matrix (Fin 2) (Fin 2) K).map b) * !![x, 0; 0, y] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hx, hy]

theorem glTwoCentDiag_mem {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    {t : K} (ht : t ≠ 0) (htq : π = false → t ^ (p ^ f) * t = 1) :
    glTwoCentDiag ht ∈ slPi π 2 (p ^ f) K := by
  cases π with
  | false =>
    have hU := hK.unitary
    have hq : t ^ (p ^ f) * t = 1 := htq rfl
    have e1 : hU.bar t * t = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply]
      exact hq
    have e2 : hU.bar t⁻¹ * t⁻¹ = 1 := by
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData.bar_apply, inv_pow, ← mul_inv, hq,
        inv_one]
    rw [mem_slPi_false hU, glTwoCentDiag_val]
    exact ⟨by simp [Matrix.det_fin_two, ht], diag_unitary_fin_two hU.bar e1 e2⟩
  | true =>
    rw [mem_slPi_true, glTwoCentDiag_val]
    simp [Matrix.det_fin_two, ht]

theorem glTwoCent_eq_smul_one {K : Type} [Field K] {t : K} {G : Matrix (Fin 2) (Fin 2) K}
    (ht0 : t ≠ 0) (ht2 : t ^ 2 ≠ 1)
    (hw : (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) K) * G = G * !![0, 1; -1, 0])
    (hd : (!![t, 0; 0, t⁻¹] : Matrix (Fin 2) (Fin 2) K) * G = G * !![t, 0; 0, t⁻¹]) :
    G = G 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  have hw00 : G 1 0 = -G 0 1 := by
    have := congrFun (congrFun hw 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hw11 : G 1 1 = G 0 0 := by
    have := congrFun (congrFun hw 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hd01 : t * G 0 1 = G 0 1 * t⁻¹ := by
    have := congrFun (congrFun hd 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : G 0 1 = 0 := by
    have key : (1 - t ^ 2) * G 0 1 = 0 := by
      linear_combination (-t) * hd01 - G 0 1 * mul_inv_cancel₀ ht0
    rcases mul_eq_zero.1 key with h | h
    · exact absurd (sub_eq_zero.1 h).symm ht2
    · exact h
  have h10 : G 1 0 = 0 := by rw [hw00, h01, neg_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h10, hw11]

theorem glTwoCentExists_diag {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq3 : 3 < p ^ f) :
    ∃ t : K, t ≠ 0 ∧ t ^ 2 ≠ 1 ∧ (π = false → t ^ (p ^ f) * t = 1) := by
  have hfin : Finite K := hK.finite
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  rw [Nat.card_units] at hg
  obtain ⟨r, hr⟩ : ∃ r, p ^ f = r + 1 := ⟨p ^ f - 1, by omega⟩
  have hr3 : 3 ≤ r := by omega
  cases π with
  | false =>
    have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
    have hN : orderOf g = r * (r + 2) := by
      rw [hg, hcard, hr]
      exact Nat.sub_eq_of_eq_add (by ring)
    refine ⟨((g ^ r : Kˣ) : K), Units.ne_zero _, ?_, fun _ => ?_⟩
    · intro h2
      have hu : g ^ (r * 2) = 1 := by
        rw [pow_mul]
        exact Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
      have hd : orderOf g ∣ r * 2 := orderOf_dvd_of_pow_eq_one hu
      rw [hN] at hd
      have hle := Nat.le_of_dvd (by omega) hd
      nlinarith
    · rw [hr]
      have hu2 : (g ^ r) ^ (r + 1) * g ^ r = 1 := by
        rw [← pow_mul, ← pow_add, show r * (r + 1) + r = orderOf g by rw [hN]; ring]
        exact pow_orderOf_eq_one g
      simpa [Units.val_mul, Units.val_pow_eq_pow_val] using congrArg Units.val hu2
  | true =>
    have hcard : Nat.card K = p ^ f := hK.card
    have hN : orderOf g = r := by
      rw [hg, hcard, hr, Nat.add_sub_cancel]
    refine ⟨(g : K), Units.ne_zero g, ?_, fun h => absurd h (by decide)⟩
    intro h2
    have hu : g ^ 2 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h2, Units.val_one])
    have hd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hu
    rw [hN] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    omega

theorem centralizer_slPi_two {π : Bool} {p f : ℕ} {K : Type} [Field K] (hK : PiField π p f K)
    (hq3 : 3 < p ^ f) :
    Subgroup.centralizer (slPi π 2 (p ^ f) K : Set (GL (Fin 2) K)) =
      CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) K := by
  refine le_antisymm (fun g hg => ?_) (statedScalars_le_centralizer _)
  rw [Subgroup.mem_centralizer_iff] at hg
  obtain ⟨t, ht0, ht2, htq⟩ := glTwoCentExists_diag hK hq3
  have hw := congrArg (fun y : GL (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K))
    (hg (glTwoCentWeyl K) (glTwoCentWeyl_mem hK))
  have hd := congrArg (fun y : GL (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K))
    (hg (glTwoCentDiag ht0) (glTwoCentDiag_mem hK ht0 htq))
  simp only [Units.val_mul, glTwoCentWeyl_val, glTwoCentDiag_val] at hw hd
  have hM := glTwoCent_eq_smul_one ht0 ht2 hw hd
  refine mem_statedScalars_of_eq_smul hM fun h0 => ?_
  have hdet := congrArg Matrix.det hM
  rw [h0, zero_smul, Matrix.det_zero] at hdet
  exact (g.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 2) (Fin 2) K →* K)).ne_zero hdet

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree

end
