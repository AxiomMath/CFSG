module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3Mod
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80U3P3Alg

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Assembly.LowTwoRank CFSG.Quasithin.A312U3 CFSG.GH74.GLS.IVK.Proofs2
  CFSG.LocalAnalysis.ComponentInitial

variable {F : Type} [Field F]

theorem three_eq_zero_u3 (hF : Nat.card F = 3 ^ 2) : (3 : F) = 0 := by
  have := (uniData (p := 3) hF).charP
  simpa using CharP.cast_eq_zero F 3

theorem exists_sq_eq_neg_one_u3 (hF : Nat.card F = 3 ^ 2) : ∃ i : F, i ^ 2 = -1 := by
  obtain ⟨u, hu⟩ := CFSG.LinearGroups.UnitaryThreeOverNine.exists_units_orderOf_eq_four
    (F := F) (by rw [hF]; norm_num)
  have h4 : (u : F) ^ 4 = 1 := by
    have := pow_orderOf_eq_one u
    rw [hu] at this
    simpa using congrArg Units.val this
  have h2 : (u : F) ^ 2 ≠ 1 := fun h => by
    have h' : u ^ 2 = 1 := Units.ext (by simpa using h)
    have := orderOf_dvd_of_pow_eq_one h'
    rw [hu] at this
    omega
  have hm : ((u : F) ^ 2 - 1) * ((u : F) ^ 2 + 1) = 0 := by linear_combination h4
  refine ⟨u, ?_⟩
  rcases mul_eq_zero.mp hm with h | h
  · exact absurd (by linear_combination h) h2
  · linear_combination h

variable (hF : Nat.card F = 3 ^ 2)

theorem bar_i {i : F} (hi : i ^ 2 = -1) : (uniData (p := 3) hF).bar i = -i := by
  rw [UnitaryFieldData.bar_apply]
  simp only [pow_one]
  linear_combination i * hi

theorem det_ne_zero_of_unitary2 {M : Matrix (Fin 2) (Fin 2) F}
    (hu : (M.map (uniData (p := 3) hF).bar)ᵀ * M = 1) : M.det ≠ 0 := fun h0 => by
  have := Lemma41aU3.bar_det_mul_det hu
  rw [h0, map_zero, zero_mul] at this
  exact zero_ne_one this

@[expose] noncomputable def mkGU2 (M : Matrix (Fin 2) (Fin 2) F)
    (hu : (M.map (uniData (p := 3) hF).bar)ᵀ * M = 1) : ↥(GU2Stated (3 ^ 1) F) :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (det_ne_zero_of_unitary2 hF hu),
    (Lemma41aU3.mem_GU2Stated_iff (uniData (p := 3) hF)).mpr hu⟩

variable {hF}

theorem unitary_gAlg1 : ((gAlg1 : Matrix (Fin 2) (Fin 2) F).map (uniData (p := 3) hF).bar)ᵀ *
    gAlg1 = 1 := by
  have : ((gAlg1 : Matrix (Fin 2) (Fin 2) F).map (uniData (p := 3) hF).bar)ᵀ = gAlg1 := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gAlg1]
  rw [this]
  exact gAlg1_mul

theorem unitary_gAlg2 {i : F} (hi : i ^ 2 = -1) :
    ((gAlg2 i).map (uniData (p := 3) hF).bar)ᵀ * gAlg2 i = 1 := by
  have : ((gAlg2 i).map (uniData (p := 3) hF).bar)ᵀ = gAlg2' i := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gAlg2, gAlg2', bar_i hF hi]
  rw [this]
  exact gAlg2'_mul hi

theorem unitary_gAlg3 {i : F} (hi : i ^ 2 = -1) :
    ((gAlg3 i).map (uniData (p := 3) hF).bar)ᵀ * gAlg3 i = 1 := by
  have : ((gAlg3 i).map (uniData (p := 3) hF).bar)ᵀ = gAlg3' i := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gAlg3, gAlg3', bar_i hF hi] <;> ring1
  rw [this]
  exact gAlg3'_mul (three_eq_zero_u3 hF) hi

theorem unitary_swap :
    ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F).map (uniData (p := 3) hF).bar)ᵀ *
      !![0, 1; 1, 0] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem unitary_diagO {i : F} (hi : i ^ 2 = -1) :
    ((!![-i, 0; 0, i] : Matrix (Fin 2) (Fin 2) F).map (uniData (p := 3) hF).bar)ᵀ *
      !![-i, 0; 0, i] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, bar_i hF hi]
  · linear_combination -hi
  · linear_combination -hi

variable (hF)

@[expose] noncomputable def gE1 : ↥(GU2Stated (3 ^ 1) F) :=
  mkGU2 hF gAlg1 (unitary_gAlg1 (hF := hF))

@[expose] noncomputable def gE2 {i : F} (hi : i ^ 2 = -1) : ↥(GU2Stated (3 ^ 1) F) :=
  mkGU2 hF (gAlg2 i) (unitary_gAlg2 (hF := hF) hi)

@[expose] noncomputable def gE3 {i : F} (hi : i ^ 2 = -1) : ↥(GU2Stated (3 ^ 1) F) :=
  mkGU2 hF (gAlg3 i) (unitary_gAlg3 (hF := hF) hi)

@[expose] noncomputable def gEs : ↥(GU2Stated (3 ^ 1) F) :=
  mkGU2 hF !![0, 1; 1, 0] (unitary_swap (hF := hF))

@[expose] noncomputable def gEO {i : F} (hi : i ^ 2 = -1) : ↥(GU2Stated (3 ^ 1) F) :=
  mkGU2 hF !![-i, 0; 0, i] (unitary_diagO (hF := hF) hi)

variable {hF}

theorem coe_inv_gu2 {g : ↥(GU2Stated (3 ^ 1) F)} {ginv : Matrix (Fin 2) (Fin 2) F}
    (h : ginv * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1) :
    (((g⁻¹ : ↥(GU2Stated (3 ^ 1) F)) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = ginv := by
  rw [Subgroup.coe_inv, Matrix.coe_units_inv]
  exact Matrix.inv_eq_left_inv h

theorem gu2_conj_commute {Y N : Subgroup (SU3F 3 F)} (hB : leviU hF ≤ Y)
    (hnorm : ∀ y ∈ Y, ∀ a ∈ N, y * a * y⁻¹ ∈ N) (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a)
    {A g : ↥(GU2Stated (3 ^ 1) F)} (hA : Lemma41aU3.blkU (uniData hF) A ∈ N)
    {ginv : Matrix (Fin 2) (Fin 2) F}
    (hginv : ginv * ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1) :
    ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ginv) =
      (((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ginv) *
        ((A : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  have hgY : Lemma41aU3.blkU (uniData hF) g ∈ Y := hB ⟨g, rfl⟩
  have h1 := hnorm _ hgY _ hA
  have h2 := hcomm _ hA _ h1
  have h3 : A * (g * A * g⁻¹) = (g * A * g⁻¹) * A := by
    apply Lemma41aU3.blkU_injective (uniData hF)
    simpa only [map_mul, map_inv] using h2
  have h4 := congrArg
    (fun x : ↥(GU2Stated (3 ^ 1) F) => ((x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h3
  simpa only [Subgroup.coe_mul, Units.val_mul, coe_inv_gu2 hginv] using h4

end CFSG.Quasithin.E2P.Asc80
