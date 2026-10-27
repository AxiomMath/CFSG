module

public import CFSG.RankThree.Classical.UnitaryRankWitness
public import CFSG.RankThree.PartOne.SRC.RankOneAux

public section

namespace CFSG.RankThree.PartOne.SLB4B

open CFSG CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Classical

namespace RadicalU

section Levi

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {r m : ℕ}

def leviMat (D : Matrix (Fin r) (Fin r) K) :
    Matrix ((Fin r ⊕ Fin r) ⊕ Fin m) ((Fin r ⊕ Fin r) ⊕ Fin m) K :=
  Matrix.fromBlocks (Matrix.fromBlocks D 0 0 D) 0 0 1

theorem leviMat_isometry {D : Matrix (Fin r) (Fin r) K} (hD : hadj h D = D) (hDD : D * D = 1) :
    hadj h (leviMat (m := m) D) * frameGram r m K * leviMat D = frameGram r m K := by
  simp only [leviMat, frameGram, hypGram2, hadj_fromBlocks, hD, hadj_zero, hadj_one,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one,
    add_zero, zero_add, hDD]

theorem det_leviMat {D : Matrix (Fin r) (Fin r) K} (hDD : D * D = 1) :
    (leviMat (m := m) D).det = 1 := by
  rw [leviMat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one,
    mul_one, ← Matrix.det_mul, hDD, Matrix.det_one]

theorem leviMat_mul_frameMat {D : Matrix (Fin r) (Fin r) K} (hDD : D * D = 1)
    (B : Matrix (Fin r) (Fin r) K) :
    leviMat (m := m) D * frameMat m B = frameMat m (D * B * D) * leviMat D := by
  simp only [leviMat, frameMat, siegelMat, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, add_zero, zero_add, Matrix.mul_assoc, hDD]

theorem skewHerm_conj {D : Matrix (Fin r) (Fin r) K} (hD : hadj h D = D)
    {B : Matrix (Fin r) (Fin r) K} (hB : B ∈ skewHermMatrices h r) :
    D * B * D ∈ skewHermMatrices h r := by
  have hB' : B + hadj h B = 0 := hB
  change D * B * D + hadj h (D * B * D) = 0
  have : D * B * D + hadj h (D * B * D) = D * (B + hadj h B) * D := by
    rw [hadj_mul, hadj_mul, hD]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  rw [this, hB', Matrix.mul_zero, Matrix.zero_mul]

def leviAct {D : Matrix (Fin r) (Fin r) K} (hD : hadj h D = D) (B : skewHermMatrices h r) :
    skewHermMatrices h r :=
  ⟨D * B * D, skewHerm_conj h hD B.2⟩

variable {n : ℕ} {P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram r m K) (hnm : 2 * r + m = n)

theorem exists_leviSU_conj {D : Matrix (Fin r) (Fin r) K} (hD : hadj h D = D)
    (hDD : D * D = 1) :
    ∃ g : unitarySU p f K n, ∀ B : skewHermMatrices h r,
      g * frameSUHom h hP hnm (Multiplicative.ofAdd B) * g⁻¹ =
        frameSUHom h hP hnm (Multiplicative.ofAdd (leviAct h hD B)) := by
  refine ⟨frameSU h hP hnm (leviMat D) (leviMat_isometry h hD hDD) (det_leviMat hDD),
    fun B => ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_frameSUHom,
    coe_frameSUHom, coe_frameSU, frameConj_mul h hP, frameConj_mul h hP,
    toAdd_ofAdd, toAdd_ofAdd, leviMat_mul_frameMat hDD]
  rfl

end Levi

section Matrices

variable {K : Type} [Field K]

def levD1 : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, -1]

def levD2 : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

def radBasis (η : K) : Fin 4 → Matrix (Fin 2) (Fin 2) K :=
  ![!![η, 0; 0, η], !![η, 0; 0, -η], !![0, η; η, 0], !![0, 1; -1, 0]]

theorem levD1_mul_self : (levD1 : Matrix (Fin 2) (Fin 2) K) * levD1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD1, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD2_mul_self : (levD2 : Matrix (Fin 2) (Fin 2) K) * levD2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD2, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD1_conj_zero (η : K) : levD1 * radBasis η 0 * levD1 = radBasis η 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD1, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD1_conj_one (η : K) : levD1 * radBasis η 1 * levD1 = radBasis η 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD1, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD1_conj_two (η : K) : levD1 * radBasis η 2 * levD1 = -radBasis η 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD1, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD1_conj_three (η : K) : levD1 * radBasis η 3 * levD1 = -radBasis η 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD1, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD2_conj_zero (η : K) : levD2 * radBasis η 0 * levD2 = radBasis η 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD2, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD2_conj_one (η : K) : levD2 * radBasis η 1 * levD2 = -radBasis η 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD2, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD2_conj_two (η : K) : levD2 * radBasis η 2 * levD2 = radBasis η 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD2, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem levD2_conj_three (η : K) : levD2 * radBasis η 3 * levD2 = -radBasis η 3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [levD2, radBasis, Matrix.mul_apply, Fin.sum_univ_two]

theorem hadj_levD1 {p f : ℕ} (h : UnitaryFieldData p f K) :
    hadj h (levD1 : Matrix (Fin 2) (Fin 2) K) = levD1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadj, levD1]

theorem hadj_levD2 {p f : ℕ} (h : UnitaryFieldData p f K) :
    hadj h (levD2 : Matrix (Fin 2) (Fin 2) K) = levD2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hadj, levD2]

theorem radBasis_mem {p f : ℕ} (h : UnitaryFieldData p f K) {η : K} (hη : h.bar η = -η)
    (i : Fin 4) : radBasis η i ∈ skewHermMatrices h 2 := by
  rw [mem_skewHermMatrices_iff]
  intro k l
  fin_cases i <;> fin_cases k <;> fin_cases l <;> simp [radBasis, hη]

end Matrices

section Spanning

variable {K : Type} [Field K]

theorem three_eq_zero_of_data (h : UnitaryFieldData 3 1 K) : (3 : K) = 0 := by
  have : CharP K 3 := h.charP
  exact_mod_cast CharP.cast_eq_zero K 3

theorem exists_natCast_of_bar_eq (h : UnitaryFieldData 3 1 K) {x : K} (hx : h.bar x = x) :
    ∃ c : ℕ, x = c := by
  have h3 := three_eq_zero_of_data h
  have h1 : x ^ 3 = x := by simpa [h.bar_apply] using hx
  have h2 : x * (x - 1) * (x + 1) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h2 | h2
    · exact ⟨0, by simpa using h2⟩
    · exact ⟨1, by simpa [sub_eq_zero] using h2⟩
  · exact ⟨2, by push_cast; linear_combination h2 - h3⟩

theorem exists_natCast_mul_of_bar_eq_neg (h : UnitaryFieldData 3 1 K) {η : K}
    (hη : h.bar η = -η) (hη0 : η ≠ 0) {x : K} (hx : h.bar x = -x) : ∃ c : ℕ, x = c * η := by
  have hxη : h.bar (x / η) = x / η := by
    rw [map_div₀, hx, hη, neg_div_neg_eq]
  obtain ⟨c, hc⟩ := exists_natCast_of_bar_eq h hxη
  exact ⟨c, by rw [← hc]; field_simp⟩

theorem exists_natCast_add_mul (h : UnitaryFieldData 3 1 K) {η : K} (hη : h.bar η = -η)
    (hη0 : η ≠ 0) (x : K) : ∃ a b : ℕ, x = a + b * η := by
  have h3 := three_eq_zero_of_data h
  have hy : h.bar (x + h.bar x) = x + h.bar x := by rw [map_add, h.bar_bar, add_comm]
  have hz : h.bar (x - h.bar x) = -(x - h.bar x) := by rw [map_sub, h.bar_bar, neg_sub]
  obtain ⟨c, hc⟩ := exists_natCast_of_bar_eq h hy
  obtain ⟨c', hc'⟩ := exists_natCast_mul_of_bar_eq_neg h hη hη0 hz
  refine ⟨2 * c, 2 * c', ?_⟩
  push_cast
  linear_combination 2 * hc + 2 * hc' - x * h3

theorem exists_nsmul_decomp (h : UnitaryFieldData 3 1 K) {η : K} (hη : h.bar η = -η)
    (hη0 : η ≠ 0) {B : Matrix (Fin 2) (Fin 2) K} (hB : B ∈ skewHermMatrices h 2) :
    ∃ α : Fin 4 → ℕ, B = ∑ i, α i • radBasis η i := by
  have h3 := three_eq_zero_of_data h
  have hB' := (mem_skewHermMatrices_iff h).mp hB
  have e00 : h.bar (B 0 0) = -B 0 0 := eq_neg_of_add_eq_zero_right (hB' 0 0)
  have e11 : h.bar (B 1 1) = -B 1 1 := eq_neg_of_add_eq_zero_right (hB' 1 1)
  have e10 : B 1 0 = -h.bar (B 0 1) := eq_neg_of_add_eq_zero_left (hB' 1 0)
  obtain ⟨c₁, hc₁⟩ := exists_natCast_mul_of_bar_eq_neg h hη hη0 e00
  obtain ⟨c₂, hc₂⟩ := exists_natCast_mul_of_bar_eq_neg h hη hη0 e11
  obtain ⟨a, b, hab⟩ := exists_natCast_add_mul h hη hη0 (B 0 1)
  have hba : B 1 0 = -(a : K) + b * η := by
    rw [e10, hab, map_add, map_mul, map_natCast, map_natCast, hη]
    ring
  refine ⟨![2 * c₁ + 2 * c₂, 2 * c₁ + c₂, b, a], ?_⟩
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Fin.sum_univ_four]
  fin_cases i <;> fin_cases j <;> simp [radBasis]
  · linear_combination hc₁ - ((c₁ : K) + c₂) * η * h3
  · linear_combination hab
  · linear_combination hba
  · linear_combination hc₂

end Spanning

section Pairing

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {r m n : ℕ}
  {P : Matrix (Fin n) ((Fin r ⊕ Fin r) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram r m K) (hnm : 2 * r + m = n)
  {Y : Type} [Group Y] {φ : Y →* unitarySU 3 1 K n} (hφ : Function.Surjective φ)
  (hZ : φ.ker ≤ Subgroup.center Y)

include hZ in
theorem liftPair_eq_one_of_levi {D : Matrix (Fin r) (Fin r) K} (hD : hadj h D = D)
    (hDD : D * D = 1) {u w : skewHermMatrices h r} (hu : leviAct h hD u = u)
    (hw : leviAct h hD w = -w) :
    liftPair hφ (frameSUHom h hP hnm) u w = 1 ∧ liftPair hφ (frameSUHom h hP hnm) w u = 1 := by
  have : CharP K 3 := h.charP
  obtain ⟨g, hg⟩ := exists_leviSU_conj h hP hnm hD hDD
  have h3 : ∀ v : skewHermMatrices h r, 3 • v = 0 := nsmul_char_eq_zero _
  have h2 : ∀ v : skewHermMatrices h r, 2 • v = -v := fun v => by
    have : 2 • v + v = 0 := by rw [← succ_nsmul]; exact h3 v
    exact eq_neg_of_add_eq_zero_left this
  have key1 : liftPair hφ (frameSUHom h hP hnm) u (-w) =
      liftPair hφ (frameSUHom h hP hnm) u w := by
    have := liftPair_conj' hφ (frameSUHom h hP hnm) hZ g (hg u) (hg w)
    rwa [hu, hw] at this
  have key2 : liftPair hφ (frameSUHom h hP hnm) (-w) u =
      liftPair hφ (frameSUHom h hP hnm) w u := by
    have := liftPair_conj' hφ (frameSUHom h hP hnm) hZ g (hg w) (hg u)
    rwa [hu, hw] at this
  refine ⟨liftPair_eq_one_of_weight hφ (frameSUHom h hP hnm) hZ Nat.prime_three (h3 u)
    (s := 1) (t := 2) (by norm_num) (by norm_num) ?_,
    liftPair_eq_one_of_weight hφ (frameSUHom h hP hnm) hZ Nat.prime_three (h3 w)
    (s := 2) (t := 1) (by norm_num) (by norm_num) ?_⟩
  · rw [one_smul, h2, key1]
  · rw [h2, one_smul, key2]

end Pairing

section Radical

variable {K : Type} [Field K] (h : UnitaryFieldData 3 1 K) {m n : ℕ}
  {P : Matrix (Fin n) ((Fin 2 ⊕ Fin 2) ⊕ Fin m) K}
  (hP : hadj h P * P = frameGram 2 m K) (hnm : 2 * 2 + m = n)
  {Y : Type} [Group Y] {φ : Y →* unitarySU 3 1 K n} (hφ : Function.Surjective φ)
  (hZ : φ.ker ≤ Subgroup.center Y)

def radVec {η : K} (hη : h.bar η = -η) (i : Fin 4) : skewHermMatrices h 2 :=
  ⟨radBasis η i, radBasis_mem h hη i⟩

theorem levD1_act_zero {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD1 h) (radVec h hη 0) = radVec h hη 0 :=
  Subtype.ext (levD1_conj_zero η)

theorem levD1_act_one {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD1 h) (radVec h hη 1) = radVec h hη 1 :=
  Subtype.ext (levD1_conj_one η)

theorem levD1_act_two {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD1 h) (radVec h hη 2) = -radVec h hη 2 :=
  Subtype.ext (levD1_conj_two η)

theorem levD1_act_three {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD1 h) (radVec h hη 3) = -radVec h hη 3 :=
  Subtype.ext (levD1_conj_three η)

theorem levD2_act_zero {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD2 h) (radVec h hη 0) = radVec h hη 0 :=
  Subtype.ext (levD2_conj_zero η)

theorem levD2_act_one {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD2 h) (radVec h hη 1) = -radVec h hη 1 :=
  Subtype.ext (levD2_conj_one η)

theorem levD2_act_two {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD2 h) (radVec h hη 2) = radVec h hη 2 :=
  Subtype.ext (levD2_conj_two η)

theorem levD2_act_three {η : K} (hη : h.bar η = -η) :
    leviAct h (hadj_levD2 h) (radVec h hη 3) = -radVec h hη 3 :=
  Subtype.ext (levD2_conj_three η)

include hZ in
theorem liftPair_radVec {η : K} (hη : h.bar η = -η) (i j : Fin 4) :
    liftPair hφ (frameSUHom h hP hnm) (radVec h hη i) (radVec h hη j) = 1 := by
  have p01 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD2 h) levD2_mul_self
    (levD2_act_zero h hη) (levD2_act_one h hη)
  have p02 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD1 h) levD1_mul_self
    (levD1_act_zero h hη) (levD1_act_two h hη)
  have p03 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD1 h) levD1_mul_self
    (levD1_act_zero h hη) (levD1_act_three h hη)
  have p12 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD1 h) levD1_mul_self
    (levD1_act_one h hη) (levD1_act_two h hη)
  have p13 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD1 h) levD1_mul_self
    (levD1_act_one h hη) (levD1_act_three h hη)
  have p23 := liftPair_eq_one_of_levi h hP hnm hφ hZ (hadj_levD2 h) levD2_mul_self
    (levD2_act_two h hη) (levD2_act_three h hη)
  fin_cases i <;> fin_cases j
  · exact liftPair_self hφ _ _
  · exact p01.1
  · exact p02.1
  · exact p03.1
  · exact p01.2
  · exact liftPair_self hφ _ _
  · exact p12.1
  · exact p13.1
  · exact p02.2
  · exact p12.2
  · exact liftPair_self hφ _ _
  · exact p23.1
  · exact p03.2
  · exact p13.2
  · exact p23.2
  · exact liftPair_self hφ _ _

include hZ in
theorem liftPair_radical {η : K} (hη : h.bar η = -η) (hη0 : η ≠ 0)
    (v w : skewHermMatrices h 2) : liftPair hφ (frameSUHom h hP hnm) v w = 1 := by
  have hspan : ∀ v : skewHermMatrices h 2, ∃ α : Fin 4 → ℕ, v = ∑ i, α i • radVec h hη i := by
    intro v
    obtain ⟨α, hα⟩ := exists_nsmul_decomp h hη hη0 v.2
    exact ⟨α, Subtype.ext (by simpa [radVec] using hα)⟩
  obtain ⟨α, hα⟩ := hspan v
  obtain ⟨γ, hγ⟩ := hspan w
  rw [hα, hγ]
  exact liftPair_eq_one_of_sum hφ (frameSUHom h hP hnm) hZ Finset.univ Finset.univ
    (fun i => α i • radVec h hη i) (fun j => γ j • radVec h hη j) fun i _ j _ => by
      rw [liftPair_nsmul_left hφ _ hZ, liftPair_nsmul_right hφ _ hZ,
        liftPair_radVec h hP hnm hφ hZ hη, one_pow, one_pow]

end Radical

end RadicalU

theorem exists_su4_three_radical {p e : ℕ} [Fact p.Prime] (hp3 : p = 3) (he : e = 1)
    {K : Type} [Field K] (hK : Nat.card K = p ^ (2 * e)) :
    ∃ E₀ : Subgroup (StatedSU 4 (p ^ e) K), IsElementaryAbelian p E₀ ∧ Nat.card E₀ = p ^ 4 ∧
      ∀ (Y : Type) [Group Y] (φ : Y →* StatedSU 4 (p ^ e) K), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y → ∀ x ∈ E₀.comap φ, ∀ y ∈ E₀.comap φ, x * y = y * x := by
  subst hp3 he
  classical
  have h : UnitaryFieldData 3 1 K := ⟨Fact.out, le_refl 1, hK⟩
  have : CharP K 3 := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K 3]; norm_num)
  obtain ⟨P, hP⟩ := exists_evenFrame h h2 (n := 4) (r := 2) (by norm_num)
  have hP' : hadj h P * P = frameGram 2 (4 - 2 * 2) K := hP
  have hnm : 2 * 2 + (4 - 2 * 2) = 4 := by omega
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  have hη0 : c - h.bar c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have hη : h.bar (c - h.bar c) = -(c - h.bar c) := by rw [map_sub, h.bar_bar, neg_sub]
  set φ₀ := frameSUHom h hP' hnm with hφ₀
  have hinj : Function.Injective φ₀ :=
    Function.Injective.of_comp (f := unitaryProj h 4) (frameUnipotentHom_injective h hP' hnm)
  have hpow : ∀ a : Multiplicative (skewHermMatrices h 2), a ^ 3 = 1 := fun a =>
    Multiplicative.toAdd.injective (by rw [toAdd_pow, toAdd_one]; exact nsmul_char_eq_zero _ _)
  refine ⟨φ₀.range, CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range φ₀ hpow, ?_, ?_⟩
  · rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, card_skewHermMatrices]
    norm_num
  · intro Y _ φ hφ hZ x hx y hy
    exact mul_comm_of_liftPair_eq_one hφ φ₀ hZ
      (RadicalU.liftPair_radical h hP' hnm hφ hZ hη hη0) (Subgroup.mem_comap.mp hx)
      (Subgroup.mem_comap.mp hy)

end CFSG.RankThree.PartOne.SLB4B
