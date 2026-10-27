module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4DiagPSU
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.ClassicalInvolution.Phan.Torus
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD291DefCharSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open CFSG.Open Subgroup
open Matrix CFSG.GH74.L5U5 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.GH74.GLS.Stage2.Final.ModelOrd
open CFSG.ClassicalGroups.UnitaryFlag

variable {K : Type} [Field K] [Finite K]

private lemma stdDiagHom_coe (ζ : CubeRoot K) (v : Multiplicative (Fin 4 → ZMod 3)) :
    (((stdDiagHom ζ v : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => ((ζ.pow (Multiplicative.toAdd v i -
        ∑ j, Multiplicative.toAdd v j)) : K)) := rfl

private lemma cent1_w_ne (ζ : CubeRoot K) : (ζ.ω : K) ≠ ((ζ.ω)⁻¹ : K) := by
  intro h
  have h3 : (ζ.ω : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
    simpa using this
  have hω2 : (ζ.ω : K) ^ 2 = (ζ.ω : K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc (ζ.ω : K) * (ζ.ω : K) ^ 2 = (ζ.ω : K) ^ 3 := by ring
      _ = 1 := h3
  have h2 : (ζ.ω : K) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ (Units.ne_zero ζ.ω)
  have hone : (ζ.ω : K) = 1 := by
    have h1 : (ζ.ω : K) = (ζ.ω : K) ^ 2 := by
      calc (ζ.ω : K) = (ζ.ω : K)⁻¹ := h
        _ = (ζ.ω : K) ^ 2 := hω2.symm
    exact h1.trans h2
  exact ζ.ne_one (Units.ext hone)

private lemma cent1_diag_d1 (ζ : CubeRoot K) :
    (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i : Fin 4 => if i = 0 ∨ i = 1 then (ζ.ω : K) else ((ζ.ω)⁻¹ : K)) := by
  have hs : (∑ x : Fin 4, (![1, 1, -1, -1] : Fin 4 → ZMod 3) x) = 0 := by decide
  have h3 : (ζ.ω : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
    simpa using this
  have hω2 : (ζ.ω : K) ^ 2 = (ζ.ω : K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc (ζ.ω : K) * (ζ.ω : K) ^ 2 = (ζ.ω : K) ^ 3 := by ring
      _ = 1 := h3
  have h1 : ((1 : ZMod 3) - 0).val = 1 := by decide
  have hm1 : ((-1 : ZMod 3) - 0).val = 2 := by decide
  rw [d₁, stdDiagHom_coe]
  simp only [toAdd_ofAdd]
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [CubeRoot.pow, hω2, h1, hm1]

private lemma cent1_diag_y :
    (((yGL K : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i : Fin 4 => if i = 0 ∨ i = 1 then (-1 : K) else 1) := by
  have hbase : (((yGL K : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (![-1, -1, 1, 1] : Fin 4 → K) := by
    rw [yGL, coe_diagGL, Units.val_neg, Units.val_one]
    rw [blk4_eq_reindex, Matrix.coe_reindexAlgEquiv]
    have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
    have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
    have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
    have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock,
        Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks, e0, e1, e2, e3]
  rw [hbase]
  congr 1
  funext i
  fin_cases i <;> simp

private lemma commute_diagonal_congr {d e : Fin 4 → K}
    (h : ∀ i j, d i = d j ↔ e i = e j) (g : Matrix (Fin 4) (Fin 4) K) :
    Commute (Matrix.diagonal d) g ↔ Commute (Matrix.diagonal e) g := by
  constructor
  · intro hg
    rw [Commute]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : e i = e j
    · rw [hij, mul_comm]
    · have hd : d i ≠ d j := fun hd => hij ((h i j).1 hd)
      rw [TauCeti.apply_eq_zero_of_commute_diagonal hg hd, mul_zero, zero_mul]
  · intro hg
    rw [Commute]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : d i = d j
    · rw [hij, mul_comm]
    · have he : e i ≠ e j := fun he => hij ((h i j).2 he)
      rw [TauCeti.apply_eq_zero_of_commute_diagonal hg he, mul_zero, zero_mul]

private lemma commute_units_iff_matrix (g a : GL (Fin 4) K) :
    g * a = a * g ↔ Commute ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      (g : Matrix (Fin 4) (Fin 4) K) := by
  constructor
  · intro h
    have h' : (g : Matrix (Fin 4) (Fin 4) K) *
        ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
          (g : Matrix (Fin 4) (Fin 4) K) := by
      have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
      simpa only [Units.val_mul] using this
    exact h'.symm
  · intro h
    apply Units.ext
    have h' : ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (g : Matrix (Fin 4) (Fin 4) K) =
        (g : Matrix (Fin 4) (Fin 4) K) *
          ((a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := h
    simpa only [Units.val_mul] using h'.symm

private lemma cent1_commuteGL (ζ : CubeRoot K) (h2k : (2 : K) ≠ 0) (g : GL (Fin 4) K) :
    g * d₁ ζ = d₁ ζ * g ↔ g * yGL K = yGL K * g := by
  have h1 := cent1_diag_d1 ζ
  have h2 := cent1_diag_y (K := K)
  have hneg : (-1 : K) ≠ 1 := by
    intro h
    apply h2k
    have h1 : (-1 : K) + 1 = (1 : K) + 1 := congrArg (fun x : K => x + 1) h
    have h2 : (-1 : K) + 1 = 0 := by ring
    have h3 : (1 : K) + 1 = 2 := by ring
    rw [h2, h3] at h1
    exact h1.symm
  have hcond : ∀ i j : Fin 4,
      (if i = 0 ∨ i = 1 then (ζ.ω : K) else ((ζ.ω)⁻¹ : K)) =
        (if j = 0 ∨ j = 1 then (ζ.ω : K) else ((ζ.ω)⁻¹ : K)) ↔
      (if i = 0 ∨ i = 1 then (-1 : K) else 1) =
        (if j = 0 ∨ j = 1 then (-1 : K) else 1) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [cent1_w_ne ζ, (cent1_w_ne ζ).symm, hneg, hneg.symm]
  have key : Commute ((d₁ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      (g : Matrix (Fin 4) (Fin 4) K) ↔
      Commute ((yGL K : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        (g : Matrix (Fin 4) (Fin 4) K) := by
    have := commute_diagonal_congr hcond (g : Matrix (Fin 4) (Fin 4) K)
    rwa [← h1, ← h2] at this
  rw [commute_units_iff_matrix g (d₁ ζ), commute_units_iff_matrix g (yGL K)]
  exact key

private lemma cent1_centralizer_eq {r : ℕ} (ζ : CubeRoot K) (h2k : (2 : K) ≠ 0)
    {d y : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₁ ζ)
    (hy : (y : GL (Fin 4) K) = yGL K) :
    Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) =
      Subgroup.centralizer ({y} : Set (StatedSU 4 r K)) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  rw [Subtype.ext_iff, Subtype.ext_iff]
  simp only [Subgroup.coe_mul]
  rw [hd, hy]
  exact cent1_commuteGL ζ h2k (g : GL (Fin 4) K)

private noncomputable abbrev cent1_model {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2) :
    ModelData K :=
  letI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  letI : CharP K r := hUF.charP
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  have hpowSU : StatedSU 4 r K = StatedSU 4 (r ^ 1) K := by rw [pow_one]
  have hpowSU2 : StatedSU 2 r K = StatedSU 2 (r ^ 1) K := by rw [pow_one]
  { U2 := uniGL (unitaryInvolution K r 1) 2
    U4 := uniGL (unitaryInvolution K r 1) 4
    K4 := StatedSU 4 r K
    H2 := StatedSU 2 r K
    mem_K4 g := by
      rw [hpowSU, ← SUid_eq_statedSU hF, SUid_four_eq_inf]
      simp [mem_detOne]
    mem_H2 g := by
      rw [hpowSU2, ← SUid_eq_statedSU hF, SUid_two_eq_inf]
      simp [mem_detOne]
    diag_mem_iff a b := by
      rw [mem_uniGL, mem_uniGL, mem_uniGL, coe_diagGL, conjTr_blk4, blk4_mul, ← blk4_one]
      constructor
      · intro h; exact blk4_inj h
      · rintro ⟨h1, h2⟩; rw [h1, h2]
    neg_mem := by
      rw [mem_uniGL]
      simp only [Units.val_neg, Units.val_one]
      rw [conjTr_neg_one]; simp
    swap_mem := by
      rw [mem_uniGL, coe_swapGL, conjTr_wMat]
      exact wMat_mul_self }

private lemma cent1_factorization {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    (r ^ 2 * ((r + 1) * (r ^ 2 - 1) ^ 2)).factorization r = 2 := by
  have hX1 : ¬ r ∣ r + 1 := by
    intro h
    have h1 : r ∣ 1 := by
      have hh := Nat.dvd_sub h (dvd_refl r)
      have h2 : r + 1 - r = 1 := by omega
      rwa [h2] at hh
    exact hr.not_dvd_one h1
  have hX2 : ¬ r ∣ r ^ 2 - 1 := by
    intro h
    have hb : r ∣ r ^ 2 := ⟨r, by ring⟩
    have h1 : r ∣ 1 := by
      have hh := Nat.dvd_sub hb h
      have h2 : r ^ 2 - (r ^ 2 - 1) = 1 := by
        rw [Nat.sub_sub_self (by nlinarith [h5])]
      rwa [h2] at hh
    exact hr.not_dvd_one h1
  have hX : ¬ r ∣ (r + 1) * (r ^ 2 - 1) ^ 2 := by
    intro h
    rcases (hr.dvd_mul).mp h with h' | h'
    · exact hX1 h'
    · exact hX2 (hr.dvd_of_dvd_pow h')
  have hXne : (r + 1) * (r ^ 2 - 1) ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · omega
    · apply pow_ne_zero
      have h : 1 < r ^ 2 := by nlinarith [h5]
      omega
  rw [Nat.factorization_mul (pow_ne_zero 2 hr.ne_zero) hXne]
  rw [Finsupp.add_apply, Nat.factorization_pow_self hr,
    Nat.factorization_eq_zero_of_not_dvd hX]

theorem cent1_card_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₁ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))).factorization r = 2 := by
  intro d hd
  letI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  letI : CharP K r := hUF.charP
  have h2k : (2 : K) ≠ 0 := by
    intro h
    have hdvd : r ∣ 2 := (CharP.cast_eq_zero_iff K r 2).mp h
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  let M := cent1_model (K := K) hr hK
  have hcent := cent1_centralizer_eq (r := r) ζ h2k (y := M.yK) hd rfl
  have hcard : Nat.card ↥(Subgroup.centralizer ({M.yK} : Set (StatedSU 4 r K))) =
      Nat.card ↥M.U2 * Nat.card ↥M.H2 :=
    card_centralizer_yK M h2k
  have hH2z := card_statedSU_int hUF (n := 2) (by norm_num)
  rw [prod_Icc_two_two, show 2 * (2 - 1) / 2 = 1 by norm_num] at hH2z
  rw [pow_one] at hH2z
  rw [pow_one] at hH2z
  rw [show ((r : ℤ) ^ 2 - 1) = ((r ^ 2 - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (by nlinarith [h5]), Nat.cast_pow, Nat.cast_one]] at hH2z
  have hH2 : Nat.card ↥M.H2 = r * (r ^ 2 - 1) := by
    exact_mod_cast hH2z
  have hU2z := card_uniGL_int hUF (n := 2) (by norm_num)
  rw [prod_Icc_one_two, show 2 * (2 - 1) / 2 = 1 by norm_num] at hU2z
  rw [pow_one] at hU2z
  rw [pow_one] at hU2z
  rw [show ((r : ℤ) ^ 2 - 1) = ((r ^ 2 - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (by nlinarith [h5]), Nat.cast_pow, Nat.cast_one]] at hU2z
  rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring] at hU2z
  have hU2 : Nat.card ↥M.U2 = r * ((r + 1) * (r ^ 2 - 1)) := by
    exact_mod_cast hU2z
  rw [hcent, hcard, hU2, hH2]
  have harith : r * ((r + 1) * (r ^ 2 - 1)) * (r * (r ^ 2 - 1)) =
      r ^ 2 * ((r + 1) * (r ^ 2 - 1) ^ 2) := by ring
  rw [harith]
  exact cent1_factorization hr h5

private def cent2_t (ζ : CubeRoot K) : Fin 4 → K :=
  ![(ζ.ω : K), ((ζ.ω)⁻¹ : K), 1, 1]

private lemma cent2_diag_d2 (ζ : CubeRoot K) :
    (((d₂ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (cent2_t ζ) := by
  have hs : (∑ x : Fin 4, (![1, -1, 0, 0] : Fin 4 → ZMod 3) x) = 0 := by decide
  have h1 : ((1 : ZMod 3) - 0).val = 1 := by decide
  have hm1 : ((-1 : ZMod 3) - 0).val = 2 := by decide
  have h0 : ((0 : ZMod 3) - 0).val = 0 := by decide
  have h3 : (ζ.ω : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
    simpa using this
  have hω2 : (ζ.ω : K) ^ 2 = (ζ.ω : K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc (ζ.ω : K) * (ζ.ω : K) ^ 2 = (ζ.ω : K) ^ 3 := by ring
      _ = 1 := h3
  have hself : (ζ.ω : K) ≠ 1 := fun h => ζ.ne_one (Units.ext h)
  rw [d₂, stdDiagHom_coe]
  simp only [toAdd_ofAdd]
  rw [hs]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cent2_t, CubeRoot.pow, hω2, h1, hm1, h0, hself]

private lemma cent2_w_ne (ζ : CubeRoot K) : (ζ.ω : K) ≠ ((ζ.ω)⁻¹ : K) := by
  intro h
  have h3 : (ζ.ω : K) ^ 3 = 1 := by
    have := congrArg (fun u : Kˣ => (u : K)) ζ.pow_three
    simpa using this
  have hω2 : (ζ.ω : K) ^ 2 = (ζ.ω : K)⁻¹ := by
    apply eq_inv_of_mul_eq_one_right
    calc (ζ.ω : K) * (ζ.ω : K) ^ 2 = (ζ.ω : K) ^ 3 := by ring
      _ = 1 := h3
  have h2 : (ζ.ω : K) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ (Units.ne_zero ζ.ω)
  have hone : (ζ.ω : K) = 1 := by
    have h1 : (ζ.ω : K) = (ζ.ω : K) ^ 2 := by
      calc (ζ.ω : K) = (ζ.ω : K)⁻¹ := h
        _ = (ζ.ω : K) ^ 2 := hω2.symm
    exact h1.trans h2
  exact ζ.ne_one (Units.ext hone)

private lemma cent2_block_extract (ζ : CubeRoot K) {g : Matrix (Fin 4) (Fin 4) K}
    (hg : Commute (Matrix.diagonal (cent2_t ζ)) g) :
    g = blk4 (Matrix.diagonal ![g 0 0, g 1 1]) !![g 2 2, g 2 3; g 3 2, g 3 3] := by
  have hω := cent2_w_ne ζ
  have hω1 : (ζ.ω : K) ≠ 1 := fun h => ζ.ne_one (Units.ext h)
  have hω1' : ((ζ.ω : K)⁻¹) ≠ 1 := by
    intro h
    exact hω1 (inv_eq_one.mp h)
  have h01 : g 0 1 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω, (hω).symm])
  have h10 : g 1 0 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω, (hω).symm])
  have h02 : g 0 2 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1, hω1.symm])
  have h20 : g 2 0 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1, hω1.symm])
  have h03 : g 0 3 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1, hω1.symm])
  have h30 : g 3 0 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1, hω1.symm])
  have h12 : g 1 2 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1', hω1'.symm, (hω).symm, hω1.symm])
  have h21 : g 2 1 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1', hω1'.symm, (hω).symm, hω1.symm])
  have h13 : g 1 3 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1', hω1'.symm, (hω).symm, hω1.symm])
  have h31 : g 3 1 = 0 := TauCeti.apply_eq_zero_of_commute_diagonal hg
    (by simp [cent2_t, hω1', hω1'.symm, (hω).symm, hω1.symm])
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks, e0, e1, e2, e3,
      h01, h10, h02, h20, h03, h30, h12, h21, h13, h31]

private def cent2_diag2 (a b : Kˣ) : GL (Fin 2) K where
  val := Matrix.diagonal ![(a : K), (b : K)]
  inv := Matrix.diagonal ![(a : K)⁻¹, (b : K)⁻¹]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

private lemma cent2_diag2_coe (a b : Kˣ) :
    ((cent2_diag2 a b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      Matrix.diagonal ![(a : K), (b : K)] := rfl

private lemma cent2_diag2_mem_uniGL {r : ℕ} [Fact r.Prime] [CharP K r]
    (hUF : UnitaryFieldData r 1 K) (a b : Kˣ) :
    cent2_diag2 a b ∈ uniGL (unitaryInvolution K r 1) 2 ↔
      hUF.norm (a : K) = 1 ∧ hUF.norm (b : K) = 1 := by
  rw [mem_uniGL]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [cent2_diag2, conjTr, unitaryInvolution_apply, frobenius_def,
      Matrix.diagonal_mul_diagonal] at h00 h11
    exact ⟨by simpa [UnitaryFieldData.norm, hUF.bar_apply, pow_one, mul_comm] using h00,
      by simpa [UnitaryFieldData.norm, hUF.bar_apply, pow_one, mul_comm] using h11⟩
  · rintro ⟨h1, h2⟩
    have h1' : (a : K) ^ r * (a : K) = 1 := by
      simpa [UnitaryFieldData.norm, hUF.bar_apply, pow_one, mul_comm] using h1
    have h2' : (b : K) ^ r * (b : K) = 1 := by
      simpa [UnitaryFieldData.norm, hUF.bar_apply, pow_one, mul_comm] using h2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cent2_diag2, conjTr, unitaryInvolution_apply, frobenius_def,
        Matrix.diagonal_mul_diagonal, hUF.prime.ne_zero, h1', h2']

private lemma cent2_norm_det {r : ℕ} [Fact r.Prime] [CharP K r] (hUF : UnitaryFieldData r 1 K)
    {n : ℕ} {M : GL (Fin n) K} (hM : M ∈ uniGL (unitaryInvolution K r 1) n) :
    hUF.norm ((Matrix.GeneralLinearGroup.det M : Kˣ) : K) = 1 := by
  have h := (mem_uniGL (σ := unitaryInvolution K r 1)).mp hM
  have hdet := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one, conjTr, Matrix.det_transpose] at hdet
  change (RingHom.mapMatrix (unitaryInvolution K r 1)
    (M : Matrix (Fin n) (Fin n) K)).det * (M : Matrix (Fin n) (Fin n) K).det = 1 at hdet
  rw [← RingHom.map_det] at hdet
  have hbar : (unitaryInvolution K r 1 : K →+* K) = hUF.bar := by
    ext c
    change unitaryInvolution K r 1 c = hUF.bar c
    rw [unitaryInvolution_apply, hUF.bar_apply, pow_one]
  rw [hbar] at hdet
  rw [UnitaryFieldData.norm, Matrix.GeneralLinearGroup.val_det_apply, mul_comm]
  exact hdet

private def cent2C {r : ℕ} (ζ : CubeRoot K) : Subgroup (StatedSU 4 r K) :=
  (Subgroup.centralizer ({d₂ ζ} : Set (GL (Fin 4) K))).comap (StatedSU 4 r K).subtype

private lemma mem_cent2C {r : ℕ} {ζ : CubeRoot K} {g : StatedSU 4 r K} :
    g ∈ cent2C (r := r) ζ ↔ (g : GL (Fin 4) K) * d₂ ζ = d₂ ζ * (g : GL (Fin 4) K) := by
  rw [cent2C, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
  rfl

private lemma cent2_d2_blk4 (ζ : CubeRoot K) :
    (((d₂ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      blk4 (Matrix.diagonal ![(ζ.ω : K), ((ζ.ω)⁻¹ : K)]) 1 := by
  rw [cent2_diag_d2]
  have e0 : (finSumFinEquiv.symm (0 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 0 := by decide
  have e1 : (finSumFinEquiv.symm (1 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inl 1 := by decide
  have e2 : (finSumFinEquiv.symm (2 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 0 := by decide
  have e3 : (finSumFinEquiv.symm (3 : Fin 4) : Fin 2 ⊕ Fin 2) = Sum.inr 1 := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cent2_t, blk4, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.diagBlock,
      Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks, e0, e1, e2, e3]

private noncomputable def cent2_std (a : Kˣ) (M : GL (Fin 2) K) : GL (Fin 4) K :=
  diagGL (cent2_diag2 a ((a * Matrix.GeneralLinearGroup.det M)⁻¹)) M

private lemma cent2_std_mem_K4 {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (hUF : UnitaryFieldData r 1 K) (a : Kˣ) (M : GL (Fin 2) K)
    (ha : hUF.norm (a : K) = 1) (hM : M ∈ (cent1_model (K := K) hr hK).U2) :
    cent2_std a M ∈ (cent1_model (K := K) hr hK).K4 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := hUF.charP
  have hMuni : M ∈ uniGL (unitaryInvolution K r 1) 2 := hM
  have hb : hUF.norm (((a * Matrix.GeneralLinearGroup.det M)⁻¹ : Kˣ) : K) = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv_eq hUF, Units.val_mul, norm_mul_eq hUF,
      ha, one_mul, cent2_norm_det hUF hMuni, inv_one]
  have hA : cent2_diag2 a ((a * Matrix.GeneralLinearGroup.det M)⁻¹) ∈
      (cent1_model (K := K) hr hK).U2 := by
    show cent2_diag2 a ((a * Matrix.GeneralLinearGroup.det M)⁻¹) ∈
      uniGL (unitaryInvolution K r 1) 2
    rw [cent2_diag2_mem_uniGL hUF]
    exact ⟨ha, hb⟩
  have hdet : ((cent2_diag2 a ((a * Matrix.GeneralLinearGroup.det M)⁻¹) : GL (Fin 2) K) :
      Matrix (Fin 2) (Fin 2) K).det * (M : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [cent2_diag2_coe, Matrix.det_diagonal]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.GeneralLinearGroup.val_det_apply, Units.val_inv_eq_inv_val, Units.val_mul]
    field_simp [Units.ne_zero a, (Matrix.GeneralLinearGroup.det M).ne_zero]
    exact div_self (by simpa [Matrix.GeneralLinearGroup.val_det_apply] using
      (Matrix.GeneralLinearGroup.det M).ne_zero)
  rw [cent2_std, (cent1_model (K := K) hr hK).diagGL_mem_K4_iff]
  exact ⟨hA, hM, hdet⟩

private lemma cent2_std_comm (ζ : CubeRoot K) (a : Kˣ) (M : GL (Fin 2) K) :
    cent2_std a M * d₂ ζ = d₂ ζ * cent2_std a M := by
  apply Units.ext
  simp only [Units.val_mul, cent2_std, cent2_d2_blk4, coe_diagGL, cent2_diag2_coe,
    blk4_mul]
  congr 1
  · rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]
  · rw [mul_one, one_mul]

private lemma cent2_std_mem {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) (a : Kˣ) (M : GL (Fin 2) K)
    (ha : hUF.norm (a : K) = 1) (hM : M ∈ (cent1_model (K := K) hr hK).U2) :
    (⟨cent2_std a M, cent2_std_mem_K4 hr hK hUF a M ha hM⟩ : StatedSU 4 r K) ∈
      cent2C (r := r) ζ := by
  rw [mem_cent2C]
  exact cent2_std_comm ζ a M

private noncomputable def cent2_map {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) :
    {a : Kˣ // hUF.norm (a : K) = 1} × (cent1_model (K := K) hr hK).U2 →
      cent2C (r := r) ζ :=
  fun p => ⟨⟨cent2_std p.1.1 p.2,
      cent2_std_mem_K4 hr hK hUF p.1.1 p.2 p.1.2 p.2.2⟩,
    cent2_std_mem hr hK ζ hUF p.1.1 p.2 p.1.2 p.2.2⟩

private lemma cent2_map_injective {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) :
    Function.Injective (cent2_map hr hK ζ hUF) := by
  rintro ⟨⟨a, ha⟩, M⟩ ⟨⟨a', ha'⟩, M'⟩ h
  have hmat : (cent2_std a M : Matrix (Fin 4) (Fin 4) K) =
      (cent2_std a' M' : Matrix (Fin 4) (Fin 4) K) := by
    have h1 := congrArg (fun x : cent2C (r := r) ζ =>
      ((x : StatedSU 4 r K) : GL (Fin 4) K)) h
    exact congrArg (fun x : GL (Fin 4) K => (x : Matrix (Fin 4) (Fin 4) K)) h1
  rw [cent2_std, cent2_std, coe_diagGL, coe_diagGL] at hmat
  obtain ⟨hA, hM⟩ := blk4_inj hmat
  have haeq : a = a' := by
    apply Units.ext
    have h00 := congrFun (congrFun hA 0) 0
    simpa [cent2_diag2_coe, Matrix.diagonal] using h00
  exact Prod.ext (Subtype.ext haeq) (Subtype.ext (Units.ext hM))

private lemma cent2_mem_block {r : ℕ} {ζ : CubeRoot K} (g : cent2C (r := r) ζ) :
    ((g : StatedSU 4 r K) : GL (Fin 4) K) * d₂ ζ =
      d₂ ζ * ((g : StatedSU 4 r K) : GL (Fin 4) K) := (mem_cent2C).mp g.2

private lemma cent2_comm_block (ζ : CubeRoot K) {gmat : Matrix (Fin 4) (Fin 4) K}
    (hcommD : gmat * Matrix.diagonal (cent2_t ζ) = Matrix.diagonal (cent2_t ζ) * gmat)
    (hunit : IsUnit gmat) :
    ∃ (u v : Kˣ) (B : Matrix (Fin 2) (Fin 2) K),
      gmat = blk4 (Matrix.diagonal ![(u : K), (v : K)]) B ∧ B.det ≠ 0 := by
  obtain hblock : gmat = blk4 (Matrix.diagonal ![gmat 0 0, gmat 1 1])
      !![gmat 2 2, gmat 2 3; gmat 3 2, gmat 3 3] := cent2_block_extract ζ hcommD.symm
  have hdetg : gmat.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det gmat).mp hunit).ne_zero
  have hA0 : (Matrix.diagonal ![gmat 0 0, gmat 1 1] : Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    intro h0
    apply hdetg
    rw [hblock, det_blk4, h0, zero_mul]
  have hB0 : (!![gmat 2 2, gmat 2 3; gmat 3 2, gmat 3 3] :
      Matrix (Fin 2) (Fin 2) K).det ≠ 0 := by
    intro h0
    apply hdetg
    rw [hblock, det_blk4, h0, mul_zero]
  have h00 : gmat 0 0 ≠ 0 := fun h =>
    hA0 (by rw [Matrix.det_diagonal]; simp [Fin.prod_univ_two, h])
  have h11 : gmat 1 1 ≠ 0 := fun h =>
    hA0 (by rw [Matrix.det_diagonal]; simp [Fin.prod_univ_two, h])
  exact ⟨Units.mk0 (gmat 0 0) h00, Units.mk0 (gmat 1 1) h11,
    !![gmat 2 2, gmat 2 3; gmat 3 2, gmat 3 3], hblock, hB0⟩

private lemma cent2_map_surjective_diag {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) (g : cent2C (r := r) ζ) :
    ∃ (u v : Kˣ) (b : GL (Fin 2) K),
      ((((g : cent2C (r := r) ζ) : StatedSU 4 r K) : GL (Fin 4) K) =
        diagGL (cent2_diag2 u v) b) ∧
      cent2_diag2 u v ∈ (cent1_model (K := K) hr hK).U2 ∧
      b ∈ (cent1_model (K := K) hr hK).U2 ∧
      u * v * Matrix.GeneralLinearGroup.det b = 1 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := hUF.charP
  let mdl := cent1_model (K := K) hr hK
  set gmat : Matrix (Fin 4) (Fin 4) K :=
    ((((g : cent2C (r := r) ζ) : StatedSU 4 r K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) with hgmat
  have hcommD : gmat * Matrix.diagonal (cent2_t ζ) = Matrix.diagonal (cent2_t ζ) * gmat := by
    rw [hgmat]
    have h := cent2_mem_block g
    have := congrArg (fun u : GL (Fin 4) K => (u : Matrix (Fin 4) (Fin 4) K)) h
    simpa only [Units.val_mul, cent2_diag_d2] using this
  have hunit : IsUnit gmat :=
    ⟨((g : cent2C (r := r) ζ) : StatedSU 4 r K), hgmat.symm⟩
  obtain ⟨u, v, B, hblock, hB0⟩ := cent2_comm_block ζ hcommD hunit
  let b : GL (Fin 2) K := GeneralLinearGroup.mkOfDetNeZero B hB0
  have hb : (b : Matrix (Fin 2) (Fin 2) K) = B :=
    GeneralLinearGroup.val_mkOfDetNeZero _ _
  have hg_eq : (((g : cent2C (r := r) ζ) : StatedSU 4 r K) : GL (Fin 4) K) =
      diagGL (cent2_diag2 u v) b := by
    apply Units.ext
    rw [coe_diagGL, cent2_diag2_coe, hb, ← hgmat]
    exact hblock
  have hgK4 : (((g : cent2C (r := r) ζ) : StatedSU 4 r K) : GL (Fin 4) K) ∈ mdl.K4 :=
    ((g : cent2C (r := r) ζ) : StatedSU 4 r K).2
  have hcond := (mdl.diagGL_mem_K4_iff).mp (hg_eq ▸ hgK4)
  refine ⟨u, v, b, hg_eq, hcond.1, hcond.2.1, ?_⟩
  apply Units.ext
  have h2 := hcond.2.2
  rw [cent2_diag2_coe, Matrix.det_diagonal, ← Matrix.GeneralLinearGroup.val_det_apply] at h2
  simpa [Fin.prod_univ_two, Units.val_mul] using h2

private lemma cent2_map_surjective {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) :
    Function.Surjective (cent2_map hr hK ζ hUF) := by
  intro g
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := hUF.charP
  obtain ⟨u, v, b, hg, huU2, hbU2, huv⟩ := cent2_map_surjective_diag hr hK ζ hUF g
  have hnorm : hUF.norm (u : K) = 1 :=
    ((cent2_diag2_mem_uniGL hUF u v).mp huU2).1
  refine ⟨(⟨u, hnorm⟩, ⟨b, hbU2⟩), ?_⟩
  have hv : v = (u * Matrix.GeneralLinearGroup.det b)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by simpa only [mul_assoc, mul_comm, mul_left_comm] using huv)
  apply Subtype.ext
  apply Subtype.ext
  change cent2_std u b = (((g : cent2C (r := r) ζ) : StatedSU 4 r K) : GL (Fin 4) K)
  unfold cent2_std
  rw [← hv]
  exact hg.symm

private lemma cent2_normOne_card {r : ℕ} [Fact r.Prime] [CharP K r]
    (hUF : UnitaryFieldData r 1 K) :
    Nat.card {a : Kˣ // hUF.norm (a : K) = 1} = r + 1 := by
  have hker : Nat.card {a : Kˣ // hUF.norm (a : K) = 1} =
      Nat.card (Units.map hUF.normHom).ker :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1, (UnitaryFieldData.mem_ker_normUnits hUF).2 x.2⟩
        invFun := fun x => ⟨x.1, (UnitaryFieldData.mem_ker_normUnits hUF).1 x.2⟩
        left_inv := fun _ => Subtype.ext rfl
        right_inv := fun _ => Subtype.ext rfl }
  have hc := (UnitaryFieldData.card_ker_normUnits_and_surjective hUF).1
  rw [hker, hc, pow_one]

private lemma cent2_card_C {r : ℕ} (hr : r.Prime) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (hUF : UnitaryFieldData r 1 K) :
    Nat.card (cent2C (r := r) ζ) =
      (r + 1) * Nat.card ↥(cent1_model (K := K) hr hK).U2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K r := hUF.charP
  rw [← Nat.card_congr (Equiv.ofBijective (cent2_map hr hK ζ hUF)
    ⟨cent2_map_injective hr hK ζ hUF, cent2_map_surjective hr hK ζ hUF⟩)]
  rw [Nat.card_prod, cent2_normOne_card hUF]

private lemma cent2_U2_card {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2) :
    Nat.card ↥(cent1_model (K := K) hr hK).U2 = r * ((r + 1) * (r ^ 2 - 1)) := by
  letI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  letI : CharP K r := hUF.charP
  have hU2z := card_uniGL_int hUF (n := 2) (by norm_num)
  rw [prod_Icc_one_two, show 2 * (2 - 1) / 2 = 1 by norm_num] at hU2z
  rw [pow_one] at hU2z
  rw [pow_one] at hU2z
  rw [show ((r : ℤ) ^ 2 - 1) = ((r ^ 2 - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (by nlinarith [h5]), Nat.cast_pow, Nat.cast_one]] at hU2z
  rw [show ((r : ℤ) + 1) = ((r + 1 : ℕ) : ℤ) by push_cast; ring] at hU2z
  exact_mod_cast hU2z

private lemma cent2_factorization {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) :
    ((r + 1) * (r * ((r + 1) * (r ^ 2 - 1)))).factorization r = 1 := by
  have hX1 : ¬ r ∣ r + 1 := by
    intro h
    have h1 : r ∣ 1 := by
      have hh := Nat.dvd_sub h (dvd_refl r)
      have h2 : r + 1 - r = 1 := by omega
      rwa [h2] at hh
    exact hr.not_dvd_one h1
  have hX2 : ¬ r ∣ r ^ 2 - 1 := by
    intro h
    have hb : r ∣ r ^ 2 := ⟨r, by ring⟩
    have hh := Nat.dvd_sub hb h
    have h2 : r ^ 2 - (r ^ 2 - 1) = 1 := by
      rw [Nat.sub_sub_self (by nlinarith [h5])]
    rw [h2] at hh
    exact hr.not_dvd_one hh
  have hX : ¬ r ∣ ((r + 1) * (r + 1)) * (r ^ 2 - 1) := by
    intro h
    rcases (hr.dvd_mul).mp h with h' | h'
    · rcases (hr.dvd_mul).mp h' with h'' | h''
      · exact hX1 h''
      · exact hX1 h''
    · exact hX2 h'
  have hrewrite : (r + 1) * (r * ((r + 1) * (r ^ 2 - 1))) =
      r * (((r + 1) * (r + 1)) * (r ^ 2 - 1)) := by ring
  have h2ne : r ^ 2 - 1 ≠ 0 := by
    have : 1 < r ^ 2 := by nlinarith [h5]
    omega
  rw [hrewrite]
  rw [Nat.factorization_mul hr.ne_zero (mul_ne_zero (by positivity) h2ne)]
  rw [Finsupp.add_apply, hr.factorization_self, Nat.factorization_eq_zero_of_not_dvd hX]

theorem cent2_card_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₂ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))).factorization r = 1 := by
  intro d hd
  letI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  letI : CharP K r := hUF.charP
  have hcen : Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) = cent2C (r := r) ζ := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, mem_cent2C]
    rw [Subtype.ext_iff]
    simp only [Subgroup.coe_mul]
    rw [hd]
  rw [hcen, cent2_card_C hr hK ζ hUF, cent2_U2_card hr h5 hK]
  exact cent2_factorization hr h5


private lemma cent1_uN_comm (ζ : CubeRoot K) (σ : K →+* K) (u η y : K) :
    (1 + CFSG.SectionRank.ClassicalOdd.uN (n := 4) (by norm_num) σ u η (0, y) :
        Matrix (Fin 4) (Fin 4) K) *
      (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
    (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) *
      (1 + CFSG.SectionRank.ClassicalOdd.uN (n := 4) (by norm_num) σ u η (0, y) :
        Matrix (Fin 4) (Fin 4) K) := by
  rw [cent1_diag_d1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.SectionRank.ClassicalOdd.uN, CFSG.SectionRank.ClassicalOdd.uP,
      CFSG.SectionRank.ClassicalOdd.uε, CFSG.SectionRank.ClassicalOdd.uεbar, vecMulVec_apply,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal, unitaryInvolution_apply, pow_one,
      mul_comm, mul_left_comm, mul_assoc]


private lemma cent1_rank_le_two {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    CFSG.Open.pRank r (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) ≤ 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  set C := Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) with hC
  have hfac : (Nat.card C).factorization r = 2 := by
    rw [hC]; exact cent1_card_su hr h5 hK ζ d hd
  refine CFSG.SectionRank.pRank_le hr.one_lt ?_
  intro E hE hEa
  have hEpg : IsPGroup r E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEa.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEpg.exists_card_eq
  have hdvd : r ^ k ∣ Nat.card C := by rw [← hk]; exact Subgroup.card_dvd_of_le hE
  have hk2 : k ≤ 2 := by
    have h := (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
    rwa [hfac] at h
  rw [hk]
  exact Nat.pow_le_pow_right hr.pos hk2

private def cent1_inc : Multiplicative K →* Multiplicative (K × K) :=
  (AddMonoidHom.toMultiplicative
    ({ toFun := fun y : K => (0, y)
       map_zero' := rfl
       map_add' := fun a b => by ext <;> simp } : K →+ K × K))

private noncomputable def cent1_unipotent_hom {σ : K →+* K} (u η : K) (hu : σ u * u = -1) :
    Multiplicative K →* GL (Fin 4) K :=
  (CFSG.SectionRank.ClassicalOdd.uHom₄ (n := 4) (by norm_num : 4 ≤ 4)
    (σ := σ) (u := u) (η := η) hu).comp cent1_inc

private lemma cent1_unipotent_hom_mem {r : ℕ} [Fact r.Prime] [CharP K r] {σ : K →+* K}
    {u η : K} {hu : σ u * u = -1}
    (hσeq : ∀ x, σ x = x ^ r) (hσ : ∀ x, σ (σ x) = x) (hη : σ η = -η) :
    ∀ a, cent1_unipotent_hom (σ := σ) u η hu a ∈ StatedSU 4 r K := by
  intro a
  refine Subgroup.subset_closure ⟨CFSG.SectionRank.ClassicalOdd.det_eq_one_of_hom (p := r)
    (cent1_unipotent_hom (σ := σ) u η hu) a, ?_⟩
  have hmap : (((cent1_unipotent_hom (σ := σ) u η hu a : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).map (· ^ r)) =
      (((cent1_unipotent_hom (σ := σ) u η hu a : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K).map σ) := by
    have hfun : (fun x : K => x ^ r) = σ := funext fun x => (hσeq x).symm
    rw [hfun]
  rw [hmap]
  exact CFSG.SectionRank.ClassicalOdd.hstar_uHom₄ (n := 4) (by norm_num : 4 ≤ 4)
    (σ := σ) (u := u) (η := η) hu hσ hη (cent1_inc a)

private lemma cent1_unipotent_hom_inj {σ : K →+* K} {u η : K} {hu : σ u * u = -1}
    (h2 : (2 : K) ≠ 0) (hηne : η ≠ 0) :
    Function.Injective (cent1_unipotent_hom (σ := σ) u η hu) := by
  have hM : Function.Injective (fun v : K × K =>
      (1 + CFSG.SectionRank.ClassicalOdd.uN (n := 4) (by norm_num : 4 ≤ 4)
        (σ := σ) (u := u) (η := η) v : Matrix (Fin 4) (Fin 4) K)) := by
    intro v w h
    exact CFSG.SectionRank.ClassicalOdd.uN_injective (n := 4) (by norm_num : 4 ≤ 4)
      (σ := σ) (u := u) (η := η) h2 hηne (add_left_cancel h)
  intro a b hab
  have h1 : (CFSG.SectionRank.ClassicalOdd.uHom₄ (n := 4) (by norm_num : 4 ≤ 4)
      (σ := σ) (u := u) (η := η) hu) (cent1_inc a) =
      (CFSG.SectionRank.ClassicalOdd.uHom₄ (n := 4) (by norm_num : 4 ≤ 4)
      (σ := σ) (u := u) (η := η) hu) (cent1_inc b) := by
    simpa [cent1_unipotent_hom] using hab
  have h2' : cent1_inc a = cent1_inc b :=
    CFSG.SectionRank.ClassicalOdd.glOfAdd_injective hM h1
  have h4 : a.toAdd = b.toAdd := by
    simpa [cent1_inc] using congrArg Prod.snd (congrArg Multiplicative.toAdd h2')
  exact congrArg Multiplicative.ofAdd h4

private lemma cent1_unipotent_hom_comm (ζ : CubeRoot K) {σ : K →+* K} {u η : K}
    {hu : σ u * u = -1} (a : Multiplicative K) :
    (((cent1_unipotent_hom (σ := σ) u η hu a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
      (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) *
        ((cent1_unipotent_hom (σ := σ) u η hu a : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K)) := by
  change (1 + CFSG.SectionRank.ClassicalOdd.uN (n := 4) (by norm_num : 4 ≤ 4)
      σ u η (0, Multiplicative.toAdd a) : Matrix (Fin 4) (Fin 4) K) *
      (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
    (((d₁ ζ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) *
      (1 + CFSG.SectionRank.ClassicalOdd.uN (n := 4) (by norm_num : 4 ≤ 4)
        σ u η (0, Multiplicative.toAdd a) : Matrix (Fin 4) (Fin 4) K)
  exact cent1_uN_comm ζ σ u η (Multiplicative.toAdd a)

private lemma cent1_rank_ge_two {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₁ ζ) :
    2 ≤ CFSG.Open.pRank r (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  haveI : CharP K r := hUF.charP
  have hKf : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  obtain ⟨u, η, hu0, hηne, hη0⟩ :=
    CFSG.SectionRank.ClassicalOdd.exists_unitary_elems (K := K) (p := r) (f := 1) (by omega) hKf
  haveI : Fintype K := Fintype.ofFinite K
  set σ : K →+* K := frobenius K r with hσdef
  have hu : σ u * u = -1 := by simpa [hσdef, frobenius_def, pow_one] using hu0
  have hη : σ η = -η := by simpa [hσdef, frobenius_def, pow_one] using hη0
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hdvd : r ∣ 2 := (CharP.cast_eq_zero_iff K r 2).mp h
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hσeq : ∀ x, σ x = x ^ r := fun x => by rw [hσdef, frobenius_def]
  have hσ : ∀ x, σ (σ x) = x := by
    intro x
    rw [hσeq, hσeq, ← pow_mul, ← sq, ← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  let f : Multiplicative K →* StatedSU 4 r K :=
    (cent1_unipotent_hom (σ := σ) u η hu).codRestrict _
      (cent1_unipotent_hom_mem (r := r) hσeq hσ hη)
  have hf : Function.Injective f := fun a b h =>
    cent1_unipotent_hom_inj (σ := σ) (u := u) (η := η) (hu := hu) h2 hηne
      (Subtype.ext_iff.mp h)
  have hA : Nat.card (Multiplicative K) = r ^ 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, hK]
  refine CFSG.SectionRank.le_pRank_of_injective hr.one_lt
    (fun a b => mul_comm a b)
    (fun a => CFSG.SectionRank.ClassicalOdd.pow_char_eq_one (K := K) (V := K) a)
    hA f hf ?_
  rintro x ⟨a, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [hd]
  exact cent1_unipotent_hom_comm ζ a

theorem cent1_rank_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₁ ζ →
      CFSG.Open.pRank r (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) = 2 := by
  intro d hd
  exact le_antisymm (cent1_rank_le_two hr h5 hK ζ d hd) (cent1_rank_ge_two hr h5 hK ζ d hd)

namespace Aux

open CFSG.Open CFSG.GH74.L5U5
open CFSG.LieType.Universal.Unitary
open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.BorelTits
open Subgroup Matrix

private def tstblk3 {F : Type} [Zero F] (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    Matrix (Fin 4) (Fin 4) F :=
  !![A 0 0, A 0 1, A 0 2, 0;
     A 1 0, A 1 1, A 1 2, 0;
     A 2 0, A 2 1, A 2 2, 0;
     0, 0, 0, c]

private theorem tstblk3_mul {F : Type} [Field F] (A A' : Matrix (Fin 3) (Fin 3) F) (c c' : F) :
    tstblk3 A c * tstblk3 A' c' = tstblk3 (A * A') (c * c') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tstblk3, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

private theorem tstblk3_det {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (tstblk3 A c).det = A.det * c := by
  rw [Matrix.det_succ_row _ 3, Fin.sum_univ_four]
  have h1 : (tstblk3 A c).submatrix (Fin.succAbove 3) (Fin.succAbove 3) = A := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have e0 : tstblk3 A c 3 0 = 0 := rfl
  have e1 : tstblk3 A c 3 1 = 0 := rfl
  have e2 : tstblk3 A c 3 2 = 0 := rfl
  have e3 : tstblk3 A c 3 3 = c := rfl
  rw [e0, e1, e2, e3, h1]
  norm_num
  ring

private theorem tstblk3_comm {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (c ω : F) :
    tstblk3 A c * Matrix.diagonal ![ω, ω, ω, 1] =
      Matrix.diagonal ![ω, ω, ω, 1] * tstblk3 A c := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;> simp [tstblk3, mul_comm]

private theorem tstblk3_inj {F : Type} [Zero F] :
    Function.Injective (fun p : Matrix (Fin 3) (Fin 3) F × F => tstblk3 p.1 p.2) := by
  rintro ⟨A, c⟩ ⟨A', c'⟩ h
  have hA : A = A' := by
    ext i j
    have e := congrFun (congrFun h (Fin.castSucc i)) (Fin.castSucc j)
    fin_cases i <;> fin_cases j <;> simpa [tstblk3] using e
  have hc : c = c' := by
    have e := congrFun (congrFun h 3) 3
    simpa [tstblk3] using e
  simp [hA, hc]

private theorem tstblk3_map {F : Type} [Field F] (τ : F →+* F)
    (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (tstblk3 A c).map τ = tstblk3 (A.map τ) (τ c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tstblk3]

private theorem tstblk3_transpose {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (tstblk3 A c)ᵀ = tstblk3 Aᵀ c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tstblk3]

private theorem tstblk3_gram {F : Type} [Field F] (τ : F →+* F)
    (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    ((tstblk3 A c).map τ)ᵀ * tstblk3 A c = tstblk3 ((A.map τ)ᵀ * A) (τ c * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tstblk3, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]

private theorem tstblk3_gram_equiv {F : Type} [Field F] (σ : F ≃+* F)
    (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    ((tstblk3 A c).map σ)ᵀ * tstblk3 A c = tstblk3 ((A.map σ)ᵀ * A) (σ c * c) :=
  tstblk3_gram (σ : F →+* F) A c

private theorem tstblk3_map_equiv {F : Type} [Field F] (σ : F ≃+* F)
    (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (tstblk3 A c).map σ = tstblk3 (A.map σ) (σ c) :=
  tstblk3_map (σ : F →+* F) A c

private theorem tstblk3_conjTr {F : Type} [Field F] (σ : F ≃+* F)
    (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    CFSG.LieType.Universal.Unitary.conjTr σ (tstblk3 A c) =
      tstblk3 ((A.map σ)ᵀ) (σ c) := by
  rw [CFSG.LieType.Universal.Unitary.conjTr, tstblk3_map_equiv, tstblk3_transpose]

private theorem tstblk3_inj' {F : Type} [Zero F] {A A' : Matrix (Fin 3) (Fin 3) F} {c c' : F}
    (h : tstblk3 A c = tstblk3 A' c') : A = A' ∧ c = c' := by
  have h' : (fun p : Matrix (Fin 3) (Fin 3) F × F => tstblk3 p.1 p.2) (A, c) =
      (fun p : Matrix (Fin 3) (Fin 3) F × F => tstblk3 p.1 p.2) (A', c') := h
  exact Prod.ext_iff.mp (tstblk3_inj h')


private theorem tstd3_eq (ζ : CubeRoot K) :
    ((d₃ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] := by
  have hsum : (∑ j : Fin 4, (![1, 1, 1, 0] j : ZMod 3)) = 0 := by decide
  have h10 : (1 - 0 : ZMod 3) = 1 := by decide
  have h00 : (0 - 0 : ZMod 3) = 0 := by decide
  have h1 : (1 : ZMod 3).val = 1 := by decide
  have h0 : (0 : ZMod 3).val = 0 := by decide
  ext i j
  simp only [d₃, stdDiagHom, diagUnit, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [CubeRoot.pow, hsum, h10, h00, h1, h0]

private theorem tstpattern {F : Type} [Field F] {g : Matrix (Fin 4) (Fin 4) F} {ω : F} (hω : ω ≠ 1)
    (h : g * Matrix.diagonal ![ω, ω, ω, 1] = Matrix.diagonal ![ω, ω, ω, 1] * g) :
    g 0 3 = 0 ∧ g 1 3 = 0 ∧ g 2 3 = 0 ∧ g 3 0 = 0 ∧ g 3 1 = 0 ∧ g 3 2 = 0 := by
  have hc : Commute (Matrix.diagonal ![ω, ω, ω, 1]) g := h.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω.symm)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω.symm)
  · exact TauCeti.apply_eq_zero_of_commute_diagonal hc (by simpa using hω.symm)






private def tstopLeft (g : GL (Fin 4) K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.submatrix (g : Matrix (Fin 4) (Fin 4) K) Fin.castSucc Fin.castSucc

private def tsbotRight (g : GL (Fin 4) K) : K := (g : Matrix (Fin 4) (Fin 4) K) 3 3

private theorem tsblock_of_comm {ω : K} (hω : ω ≠ 1) {g : GL (Fin 4) K}
    (h : (g : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal ![ω, ω, ω, 1] =
      Matrix.diagonal ![ω, ω, ω, 1] * (g : Matrix (Fin 4) (Fin 4) K)) :
    (g : Matrix (Fin 4) (Fin 4) K) = tstblk3 (tstopLeft g) (tsbotRight g) := by
  obtain ⟨h03, h13, h23, h30, h31, h32⟩ := tstpattern hω h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tstblk3, tstopLeft, tsbotRight, h03, h13, h23, h30, h31, h32]

private theorem tshF {r : ℕ} (hK : Nat.card K = r ^ 2) : Nat.card K = (r ^ 1) ^ 2 := by
  simpa using hK

private theorem tsH_eq {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2) :
    StatedSU 4 r K = SUid (unitaryInvolution K r 1) 4 := by
  rw [SUid_eq_statedSU (p := r) (f := 1) (by simpa using hK) 4]
  simp

private theorem tsd3_mat (ζ : CubeRoot K) : ((d₃ ζ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] := tstd3_eq ζ

private theorem tsω_ne_one (ζ : CubeRoot K) : (ζ.ω : K) ≠ 1 := by
  intro h
  apply ζ.ne_one
  apply Units.ext
  exact h





private theorem tstblk3_one {F : Type} [Field F] :
    (1 : Matrix (Fin 4) (Fin 4) F) = tstblk3 1 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tstblk3]

private theorem tscentralizer_facts {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) {g : GL (Fin 4) K} (hgH : g ∈ StatedSU 4 r K)
    (hgcomm : (g : Matrix (Fin 4) (Fin 4) K) * Matrix.diagonal
        ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
        (g : Matrix (Fin 4) (Fin 4) K)) :
    (g : Matrix (Fin 4) (Fin 4) K) = tstblk3 (tstopLeft g) (tsbotRight g) ∧
    ((tstopLeft g).map (unitaryInvolution K r 1))ᵀ * tstopLeft g = 1 ∧
    (unitaryInvolution K r 1) (tsbotRight g) * tsbotRight g = 1 ∧
    (tstopLeft g).det * tsbotRight g = 1 := by
  have hblk := tsblock_of_comm (tsω_ne_one ζ) hgcomm
  have hSU : g ∈ SUid (unitaryInvolution K r 1) 4 := by
    rw [← tsH_eq hK]
    exact hgH
  obtain ⟨hdet, huni⟩ := mem_SUid.mp hSU
  have hgram : tstblk3 (((tstopLeft g).map (unitaryInvolution K r 1))ᵀ * tstopLeft g)
      ((unitaryInvolution K r 1) (tsbotRight g) * tsbotRight g) = tstblk3 1 1 := by
    have huni' : conjTr (unitaryInvolution K r 1) (tstblk3 (tstopLeft g) (tsbotRight g)) *
        tstblk3 (tstopLeft g) (tsbotRight g) = 1 := by
      rw [← hblk]
      exact huni
    rw [tstblk3_conjTr, tstblk3_mul] at huni'
    rw [tstblk3_one] at huni'
    exact huni'
  obtain ⟨hA, hc⟩ := tstblk3_inj' hgram
  refine ⟨hblk, hA, hc, ?_⟩
  rw [hblk, tstblk3_det] at hdet
  exact hdet





private noncomputable def tstblk3GL {F : Type} [Field F] (A : GL (Fin 3) F) (c : Fˣ) :
    GL (Fin 4) F where
  val := tstblk3 (A : Matrix (Fin 3) (Fin 3) F) (c : F)
  inv := tstblk3 ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ((c⁻¹ : Fˣ) : F)
  val_inv := by
    rw [tstblk3_mul]
    simp [tstblk3_one]
  inv_val := by
    rw [tstblk3_mul]
    simp [tstblk3_one]

private theorem tstblk3GL_coe {F : Type} [Field F] (A : GL (Fin 3) F) (c : Fˣ) :
    ((tstblk3GL A c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      tstblk3 (A : Matrix (Fin 3) (Fin 3) F) (c : F) := rfl

private theorem tstopLeft_tstblk3 {F : Type} [Field F] (A : Matrix (Fin 3) (Fin 3) F) (c : F) :
    (Matrix.submatrix (tstblk3 A c) (Fin.castSucc) (Fin.castSucc)) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

section Cent3Equiv

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)

private noncomputable def tsproj {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) →
      uniGL (unitaryInvolution K r 1) 3 :=
  fun g => by
    classical
    have hgmem : ((g : StatedSU 4 r K) : GL (Fin 4) K) ∈ StatedSU 4 r K := (g : StatedSU 4 r K).2
    have hcomm : (g : StatedSU 4 r K) * d = d * (g : StatedSU 4 r K) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (g.2 : (g : StatedSU 4 r K) ∈
          Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))
    have hcomm' : (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
        Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
          (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have := congrArg (fun x : StatedSU 4 r K =>
        ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hcomm
      simpa only [Subgroup.coe_mul, Units.val_mul, hd, tsd3_mat] using this
    obtain ⟨-, hunit, -, hdet⟩ :=
      tscentralizer_facts hK ζ hgmem hcomm'
    exact ⟨Matrix.nonsingInvUnit (tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K))
        (IsUnit.of_mul_eq_one _ hdet), by
      rw [mem_uniGL]
      exact hunit⟩

end Cent3Equiv





section Cent3Bij

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)

private theorem tsproj_coe {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ)
    (g : Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) :
    ((tsproj hK ζ hd g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K) := rfl

private theorem tsproj_injective {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    Function.Injective (tsproj hK ζ hd) := by
  intro g h hgh
  have htop : tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K) =
      tstopLeft ((h : StatedSU 4 r K) : GL (Fin 4) K) := by
    have := congrArg (fun x : uniGL (unitaryInvolution K r 1) 3 =>
      ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hgh
    rwa [tsproj_coe, tsproj_coe] at this
  have hgcomm : (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
        (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have hc : (g : StatedSU 4 r K) * d = d * (g : StatedSU 4 r K) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (g.2 : (g : StatedSU 4 r K) ∈ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))
    have := congrArg (fun x : StatedSU 4 r K => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hc
    simpa only [Subgroup.coe_mul, Units.val_mul, hd, tsd3_mat] using this
  have hhcomm : (((h : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
        (((h : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    have hc : (h : StatedSU 4 r K) * d = d * (h : StatedSU 4 r K) :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (h.2 : (h : StatedSU 4 r K) ∈ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))
    have := congrArg (fun x : StatedSU 4 r K => ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hc
    simpa only [Subgroup.coe_mul, Units.val_mul, hd, tsd3_mat] using this
  obtain ⟨hgb, -, -, hgdet⟩ := tscentralizer_facts hK ζ
    ((g : StatedSU 4 r K).2) hgcomm
  obtain ⟨hhb, -, -, hhdet⟩ := tscentralizer_facts hK ζ
    ((h : StatedSU 4 r K).2) hhcomm
  have hbot : tsbotRight ((g : StatedSU 4 r K) : GL (Fin 4) K) =
      tsbotRight ((h : StatedSU 4 r K) : GL (Fin 4) K) := by
    have hne : (tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K)).det ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hgdet
      exact zero_ne_one hgdet
    have heq : (tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K)).det *
        tsbotRight ((g : StatedSU 4 r K) : GL (Fin 4) K) =
        (tstopLeft ((g : StatedSU 4 r K) : GL (Fin 4) K)).det *
          tsbotRight ((h : StatedSU 4 r K) : GL (Fin 4) K) := by
      rw [hgdet, htop]
      exact hhdet.symm
    exact mul_left_cancel₀ hne heq
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [hgb, hhb, htop, hbot]

end Cent3Bij





private theorem tstblk3GL_det {F : Type} [Field F] (A : GL (Fin 3) F) (c : Fˣ) :
    ((tstblk3GL A c : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).det =
      (A : Matrix (Fin 3) (Fin 3) F).det * (c : F) := by
  rw [tstblk3GL_coe, tstblk3_det]

private theorem tstopLeft_tstblk3GL {F : Type} [Field F] (A : GL (Fin 3) F) (c : Fˣ) :
    tstopLeft (tstblk3GL A c) = (A : Matrix (Fin 3) (Fin 3) F) := by
  unfold tstopLeft
  rw [tstblk3GL_coe]
  exact tstopLeft_tstblk3 (A : Matrix (Fin 3) (Fin 3) F) (c : F)

section Cent3Surj

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)

private theorem tsdet_unitary {M : GL (Fin 3) K} (hM : M ∈ uniGL (unitaryInvolution K r 1) 3) :
    (unitaryInvolution K r 1) ((GeneralLinearGroup.det M : Kˣ) : K) *
      ((GeneralLinearGroup.det M : Kˣ) : K) = 1 := by
  have h := (mem_uniGL (unitaryInvolution K r 1) (A := M)).mp hM
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at hd
  have hc : (conjTr (unitaryInvolution K r 1) (M : Matrix (Fin 3) (Fin 3) K)).det =
      (unitaryInvolution K r 1) ((M : Matrix (Fin 3) (Fin 3) K).det) := by
    rw [conjTr, Matrix.det_transpose]
    exact ((unitaryInvolution K r 1).toRingHom.map_det (M : Matrix (Fin 3) (Fin 3) K)).symm
  rw [hc, ← GeneralLinearGroup.val_det_apply] at hd
  exact hd

private theorem tstblk3GL_mem_SUid {M : GL (Fin 3) K} (hM : M ∈ uniGL (unitaryInvolution K r 1) 3) :
    tstblk3GL M ((GeneralLinearGroup.det M)⁻¹) ∈ SUid (unitaryInvolution K r 1) 4 := by
  have hdetM := tsdet_unitary (r := r) hM
  have hdetc : (unitaryInvolution K r 1) (((GeneralLinearGroup.det M)⁻¹ : Kˣ) : K) *
      (((GeneralLinearGroup.det M)⁻¹ : Kˣ) : K) = 1 := by
    have hcomm : ((GeneralLinearGroup.det M : Kˣ) : K) *
        (unitaryInvolution K r 1) ((GeneralLinearGroup.det M : Kˣ) : K) = 1 := by
      rw [mul_comm]
      exact hdetM
    rw [Units.val_inv_eq_inv_val, map_inv₀, ← mul_inv, hdetM, inv_one]
  refine mem_SUid.mpr ⟨?_, ?_⟩
  · rw [tstblk3GL_det, ← GeneralLinearGroup.val_det_apply]
    exact Units.mul_inv _
  · have hM' : ((M : Matrix (Fin 3) (Fin 3) K).map (unitaryInvolution K r 1))ᵀ *
        (M : Matrix (Fin 3) (Fin 3) K) = 1 :=
      (mem_uniGL (unitaryInvolution K r 1) (A := M)).mp hM
    rw [tstblk3GL_coe, tstblk3_conjTr, tstblk3_mul, hM', hdetc]
    exact (tstblk3_one).symm

private theorem tsproj_surjective {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    Function.Surjective (tsproj hK ζ hd) := by
  intro M
  let c : Kˣ := (GeneralLinearGroup.det (M : GL (Fin 3) K))⁻¹
  have hmem : tstblk3GL (M : GL (Fin 3) K) c ∈ StatedSU 4 r K := by
    rw [tsH_eq hK]
    exact tstblk3GL_mem_SUid (M := (M : GL (Fin 3) K)) M.2
  have hcommM : ((tstblk3GL (M : GL (Fin 3) K) c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
        ((tstblk3GL (M : GL (Fin 3) K) c : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
    rw [tstblk3GL_coe]
    exact tstblk3_comm ((M : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (c : K) (ζ.ω : K)
  refine ⟨⟨⟨tstblk3GL (M : GL (Fin 3) K) c, hmem⟩, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hd, tsd3_mat]
    exact hcommM
  · apply Subtype.ext
    apply Units.ext
    rw [tsproj_coe, tstopLeft_tstblk3GL]

end Cent3Surj





section Cent3Card

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2)

private theorem tsudata (hK : Nat.card K = r ^ 2) : UnitaryFieldData r 1 K :=
  ⟨Fact.out, le_refl 1, by simpa using hK⟩

private theorem tsprod_Icc_one_three (Q : ℤ) :
    ∏ i ∈ Finset.Icc 1 3, (Q ^ i - (-1) ^ i) = (Q + 1) * (Q ^ 2 - 1) * (Q ^ 3 + 1) := by
  have e : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [e]
  simp
  ring

private theorem tscard_uniGL3 (hK : Nat.card K = r ^ 2) :
    Nat.card (uniGL (unitaryInvolution K r 1) 3) =
      r ^ 3 * ((r + 1) * (r ^ 2 - 1) * (r ^ 3 + 1)) := by
  have hZ := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_uniGL_int
    (h := tsudata hK) (n := 3) (by norm_num)
  rw [tsprod_Icc_one_three, show 3 * (3 - 1) / 2 = 3 by norm_num, pow_one] at hZ
  have hP : (((r + 1) * (r ^ 2 - 1) * (r ^ 3 + 1) : ℕ) : ℤ) =
      ((r : ℤ) + 1) * ((r : ℤ) ^ 2 - 1) * ((r : ℤ) ^ 3 + 1) := by
    have hr2 : 1 ≤ r ^ 2 := by nlinarith [(Fact.out : Nat.Prime r).two_le]
    push_cast [Nat.cast_sub hr2]
    ring
  apply Nat.cast_injective (R := ℤ)
  rw [hZ, Nat.cast_mul, Nat.cast_pow, hP]

end Cent3Card





section Cent3Fact

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2)

private theorem tsnot_dvd_r_add_one : ¬ r ∣ r + 1 := by
  intro h
  have h' : r ∣ 1 := by
    have hd := Nat.dvd_sub h (dvd_refl r)
    rwa [Nat.add_sub_cancel_left] at hd
  exact (Fact.out : Nat.Prime r).one_lt.ne' (Nat.dvd_one.mp h')

private theorem tsnot_dvd_r_sq_sub_one : ¬ r ∣ r ^ 2 - 1 := by
  intro h
  have h3 : r ∣ r ^ 2 := dvd_pow_self r (by norm_num)
  have h' : r ∣ 1 := by
    have hd := Nat.dvd_sub h3 h
    have he : r ^ 2 - (r ^ 2 - 1) = 1 := by
      have : 1 ≤ r ^ 2 := by nlinarith [(Fact.out : Nat.Prime r).two_le]
      omega
    rwa [he] at hd
  exact (Fact.out : Nat.Prime r).one_lt.ne' (Nat.dvd_one.mp h')

private theorem tsnot_dvd_r_cu_add_one : ¬ r ∣ r ^ 3 + 1 := by
  intro h
  have h3 : r ∣ r ^ 3 := dvd_pow_self r (by norm_num)
  have h' : r ∣ 1 := by
    have hd := Nat.dvd_sub h h3
    rwa [Nat.add_sub_cancel_left] at hd
  exact (Fact.out : Nat.Prime r).one_lt.ne' (Nat.dvd_one.mp h')

private theorem tsfact (hK : Nat.card K = r ^ 2) :
    (Nat.card (uniGL (unitaryInvolution K r 1) 3)).factorization r = 3 := by
  have hr : 1 < r := (Fact.out : Nat.Prime r).one_lt
  rw [tscard_uniGL3 hK]
  have hrP : ¬ r ∣ (r + 1) * (r ^ 2 - 1) * (r ^ 3 + 1) := by
    intro h
    rcases (Fact.out : Nat.Prime r).dvd_mul.mp h with h1 | h1
    · rcases (Fact.out : Nat.Prime r).dvd_mul.mp h1 with h2 | h2
      · exact tsnot_dvd_r_add_one h2
      · exact tsnot_dvd_r_sq_sub_one h2
    · exact tsnot_dvd_r_cu_add_one h1
  rw [Nat.factorization_mul (by positivity : r ^ 3 ≠ 0)
    (by
      have h2 : 0 < r ^ 2 - 1 := Nat.sub_pos_of_lt (by nlinarith [hr])
      positivity)]
  rw [Finsupp.add_apply, Nat.factorization_pow_self Fact.out,
    Nat.factorization_eq_zero_of_not_dvd hrP, add_zero]

end Cent3Fact





section Cent3Final

variable {r : ℕ} [Fact r.Prime] [CharP K r] (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)

private theorem tscent3_card (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)
    (d : StatedSU 4 r K) (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) =
      Nat.card (uniGL (unitaryInvolution K r 1) 3) :=
  Nat.card_congr (Equiv.ofBijective _
    ⟨tsproj_injective hK ζ hd, tsproj_surjective hK ζ hd⟩)

end Cent3Final

section Cent3Rank

variable {r : ℕ} [Fact r.Prime] [CharP K r]

private theorem tscomm_of_mem (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)
    {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ)
    (g : Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) :
    (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] =
      Matrix.diagonal ![(ζ.ω : K), (ζ.ω : K), (ζ.ω : K), (1 : K)] *
        (((g : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have hc : (g : StatedSU 4 r K) * d = d * (g : StatedSU 4 r K) :=
    Subgroup.mem_centralizer_singleton_iff.mp
      (g.2 : (g : StatedSU 4 r K) ∈ Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))
  have := congrArg (fun x : StatedSU 4 r K =>
    ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) hc
  simpa only [Subgroup.coe_mul, Units.val_mul, hd, tsd3_mat] using this

private theorem tstopLeft_mul_blk {g h : GL (Fin 4) K}
    {A A' : Matrix (Fin 3) (Fin 3) K} {c c' : K}
    (hg : (g : Matrix (Fin 4) (Fin 4) K) = tstblk3 A c)
    (hh : (h : Matrix (Fin 4) (Fin 4) K) = tstblk3 A' c') :
    tstopLeft (g * h) = tstopLeft g * tstopLeft h := by
  have hgA : tstopLeft g = A := by rw [tstopLeft, hg]; exact tstopLeft_tstblk3 A c
  have hhA : tstopLeft h = A' := by rw [tstopLeft, hh]; exact tstopLeft_tstblk3 A' c'
  rw [tstopLeft, Units.val_mul, hg, hh, tstblk3_mul, tstopLeft_tstblk3, hgA, hhA]

private noncomputable def tsprojHom (hK : Nat.card K = r ^ 2) (ζ : CubeRoot K)
    {d : StatedSU 4 r K} (hd : (d : GL (Fin 4) K) = d₃ ζ) :
    (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) →*
      uniGL (unitaryInvolution K r 1) 3 where
  toFun := tsproj hK ζ hd
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [tsproj_coe, tstopLeft]
    ext i j
    simp [Matrix.submatrix, Matrix.one_apply]
  map_mul' g h := by
    apply Subtype.ext
    apply Units.ext
    have hcoe : (((g * h : Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) :
        StatedSU 4 r K) : GL (Fin 4) K) =
        ((g : StatedSU 4 r K) : GL (Fin 4) K) * ((h : StatedSU 4 r K) : GL (Fin 4) K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rw [tsproj_coe, hcoe]
    rw [tstopLeft_mul_blk
      (tscentralizer_facts hK ζ (g : StatedSU 4 r K).2 (tscomm_of_mem hK ζ hd g)).1
      (tscentralizer_facts hK ζ (h : StatedSU 4 r K).2 (tscomm_of_mem hK ζ hd h)).1]
    rw [Subgroup.coe_mul, Units.val_mul, tsproj_coe, tsproj_coe]

private theorem tsSU3_eq (hK : Nat.card K = r ^ 2) :
    StatedSU 3 r K = SUid (unitaryInvolution K r 1) 3 := by
  rw [SUid_eq_statedSU (p := r) (f := 1) (by simpa using hK) 3]
  simp

private theorem tscard_scalars_SU3 (hK : Nat.card K = r ^ 2) :
    Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 r K)) =
      Nat.gcd 3 (r + 1) := by
  have h1 : (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 (r ^ 1) K) =
      CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars (tsudata hK) 3 :=
    (CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq (tsudata hK) (by norm_num)).symm
  rw [show StatedSU 3 r K = StatedSU 3 (r ^ 1) K from by rw [pow_one], h1,
    CFSG.ClassicalGroups.UnitaryFlag.card_unitaryScalars (tsudata hK) (n := 3) (by norm_num),
    pow_one]

private theorem tsnot_dvd_scalars (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    ¬ r ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 r K)) := by
  rw [tscard_scalars_SU3 hK]
  intro h
  have h1 : r ≤ Nat.gcd 3 (r + 1) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by norm_num)) h
  have h2 : Nat.gcd 3 (r + 1) ≤ 3 :=
    Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 (r + 1))
  omega

private theorem tspRank_statedSU3_le (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU 3 r K)) ≤ 2 := by
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  set N : Subgroup ↥(StatedSU 3 r K) :=
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 r K) with hNdef
  have hproj : CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSU 3 r K))) ≤ 2 := by
    have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291DC.pRank_le_two_statedSU_three_prime
      (p := r) (K := K) (by omega) (by simpa using hF)
      (MulEquiv.refl (StatedProj (StatedSU 3 (r ^ 1) K)))
    rwa [show r ^ 1 = r from pow_one r] at h
  have hN : ¬ r ∣ Nat.card N := by
    rw [hNdef]
    exact tsnot_dvd_scalars hK h5
  rw [← CFSG.SectionRank.pRank_quotient_eq (p := r) N hN]
  exact hproj

private theorem tspRank_statedSU3_lower (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥(StatedSU 3 r K)) := by
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  set N : Subgroup ↥(StatedSU 3 r K) :=
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 r K) with hNdef
  have hproj : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSU 3 r K))) := by
    have h := CFSG.SectionRank.ClassicalOdd.two_mul_le_pRank_SU_three (K := K) (p := r) (f := 1)
      (by omega) (by simpa using hF)
    rw [show r ^ 1 = r from pow_one r] at h
    simpa only [mul_one] using h
  have hN : ¬ r ∣ Nat.card N := by
    rw [hNdef]
    exact tsnot_dvd_scalars hK h5
  rw [← CFSG.SectionRank.pRank_quotient_eq (p := r) N hN]
  exact hproj

private theorem tsOpenPRank_eq_top {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    CFSG.Open.pRank r H = CFSG.Open.pRank r (⊤ : Subgroup H) :=
  CFSG.SectionRank.pRank_eq_pRank_top_subgroup H

private theorem tspRank_SUid3_le (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(SUid (unitaryInvolution K r 1) 3)) ≤ 2 := by
  rw [← tsSU3_eq hK]
  exact tspRank_statedSU3_le hK h5

private theorem tspRank_SUid3_lower (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥(SUid (unitaryInvolution K r 1) 3)) := by
  rw [← tsSU3_eq hK]
  exact tspRank_statedSU3_lower hK h5

private theorem tsSUid_le_uniGL :
    SUid (unitaryInvolution K r 1) 3 ≤ uniGL (unitaryInvolution K r 1) 3 := by
  intro A hA
  rw [mem_uniGL]
  exact (mem_SUid.mp hA).2

private theorem tspRank_uniGL_le (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    CFSG.Open.pRank r (⊤ : Subgroup ↥(uniGL (unitaryInvolution K r 1) 3)) ≤ 2 := by
  have hSU : CFSG.Open.pRank r (⊤ : Subgroup ↥(SUid (unitaryInvolution K r 1) 3)) ≤ 2 :=
    tspRank_SUid3_le hK h5
  have hSU' : CFSG.Open.pRank r
      ((SUid (unitaryInvolution K r 1) 3).subgroupOf (uniGL (unitaryInvolution K r 1) 3)) ≤ 2 := by
    rw [tsOpenPRank_eq_top]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : Nat.Prime r).one_lt
      (Subgroup.subgroupOfEquivOfLe tsSUid_le_uniGL)]
    exact hSU
  refine CFSG.SectionRank.pRank_le (Fact.out : Nat.Prime r).one_lt ?_
  intro E hE hEa
  have hEsu : E ≤ (SUid (unitaryInvolution K r 1) 3).subgroupOf
      (uniGL (unitaryInvolution K r 1) 3) := by
    intro g hg
    rw [Subgroup.mem_subgroupOf, mem_SUid]
    refine ⟨?_, g.2⟩
    have hgr : (g : GL (Fin 3) K) ^ r = 1 := by
      have := congrArg (fun x : ↥(uniGL (unitaryInvolution K r 1) 3) =>
        (x : GL (Fin 3) K)) (hEa.2 g hg)
      simpa using this
    have h1 : (GeneralLinearGroup.det (g : GL (Fin 3) K)) ^ r = 1 := by
      rw [← map_pow, hgr, map_one]
    have h2 : orderOf (GeneralLinearGroup.det (g : GL (Fin 3) K)) ∣ r :=
      orderOf_dvd_iff_pow_eq_one.mpr h1
    have h3 : orderOf (GeneralLinearGroup.det (g : GL (Fin 3) K)) ∣ Nat.card Kˣ :=
      orderOf_dvd_iff_pow_eq_one.mpr (pow_card_eq_one' (x := GeneralLinearGroup.det _))
    have hcop : Nat.Coprime r (Nat.card Kˣ) := by
      rw [Nat.card_units, hK]
      exact ((Fact.out : Nat.Prime r).coprime_iff_not_dvd).mpr tsnot_dvd_r_sq_sub_one
    have h4 : orderOf (GeneralLinearGroup.det (g : GL (Fin 3) K)) ∣ Nat.gcd r (Nat.card Kˣ) :=
      Nat.dvd_gcd h2 h3
    rw [show Nat.gcd r (Nat.card Kˣ) = 1 from hcop] at h4
    have h5 : orderOf (GeneralLinearGroup.det (g : GL (Fin 3) K)) = 1 := Nat.dvd_one.mp h4
    have h6 : GeneralLinearGroup.det (g : GL (Fin 3) K) = 1 := orderOf_eq_one_iff.mp h5
    rw [← GeneralLinearGroup.val_det_apply, h6, Units.val_one]
  have hEpg : IsPGroup r E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hEa.2 g g.2)⟩
  obtain ⟨k, hk⟩ := hEpg.exists_card_eq
  have hk2 : k ≤ 2 :=
    (CFSG.SectionRank.le_pRank (Fact.out : Nat.Prime r).one_lt hEsu hEa hk).trans hSU'
  rw [hk]
  exact Nat.pow_le_pow_right (Fact.out : Nat.Prime r).pos hk2

private theorem tspRank_uniGL_lower (hK : Nat.card K = r ^ 2) (h5 : 5 ≤ r) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup ↥(uniGL (unitaryInvolution K r 1) 3)) := by
  have h1 : 2 ≤ CFSG.Open.pRank r (SUid (unitaryInvolution K r 1) 3) := by
    rw [tsOpenPRank_eq_top]
    exact tspRank_SUid3_lower hK h5
  rw [← tsOpenPRank_eq_top (uniGL (unitaryInvolution K r 1) 3)]
  exact h1.trans (CFSG.SectionRank.pRank_mono (Fact.out : Nat.Prime r).one_lt tsSUid_le_uniGL)

end Cent3Rank

end Aux

theorem cent3_card_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₃ ζ →
      (Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))).factorization r = 3 := by
  intro d hd
  haveI : Fact r.Prime := ⟨hr⟩
  have udata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K :=
    ⟨hr, le_refl 1, by simpa using hK⟩
  haveI : CharP K r := udata.charP
  rw [Aux.tscent3_card hK ζ d hd]
  exact Aux.tsfact hK

theorem cent3_rank_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₃ ζ →
      CFSG.Open.pRank r (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) = 2 := by
  intro d hd
  haveI : Fact r.Prime := ⟨hr⟩
  have udata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r 1 K :=
    ⟨hr, le_refl 1, by simpa using hK⟩
  haveI : CharP K r := udata.charP
  let C := Subgroup.centralizer ({d} : Set (StatedSU 4 r K))
  have hbij : Function.Bijective (Aux.tsprojHom hK ζ hd) :=
    ⟨Aux.tsproj_injective hK ζ hd, Aux.tsproj_surjective hK ζ hd⟩
  let e : C ≃* CFSG.GH74.L5U5.uniGL (CFSG.LieType.BorelTits.unitaryInvolution K r 1) 3 :=
    MulEquiv.ofBijective (Aux.tsprojHom hK ζ hd) hbij
  have hp : CFSG.Open.pRank r C =
      CFSG.Open.pRank r (CFSG.GH74.L5U5.uniGL
        (CFSG.LieType.BorelTits.unitaryInvolution K r 1) 3) := by
    rw [Aux.tsOpenPRank_eq_top C,
      Aux.tsOpenPRank_eq_top (CFSG.GH74.L5U5.uniGL
        (CFSG.LieType.BorelTits.unitaryInvolution K r 1) 3)]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e
  rw [hp, Aux.tsOpenPRank_eq_top (CFSG.GH74.L5U5.uniGL
    (CFSG.LieType.BorelTits.unitaryInvolution K r 1) 3)]
  exact le_antisymm (Aux.tspRank_uniGL_le hK h5) (Aux.tspRank_uniGL_lower hK h5)

private lemma cent4_diag_comm {A B : GL (Fin 4) K}
    (hA : ((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag)
    (hB : ((B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag) : A * B = B * A := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, ← hA.diagonal_diag, ← hB.diagonal_diag,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

private lemma cent4_omega {r : ℕ} (h3 : r % 3 = 2) (ζ : CubeRoot K) :
    (ζ.ω : K) ^ (r + 1) = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, r + 1 = 3 * m := by
    refine ⟨r / 3 + 1, ?_⟩
    have := Nat.mod_add_div r 3
    omega
  have hu : ζ.ω ^ (r + 1) = 1 := by rw [hm, pow_mul, ζ.pow_three, one_pow]
  have := congrArg (fun u : Kˣ => (u : K)) hu
  simpa using this

private lemma cent4_centralizer_eq_torus {r : ℕ} [Fact r.Prime] [CharP K r] (ζ : CubeRoot K)
    (hD : D₀ ζ ≤ StatedSU 4 r K)
    (hSU : StatedSU 4 r K = SUid (unitaryInvolution K r 1) 4) :
    Subgroup.centralizer
        (((D₀ ζ).subgroupOf (StatedSU 4 r K) : Subgroup (StatedSU 4 r K)) :
          Set (StatedSU 4 r K)) =
      (CFSG.ClassicalInvolution.Phan.torus (unitaryInvolution K r 1) 4).map
        ((MulEquiv.subgroupCongr hSU.symm : SUid (unitaryInvolution K r 1) 4 ≃*
          StatedSU 4 r K) : SUid (unitaryInvolution K r 1) 4 →* StatedSU 4 r K) := by
  let e : SUid (unitaryInvolution K r 1) 4 ≃* StatedSU 4 r K := MulEquiv.subgroupCongr hSU.symm
  have he : ∀ x : SUid (unitaryInvolution K r 1) 4, (e x : GL (Fin 4) K) = x :=
    fun x => MulEquiv.subgroupCongr_apply hSU.symm x
  have hee : ∀ x : StatedSU 4 r K, (e.symm x : GL (Fin 4) K) = x :=
    fun x => MulEquiv.subgroupCongr_symm_apply hSU.symm x
  ext g
  rw [Subgroup.mem_map]
  constructor
  · intro hg
    refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
    rw [CFSG.ClassicalInvolution.Phan.mem_torus_iff]
    intro a b hab
    have hdiag := centralizer_D₀_comm_diag ζ hD hg
    show ((e.symm g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) a b = 0
    rw [hee g]
    exact hdiag hab
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine Subtype.ext ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    refine cent4_diag_comm ?_ ?_
    · exact monomial_of_normalizes_diag ζ (Subgroup.mem_subgroupOf.mp hy)
    · show (((e x : StatedSU 4 r K) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).IsDiag
      rw [he x]
      exact (CFSG.ClassicalInvolution.Phan.mem_torus_iff x).mp hx

private lemma cent4_factorization {r : ℕ} (hr : r.Prime) (h3 : r % 3 = 2) :
    ((r + 1) ^ 3).factorization 3 =
      ((r + 1) * (r * ((r + 1) * (r ^ 2 - 1)))).factorization 3 := by
  have hsub : r ^ 2 - 1 = (r - 1) * (r + 1) := by
    have h1 : 1 ≤ r ^ 2 := by nlinarith [hr.two_le]
    have h2 : 1 ≤ r := hr.one_le
    have h4 : r = (r - 1) + 1 := (Nat.sub_add_cancel h2).symm
    rw [Nat.sub_eq_iff_eq_add h1]
    nlinarith [h4]
  have hX : (r + 1) * (r * ((r + 1) * (r ^ 2 - 1))) = (r + 1)^3 * (r * (r - 1)) := by
    rw [hsub]; ring
  rw [hX, Nat.factorization_mul (pow_ne_zero 3 (by positivity))
    (mul_ne_zero hr.ne_zero (by omega : r - 1 ≠ 0))]
  rw [Finsupp.add_apply]
  have hzero : (r * (r - 1)).factorization 3 = 0 := by
    rw [Nat.factorization_mul hr.ne_zero (by omega : r - 1 ≠ 0)]
    rw [Finsupp.add_apply]
    have hnr : ¬ 3 ∣ r := by
      intro h
      have := Nat.dvd_iff_mod_eq_zero.mp h
      omega
    have hnr1 : ¬ 3 ∣ r - 1 := by
      intro h
      have hmod : (r - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
      have hr1 : (r - 1) % 3 = 1 := by omega
      omega
    rw [Nat.factorization_eq_zero_of_not_dvd hnr,
      Nat.factorization_eq_zero_of_not_dvd hnr1, add_zero]
  rw [hzero, add_zero]

theorem cent4_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2) (h3 : r % 3 = 2)
    (ζ : CubeRoot K) :
    ∀ d : StatedSU 4 r K, (d : GL (Fin 4) K) = d₂ ζ →
      (Nat.card (Subgroup.centralizer
        (((D₀ ζ).subgroupOf (StatedSU 4 r K) : Subgroup (StatedSU 4 r K)) :
          Set (StatedSU 4 r K)))).factorization 3 =
        (Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K)))).factorization 3 := by
  intro d hd
  haveI : Fact r.Prime := ⟨hr⟩
  have hUF : UnitaryFieldData r 1 K := ⟨hr, le_refl 1, by simpa using hK⟩
  letI : CharP K r := hUF.charP
  have hF : Nat.card K = (r ^ 1) ^ 2 := by simpa using hK
  have hD : D₀ ζ ≤ StatedSU 4 r K := d₀_le_su hr hK h3 ζ
  have hSU : StatedSU 4 r K = SUid (unitaryInvolution K r 1) 4 :=
    ((SUid_eq_statedSU (F := K) (p := r) (f := 1) hF 4).trans (by rw [pow_one])).symm
  have hCLeq : Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSU 4 r K) : Subgroup (StatedSU 4 r K)) :
        Set (StatedSU 4 r K)) =
      (CFSG.ClassicalInvolution.Phan.torus (unitaryInvolution K r 1) 4).map
        ((MulEquiv.subgroupCongr hSU.symm : SUid (unitaryInvolution K r 1) 4 ≃*
          StatedSU 4 r K) : SUid (unitaryInvolution K r 1) 4 →* StatedSU 4 r K) :=
    cent4_centralizer_eq_torus ζ hD hSU
  have hL : Nat.card (Subgroup.centralizer
      (((D₀ ζ).subgroupOf (StatedSU 4 r K) : Subgroup (StatedSU 4 r K)) :
        Set (StatedSU 4 r K))) = (r + 1) ^ 3 := by
    rw [hCLeq, Subgroup.card_map_of_injective
      (MulEquiv.subgroupCongr hSU.symm).injective]
    have hcard := CFSG.ClassicalInvolution.Phan.card_torus (p := r) (f := 1) hF 3
    simpa [pow_one] using hcard
  have hcen : Subgroup.centralizer ({d} : Set (StatedSU 4 r K)) = cent2C (r := r) ζ := by
    ext g
    rw [Subgroup.mem_centralizer_singleton_iff, mem_cent2C]
    rw [Subtype.ext_iff]
    simp only [Subgroup.coe_mul]
    rw [hd]
  have hR : Nat.card (Subgroup.centralizer ({d} : Set (StatedSU 4 r K))) =
      (r + 1) * (r * ((r + 1) * (r ^ 2 - 1))) := by
    rw [hcen, cent2_card_C hr hK ζ hUF, cent2_U2_card hr h5 hK]
  rw [hL, hR]
  exact cent4_factorization hr h3

theorem centFact_su {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    (h3 : r % 3 = 2) (ζ : CubeRoot K) : CentFact (StatedSU 4 r K) ζ r :=
  ⟨fun d hd => ⟨cent1_card_su hr h5 hK ζ d hd, cent1_rank_su hr h5 hK ζ d hd⟩,
    cent2_card_su hr h5 hK ζ,
    fun d hd => ⟨cent3_card_su hr h5 hK ζ d hd, cent3_rank_su hr h5 hK ζ d hd⟩,
    cent4_su hr h5 hK h3 ζ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
