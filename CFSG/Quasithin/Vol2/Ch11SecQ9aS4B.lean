module

public import CFSG.Quasithin.Vol2.Ch11SecQ9aS4A
public import CFSG.Quasithin.Vol2.Ch1Xi

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Open (pCoreOf)

variable {K : Type} [Field K]

@[expose] def uSL2 (K : Type) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem coe_uSL2 : ((uSL2 K : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
    !![1, 1; 0, 1] := rfl

theorem coe_uSL2_inv :
    (((uSL2 K)⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![1, -1; 0, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_uSL2, Matrix.adjugate_fin_two_of]
  simp

theorem blkQ_comm (j : Fin 2) {t x : StatedSp 2 K} (ht : t ∈ Q2 K j) (hx : x ∈ Q2 K j)
    (hc : t * x * t⁻¹ * x⁻¹ ∈ Q2 K j) :
    blkQ j ⟨t * x * t⁻¹ * x⁻¹, hc⟩ = blkQ j ⟨t, ht⟩ * blkQ j ⟨x, hx⟩ *
      blkQ j ⟨t⁻¹, (Q2 K j).inv_mem ht⟩ * blkQ j ⟨x⁻¹, (Q2 K j).inv_mem hx⟩ := by
  rw [← map_mul, ← map_mul, ← map_mul]
  rfl

theorem blkQ_mul_inv (j : Fin 2) {x : StatedSp 2 K} (hx : x ∈ Q2 K j) :
    blkQ j ⟨x, hx⟩ * blkQ j ⟨x⁻¹, (Q2 K j).inv_mem hx⟩ = 1 := by
  rw [← map_mul, ← map_one (blkQ (K := K) j)]
  congr 1
  exact Subtype.ext (mul_inv_cancel x)

theorem blkQ_spLevi (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K) :
    blkQ j ⟨spLevi j A, spLevi_mem j A⟩ = (A : Matrix (Fin 2) (Fin 2) K) := by
  rw [blkQ_apply]
  exact blkIdx_spLevi j A

theorem mem_normalizer_N (j : Fin 2) {t : StatedSp 2 K} (ht : t ∈ Q2 K j) :
    t ∈ Subgroup.normalizer (perfectCore (Q2 K j) : Set (StatedSp 2 K)) :=
  normalizer_le_normalizer_perfectCore (Q2 K j) (Subgroup.le_normalizer ht)

variable [Finite K] [CharP K 2]

theorem mem_pCoreOf_N_iff (hK4 : ∃ s : Finset K, s.card = 4) (j : Fin 2) {c : StatedSp 2 K}
    (hc : c ∈ perfectCore (Q2 K j)) :
    c ∈ pCoreOf 2 (perfectCore (Q2 K j)) ↔ blkQ j ⟨c, perfectCore_le _ hc⟩ = 1 := by
  rw [pCoreOf_N_eq hK4 j]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h1 := congrArg (fun A : SpecialLinearGroup (Fin 2) K => (A : Matrix (Fin 2) (Fin 2) K))
      (MonoidHom.mem_ker.mp hy)
    simp only [blkN_coe] at h1
    rw [blkQ_apply]
    exact h1
  · intro h
    refine ⟨⟨c, hc⟩, MonoidHom.mem_ker.mpr (Subtype.ext ?_), rfl⟩
    show blkIdx (sigma2 j) (spMat c) = 1
    rw [blkQ_apply] at h
    exact h

omit [Finite K] [CharP K 2] in
theorem blkQ_torusHom_inv_zero (t : Fin 2 → Kˣ) (h : (torusHom t)⁻¹ ∈ Q2 K 0) :
    blkQ 0 ⟨(torusHom t)⁻¹, h⟩ = !![(((t 1)⁻¹ : Kˣ) : K), 0; 0, (t 1 : K)] := by
  have e : (⟨(torusHom t)⁻¹, h⟩ : ↥(Q2 K 0)) = ⟨torusHom t⁻¹, torusHom_mem_Q2 0 t⁻¹⟩ :=
    Subtype.ext (map_inv _ _).symm
  rw [e, blkQ_torusHom_zero]
  simp

omit [Finite K] [CharP K 2] in
theorem blkQ_torusHom_inv_one (t : Fin 2 → Kˣ) (h : (torusHom t)⁻¹ ∈ Q2 K 1) :
    blkQ 1 ⟨(torusHom t)⁻¹, h⟩ = !![(((t 0)⁻¹ : Kˣ) : K), 0; 0, (((t 1)⁻¹ : Kˣ) : K)] := by
  have e : (⟨(torusHom t)⁻¹, h⟩ : ↥(Q2 K 1)) = ⟨torusHom t⁻¹, torusHom_mem_Q2 1 t⁻¹⟩ :=
    Subtype.ext (map_inv _ _).symm
  rw [e, blkQ_torusHom_one]
  simp

omit [Finite K] [CharP K 2] in
theorem blkQ_spLevi_inv (j : Fin 2) (A : SpecialLinearGroup (Fin 2) K)
    (h : (spLevi j A)⁻¹ ∈ Q2 K j) :
    blkQ j ⟨(spLevi j A)⁻¹, h⟩ =
      ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) := by
  have e : (⟨(spLevi j A)⁻¹, h⟩ : ↥(Q2 K j)) = ⟨spLevi j A⁻¹, spLevi_mem j A⁻¹⟩ :=
    Subtype.ext (map_inv _ _).symm
  rw [e, blkQ_spLevi]

theorem torusHom_mem_sc0_iff (hK4 : ∃ s : Finset K, s.card = 4) (t : Fin 2 → Kˣ) :
    (torusHom t : StatedSp 2 K) ∈ sectionCentralizer (perfectCore (Q2 K 0))
      (pCoreOf 2 (perfectCore (Q2 K 0))) ↔ t 1 = 1 := by
  have ht := torusHom_mem_Q2 0 t
  have hN := mem_normalizer_N 0 ht
  have hcN : ∀ x ∈ perfectCore (Q2 K 0),
      torusHom t * x * (torusHom t)⁻¹ * x⁻¹ ∈ perfectCore (Q2 K 0) :=
    fun x hx => mul_mem ((Subgroup.mem_normalizer_iff.mp hN x).mp hx) (inv_mem hx)
  constructor
  · rintro ⟨-, -, h⟩
    have hx := spLevi_mem_perfectCore hK4 0 (uSL2 K)
    have h1 := (mem_pCoreOf_N_iff hK4 0 (hcN _ hx)).mp (h _ hx)
    rw [blkQ_comm 0 ht (spLevi_mem 0 _), blkQ_torusHom_zero, blkQ_torusHom_inv_zero, blkQ_spLevi,
      blkQ_spLevi_inv, coe_uSL2, coe_uSL2_inv] at h1
    have e := congrFun₂ h1 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    have h2 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have hb : ((t 1 : K) - 1) ^ 2 = 0 := by linear_combination e - ((t 1 : K) - 1) * h2
    exact Units.ext (by simpa [sub_eq_zero] using pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hb)
  · intro h1
    refine ⟨hN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hN, fun x hx => ?_⟩
    refine (mem_pCoreOf_N_iff hK4 0 (hcN x hx)).mpr ?_
    rw [blkQ_comm 0 ht (perfectCore_le _ hx), blkQ_torusHom_zero, blkQ_torusHom_inv_zero, h1]
    have e : !![((1 : Kˣ) : K), 0; 0, (((1 : Kˣ)⁻¹ : Kˣ) : K)] = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    have e' : !![(((1 : Kˣ)⁻¹ : Kˣ) : K), 0; 0, ((1 : Kˣ) : K)] = 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    rw [e, e', Matrix.one_mul, Matrix.mul_one]
    exact blkQ_mul_inv 0 (perfectCore_le _ hx)

theorem torusHom_mem_sc1_iff (hK4 : ∃ s : Finset K, s.card = 4) (t : Fin 2 → Kˣ) :
    (torusHom t : StatedSp 2 K) ∈ sectionCentralizer (perfectCore (Q2 K 1))
      (pCoreOf 2 (perfectCore (Q2 K 1))) ↔ t 0 = t 1 := by
  have ht := torusHom_mem_Q2 1 t
  have hN := mem_normalizer_N 1 ht
  have hcN : ∀ x ∈ perfectCore (Q2 K 1),
      torusHom t * x * (torusHom t)⁻¹ * x⁻¹ ∈ perfectCore (Q2 K 1) :=
    fun x hx => mul_mem ((Subgroup.mem_normalizer_iff.mp hN x).mp hx) (inv_mem hx)
  constructor
  · rintro ⟨-, -, h⟩
    have hx := spLevi_mem_perfectCore hK4 1 (uSL2 K)
    have h1 := (mem_pCoreOf_N_iff hK4 1 (hcN _ hx)).mp (h _ hx)
    rw [blkQ_comm 1 ht (spLevi_mem 1 _), blkQ_torusHom_one, blkQ_torusHom_inv_one, blkQ_spLevi,
      blkQ_spLevi_inv, coe_uSL2, coe_uSL2_inv] at h1
    have e := congrFun₂ h1 0 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e
    have h0 : (t 1 : K) ≠ 0 := (t 1).ne_zero
    refine Units.ext ?_
    field_simp at e
    linear_combination e
  · intro h1
    refine ⟨hN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hN, fun x hx => ?_⟩
    refine (mem_pCoreOf_N_iff hK4 1 (hcN x hx)).mpr ?_
    rw [blkQ_comm 1 ht (perfectCore_le _ hx), blkQ_torusHom_one, blkQ_torusHom_inv_one, ← h1]
    have e : !![((t 0 : Kˣ) : K), 0; 0, ((t 0 : Kˣ) : K)] = (t 0 : K) • 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    have e' : !![(((t 0)⁻¹ : Kˣ) : K), 0; 0, (((t 0)⁻¹ : Kˣ) : K)] = (((t 0)⁻¹ : Kˣ) : K) • 1 := by
      ext i k
      fin_cases i <;> fin_cases k <;> simp
    rw [e, e']
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
    rw [Units.inv_mul, one_smul]
    exact blkQ_mul_inv 1 (perfectCore_le _ hx)

end CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
