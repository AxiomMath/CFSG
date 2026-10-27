module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubflag
public import CFSG.LocalAnalysis.QuasithinUnique.SteinbergCHBinaryFlagBlocks

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open Matrix Module CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.SteinbergCH

variable {K : Type*} [Field K] {n : ℕ}

theorem mem_dotOrth_flagSpace {c : ℕ} {f : Fin n → K} :
    f ∈ dotOrth (flagSpace n K c) ↔ ∀ j : Fin n, (j : ℕ) < c → f j = 0 := by
  rw [mem_dotOrth]
  constructor
  · intro h j hj
    have hv : (Pi.single j 1 : Fin n → K) ∈ flagSpace n K c :=
      mem_flagSpace.2 fun i hi => Pi.single_eq_of_ne (fun h => by subst h; omega) _
    simpa using h _ hv
  · intro h v hv
    show ∑ j, f j * v j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : (j : ℕ) < c
    · rw [h j hj, zero_mul]
    · rw [mem_flagSpace.1 hv j (not_lt.1 hj), mul_zero]

@[expose] noncomputable def rankOneElem (w f : Fin n → K) (h : f ⬝ᵥ w = 0) :
    SpecialLinearGroup (Fin n) K :=
  ⟨1 + vecMulVec w f, by
    rw [vecMulVec_eq Unit, det_one_add_replicateCol_mul_replicateRow, h, add_zero]⟩

theorem coe_rankOneElem (w f : Fin n → K) (h : f ⬝ᵥ w = 0) :
    ((rankOneElem w f h : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 + vecMulVec w f :=
  rfl

theorem mul_eq_zero_of_le {c : ℕ} {w f : Fin n → K} (hw : w ∈ flagSpace n K c)
    (hf : f ∈ dotOrth (flagSpace n K c)) {i j : Fin n} (hji : (j : ℕ) ≤ i) : w i * f j = 0 := by
  by_cases hi : (i : ℕ) < c
  · rw [mem_dotOrth_flagSpace.1 hf j (by omega), mul_zero]
  · rw [mem_flagSpace.1 hw i (not_lt.1 hi), zero_mul]

theorem rankOneElem_mem_blockRadical {I : Set ℕ} {c : ℕ} (hc : c ∈ I) {w f : Fin n → K}
    (hw : w ∈ flagSpace n K c) (hf : f ∈ dotOrth (flagSpace n K c)) (h : f ⬝ᵥ w = 0) :
    rankOneElem w f h ∈ blockRadical n K I := by
  have hU : rankOneElem w f h ∈ unitriangular n K := by
    refine ⟨fun i j hji => ?_, fun i => ?_⟩
    · rw [coe_rankOneElem, Matrix.add_apply, one_apply_ne (ne_of_gt hji), vecMulVec_apply,
        mul_eq_zero_of_le hw hf (le_of_lt (Fin.lt_def.1 hji)), add_zero]
    · rw [coe_rankOneElem, Matrix.add_apply, one_apply_eq, vecMulVec_apply,
        mul_eq_zero_of_le hw hf le_rfl, add_zero]
  refine ⟨upperTriangular_le_flagStabilizer I (unitriangular_le_upperTriangular n K hU),
    fun i j hij => ?_⟩
  rw [coe_rankOneElem, Matrix.add_apply, vecMulVec_apply]
  suffices hwf : w i * f j = 0 by rw [hwf, add_zero]
  by_cases hi : (i : ℕ) < c
  · by_cases hj : (j : ℕ) < c
    · rw [mem_dotOrth_flagSpace.1 hf j hj, mul_zero]
    · exact absurd ((hij c hc).2 (not_lt.1 hj)) (by omega)
  · rw [mem_flagSpace.1 hw i (not_lt.1 hi), zero_mul]

theorem mul_rankOne_mul_apply (X Y : Matrix (Fin n) (Fin n) K) (w f : Fin n → K) (i j : Fin n) :
    (X * (1 + vecMulVec w f) * Y) i j = (X * Y) i j + (X *ᵥ w) i * (f ᵥ* Y) j := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_apply]
  congr 1
  simp only [Matrix.mul_apply, vecMulVec_apply, mulVec, vecMul, dotProduct, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem exists_entry_ne_zero {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K} (hYX : Y * X = 1)
    (hX : (flagSpace n K c).map (mulVecLin X) ≠ flagSpace n K c) :
    ∃ w ∈ flagSpace n K c, ∃ f ∈ dotOrth (flagSpace n K c), ∃ i j : Fin n, (j : ℕ) ≤ i ∧
      (X *ᵥ w) i * (f ᵥ* Y) j ≠ 0 := by
  classical
  obtain ⟨w, hw, hxw⟩ : ∃ w ∈ flagSpace n K c, X *ᵥ w ∉ flagSpace n K c := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective (mulVecLin X) := fun v v' hvv' => by
      have h1 := congrArg (fun u => Y *ᵥ u) hvv'
      simpa [mulVec_mulVec, hYX] using h1
    refine hX (Submodule.eq_of_le_of_finrank_eq ?_ ?_)
    · rintro _ ⟨v, hv, rfl⟩
      exact hall v hv
    · exact (LinearEquiv.finrank_eq
        (Submodule.equivMapOfInjective (mulVecLin X) hinj (flagSpace n K c))).symm
  obtain ⟨i₀, hi₀c, hi₀⟩ : ∃ i₀ : Fin n, c ≤ (i₀ : ℕ) ∧ (X *ᵥ w) i₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hxw (mem_flagSpace.2 h')
  have hcn : c + 1 ≤ n := by omega
  obtain ⟨f, hf, hfY⟩ : ∃ f ∈ dotOrth (flagSpace n K c),
      f ᵥ* Y ∉ dotOrth (flagSpace n K (c + 1)) := by
    by_contra hall
    push Not at hall
    have hinj : Function.Injective (vecMulLinear Y) := fun v v' hvv' => by
      have h1 := congrArg (fun u => u ᵥ* X) hvv'
      simpa [vecMul_vecMul, hYX] using h1
    have hle : (dotOrth (flagSpace n K c)).map (vecMulLinear Y) ≤
        dotOrth (flagSpace n K (c + 1)) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hall v hv
    have h1 := Submodule.finrank_mono hle
    rw [← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (vecMulLinear Y) hinj _),
      finrank_dotOrth, finrank_dotOrth, finrank_flagSpace (by omega),
      finrank_flagSpace hcn] at h1
    omega
  obtain ⟨j, hjc, hj⟩ : ∃ j : Fin n, (j : ℕ) < c + 1 ∧ (f ᵥ* Y) j ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hfY (mem_dotOrth_flagSpace.2 h')
  exact ⟨w, hw, f, hf, i₀, j, by omega, mul_ne_zero hi₀ hj⟩

theorem mem_stabilizer_of_conj_le {I : Set ℕ} {c : ℕ} (hc : c ∈ I)
    {x : SpecialLinearGroup (Fin n) K}
    (h : ∀ r ∈ blockRadical n K I, x * r * x⁻¹ ∈ unitriangular n K) :
    x ∈ stabilizer (flagSpace n K c) := by
  have hXY : (↑x : Matrix (Fin n) (Fin n) K) *
      (↑(x⁻¹) : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hYX : (↑(x⁻¹) : Matrix (Fin n) (Fin n) K) *
      (↑x : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  by_contra hx
  obtain ⟨w, hw, f, hf, i, j, hji, hne⟩ := exists_entry_ne_zero hYX hx
  have hfw : f ⬝ᵥ w = 0 := mem_dotOrth.1 hf w hw
  have hr := h _ (rankOneElem_mem_blockRadical hc hw hf hfw)
  have hentry : (↑(x * rankOneElem w f hfw * x⁻¹) : Matrix (Fin n) (Fin n) K) i j =
      (1 : Matrix (Fin n) (Fin n) K) i j +
        ((↑x : Matrix (Fin n) (Fin n) K) *ᵥ w) i *
          (f ᵥ* (↑(x⁻¹) : Matrix (Fin n) (Fin n) K)) j := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rankOneElem,
      mul_rankOne_mul_apply, hXY]
  rcases Nat.lt_or_ge (j : ℕ) i with hlt | hge
  · have h0 := hr.1 i j (Fin.lt_def.2 hlt)
    rw [hentry, one_apply_ne (ne_of_gt (Fin.lt_def.2 hlt)), zero_add] at h0
    exact hne h0
  · have hji' : j = i := Fin.ext (by omega)
    subst hji'
    have h1 := hr.2 j
    rw [hentry, one_apply_eq, add_eq_left] at h1
    exact hne h1

theorem mem_flagStabilizer_of_conj_le {I : Set ℕ} {x : SpecialLinearGroup (Fin n) K}
    (h : ∀ r ∈ blockRadical n K I, x * r * x⁻¹ ∈ unitriangular n K) :
    x ∈ flagStabilizer n K I :=
  mem_flagStabilizer.2 fun _ hc => mem_stabilizer_of_conj_le hc h

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
