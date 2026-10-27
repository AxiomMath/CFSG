module

public import CFSG.Quasithin.Background.SmithB45HM22Check
public import CFSG.Quasithin.Background.SmithB45HM22Brauer

public section

namespace CFSG.Quasithin.HM22

open CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour
  CFSG.Quasithin.HatM22 CFSG.Quasithin.B45Mat Module
open scoped Kronecker

section Scalars

variable {G : Type*} [Group G] {n m : ℕ}

theorem dualRep_scalar {M : G →* Matrix (Fin n) (Fin n) FieldFour} {g : G} {c : FieldFour}
    (h : M g⁻¹ = c • 1) : dualRep M g = c • 1 := by
  rw [dualRep_apply, h, Matrix.transpose_smul, Matrix.transpose_one]

theorem frobRep_scalar {M : G →* Matrix (Fin n) (Fin n) FieldFour} {g : G} {c : FieldFour}
    (h : M g = c • 1) : frobRep M g = FieldFour.frob c • 1 := by
  rw [frobRep_apply, h]
  funext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem kronRep_scalar {M : G →* Matrix (Fin n) (Fin n) FieldFour}
    {N : G →* Matrix (Fin m) (Fin m) FieldFour} {g : G} {c d : FieldFour}
    (hM : M g = c • 1) (hN : N g = d • 1) : kronRep M N g = (c * d) • 1 := by
  rw [kronRep_apply, hM, hN, Matrix.smul_kronecker, Matrix.kronecker_smul,
    Matrix.one_kronecker_one, smul_smul]
  funext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.one_apply,
    (Equiv.injective _).eq_iff]

theorem subRep_scalar {K : G →* Matrix (Fin n) (Fin n) FieldFour}
    {B : Matrix (Fin n) (Fin m) FieldFour} {P : Matrix (Fin m) (Fin n) FieldFour}
    {hPB : P * B = 1} {hinv : ∀ g, K g * B = B * (P * K g * B)} {g : G} {c : FieldFour}
    (h : K g = c • 1) : subRep K B P hPB hinv g = c • 1 := by
  rw [subRep_apply, h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPB]

end Scalars

theorem gmat_zH : gmat (zH : ↥hatM22Γ₀) = ω • 1 := hatM22Z_val

theorem zH_pow_three : zH ^ 3 = 1 := Subtype.ext hatM22Z_pow_three

theorem zH_inv : zH⁻¹ = zH * zH := by
  rw [inv_eq_iff_mul_eq_one, ← pow_two, ← pow_succ']
  exact zH_pow_three

theorem rep3a_zH : rep3a zH = ω • 1 := by
  rw [rep3a_apply, gmat_zH, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hatM22L0_mul_B0]

theorem rep3b_zH : rep3b zH = ω • 1 := by
  rw [rep3b_apply, gmat_zH, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hatM22F0_mul_R0]

theorem rep3a_zH_inv : rep3a zH⁻¹ = ω₂ • 1 := by
  rw [zH_inv, map_mul, rep3a_zH, smul_mul_smul_comm, Matrix.one_mul,
    show ω * ω = ω₂ by decide]

theorem dual3a_zH : dualRep rep3a zH = ω₂ • 1 := dualRep_scalar rep3a_zH_inv

theorem rep9_zH : rep9 zH = ω • 1 := by
  rw [rep9, kronRep_scalar dual3a_zH (frobRep_scalar rep3a_zH),
    show ω₂ * FieldFour.frob ω = ω by decide]

theorem rep33_zH : rep33 zH = (1 : FieldFour) • 1 := by
  rw [rep33, kronRep_scalar rep3a_zH dual3a_zH, show ω * ω₂ = 1 by decide]

theorem rep8_zH : rep8 zH = (1 : FieldFour) • 1 := subRep_scalar rep33_zH

theorem rep24a_zH : rep24a zH = ω • 1 := by
  rw [rep24a, kronRep_scalar rep8_zH (frobRep_scalar dual3a_zH),
    show (1 : FieldFour) * FieldFour.frob ω₂ = ω by decide]

theorem rep24b_zH : rep24b zH = ω • 1 := by
  rw [rep24b, kronRep_scalar rep3a_zH (frobRep_scalar rep8_zH),
    show ω * FieldFour.frob 1 = ω by decide]

abbrev hDim : Fin 5 → ℕ := ![3, 3, 3 * 3, 8 * 3, 3 * 8]

@[expose] noncomputable def hRepK {K : Type*} [Field K] (φ : FieldFour →+* K) :
    ∀ i : Fin 5, Representation K ↥hatH (Fin (hDim i) → K)
  | 0 => matrixBaseChange φ rep3a
  | 1 => matrixBaseChange φ rep3b
  | 2 => matrixBaseChange φ rep9
  | 3 => matrixBaseChange φ rep24a
  | 4 => matrixBaseChange φ rep24b

theorem isIrreducible_hRepK {K : Type*} [Field K]
    (φ : FieldFour →+* K) : ∀ i, (hRepK φ i).IsIrreducible := by
  intro i
  fin_cases i
  · exact isIrreducible_rep3a φ
  · exact isIrreducible_rep3b φ
  · exact isIrreducible_rep9 φ
  · exact isIrreducible_rep24a φ
  · exact isIrreducible_rep24b φ

theorem matrixBaseChange_scalar {K : Type*} [Field K] (φ : FieldFour →+* K) {G : Type*}
    [Group G] {n : ℕ} {M : G →* Matrix (Fin n) (Fin n) FieldFour} {g : G} {c : FieldFour}
    (h : M g = c • 1) : matrixBaseChange φ M g = φ c • LinearMap.id := by
  apply LinearMap.ext
  intro x
  rw [matrixBaseChange_apply, h]
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, apply_ite φ, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, LinearMap.smul_apply, LinearMap.id_apply,
    Pi.smul_apply]

theorem hRepK_zH {K : Type*} [Field K] (φ : FieldFour →+* K) :
    ∀ i, hRepK φ i zH = φ ω • LinearMap.id := by
  intro i
  fin_cases i
  · exact matrixBaseChange_scalar φ rep3a_zH
  · exact matrixBaseChange_scalar φ rep3b_zH
  · exact matrixBaseChange_scalar φ rep9_zH
  · exact matrixBaseChange_scalar φ rep24a_zH
  · exact matrixBaseChange_scalar φ rep24b_zH

theorem hRepK_ne {K : Type*} [Field K] (φ : FieldFour →+* K) :
    ∀ i j, i ≠ j → IsEmpty ((hRepK φ i).Equiv (hRepK φ j)) := by
  have h01 : φ (Matrix.trace (rep3a (Blk.hOf hABW_mem))) ≠
      φ (Matrix.trace (rep3b (Blk.hOf hABW_mem))) :=
    fun h => trace_rep3a_ne (φ.injective h)
  have h34 : φ (Matrix.trace (rep24a (Blk.hOf hAABW_mem))) ≠
      φ (Matrix.trace (rep24b (Blk.hOf hAABW_mem))) :=
    fun h => trace_rep24a_ne (φ.injective h)
  intro i j hij
  by_cases hd : hDim i = hDim j
  · have hcases : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) := by
      revert i j
      decide
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine isEmpty_equiv_of_trace_ne (Blk.hOf hABW_mem) ?_
      change LinearMap.trace K _ (matrixBaseChange φ rep3a _) ≠
        LinearMap.trace K _ (matrixBaseChange φ rep3b _)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h01
    · refine isEmpty_equiv_of_trace_ne (Blk.hOf hABW_mem) ?_
      change LinearMap.trace K _ (matrixBaseChange φ rep3b _) ≠
        LinearMap.trace K _ (matrixBaseChange φ rep3a _)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h01.symm
    · refine isEmpty_equiv_of_trace_ne (Blk.hOf hAABW_mem) ?_
      change LinearMap.trace K _ (matrixBaseChange φ rep24a _) ≠
        LinearMap.trace K _ (matrixBaseChange φ rep24b _)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h34
    · refine isEmpty_equiv_of_trace_ne (Blk.hOf hAABW_mem) ?_
      change LinearMap.trace K _ (matrixBaseChange φ rep24b _) ≠
        LinearMap.trace K _ (matrixBaseChange φ rep24a _)
      rw [trace_matrixBaseChange, trace_matrixBaseChange]
      exact h34.symm
  · exact isEmpty_equiv_of_finrank_ne (by rwa [Module.finrank_fin_fun, Module.finrank_fin_fun])

theorem nonempty_equiv_of_intertwining_four {G : Type*} [Group G] {K : Type*} [Field K]
    {d m : ℕ} (M : G →* Matrix (Fin d) (Fin d) FieldFour)
    (N : G →* Matrix (Fin m) (Fin m) FieldFour)
    (hM : (matrixBaseChange (RingHom.id FieldFour) M).IsIrreducible)
    (hN : (matrixBaseChange (RingHom.id FieldFour) N).IsIrreducible) (ψ : FieldFour →+* K)
    (f : (matrixBaseChange ψ M).IntertwiningMap (matrixBaseChange ψ N)) (hf : f ≠ 0) :
    Nonempty ((matrixBaseChange (RingHom.id FieldFour) N).Equiv
      (matrixBaseChange (RingHom.id FieldFour) M)) := by
  have hT0 : LinearMap.toMatrix' f.toLinearMap ≠ 0 := by
    intro h
    apply hf
    apply Representation.IntertwiningMap.ext
    exact LinearMap.toMatrix'.injective (h.trans (map_zero _).symm)
  obtain ⟨T, hT, hTM⟩ := exists_ne_zero_mul_eq_mul_of_map ψ (fun g => M g) (fun g => N g) _ hT0
    (toMatrix'_mul_map_eq ψ M N f)
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero (intertwiningMapOfMatrix (RingHom.id FieldFour) M N T hTM)
    (intertwiningMapOfMatrix_ne_zero _ M N T hTM hT)
  exact ⟨e.symm⟩

theorem hatH_classify
    (X : Type*) [AddCommGroup X] [Module FieldFour X]
    [FiniteDimensional FieldFour X] (τ : Representation FieldFour ↥hatH X)
    (hτ : τ.IsIrreducible) (hz : τ zH = ω • LinearMap.id) (hdim : finrank FieldFour X ≤ 14) :
    Nonempty (τ.Equiv (matrixBaseChange (RingHom.id FieldFour) rep3a)) ∨
      Nonempty (τ.Equiv (matrixBaseChange (RingHom.id FieldFour) rep3b)) ∨
        Nonempty (τ.Equiv (matrixBaseChange (RingHom.id FieldFour) rep9)) := by
  classical
  let k := AlgebraicClosure (ZMod 2)
  let φ : FieldFour →+* k := toField k
  have hnt := nontrivial_of_isIrreducible τ
  let eX := (Module.finBasis FieldFour X).equivFun
  let τ' := transportRep eX τ
  have hτ' : τ'.IsIrreducible := isIrreducible_of_equiv (transportRepEquiv eX τ) hτ
  let N := repMatrix τ'
  have hN : matrixBaseChange (RingHom.id FieldFour) N = τ' := matrixBaseChange_repMatrix τ'
  have hNirr : (matrixBaseChange (RingHom.id FieldFour) N).IsIrreducible := by rw [hN]; exact hτ'
  obtain ⟨eτ⟩ : Nonempty (τ.Equiv (matrixBaseChange (RingHom.id FieldFour) N)) := by
    rw [hN]
    exact ⟨transportRepEquiv eX τ⟩
  have hNz : N zH = ω • 1 := by
    change LinearMap.toMatrix' (eX.toLinearMap ∘ₗ τ zH ∘ₗ eX.symm.toLinearMap) = ω • 1
    rw [hz]
    funext i j
    simp [LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]
  have hm : 0 < finrank FieldFour X := Module.finrank_pos
  have : Nonempty (Fin (finrank FieldFour X)) := ⟨⟨0, hm⟩⟩
  let σ := matrixBaseChange φ N
  obtain ⟨U, hU0, hUirr⟩ := exists_isIrreducible_subrepresentation σ
  have hσz : σ zH = φ ω • LinearMap.id := matrixBaseChange_scalar φ hNz
  have hUz : U.toRepresentation zH = φ ω • LinearMap.id := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    change σ zH (u : Fin _ → k) = φ ω • (u : Fin _ → k)
    rw [hσz]
    rfl
  have hc : φ ω ≠ 1 := by
    intro h
    apply FieldFour.ω_ne_one
    apply φ.injective
    rw [h, map_one]
  have := isIrreducible_hRepK (K := k) φ
  have hU : U.toRepresentation.IsIrreducible := hUirr
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_central 2 hDim (hRepK φ) (hRepK_ne φ) zH_mem_center hc
    (hRepK_zH φ) hRep (fun g hg => hatH_cover g hg) (by simp) U.toSubmodule U.toRepresentation hUz
  have hUdim : finrank k U.toSubmodule ≤ 14 := by
    have h1 := Submodule.finrank_le U.toSubmodule
    rw [Module.finrank_fin_fun] at h1
    exact h1.trans hdim
  have hdi : hDim i ≤ 14 := by
    have h1 := e.toLinearEquiv.finrank_eq
    rw [Module.finrank_fin_fun] at h1
    exact h1 ▸ hUdim
  let incl : U.toRepresentation.IntertwiningMap σ :=
    ⟨U.toSubmodule.subtype, fun g => LinearMap.ext fun _ => rfl⟩
  let f := incl.comp e.symm.toIntertwiningMap
  have hf : f ≠ 0 := by
    obtain ⟨u, huU, hu0⟩ : ∃ u ∈ U, u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hU0
      ext x
      exact ⟨fun hx => (Submodule.mem_bot k).mpr (hcon x hx),
        fun hx => (Submodule.mem_bot k).mp hx ▸ Submodule.zero_mem _⟩
    intro h0
    apply hu0
    have h1 : f (e ⟨u, huU⟩) = u := by
      change U.toSubmodule.subtype (e.symm (e ⟨u, huU⟩)) = u
      rw [Representation.Equiv.symm_apply_apply]
      rfl
    rw [← h1, h0]
    rfl
  fin_cases i
  · left
    obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_four rep3a N (isIrreducible_rep3a _) hNirr φ f hf
    exact ⟨eτ.trans e'⟩
  · right; left
    obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_four rep3b N (isIrreducible_rep3b _) hNirr φ f hf
    exact ⟨eτ.trans e'⟩
  · right; right
    obtain ⟨e'⟩ := nonempty_equiv_of_intertwining_four rep9 N (isIrreducible_rep9 _) hNirr φ f hf
    exact ⟨eτ.trans e'⟩
  · exact absurd hdi (by decide)
  · exact absurd hdi (by decide)

end CFSG.Quasithin.HM22
