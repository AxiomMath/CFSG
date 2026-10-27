module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKZ3Def

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix

def s16kR : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

def s16kF4Mat : Fin 4 → Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![0, 1, s16kR, s16kR * s16kR]

def s16kF4Exp : Fin 4 → ℕ := ![0, 0, 1, 2]

def s16kRealify (A : Fin 3 → Fin 3 → Fin 4) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r s =>
    s16kF4Mat (A ⟨r.val / 2, by omega⟩ ⟨s.val / 2, by omega⟩)
      ⟨r.val % 2, by omega⟩ ⟨s.val % 2, by omega⟩

def s16kOmegaMat : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  Matrix.of fun r s =>
    if r.val / 2 = s.val / 2 then s16kR ⟨r.val % 2, by omega⟩ ⟨s.val % 2, by omega⟩ else 0

def s16kDiagMat (f : Fin 3 → Fin 4) : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  s16kRealify fun i j => if i = j then f i else 0

def s16kDiagAll : Finset (Matrix (Fin 6) (Fin 6) (ZMod 2)) :=
  ((Finset.univ : Finset (Fin 3 → Fin 4)).filter fun f => ∀ i, f i ≠ 0).image s16kDiagMat

@[expose] def s16kDi (i : Fin 3) : S16kGL6 :=
  Units.mk (s16kBlockMat i) (s16kBlockMat i * s16kBlockMat i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

theorem s16kDi_val (i : Fin 3) :
    (s16kDi i : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kBlockMat i := rfl

theorem s16kDi_mem (i : Fin 3) : s16kDi i ∈ s16kDiag :=
  Subgroup.subset_closure ⟨i, s16kDi_val i⟩

def s16kDiagUnit (f : Fin 3 → Fin 4) : S16kGL6 :=
  s16kDi 0 ^ (s16kF4Exp (f 0)) * s16kDi 1 ^ (s16kF4Exp (f 1)) *
    s16kDi 2 ^ (s16kF4Exp (f 2))

theorem s16kDiagUnit_mem (f : Fin 3 → Fin 4) : s16kDiagUnit f ∈ s16kDiag :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ (s16kDi_mem 0) _) (Subgroup.pow_mem _ (s16kDi_mem 1) _))
    (Subgroup.pow_mem _ (s16kDi_mem 2) _)

theorem s16kDiagUnit_val : ∀ (f : Fin 3 → Fin 4), (∀ i, f i ≠ 0) →
    (s16kDiagUnit f : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kDiagMat f := by
  decide +kernel

theorem s16kDiagAll_mem {d : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hd : d ∈ s16kDiagAll) :
    ∃ f : Fin 3 → Fin 4, (∀ i, f i ≠ 0) ∧ d = s16kDiagMat f := by
  rw [s16kDiagAll, Finset.mem_image] at hd
  obtain ⟨f, hf, rfl⟩ := hd
  rw [Finset.mem_filter] at hf
  exact ⟨f, hf.2, rfl⟩

theorem s16kDiagAll_exists_unit {d : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hd : d ∈ s16kDiagAll) : ∃ u ∈ s16kDiag, (u : Matrix (Fin 6) (Fin 6) (ZMod 2)) = d := by
  obtain ⟨f, hf, rfl⟩ := s16kDiagAll_mem hd
  exact ⟨s16kDiagUnit f, s16kDiagUnit_mem f, s16kDiagUnit_val f hf⟩

theorem s16kOmegaMat_eq_prod :
    s16kOmegaMat = s16kBlockMat 0 * s16kBlockMat 1 * s16kBlockMat 2 := by
  decide +kernel

def s16kAllNonzero : Finset (Fin 6 → ZMod 2) :=
  (Finset.univ : Finset (Fin 6 → ZMod 2)).erase 0

abbrev s16kBlockZero (v : Fin 6 → ZMod 2) (i : Fin 3) : Prop :=
  v ⟨2 * i.val, by omega⟩ = 0 ∧ v ⟨2 * i.val + 1, by omega⟩ = 0

def s16kF0 : Finset (Fin 6 → ZMod 2) :=
  s16kAllNonzero.filter fun v =>
    ∃ d ∈ s16kDiagAll, d ≠ 1 ∧ d.mulVec v = v

def s16kFull : Finset (Fin 6 → ZMod 2) :=
  s16kAllNonzero.filter fun v => ∀ i : Fin 3, ¬ s16kBlockZero v i

theorem s16kF0_subset_allNonzero : s16kF0 ⊆ s16kAllNonzero := Finset.filter_subset _ _

theorem s16kAllNonzero_eq_union : s16kAllNonzero = s16kF0 ∪ s16kFull := by
  decide +kernel

theorem s16kFull_transitive :
    ∀ v : Fin 6 → ZMod 2, v ∈ s16kFull →
      ∀ w : Fin 6 → ZMod 2, w ∈ s16kFull →
        ∃ d ∈ s16kDiagAll, d.mulVec v = w := by
  decide +kernel

theorem s16kMulVec_ne_zero_of_unit {g : S16kGL6} {w : Fin 6 → ZMod 2} (hw : w ≠ 0) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w ≠ 0 := by
  intro h0
  apply hw
  have h1 : (g⁻¹ : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)).mulVec w) = w := by
    rw [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_inv,
      ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]
  rw [h0] at h1
  simpa using h1.symm

@[expose] def s16kOmega : S16kGL6 :=
  Units.mk s16kOmegaMat (s16kOmegaMat * s16kOmegaMat) (by decide) (by decide)

theorem s16kOmega_val : (s16kOmega : Matrix (Fin 6) (Fin 6) (ZMod 2)) = s16kOmegaMat := rfl

theorem s16kOmega_ne_one : s16kOmega ≠ 1 := by
  intro h
  have h' : s16kOmegaMat = (1 : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
    have := congrArg (fun u : S16kGL6 => (u : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
    rwa [s16kOmega_val] at this
  exact (by decide : s16kOmegaMat ≠ (1 : Matrix (Fin 6) (Fin 6) (ZMod 2))) h'

theorem s16kOmega_orderOf : orderOf s16kOmega = 3 := by
  have h3 : s16kOmega ^ 3 = 1 := by
    apply Units.ext
    show ((s16kOmega : Matrix (Fin 6) (Fin 6) (ZMod 2))) ^ 3 = 1
    rw [s16kOmega_val]
    decide
  have hdvd : orderOf s16kOmega ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr h3
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) s16kOmega_ne_one
  · exact h

theorem s16kScal_eq_zpowers : s16kScal = Subgroup.zpowers s16kOmega := by
  rw [s16kScal, s16kOmega, Subgroup.zpowers_eq_closure]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact Units.ext (by simpa using h.trans s16kOmegaMat_eq_prod.symm)
  · intro h
    rw [h]
    simpa using s16kOmegaMat_eq_prod

theorem s16kDiag_eq_closure_range : s16kDiag = Subgroup.closure (Set.range s16kDi) := by
  rw [s16kDiag]
  congr 1
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_range]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, Units.ext ((s16kDi_val i).trans hi.symm)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i, s16kDi_val i⟩

theorem s16k_mem_normalizer_diag_iff {g : S16kGL6} :
    g ∈ Subgroup.normalizer (s16kDiag : Set S16kGL6) ↔
      ∀ i : Fin 3, g * s16kDi i * g⁻¹ ∈ s16kDiag := by
  constructor
  · intro hg i
    exact (Subgroup.mem_normalizer_iff.mp hg (s16kDi i)).mp (s16kDi_mem i)
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : s16kDiag.map (MulAut.conj g).toMonoidHom ≤ s16kDiag := by
      conv_lhs => rw [s16kDiag_eq_closure_range]
      rw [MonoidHom.map_closure]
      refine (Subgroup.closure_le s16kDiag).mpr ?_
      rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
      simpa [MulAut.conj_apply] using h i
    exact Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

theorem s16kF0_mem {v : Fin 6 → ZMod 2} (hv : v ∈ s16kF0) :
    ∃ d ∈ s16kDiagAll, d ≠ 1 ∧ d.mulVec v = v := by
  rw [s16kF0, Finset.mem_filter] at hv
  exact hv.2

theorem s16kAllNonzero_mem {v : Fin 6 → ZMod 2} : v ∈ s16kAllNonzero ↔ v ≠ 0 := by
  simp [s16kAllNonzero]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
