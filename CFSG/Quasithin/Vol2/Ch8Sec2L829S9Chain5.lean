module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain3
public import CFSG.Quasithin.Vol2.Ch8Sec2L829S9Chain4

public section

namespace CFSG.Quasithin.H13.L829N

open Matrix

theorem s9c5_det_zero_of_flag {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (hAB : A < B) (Q : Matrix (Fin d) (Fin d) E) (hQ : ∀ v ∈ B, Q *ᵥ v ∈ A) :
    Q.det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  let f : ↥B →ₗ[E] (Fin d → E) := (Matrix.toLin' Q).comp B.subtype
  have hrange : LinearMap.range f ≤ A := by
    rintro _ ⟨w, rfl⟩
    exact hQ w.1 w.2
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 : Module.finrank E (LinearMap.range f) ≤ Module.finrank E A :=
    Submodule.finrank_mono hrange
  have h3 : Module.finrank E A < Module.finrank E B := Submodule.finrank_lt_finrank_of_lt hAB
  have hk : LinearMap.ker f ≠ ⊥ := by
    intro h
    have h0 : Module.finrank E (LinearMap.ker f) = 0 := by rw [h, finrank_bot]
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨(w : Fin d → E), fun h => hw0 (Subtype.ext h), ?_⟩
  exact LinearMap.mem_ker.mp hw

theorem s9c5_mk_zero_iff {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    {w : Fin d → E} (hw : w ∈ B) : s9cMk (A := A) (B := B) w hw = 0 ↔ w ∈ A := by
  unfold s9cMk
  rw [Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

theorem s9c5_ind_P1 {E : Type} [Field E] {d : ℕ} {A B : Submodule E (Fin d → E)}
    (K : s9cFlag A B) :
    s9cIndHom (s9P1 K) = s9P1 (s9cIndHom K) := by
  simp only [s9P1, map_add, map_mul, map_one]

theorem s9c5_toMat_P1 {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι E V) (T : Module.End E V) :
    LinearMap.toMatrixAlgEquiv b (s9P1 (R := Module.End E V) T) = s9P1 (LinearMap.toMatrixAlgEquiv b T) := by
  simp only [s9P1, map_add, map_mul, map_one]

theorem s9c5_matrix_P1 {E : Type} [Field E] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (x : N) :
    (((s9P1 (s9cOfN hA hB x) : s9cFlag A B)) : Matrix (Fin d) (Fin d) E) =
      s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) := by
  simp only [s9P1, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_one]
  rfl

theorem s9c_claim_i {E : Type} [Field E] [CharP E 2] {d : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (hAB : A < B) (x : N)
    (hR : s9P1 ((s9cRep hA hB x : GL (Fin (Module.finrank E (s9cSub A B))) E) :
      Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) = 0) :
    (s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det = 0 := by
  set T : Module.End E (s9cSub A B) := s9cIndHom (s9cOfN hA hB x) with hT
  have hRT : LinearMap.toMatrixAlgEquiv (Module.finBasis E (s9cSub A B)) T =
      ((s9cRep hA hB x : GL (Fin (Module.finrank E (s9cSub A B))) E) :
        Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) := by
    rw [s9cRep_val]
    rfl
  have hST : s9P1 (R := Module.End E (s9cSub A B)) T = 0 := by
    apply (LinearMap.toMatrixAlgEquiv (Module.finBasis E (s9cSub A B))).injective
    rw [map_zero, s9c5_toMat_P1, hRT]
    exact hR
  apply s9c5_det_zero_of_flag hAB
  intro v hv
  have hz : s9cIndHom (s9P1 (s9cOfN hA hB x)) (s9cMk v hv) = 0 := by
    rw [s9c5_ind_P1, ← hT, hST]
    rfl
  rw [s9cIndHom_mk, s9c5_mk_zero_iff, s9c5_matrix_P1] at hz
  exact hz

theorem s9c_claim_j {E : Type} [Field E] [CharP E 2] {d r : ℕ} {N : Subgroup (GL (Fin d) E)}
    {A B : Submodule E (Fin d → E)} (hA : S9cInv N A) (hB : S9cInv N B) (hAB : A < B) (x : N)
    (Y : ℕ → Submodule E (Fin d → E)) (hY0 : Y 0 = ⊥) (hYr : Y r = ⊤) (i₀ : ℕ) (hi₀ : i₀ < r)
    (hYA : Y i₀ = A) (hYB : Y (i₀ + 1) = B) (hYinv : ∀ i, i ≤ r → S9cInv N (Y i))
    (htriv : ∀ i, i < r → i ≠ i₀ → ∀ v ∈ Y (i + 1),
      ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ v - v ∈ Y i)
    (hinv : s9P1 ((s9cRep hA hB x : GL (Fin (Module.finrank E (s9cSub A B))) E) :
        Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) *
      ((s9cRep hA hB x : GL (Fin (Module.finrank E (s9cSub A B))) E) :
        Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) = 1) :
    (s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)).det ≠ 0 := by
  set T : Module.End E (s9cSub A B) := s9cIndHom (s9cOfN hA hB x) with hT
  have hRT : LinearMap.toMatrixAlgEquiv (Module.finBasis E (s9cSub A B)) T =
      ((s9cRep hA hB x : GL (Fin (Module.finrank E (s9cSub A B))) E) :
        Matrix (Fin (Module.finrank E (s9cSub A B))) (Fin (Module.finrank E (s9cSub A B))) E) := by
    rw [s9cRep_val]
    rfl
  have hST1 : s9P1 (R := Module.End E (s9cSub A B)) T * T = 1 := by
    apply (LinearMap.toMatrixAlgEquiv (Module.finBasis E (s9cSub A B))).injective
    rw [map_mul, s9c5_toMat_P1, hRT, map_one]
    exact hinv
  have hsurj : Function.Surjective (s9P1 (R := Module.End E (s9cSub A B)) T) := by
    intro u
    refine ⟨T u, ?_⟩
    have := congrArg (fun F : Module.End E (s9cSub A B) => F u) hST1
    simpa using this
  have hinj : Function.Injective (s9P1 (R := Module.End E (s9cSub A B)) T) := LinearMap.injective_iff_surjective.mpr hsurj
  have hQ : ∀ i, i < r → ∀ v ∈ Y (i + 1),
      (s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)) *ᵥ v ∈ Y i → v ∈ Y i := by
    intro i hi v hv hQv
    by_cases hii : i = i₀
    · subst hii
      have hvB : v ∈ B := by
        rw [← hYB]
        exact hv
      have hQA : (s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)) *ᵥ v ∈ A := by
        rw [← hYA]
        exact hQv
      have hK0 : s9cMk (A := A) (((s9P1 (s9cOfN hA hB x) : s9cFlag A B) : Matrix (Fin d) (Fin d) E) *ᵥ v)
          (s9cFlag_mapB (s9P1 (s9cOfN hA hB x)) hvB) = 0 := by
        rw [s9c5_mk_zero_iff, s9c5_matrix_P1]
        exact hQA
      have h1 : s9P1 (R := Module.End E (s9cSub A B)) T (s9cMk (A := A) v hvB) = 0 := by
        have e : s9P1 (R := Module.End E (s9cSub A B)) T = s9cIndHom (s9P1 (s9cOfN hA hB x)) := by
          rw [s9c5_ind_P1]
        rw [e, s9cIndHom_mk]
        exact hK0
      have h2 : s9cMk (A := A) v hvB = 0 := by
        apply hinj
        rw [h1, map_zero]
      have h3 := (s9c5_mk_zero_iff hvB).mp h2
      rw [hYA]
      exact h3
    · have hMinv : ∀ w ∈ Y i,
          ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) *ᵥ w ∈ Y i :=
        fun w hw => hYinv i (by omega) (x : GL (Fin d) E) x.2 w hw
      have hstep := s9c_trivial_step_P1 (Y i) (Y (i + 1))
        ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E) hMinv
        (fun w hw => htriv i hi hii w hw) v hv
      have hv' : v = (s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)) *ᵥ v -
          ((s9P1 ((x : GL (Fin d) E) : Matrix (Fin d) (Fin d) E)) *ᵥ v - v) := by
        abel
      rw [hv']
      exact (Y i).sub_mem hQv hstep
  exact s9c_flag_injective r Y hY0 hYr _ hQ

end CFSG.Quasithin.H13.L829N
