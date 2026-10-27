module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

public section

namespace CFSG.Quasithin.H13.KGInspOdd

open Subgroup

section Matrix

variable {K : Type*} [Field K]

theorem comm_iff (M N : Matrix (Fin 2) (Fin 2) K) : M * N = N * M ↔
    M 0 1 * N 1 0 = N 0 1 * M 1 0 ∧ N 0 1 * (M 0 0 - M 1 1) = M 0 1 * (N 0 0 - N 1 1) ∧
      M 1 0 * (N 0 0 - N 1 1) = N 1 0 * (M 0 0 - M 1 1) := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10
    exact ⟨by linear_combination h00, by linear_combination h01, by linear_combination h10⟩
  · rintro ⟨h1, h2, h3⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · linear_combination h1
    · linear_combination h2
    · linear_combination h3
    · linear_combination -h1

theorem scalar_of_commute {A B C : Matrix (Fin 2) (Fin 2) K} (hB : A * B = B * A)
    (hC : A * C = C * A) (hBC : B * C ≠ C * B) : A = A 0 0 • (1 : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨iB, iiB, iiiB⟩ := (comm_iff A B).mp hB
  obtain ⟨iC, iiC, iiiC⟩ := (comm_iff A C).mp hC
  by_contra hne
  apply hBC
  rw [comm_iff]
  have hv : A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 0 0 - A 1 1 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2, h3⟩ := h
    apply hne
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2]
    linear_combination -h3
  rcases hv with h | h | h
  · have G1 : B 0 1 * C 1 0 = C 0 1 * B 1 0 :=
      mul_left_cancel₀ h (by linear_combination B 0 1 * iC - C 0 1 * iB)
    have G2 : C 0 1 * (B 0 0 - B 1 1) = B 0 1 * (C 0 0 - C 1 1) :=
      mul_left_cancel₀ h (by linear_combination -(C 0 1) * iiB + B 0 1 * iiC)
    refine ⟨G1, G2, mul_left_cancel₀ h ?_⟩
    linear_combination (C 0 0 - C 1 1) * iB - (B 0 0 - B 1 1) * iC - A 1 0 * G2
  · have G1 : B 0 1 * C 1 0 = C 0 1 * B 1 0 :=
      mul_left_cancel₀ h (by linear_combination -(C 1 0) * iB + B 1 0 * iC)
    have G3 : B 1 0 * (C 0 0 - C 1 1) = C 1 0 * (B 0 0 - B 1 1) :=
      mul_left_cancel₀ h (by linear_combination B 1 0 * iiiC - C 1 0 * iiiB)
    refine ⟨G1, mul_left_cancel₀ h ?_, G3⟩
    linear_combination C 0 1 * iiiB - B 0 1 * iiiC - (A 0 0 - A 1 1) * G1
  · have G2 : C 0 1 * (B 0 0 - B 1 1) = B 0 1 * (C 0 0 - C 1 1) :=
      mul_left_cancel₀ h (by linear_combination (B 0 0 - B 1 1) * iiC - (C 0 0 - C 1 1) * iiB)
    have G3 : B 1 0 * (C 0 0 - C 1 1) = C 1 0 * (B 0 0 - B 1 1) :=
      mul_left_cancel₀ h (by linear_combination -(C 0 0 - C 1 1) * iiiB + (B 0 0 - B 1 1) * iiiC)
    refine ⟨mul_left_cancel₀ h ?_, G2, G3⟩
    linear_combination C 1 0 * iiB - B 1 0 * iiC - A 0 1 * G3

theorem commute_of_commute_gl {A B C : GL (Fin 2) K} (hB : A * B = B * A) (hC : A * C = C * A)
    (hBC : B * C ≠ C * B) (D : GL (Fin 2) K) : A * D = D * A := by
  have hB' : (A : Matrix (Fin 2) (Fin 2) K) * B = B * A := by
    rw [← Units.val_mul, hB, Units.val_mul]
  have hC' : (A : Matrix (Fin 2) (Fin 2) K) * C = C * A := by
    rw [← Units.val_mul, hC, Units.val_mul]
  have hBC' : (B : Matrix (Fin 2) (Fin 2) K) * C ≠ C * B := fun h =>
    hBC (Units.ext (by rw [Units.val_mul, Units.val_mul, h]))
  have hA := scalar_of_commute hB' hC' hBC'
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

end Matrix

section Param

variable {S X H : Type*} [Group S] [Group X] [Group H]

theorem mem_centralizer_of_param (ρ : S →* X) {a : S} (φ : H →* S)
    (hrange : φ.range = centralizer ({a} : Set S)) (A : H) :
    ρ (φ A) ∈ centralizer ({ρ a} : Set X) := by
  have h : φ A ∈ centralizer ({a} : Set S) := hrange ▸ ⟨A, rfl⟩
  rw [mem_centralizer_singleton_iff] at h ⊢
  rw [← map_mul, ← map_mul, h]

theorem exists_of_mem_centralizer (ρ : S →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center S) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1)
    (φ : H →* S) (hrange : φ.range = centralizer ({a} : Set S)) {g : X}
    (hg : g ∈ centralizer ({ρ a} : Set X)) : ∃ A : H, ρ (φ A) = g := by
  obtain ⟨s, rfl⟩ := hρ g
  have hs : s * a = a * s := CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3.commute_of_map_commute ρ hker
    h3 ha (mem_centralizer_singleton_iff.mp hg)
  have hs' : s ∈ φ.range := by
    rw [hrange]
    exact mem_centralizer_singleton_iff.mpr hs
  obtain ⟨A, rfl⟩ := hs'
  exact ⟨A, rfl⟩

theorem commutator_le_of_param (ρ : S →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center S) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1)
    (φ : H →* S) (hrange : φ.range = centralizer ({a} : Set S)) (T : Subgroup H)
    (hHT : ∀ A B : H, A * B * A⁻¹ * B⁻¹ ∈ T) :
    ⁅centralizer ({ρ a} : Set X), centralizer ({ρ a} : Set X)⁆ ≤ (T.map φ).map ρ := by
  rw [Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨A, rfl⟩ := exists_of_mem_centralizer ρ hρ hker h3 ha φ hrange hg
  obtain ⟨B, rfl⟩ := exists_of_mem_centralizer ρ hρ hker h3 ha φ hrange hg'
  refine ⟨φ (A * B * A⁻¹ * B⁻¹), ⟨_, hHT A B, rfl⟩, ?_⟩
  simp only [map_mul, map_inv, commutatorElement_def]

theorem central_of_param (ρ : S →* X) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center S) (h3 : ∀ z ∈ ρ.ker, z ^ 3 = 1) {a : S} (ha : a * a = 1)
    (φ : H →* S) (hrange : φ.range = centralizer ({a} : Set S)) (T : Subgroup H)
    (hT : T.Normal) (hinj : ∀ t ∈ T, ρ (φ t) = 1 → t = 1) {H₀ : Subgroup H} (hH₀ : H₀ ≤ T)
    (hschur : ∀ A : H, (∀ h ∈ H₀, A * h = h * A) → ∀ B : H, A * B = B * A) {g : X}
    (hg : g ∈ centralizer ({ρ a} : Set X)) (hgH : ∀ h ∈ H₀, g * ρ (φ h) = ρ (φ h) * g) :
    ∀ c ∈ centralizer ({ρ a} : Set X), g * c = c * g := by
  obtain ⟨A, rfl⟩ := exists_of_mem_centralizer ρ hρ hker h3 ha φ hrange hg
  have hA : ∀ h ∈ H₀, A * h = h * A := by
    intro h hh
    have hc : A * h * A⁻¹ * h⁻¹ ∈ T :=
      T.mul_mem (hT.conj_mem h (hH₀ hh) A) (T.inv_mem (hH₀ hh))
    have h1 : A * h * A⁻¹ * h⁻¹ = 1 := hinj _ hc (by
      simp only [map_mul, map_inv]
      rw [hgH h hh]
      group)
    calc A * h = A * h * A⁻¹ * h⁻¹ * (h * A) := by group
      _ = h * A := by rw [h1, one_mul]
  intro c hc
  obtain ⟨B, rfl⟩ := exists_of_mem_centralizer ρ hρ hker h3 ha φ hrange hc
  have hAB := hschur A hA B
  calc ρ (φ A) * ρ (φ B) = ρ (φ (A * B)) := by rw [map_mul, map_mul]
    _ = ρ (φ (B * A)) := by rw [hAB]
    _ = ρ (φ B) * ρ (φ A) := by rw [map_mul, map_mul]

end Param

end CFSG.Quasithin.H13.KGInspOdd
