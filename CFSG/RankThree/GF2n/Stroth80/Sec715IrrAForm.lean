module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrALin
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module Matrix

section Contr

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

theorem finrank_comap_contr [FiniteDimensional K L] {d : Fin 2 → K} (hd : d ≠ 0)
    (S : Submodule K L) :
    finrank K (Submodule.comap (contr d) S) = finrank K L + finrank K S := by
  set c := (contr d : (Fin 2 → L) →ₗ[K] L) with hc
  have hsurj := contr_surjective (L := L) hd
  have hker : LinearMap.ker c ≤ Submodule.comap c S := fun x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _
  have hrn := LinearMap.finrank_range_add_finrank_ker (c.domRestrict (Submodule.comap c S))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hker),
    Submodule.map_comap_eq_of_surjective hsurj] at hrn
  have hrn' := LinearMap.finrank_range_add_finrank_ker c
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn'
  have e : finrank K (Fin 2 → L) = 2 * finrank K L := by
    rw [Module.finrank_pi_fintype, Fin.sum_univ_two, two_mul]
  omega

theorem pureT_smul_smul (c a : K) (f : Fin 2 → K) (n : L) :
    pureT (c • f) (a • n) = (c * a) • pureT f n := by
  funext i
  simp only [pureT_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
  ring_nf

end Contr

section Pairing

variable {K L₃ L₄ U : Type*} [Field K] [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄]
  [Module K L₄] [AddCommGroup U] [Module K U]

theorem betaMu_pureT_right (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (f : Fin 2 → K) (n : L₄)
    (m : Fin 2 → L₃) : betaMu μ (pureT f n) m = μ (contr f m) n := by
  simp only [betaMu_apply, pureT_apply, contr_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply]

theorem ker_betaMu_pureT (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) (f : Fin 2 → K) (n : L₄) :
    LinearMap.ker (betaMu μ (pureT f n)) =
      Submodule.comap (contr f) (LinearMap.ker (μ.flip n)) := by
  ext m
  rw [LinearMap.mem_ker, Submodule.mem_comap, LinearMap.mem_ker, LinearMap.flip_apply,
    betaMu_pureT_right]

end Pairing

section Form

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

@[expose] def formT (P : L →ₗ[K] L →ₗ[K] K) (φ : Matrix (Fin 2) (Fin 2) K) :
    LinearMap.BilinForm K (Fin 2 → L) :=
  LinearMap.mk₂ K (fun m m' => ∑ i, ∑ j, φ i j * P (m i) (m' j))
    (fun m₁ m₂ m' => by
      simp only [Fin.sum_univ_two, Pi.add_apply, map_add, LinearMap.add_apply]
      ring)
    (fun c m m' => by
      simp only [Fin.sum_univ_two, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring)
    (fun m m₁ m₂ => by
      simp only [Fin.sum_univ_two, Pi.add_apply, map_add]
      ring)
    (fun c m m' => by
      simp only [Fin.sum_univ_two, Pi.smul_apply, map_smul, smul_eq_mul]
      ring)

theorem formT_apply (P : L →ₗ[K] L →ₗ[K] K) (φ : Matrix (Fin 2) (Fin 2) K) (m m' : Fin 2 → L) :
    formT P φ m m' = ∑ i, ∑ j, φ i j * P (m i) (m' j) := rfl

theorem formT_pureT_right (P : L →ₗ[K] L →ₗ[K] K) (φ : Matrix (Fin 2) (Fin 2) K)
    (m : Fin 2 → L) (d : Fin 2 → K) (k : L) :
    formT P φ m (pureT d k) = P (contr (φ *ᵥ d) m) k := by
  simp only [formT_apply, pureT_apply, contr_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem ker_formT_eq_bot {P : L →ₗ[K] L →ₗ[K] K} (hP : ∀ a, (∀ a', P a a' = 0) → a = 0)
    {φ ψ : Matrix (Fin 2) (Fin 2) K} (hφψ : φ * ψ = 1) : LinearMap.ker (formT P φ) = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun m hm => ?_
  have h : ∀ d : Fin 2 → K, contr (φ *ᵥ d) m = 0 := fun d =>
    hP _ fun k => by rw [← formT_pureT_right, hm, LinearMap.zero_apply]
  funext i
  have h1 := h (ψ *ᵥ Pi.single i 1)
  rw [Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec] at h1
  fin_cases i <;> simpa [contr_apply] using h1

theorem orthogonal_comap_contr [FiniteDimensional K L] {P : L →ₗ[K] L →ₗ[K] K}
    (hP : ∀ a, (∀ a', P a a' = 0) → a = 0) {φ ψ : Matrix (Fin 2) (Fin 2) K} (hφψ : φ * ψ = 1)
    {f : Fin 2 → K} (hf : f ≠ 0) {S : Submodule K L} (hS : ∀ a, (∀ s ∈ S, P s a = 0) ↔ a ∈ S) :
    (formT P φ).orthogonal (Submodule.comap (contr f) S) = S.map (pureT (ψ *ᵥ f)) := by
  have hφd : φ *ᵥ (ψ *ᵥ f) = f := by rw [Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  have hd : ψ *ᵥ f ≠ 0 := by
    intro h
    rw [h, Matrix.mulVec_zero] at hφd
    exact hf hφd.symm
  have hle : S.map (pureT (ψ *ᵥ f)) ≤ (formT P φ).orthogonal (Submodule.comap (contr f) S) := by
    rintro _ ⟨k, hk, rfl⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro m hm
    rw [formT_pureT_right, hφd]
    exact (hS k).mpr hk _ hm
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := formT P φ)
    (Submodule.comap (contr f) S)
  rw [ker_formT_eq_bot hP hφψ, inf_bot_eq, finrank_bot, add_zero, finrank_comap_contr hf] at h1
  have e : finrank K (Fin 2 → L) = 2 * finrank K L := by
    rw [Module.finrank_pi_fintype, Fin.sum_univ_two, two_mul]
  have hPker : LinearMap.ker P = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun a ha => hP a fun a' => by rw [ha, LinearMap.zero_apply]
  have hSS : LinearMap.BilinForm.orthogonal P S = S := by
    ext a
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact hS a
  have h2 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := P) S
  rw [hPker, inf_bot_eq, finrank_bot, add_zero, hSS] at h2
  have h3 : finrank K (S.map (pureT (ψ *ᵥ f))) = finrank K S :=
    (Submodule.equivMapOfInjective _ (pureT_injective hd) S).finrank_eq.symm
  refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
  omega

end Form

section Triality

variable {K L₃ L₄ U : Type*} [Field K] [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄]
  [Module K L₄] [AddCommGroup U] [Module K U]

structure TrialityFacts (q₃ : QuadraticForm K L₃) (q₄ : QuadraticForm K L₄)
    (μ : L₃ →ₗ[K] L₄ →ₗ[K] U) : Prop where
  ker_eq_bot : ∀ y : L₄, y ≠ 0 → q₄ y ≠ 0 → LinearMap.ker (μ.flip y) = ⊥
  finrank_range : ∀ y : L₄, y ≠ 0 → q₄ y = 0 → finrank K (LinearMap.range (μ.flip y)) = 4
  ker_singular : ∀ y : L₄, y ≠ 0 → q₄ y = 0 → ∀ x ∈ LinearMap.ker (μ.flip y), q₃ x = 0
  range_det : ∀ y y' : L₄, y ≠ 0 → y' ≠ 0 → q₄ y = 0 → q₄ y' = 0 →
    LinearMap.range (μ.flip y) = LinearMap.range (μ.flip y') → ∃ c : K, y' = c • y
  ker_det : ∀ y y' : L₄, y ≠ 0 → y' ≠ 0 → q₄ y = 0 → q₄ y' = 0 →
    LinearMap.ker (μ.flip y) = LinearMap.ker (μ.flip y') → ∃ c : K, y' = c • y

namespace TrialityFacts

variable {q₃ : QuadraticForm K L₃} {q₄ : QuadraticForm K L₄} {μ : L₃ →ₗ[K] L₄ →ₗ[K] U}

theorem finrank_ker [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8) {y : L₄} (hy : y ≠ 0) (hqy : q₄ y = 0) :
    finrank K (LinearMap.ker (μ.flip y)) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (μ.flip y)
  rw [T.finrank_range y hy hqy, h8] at h
  omega

theorem ker_ne_bot [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8) {y : L₄} (hy : y ≠ 0) (hqy : q₄ y = 0) :
    LinearMap.ker (μ.flip y) ≠ ⊥ := by
  intro h
  have := T.finrank_ker h8 hy hqy
  rw [h, finrank_bot] at this
  omega

theorem lt_finrank_range [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8) {y : L₄} (hy : y ≠ 0) (hqy : q₄ y ≠ 0) :
    4 < finrank K (LinearMap.range (μ.flip y)) := by
  have h := LinearMap.finrank_range_add_finrank_ker (μ.flip y)
  rw [T.ker_eq_bot y hy hqy, finrank_bot, h8] at h
  omega

theorem orthogonal_ker_iff [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8)
    (hnd : ∀ a : L₃, (∀ a' : L₃, QuadraticMap.polar q₃ a a' = 0) → a = 0) {n : L₄} (hn : n ≠ 0)
    (hqn : q₄ n = 0) (a : L₃) :
    (∀ s ∈ LinearMap.ker (μ.flip n), QuadraticMap.polarBilin q₃ s a = 0) ↔
      a ∈ LinearMap.ker (μ.flip n) := by
  set S := LinearMap.ker (μ.flip n) with hS
  have hpol : ∀ s ∈ S, ∀ s' ∈ S, QuadraticMap.polarBilin q₃ s s' = 0 := by
    intro s hs s' hs'
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      T.ker_singular n hn hqn _ (S.add_mem hs hs'), T.ker_singular n hn hqn _ hs,
      T.ker_singular n hn hqn _ hs', sub_zero, sub_zero]
  have hle : S ≤ LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin q₃) S :=
    fun s' hs' => (LinearMap.BilinForm.mem_orthogonal_iff).mpr fun s hs => hpol s hs s' hs'
  have hker : LinearMap.ker (QuadraticMap.polarBilin q₃) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun a ha => hnd a fun a' => by
      rw [← QuadraticMap.polarBilin_apply_apply, ha, LinearMap.zero_apply]
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := QuadraticMap.polarBilin q₃) S
  rw [hker, inf_bot_eq, finrank_bot, add_zero, T.finrank_ker h8 hn hqn, h8] at h1
  have heq : S = LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin q₃) S :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [T.finrank_ker h8 hn hqn]; omega)
  constructor
  · intro h
    rw [heq, LinearMap.BilinForm.mem_orthogonal_iff]
    exact h
  · intro ha s hs
    exact hpol s hs a ha

theorem exists_eq_pureT [FiniteDimensional K L₃] [FiniteDimensional K U]
    (T : TrialityFacts q₃ q₄ μ) (h8 : finrank K L₃ = 8) {x : Fin 2 → L₄} (hx : x ≠ 0)
    (hrk : finrank K (LinearMap.range (betaMu μ x)) ≤ 4) :
    ∃ (f : Fin 2 → K) (n : L₄), f ≠ 0 ∧ n ≠ 0 ∧ q₄ n = 0 ∧ x = pureT f n :=
  exists_eq_pureT_of_finrank_range_le q₄ μ (fun _ hc hq => T.lt_finrank_range h8 hc hq)
    T.finrank_range T.range_det hx hrk

theorem forall_betaMu_pureT_eq_zero_iff' [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8) {n : L₄} (hn : n ≠ 0) (hqn : q₄ n = 0) (d : Fin 2 → K)
    (x : Fin 2 → L₄) :
    (∀ k ∈ LinearMap.ker (μ.flip n), betaMu μ x (pureT d k) = 0) ↔ contr d x ∈ K ∙ n :=
  forall_betaMu_pureT_eq_zero_iff q₄ μ T.ker_eq_bot
    (fun c c' hc hc' hqc hqc' => by rw [T.finrank_ker h8 hc hqc, T.finrank_ker h8 hc' hqc'])
    (fun c hc hqc => T.ker_ne_bot h8 hc hqc) T.ker_det hn hqn d x

theorem eq_smul_of_map_eq [FiniteDimensional K L₃] (T : TrialityFacts q₃ q₄ μ)
    (h8 : finrank K L₃ = 8) {φ ψ : Matrix (Fin 2) (Fin 2) K} (hφψ : φ * ψ = 1)
    {f f' : Fin 2 → K} (hf : f ≠ 0) (hf' : f' ≠ 0) {n n' : L₄} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hqn : q₄ n = 0) (hqn' : q₄ n' = 0)
    (h : (LinearMap.ker (μ.flip n)).map (pureT (ψ *ᵥ f)) =
      (LinearMap.ker (μ.flip n')).map (pureT (ψ *ᵥ f'))) :
    ∃ c : K, pureT f' n' = c • pureT f n := by
  have hne : ∀ g : Fin 2 → K, g ≠ 0 → ψ *ᵥ g ≠ 0 := by
    intro g hg h0
    apply hg
    rw [← Matrix.one_mulVec g, ← hφψ, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  obtain ⟨⟨c, -, hc⟩, hS⟩ := eq_smul_of_map_pureT_eq (hne f hf) (hne f' hf')
    (T.ker_ne_bot h8 hn hqn) h
  obtain ⟨a, ha⟩ := T.ker_det n n' hn hn' hqn hqn' hS
  have hff : f' = c • f := by
    rw [← Matrix.one_mulVec f', ← hφψ, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul,
      Matrix.mulVec_mulVec, hφψ, Matrix.one_mulVec]
  exact ⟨c * a, by rw [hff, ha, pureT_smul_smul]⟩

end TrialityFacts

end Triality

end CFSG.RankThree.GF2n.Stroth80.S715L
