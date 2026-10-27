module

public import CFSG.RankThree.PartOne.K1320.L4TorusWeyl

public section

namespace CFSG.RankThree.PartOne.K1327

open CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ CFSG.RankThree.PartOne.K1320

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [Finite K] in
theorem units_eq_one_of_inv_eq {a : Kˣ} (h : a = a⁻¹) : a = 1 := by
  have h1 : (a : K) ^ 2 = 1 := by
    have := congrArg (fun x : Kˣ => (x : K) * (a : K)) h
    simp only [Units.inv_mul] at this
    rw [pow_two]
    exact this
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h3 : ((a : K) - 1) ^ 2 = 0 := by linear_combination h1 + (1 - (a : K)) * h2
  have h4 : (a : K) = 1 := sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h3)
  exact Units.ext h4

theorem preserves_of_comm_Tl {a : Kˣ} (ha : a ≠ 1) {m : ↥(M8 K)}
    (hm : m * Tl K a = Tl K a * m) :
    (∀ v : QV K (Fin 2), v 1 = 0 → ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 1 = 0) ∧
      (∀ v : QV K (Fin 2), v 0 = 0 → ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 0 = 0) := by
  have hne : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => ha (units_eq_one_of_inv_eq (Units.ext h))
  have key : ∀ v : QV K (Fin 2),
      (Tl K a : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) =
        (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ((Tl K a : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) := by
    intro v
    have := congrArg (fun y : ↥(M8 K) => (y : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) hm.symm
    exact this
  constructor
  · intro v hv
    have h1 := key v
    rw [Tl_apply_of_snd_eq_zero a v hv, map_smul] at h1
    have h2 := congrFun h1 1
    rw [Tl_apply_one] at h2
    simp only [Pi.smul_apply, Algebra.smul_def] at h2
    have h3 : (algebraMap K (Qext K) (a : K) - algebraMap K (Qext K) ((a⁻¹ : Kˣ) : K)) *
        ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 1 = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.2 h2.symm
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd ((algebraMap K (Qext K)).injective (sub_eq_zero.1 h4)) hne
    · exact h4
  · intro v hv
    have h1 := key v
    rw [Tl_apply_of_fst_eq_zero a v hv, map_smul] at h1
    have h2 := congrFun h1 0
    rw [Tl_apply_zero] at h2
    simp only [Pi.smul_apply, Algebra.smul_def] at h2
    have h3 : (algebraMap K (Qext K) (a : K) - algebraMap K (Qext K) ((a⁻¹ : Kˣ) : K)) *
        ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 0 = 0 := by
      rw [sub_mul]
      exact sub_eq_zero.2 h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd ((algebraMap K (Qext K)).injective (sub_eq_zero.1 h4)) hne
    · exact h4


theorem exists_blocks {m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)}
    (h1 : ∀ v : QV K (Fin 2), v 1 = 0 → (m v) 1 = 0)
    (h2 : ∀ v : QV K (Fin 2), v 0 = 0 → (m v) 0 = 0) :
    ∃ m₁ m₂ : Qext K ≃ₗ[K] Qext K, ∀ v : QV K (Fin 2),
      (m v) 0 = m₁ (v 0) ∧ (m v) 1 = m₂ (v 1) := by
  let A : Qext K →ₗ[K] Qext K :=
    (LinearMap.proj (0 : Fin 2)).comp (m.toLinearMap.comp (LinearMap.single K (fun _ => Qext K) 0))
  let B : Qext K →ₗ[K] Qext K :=
    (LinearMap.proj (1 : Fin 2)).comp (m.toLinearMap.comp (LinearMap.single K (fun _ => Qext K) 1))
  have hA : ∀ w : Qext K, A w = (m (Pi.single 0 w)) 0 := fun w => rfl
  have hB : ∀ w : Qext K, B w = (m (Pi.single 1 w)) 1 := fun w => rfl
  have hv : ∀ v : QV K (Fin 2), (m v) 0 = A (v 0) ∧ (m v) 1 = B (v 1) := by
    intro v
    have hd := single_decomp v
    have e0 : ((m (Pi.single 1 (v 1) : QV K (Fin 2))) 0) = 0 := h2 _ (by simp)
    have e1 : ((m (Pi.single 0 (v 0) : QV K (Fin 2))) 1) = 0 := h1 _ (by simp)
    constructor
    · conv_lhs => rw [hd]
      rw [map_add, Pi.add_apply, e0, add_zero, hA]
    · conv_lhs => rw [hd]
      rw [map_add, Pi.add_apply, e1, zero_add, hB]
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h3 : m (Pi.single 0 w : QV K (Fin 2)) = 0 := by
      funext i
      fin_cases i
      · exact hw
      · exact h1 _ (by simp)
    have h4 : (Pi.single 0 w : QV K (Fin 2)) = 0 := by
      have := congrArg m.symm h3
      simpa using this
    have := congrFun h4 0
    simpa using this
  have hBinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have h3 : m (Pi.single 1 w : QV K (Fin 2)) = 0 := by
      funext i
      fin_cases i
      · exact h2 _ (by simp)
      · exact hw
    have h4 : (Pi.single 1 w : QV K (Fin 2)) = 0 := by
      have := congrArg m.symm h3
      simpa using this
    have := congrFun h4 1
    simpa using this
  refine ⟨LinearEquiv.ofInjectiveEndo A hAinj, LinearEquiv.ofInjectiveEndo B hBinj, fun v => ?_⟩
  exact hv v

theorem conj_extCoord {m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)} {m₁ m₂ : Qext K ≃ₗ[K] Qext K}
    (hm : ∀ v : QV K (Fin 2), (m v) 0 = m₁ (v 0) ∧ (m v) 1 = m₂ (v 1))
    (g : Qext K ≃ₗ[K] Qext K) :
    m * extCoord 0 g * m⁻¹ = extCoord 0 (m₁ * g * m₁⁻¹) ∧
      m * extCoord 1 g * m⁻¹ = extCoord 1 (m₂ * g * m₂⁻¹) := by
  have hinv : ∀ v : QV K (Fin 2), (m⁻¹ v) 0 = m₁.symm (v 0) ∧ (m⁻¹ v) 1 = m₂.symm (v 1) := by
    intro v
    have h := hm (m⁻¹ v)
    have hmv : m (m⁻¹ v) = v := by simp
    rw [hmv] at h
    exact ⟨by rw [h.1]; simp, by rw [h.2]; simp⟩
  have hk : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k
    fin_cases k <;> simp
  constructor
  · refine LinearEquiv.ext fun v => funext fun k => ?_
    show (m (extCoord 0 g (m⁻¹ v))) k = (extCoord 0 (m₁ * g * m₁⁻¹) v) k
    rcases hk k with rfl | rfl
    · rw [(hm _).1, extCoord_apply, extCoord_apply]
      simp [(hinv v).1]
    · rw [(hm _).2, extCoord_apply, extCoord_apply]
      simp [(hinv v).2]
  · refine LinearEquiv.ext fun v => funext fun k => ?_
    show (m (extCoord 1 g (m⁻¹ v))) k = (extCoord 1 (m₂ * g * m₂⁻¹) v) k
    rcases hk k with rfl | rfl
    · rw [(hm _).1, extCoord_apply, extCoord_apply]
      simp [(hinv v).1]
    · rw [(hm _).2, extCoord_apply, extCoord_apply]
      simp [(hinv v).2]

theorem conj_blkA_mem {m : ↥(M8 K)}
    (h1 : ∀ v : QV K (Fin 2), v 1 = 0 → ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 1 = 0)
    (h2 : ∀ v : QV K (Fin 2), v 0 = 0 → ((m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) v) 0 = 0)
    (i : Fin 2) (X : Matrix.SpecialLinearGroup (Fin 2) K) :
    ∃ X' : Matrix.SpecialLinearGroup (Fin 2) K, m * blkA i X * m⁻¹ = blkA i X' := by
  obtain ⟨m₁, m₂, hm⟩ := exists_blocks h1 h2
  have hc := conj_extCoord hm (iotaK X)
  have hdet : ∀ n : Qext K ≃ₗ[K] Qext K, LinearEquiv.det (n * iotaK X * n⁻¹) = 1 := by
    intro n
    rw [map_mul, map_mul, det_iotaK, map_inv, mul_one, mul_inv_cancel]
  have hlift : ∀ g' : Qext K ≃ₗ[K] Qext K, LinearEquiv.det g' = 1 →
      ∃ X' : Matrix.SpecialLinearGroup (Fin 2) K, iotaK X' = g' := by
    intro g' hg'
    have hd : ((glK g' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1 := by
      rw [det_glK, hg']
      rfl
    refine ⟨⟨(glK g' : Matrix (Fin 2) (Fin 2) K), hd⟩, ?_⟩
    apply glK.injective
    refine (glK_iotaK (K := K) _).trans ?_
    apply Units.ext
    rfl
  fin_cases i
  · obtain ⟨X', hX'⟩ := hlift (m₁ * iotaK X * m₁⁻¹) (hdet m₁)
    refine ⟨X', Subtype.ext ?_⟩
    show (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * extCoord 0 (iotaK X) *
      (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))⁻¹ = extCoord 0 (iotaK X')
    rw [hc.1, hX']
  · obtain ⟨X', hX'⟩ := hlift (m₂ * iotaK X * m₂⁻¹) (hdet m₂)
    refine ⟨X', Subtype.ext ?_⟩
    show (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * extCoord 1 (iotaK X) *
      (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))⁻¹ = extCoord 1 (iotaK X')
    rw [hc.2, hX']

theorem conj_slB {a : Kˣ} (ha : a ≠ 1) {m : ↥(M8 K)} (hm : m * Tl K a = Tl K a * m) :
    (∀ g ∈ slB K 0 1, m * g * m⁻¹ ∈ slB K 0 1) ∧ (∀ g ∈ slB K 2 3, m * g * m⁻¹ ∈ slB K 2 3) := by
  obtain ⟨h1, h2⟩ := preserves_of_comm_Tl ha hm
  constructor
  · intro g hg
    rw [← blkA_zero_range] at hg ⊢
    obtain ⟨X, rfl⟩ := hg
    obtain ⟨X', hX'⟩ := conj_blkA_mem h1 h2 0 X
    exact ⟨X', hX'.symm⟩
  · intro g hg
    rw [← blkA_one_range] at hg ⊢
    obtain ⟨X, rfl⟩ := hg
    obtain ⟨X', hX'⟩ := conj_blkA_mem h1 h2 1 X
    exact ⟨X', hX'.symm⟩

end CFSG.RankThree.PartOne.K1327
