module

public import CFSG.RankThree.PartOne.KC.UnitaryTransvectionDefs
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherIsotropicRadical
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryDefiningRadical
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartOne.KCUnitaryTrv

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

section Semilinear

variable {K : Type} [Field K] {n : ℕ}

@[expose] def semilin (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) (x : Fin n → K) : Fin n → K :=
  A *ᵥ fun i => σ (x i)

theorem semilin_add (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) (x y : Fin n → K) :
    semilin A σ (x + y) = semilin A σ x + semilin A σ y := by
  simp only [semilin]
  rw [← mulVec_add]
  congr 1
  funext i
  simp

theorem semilin_smul (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) (t : K) (x : Fin n → K) :
    semilin A σ (t • x) = σ t • semilin A σ x := by
  simp only [semilin]
  rw [← mulVec_smul]
  congr 1
  funext i
  simp

theorem semilin_sub (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) (x y : Fin n → K) :
    semilin A σ (x - y) = semilin A σ x - semilin A σ y := by
  have h := semilin_add A σ (x - y) y
  rw [sub_add_cancel] at h
  rw [h]
  abel

theorem semilin_single (A : Matrix (Fin n) (Fin n) K) (σ : K ≃+* K) (j : Fin n) :
    semilin A σ (Pi.single j 1) = A *ᵥ Pi.single j 1 := by
  simp only [semilin]
  congr 1
  funext i
  by_cases hij : i = j <;> simp [hij]

theorem semilin_mulVec {A M : Matrix (Fin n) (Fin n) K} {σ : K ≃+* K}
    (hM : A * M.map σ = M * A) (x : Fin n → K) :
    semilin A σ (M *ᵥ x) = M *ᵥ semilin A σ x := by
  have h1 : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ fun i => σ (x i) := by
    funext i
    exact RingHom.map_mulVec (σ : K →+* K) M x i
  simp only [semilin]
  rw [h1, mulVec_mulVec, hM, ← mulVec_mulVec]

end Semilinear

section Pointwise

variable {p f : ℕ} {K : Type} [Field K] {m : ℕ} (h : UnitaryFieldData p f K)

local notation "e₀" => (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K)
local notation "eₗ" => (Pi.single (Fin.last (m + 1)) (1 : K) : Fin (m + 2) → K)

theorem eich_apply (y : Fin (m + 2) → K) (c : K) (v : Fin (m + 2) → K) :
    eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c *ᵥ v =
      v + v (Fin.last (m + 1)) • y - gramForm h (trvGram K m) y v •
        (Pi.single 0 1 : Fin (m + 2) → K) +
        (c * v (Fin.last (m + 1))) • (Pi.single 0 1 : Fin (m + 2) → K) := by
  rw [eichlerMatrix_mulVec, gramForm_trv_single_left, trvPerm_zero]

theorem gramForm_trv_smul_single_left (t : K) (i : Fin (m + 2)) (v : Fin (m + 2) → K) :
    gramForm h (trvGram K m) (t • (Pi.single i 1 : Fin (m + 2) → K)) v =
      h.bar t * v (trvPerm m i) := by
  rw [map_smulₛₗ, LinearMap.smul_apply, gramForm_trv_single_left, smul_eq_mul]

theorem exists_add_bar_eq {a : K} (ha : h.bar a = a) : ∃ c : K, c + h.bar c = a := by
  obtain ⟨c, hc⟩ := h.traceLin_surjective ⟨a, ha⟩
  refine ⟨c, ?_⟩
  have := congrArg Subtype.val hc
  simpa [UnitaryFieldData.trace] using this

theorem bar_bar_mul_self (t : K) : h.bar (h.bar t * t) = h.bar t * t := by
  rw [map_mul, h.bar_bar, mul_comm]

theorem gramForm_trv_e0el (a b a' b' : K) :
    gramForm h (trvGram K m) (a • (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K) +
        b • (Pi.single (Fin.last (m + 1)) (1 : K) : Fin (m + 2) → K))
      (a' • (Pi.single (0 : Fin (m + 2)) (1 : K) : Fin (m + 2) → K) +
        b' • (Pi.single (Fin.last (m + 1)) (1 : K) : Fin (m + 2) → K)) =
      h.bar a * b' + h.bar b * a' := by
  simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    gramForm_trv_single_left, trvPerm_zero, trvPerm_last]
  simp [Fin.last]
  ring

theorem trv_pointwise (hm : 1 ≤ m) (A : GL (Fin (m + 2)) K)
    (hA : A ∈ primeFormUnitary h (trvGram K m)) (σ : K ≃+* K)
    (hΦ : ∀ (y : Fin (m + 2) → K) (c : K), y (Fin.last (m + 1)) = 0 →
      c + h.bar c = -gramForm h (trvGram K m) y y → ∀ x : Fin (m + 2) → K,
      semilin (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) σ
          (eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c *ᵥ x) =
        eichlerMatrix h (trvGram K m) (Pi.single 0 1) y c *ᵥ
          semilin (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) σ x) :
    (∀ t, σ t = t) ∧ ∃ z d : K, z ≠ 0 ∧ h.norm z = 1 ∧ d + h.bar d = 0 ∧
      (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
        z • (1 + d • Matrix.single 0 (Fin.last (m + 1)) (1 : K)) := by
  set Am : Matrix (Fin (m + 2)) (Fin (m + 2)) K := (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K)
    with hAm
  set Φ : (Fin (m + 2) → K) → (Fin (m + 2) → K) := semilin Am σ with hΦdef
  have Φadd : ∀ x y : Fin (m + 2) → K, Φ (x + y) = Φ x + Φ y := semilin_add Am σ
  have Φsmul : ∀ (t : K) (x : Fin (m + 2) → K), Φ (t • x) = σ t • Φ x := semilin_smul Am σ
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Fin (m + 2) → K, ξ = Φ eₗ := ⟨_, rfl⟩
  have hne : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro e
    have := congrArg Fin.val e
    simp at this
  have hone0 : (1 : Fin (m + 2)) ≠ 0 := by
    intro e
    have := congrArg Fin.val e
    simp at this
  have honeL : (1 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  obtain ⟨η, hη, hη0⟩ := h.exists_mem_traceZero_ne_zero
  have hηb : η + h.bar η = 0 := h.mem_traceZero.mp hη
  have hση : σ η ≠ 0 := fun e => hη0 (σ.injective (by rw [e, map_zero]))
  have hΦ0 : ∀ x : Fin (m + 2) → K,
      σ (η * x (Fin.last (m + 1))) • Φ e₀ = (η * Φ x (Fin.last (m + 1))) • e₀ := by
    intro x
    have h1 := hΦ 0 η (by simp) (by simp [hηb]) x
    rw [eich_apply, eich_apply] at h1
    simp only [smul_zero, add_zero, map_zero, LinearMap.zero_apply, zero_smul, sub_zero] at h1
    rw [Φadd, Φsmul] at h1
    exact add_left_cancel h1
  have hel : eₗ (Fin.last (m + 1)) = 1 := by simp
  obtain ⟨z, hz⟩ : ∃ z : K, Φ e₀ = z • e₀ := by
    refine ⟨(σ η)⁻¹ * (η * ξ (Fin.last (m + 1))), ?_⟩
    have h1 := hΦ0 eₗ
    rw [hel, mul_one, ← hξ] at h1
    calc Φ e₀ = (σ η)⁻¹ • σ η • Φ e₀ := by rw [smul_smul, inv_mul_cancel₀ hση, one_smul]
      _ = _ := by rw [h1, smul_smul]
  have hAinj : ∀ v : Fin (m + 2) → K, Am *ᵥ v = 0 → v = 0 := by
    intro v hv
    have hAi : (↑(A⁻¹) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) * Am = 1 := by
      rw [hAm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc v = (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) K) *ᵥ v := (one_mulVec v).symm
      _ = (↑(A⁻¹) * Am) *ᵥ v := by rw [hAi]
      _ = 0 := by rw [← mulVec_mulVec, hv, mulVec_zero]
  have hΦe0 : Φ e₀ = Am *ᵥ e₀ := semilin_single Am σ 0
  have hz0 : z ≠ 0 := by
    intro e
    have h2 : Am *ᵥ e₀ = 0 := by rw [← hΦe0, hz, e, zero_smul]
    have h3 := congrFun (hAinj _ h2) 0
    simp at h3
  have hex : ∀ t : K, ∃ c : K, c + h.bar c = -(h.bar t * t) := fun t =>
    exists_add_bar_eq h (by rw [map_neg, bar_bar_mul_self h t])
  have hS3 : ∀ i : Fin (m + 2), i ≠ 0 → i ≠ Fin.last (m + 1) → ∀ t c : K,
      c + h.bar c = -(h.bar t * t) →
      Φ (t • (Pi.single i 1 : Fin (m + 2) → K)) =
        (ξ (Fin.last (m + 1)) * t) • (Pi.single i 1 : Fin (m + 2) → K) +
          (c * ξ (Fin.last (m + 1)) - h.bar t * ξ i - σ c * z) • e₀ := by
    intro i hi0 hiL t c hc
    have hy : (t • (Pi.single i 1 : Fin (m + 2) → K)) (Fin.last (m + 1)) = 0 := by
      simp [hiL.symm]
    have hadm : c + h.bar c = -gramForm h (trvGram K m) (t • (Pi.single i 1 : Fin (m + 2) → K))
        (t • (Pi.single i 1 : Fin (m + 2) → K)) := by
      rw [gramForm_trv_smul_single_left, trvPerm_of_mid hi0 hiL]
      simp [hc]
    have h1 := hΦ _ c hy hadm eₗ
    rw [eich_apply, eich_apply] at h1
    have hHe : gramForm h (trvGram K m) (t • (Pi.single i 1 : Fin (m + 2) → K)) eₗ = 0 := by
      rw [gramForm_trv_smul_single_left, trvPerm_of_mid hi0 hiL]
      simp [hiL]
    rw [hHe, hel] at h1
    simp only [one_smul, zero_smul, sub_zero, mul_one] at h1
    rw [Φadd, Φadd, Φsmul c, hz] at h1
    rw [gramForm_trv_smul_single_left, trvPerm_of_mid hi0 hiL, ← hξ] at h1
    funext j
    have h2 := congrFun h1 j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at h2 ⊢
    linear_combination h2
  have hξ0 : ξ (Fin.last (m + 1)) ≠ 0 := by
    intro hξ0
    obtain ⟨c₁, hc₁⟩ := hex 1
    have h1 := hS3 1 hone0 honeL 1 c₁ hc₁
    have hA1 : Φ (Pi.single 1 1) = Am *ᵥ Pi.single 1 1 := semilin_single Am σ 1
    rw [one_smul] at h1
    obtain ⟨κ, hκ⟩ : ∃ κ : K, Φ (Pi.single 1 1 : Fin (m + 2) → K) = κ • e₀ := by
      refine ⟨(c₁ * ξ (Fin.last (m + 1)) - h.bar 1 * ξ 1 - σ c₁ * z), ?_⟩
      rw [h1, hξ0]
      simp
    have h2 : Am *ᵥ ((z • (Pi.single 1 1 : Fin (m + 2) → K)) - κ • e₀) = 0 := by
      rw [mulVec_sub, mulVec_smul, mulVec_smul, ← hA1, ← hΦe0, hκ, hz, smul_smul, smul_smul,
        mul_comm, sub_self]
    have h3 := congrFun (hAinj _ h2) 1
    simp [hone0] at h3
    exact hz0 h3
  have hσ : ∀ t, σ t = t := by
    intro t
    obtain ⟨c, hc⟩ := hex t
    obtain ⟨c₁, hc₁⟩ := hex 1
    have h1 := hS3 1 hone0 honeL t c hc
    have h2 := hS3 1 hone0 honeL 1 c₁ hc₁
    have h3 := congrFun h1 1
    have h4 := congrFun h2 1
    have h5 : Φ (t • (Pi.single 1 1 : Fin (m + 2) → K)) 1 =
        σ t * Φ (1 • (Pi.single 1 1 : Fin (m + 2) → K)) 1 := by
      rw [Φsmul, one_smul]
      rfl
    simp [hone0] at h3 h4
    rw [one_smul] at h5
    have h6 : σ t * ξ (Fin.last (m + 1)) = ξ (Fin.last (m + 1)) * t := by
      rw [← h3, h5, h4]
    exact mul_right_cancel₀ hξ0 (by linear_combination h6)
  have hΦA : ∀ x, Φ x = Am *ᵥ x := by
    intro x
    simp only [hΦdef, semilin]
    congr 1
    funext i
    exact hσ _
  have hξz : ξ (Fin.last (m + 1)) = z := by
    obtain ⟨c, hc⟩ := hex 1
    have hc' : (c + η) + h.bar (c + η) = -(h.bar 1 * 1) := by
      rw [map_add]
      linear_combination hc + hηb
    have h1 := hS3 1 hone0 honeL 1 c hc
    have h2 := hS3 1 hone0 honeL 1 (c + η) hc'
    have h3 := congrFun h1 0
    have h4 := congrFun h2 0
    simp [hone0.symm] at h3 h4
    simp only [hσ] at h3 h4
    have h5 : η * (ξ (Fin.last (m + 1)) - z) = 0 := by
      first | linear_combination h4 - h3 | linear_combination h3 - h4
    exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_left hη0)
  have hξmid : ∀ i : Fin (m + 2), i ≠ 0 → i ≠ Fin.last (m + 1) → ξ i = 0 := by
    intro i hi0 hiL
    obtain ⟨t, ht⟩ := h.exists_bar_ne
    obtain ⟨c, hc⟩ := hex t
    obtain ⟨c₁, hc₁⟩ := hex 1
    have h1 := hS3 i hi0 hiL t c hc
    have h2 := hS3 i hi0 hiL 1 c₁ hc₁
    have h3 := congrFun h1 0
    have h4 := congrFun h2 0
    have h5 : Φ (t • (Pi.single i 1 : Fin (m + 2) → K)) 0 =
        t * Φ (1 • (Pi.single i 1 : Fin (m + 2) → K)) 0 := by
      rw [Φsmul, one_smul, Pi.smul_apply, hσ, smul_eq_mul]
    simp [hi0.symm] at h3 h4
    simp only [hσ, hξz] at h3 h4
    rw [one_smul] at h5
    have h6 : (t - h.bar t) * ξ i = 0 := by
      rw [h3, h4] at h5
      linear_combination h5
    exact (mul_eq_zero.mp h6).resolve_left (sub_ne_zero.mpr (Ne.symm ht))
  have hcol0 : Am *ᵥ e₀ = z • e₀ := hΦe0.symm.trans hz
  have hcolMid : ∀ j : Fin (m + 2), j ≠ 0 → j ≠ Fin.last (m + 1) →
      Am *ᵥ (Pi.single j 1 : Fin (m + 2) → K) = z • Pi.single j 1 := by
    intro j hj0 hjL
    obtain ⟨c₁, hc₁⟩ := hex 1
    have h1 := hS3 j hj0 hjL 1 c₁ hc₁
    rw [one_smul, hΦA, hξz, hξmid j hj0 hjL, hσ c₁] at h1
    rw [h1]
    simp
  obtain ⟨c0, hc0⟩ : ∃ c0 : K, ξ = c0 • e₀ + z • eₗ := by
    refine ⟨ξ 0, ?_⟩
    funext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hj0 : j = 0
    · subst hj0
      simp [hne]
    · by_cases hjL : j = Fin.last (m + 1)
      · subst hjL
        simp [hξz, hne.symm]
      · simp [hξmid j hj0 hjL, hj0, hjL]
  have hcolL : Am *ᵥ eₗ = c0 • e₀ + z • eₗ := by
    rw [← hc0, hξ, hΦA]
  have hH : ∀ x y : Fin (m + 2) → K, gramForm h (trvGram K m) (Am *ᵥ x) (Am *ᵥ y) =
      gramForm h (trvGram K m) x y :=
    (gramForm_isometry_iff h _ _).mpr (mem_primeFormUnitary.mp hA)
  have hn1 : h.bar z * z = 1 := by
    have h1 := hH e₀ eₗ
    have e1 : Am *ᵥ e₀ = z • e₀ + (0 : K) • eₗ := by rw [hcol0, zero_smul, add_zero]
    have e2 : Am *ᵥ eₗ = c0 • e₀ + z • eₗ := hcolL
    rw [e1, e2, gramForm_trv_e0el, gramForm_trv_single_left, trvPerm_zero, hel] at h1
    simpa using h1
  have hn2 : h.bar c0 * z + h.bar z * c0 = 0 := by
    have h1 := hH eₗ eₗ
    rw [hcolL, gramForm_trv_e0el, gramForm_trv_single_left, trvPerm_last] at h1
    simpa [hne] using h1
  have hbz : h.bar z ≠ 0 := fun e => hz0 (by rw [← h.bar_bar z, e, map_zero])
  have hcase : ∀ i : Fin (m + 2),
      i = 0 ∨ i = Fin.last (m + 1) ∨ (i ≠ 0 ∧ i ≠ Fin.last (m + 1)) := by
    intro i
    by_cases h0 : i = 0
    · exact Or.inl h0
    · by_cases hL : i = Fin.last (m + 1)
      · exact Or.inr (Or.inl hL)
      · exact Or.inr (Or.inr ⟨h0, hL⟩)
  have hzd : z * (c0 / z) = c0 := by field_simp
  refine ⟨hσ, z, c0 / z, hz0, ?_, ?_, ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm]
    exact hn1
  · rw [map_div₀]
    have h3 : c0 / z + h.bar c0 / h.bar z = (c0 * h.bar z + h.bar c0 * z) / (z * h.bar z) := by
      field_simp
    rw [h3, show c0 * h.bar z + h.bar c0 * z = 0 by linear_combination hn2, zero_div]
  · ext i j
    have hcol : Am i j = (Am *ᵥ (Pi.single j 1 : Fin (m + 2) → K)) i := by
      rw [mulVec_single_one, col_apply]
    rw [hcol]
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
      smul_eq_mul]
    rcases hcase j with rfl | rfl | ⟨hj0, hjL⟩
    · rw [hcol0]
      rcases hcase i with rfl | rfl | ⟨hi0, hiL⟩
      · simp
      · simp [hne.symm]
      · simp [hi0, hi0.symm]
    · rw [hcolL]
      rcases hcase i with rfl | rfl | ⟨hi0, hiL⟩
      · simp [hne, hzd]
      · simp [hne.symm]
      · simp [hi0, hi0.symm, hiL]
    · rw [hcolMid j hj0 hjL]
      rcases hcase i with rfl | rfl | ⟨hi0, hiL⟩
      · simp [hj0.symm, hjL.symm]
      · simp [hjL.symm]
      · by_cases hij : i = j
        · subst hij
          simp [hi0.symm]
        · simp [hij, hi0.symm]

end Pointwise

end CFSG.RankThree.PartOne.KCUnitaryTrv
