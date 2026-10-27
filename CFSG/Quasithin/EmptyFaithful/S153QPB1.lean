module

public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherTypePreserving

public section

namespace CFSG.Quasithin.QP

open Matrix Module CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBHigherLinearAction

section Alg

variable {F : Type} [Field F] {n : ℕ}

theorem mul_single_mul_apply (M N : Matrix (Fin n) (Fin n) F) (i j : Fin n) (c : F) (a b : Fin n) :
    (M * Matrix.single i j c * N) a b = M a i * c * N j b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_single_apply_same c i j a M]
  · intro k _ hk
    rw [Matrix.mul_single_apply_of_ne c i j a k hk M, zero_mul]
  · simp

theorem map_transvection (σ : F ≃+* F) (i j : Fin n) (c : F) :
    (Matrix.transvection i j c).map σ = Matrix.transvection i j (σ c) := by
  ext a b
  simp [Matrix.transvection, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tv_apply_ne {i j : Fin n} (h : i ≠ j) (x : F) :
    ((SpecialLinearGroup.transvection h x : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = x := by
  show (Matrix.transvection i j x) i j = x
  simp [Matrix.transvection, h]

theorem tv_mul_self [CharP F 2] {i j : Fin n} (h : i ≠ j) (x : F) :
    SpecialLinearGroup.transvection h x * SpecialLinearGroup.transvection h x = 1 := by
  apply Subtype.ext
  show Matrix.transvection i j x * Matrix.transvection i j x = 1
  rw [Matrix.transvection_mul_transvection_same i j h, CharTwo.add_self_eq_zero, Matrix.transvection_zero]

theorem eq_one_of_mem_scalars_sq [CharP F 2] (i : Fin n) {z : SpecialLinearGroup (Fin n) F}
    (hz : z ∈ scalars n F) (h : z * z = 1) : z = 1 := by
  obtain ⟨c, -, hc⟩ := mem_scalars.1 hz
  have h1 : ((z * z : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
    rw [h]
    simp
  rw [Matrix.SpecialLinearGroup.coe_mul, hc, ← map_mul] at h1
  simp at h1
  have h2 : ((c : F) - 1) ^ 2 = 0 := by
    have : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination h1 + (1 - (c : F)) * this
  have h3 : (c : F) = 1 := by
    have := pow_eq_zero_iff (two_ne_zero) |>.1 h2
    linear_combination this
  apply Subtype.ext
  rw [hc, h3]
  simp

end Alg

section Sigma

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem sigma_eq_of_entry (i j : Fin n) (h : i ≠ j)
    (φ : MulAut (SpecialLinearGroup (Fin n) F)) (A : GL (Fin n) F) (σ : F ≃+* F)
    (hφ : ∀ g : SpecialLinearGroup (Fin n) F, ∃ z ∈ scalars n F,
      φ g = z * slConjugation n F A (SpecialLinearGroup.map σ.toRingHom g))
    (hentry : ∀ x : F, ((φ (SpecialLinearGroup.transvection h x) : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) i j = x) : ∀ x, σ x = x := by
  have key : ∀ y : F, σ y * ((A.val i i) * ((A⁻¹).val j j)) = y := by
    intro y
    obtain ⟨z, hz, hzφ⟩ := hφ (SpecialLinearGroup.transvection h y)
    have hTT := tv_mul_self h y
    set w := slConjugation n F A (SpecialLinearGroup.map σ.toRingHom
      (SpecialLinearGroup.transvection h y)) with hw
    have hz2 : z * z = 1 := by
      have h1 : φ (SpecialLinearGroup.transvection h y) * φ (SpecialLinearGroup.transvection h y) = 1 := by
        rw [← map_mul, hTT, map_one]
      have h2 : w * w = 1 := by
        rw [hw, ← map_mul, ← map_mul, hTT, map_one, map_one]
      have hc : w * z = z * w := (Subgroup.mem_center_iff.1 (scalars_le_center n F hz) w)
      rw [hzφ] at h1
      calc z * z = z * z * (w * w) := by rw [h2, mul_one]
        _ = z * (z * w) * w := by group
        _ = z * (w * z) * w := by rw [hc]
        _ = (z * w) * (z * w) := by group
        _ = 1 := h1
    have hz1 : z = 1 := eq_one_of_mem_scalars_sq i hz hz2
    rw [hz1, one_mul] at hzφ
    have hmat : ((φ (SpecialLinearGroup.transvection h y) : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = A.val * Matrix.transvection i j (σ y) * (A⁻¹).val := by
      rw [hzφ, hw, slConjugation_matrix]
      congr 2
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact map_transvection σ i j y
    have hMN : A.val * (A⁻¹).val = 1 := Units.mul_inv A
    have h3 := hentry y
    rw [hmat, Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.add_apply,
      hMN, mul_single_mul_apply] at h3
    simp only [Matrix.one_apply_ne h, zero_add] at h3
    linear_combination h3
  have h1 : (A.val i i) * ((A⁻¹).val j j) = 1 := by
    have := key 1
    rwa [map_one, one_mul] at this
  intro x
  have := key x
  rwa [h1, mul_one] at this

end Sigma

section Dichotomy

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_conjAut_fieldAut (hn : 3 ≤ n) {W : Submodule F (Fin n → F)}
    (hW : finrank F W = 1 ∨ finrank F W = n - 1) (α : MulAut (projectiveSL n F))
    (hα : (projStabilizer W).map (α : projectiveSL n F →* projectiveSL n F) = projStabilizer W) :
    ∃ (A : GL (Fin n) F) (σ : F ≃+* F), α = conjAut n F A * fieldAut n F σ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hbip, -, -, -, -, haut⟩ := incidence_graph (K := F) 2 hn
  obtain ⟨hE, -, -, -, -⟩ := intrinsic_extremal_parabolics (K := F) 2 hn
  have hmemL : ∀ L : Submodule F (Fin n → F), finrank F L = 1 →
      projStabilizer L ∈ extremalParabolics (projectiveSL n F) 2 := fun L hL => by
    rw [hE]
    exact Or.inl ⟨L, hL, rfl⟩
  have hmemH : ∀ H : Submodule F (Fin n → F), finrank F H = n - 1 →
      projStabilizer H ∈ extremalParabolics (projectiveSL n F) 2 := fun H hH => by
    rw [hE]
    exact Or.inr ⟨H, hH, rfl⟩
  obtain ⟨Φ, hΦ, hpres⟩ := haut α
  have hdisj : Disjoint (pointVertices n F 2) (hyperplaneVertices n F 2) := hbip.1
  have hpp : ∀ M, M ∈ pointVertices n F 2 → Φ M ∈ pointVertices n F 2 := by
    rcases hW with hW1 | hWn
    · rcases hpres with ⟨hpp, -⟩ | ⟨hph, -⟩
      · exact hpp
      · exfalso
        let M₀ : extremalParabolics (projectiveSL n F) 2 := ⟨projStabilizer W, hmemL W hW1⟩
        have h1 : Φ M₀ ∈ hyperplaneVertices n F 2 := hph M₀ ⟨W, hW1, rfl⟩
        have h2 : Φ M₀ ∈ pointVertices n F 2 := ⟨W, hW1, by rw [hΦ]; exact hα⟩
        exact Set.disjoint_left.mp hdisj h2 h1
    · rcases hpres with ⟨hpp, -⟩ | ⟨-, hhp⟩
      · exact hpp
      · exfalso
        let M₀ : extremalParabolics (projectiveSL n F) 2 := ⟨projStabilizer W, hmemH W hWn⟩
        have h1 : Φ M₀ ∈ pointVertices n F 2 := hhp M₀ ⟨W, hWn, rfl⟩
        have h2 : Φ M₀ ∈ hyperplaneVertices n F 2 := ⟨W, hWn, by rw [hΦ]; exact hα⟩
        exact Set.disjoint_left.mp hdisj h1 h2
  exact type_preserving_automorphisms hn α fun L hL => by
    obtain ⟨L', hL', hL'eq⟩ := hpp ⟨_, hmemL L hL⟩ ⟨L, hL, rfl⟩
    rw [hΦ] at hL'eq
    exact ⟨L', hL', hL'eq⟩

end Dichotomy

section Entry

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
theorem mulVec_mul_inv_mulVec {n : ℕ} (a b : SpecialLinearGroup (Fin n) F) (v : Fin n → F) :
    ((a * b⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
      ((b : Matrix (Fin n) (Fin n) F) *ᵥ v) = (a : Matrix (Fin n) (Fin n) F) *ᵥ v := by
  rw [mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

omit [Finite F] [CharP F 2] in
theorem radU_le_stabilizer {n : ℕ} (W : Submodule F (Fin n → F)) : radU F W ≤ stabilizer W := by
  intro r hr
  apply mem_stabilizer_of_map_le
  rintro _ ⟨w, hw, rfl⟩
  rw [mulVecLin_apply]
  have := hr.2 w hw
  simp only [this]
  exact hw

omit [CharP F 2] in
theorem map_stabilizer_eq_of_trivial_mod_radU {n : ℕ} (W : Submodule F (Fin n → F))
    (φ : MulAut (SpecialLinearGroup (Fin n) F))
    (hφ : ∀ p ∈ stabilizer W, φ p * p⁻¹ ∈ radU F W) :
    (stabilizer W).map (φ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) =
      stabilizer W := by
  have hle : (stabilizer W).map (φ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) ≤
      stabilizer W := by
    rintro _ ⟨p, hp, rfl⟩
    have e : φ p = (φ p * p⁻¹) * p := by group
    show φ p ∈ stabilizer W
    rw [e]
    exact mul_mem (radU_le_stabilizer W (hφ p hp)) hp
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective φ.injective])

omit [Finite F] [CharP F 2] in
theorem tv12_mem_stabilizer (x : F) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) x ∈
      stabilizer (flagSpace 3 F 1) := by
  apply mem_stabilizer_of_map_le
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply]
  show (Matrix.transvection (1 : Fin 3) 2 x) *ᵥ v ∈ _
  rw [transvection_mulVec]
  have hv' : v ∈ flagSpace 3 F 1 := hv
  rw [mem_flagSpace] at hv' ⊢
  intro k hk
  have hvk := hv' k hk
  simp only [Pi.add_apply, hvk, zero_add, Pi.single_apply]
  split_ifs with h
  · subst h
    rw [hv' 2 (by decide), mul_zero]
  · rfl

omit [Finite F] [CharP F 2] in
theorem tv01_mem_stabilizer (x : F) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) x ∈
      stabilizer (flagSpace 3 F 2) := by
  apply mem_stabilizer_of_map_le
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply]
  show (Matrix.transvection (0 : Fin 3) 1 x) *ᵥ v ∈ _
  rw [transvection_mulVec]
  have hv' : v ∈ flagSpace 3 F 2 := hv
  rw [mem_flagSpace] at hv' ⊢
  intro k hk
  have hvk := hv' k hk
  simp only [Pi.add_apply, hvk, zero_add, Pi.single_apply]
  split_ifs with h
  · subst h
    exact absurd hk (by decide)
  · rfl

end Entry

section Sigma3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem sigma_eq_refl {d : ℕ} (hd : d = 1 ∨ d = 2)
    (φ : MulAut (SpecialLinearGroup (Fin 3) F)) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (hφ : ∀ p ∈ stabilizer (flagSpace 3 F d), φ p * p⁻¹ ∈ radU F (flagSpace 3 F d))
    (hsc : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ z ∈ scalars 3 F,
      φ g = z * slConjugation 3 F A (SpecialLinearGroup.map σ.toRingHom g)) :
    σ = RingEquiv.refl F := by
  apply RingEquiv.ext
  rcases hd with rfl | rfl
  ·
    refine sigma_eq_of_entry (1 : Fin 3) 2 (by decide) φ A σ hsc fun x => ?_
    have hr := (mem_radU.1 (hφ _ (tv12_mem_stabilizer x))).1
      (((SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) x : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 2 1)
    rw [mulVec_mul_inv_mulVec] at hr
    have h1 := mem_flagSpace.1 hr 1 (le_refl _)
    simp at h1
    rw [tv_apply_ne] at h1
    linear_combination h1
  ·
    refine sigma_eq_of_entry (0 : Fin 3) 1 (by decide) φ A σ hsc fun x => ?_
    have hT := tv01_mem_stabilizer x
    have he : (Pi.single 1 1 : Fin 3 → F) ∈ flagSpace 3 F 2 := by
      rw [mem_flagSpace]
      intro k hk
      have : k ≠ 1 := fun h => by subst h; exact absurd hk (by decide)
      simp [this]
    have hw : ((SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) x :
        SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ Pi.single 1 1 ∈ flagSpace 3 F 2 := by
      have h := mem_stabilizer.1 hT
      rw [← h]
      exact Submodule.mem_map_of_mem (f := mulVecLin _) he
    have hr := (mem_radU.1 (hφ _ hT)).2 _ hw
    rw [mulVec_mul_inv_mulVec] at hr
    have h1 := congrFun hr 0
    simp at h1
    rw [tv_apply_ne] at h1
    exact h1

end Sigma3

section Final

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem eq_of_forall_mul_inv_mem_center {Γ : Type*} [Group Γ] (hperf : commutator Γ = ⊤)
    (ψ : MulAut Γ) (hz : ∀ a : Γ, a * (ψ a)⁻¹ ∈ Subgroup.center Γ) (a : Γ) : ψ a = a := by
  let z : Γ →* Γ :=
    { toFun := fun a => a * (ψ a)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := Subgroup.mem_center_iff.mp (hz b)
        have ha := Subgroup.mem_center_iff.mp (hz a)
        simp only [map_mul, _root_.mul_inv_rev]
        calc a * b * ((ψ b)⁻¹ * (ψ a)⁻¹) = a * (b * (ψ b)⁻¹) * (ψ a)⁻¹ := by group
          _ = (b * (ψ b)⁻¹) * a * (ψ a)⁻¹ := by rw [hb a]
          _ = (b * (ψ b)⁻¹) * (a * (ψ a)⁻¹) := by group
          _ = (a * (ψ a)⁻¹) * (b * (ψ b)⁻¹) := ha _ }
  have hzdef : ∀ a, z a = a * (ψ a)⁻¹ := fun _ => rfl
  have hker : (⊤ : Subgroup Γ) ≤ z.ker := by
    rw [← hperf, commutator_def Γ]
    refine Subgroup.commutator_le.mpr fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have hc : z g₁ * z g₂ = z g₂ * z g₁ := (Subgroup.mem_center_iff.mp (hz g₁) (z g₂)).symm
    rw [hc]
    group
  have h1 := hker (Subgroup.mem_top a)
  rw [MonoidHom.mem_ker, hzdef, mul_inv_eq_one] at h1
  exact h1.symm

end Final

section Det

variable {K : Type} [Field K]

theorem exists_conj_of_slConjugation_pow_five (A : GL (Fin 3) K)
    (h5 : slConjugation 3 K (A ^ 5) = 1) :
    ∃ g : SpecialLinearGroup (Fin 3) K, ∀ x, slConjugation 3 K A x = g * x * g⁻¹ := by
  classical
  set M : Matrix (Fin 3) (Fin 3) K := ((A ^ 5 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hcomm : ∀ g : SpecialLinearGroup (Fin 3) K, Commute (g : Matrix (Fin 3) (Fin 3) K) M := by
    intro g
    have h1 := congrArg (fun a : MulAut (SpecialLinearGroup (Fin 3) K) =>
      (a g : Matrix (Fin 3) (Fin 3) K)) h5
    simp only [MulAut.one_apply] at h1
    rw [slConjugation_matrix] at h1
    have hAinv : ((A ^ 5)⁻¹ : GL (Fin 3) K).val * (A ^ 5 : GL (Fin 3) K).val = 1 := Units.inv_mul _
    show (g : Matrix (Fin 3) (Fin 3) K) * M = M * (g : Matrix (Fin 3) (Fin 3) K)
    calc (g : Matrix (Fin 3) (Fin 3) K) * M
        = (M * (g : Matrix (Fin 3) (Fin 3) K) * ((A ^ 5)⁻¹ : GL (Fin 3) K).val) * M := by
          rw [hM, h1]
      _ = M * (g : Matrix (Fin 3) (Fin 3) K) * (((A ^ 5)⁻¹ : GL (Fin 3) K).val * M) := by
          rw [Matrix.mul_assoc]
      _ = M * (g : Matrix (Fin 3) (Fin 3) K) := by rw [hM, hAinv, Matrix.mul_one]
  obtain ⟨lam, hlam⟩ := Matrix.mem_range_scalar_of_commute_transvectionStruct
    (fun t => hcomm (SpecialLinearGroup.transvection t.hij t.c))
  have hdet : (A.val.det) ^ 5 = lam ^ 3 := by
    have h1 : M.det = (A.val.det) ^ 5 := by
      rw [hM, Units.val_pow_eq_pow_val, Matrix.det_pow]
    rw [← h1, ← hlam]
    simp [Matrix.scalar_apply, Matrix.det_diagonal]
  have hD0 : A.val.det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det A).ne_zero
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h] at hdet
    simp at hdet
    exact hD0 hdet
  set D := A.val.det with hD
  set μ : K := D ^ 2 / lam with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero (pow_ne_zero 2 hD0) hlam0
  have hμ3 : μ ^ 3 = D := by
    rw [hμ, div_pow, ← pow_mul, show (2 * 3 : ℕ) = 6 by rfl]
    field_simp
    rw [← hdet]
  have hdetinv : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = D⁻¹ := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, map_inv, Units.val_inv_eq_inv_val,
      Matrix.GeneralLinearGroup.val_det_apply]
  let g₀ : SpecialLinearGroup (Fin 3) K :=
    ⟨μ⁻¹ • A.val, by
      rw [Matrix.det_smul, Fintype.card_fin, inv_pow, hμ3]
      exact inv_mul_cancel₀ hD0⟩
  let h₀ : SpecialLinearGroup (Fin 3) K :=
    ⟨μ • ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), by
      rw [Matrix.det_smul, Fintype.card_fin, hμ3, hdetinv]
      exact mul_inv_cancel₀ hD0⟩
  have hgh : g₀ * h₀ = 1 := by
    apply Subtype.ext
    show (μ⁻¹ • A.val) * (μ • ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) = 1
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul, Units.mul_inv]
  have hinv : g₀⁻¹ = h₀ := inv_eq_of_mul_eq_one_right hgh
  refine ⟨g₀, fun x => ?_⟩
  rw [hinv]
  apply Subtype.ext
  rw [slConjugation_matrix, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show A.val * (x : Matrix (Fin 3) (Fin 3) K) * ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    (μ⁻¹ • A.val) * (x : Matrix (Fin 3) (Fin 3) K) * (μ • ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hμ0, one_smul]

end Det

section Main

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem exists_conj_of_trivial_mod_radU {d : ℕ} (hd : d = 1 ∨ d = 2)
    (φ : MulAut (SpecialLinearGroup (Fin 3) F)) (hφ5 : φ ^ 5 = 1)
    (hφ : ∀ p ∈ stabilizer (flagSpace 3 F d), φ p * p⁻¹ ∈ radU F (flagSpace 3 F d)) :
    ∃ g : SpecialLinearGroup (Fin 3) F, ∀ x, φ x = g * x * g⁻¹ := by
  have hW : finrank F (flagSpace 3 F d) = 1 ∨ finrank F (flagSpace 3 F d) = 3 - 1 := by
    rcases hd with rfl | rfl
    · exact Or.inl (finrank_flagSpace (by norm_num))
    · exact Or.inr (finrank_flagSpace (by norm_num))
  have hα : (projStabilizer (flagSpace 3 F d)).map
      (descendAut 3 F φ : projectiveSL 3 F →* projectiveSL 3 F) = projStabilizer (flagSpace 3 F d) := by
    rw [map_projStabilizer_descendAut, map_stabilizer_eq_of_trivial_mod_radU _ φ hφ]
    rfl
  obtain ⟨A, σ, hασ⟩ := exists_conjAut_fieldAut (by norm_num) hW (descendAut 3 F φ) hα
  have hsc : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ z ∈ scalars 3 F,
      φ g = z * slConjugation 3 F A (SpecialLinearGroup.map σ.toRingHom g) := by
    intro g
    have h1 := congrArg (fun a : MulAut (projectiveSL 3 F) => a (proj 3 F g)) hασ
    simp only [MulAut.mul_apply, descendAut_proj, conjAut_proj, fieldAut_proj] at h1
    set w := slConjugation 3 F A (SpecialLinearGroup.map σ.toRingHom g) with hw
    have h2 : (φ g)⁻¹ * w ∈ scalars 3 F := proj_eq_proj_iff.1 h1
    have h3 : w⁻¹ * φ g ∈ scalars 3 F := by simpa using inv_mem h2
    refine ⟨w⁻¹ * φ g, h3, ?_⟩
    have hc : w * (w⁻¹ * φ g) = (w⁻¹ * φ g) * w :=
      Subgroup.mem_center_iff.1 (scalars_le_center 3 F h3) w
    rw [← hc]
    group
  have hσ := sigma_eq_refl hd φ A σ hφ hsc
  subst hσ
  have hsc' : ∀ g : SpecialLinearGroup (Fin 3) F, ∃ z ∈ scalars 3 F,
      φ g = z * slConjugation 3 F A g := by
    intro g
    obtain ⟨z, hz, h⟩ := hsc g
    refine ⟨z, hz, ?_⟩
    rw [h]
    congr 2
  have hperf : commutator (SpecialLinearGroup (Fin 3) F) = ⊤ :=
    (CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := F) (n := 3) le_rfl).commutator_eq_top
  have hφA : ∀ x, φ x = slConjugation 3 F A x := by
    have key := eq_of_forall_mul_inv_mem_center hperf (φ * (slConjugation 3 F A)⁻¹) (fun a => by
      obtain ⟨z, hz, h⟩ := hsc' ((slConjugation 3 F A)⁻¹ a)
      have h2 : (φ * (slConjugation 3 F A)⁻¹) a = z * a := by
        rw [MulAut.mul_apply, h, MulAut.apply_inv_self]
      rw [h2]
      have : a * (z * a)⁻¹ = z⁻¹ := by group
      rw [this]
      exact inv_mem (scalars_le_center 3 F hz))
    intro x
    have := key (slConjugation 3 F A x)
    rwa [MulAut.mul_apply, MulAut.inv_apply_self] at this
  have hφeq : φ = slConjugation 3 F A := MulEquiv.ext hφA
  have h5 : slConjugation 3 F (A ^ 5) = 1 := by
    rw [map_pow, ← hφeq, hφ5]
  obtain ⟨g, hg⟩ := exists_conj_of_slConjugation_pow_five A h5
  exact ⟨g, fun x => by rw [hφA, hg]⟩

end Main

end CFSG.Quasithin.QP
