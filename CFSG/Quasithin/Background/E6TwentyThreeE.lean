module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Dickson
public import CFSG.Quasithin.Background.C2Six
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesConfining

public section

namespace CFSG.Quasithin.E6.A3Push

open Matrix MatrixGroups Matrix.SpecialLinearGroup CFSG.QuasithinUnique.Lin2

section SL2

variable {F : Type*} [Field F]

theorem eq_slUpper_of_commute (h2 : (2 : F) = 0) {A : SL(2, F)}
    (hA : A * slUpper 1 = slUpper 1 * A) :
    A = slUpper ((A : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have h := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) hA
  simp only [coe_mul, slUpper_val] at h
  have h00 := congrFun (congrFun h 0) 0
  have h01 := congrFun (congrFun h 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -h01
  have hdet := A.property
  rw [Matrix.det_fin_two, h00, h11, mul_zero, sub_zero] at hdet
  have ha : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have hsq : ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) ^ 2 = 0 := by
      linear_combination hdet + (1 - (A : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slUpper_val, h00, h11, ha]

theorem fix_of_apply_one_zero (h2 : (2 : F) = 0) (φ : SL(2, F) →* SL(2, F))
    (h3 : ∀ A, φ (φ (φ A)) = A) (hU : ∀ c : F, φ (slUpper c) = slUpper c)
    {A : SL(2, F)} (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) : φ A = A := by
  have hconj := conj_slUpper_of_apply_one_zero A hA 1
  have hφ : φ A * slUpper 1 * (φ A)⁻¹ = A * slUpper 1 * A⁻¹ := by
    have := congrArg φ hconj
    simp only [map_mul, map_inv, hU] at this
    rw [this, hconj]
  have hB : A⁻¹ * φ A * slUpper 1 = slUpper 1 * (A⁻¹ * φ A) := by
    have h' : A⁻¹ * (φ A * slUpper 1 * (φ A)⁻¹) * φ A = A⁻¹ * (A * slUpper 1 * A⁻¹) * φ A := by
      rw [hφ]
    simpa [mul_assoc] using h'
  have hBeq := eq_slUpper_of_commute h2 hB
  set d := ((A⁻¹ * φ A : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 1
  have hφA : φ A = A * slUpper d := by
    rw [← hBeq]
    group
  have hφφ : φ (φ A) = A := by
    rw [hφA, map_mul, hU, hφA, mul_assoc, ← slUpper_add]
    have : d + d = 0 := by linear_combination d * h2
    rw [this, slUpper_zero, mul_one]
  have h := h3 A
  rw [hφφ] at h
  exact h

@[expose] def slDiag (μ : F) (hμ : μ ≠ 0) : SL(2, F) :=
  ⟨!![μ, 0; 0, μ⁻¹], by simp [Matrix.det_fin_two, hμ]⟩

theorem slDiag_val (μ : F) (hμ : μ ≠ 0) :
    (slDiag μ hμ : Matrix (Fin 2) (Fin 2) F) = !![μ, 0; 0, μ⁻¹] := rfl

theorem fix_slWeyl_one (h2 : (2 : F) = 0) {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (φ : SL(2, F) →* SL(2, F))
    (h3 : ∀ A, φ (φ (φ A)) = A) (hU : ∀ c : F, φ (slUpper c) = slUpper c) :
    φ (slWeyl 1 one_ne_zero) = slWeyl 1 one_ne_zero := by
  set W := slWeyl (1 : F) one_ne_zero with hW
  set D := φ W with hD
  have hT : W * slDiag μ hμ0 * W⁻¹ = slDiag μ⁻¹ (inv_ne_zero hμ0) := by
    apply Subtype.ext
    change ((W * slDiag μ hμ0 * W⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (slDiag μ⁻¹ (inv_ne_zero hμ0) : Matrix (Fin 2) (Fin 2) F)
    rw [coe_mul, coe_mul, coe_inv, hW, slWeyl_val, slDiag_val, slDiag_val]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  have hfixT : ∀ (ν : F) (hν : ν ≠ 0), φ (slDiag ν hν) = slDiag ν hν := fun ν hν =>
    fix_of_apply_one_zero h2 φ h3 hU (by simp [slDiag_val])
  have hDT : D * slDiag μ hμ0 = slDiag μ⁻¹ (inv_ne_zero hμ0) * D := by
    have := congrArg φ hT
    rw [map_mul, map_mul, map_inv, hfixT, hfixT] at this
    rw [← this, hD]
    group
  have hDm := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F)) hDT
  simp only [coe_mul] at hDm
  have e00 := congrFun (congrFun hDm 0) 0
  have e11 := congrFun (congrFun hDm 1) 1
  simp [slDiag_val, Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have hμμ : μ - μ⁻¹ ≠ 0 := by
    intro h
    apply hμ1
    have h' : μ * μ = 1 := by
      have : μ = μ⁻¹ := sub_eq_zero.mp h
      calc μ * μ = μ * μ⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel₀ hμ0
    have hsq : (μ - 1) ^ 2 = 0 := by linear_combination h' + (1 - μ) * h2
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
    linear_combination this
  have hD00 : (D : Matrix (Fin 2) (Fin 2) F) 0 0 = 0 := by
    have : (D : Matrix (Fin 2) (Fin 2) F) 0 0 * (μ - μ⁻¹) = 0 := by linear_combination e00
    exact (mul_eq_zero.mp this).resolve_right hμμ
  have hD11 : (D : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    have : (D : Matrix (Fin 2) (Fin 2) F) 1 1 * (μ - μ⁻¹) = 0 := by linear_combination -e11
    exact (mul_eq_zero.mp this).resolve_right hμμ
  have hdet := D.property
  rw [Matrix.det_fin_two, hD00, hD11, zero_mul, zero_sub] at hdet
  have hcube : (W * slUpper 1) ^ 3 = 1 := by
    apply Subtype.ext
    change (((W * slUpper 1) ^ 3 : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [coe_pow, coe_mul, hW, slWeyl_val, slUpper_val]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals linear_combination -h2
  have hcube' : (D * slUpper 1) ^ 3 = 1 := by
    have := congrArg φ hcube
    rwa [map_pow, map_mul, hU, map_one] at this
  have hc := congrArg (fun B : SL(2, F) => (B : Matrix (Fin 2) (Fin 2) F) 0 0) hcube'
  simp only [coe_pow, coe_mul, coe_one, slUpper_val] at hc
  simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, hD00, hD11] at hc
  have hD10 : (D : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    linear_combination -hc - (D : Matrix (Fin 2) (Fin 2) F) 1 0 * hdet - h2
  have hD01 : (D : Matrix (Fin 2) (Fin 2) F) 0 1 = -1 := by
    rw [hD10, mul_one] at hdet
    linear_combination -hdet
  apply Subtype.ext
  rw [hW, slWeyl_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hD00, hD11, hD10, hD01]

theorem eq_of_fix_slUni (h2 : (2 : F) = 0) {μ : F} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (φ : SL(2, F) →* SL(2, F))
    (h3 : ∀ A, φ (φ (φ A)) = A) (hU : ∀ c : F, φ (slUpper c) = slUpper c) (A : SL(2, F)) :
    φ A = A := by
  by_cases hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · exact fix_of_apply_one_zero h2 φ h3 hU hA
  have hW := fix_slWeyl_one h2 hμ0 hμ1 φ h3 hU
  have hwc : ∀ (c : F) (hc : c ≠ 0), φ (slWeyl c hc) = slWeyl c hc := by
    intro c hc
    have hup : (((slWeyl (1 : F) one_ne_zero)⁻¹ * slWeyl c hc : SL(2, F)) :
        Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      rw [coe_mul, coe_inv, slWeyl_val, slWeyl_val]
      simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    have := fix_of_apply_one_zero h2 φ h3 hU hup
    rw [map_mul, map_inv, hW] at this
    have h' := congrArg (fun B => slWeyl (1 : F) one_ne_zero * B) this
    simpa using h'
  rw [eq_slUpper_mul_slWeyl_mul_slUpper A hA, map_mul, map_mul, hU, hU, hwc]

theorem eq_of_fix_sylow [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m) (hm : 1 < m)
    {P : Subgroup SL(2, F)} (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤)
    (φ : SL(2, F) →* SL(2, F)) (h3 : ∀ A, φ (φ (φ A)) = A) (hfix : ∀ A ∈ P, φ A = A)
    (A : SL(2, F)) : φ A = A := by
  classical
  have h2 : (2 : F) = 0 := by
    have h := FiniteField.cast_card_eq_zero F
    rw [hF, Nat.cast_pow, Nat.cast_ofNat] at h
    exact pow_eq_zero_iff (by omega) |>.mp h
  obtain ⟨μ, hμ0, hμ1⟩ : ∃ μ : F, μ ≠ 0 ∧ μ ≠ 1 := by
    by_contra h
    push Not at h
    have hle : Fintype.card F ≤ 2 := by
      calc Fintype.card F = (Finset.univ : Finset F).card := Finset.card_univ.symm
        _ ≤ ({0, 1} : Finset F).card := Finset.card_le_card fun x _ => by
            by_cases hx : x = 0
            · simp [hx]
            · simp [h x hx]
        _ ≤ 2 := Finset.card_le_two
    have : (4 : ℕ) ≤ 2 ^ m := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  obtain ⟨g, -, hg⟩ := (isSylowTwoOf_slUni hF (by omega)).exists_conj hP
  let ψ : SL(2, F) →* SL(2, F) :=
    ((MulAut.conj g⁻¹).toMonoidHom.comp φ).comp (MulAut.conj g).toMonoidHom
  have hψ : ∀ B, ψ B = g⁻¹ * φ (g * B * g⁻¹) * g := by
    intro B
    simp [ψ, MulAut.conj_apply]
  have hψ3 : ∀ B, ψ (ψ (ψ B)) = B := by
    intro B
    simp only [hψ]
    have e : ∀ C, g * (g⁻¹ * C * g) * g⁻¹ = C := fun C => by group
    rw [e, e, h3]
    group
  have hψU : ∀ c : F, ψ (slUpper c) = slUpper c := by
    intro c
    rw [hψ]
    have hmem : g * slUpper c * g⁻¹ ∈ P := by
      rw [hg]
      exact ⟨slUpper c, slUpper_mem_slUni c, by simp [MulAut.conj_apply]⟩
    rw [hfix _ hmem]
    group
  have := eq_of_fix_slUni h2 hμ0 hμ1 ψ hψ3 hψU (g⁻¹ * A * g)
  rw [hψ] at this
  have e1 : g * (g⁻¹ * A * g) * g⁻¹ = A := by group
  rw [e1] at this
  have e2 := congrArg (fun B => g * B * g⁻¹) this
  rw [show g * (g⁻¹ * φ A * g) * g⁻¹ = φ A by group,
    show g * (g⁻¹ * A * g) * g⁻¹ = A by group] at e2
  exact e2


end SL2

section Block

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem conj_mul_inv_mem_pCoreOf_of_sylow {B S : Subgroup G} {x : G}
    {K : Type} [Field K] [Fintype K] {m : ℕ} (hK : Fintype.card K = 2 ^ m) (hm : 1 < m)
    (α : ↥B →* SL(2, K)) (hαs : Function.Surjective α) (hαk : α.ker = CFSG.pCore 2 ↥B)
    (hxB : x ∈ Subgroup.normalizer (B : Set G)) (hx3 : x ^ 3 = 1)
    (hS : IsSylowTwoOf S B) (hSx : ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ pCoreOf 2 B) :
    ∀ b ∈ B, x * b * x⁻¹ * b⁻¹ ∈ pCoreOf 2 B := by
  classical
  have hxB' : ∀ b ∈ B, x * b * x⁻¹ ∈ B := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hxB b).mp hb
  let c : ↥B →* ↥B :=
    { toFun := fun b => ⟨x * b * x⁻¹, hxB' b b.2⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hc : ∀ b : ↥B, ((c b : ↥B) : G) = x * b * x⁻¹ := fun _ => rfl
  have hxO : x ∈ Subgroup.normalizer (pCoreOf 2 B : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 B hxB
  have hker : α.ker ≤ (α.comp c).ker := by
    intro k hk
    rw [hαk] at hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk]
    apply CFSG.Quasithin.C2Six.mem_pCore_two_iff.mpr
    rw [hc]
    exact (Subgroup.mem_normalizer_iff.mp hxO k).mp (CFSG.Quasithin.C2Six.mem_pCore_two_iff.mp hk)
  let φ : SL(2, K) →* SL(2, K) :=
    (α.liftOfRightInverse (Function.surjInv hαs) (Function.rightInverse_surjInv hαs))
      ⟨α.comp c, hker⟩
  have hφ : ∀ b : ↥B, φ (α b) = α (c b) := fun b => by
    have := MonoidHom.liftOfRightInverse_comp_apply α (Function.surjInv hαs)
      (Function.rightInverse_surjInv hαs) ⟨α.comp c, hker⟩ b
    exact this
  have hc3 : ∀ b : ↥B, c (c (c b)) = b := fun b => by
    apply Subtype.ext
    simp only [hc]
    have h3' : x * x * x = 1 := by rw [mul_assoc, ← pow_three, hx3]
    calc x * (x * (x * (b : G) * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * b * (x * x * x)⁻¹ := by
          group
      _ = b := by rw [h3']; group
  have hφ3 : ∀ A, φ (φ (φ A)) = A := by
    intro A
    obtain ⟨b, rfl⟩ := hαs A
    rw [hφ, hφ, hφ, hc3]
  let S' : Subgroup ↥B := S.subgroupOf B
  have hker' : α.ker ≤ S' := by
    intro l hl
    rw [hαk] at hl
    exact CFSG.QuasithinUnique.IsSylowTwoOf.pCoreOf_le hS
      (CFSG.Quasithin.C2Six.mem_pCore_two_iff.mp hl)
  have hS'2 : IsPGroup 2 S' := by
    have e : ↥S' ≃* ↥S := Subgroup.subgroupOfEquivOfLe hS.le
    exact hS.isPGroup.of_equiv e.symm
  let P : Subgroup SL(2, K) := S'.map α
  have hcomap : P.comap α = S' := by
    rw [Subgroup.comap_map_eq]
    exact sup_eq_left.mpr hker'
  have hPsyl : IsSylowTwoOf P ⊤ := by
    refine ⟨le_top, hS'2.map α, ?_⟩
    show ¬ 2 ∣ P.relIndex ⊤
    rw [Subgroup.relIndex_top_right, ← Subgroup.index_comap_of_surjective P hαs, hcomap]
    exact hS.2.2
  have hfix : ∀ A ∈ P, φ A = A := by
    rintro A ⟨s, hs, rfl⟩
    rw [hφ]
    have hmem : c s * s⁻¹ ∈ α.ker := by
      rw [hαk]
      apply CFSG.Quasithin.C2Six.mem_pCore_two_iff.mpr
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hc]
      exact hSx s hs
    have h1 := MonoidHom.mem_ker.mp hmem
    rw [map_mul, map_inv] at h1
    exact mul_inv_eq_one.mp h1
  intro b hb
  have h := eq_of_fix_sylow hK hm hPsyl φ hφ3 hfix (α ⟨b, hb⟩)
  rw [hφ] at h
  have hmem : c ⟨b, hb⟩ * (⟨b, hb⟩ : ↥B)⁻¹ ∈ α.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  rw [hαk] at hmem
  have := CFSG.Quasithin.C2Six.mem_pCore_two_iff.mp hmem
  simpa [hc] using this

end Block

end CFSG.Quasithin.E6.A3Push
