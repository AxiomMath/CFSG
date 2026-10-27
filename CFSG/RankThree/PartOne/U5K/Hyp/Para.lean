module

public import CFSG.RankThree.PartOne.U5K.Hyp.Aut

public noncomputable section

namespace CFSG.RankThree.PartOne.U5K.Hyp

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

abbrev Gam : Type := ↥(semilinearSimilitudes hK 2 1)

@[expose] def Phi : Gam hK →* MulAut (hypPSU hK 2 1) :=
  semilinearAutHom hK (r := 2) (ε := 1) (by norm_num) le_rfl

theorem Phi_surjective : Function.Surjective (Phi hK) :=
  semilinearAutHom_surjective_of_admissible hK (r := 2) (ε := 1) (by norm_num) le_rfl
    (by norm_num) (by omega)

@[expose] def act (x : Gam hK) (g : hypSU hK 2 1) : hypSU hK 2 1 :=
  ⟨x.1.left * glAut x.1.right (g : GL (HypIndex 2 1) K) * x.1.left⁻¹, conj_mem_hypSU x.2 g⟩

variable {hK}

@[expose] def lmat (x : Gam hK) : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
  ((x.1.left : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K)

theorem Phi_apply (x : Gam hK) (g : hypSU hK 2 1) :
    Phi hK x (hypProj hK 2 1 g) = hypProj hK 2 1 (act hK x g) :=
  semilinearAutHom_apply hK (by norm_num) le_rfl x g

theorem Phi_mul_innM_mul_inv (x : Gam hK) (g : hypSU hK 2 1) :
    Phi hK x * innM hK g * (Phi hK x)⁻¹ = innM hK (act hK x g) := by
  ext z
  simp only [MulAut.mul_apply, innM_apply, MulAut.inv_apply]
  set α := Phi hK x
  have h1 : α (hypProj hK 2 1 g) = hypProj hK 2 1 (act hK x g) := Phi_apply x g
  rw [← h1]
  conv_rhs => rw [← α.apply_symm_apply z]
  simp [map_mul, map_inv]

theorem lmat_mul_map (x : Gam hK) (g : hypSU hK 2 1) :
    lmat x * (mat g).map x.1.right = mat (act hK x g) * lmat x := by
  have h1 : (((x.1.left⁻¹ : GL (HypIndex 2 1) K)) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
      lmat x = 1 := by
    rw [lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  change lmat x * (mat g).map x.1.right =
    ((x.1.left * glAut x.1.right (g : GL (HypIndex 2 1) K) * x.1.left⁻¹ : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) * lmat x
  rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, h1, Matrix.mul_one, coe_glAut]
  rfl

theorem act_mul (x : Gam hK) (g g' : hypSU hK 2 1) :
    act hK x (g * g') = act hK x g * act hK x g' := by
  apply Subtype.ext
  change x.1.left * glAut x.1.right (((g * g' : hypSU hK 2 1) : GL (HypIndex 2 1) K)) *
      x.1.left⁻¹ = (x.1.left * glAut x.1.right (g : GL (HypIndex 2 1) K) * x.1.left⁻¹) *
        (x.1.left * glAut x.1.right (g' : GL (HypIndex 2 1) K) * x.1.left⁻¹)
  rw [Subgroup.coe_mul, map_mul]
  group

theorem act_one (x : Gam hK) : act hK x 1 = 1 := by
  apply Subtype.ext
  change x.1.left * glAut x.1.right (((1 : hypSU hK 2 1) : GL (HypIndex 2 1) K)) *
      x.1.left⁻¹ = 1
  rw [Subgroup.coe_one, map_one]
  group

theorem scalar_central {g : hypSU hK 2 1} (hg : g ∈ hypScalars hK 2 1) (y : hypSU hK 2 1) :
    y * g = g * y := by
  obtain ⟨c, -, -, hc⟩ := hg
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hc,
    GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (c : K) (fun r => Commute.all (c : K) r) _).eq.symm

theorem eq_of_innM_eq_of_sq (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {g g' : hypSU hK 2 1}
    (h : innM hK g = innM hK g') (hg : g * g = 1) (hg' : g' * g' = 1) : g = g' := by
  have h1 : innM hK (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have hz := (innM_eq_one_iff hZ).1 h1
  set z := g⁻¹ * g' with hzdef
  have hg'z : g' = g * z := by rw [hzdef]; group
  have hcomm : Commute z g := (scalar_central hz g).symm
  have hz2 : z * z = 1 := by
    have h2 : g' * g' = (g * g) * (z * z) := by
      calc g' * g' = (g * z) * (g * z) := by rw [← hg'z]
        _ = (g * g) * (z * z) := Commute.mul_mul_mul_comm hcomm g z
    rw [hg', hg, one_mul] at h2
    exact h2.symm
  obtain ⟨c, -, hc5, hc⟩ := hz
  have hc2 : c * c = 1 := by
    have := congrArg (fun w : hypSU hK 2 1 => (mat w) (.inl 0) (.inl 0)) hz2
    simp only [mat_mul, mat_one] at this
    have hzm : mat z = Matrix.scalar _ (c : K) := by
      change ((z : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) = _
      rw [hc]
      rfl
    rw [hzm] at this
    simp [Matrix.mul_apply] at this
    exact Units.ext (by simpa using this)
  have hc1 : c = 1 := by
    have h5 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
    have h2 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hc2)
    have : orderOf c ∣ Nat.gcd 5 2 := Nat.dvd_gcd h5 h2
    have h1 : orderOf c = 1 := Nat.dvd_one.1 (by simpa using this)
    exact orderOf_eq_one_iff.1 h1
  have hz1 : z = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [hc, hc1, map_one]
    rfl
  rw [hg'z, hz1, mul_one]

@[expose] def IsParaW (A : Matrix (HypIndex 2 1) (HypIndex 2 1) K) : Prop :=
  (∀ i, A (.inr (.inl 0)) (.inl i) = 0) ∧ ∀ i j, A (.inr (.inr j)) (.inl i) = 0

theorem act_mem_Vsub (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {x : Gam hK}
    (hρ : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))))
    {v : hypSU hK 2 1} (hv : v ∈ Vsub hK) : act hK x v ∈ Vsub hK := by
  have h1 : innM hK (act hK x v) ∈ Vh hK := by
    rw [← Phi_mul_innM_mul_inv]
    exact (Subgroup.mem_normalizer_iff.1 hρ (innM hK v)).1 ⟨v, hv, rfl⟩
  obtain ⟨v', hv', hv'e⟩ := h1
  have hsq : act hK x v * act hK x v = 1 := by rw [← act_mul, Vsub_sq hv, act_one]
  have := eq_of_innM_eq_of_sq hZ hv'e (Vsub_sq hv') hsq
  rw [← this]
  exact hv'

theorem isParaW_of_act_mem {x : Gam hK} (hact : ∀ v ∈ Vsub hK, act hK x v ∈ Vsub hK) :
    IsParaW (lmat x) := by
  have key : ∀ E : Matrix (Fin 2) (Fin 2) K, IsHerm hK E → ∃ Y' : Matrix (Fin 2) (Fin 2) K,
      lmat x * (oddUni hK 0 E).map x.1.right = oddUni hK 0 Y' * lmat x := by
    intro E hE
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub hE
    obtain ⟨-, Y', hY'⟩ := hact v hv
    exact ⟨Y', by rw [← hvm, lmat_mul_map, hY']⟩
  have h0 := key (hermM hK 1 0 0) (hermM_isHerm (by simp) (by simp))
  have h1 := key (hermM hK 0 1 0) (hermM_isHerm (by simp) (by simp))
  obtain ⟨Y0, e0⟩ := h0
  obtain ⟨Y1, e1⟩ := h1
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · have a0 := congrFun (congrFun e0 (.inr (.inl 0))) (.inr (.inr 0))
    have a1 := congrFun (congrFun e1 (.inr (.inl 0))) (.inr (.inr 1))
    fin_cases i
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a0
    · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a1
  · fin_cases j
    · have a0 := congrFun (congrFun e0 (.inr (.inr 0))) (.inr (.inr 0))
      have a1 := congrFun (congrFun e1 (.inr (.inr 0))) (.inr (.inr 1))
      fin_cases i
      · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a0
      · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a1
    · have a0 := congrFun (congrFun e0 (.inr (.inr 1))) (.inr (.inr 0))
      have a1 := congrFun (congrFun e1 (.inr (.inr 1))) (.inr (.inr 1))
      fin_cases i
      · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a0
      · simpa [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, oddUni, hermM] using a1

@[expose] def blkEE (x : Gam hK) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i l => lmat x (.inl i) (.inl l)

@[expose] def blkFF (x : Gam hK) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun j k => lmat x (.inr (.inr j)) (.inr (.inr k))

theorem ef_block {x : Gam hK} {v : hypSU hK 2 1} {Y Y'' : Matrix (Fin 2) (Fin 2) K}
    (hv : mat v = oddUni hK 0 Y) (hv' : mat (act hK x v) = oddUni hK 0 Y'') :
    blkEE x * Y.map x.1.right = Y'' * blkFF x := by
  have h := lmat_mul_map x v
  rw [hv, hv'] at h
  ext i k
  have := congrFun (congrFun h (.inl i)) (.inr (.inr k))
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, oddUni, blkEE, blkFF,
      Fin.sum_univ_two] at this ⊢ <;>
    linear_combination this

theorem det_blkEE_ne_zero {x : Gam hK} (hP : IsParaW (lmat x)) : (blkEE x).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc, hcz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  let v5 : HypIndex 2 1 → K := fun a => match a with
    | .inl i => c i
    | .inr _ => 0
  have h5 : lmat x *ᵥ v5 = 0 := by
    funext p
    rcases p with i | k | j
    · have := congrFun hcz i
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v5, blkEE] at this ⊢
      exact this
    · fin_cases k
      simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v5, hP.1]
    · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, v5, hP.2]
  have h6 : v5 = 0 := by
    have h7 : ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
        lmat x = 1 := by
      rw [lmat, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc v5 = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *ᵥ v5 := by rw [Matrix.one_mulVec]
      _ = (((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) *
          lmat x) *ᵥ v5 := by rw [h7]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, h5, Matrix.mulVec_zero]
  apply hc
  funext i
  have := congrFun h6 (.inl i)
  simpa [v5] using this

theorem hermM_map (σ : K ≃+* K) (y₁ y₂ b : K) :
    (hermM hK y₁ y₂ b).map σ = hermM hK (σ y₁) (σ y₂) (σ b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermM, map_bar_comm hK σ]

theorem sigma_eq_one_of_central (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {x : Gam hK}
    (hρ : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))))
    (hc : ∀ v ∈ Vsub hK, act hK x v = v) : x.1.right = 1 := by
  have hP := isParaW_of_act_mem (fun v hv => act_mem_Vsub hZ hρ hv)
  have hdet := det_blkEE_ne_zero hP
  have key : ∀ Y : Matrix (Fin 2) (Fin 2) K, IsHerm hK Y →
      blkEE x * Y.map x.1.right = Y * blkFF x := by
    intro Y hY
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub hY
    refine ef_block hvm ?_
    rw [hc v hv, hvm]
  set σ := x.1.right with hσ
  have e0 := key (hermM hK 1 0 0) (hermM_isHerm (by simp) (by simp))
  have e1 := key (hermM hK 0 1 0) (hermM_isHerm (by simp) (by simp))
  have e2 : ∀ t : K, blkEE x * (hermM hK 0 0 t).map σ = hermM hK 0 0 t * blkFF x :=
    fun t => key _ (hermM_isHerm (by simp) (by simp))
  rw [hermM_map] at e0 e1
  have a10 := congrFun (congrFun e0 1) 0
  have a00 := congrFun (congrFun e0 0) 0
  have a01 := congrFun (congrFun e1 0) 1
  have a11 := congrFun (congrFun e1 1) 1
  have t1 := congrFun (congrFun (e2 1) 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hermM, blkEE, blkFF] at a10 a00 a01 a11 t1
  have hne : lmat x (.inl 0) (.inl 0) ≠ 0 := by
    intro h0
    apply hdet
    simp [Matrix.det_fin_two, blkEE, h0, a01]
  have hsame : lmat x (Sum.inr (Sum.inr 1)) (Sum.inr (Sum.inr 1)) = lmat x (.inl 0) (.inl 0) :=
    t1.symm
  ext t
  have h2 := congrFun (congrFun (e2 t) 0) 1
  rw [hermM_map] at h2
  simp [Matrix.mul_apply, Fin.sum_univ_two, hermM, blkEE, blkFF, a01, hsame] at h2
  exact mul_left_cancel₀ hne (h2.trans (mul_comm _ _))

section Count

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {x : Gam hK}
  (hρ : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))))

include hZ hρ

@[expose] def chi : Vsub hK →* Vsub hK where
  toFun v := ⟨act hK x v * (v : hypSU hK 2 1)⁻¹,
    mul_mem (act_mem_Vsub hZ hρ v.2) (inv_mem v.2)⟩
  map_one' := by
    apply Subtype.ext
    simp [act_one]
  map_mul' v w := by
    apply Subtype.ext
    change act hK x ((v : hypSU hK 2 1) * w) * ((v : hypSU hK 2 1) * w)⁻¹ =
      (act hK x v * (v : hypSU hK 2 1)⁻¹) * (act hK x w * (w : hypSU hK 2 1)⁻¹)
    have hc : (v : hypSU hK 2 1)⁻¹ * (act hK x w * (w : hypSU hK 2 1)⁻¹) =
        (act hK x w * (w : hypSU hK 2 1)⁻¹) * (v : hypSU hK 2 1)⁻¹ :=
      Vsub_comm (inv_mem v.2) (mul_mem (act_mem_Vsub hZ hρ w.2) (inv_mem w.2))
    rw [act_mul, _root_.mul_inv_rev]
    calc act hK x v * act hK x w * ((w : hypSU hK 2 1)⁻¹ * (v : hypSU hK 2 1)⁻¹)
        = act hK x v * (act hK x w * (w : hypSU hK 2 1)⁻¹) * (v : hypSU hK 2 1)⁻¹ := by group
      _ = (act hK x v * (v : hypSU hK 2 1)⁻¹) * (act hK x w * (w : hypSU hK 2 1)⁻¹) := by
          rw [mul_assoc (act hK x v), hc.symm, ← mul_assoc]

theorem mem_ker_chi {v : Vsub hK} : v ∈ (chi hZ hρ).ker ↔ act hK x v = v := by
  rw [MonoidHom.mem_ker]
  change (⟨act hK x v * (v : hypSU hK 2 1)⁻¹, _⟩ : Vsub hK) = 1 ↔ _
  rw [Subtype.ext_iff]
  change act hK x v * (v : hypSU hK 2 1)⁻¹ = 1 ↔ _
  rw [mul_inv_eq_one]

end Count

section Smul

theorem isHerm_smul {Y : Matrix (Fin 2) (Fin 2) K} (hY : IsHerm hK Y) {t : K}
    (ht : hK.bar t = t) : IsHerm hK (t • Y) := by
  unfold IsHerm at hY ⊢
  have : ((t • Y).map hK.bar)ᵀ = t • (Y.map hK.bar)ᵀ := by
    ext i j; simp [ht]
  rw [this, ← smul_add, hY, smul_zero]

theorem oddUni_zero_smul (t : K) (Y : Matrix (Fin 2) (Fin 2) K) :
    oddUni hK 0 (t • Y) = 1 + t • (oddUni hK 0 Y - 1) := by
  ext p q
  rcases p with i | k | j <;> rcases q with i' | k' | j' <;>
    simp [oddUni, Matrix.one_apply]

theorem oddUni_zero_smul_map (σ : K ≃+* K) {t : K} (ht : σ t = t)
    (Y : Matrix (Fin 2) (Fin 2) K) :
    (oddUni hK 0 (t • Y)).map σ = 1 + t • ((oddUni hK 0 Y).map σ - 1) := by
  ext p q
  rcases p with i | k | j <;> rcases q with i' | k' | j' <;>
    simp [oddUni, Matrix.one_apply, ht]

theorem mat_act_smul (x : Gam hK) {t : K} (ht : x.1.right t = t) {v w : hypSU hK 2 1}
    {Y Y'' : Matrix (Fin 2) (Fin 2) K} (hv : mat v = oddUni hK 0 Y)
    (hv' : mat (act hK x v) = oddUni hK 0 Y'') (hw : mat w = oddUni hK 0 (t • Y)) :
    mat (act hK x w) = oddUni hK 0 (t • Y'') := by
  have h1 := lmat_mul_map x v
  have h2 := lmat_mul_map x w
  rw [hv, hv'] at h1
  rw [hw, oddUni_zero_smul_map x.1.right ht] at h2
  have h3 : mat (act hK x w) * lmat x = (oddUni hK 0 (t • Y'')) * lmat x := by
    rw [← h2, oddUni_zero_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_sub, h1,
      Matrix.add_mul, Matrix.smul_mul, Matrix.sub_mul]
    simp
  have hinv : lmat x * (lmat x)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (x.1.left).isUnit)
  have := congrArg (fun M => M * (lmat x)⁻¹) h3
  simpa [Matrix.mul_assoc, hinv] using this

end Smul

section Count2

variable (hZ : Subgroup.center (hypPSU hK 2 1) = ⊥) {x : Gam hK}
  (hρ : Phi hK x ∈ Subgroup.normalizer (Vh hK : Set (MulAut (hypPSU hK 2 1))))

include hZ hρ

theorem card_ker_chi_le (hσ : x.1.right ≠ 1) (hσF : ∀ c : K, hK.bar c = c → x.1.right c = c) :
    Nat.card (chi hZ hρ).ker ≤ (2 ^ f) ^ 3 := by
  have hcard := Subgroup.card_ker_mul_card_range (chi hZ hρ)
  rw [Nat.card_congr (Equiv.refl _), card_Vsub] at hcard
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v ∈ Vsub hK, act hK x v ≠ v := by
    by_contra hcon
    push Not at hcon
    exact hσ (sigma_eq_one_of_central hZ hρ hcon)
  obtain ⟨-, Y'', hY''⟩ := act_mem_Vsub hZ hρ hv₀V
  obtain ⟨-, Y₀, hY₀⟩ := hv₀V
  have hH : IsHerm hK Y₀ := herm_of_mem_Vsub hY₀
  have hWne : Y'' - Y₀ ≠ 0 := by
    intro h0
    apply hv₀
    apply mat_injective
    rw [hY'', hY₀, sub_eq_zero.1 h0]
  have hsmul : ∀ t : hK.fixedField, IsHerm hK ((t : K) • Y₀) := fun t => isHerm_smul hH t.2
  choose vt hvtV hvtm using fun t : hK.fixedField => exists_mem_Vsub (hsmul t)
  have hmat : ∀ t : hK.fixedField, mat (act hK x (vt t) * (vt t)⁻¹) =
      oddUni hK 0 ((t : K) • Y'' - (t : K) • Y₀) := by
    intro t
    have h1 := mat_act_smul x (hσF t t.2) hY₀ hY'' (hvtm t)
    rw [mat_mul, h1, mat_inv_of_oddUni (hvtm t), oddUni_mul]
    congr 1
    · simp
    · ext i j; simp [vecMulVec]; ring
  have hrange : 2 ^ f ≤ Nat.card (chi hZ hρ).range := by
    let ψ : hK.fixedField → (chi hZ hρ).range := fun t =>
      ⟨chi hZ hρ ⟨vt t, hvtV t⟩, ⟨_, rfl⟩⟩
    have hinj : Function.Injective ψ := by
      intro t t' h
      have h1 := congrArg (fun r : (chi hZ hρ).range => ((r.1 : Vsub hK) : hypSU hK 2 1)) h
      have h2 : mat (act hK x (vt t) * (vt t)⁻¹) = mat (act hK x (vt t') * (vt t')⁻¹) :=
        congrArg mat h1
      rw [hmat, hmat] at h2
      have h3 := (oddUni_inj h2).2
      obtain ⟨i, j, hij⟩ : ∃ i j, (Y'' - Y₀) i j ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hWne (Matrix.ext fun i j => hcon i j)
      have h4 := congrFun (congrFun h3 i) j
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h4
      have h5 : ((t : K) - t') * (Y'' i j - Y₀ i j) = 0 := by linear_combination h4
      rcases mul_eq_zero.1 h5 with h6 | h6
      · exact Subtype.ext (sub_eq_zero.1 h6)
      · exact absurd (by simpa using h6) hij
    calc 2 ^ f = Nat.card hK.fixedField := hK.card_fixedField.symm
      _ ≤ Nat.card (chi hZ hρ).range := Nat.card_le_card_of_injective ψ hinj
  have hmul : Nat.card (chi hZ hρ).ker * 2 ^ f ≤ (2 ^ f) ^ 4 := by
    calc Nat.card (chi hZ hρ).ker * 2 ^ f ≤ Nat.card (chi hZ hρ).ker *
          Nat.card (chi hZ hρ).range := Nat.mul_le_mul_left _ hrange
      _ = (2 ^ f) ^ 4 := hcard
  have hpos : 0 < 2 ^ f := by positivity
  have : Nat.card (chi hZ hρ).ker * 2 ^ f ≤ (2 ^ f) ^ 3 * 2 ^ f := by
    calc _ ≤ (2 ^ f) ^ 4 := hmul
      _ = (2 ^ f) ^ 3 * 2 ^ f := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

end Count2

end CFSG.RankThree.PartOne.U5K.Hyp
