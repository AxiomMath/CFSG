module

public import CFSG.Milestones.ASVolI.F429.C6Sp4
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section U5Model

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.QuasithinUnique
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.BA CFSG.Quasithin.H13.Sec53F.Unit

variable {f : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 f K)

theorem burnsideF429b_U5_proj_injOn {u v : hypSU hK 2 1} (hu : u ∈ hypUnitriangular hK 2 1)
    (hv : v ∈ hypUnitriangular hK 2 1) (h : hypProj hK 2 1 u = hypProj hK 2 1 v) : u = v := by
  have hw : u * v⁻¹ ∈ hypScalars hK 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨c, -, -, hc⟩ := hw
  have hwU : u * v⁻¹ ∈ hypUnitriangular hK 2 1 := mul_mem hu (inv_mem hv)
  have h1 := U_diag hwU (.inl 0)
  have h2 : mat (u * v⁻¹) (.inl 0) (.inl 0) = c := by
    unfold mat
    rw [hc]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  have hc1 : c = 1 := Units.ext (h2.symm.trans h1)
  have h3 : u * v⁻¹ = 1 := Subtype.ext (by rw [hc, hc1, map_one]; rfl)
  exact mul_inv_eq_one.1 h3

theorem burnsideF429b_U5_card_map {X : Subgroup (hypSU hK 2 1)}
    (hX : X ≤ hypUnitriangular hK 2 1) : Nat.card (X.map (hypProj hK 2 1)) = Nat.card X := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun x : X => (⟨hypProj hK 2 1 x, x, x.2, rfl⟩ : X.map (hypProj hK 2 1))) ⟨?_, ?_⟩)).symm
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ h
    exact Subtype.ext (burnsideF429b_U5_proj_injOn hK (hX hx) (hX hy) (congrArg Subtype.val h))
  · rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem burnsideF429b_U5_card_V :
    Nat.card ((Vsub hK).map (hypProj hK 2 1)) = (2 ^ f) ^ 4 := by
  rw [burnsideF429b_U5_card_map hK (Vsub_le_Ssub.trans Ssub_le_Usub), card_Vsub]

theorem burnsideF429b_U5_V_le_U :
    (Vsub hK).map (hypProj hK 2 1) ≤ hypProjUnitriangular hK 2 1 :=
  Subgroup.map_mono (Vsub_le_Ssub.trans Ssub_le_Usub)

theorem burnsideF429b_U5_V_comm :
    ∀ x ∈ (Vsub hK).map (hypProj hK 2 1), ∀ y ∈ (Vsub hK).map (hypProj hK 2 1),
      x * y = y * x := by
  rintro _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
  rw [← map_mul, ← map_mul, Vsub_comm hv hw]

theorem burnsideF429b_U5_V_sq : ∀ x ∈ (Vsub hK).map (hypProj hK 2 1), x * x = 1 := by
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, Vsub_sq hv, map_one]

theorem burnsideF429b_U5_elemAb {B : Subgroup (hypPSU hK 2 1)}
    (hBU : B ≤ hypProjUnitriangular hK 2 1) (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ B, x * x = 1) :
    B ≤ (Vsub hK).map (hypProj hK 2 1) ∨ Nat.card B ≤ (2 ^ f) ^ 3 := by
  set B₁ : Subgroup (hypSU hK 2 1) := B.comap (hypProj hK 2 1) ⊓ hypUnitriangular hK 2 1
    with hB₁def
  have hB₁U : B₁ ≤ hypUnitriangular hK 2 1 := inf_le_right
  have hB₁c : ∀ x ∈ B₁, ∀ y ∈ B₁, x * y = y * x := fun x hx y hy =>
    burnsideF429b_U5_proj_injOn hK (mul_mem hx.2 hy.2) (mul_mem hy.2 hx.2)
      (by rw [map_mul, map_mul]; exact hc _ hx.1 _ hy.1)
  have hB₁2 : ∀ x ∈ B₁, x * x = 1 := fun x hx =>
    burnsideF429b_U5_proj_injOn hK (mul_mem hx.2 hx.2) (one_mem _)
      (by rw [map_mul, map_one]; exact h2 _ hx.1)
  have hmap : B₁.map (hypProj hK 2 1) = B := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.1
    · intro y hy
      obtain ⟨u, hu, rfl⟩ := hBU hy
      exact ⟨u, ⟨hy, hu⟩, rfl⟩
  rcases elemAb_le_Vsub_or_card_le hB₁U hB₁c hB₁2 with h | h
  · left
    rw [← hmap]
    exact Subgroup.map_mono h
  · right
    rw [← hmap, burnsideF429b_U5_card_map hK hB₁U]
    exact h

theorem burnsideF429b_U5_normal_form (α : MulAut (hypPSU hK 2 1))
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1) :
    ∃ b ∈ hypBorel hK 2 1, ∃ δ : normOne hK, ∃ σ : K ≃+* K,
      α = MulAut.conj (hypProj hK 2 1 b) * dHom hK δ * fieldP hK σ := by
  obtain ⟨x₀, hx₀⟩ := Phi_surjective hK α
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep hK (r := 2) (ε := 1) (by norm_num)
    (by norm_num) (by norm_num) x₀
  set A : GL (HypIndex 2 1) K := (x : SemiGL (HypIndex 2 1) K).left with hAdef
  set σ : K ≃+* K := (x : SemiGL (HypIndex 2 1) K).right with hσdef
  set δ : Kˣ := Matrix.GeneralLinearGroup.det A with hδdef
  have hδ : hK.norm (δ : K) = 1 := by
    rw [hδdef, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one hxU
  have hδ' : δ ∈ normOne hK := (mem_normOne hK).2 hδ
  have hδi : hK.norm ((δ⁻¹ : Kˣ) : K) = 1 := (mem_normOne hK).1 ((normOne hK).inv_mem hδ')
  have hgu : A * dGL hK δ⁻¹ ∈ hypUnitary hK 2 1 := mul_mem hxU (dGL_mem_hypUnitary hK hδi)
  have hgd : ((A * dGL hK δ⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K).det
      = 1 := by
    rw [Units.val_mul, Matrix.det_mul, det_dGL, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← hδdef, Units.val_inv_eq_inv_val, mul_inv_cancel₀ δ.ne_zero]
  let g : hypSU hK 2 1 := ⟨A * dGL hK δ⁻¹, mem_gramSU.2 ⟨mem_hypUnitary.1 hgu, hgd⟩⟩
  have hA : (g : GL (HypIndex 2 1) K) * dGL hK δ = A := by
    change A * dGL hK δ⁻¹ * dGL hK δ = A
    rw [mul_assoc, ← dGL_mul, inv_mul_cancel, dGL_one, mul_one]
  have hx : x = inlG g * dGam hK δ hδ * inrGam hK σ := by
    refine Subtype.ext ?_
    rw [← SemidirectProduct.inl_left_mul_inr_right (x : SemiGL (HypIndex 2 1) K)]
    change SemidirectProduct.inl A * SemidirectProduct.inr σ =
      SemidirectProduct.inl (g : GL (HypIndex 2 1) K) * SemidirectProduct.inl (dGL hK δ) *
        SemidirectProduct.inr σ
    rw [← map_mul, hA]
  have hα' : α = innM hK g * dHom hK ⟨δ, hδ'⟩ * fieldP hK σ := by
    have h1 : Phi hK x = α := hxΦ.trans hx₀
    rw [← h1, hx, map_mul, map_mul, Phi_inlG]
    rfl
  have hstab : ∀ y, MulAut.conj (hypProj hK 2 1 g) y ∈ hypProjUnitriangular hK 2 1 ↔
      y ∈ hypProjUnitriangular hK 2 1 := by
    intro y
    have e1 : MulAut.conj (hypProj hK 2 1 g) = α * (fieldP hK σ)⁻¹ * (dHom hK ⟨δ, hδ'⟩)⁻¹ := by
      have : MulAut.conj (hypProj hK 2 1 g) = innM hK g := rfl
      rw [this, hα']
      group
    have h2 := dHom_stab hK ⟨δ, hδ'⟩ ((dHom hK ⟨δ, hδ'⟩)⁻¹ y)
    rw [MulAut.apply_inv_self] at h2
    have h3 := fieldP_stab_U hK σ ((fieldP hK σ)⁻¹ ((dHom hK ⟨δ, hδ'⟩)⁻¹ y))
    rw [MulAut.apply_inv_self] at h3
    rw [e1, MulAut.mul_apply, MulAut.mul_apply, hα]
    exact h3.symm.trans h2.symm
  have hgB : hypProj hK 2 1 g ∈ Subgroup.normalizer ((hypProjUnitriangular hK 2 1 :
      Subgroup (hypPSU hK 2 1)) : Set (hypPSU hK 2 1)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← MulAut.conj_apply]
    exact (hstab y).symm
  rw [normalizer_hypProjUnitriangular hK (by norm_num) (by norm_num)] at hgB
  obtain ⟨b, hb, hbg⟩ := hgB
  refine ⟨b, hb, ⟨δ, hδ'⟩, σ, ?_⟩
  rw [hα', hbg]
  rfl

theorem burnsideF429b_U5_mem_Eext {b : hypSU hK 2 1} (hb : b ∈ hypBorel hK 2 1)
    (δ : normOne hK) : MulAut.conj (hypProj hK 2 1 b) * dHom hK δ ∈ Eext hK := by
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨_, ?_, rfl⟩)
    (Subgroup.mem_sup_right ⟨δ, rfl⟩)
  rw [normalizer_hypProjUnitriangular hK (by norm_num) (by norm_num)]
  exact ⟨b, hb, rfl⟩

theorem burnsideF429b_U5_eq_one_of_fieldP_mem {τ : K ≃+* K} (h : fieldP hK τ ∈ Eext hK) :
    τ = 1 := by
  have D := borelAutDiag_u5 hK
  refine eq_one_of_fieldP_fixes hK τ fun x hx => ?_
  have h1 := D.E_triv _ h x (D.H_le hx)
  have h2 := D.F_H _ ⟨τ, rfl⟩ x hx
  have h3 := D.U_inf_H _ h1 (mul_mem (inv_mem hx) h2)
  exact (inv_mul_eq_one.1 h3).symm

theorem burnsideF429b_U5_field_part {e : MulAut (hypPSU hK 2 1)} (he : e ∈ Eext hK)
    (σ : K ≃+* K) (h2 : (e * fieldP hK σ) * (e * fieldP hK σ) = 1)
    (hno : e * fieldP hK σ ∉ (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range) :
    (∀ c, σ c = c ^ 2 ^ f) ∧ Nat.card {c : K // σ c = c} = 2 ^ f ∧ σ ^ 2 = 1 := by
  have D := borelAutDiag_u5 hK
  have he' : fieldP hK σ * e * (fieldP hK σ)⁻¹ ∈ Eext hK := D.F_E _ ⟨σ, rfl⟩ e he
  have hσ2mem : fieldP hK (σ ^ 2) ∈ Eext hK := by
    have e2 : fieldP hK (σ ^ 2) = (e * (fieldP hK σ * e * (fieldP hK σ)⁻¹))⁻¹ := by
      rw [map_pow, sq]
      refine eq_inv_of_mul_eq_one_right ?_
      calc e * (fieldP hK σ * e * (fieldP hK σ)⁻¹) * (fieldP hK σ * fieldP hK σ) =
          (e * fieldP hK σ) * (e * fieldP hK σ) := by group
        _ = 1 := h2
    rw [e2]
    exact inv_mem (mul_mem he he')
  have hσ2 : σ ^ 2 = 1 := burnsideF429b_U5_eq_one_of_fieldP_mem hK hσ2mem
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at h2 hno
    obtain ⟨u, -, hu⟩ := D.E_two e he 1 (by rw [pow_one, sq]; exact h2)
    exact hno ⟨u, hu.symm⟩
  haveI := hK.finite
  have hf1 := hK.one_le
  obtain ⟨-, hc, hcard⟩ := CFSG.LieType.Chevalley.ringEquiv_sq_eq_one_facts Nat.prime_two
    (by omega) hK.card hσ2 hσ1
  rw [show 2 * f / 2 = f by omega] at hc hcard
  exact ⟨hc, hcard, hσ2⟩

theorem burnsideF429b_U5_act_V {b : hypSU hK 2 1} (hb : b ∈ hypBorel hK 2 1) :
    ∃ A : Matrix (Fin 2) (Fin 2) K, A.IsUpperTriangular ∧ IsUnit A.det ∧
      ∀ (δ : normOne hK) (σ : K ≃+* K) (v : hypSU hK 2 1), v ∈ Vsub hK →
        ∃ v' ∈ Vsub hK,
          (MulAut.conj (hypProj hK 2 1 b) * dHom hK δ * fieldP hK σ) (hypProj hK 2 1 v) =
            hypProj hK 2 1 v' ∧ Yof v' = A * (Yof v).map σ * (A.map hK.bar)ᵀ := by
  obtain ⟨A, C, x, d, hAu, hAdet, -, hd, hbm⟩ := exists_oddProd_of_mem_hypBorel hb
  refine ⟨A, hAu, hAdet, fun δ σ v hv => ?_⟩
  obtain ⟨-, Y, hY⟩ := hv
  have hdd : hK.bar d * d = 1 := bar_mul_self_of_eq_div hAdet hd
  have hbm' : mat b = oddDiag hK A d * oddUni hK x C := hbm
  have hw : mat (fieldAut hK σ v) = oddUni hK 0 (Y.map σ) := by
    show (mat v).map σ = _
    rw [hY]
    ext a c
    rcases a with i | k | i <;> rcases c with j | l | j <;>
      simp [oddUni, Matrix.one_apply, apply_ite σ]
  have hdw : act hK (dGam hK δ.1 ((mem_normOne hK).1 δ.2)) (fieldAut hK σ v) =
      fieldAut hK σ v := by
    apply Subtype.ext
    apply Units.ext
    rw [phi_dGam_apply]
    ext i j
    rw [conj_dGL_apply]
    show dEnt hK δ.1 i * mat (fieldAut hK σ v) i j * dEnt hK δ.1⁻¹ j =
      mat (fieldAut hK σ v) i j
    rw [hw]
    rcases i with i | k | i <;> rcases j with j | l | j <;>
      simp [dEnt, torusEntries, oddUni, Matrix.one_apply]
  have hbw : mat (b * fieldAut hK σ v * b⁻¹) =
      oddUni hK 0 (A * Y.map σ * (A.map hK.bar)ᵀ) := by
    have h1 : mat b * mat (fieldAut hK σ v) =
        oddUni hK 0 (A * Y.map σ * (A.map hK.bar)ᵀ) * mat b := by
      rw [hbm', hw, Matrix.mul_assoc, oddUni_comm_zero, ← Matrix.mul_assoc,
        oddDiag_mul_oddUni_zero hAdet hdd, Matrix.mul_assoc]
    have h3 : mat b * mat b⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
    rw [mat_mul, mat_mul, h1, Matrix.mul_assoc, h3, Matrix.mul_one]
  refine ⟨b * fieldAut hK σ v * b⁻¹, mem_Vsub_of_mat hbw, ?_, ?_⟩
  · rw [MulAut.mul_apply, MulAut.mul_apply, fieldP_apply, dHom_apply, hdw, MulAut.conj_apply,
      ← map_inv, ← map_mul, ← map_mul]
  · rw [Yof_eq hbw, Yof_eq hY]

theorem burnsideF429b_U5_card_fixed_le {A : Matrix (Fin 2) (Fin 2) K} (hA : A.IsUpperTriangular)
    (hAdet : IsUnit A.det) (σ : K ≃+* K) (X : Set (hypSU hK 2 1)) (hX : X ⊆ Vsub hK)
    (hfix : ∀ v ∈ X, A * (Yof v).map σ * (A.map hK.bar)ᵀ = Yof v) :
    Nat.card X ≤ Nat.card {a : K // σ a = a} ^ 3 := by
  haveI := hK.finite
  have hA10 : A 1 0 = 0 := hA (show (0 : Fin 2) < 1 by decide)
  have hdet : A.det = A 0 0 * A 1 1 := by rw [Matrix.det_fin_two, hA10, mul_zero, sub_zero]
  have h00 : A 0 0 ≠ 0 := fun h => hAdet.ne_zero (by rw [hdet, h, zero_mul])
  have h11 : A 1 1 ≠ 0 := fun h => hAdet.ne_zero (by rw [hdet, h, mul_zero])
  have hb0 : ∀ a : K, a ≠ 0 → hK.bar a ≠ 0 := fun a ha => (map_ne_zero hK.bar).mpr ha
  let φ : X → (K × K) × K := fun v => ((Yof v.1 1 1, Yof v.1 0 1), Yof v.1 0 0)
  have hφ : Function.Injective φ := by
    rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    simp only [φ, Prod.mk.injEq] at h
    exact Subtype.ext (Yof_ext (hX hv) (hX hw) h.2 h.1.2 h.1.1)
  have key := burnsideF429_card_twisted_le_cube σ (l₁ := A 1 1 * hK.bar (A 1 1))
    (l₂ := A 0 0 * hK.bar (A 1 1)) (l₃ := A 0 0 * hK.bar (A 0 0))
    (mul_ne_zero h11 (hb0 _ h11)) (mul_ne_zero h00 (hb0 _ h11)) (mul_ne_zero h00 (hb0 _ h00))
    (fun y => A 0 1 * hK.bar (A 1 1) * σ y)
    (fun p => A 0 1 * hK.bar (A 0 0) * σ (hK.bar p.2) + A 0 0 * hK.bar (A 0 1) * σ p.2 +
      A 0 1 * hK.bar (A 0 1) * σ p.1)
    (Set.range φ) ?_
  · calc Nat.card X = Nat.card (Set.range φ) := (Nat.card_range_of_injective hφ).symm
      _ ≤ Nat.card {a : K // σ a = a} ^ 3 := key
  · rintro _ ⟨⟨v, hv⟩, rfl⟩
    have e := hfix v hv
    have hh := isHerm_iff.1 (herm_Yof (hX hv))
    have e11 := congrFun (congrFun e 1) 1
    have e01 := congrFun (congrFun e 0) 1
    have e00 := congrFun (congrFun e 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
      hA10, map_zero, zero_mul, mul_zero, zero_add, add_zero] at e11 e01 e00
    rw [hh.2.2] at e00
    refine ⟨?_, ?_, ?_⟩
    · show A 1 1 * hK.bar (A 1 1) * σ (Yof v 1 1) = Yof v 1 1
      linear_combination e11
    · show A 0 0 * hK.bar (A 1 1) * σ (Yof v 0 1) + A 0 1 * hK.bar (A 1 1) * σ (Yof v 1 1) =
        Yof v 0 1
      linear_combination e01
    · show A 0 0 * hK.bar (A 0 0) * σ (Yof v 0 0) +
        (A 0 1 * hK.bar (A 0 0) * σ (hK.bar (Yof v 0 1)) + A 0 0 * hK.bar (A 0 1) * σ (Yof v 0 1) +
          A 0 1 * hK.bar (A 0 1) * σ (Yof v 1 1)) = Yof v 0 0
      linear_combination e00

theorem burnsideF429b_U5_eq_one_of_fix_all {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A.IsUpperTriangular) (σ : K ≃+* K)
    (hfix : ∀ Y : Matrix (Fin 2) (Fin 2) K, IsHerm hK Y → A * Y.map σ * (A.map hK.bar)ᵀ = Y) :
    σ = 1 := by
  have hA10 : A 1 0 = 0 := hA (show (0 : Fin 2) < 1 by decide)
  have key : ∀ c : K, A 0 0 * hK.bar (A 1 1) * σ c = c := by
    intro c
    have hY : IsHerm hK !![0, c; hK.bar c, 0] := by
      rw [isHerm_iff]
      simp
    have e := congrFun (congrFun (hfix _ hY) 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, Matrix.transpose_apply,
      hA10, map_zero, zero_mul, mul_zero, zero_add, add_zero, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_cons, Matrix.head_fin_const] at e
    linear_combination e
  have h1 : A 0 0 * hK.bar (A 1 1) = 1 := by simpa using key 1
  exact RingEquiv.ext fun c => by simpa [h1] using key c

theorem burnsideF429b_U5_mul_mem_Eext {α β : MulAut (hypPSU hK 2 1)}
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1)
    (hβ : ∀ x, β x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1)
    (hα2 : α * α = 1) (hβ2 : β * β = 1)
    (hαn : α ∉ (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range)
    (hβn : β ∉ (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range) :
    α * β ∈ Eext hK := by
  obtain ⟨b, hb, δ, σ, rfl⟩ := burnsideF429b_U5_normal_form hK α hα
  obtain ⟨b', hb', δ', σ', rfl⟩ := burnsideF429b_U5_normal_form hK β hβ
  have he := burnsideF429b_U5_mem_Eext hK hb δ
  have he' := burnsideF429b_U5_mem_Eext hK hb' δ'
  obtain ⟨hσ, -, hσ2⟩ := burnsideF429b_U5_field_part hK he σ hα2 hαn
  obtain ⟨hσ', -, -⟩ := burnsideF429b_U5_field_part hK he' σ' hβ2 hβn
  have hσσ : σ' = σ := RingEquiv.ext fun c => by rw [hσ, hσ']
  subst hσσ
  have hσσ2 : σ' * σ' = 1 := by rw [← sq]; exact hσ2
  have hs2 : fieldP hK σ' * fieldP hK σ' = 1 := by rw [← map_mul, hσσ2, map_one]
  have D := borelAutDiag_u5 hK
  have hconj := D.F_E _ ⟨σ', rfl⟩ _ he'
  have e : MulAut.conj (hypProj hK 2 1 b) * dHom hK δ * fieldP hK σ' *
      (MulAut.conj (hypProj hK 2 1 b') * dHom hK δ' * fieldP hK σ') =
      (MulAut.conj (hypProj hK 2 1 b) * dHom hK δ) *
        (fieldP hK σ' * (MulAut.conj (hypProj hK 2 1 b') * dHom hK δ') * (fieldP hK σ')⁻¹) *
          (fieldP hK σ' * fieldP hK σ') := by group
  rw [e, hs2, mul_one]
  exact mul_mem he hconj

theorem burnsideF429b_U5_card_fixed_V {α : MulAut (hypPSU hK 2 1)}
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1)
    (hα2 : α * α = 1)
    (hαn : α ∉ (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range)
    (X : Set (hypPSU hK 2 1)) (hX : X ⊆ (Vsub hK).map (hypProj hK 2 1))
    (hfix : ∀ x ∈ X, α x = x) : Nat.card X ≤ (2 ^ f) ^ 3 := by
  obtain ⟨b, hb, δ, σ, rfl⟩ := burnsideF429b_U5_normal_form hK α hα
  obtain ⟨-, hcard, -⟩ :=
    burnsideF429b_U5_field_part hK (burnsideF429b_U5_mem_Eext hK hb δ) σ hα2 hαn
  obtain ⟨A, hAu, hAdet, hact⟩ := burnsideF429b_U5_act_V hK hb
  have hVU : ∀ {v : hypSU hK 2 1}, v ∈ Vsub hK → v ∈ hypUnitriangular hK 2 1 :=
    fun hv => Ssub_le_Usub (Vsub_le_Ssub hv)
  set X' : Set (hypSU hK 2 1) := {v | v ∈ Vsub hK ∧ hypProj hK 2 1 v ∈ X} with hX'def
  have hcardX : Nat.card X = Nat.card X' := by
    refine (Nat.card_congr (Equiv.ofBijective
      (fun v : X' => (⟨hypProj hK 2 1 v.1, v.2.2⟩ : X)) ⟨?_, ?_⟩)).symm
    · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
      exact Subtype.ext (burnsideF429b_U5_proj_injOn hK (hVU hv.1) (hVU hw.1)
        (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨v, hv, rfl⟩ := hX hx
      exact ⟨⟨v, hv, hx⟩, rfl⟩
  rw [hcardX, ← hcard]
  refine burnsideF429b_U5_card_fixed_le hK hAu hAdet σ X' (fun v hv => hv.1) fun v hv => ?_
  obtain ⟨v', hv', he, hY⟩ := hact δ σ v hv.1
  have hfx := hfix _ hv.2
  rw [he] at hfx
  have hvv := burnsideF429b_U5_proj_injOn hK (hVU hv') (hVU hv.1) hfx
  rw [hvv] at hY
  exact hY.symm

theorem burnsideF429b_U5_inner_of_fix_V {α : MulAut (hypPSU hK 2 1)}
    (hα : ∀ x, α x ∈ hypProjUnitriangular hK 2 1 ↔ x ∈ hypProjUnitriangular hK 2 1)
    (hfix : ∀ x ∈ (Vsub hK).map (hypProj hK 2 1), α x = x) {n : ℕ} (hn : α ^ 2 ^ n = 1) :
    α ∈ (MulAut.conj : hypPSU hK 2 1 →* MulAut (hypPSU hK 2 1)).range := by
  obtain ⟨b, hb, δ, σ, rfl⟩ := burnsideF429b_U5_normal_form hK α hα
  obtain ⟨A, hAu, -, hact⟩ := burnsideF429b_U5_act_V hK hb
  have hVU : ∀ {v : hypSU hK 2 1}, v ∈ Vsub hK → v ∈ hypUnitriangular hK 2 1 :=
    fun hv => Ssub_le_Usub (Vsub_le_Ssub hv)
  have hσ : σ = 1 := burnsideF429b_U5_eq_one_of_fix_all hK hAu σ fun Y hY => by
    obtain ⟨v, hv, hvm⟩ := exists_mem_Vsub hY
    obtain ⟨v', hv', he, hY'⟩ := hact δ σ v hv
    have hfx := hfix _ ⟨v, hv, rfl⟩
    rw [he] at hfx
    have hvv := burnsideF429b_U5_proj_injOn hK (hVU hv') (hVU hv) hfx
    rw [hvv, Yof_eq hvm] at hY'
    exact hY'.symm
  subst hσ
  rw [map_one, mul_one] at hn ⊢
  obtain ⟨u, -, hu⟩ := (borelAutDiag_u5 hK).E_two _ (burnsideF429b_U5_mem_Eext hK hb δ) n hn
  exact ⟨u, hu.symm⟩

end U5Model

end CFSG.ASVolI
