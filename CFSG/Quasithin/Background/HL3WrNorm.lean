module

public import CFSG.Quasithin.Background.HL3WrModel
public import CFSG.Quasithin.Background.HSL3Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix commutatorElement

section Square

variable {Γ : Type*} [Group Γ] [Finite Γ]

omit [Finite Γ] in
theorem card_prod_subgroup (H K : Subgroup Γ) : Nat.card (H.prod K) = Nat.card H * Nat.card K := by
  rw [Nat.card_congr (Subgroup.prodEquiv H K).toEquiv, Nat.card_prod]

theorem prod_eq_or_of_normal (hs : IsSimpleGroup Γ)
    (hp : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = (⊤ : Subgroup Γ))
    {N : Subgroup (Γ × Γ)} (hN : N.Normal) (hc : Nat.card N = Nat.card Γ) :
    N = (⊤ : Subgroup Γ).prod ⊥ ∨ N = (⊥ : Subgroup Γ).prod ⊤ := by
  have hsn : (N.map (MonoidHom.snd Γ Γ)).Normal :=
    hN.map _ fun y => ⟨(1, y), rfl⟩
  have hcard1 : Nat.card ((⊤ : Subgroup Γ).prod (⊥ : Subgroup Γ)) = Nat.card Γ := by
    rw [card_prod_subgroup, Subgroup.card_top, Subgroup.card_bot, mul_one]
  have hcard2 : Nat.card ((⊥ : Subgroup Γ).prod (⊤ : Subgroup Γ)) = Nat.card Γ := by
    rw [card_prod_subgroup, Subgroup.card_top, Subgroup.card_bot, one_mul]
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hsn with h | h
  · left
    have hle : N ≤ (⊤ : Subgroup Γ).prod ⊥ := by
      intro x hx
      have h2 : (MonoidHom.snd Γ Γ) x ∈ N.map (MonoidHom.snd Γ Γ) := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at h2
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr h2⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard1])
  · right
    have hcomm : ⁅(⊤ : Subgroup Γ), ⊤⁆ ≤ N.comap (MonoidHom.inr Γ Γ) := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      have hx : x ∈ N.map (MonoidHom.snd Γ Γ) := by
        rw [h]
        exact Subgroup.mem_top x
      obtain ⟨n, hn, hnx⟩ := hx
      have hmem : n * (MonoidHom.inr Γ Γ y) * n⁻¹ * (MonoidHom.inr Γ Γ y)⁻¹ ∈ N := by
        have h1 : (MonoidHom.inr Γ Γ y) * n⁻¹ * (MonoidHom.inr Γ Γ y)⁻¹ ∈ N :=
          hN.conj_mem _ (N.inv_mem hn) _
        have := N.mul_mem hn h1
        simpa [mul_assoc] using this
      have heq : n * (MonoidHom.inr Γ Γ y) * n⁻¹ * (MonoidHom.inr Γ Γ y)⁻¹ =
          MonoidHom.inr Γ Γ ⁅x, y⁆ := by
        rw [← hnx]
        ext <;> simp [commutatorElement_def]
      rw [heq] at hmem
      exact hmem
    rw [hp] at hcomm
    have hle : (⊥ : Subgroup Γ).prod ⊤ ≤ N := by
      intro x hx
      obtain ⟨h1, -⟩ := Subgroup.mem_prod.mp hx
      have hx' : x = MonoidHom.inr Γ Γ x.2 := by
        rw [Subgroup.mem_bot] at h1
        ext
        · exact h1
        · rfl
      rw [hx']
      exact hcomm (Subgroup.mem_top x.2)
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hcard2])).symm

omit [Finite Γ] in
theorem prod_top_bot_normal : ((⊤ : Subgroup Γ).prod (⊥ : Subgroup Γ)).Normal := by
  rw [← MonoidHom.ker_snd]
  exact MonoidHom.normal_ker _

omit [Finite Γ] in
theorem prod_bot_top_normal : ((⊥ : Subgroup Γ).prod (⊤ : Subgroup Γ)).Normal := by
  rw [← MonoidHom.ker_fst]
  exact MonoidHom.normal_ker _

theorem map_prod_eq_or (hs : IsSimpleGroup Γ)
    (hp : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = (⊤ : Subgroup Γ))
    (α : MulAut (Γ × Γ)) :
    ((⊤ : Subgroup Γ).prod ⊥).map α.toMonoidHom = (⊤ : Subgroup Γ).prod ⊥ ∨
      ((⊤ : Subgroup Γ).prod ⊥).map α.toMonoidHom = (⊥ : Subgroup Γ).prod ⊤ := by
  refine prod_eq_or_of_normal hs hp (prod_top_bot_normal.map _ α.surjective) ?_
  rw [Subgroup.card_map_of_injective α.injective, card_prod_subgroup, Subgroup.card_top,
    Subgroup.card_bot, mul_one]

theorem map_prod_eq_or' (hs : IsSimpleGroup Γ)
    (hp : ⁅(⊤ : Subgroup Γ), (⊤ : Subgroup Γ)⁆ = (⊤ : Subgroup Γ))
    (α : MulAut (Γ × Γ)) :
    ((⊥ : Subgroup Γ).prod ⊤).map α.toMonoidHom = (⊤ : Subgroup Γ).prod ⊥ ∨
      ((⊥ : Subgroup Γ).prod ⊤).map α.toMonoidHom = (⊥ : Subgroup Γ).prod ⊤ := by
  refine prod_eq_or_of_normal hs hp (prod_bot_top_normal.map _ α.surjective) ?_
  rw [Subgroup.card_map_of_injective α.injective, card_prod_subgroup, Subgroup.card_top,
    Subgroup.card_bot, one_mul]

end Square

theorem eq_zero_of_left_fix {Y : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h1 : Matrix.transvection (1 : Fin 3) 0 (1 : ZMod 2) * Y = Y)
    (h2 : Matrix.transvection (2 : Fin 3) 1 (1 : ZMod 2) * Y = Y)
    (h3 : Matrix.transvection (1 : Fin 3) 2 (1 : ZMod 2) * Y = Y) : Y = 0 := by
  have e1 := fun j => congrFun (congrFun h1 1) j
  have e2 := fun j => congrFun (congrFun h2 2) j
  have e3 := fun j => congrFun (congrFun h3 1) j
  simp [Matrix.transvection, Matrix.add_mul, Matrix.single_mul_apply_same] at e1 e2 e3
  ext i j
  fin_cases i
  · simpa using e1 j
  · simpa using e2 j
  · simpa using e3 j

theorem eq_zero_of_right_fix {Y : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h1 : Y * Matrix.transvection (0 : Fin 3) 1 (1 : ZMod 2) = Y)
    (h2 : Y * Matrix.transvection (1 : Fin 3) 2 (1 : ZMod 2) = Y)
    (h3 : Y * Matrix.transvection (2 : Fin 3) 1 (1 : ZMod 2) = Y) : Y = 0 := by
  have e1 := fun i => congrFun (congrFun h1 i) 1
  have e2 := fun i => congrFun (congrFun h2 i) 2
  have e3 := fun i => congrFun (congrFun h3 i) 1
  simp [Matrix.transvection, Matrix.mul_add, Matrix.mul_single_apply_same] at e1 e2 e3
  ext i j
  fin_cases j
  · simpa using e1 i
  · simpa using e2 i
  · simpa using e3 i

theorem eq_smul_E00 {Y : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h1 : Matrix.transvection (0 : Fin 3) 1 (1 : ZMod 2) * Y = Y)
    (h2 : Matrix.transvection (0 : Fin 3) 2 (1 : ZMod 2) * Y = Y)
    (h3 : Y * (Matrix.transvection (0 : Fin 3) 1 (1 : ZMod 2))ᵀ = Y)
    (h4 : Y * (Matrix.transvection (0 : Fin 3) 2 (1 : ZMod 2))ᵀ = Y) :
    Y = Matrix.single 0 0 (Y 0 0) := by
  have e1 := fun j => congrFun (congrFun h1 0) j
  have e2 := fun j => congrFun (congrFun h2 0) j
  have e3 := fun i => congrFun (congrFun h3 i) 0
  have e4 := fun i => congrFun (congrFun h4 i) 0
  simp [Matrix.transvection, Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_apply_same,
    Matrix.mul_single_apply_same, Matrix.transpose_add, Matrix.transpose_single] at e1 e2 e3 e4
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

theorem transvection_mul_E00 {i j : Fin 3} (hj : j ≠ 0) :
    Matrix.transvection i j (1 : ZMod 2) * Matrix.single 0 0 1 = Matrix.single 0 0 1 := by
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul,
    Matrix.single_mul_single_of_ne (1 : ZMod 2) i j 0 hj, add_zero]

theorem E00_mul_transvection_transpose {i j : Fin 3} (hj : j ≠ 0) :
    Matrix.single 0 0 1 * (Matrix.transvection i j (1 : ZMod 2))ᵀ = Matrix.single 0 0 1 := by
  rw [Matrix.transvection, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single,
    Matrix.mul_add, Matrix.mul_one, Matrix.single_mul_single_of_ne (1 : ZMod 2) 0 0 j hj.symm,
    add_zero]

@[expose] noncomputable def tr (i j : Fin 3) (h : i ≠ j) : ↥SL32 :=
  ⟨SL3Pair.tGL i j h 1, SL3Pair.tGL_mem i j h 1⟩

theorem mat_tr (i j : Fin 3) (h : i ≠ j) : mat (tr i j h) = Matrix.transvection i j 1 := rfl

@[expose] noncomputable def dualSL : ↥SL32 →* ↥SL32 where
  toFun g := ⟨SL3Pair.dualGL (g : GL (Fin 3) (ZMod 2)), mem_SL32 _⟩
  map_one' := Subtype.ext (map_one SL3Pair.dualHom)
  map_mul' g h := Subtype.ext (map_mul SL3Pair.dualHom (g : GL (Fin 3) (ZMod 2)) h)

theorem mat_dualSL (g : ↥SL32) : mat (dualSL g) = (mat g⁻¹)ᵀ := rfl

theorem mat_dualSL_tr (i j : Fin 3) (h : i ≠ j) :
    mat (dualSL (tr i j h)) = Matrix.transvection j i 1 := by
  change ((SL3Pair.dualGL (SL3Pair.tGL i j h 1) : GL (Fin 3) (ZMod 2)) :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = _
  rw [SL3Pair.coe_dualGL_tGL]
  congr 1

theorem tr_mul_tr_ne : tr 0 1 (by decide) * tr 1 0 (by decide) ≠
    tr 1 0 (by decide) * tr 0 1 (by decide) := by
  intro h
  have h1 := congrArg mat h
  rw [mat_mul, mat_mul, mat_tr, mat_tr] at h1
  revert h1
  decide

theorem isSimpleGroup_SL32 : IsSimpleGroup ↥SL32 := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    CFSG.QuasithinUnique.Bridge.isSimple_sl_zmod2 3 le_rfl
  exact (SL3Pair.slEquiv (ZMod 2)).symm.isSimpleGroup

theorem commutator_SL32 :
    ⁅(⊤ : Subgroup ↥SL32), (⊤ : Subgroup ↥SL32)⁆ = (⊤ : Subgroup ↥SL32) := by
  have hs := isSimpleGroup_SL32
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _
    (Subgroup.commutator_normal (⊤ : Subgroup ↥SL32) ⊤) with h | h
  · exfalso
    apply tr_mul_tr_ne
    have hc : ⁅tr 0 1 (by decide), tr 1 0 (by decide)⁆ ∈
        ⁅(⊤ : Subgroup ↥SL32), (⊤ : Subgroup ↥SL32)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · exact h

theorem ringEquiv_zmod_two_apply (σ : ZMod 2 ≃+* ZMod 2) (z : ZMod 2) : σ z = z := by
  have h := RingHom.ext_zmod (σ : ZMod 2 →+* ZMod 2) (RingHom.id _)
  exact congrArg (fun f : ZMod 2 →+* ZMod 2 => f z) h

theorem exists_std (α : MulAut ↥SL32) :
    ∃ A : ↥SL32, (∀ a, α a = A * a * A⁻¹) ∨ (∀ a, α a = A * dualSL a * A⁻¹) := by
  set β : MulAut (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    (MulAut.congr (SL3Pair.slEquiv (ZMod 2)).symm) α with hβ
  obtain ⟨A, σ, ε, hε, hstd⟩ := SL3Pair.exists_eq_stdAut β
  have hσ : ∀ M : Matrix (Fin 3) (Fin 3) (ZMod 2), M.map σ = M := fun M => by
    ext i j
    exact ringEquiv_zmod_two_apply σ (M i j)
  have hαβ : ∀ a : ↥SL32, mat (α a) =
      ((β ((SL3Pair.slEquiv (ZMod 2)).symm a) : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
    intro a
    rw [hβ]
    change mat (α a) = mat (SL3Pair.slEquiv (ZMod 2) ((SL3Pair.slEquiv (ZMod 2)).symm
      (α (SL3Pair.slEquiv (ZMod 2) ((SL3Pair.slEquiv (ZMod 2)).symm a)))))
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hsymm : ∀ a : ↥SL32, (((SL3Pair.slEquiv (ZMod 2)).symm a :
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = mat a := by
    intro a
    conv_rhs => rw [← MulEquiv.apply_symm_apply (SL3Pair.slEquiv (ZMod 2)) a]
    rfl
  refine ⟨⟨A, mem_SL32 A⟩, ?_⟩
  interval_cases ε
  · left
    intro a
    apply Subtype.ext
    apply Units.ext
    change mat (α a) = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * mat a *
      ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [hαβ, hstd, CFSG.QuasithinUnique.K1.coe_stdAut_zero, hσ, hsymm]
  · right
    intro a
    apply Subtype.ext
    apply Units.ext
    change mat (α a) = (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * (mat a⁻¹)ᵀ *
      ((A⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))
    rw [hαβ, hstd, CFSG.QuasithinUnique.K1.coe_stdAut_one, hσ]
    have hinv : ((((SL3Pair.slEquiv (ZMod 2)).symm a)⁻¹ :
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        mat a⁻¹ := by
      rw [← map_inv (SL3Pair.slEquiv (ZMod 2)).symm a]
      exact hsymm a⁻¹
    rw [hinv]

@[expose] noncomputable def sel : Fin 3 → ↥SL32
  | 0 => 1
  | 1 => tr 0 1 (by decide) * tr 1 0 (by decide)
  | 2 => tr 0 2 (by decide) * tr 2 0 (by decide)

theorem mat_sel_mul (i j : Fin 3) :
    mat (sel i) * Matrix.single 0 0 1 * (mat (sel j))ᵀ = Matrix.single i j 1 := by
  fin_cases i <;> fin_cases j <;>
    simp only [sel, mat_mul, mat_one, mat_tr, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    decide

@[expose] def addMap (ψ : MulAut WMod) : Matrix (Fin 3) (Fin 3) (ZMod 2) →+
    Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  AddMonoidHom.toMultiplicative.symm ψ.toMonoidHom

theorem addMap_apply (ψ : MulAut WMod) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    addMap ψ X = Multiplicative.toAdd (ψ (Multiplicative.ofAdd X)) := rfl

theorem eq_one_of_fix_single {ψ : MulAut WMod}
    (h : ∀ i j : Fin 3, ψ (Multiplicative.ofAdd (Matrix.single i j 1)) =
      Multiplicative.ofAdd (Matrix.single i j 1)) : ψ = 1 := by
  have hc : ∀ (i j : Fin 3) (c : ZMod 2), addMap ψ (Matrix.single i j c) = Matrix.single i j c := by
    intro i j c
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c with rfl | rfl
    · rw [Matrix.single_zero, map_zero]
    · rw [addMap_apply, h]
      rfl
  refine MulEquiv.ext fun X => ?_
  apply Multiplicative.toAdd.injective
  change addMap ψ (Multiplicative.toAdd X) = Multiplicative.toAdd X
  rw [Matrix.matrix_eq_sum_single (Multiplicative.toAdd X), map_sum]
  simp only [map_sum, hc]

theorem eq_one_of_commute {ψ : MulAut WMod} (h : ∀ g, ψ * rho g = rho g * ψ) : ψ = 1 := by
  set X₀ : WMod := Multiplicative.ofAdd (Matrix.single 0 0 1) with hX₀
  have hfix : ∀ g : ↥SL32 × ↥SL32, rho g X₀ = X₀ → rho g (ψ X₀) = ψ X₀ := by
    intro g hg
    have := congrArg (fun φ : MulAut WMod => φ X₀) (h g)
    simp only [MulAut.mul_apply, hg] at this
    exact this.symm
  set Y := Multiplicative.toAdd (ψ X₀) with hY
  have hl : ∀ (j : Fin 3) (hj : (0 : Fin 3) ≠ j), Matrix.transvection 0 j (1 : ZMod 2) * Y = Y := by
    intro j hj
    have h1 := hfix (tr 0 j hj, 1) (by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho]
      change Matrix.transvection 0 j 1 * Matrix.single 0 0 1 * (mat 1)ᵀ = Matrix.single 0 0 1
      rw [mat_one, Matrix.transpose_one, Matrix.mul_one, transvection_mul_E00 hj.symm])
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_rho] at h2
    change Matrix.transvection 0 j 1 * Y * (mat 1)ᵀ = Y at h2
    rwa [mat_one, Matrix.transpose_one, Matrix.mul_one] at h2
  have hr : ∀ (j : Fin 3) (hj : (0 : Fin 3) ≠ j),
      Y * (Matrix.transvection 0 j (1 : ZMod 2))ᵀ = Y := by
    intro j hj
    have h1 := hfix (1, tr 0 j hj) (by
      apply Multiplicative.toAdd.injective
      rw [toAdd_rho]
      change mat 1 * Matrix.single 0 0 1 * (Matrix.transvection 0 j 1)ᵀ = Matrix.single 0 0 1
      rw [mat_one, Matrix.one_mul, E00_mul_transvection_transpose hj.symm])
    have h2 := congrArg Multiplicative.toAdd h1
    rw [toAdd_rho] at h2
    change mat 1 * Y * (Matrix.transvection 0 j 1)ᵀ = Y at h2
    rwa [mat_one, Matrix.one_mul] at h2
  have hY0 := eq_smul_E00 (hl 1 (by decide)) (hl 2 (by decide)) (hr 1 (by decide))
    (hr 2 (by decide))
  have hYX : ψ X₀ = X₀ := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (Y 0 0) with h0 | h0
    · exfalso
      rw [h0, Matrix.single_zero] at hY0
      have hψ1 : ψ X₀ = ψ 1 := by
        rw [map_one]
        apply Multiplicative.toAdd.injective
        rw [← hY, hY0]
        rfl
      have h3 := congrArg Multiplicative.toAdd (ψ.injective hψ1)
      change Matrix.single (0 : Fin 3) 0 (1 : ZMod 2) = 0 at h3
      have h4 := congrFun (congrFun h3 0) 0
      rw [Matrix.single_apply_same, Matrix.zero_apply] at h4
      exact one_ne_zero h4
    · apply Multiplicative.toAdd.injective
      rw [← hY, hY0, h0]
      rfl
  apply eq_one_of_fix_single
  intro i j
  have hX : Multiplicative.ofAdd (Matrix.single i j 1) = rho (sel i, sel j) X₀ := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho]
    exact (mat_sel_mul i j).symm
  rw [hX]
  have := congrArg (fun φ : MulAut WMod => φ X₀) (h (sel i, sel j))
  simp only [MulAut.mul_apply] at this
  rw [this, hYX]

@[expose] noncomputable def rhoEquiv : ↥SL32 × ↥SL32 ≃* ↥img :=
  MonoidHom.ofInjective rho_injective

@[expose] noncomputable def conjAut (x : ↥norm) : MulAut (↥SL32 × ↥SL32) :=
  (MulAut.congr rhoEquiv.symm) (img.normalizerMonoidHom x)

theorem rho_conjAut (x : ↥norm) (g : ↥SL32 × ↥SL32) :
    rho (conjAut x g) = (x : MulAut WMod) * rho g * (x : MulAut WMod)⁻¹ := by
  have h : rho (conjAut x g) = ((rhoEquiv (conjAut x g) : ↥img) : MulAut WMod) := rfl
  rw [h]
  change ((rhoEquiv (rhoEquiv.symm (img.normalizerMonoidHom x (rhoEquiv g))) : ↥img) :
    MulAut WMod) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem mem_img_of_preserves {x : ↥norm}
    (hx : ((⊤ : Subgroup ↥SL32).prod ⊥).map (conjAut x).toMonoidHom =
      (⊤ : Subgroup ↥SL32).prod ⊥) :
    ∃ g, rho g = (x : MulAut WMod) := by
  set α := conjAut x with hα
  have hs := isSimpleGroup_SL32
  have hp := commutator_SL32
  have hx2 : ((⊥ : Subgroup ↥SL32).prod ⊤).map α.toMonoidHom = (⊥ : Subgroup ↥SL32).prod ⊤ := by
    rcases map_prod_eq_or' hs hp α with h | h
    · exfalso
      rw [← hx] at h
      have h' := Subgroup.map_injective α.injective h
      have hmem : ((1 : ↥SL32), tr 0 1 (by decide)) ∈ (⊥ : Subgroup ↥SL32).prod ⊤ :=
        Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
      rw [h'] at hmem
      have h1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).2
      have h2 := congrArg mat h1
      rw [mat_tr, mat_one] at h2
      revert h2
      decide
    · exact h
  have h1 : ∀ a : ↥SL32, (α (a, 1)).2 = 1 := fun a => by
    have hm : α (a, 1) ∈ ((⊤ : Subgroup ↥SL32).prod ⊥).map α.toMonoidHom :=
      ⟨(a, 1), Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩, rfl⟩
    rw [hx] at hm
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hm).2
  have h2 : ∀ b : ↥SL32, (α (1, b)).1 = 1 := fun b => by
    have hm : α (1, b) ∈ ((⊥ : Subgroup ↥SL32).prod ⊤).map α.toMonoidHom :=
      ⟨(1, b), Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩, rfl⟩
    rw [hx2] at hm
    exact Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hm).1
  let f₁ : ↥SL32 →* ↥SL32 :=
    (MonoidHom.fst _ _).comp (α.toMonoidHom.comp (MonoidHom.inl _ _))
  let f₂ : ↥SL32 →* ↥SL32 :=
    (MonoidHom.snd _ _).comp (α.toMonoidHom.comp (MonoidHom.inr _ _))
  have hf₁ : ∀ a, f₁ a = (α (a, 1)).1 := fun a => rfl
  have hf₂ : ∀ b, f₂ b = (α (1, b)).2 := fun b => rfl
  have hα12 : ∀ a b, α (a, b) = (f₁ a, f₂ b) := by
    intro a b
    have hab : ((a, b) : ↥SL32 × ↥SL32) = (a, 1) * (1, b) := by simp
    rw [hab, map_mul, hf₁, hf₂]
    ext
    · rw [Prod.fst_mul, h2, mul_one]
    · rw [Prod.snd_mul, h1, one_mul]
  have hb₁ : Function.Bijective f₁ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro a ha
      have h3 : α (a, 1) = α 1 := by
        rw [map_one]
        exact Prod.ext ha (h1 a)
      exact congrArg Prod.fst (α.injective h3)
    · intro c
      have hc : (c, (1 : ↥SL32)) ∈ ((⊤ : Subgroup ↥SL32).prod ⊥).map α.toMonoidHom := by
        rw [hx]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩
      obtain ⟨⟨a, b⟩, hab, he⟩ := hc
      have hb : b = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hab).2
      subst hb
      exact ⟨a, congrArg Prod.fst he⟩
  have hb₂ : Function.Bijective f₂ := by
    constructor
    · rw [injective_iff_map_eq_one]
      intro b hb
      have h3 : α (1, b) = α 1 := by
        rw [map_one]
        exact Prod.ext (h2 b) hb
      exact congrArg Prod.snd (α.injective h3)
    · intro c
      have hc : ((1 : ↥SL32), c) ∈ ((⊥ : Subgroup ↥SL32).prod ⊤).map α.toMonoidHom := by
        rw [hx2]
        exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_bot.mpr rfl, Subgroup.mem_top _⟩
      obtain ⟨⟨a, b⟩, hab, he⟩ := hc
      have ha : a = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hab).1
      subst ha
      exact ⟨b, congrArg Prod.snd he⟩
  obtain ⟨A, hA⟩ := exists_std (MulEquiv.ofBijective f₁ hb₁)
  obtain ⟨B, hB⟩ := exists_std (MulEquiv.ofBijective f₂ hb₂)
  set ψ : MulAut WMod := (rho (A, B))⁻¹ * (x : MulAut WMod) with hψ
  have hψc : ∀ g, ψ * rho g * ψ⁻¹ = rho ((A, B)⁻¹ * α g * (A, B)) := by
    intro g
    rw [hψ, map_mul, map_mul, map_inv, rho_conjAut]
    group
  have hψX : ∀ g, ∀ X : WMod, ψ (rho g X) = rho ((A, B)⁻¹ * α g * (A, B)) (ψ X) := by
    intro g X
    rw [← hψc]
    simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  set X₀ : WMod := Multiplicative.ofAdd (Matrix.single 0 0 1) with hX₀
  have hne : ψ X₀ ≠ 1 := by
    intro h0
    rw [← map_one ψ] at h0
    have h3 := congrArg Multiplicative.toAdd (ψ.injective h0)
    change Matrix.single (0 : Fin 3) 0 (1 : ZMod 2) = 0 at h3
    have h4 := congrFun (congrFun h3 0) 0
    rw [Matrix.single_apply_same, Matrix.zero_apply] at h4
    exact one_ne_zero h4
  have hA0 : ∀ a, f₁ a = A * a * A⁻¹ := by
    rcases hA with hA | hA
    · exact hA
    · exfalso
      apply hne
      have key : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 →
          Matrix.transvection j i (1 : ZMod 2) * Multiplicative.toAdd (ψ X₀) =
            Multiplicative.toAdd (ψ X₀) := by
        intro i j hij hj
        have h3 := hψX (tr i j hij, 1) X₀
        have hfix : rho (tr i j hij, 1) X₀ = X₀ := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_rho]
          change Matrix.transvection i j 1 * Matrix.single 0 0 1 * (mat 1)ᵀ = Matrix.single 0 0 1
          rw [mat_one, Matrix.transpose_one, Matrix.mul_one, transvection_mul_E00 hj]
        rw [hfix, hα12] at h3
        have h4 := congrArg Multiplicative.toAdd h3
        rw [toAdd_rho] at h4
        have hm1 : mat ((A, B)⁻¹ * (f₁ (tr i j hij), f₂ 1) * (A, B)).1 =
            Matrix.transvection j i 1 := by
          change mat (A⁻¹ * MulEquiv.ofBijective f₁ hb₁ (tr i j hij) * A) = _
          rw [hA, mat_mul, mat_mul, mat_mul, mat_mul, ← mat_dualSL_tr i j hij]
          rw [show mat A⁻¹ * (mat A * mat (dualSL (tr i j hij)) * mat A⁻¹) * mat A =
            (mat A⁻¹ * mat A) * mat (dualSL (tr i j hij)) * (mat A⁻¹ * mat A) by
              simp only [Matrix.mul_assoc], mat_inv_mul, Matrix.one_mul, Matrix.mul_one]
        have hm2 : mat ((A, B)⁻¹ * (f₁ (tr i j hij), f₂ 1) * (A, B)).2 = 1 := by
          change mat (B⁻¹ * f₂ 1 * B) = 1
          rw [map_one, mul_one, inv_mul_cancel, mat_one]
        rw [hm1, hm2, Matrix.transpose_one, Matrix.mul_one] at h4
        exact h4.symm
      have hz := eq_zero_of_left_fix (key 0 1 (by decide) (by decide))
        (key 1 2 (by decide) (by decide)) (key 2 1 (by decide) (by decide))
      apply Multiplicative.toAdd.injective
      rw [hz]
      rfl
  have hB0 : ∀ b, f₂ b = B * b * B⁻¹ := by
    rcases hB with hB | hB
    · exact hB
    · exfalso
      apply hne
      have key : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 →
          Multiplicative.toAdd (ψ X₀) * Matrix.transvection i j (1 : ZMod 2) =
            Multiplicative.toAdd (ψ X₀) := by
        intro i j hij hj
        have h3 := hψX (1, tr i j hij) X₀
        have hfix : rho (1, tr i j hij) X₀ = X₀ := by
          apply Multiplicative.toAdd.injective
          rw [toAdd_rho]
          change mat 1 * Matrix.single 0 0 1 * (Matrix.transvection i j 1)ᵀ = Matrix.single 0 0 1
          rw [mat_one, Matrix.one_mul, E00_mul_transvection_transpose hj]
        rw [hfix, hα12] at h3
        have h4 := congrArg Multiplicative.toAdd h3
        rw [toAdd_rho] at h4
        have hm1 : mat ((A, B)⁻¹ * (f₁ 1, f₂ (tr i j hij)) * (A, B)).1 = 1 := by
          change mat (A⁻¹ * f₁ 1 * A) = 1
          rw [map_one, mul_one, inv_mul_cancel, mat_one]
        have hm2 : mat ((A, B)⁻¹ * (f₁ 1, f₂ (tr i j hij)) * (A, B)).2 =
            Matrix.transvection j i 1 := by
          change mat (B⁻¹ * MulEquiv.ofBijective f₂ hb₂ (tr i j hij) * B) = _
          rw [hB, mat_mul, mat_mul, mat_mul, mat_mul, ← mat_dualSL_tr i j hij]
          rw [show mat B⁻¹ * (mat B * mat (dualSL (tr i j hij)) * mat B⁻¹) * mat B =
            (mat B⁻¹ * mat B) * mat (dualSL (tr i j hij)) * (mat B⁻¹ * mat B) by
              simp only [Matrix.mul_assoc], mat_inv_mul, Matrix.one_mul, Matrix.mul_one]
        rw [hm1, hm2, Matrix.one_mul, SL3Pair.transvection_transpose'] at h4
        exact h4.symm
      have hz := eq_zero_of_right_fix (key 0 1 (by decide) (by decide))
        (key 1 2 (by decide) (by decide)) (key 2 1 (by decide) (by decide))
      apply Multiplicative.toAdd.injective
      rw [hz]
      rfl
  have hcomm : ∀ g, ψ * rho g = rho g * ψ := by
    intro g
    have h3 := hψc g
    have hg : (A, B)⁻¹ * α g * (A, B) = g := by
      obtain ⟨a, b⟩ := g
      rw [hα12, hA0, hB0]
      refine Prod.ext ?_ ?_
      · change A⁻¹ * (A * a * A⁻¹) * A = a
        group
      · change B⁻¹ * (B * b * B⁻¹) * B = b
        group
    rw [hg] at h3
    calc ψ * rho g = (ψ * rho g * ψ⁻¹) * ψ := by group
      _ = rho g * ψ := by rw [h3]
  have h1' := eq_one_of_commute hcomm
  refine ⟨(A, B), ?_⟩
  rw [hψ, inv_mul_eq_one] at h1'
  exact h1'

theorem mem_norm_iff {x : MulAut WMod} : x ∈ norm ↔ ∃ g, x = rho g ∨ x = rho g * tau := by
  constructor
  · intro hx
    rcases map_prod_eq_or isSimpleGroup_SL32 commutator_SL32 (conjAut ⟨x, hx⟩) with h | h
    · obtain ⟨g, hg⟩ := mem_img_of_preserves h
      exact ⟨g, Or.inl hg.symm⟩
    · have hy : tau * x ∈ norm := norm.mul_mem tau_mem_norm hx
      have hconj : ∀ g, conjAut ⟨tau * x, hy⟩ g = (conjAut ⟨x, hx⟩ g).swap := by
        intro g
        apply rho_injective
        rw [rho_conjAut, ← tau_conj_rho, rho_conjAut]
        change tau * x * rho g * (tau * x)⁻¹ = tau * (x * rho g * x⁻¹) * tau⁻¹
        group
      have hpres : ((⊤ : Subgroup ↥SL32).prod ⊥).map (conjAut ⟨tau * x, hy⟩).toMonoidHom =
          (⊤ : Subgroup ↥SL32).prod ⊥ := by
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          change conjAut ⟨tau * x, hy⟩ z ∈ (⊤ : Subgroup ↥SL32).prod ⊥
          rw [hconj]
          have hm : conjAut ⟨x, hx⟩ z ∈ (⊥ : Subgroup ↥SL32).prod ⊤ := by
            rw [← h]
            exact ⟨z, hz, rfl⟩
          exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, (Subgroup.mem_prod.mp hm).1⟩
        · intro hy'
          have hm : y.swap ∈ ((⊤ : Subgroup ↥SL32).prod ⊥).map (conjAut ⟨x, hx⟩).toMonoidHom := by
            rw [h]
            exact Subgroup.mem_prod.mpr ⟨(Subgroup.mem_prod.mp hy').2, Subgroup.mem_top _⟩
          obtain ⟨z, hz, hze⟩ := hm
          refine ⟨z, hz, ?_⟩
          change conjAut ⟨tau * x, hy⟩ z = y
          rw [hconj]
          change conjAut ⟨x, hx⟩ z = y.swap at hze
          rw [hze, Prod.swap_swap]
      obtain ⟨g, hg⟩ := mem_img_of_preserves hpres
      refine ⟨g.swap, Or.inr ?_⟩
      change rho g = tau * x at hg
      rw [← tau_mul_rho, hg, ← mul_assoc, tau_mul_self, one_mul]
  · rintro ⟨g, rfl | rfl⟩
    · exact img_le_norm (rho_mem_img g)
    · exact norm.mul_mem (img_le_norm (rho_mem_img g)) tau_mem_norm

end L3Wr

end H

end CFSG.Quasithin
