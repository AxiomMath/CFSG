module

public import CFSG.Milestones.ASVolI.F431.BF436U5R
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsU5Main
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieB
public import CFSG.RankThree.CentralLiftU.UnitaryBorelLift
public import CFSG.LocalAnalysis.EvenBN.U5.Model
public import CFSG.RankThree.PartOne.U5K.Hyp.Dlin
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Milestones.ASVolI.F431.BCoreU5Chart
public import CFSG.Milestones.ASVolI.F431.BF436U5
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528SKG

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open Matrix
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.LocalAnalysis.EvenBN.U5
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit

section F4GU3

@[expose] def burnsideF4m_inv3 (d₀ d₁ d₂ x y w : CFSG.Fischer.F4) :
    Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4 :=
  !![y ^ 2, w ^ 2, d₂; x ^ 2, d₁, w; d₀, x, y]

@[expose] def burnsideF4m_gu3Inv : List (Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4) :=
  [1, !![1, 0, 1; 0, 1, 0; 0, 0, 1],
    !![CFSG.Fischer.F4.ω + 1, CFSG.Fischer.F4.ω, 1; 1, 0, CFSG.Fischer.F4.ω + 1;
      1, 1, CFSG.Fischer.F4.ω],
    !![CFSG.Fischer.F4.ω, CFSG.Fischer.F4.ω + 1, 1; 1, 0, CFSG.Fischer.F4.ω;
      1, 1, CFSG.Fischer.F4.ω + 1],
    !![CFSG.Fischer.F4.ω + 1, CFSG.Fischer.F4.ω + 1, 1; CFSG.Fischer.F4.ω + 1, 0, CFSG.Fischer.F4.ω;
      1, CFSG.Fischer.F4.ω, CFSG.Fischer.F4.ω],
    !![CFSG.Fischer.F4.ω, 1, 1; CFSG.Fischer.F4.ω + 1, 0, 1;
      1, CFSG.Fischer.F4.ω, CFSG.Fischer.F4.ω + 1],
    !![CFSG.Fischer.F4.ω + 1, 1, 1; CFSG.Fischer.F4.ω, 0, 1;
      1, CFSG.Fischer.F4.ω + 1, CFSG.Fischer.F4.ω],
    !![CFSG.Fischer.F4.ω, CFSG.Fischer.F4.ω, 1; CFSG.Fischer.F4.ω, 0, CFSG.Fischer.F4.ω + 1;
      1, CFSG.Fischer.F4.ω + 1, CFSG.Fischer.F4.ω + 1],
    !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![0, 0, 1; 0, 1, 0; 1, 0, 0]]

theorem burnsideF4m_f4_idem : ∀ d : CFSG.Fischer.F4, d ^ 2 = d → d = 0 ∨ d = 1 := by
  decide

theorem burnsideF4m_gu3_inv_mem (d₀ d₁ d₂ x y w : CFSG.Fischer.F4) (h0 : d₀ ^ 2 = d₀)
    (h1 : d₁ ^ 2 = d₁) (h2 : d₂ ^ 2 = d₂)
    (hsq : burnsideF4m_inv3 d₀ d₁ d₂ x y w * burnsideF4m_inv3 d₀ d₁ d₂ x y w = 1) :
    burnsideF4m_inv3 d₀ d₁ d₂ x y w ∈ burnsideF4m_gu3Inv := by
  revert hsq
  revert w
  revert y
  revert x
  rcases burnsideF4m_f4_idem d₀ h0 with rfl | rfl <;>
    rcases burnsideF4m_f4_idem d₁ h1 with rfl | rfl <;>
    rcases burnsideF4m_f4_idem d₂ h2 with rfl | rfl <;>
    decide +kernel

theorem burnsideF4m_gu3_inv_pair : ∀ A ∈ burnsideF4m_gu3Inv, ∀ B ∈ burnsideF4m_gu3Inv,
    A * B = B * A → A = 1 ∨ B = 1 ∨ A = B := by
  intro A hA B hB
  simp only [burnsideF4m_gu3Inv, List.mem_cons, List.not_mem_nil, or_false] at hA hB
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hB with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

theorem burnsideF4m_gu3_F4 (A B : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4)
    (hA : ∀ i j, A i j = (A (Fin.rev j) (Fin.rev i)) ^ 2)
    (hB : ∀ i j, B i j = (B (Fin.rev j) (Fin.rev i)) ^ 2)
    (hA2 : A * A = 1) (hB2 : B * B = 1) (hAB : A * B = B * A) : A = 1 ∨ B = 1 ∨ A = B := by
  have key : ∀ M : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4,
      (∀ i j, M i j = (M (Fin.rev j) (Fin.rev i)) ^ 2) →
      M = burnsideF4m_inv3 (M 2 0) (M 1 1) (M 0 2) (M 2 1) (M 2 2) (M 1 2) ∧
        (M 2 0) ^ 2 = M 2 0 ∧ (M 1 1) ^ 2 = M 1 1 ∧ (M 0 2) ^ 2 = M 0 2 := by
    intro M hM
    refine ⟨?_, (hM 2 0).symm, (hM 1 1).symm, (hM 0 2).symm⟩
    ext i j
    fin_cases i <;> fin_cases j
    · exact hM 0 0
    · exact hM 0 1
    · rfl
    · exact hM 1 0
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  obtain ⟨eA, a0, a1, a2⟩ := key A hA
  obtain ⟨eB, b0, b1, b2⟩ := key B hB
  have hAL := burnsideF4m_gu3_inv_mem _ _ _ _ _ _ a0 a1 a2 (by rw [← eA]; exact hA2)
  have hBL := burnsideF4m_gu3_inv_mem _ _ _ _ _ _ b0 b1 b2 (by rw [← eB]; exact hB2)
  rw [← eA] at hAL
  rw [← eB] at hBL
  exact burnsideF4m_gu3_inv_pair A hAL B hBL hAB

end F4GU3

section FieldK

variable {K : Type} [Field K]

theorem burnsideF4m_gu3_K (h : UnitaryFieldData 2 1 K) (A B : Matrix (Fin 3) (Fin 3) K)
    (hA : ∀ i j, A i j = h.bar (A (Fin.rev j) (Fin.rev i)))
    (hB : ∀ i j, B i j = h.bar (B (Fin.rev j) (Fin.rev i)))
    (hA2 : A * A = 1) (hB2 : B * B = 1) (hAB : A * B = B * A) : A = 1 ∨ B = 1 ∨ A = B := by
  set e := burnsideF4m_eF4e h with he
  set Em : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4 ≃+* Matrix (Fin 3) (Fin 3) K := e.mapMatrix
  have hEm : ∀ M i j, Em M i j = e (M i j) := fun M i j => rfl
  obtain ⟨A', rfl⟩ := Em.surjective A
  obtain ⟨B', rfl⟩ := Em.surjective B
  have hrel : ∀ M : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4,
      (∀ i j, Em M i j = h.bar (Em M (Fin.rev j) (Fin.rev i))) →
        ∀ i j, M i j = (M (Fin.rev j) (Fin.rev i)) ^ 2 := by
    intro M hM i j
    have := hM i j
    rw [hEm, hEm, burnsideF4m_bar_eF4e] at this
    exact e.injective this
  have hA2' : A' * A' = 1 := Em.injective (by rw [map_mul, hA2, map_one])
  have hB2' : B' * B' = 1 := Em.injective (by rw [map_mul, hB2, map_one])
  have hAB' : A' * B' = B' * A' := Em.injective (by rw [map_mul, map_mul, hAB])
  rcases burnsideF4m_gu3_F4 A' B' (hrel A' hA) (hrel B' hB) hA2' hB2' hAB' with h1 | h1 | h1
  · exact Or.inl (by rw [h1, map_one])
  · exact Or.inr (Or.inl (by rw [h1, map_one]))
  · exact Or.inr (Or.inr (by rw [h1]))

theorem burnsideF4m_u5_cube (h : UnitaryFieldData 2 1 K) (δ : Kˣ) (hδ : h.norm (δ : K) = 1) :
    δ ^ 3 = 1 := by
  apply Units.ext
  have e : h.norm (δ : K) = (δ : K) ^ 3 := by
    rw [UnitaryFieldData.norm, h.bar_apply]
    ring
  rw [Units.val_pow_eq_pow_val, ← e, hδ, Units.val_one]

end FieldK

section U5Aut

variable {K : Type} [Field K] (h : UnitaryFieldData 2 1 K)

theorem burnsideF4m_u5_dGL_su (δ : Kˣ) (hδ : h.norm (δ : K) = 1) :
    GeneralLinearGroup.scalar (HypIndex 2 1) δ * dGL h δ ∈ hypSU h 2 1 := by
  have h3 := burnsideF4m_u5_cube h δ hδ
  refine mem_hypSU.mpr ⟨?_, ?_⟩
  · have hs : GeneralLinearGroup.scalar (HypIndex 2 1) δ ∈ hypUnitary h 2 1 := by
      rw [mem_hypUnitary, GeneralLinearGroup.coe_scalar, scalar_gram, hδ, one_smul]
    exact mem_hypUnitary.mp (mul_mem hs (dGL_mem_hypUnitary h hδ))
  · rw [Units.val_mul, Matrix.det_mul, det_dGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      show Fintype.card (HypIndex 2 1) = 5 from rfl, ← pow_succ,
      show (5 + 1 : ℕ) = 3 * 2 by norm_num, pow_mul, ← Units.val_pow_eq_pow_val, h3, Units.val_one,
      one_pow]

theorem burnsideF4m_u5_dHom_eq (δ : normOne h) :
    dHom h δ = innM h ⟨_, burnsideF4m_u5_dGL_su h δ ((mem_normOne h).1 δ.2)⟩ := by
  refine MulEquiv.ext fun z => ?_
  obtain ⟨y, rfl⟩ := hypProj_surjective h 2 1 z
  rw [dHom_apply, innM_apply, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [phi_dGam_apply]
  have hc : ∀ X : GL (HypIndex 2 1) K, GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ) * X =
      X * GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ) := fun X => by
    ext i j
    simp [GeneralLinearGroup.coe_scalar, mul_comm]
  show dGL h δ * (y : GL (HypIndex 2 1) K) * (dGL h δ)⁻¹ =
    GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ) * dGL h δ * (y : GL (HypIndex 2 1) K) *
      (GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ) * dGL h δ)⁻¹
  rw [_root_.mul_inv_rev]
  calc dGL h δ * (y : GL (HypIndex 2 1) K) * (dGL h δ)⁻¹ =
      GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ) * (dGL h δ * (y : GL (HypIndex 2 1) K) *
        (dGL h δ)⁻¹) * (GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ))⁻¹ := by
        rw [hc, mul_assoc _ _ (GeneralLinearGroup.scalar (HypIndex 2 1) (δ : Kˣ))⁻¹, mul_inv_cancel,
          mul_one]
    _ = _ := by group

theorem burnsideF4m_u5_normalForm (α : MulAut (hypPSU h 2 1)) :
    ∃ (g : hypSU h 2 1) (σ : K ≃+* K), α = innM h g * fieldP h σ := by
  obtain ⟨x₀, hx₀⟩ := Phi_surjective h α
  obtain ⟨x, hxΦ, hxr, hxU⟩ := exists_unitary_rep h (r := 2) (ε := 1) (by norm_num)
    (by norm_num) (by norm_num) x₀
  set A : GL (HypIndex 2 1) K := (x : SemiGL (HypIndex 2 1) K).left with hAdef
  set σ : K ≃+* K := (x : SemiGL (HypIndex 2 1) K).right with hσdef
  set δ : Kˣ := Matrix.GeneralLinearGroup.det A with hδdef
  have hδ : h.norm (δ : K) = 1 := by
    rw [hδdef, Matrix.GeneralLinearGroup.val_det_apply]
    exact norm_det_eq_one hxU
  have hδ' : δ ∈ normOne h := (mem_normOne h).2 hδ
  have hδi : h.norm ((δ⁻¹ : Kˣ) : K) = 1 := (mem_normOne h).1 ((normOne h).inv_mem hδ')
  have hgu : A * dGL h δ⁻¹ ∈ hypUnitary h 2 1 := mul_mem hxU (dGL_mem_hypUnitary h hδi)
  have hgd : ((A * dGL h δ⁻¹ : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K).det = 1 := by
    rw [Units.val_mul, Matrix.det_mul, det_dGL, ← Matrix.GeneralLinearGroup.val_det_apply,
      ← hδdef, Units.val_inv_eq_inv_val, mul_inv_cancel₀ δ.ne_zero]
  let g : hypSU h 2 1 := ⟨A * dGL h δ⁻¹, mem_gramSU.2 ⟨mem_hypUnitary.1 hgu, hgd⟩⟩
  have hA : (g : GL (HypIndex 2 1) K) * dGL h δ = A := by
    change A * dGL h δ⁻¹ * dGL h δ = A
    rw [mul_assoc, ← dGL_mul, inv_mul_cancel, dGL_one, mul_one]
  have hx : x = inlG g * dGam h δ hδ * inrGam h σ := by
    refine Subtype.ext ?_
    rw [← SemidirectProduct.inl_left_mul_inr_right (x : SemiGL (HypIndex 2 1) K)]
    change SemidirectProduct.inl A * SemidirectProduct.inr σ =
      SemidirectProduct.inl (g : GL (HypIndex 2 1) K) * SemidirectProduct.inl (dGL h δ) *
        SemidirectProduct.inr σ
    rw [← map_mul, hA]
  have hα' : α = innM h g * dHom h ⟨δ, hδ'⟩ * fieldP h σ := by
    have h1 : Phi h x = α := hxΦ.trans hx₀
    rw [← h1, hx, map_mul, map_mul, Phi_inlG]
    rfl
  rw [burnsideF4m_u5_dHom_eq h ⟨δ, hδ'⟩, ← map_mul] at hα'
  exact ⟨_, σ, hα'⟩

theorem burnsideF4m_u5_sq_inner (α : MulAut (hypPSU h 2 1)) :
    ∃ y : hypPSU h 2 1, α * α = MulAut.conj y := by
  obtain ⟨g, σ, rfl⟩ := burnsideF4m_u5_normalForm h α
  have hF : fieldP h σ * fieldP h σ = 1 := by
    rw [← map_mul, burnsideF4m_ringEquiv_sq h σ, map_one]
  refine ⟨hypProj h 2 1 g * fieldP h σ (hypProj h 2 1 g), MulEquiv.ext fun z => ?_⟩
  have hz : fieldP h σ (fieldP h σ z) = z := by
    have := congrArg (fun β : MulAut (hypPSU h 2 1) => β z) hF
    simpa only [MulAut.mul_apply, MulAut.one_apply] using this
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, innM_apply, innM_apply, map_mul,
    map_mul, map_inv, hz, MulAut.conj_apply]
  group

theorem burnsideF4m_u5_proj_injective : Function.Injective (hypProj h 2 1) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_hypProj, eq_bot_iff]
  rintro g ⟨c, hc, hc5, hg⟩
  have h3 := burnsideF4m_u5_cube h c hc
  have hc1 : c = 1 := by
    have e : c = (c ^ 3) ^ 2 * (c ^ (2 * 2 + 1))⁻¹ := by group
    rw [e, h3, hc5, one_pow, inv_one, mul_one]
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [hg, hc1, map_one]
  rfl

end U5Aut

section Ext

variable {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}

theorem burnsideF4m_u5_sq_mem (hyp : HypF_4_4g .U5 2 1 Gp M₁ M₂) (e : E) : e * e ∈ Gp := by
  haveI := hyp.normal
  obtain ⟨K, fK, h, Ψ, -, -⟩ := burnsideF4m_U5_chart hyp
  set Θ : E →* MulAut (hypPSU h 2 1) :=
    (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp) with hΘdef
  have hΘinj : Function.Injective Θ :=
    (MulAut.congr Ψ.symm).injective.comp (burnsideF4d_rho_injective hyp.centralizer_trivial)
  have hΘapp : ∀ (e : E) (y : hypPSU h 2 1), ((Ψ (Θ e y) : ↥Gp) : E) = e * Ψ y * e⁻¹ := by
    intro e y
    show ((Ψ (Ψ.symm (burnsideF4d_rho Gp e (Ψ y))) : ↥Gp) : E) = _
    rw [MulEquiv.apply_symm_apply, burnsideF4d_rho_apply]
  obtain ⟨b, hb⟩ := burnsideF4m_u5_sq_inner h (Θ e)
  have hsq : Θ (e * e) = MulAut.conj b := by rw [map_mul, hb]
  have hΘb : Θ ((Ψ b : ↥Gp) : E) = MulAut.conj b := by
    refine MulEquiv.ext fun y => Ψ.injective (Subtype.ext ?_)
    rw [hΘapp, MulAut.conj_apply]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have := hΘinj (hsq.trans hΘb.symm)
  rw [this]
  exact (Ψ b).2

end Ext

section SU

variable {K : Type} [Field K] {h : UnitaryFieldData 2 1 K}

@[expose] def burnsideF4m_mid : Fin 3 → HypIndex 2 1 := ![ιe₂, ιz, ιf₂]

theorem burnsideF4m_partner_mid :
    ∀ k : Fin 3, hypPartner (burnsideF4m_mid k) = burnsideF4m_mid (Fin.rev k) := by
  decide

theorem burnsideF4m_mid_ne : ∀ k : Fin 3, burnsideF4m_mid k ≠ ιe₁ ∧ burnsideF4m_mid k ≠ ιf₁ := by
  decide

theorem burnsideF4m_mid_inj : ∀ i j : Fin 3, burnsideF4m_mid i = burnsideF4m_mid j ↔ i = j := by
  decide

@[expose] noncomputable def burnsideF4m_blk (g : hypSU h 2 1) : Matrix (Fin 3) (Fin 3) K :=
  (mat g).submatrix burnsideF4m_mid burnsideF4m_mid

theorem burnsideF4m_row_f₁ {g : hypSU h 2 1} (hg : g ∈ u5PtStab h) (b : HypIndex 2 1)
    (hb : b ≠ ιf₁) : mat g ιf₁ b = 0 := by
  have hgi : g⁻¹ ∈ u5PtStab h := inv_mem hg
  have h1 := mat_inv_apply g⁻¹ ιf₁ b
  rw [inv_inv] at h1
  rw [h1, show hypPartner ιf₁ = ιe₁ from rfl, (mem_u5PtStab_iff g⁻¹).1 hgi (hypPartner b) ?_,
    map_zero]
  intro e
  apply hb
  rw [← hypPartner_hypPartner b, e]
  rfl

theorem burnsideF4m_e₁_mul {g g' : hypSU h 2 1} (hg' : g' ∈ u5PtStab h) :
    mat (g * g') ιe₁ ιe₁ = mat g ιe₁ ιe₁ * mat g' ιe₁ ιe₁ := by
  have hcol := (mem_u5PtStab_iff g').1 hg'
  rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single ιe₁]
  · intro c _ hc
    rw [hcol c hc, mul_zero]
  · simp

theorem burnsideF4m_blk_mul {g g' : hypSU h 2 1} (hg : g ∈ u5PtStab h) (hg' : g' ∈ u5PtStab h) :
    burnsideF4m_blk (g * g') = burnsideF4m_blk g * burnsideF4m_blk g' := by
  ext i j
  have hc : mat g (burnsideF4m_mid i) ιe₁ = 0 :=
    (mem_u5PtStab_iff g).1 hg _ (burnsideF4m_mid_ne i).1
  have hr : mat g' ιf₁ (burnsideF4m_mid j) = 0 := burnsideF4m_row_f₁ hg' _ (burnsideF4m_mid_ne j).2
  simp only [burnsideF4m_blk, Matrix.submatrix_apply, mat_mul, Matrix.mul_apply,
    Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_one, Fin.sum_univ_three]
  rw [hc, hr]
  simp [burnsideF4m_mid]
  ring

theorem burnsideF4m_blk_one : burnsideF4m_blk (1 : hypSU h 2 1) = 1 := by
  ext i j
  simp only [burnsideF4m_blk, Matrix.submatrix_apply, mat_one, Matrix.one_apply,
    burnsideF4m_mid_inj]

theorem burnsideF4m_blk_selfadj {a : hypSU h 2 1} (ha : a * a = 1) (i j : Fin 3) :
    burnsideF4m_blk a i j = h.bar (burnsideF4m_blk a (Fin.rev j) (Fin.rev i)) := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have := mat_inv_apply a (burnsideF4m_mid i) (burnsideF4m_mid j)
  rw [hai, burnsideF4m_partner_mid, burnsideF4m_partner_mid] at this
  exact this

variable (h) in
@[expose] noncomputable def burnsideF4m_K0 : Subgroup (hypSU h 2 1) where
  carrier := {g | g ∈ u5PtStab h ∧ burnsideF4m_blk g = 1 ∧ mat g ιe₁ ιe₁ = 1}
  mul_mem' := by
    intro g g' hg hg'
    obtain ⟨hg, hb, he⟩ := hg
    obtain ⟨hg', hb', he'⟩ := hg'
    exact ⟨mul_mem hg hg', by rw [burnsideF4m_blk_mul hg hg', hb, hb', mul_one],
      by rw [burnsideF4m_e₁_mul hg', he, he', mul_one]⟩
  one_mem' := ⟨one_mem _, burnsideF4m_blk_one, by rw [mat_one, Matrix.one_apply_eq]⟩
  inv_mem' := by
    intro g hg
    obtain ⟨hg, hb, he⟩ := hg
    have hgi : g⁻¹ ∈ u5PtStab h := inv_mem hg
    refine ⟨hgi, ?_, ?_⟩
    · have := burnsideF4m_blk_mul hgi hg
      rw [inv_mul_cancel, burnsideF4m_blk_one, hb, mul_one] at this
      exact this.symm
    · have := burnsideF4m_e₁_mul (g := g⁻¹) hg
      rw [inv_mul_cancel, mat_one, Matrix.one_apply_eq, he, mul_one] at this
      exact this.symm

theorem burnsideF4m_K0_le_U : burnsideF4m_K0 h ≤ hypUnitriangular h 2 1 := by
  rintro g ⟨hg, hb, he⟩
  have hcol := (mem_u5PtStab_iff g).1 hg
  have hrow := burnsideF4m_row_f₁ hg
  have hμ : mat g ιf₁ ιf₁ = 1 := by
    have h1 := burnsideF4m_e₁_mul (g := g⁻¹) hg
    rw [inv_mul_cancel, mat_one, Matrix.one_apply_eq, he, mul_one, mat_inv_apply] at h1
    have h2 := congrArg h.bar h1
    rw [h.bar_bar, map_one] at h2
    exact h2.symm
  have hb' : ∀ i j, mat g (burnsideF4m_mid i) (burnsideF4m_mid j) = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hb i) j
    simpa [burnsideF4m_blk, Matrix.one_apply] using this
  refine mem_hypUnitriangular.mpr ⟨fun i j hij => ?_, fun a => ?_⟩
  · change mat g i j = 0
    rcases CFSG.Quasithin.H13.Sec53F.Unit.hypIndex_cases i with rfl | rfl | rfl | rfl | rfl <;>
      rcases CFSG.Quasithin.H13.Sec53F.Unit.hypIndex_cases j with rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact absurd hij (by decide)
        | exact hcol _ (by decide)
        | exact hrow _ (by decide)
        | simpa [burnsideF4m_mid] using hb' 1 0
        | simpa [burnsideF4m_mid] using hb' 2 0
        | simpa [burnsideF4m_mid] using hb' 2 1
  · change mat g a a = 1
    rcases CFSG.Quasithin.H13.Sec53F.Unit.hypIndex_cases a with rfl | rfl | rfl | rfl | rfl
    · exact he
    · simpa [burnsideF4m_mid] using hb' 0 0
    · simpa [burnsideF4m_mid] using hb' 1 1
    · simpa [burnsideF4m_mid] using hb' 2 2
    · exact hμ

theorem burnsideF4m_K0_le_pCore : burnsideF4m_K0 h ≤ pCoreOf 2 (u5PtStab h) := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun g hg => hg.1) ?_
    ((CFSG.RankThree.CentralLiftU.isPGroup_hypUnitriangular le_rfl).to_le burnsideF4m_K0_le_U)
  intro g hg
  have hgi : g⁻¹ ∈ u5PtStab h := inv_mem hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨hx, hbx, hex⟩
    refine ⟨mul_mem (mul_mem hg hx) hgi, ?_, ?_⟩
    · rw [burnsideF4m_blk_mul (mul_mem hg hx) hgi, burnsideF4m_blk_mul hg hx, hbx, mul_one,
        ← burnsideF4m_blk_mul hg hgi, mul_inv_cancel, burnsideF4m_blk_one]
    · rw [burnsideF4m_e₁_mul hgi, burnsideF4m_e₁_mul hx, hex, mul_one, ← burnsideF4m_e₁_mul hgi,
        mul_inv_cancel, mat_one, Matrix.one_apply_eq]
  · rintro ⟨hx, hbx, hex⟩
    have hx' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    have hxS : x ∈ u5PtStab h := by rw [hx']; exact mul_mem (mul_mem hgi hx) hg
    refine ⟨hxS, ?_, ?_⟩
    · rw [hx', burnsideF4m_blk_mul (mul_mem hgi hx) hg, burnsideF4m_blk_mul hgi hx, hbx, mul_one,
        ← burnsideF4m_blk_mul hgi hg, inv_mul_cancel, burnsideF4m_blk_one]
    · rw [hx', burnsideF4m_e₁_mul hg, burnsideF4m_e₁_mul hx, hex, mul_one, ← burnsideF4m_e₁_mul hg,
        inv_mul_cancel, mat_one, Matrix.one_apply_eq]

theorem burnsideF4m_u5_A4_SU {a b t : hypSU h 2 1} (ha : a ∈ u5PtStab h) (hb : b ∈ u5PtStab h)
    (ht : t ∈ u5PtStab h) (h1 : a * a = 1) (h2 : b * b = 1) (h3 : a * b = b * a)
    (h4 : t * a = b * t) (h5 : t * b = a * b * t) (h6 : t * t * t = 1) :
    a ∈ burnsideF4m_K0 h := by
  have hA2 : burnsideF4m_blk a * burnsideF4m_blk a = 1 := by
    rw [← burnsideF4m_blk_mul ha ha, h1, burnsideF4m_blk_one]
  have hB2 : burnsideF4m_blk b * burnsideF4m_blk b = 1 := by
    rw [← burnsideF4m_blk_mul hb hb, h2, burnsideF4m_blk_one]
  have hAB : burnsideF4m_blk a * burnsideF4m_blk b = burnsideF4m_blk b * burnsideF4m_blk a := by
    rw [← burnsideF4m_blk_mul ha hb, ← burnsideF4m_blk_mul hb ha, h3]
  have hTA : burnsideF4m_blk t * burnsideF4m_blk a = burnsideF4m_blk b * burnsideF4m_blk t := by
    rw [← burnsideF4m_blk_mul ht ha, ← burnsideF4m_blk_mul hb ht, h4]
  have hTB : burnsideF4m_blk t * burnsideF4m_blk b =
      burnsideF4m_blk a * burnsideF4m_blk b * burnsideF4m_blk t := by
    rw [← burnsideF4m_blk_mul ht hb, ← burnsideF4m_blk_mul ha hb,
      ← burnsideF4m_blk_mul (mul_mem ha hb) ht, h5]
  have hT3 : burnsideF4m_blk t * burnsideF4m_blk t * burnsideF4m_blk t = 1 := by
    rw [← burnsideF4m_blk_mul ht ht, ← burnsideF4m_blk_mul (mul_mem ht ht) ht, h6,
      burnsideF4m_blk_one]
  have hcancel : ∀ X : Matrix (Fin 3) (Fin 3) K, burnsideF4m_blk t * X = burnsideF4m_blk t →
      X = 1 := by
    intro X hX
    calc X = burnsideF4m_blk t * burnsideF4m_blk t * burnsideF4m_blk t * X := by
          rw [hT3, Matrix.one_mul]
      _ = burnsideF4m_blk t * burnsideF4m_blk t * (burnsideF4m_blk t * X) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hX, hT3]
  have hAone : burnsideF4m_blk a = 1 := by
    rcases burnsideF4m_gu3_K h _ _ (burnsideF4m_blk_selfadj h1) (burnsideF4m_blk_selfadj h2)
      hA2 hB2 hAB with e | e | e
    · exact e
    · exact hcancel _ (by rw [hTA, e, Matrix.one_mul])
    · have hB1 : burnsideF4m_blk b = 1 := hcancel _ (by rw [hTB, e, hB2, Matrix.one_mul])
      rw [e, hB1]
  refine ⟨ha, hAone, ?_⟩
  have hl : mat a ιe₁ ιe₁ * mat a ιe₁ ιe₁ = 1 := by
    rw [← burnsideF4m_e₁_mul ha, h1, mat_one, Matrix.one_apply_eq]
  have := h.charP
  rcases mul_self_eq_one_iff.mp hl with e | e
  · exact e
  · rw [e, CharTwo.neg_eq]

end SU

theorem burnsideF4m_F436U5_A_holds : burnsideF4m_F436U5_A := by
  intro E _ Gp M₁ M₂ hyp a b t ha hb ht h1 h2 h3 h4 h5 h6
  haveI := hyp.normal
  haveI := hyp.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsq := burnsideF4m_u5_sq_mem hyp.toHypF_4_4g
  have htG : t ∈ Gp := by
    have e : t * t * (t * t) = t := by
      calc t * t * (t * t) = t ^ 3 * t := by rw [pow_three]; simp only [mul_assoc]
        _ = t := by rw [h6, one_mul]
    rw [← e]
    exact hsq (t * t)
  have haG : a ∈ Gp := by
    have e : a = t * (b * t⁻¹ * b⁻¹) := by
      calc a = a * b * b⁻¹ := by group
        _ = t * b * t⁻¹ * b⁻¹ := by rw [h5]
        _ = t * (b * t⁻¹ * b⁻¹) := by group
    rw [e]
    exact Gp.mul_mem htG (hyp.normal.conj_mem _ (Gp.inv_mem htG) b)
  have hbG : b ∈ Gp := by
    rw [← h4]
    exact hyp.normal.conj_mem _ haG t
  obtain ⟨K, fK, h, Ψ, hP1, -⟩ := burnsideF4m_U5_chart hyp.toHypF_4_4g
  set φ : hypSU h 2 1 →* E := (Gp.subtype.comp Ψ.toMonoidHom).comp (hypProj h 2 1) with hφ
  have hφinj : Function.Injective φ :=
    (Gp.subtype_injective.comp Ψ.injective).comp (burnsideF4m_u5_proj_injective h)
  have hPt : u5PtP h = (u5PtStab h).map (hypProj h 2 1) := by
    ext x
    obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 x
    constructor
    · intro hx
      exact ⟨g, CFSG.Quasithin.H13.F431.Un.proj_mem_u5PtP_iff.1 hx, rfl⟩
    · rintro ⟨g', hg', e⟩
      rw [← e]
      exact CFSG.Quasithin.H13.F431.Un.proj_mem_u5PtP_iff.2 hg'
  have hGM : Gp ⊓ M₁ = (u5PtStab h).map φ := by
    rw [hP1, hPt, Subgroup.map_map]
  have hpull : ∀ {x : E}, x ∈ Gp → x ∈ M₁ → ∃ x₀ ∈ u5PtStab h, φ x₀ = x := by
    intro x hxG hxM
    have hx : x ∈ (u5PtStab h).map φ := hGM ▸ (⟨hxG, hxM⟩ : x ∈ Gp ⊓ M₁)
    obtain ⟨x₀, hx₀, e⟩ := hx
    exact ⟨x₀, hx₀, e⟩
  obtain ⟨a₀, ha₀, rfl⟩ := hpull haG ha
  obtain ⟨b₀, hb₀, rfl⟩ := hpull hbG hb
  obtain ⟨t₀, ht₀, rfl⟩ := hpull htG ht
  have e1 : a₀ * a₀ = 1 := hφinj (by rw [map_mul, h1, map_one])
  have e2 : b₀ * b₀ = 1 := hφinj (by rw [map_mul, h2, map_one])
  have e3 : a₀ * b₀ = b₀ * a₀ := hφinj (by rw [map_mul, map_mul, h3])
  have e4 : t₀ * a₀ = b₀ * t₀ := hφinj (by
    rw [map_mul, map_mul, ← h4]
    group)
  have e5 : t₀ * b₀ = a₀ * b₀ * t₀ := hφinj (by
    rw [map_mul, map_mul, map_mul, ← h5]
    group)
  have e6 : t₀ * t₀ * t₀ = 1 := hφinj (by
    rw [map_mul, map_mul, map_one]
    calc φ t₀ * φ t₀ * φ t₀ = φ t₀ ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := h6)
  have hK0 := burnsideF4m_u5_A4_SU ha₀ hb₀ ht₀ e1 e2 e3 e4 e5 e6
  have hP : φ a₀ ∈ pCoreOf 2 (Gp ⊓ M₁) := by
    rw [hGM, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hφinj]
    exact Subgroup.mem_map_of_mem φ (burnsideF4m_K0_le_pCore hK0)
  have hle : pCoreOf 2 (Gp ⊓ M₁) ≤ pCoreOf 2 M₁ := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_right) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    intro m hm
    refine CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (Gp ⊓ M₁) ?_
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxG, hxM⟩
      exact ⟨hyp.normal.conj_mem x hxG m, M₁.mul_mem (M₁.mul_mem hm hxM) (M₁.inv_mem hm)⟩
    · rintro ⟨hxG, hxM⟩
      have e : x = m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ := by group
      rw [e]
      exact ⟨hyp.normal.conj_mem _ hxG m⁻¹,
        M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hm) hxM) (M₁.inv_mem (M₁.inv_mem hm))⟩
  exact hle hP

end CFSG.ASVolI
