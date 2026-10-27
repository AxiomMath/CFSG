module

public import CFSG.Quasithin.Vol2.Ch11SecS12YD
public import CFSG.Quasithin.Vol2.Ch11SecS12YB
public import CFSG.Quasithin.Vol2.Ch11SecS12YC

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem dgP_mul_const (x : Fin 3 → Fˣ) (c : Fˣ) : dgP (fun i => x i * c) = dgP x := by
  rw [dgP_apply, dgP_apply, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨c⁻¹, Units.ext ?_⟩
  rw [Units.val_mul, dg3_coe, dg3_coe, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    diagonal_mul_diagonal]
  congr 1
  funext i
  simp

theorem mk_eq_dgP {g : GL (Fin 3) F} {x : Fin 3 → Fˣ}
    (h : (g : Matrix (Fin 3) (Fin 3) F) = diagonal fun i => (x i : F)) :
    ProjGenLinGroup.mk g = dgP x := by
  rw [dgP_apply]
  congr 1
  exact Units.ext h

@[expose] noncomputable def dgP0 : Fˣ →* PGL3 F :=
  dgP.comp (MonoidHom.mulSingle (fun _ : Fin 3 => Fˣ) 0)

variable [Finite F]

omit [Finite F] in
theorem card_units_four (hF : Nat.card F = 4) : Nat.card Fˣ = 3 := by
  rw [Nat.card_units, hF]

theorem card_range_dgP_le_nine (hF : Nat.card F = 4) :
    Nat.card ↥(dgP (F := F)).range ≤ 9 := by
  have h := card_range_dgP_le (F := F)
  rwa [Nat.card_prod, card_units_four hF] at h

theorem card_range_dgP0_le (hF : Nat.card F = 4) : Nat.card ↥(dgP0 (F := F)).range ≤ 3 := by
  exact (Nat.card_le_card_of_surjective _ (dgP0 (F := F)).rangeRestrict_surjective).trans
    (card_units_four hF).le

variable [CharP F 2]

theorem exists_weyl_pgl (hF : Nat.card F = 4) {j : Fin 2} {g₁ h₀ : GL (Fin 3) F}
    (hgN : ProjGenLinGroup.mk g₁ ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F j) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (hgsc : ProjGenLinGroup.mk g₁ ∈ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)))
    (hg3 : ProjGenLinGroup.mk g₁ ^ 3 = 1) (hg1 : ProjGenLinGroup.mk g₁ ≠ 1)
    (hcomm : ProjGenLinGroup.mk h₀ * ProjGenLinGroup.mk g₁ =
      ProjGenLinGroup.mk g₁ * ProjGenLinGroup.mk h₀)
    (hh3 : ProjGenLinGroup.mk h₀ ^ 3 = 1)
    (hX : 9 ≤ Nat.card ↥(Subgroup.zpowers (ProjGenLinGroup.mk g₁) ⊔
      Subgroup.zpowers (ProjGenLinGroup.mk h₀))) :
    ∃ w ∈ (thetaP F).range, w ∈ Subgroup.normalizer
        ((Subgroup.zpowers (ProjGenLinGroup.mk g₁) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk h₀) :
          Subgroup (PGL3 F)) : Set (PGL3 F)) ∧
      w * ProjGenLinGroup.mk g₁ * w⁻¹ ∉ Subgroup.zpowers (ProjGenLinGroup.mk g₁) := by
  set X := Subgroup.zpowers (ProjGenLinGroup.mk g₁) ⊔ Subgroup.zpowers (ProjGenLinGroup.mk h₀)
    with hXd
  obtain ⟨m, a, d, had, hm⟩ := exists_diag_conj hF hgN hgsc hg3 hg1
  have hdetm : ((m * g₁ * m⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [hm, Matrix.det_diagonal, Fin.prod_univ_three] at hdetm
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, ne_eq, mul_eq_zero, not_or] at hdetm
  obtain ⟨⟨ha0, hd0⟩, -⟩ := hdetm
  have hg' : ProjGenLinGroup.mk (m * g₁ * m⁻¹) = dgP ![Units.mk0 a ha0, Units.mk0 d hd0,
      Units.mk0 d hd0] := mk_eq_dgP (by
    rw [hm]
    congr 1
    funext i
    fin_cases i <;> rfl)
  have hconj : ∀ y : GL (Fin 3) F, ProjGenLinGroup.mk (m * y * m⁻¹) =
      ProjGenLinGroup.mk m * ProjGenLinGroup.mk y * (ProjGenLinGroup.mk m)⁻¹ := fun y => by
    rw [map_mul, map_mul, map_inv]
  set h' := m * h₀ * m⁻¹ with hh'
  have hcomm' : ProjGenLinGroup.mk h' * ProjGenLinGroup.mk (m * g₁ * m⁻¹) =
      ProjGenLinGroup.mk (m * g₁ * m⁻¹) * ProjGenLinGroup.mk h' := by
    rw [hh', hconj, hconj]
    calc ProjGenLinGroup.mk m * ProjGenLinGroup.mk h₀ * (ProjGenLinGroup.mk m)⁻¹ *
          (ProjGenLinGroup.mk m * ProjGenLinGroup.mk g₁ * (ProjGenLinGroup.mk m)⁻¹)
        = ProjGenLinGroup.mk m * (ProjGenLinGroup.mk h₀ * ProjGenLinGroup.mk g₁) *
          (ProjGenLinGroup.mk m)⁻¹ := by group
      _ = ProjGenLinGroup.mk m * (ProjGenLinGroup.mk g₁ * ProjGenLinGroup.mk h₀) *
          (ProjGenLinGroup.mk m)⁻¹ := by rw [hcomm]
      _ = _ := by group
  obtain ⟨k01, k02, k10, k20⟩ := block_of_commute hm had hcomm'
  have hh'3 : ProjGenLinGroup.mk h' ^ 3 = 1 := by
    rw [hh', hconj, conj_pow, hh3, mul_one, mul_inv_cancel]
  obtain ⟨k00, hB3⟩ := lower_cube_eq_one hF k01 k02 k10 k20 hh'3
  have hmemD : ∀ x : Fin 3 → Fˣ, x 1 = x 2 → dgP x ∈ (dgP0 (F := F)).range := by
    intro x hx
    refine ⟨x 0 * (x 1)⁻¹, ?_⟩
    rw [dgP0, MonoidHom.comp_apply, ← dgP_mul_const _ (x 1)]
    congr 1
    funext i
    fin_cases i <;> simp [hx]
  have hBns : ¬ ((h' : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
      (h' : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 ∧
      (h' : Matrix (Fin 3) (Fin 3) F) 1 1 = (h' : Matrix (Fin 3) (Fin 3) F) 2 2) := by
    rintro ⟨k12, k21, k11⟩
    have h11 : (h' : Matrix (Fin 3) (Fin 3) F) 1 1 ≠ 0 := by
      intro h0
      have hdet : (h' : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
        rw [← GeneralLinearGroup.val_det_apply]
        exact Units.ne_zero _
      apply hdet
      rw [Matrix.det_fin_three, ← k11, h0, k12, k21, k01, k02]
      ring
    have hh'd : ProjGenLinGroup.mk h' = dgP ![Units.mk0 _ k00, Units.mk0 _ h11,
        Units.mk0 _ h11] := mk_eq_dgP (by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [k01, k02, k10, k20, k12, k21, k11])
    have hle : X.map (MulAut.conj (ProjGenLinGroup.mk m)).toMonoidHom ≤
        (dgP0 (F := F)).range := by
      rw [hXd, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hconj, hg']
        exact hmemD _ rfl
      · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hconj, ← hh', hh'd]
        exact hmemD _ rfl
    have hcard := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj (ProjGenLinGroup.mk m)).injective] at hcard
    have := hX.trans (hcard.trans (card_range_dgP0_le hF))
    norm_num at this
  have hω : (a / d) ^ 2 + a / d + 1 = 0 := by
    have h3 : (a / d) ^ 3 = 1 := cube_eq_one_of_card_four hF (div_ne_zero ha0 hd0)
    have h1 : a / d ≠ 1 := fun h => had ((div_eq_one_iff_eq hd0).mp h)
    have : (a / d - 1) * ((a / d) ^ 2 + a / d + 1) = 0 := by linear_combination h3
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)
  obtain ⟨P, hP, β₁, β₂, hBP⟩ := exists_diag_two hB3 (by simpa using hBns) hω
  obtain ⟨C, hCc, hC⟩ := exists_block_conj k01 k02 k10 k20 hP hBP
  have hdetC : ((C⁻¹ * h' * C : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  rw [hC, Matrix.det_diagonal, Fin.prod_univ_three] at hdetC
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, ne_eq, mul_eq_zero, not_or] at hdetC
  obtain ⟨⟨-, hb1⟩, hb2⟩ := hdetC
  set q := ProjGenLinGroup.mk (C⁻¹ * m) with hq
  have hqconj : ∀ y : GL (Fin 3) F, q * ProjGenLinGroup.mk y * q⁻¹ =
      ProjGenLinGroup.mk (C⁻¹ * (m * y * m⁻¹) * C) := fun y => by
    rw [hq]
    simp only [map_mul, map_inv]
    group
  have hq1 : q * ProjGenLinGroup.mk g₁ * q⁻¹ =
      dgP ![Units.mk0 a ha0, Units.mk0 d hd0, Units.mk0 d hd0] := by
    rw [hqconj]
    refine mk_eq_dgP ?_
    rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hm, ← hCc a d, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hq2 : q * ProjGenLinGroup.mk h₀ * q⁻¹ =
      dgP ![Units.mk0 _ k00, Units.mk0 β₁ hb1, Units.mk0 β₂ hb2] := by
    rw [hqconj, ← hh']
    refine mk_eq_dgP ?_
    rw [hC]
    congr 1
    funext i
    fin_cases i <;> rfl
  have hXD : X.map (MulAut.conj q).toMonoidHom ≤ (dgP (F := F)).range := by
    rw [hXd, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hq1]
      exact ⟨_, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hq2]
      exact ⟨_, rfl⟩
  have hXeq : X.map (MulAut.conj q).toMonoidHom = (dgP (F := F)).range := by
    refine Subgroup.eq_of_le_of_card_ge hXD ?_
    rw [Subgroup.card_map_of_injective (MulAut.conj q).injective]
    exact (card_range_dgP_le_nine hF).trans hX
  have hD : ∀ y, y ∈ X ↔ q * y * q⁻¹ ∈ (dgP (F := F)).range := fun y => by
    rw [← hXeq]
    constructor
    · intro hy
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y', hy', e⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
      have : y' = y := by
        have := congrArg (fun z => q⁻¹ * z * q) e
        simpa [mul_assoc] using this
      rwa [← this]
  have hR : ((thetaP F).range).Normal := by
    rw [range_thetaP_eq hF]
    exact Subgroup.commutator_normal ⊤ ⊤
  have hπ : ProjGenLinGroup.mk (perm3 : GL (Fin 3) F) ∈ (thetaP F).range :=
    mk_mem_range_thetaP det_perm3
  refine ⟨q⁻¹ * ProjGenLinGroup.mk perm3 * q, ?_, Subgroup.mem_normalizer_iff.mpr fun y => ?_,
    fun hmem => ?_⟩
  · have := hR.conj_mem _ hπ q⁻¹
    rwa [inv_inv] at this
  · rw [hD, hD]
    have e : q * (q⁻¹ * ProjGenLinGroup.mk perm3 * q * y *
        (q⁻¹ * ProjGenLinGroup.mk perm3 * q)⁻¹) * q⁻¹ =
        ProjGenLinGroup.mk perm3 * (q * y * q⁻¹) * (ProjGenLinGroup.mk perm3)⁻¹ := by group
    rw [e]
    constructor
    · intro h
      exact (perm3_conj_mem_range h).1
    · intro h
      have := (perm3_conj_mem_range h).2
      simpa [mul_assoc] using this
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have e1 : q * (q⁻¹ * ProjGenLinGroup.mk perm3 * q * ProjGenLinGroup.mk g₁ *
        (q⁻¹ * ProjGenLinGroup.mk perm3 * q)⁻¹) * q⁻¹ =
        ProjGenLinGroup.mk perm3 * (q * ProjGenLinGroup.mk g₁ * q⁻¹) *
          (ProjGenLinGroup.mk perm3)⁻¹ := by group
    rw [← hk, hq1, ← conj_zpow, hq1, ← map_zpow, dgP_apply, dgP_apply, ← map_inv, ← map_mul,
      ← map_mul, perm3_conj_dg3, ProjGenLinGroup.mk_eq_mk_iff] at e1
    obtain ⟨c, hc⟩ := e1
    have hc' := congrArg (fun A : GL (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) hc
    simp only [Units.val_mul, dg3_coe, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      diagonal_mul_diagonal] at hc'
    have e11 := congrFun (congrFun hc' 1) 1
    have e22 := congrFun (congrFun hc' 2) 2
    simp only [diagonal_apply_eq, Pi.pow_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Units.val_mk0] at e11 e22
    apply had
    exact e11.symm.trans e22

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
