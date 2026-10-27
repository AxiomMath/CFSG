module

public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU8Core
public import CFSG.RankThree.PartTwo.Sec19.SeitzFieldTwoU10

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG.LieType.SeitzGeneration CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
open Matrix

variable {K : Type} [Field K]

theorem scalar_of_suConj_eq_one (h : UnitaryFieldData 2 3 K) {X : unitaryIsom3 h}
    (hX : suConj h X = 1) :
    ∃ c : K, ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
  have := h.finite
  have hcomm : ∀ g : unitarySU 2 3 K 3, ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g
    have h1 := congrArg (fun φ : MulAut (unitarySU 2 3 K 3) =>
      ((φ g : unitarySU 2 3 K 3) : GL (Fin 3) K)) hX
    simp only [coe_suConj, MulAut.one_apply, Subgroup.coe_inv] at h1
    have h2 : (X : GL (Fin 3) K) * (g : GL (Fin 3) K) = (g : GL (Fin 3) K) * X := by
      calc (X : GL (Fin 3) K) * g = ((X : GL (Fin 3) K) * g * (X : GL (Fin 3) K)⁻¹) * X := by
            group
        _ = g * X := by rw [h1]
    exact congrArg Units.val h2
  have hK3 : 3 ∣ Nat.card K - 1 := by rw [h.card]; norm_num
  obtain ⟨ω, hω⟩ := Item19Res5Proof.exists_isPrimitiveRoot_three hK3
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hQ : 2 ^ 3 % 3 = 2 := by norm_num
  have hωN : h.norm ω = 1 := by
    rw [UnitaryFieldData.norm, bar_eq_of_cube h hQ hω3, ← pow_succ']
    exact hω3
  have hω2N : h.norm (ω ^ 2) = 1 := by
    rw [UnitaryFieldData.norm, map_pow, bar_eq_of_cube h hQ hω3, ← pow_mul, ← pow_add]
    calc ω ^ (2 + 2 * 2) = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  obtain ⟨Dω, hDω⟩ := exists_diag_mem h ![ω, ω ^ 2, 1]
    (by
      intro i
      fin_cases i
      · exact hωN
      · exact hω2N
      · show h.norm 1 = 1
        simp [UnitaryFieldData.norm])
    (by
      show ω * ω ^ 2 * 1 = 1
      linear_combination hω3)
  have hE : ∃ g : unitarySU 2 3 K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat K := ⟨⟨swapGL K, swapGL_mem_unitarySU h⟩, rfl⟩
  have hE' : ∃ g : unitarySU 2 3 K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat' K := ⟨⟨swapGL' K, swapGL'_mem_unitarySU h⟩, rfl⟩
  obtain ⟨gE, hgE⟩ := hE
  obtain ⟨gE', hgE'⟩ := hE'
  have h1 := hcomm Dω
  have h2 := hcomm gE
  have h3 := hcomm gE'
  rw [hDω] at h1
  rw [hgE] at h2
  rw [hgE'] at h3
  exact ⟨_, eq_smul_one_of_commute _ hω h1 h2 h3⟩

theorem suConj_eq_one_of_scalar_u38 (h : UnitaryFieldData 2 3 K) {X : unitaryIsom3 h} {c : K}
    (hX : ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) : suConj h X = 1 := by
  have hcomm : ∀ Z : GL (Fin 3) K, (X : GL (Fin 3) K) * Z = Z * X := by
    intro Z
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hX, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
      Matrix.mul_one]
  refine MulEquiv.ext (fun x => ?_)
  apply Subtype.ext
  rw [MulAut.one_apply, coe_suConj, Subgroup.coe_inv, hcomm, mul_inv_cancel_right]

theorem suField_mul_suConj_mul_inv (h : UnitaryFieldData 2 3 K) (σ : K ≃+* K) (A : unitaryIsom3 h) :
    suField h σ * suConj h A * (suField h σ)⁻¹ =
      suConj h ⟨glAut σ (A : GL (Fin 3) K), glAut_mem_unitaryIsom3 σ A.2⟩ := by
  refine MulEquiv.ext (fun x => ?_)
  apply Subtype.ext
  rw [MulAut.mul_apply, MulAut.mul_apply, coe_suField, coe_suConj, ← map_inv, coe_suField]
  change glAut σ ((A : GL (Fin 3) K) * glAut σ⁻¹ (x : GL (Fin 3) K) * (A : GL (Fin 3) K)⁻¹) =
    glAut σ (A : GL (Fin 3) K) * (x : GL (Fin 3) K) * (glAut σ (A : GL (Fin 3) K))⁻¹
  simp only [map_mul, map_inv, MulAut.apply_inv_self]

theorem closure_fixSet_eq_top_of_field_gen_eight
    (h : UnitaryFieldData 2 3 K) (D : Subgroup (MulAut (unitarySU 2 3 K 3)))
    (hD3 : ∀ φ ∈ D, φ ^ 3 = 1) (hDc : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    {φ : MulAut (unitarySU 2 3 K 3)} (hφD : φ ∈ D) (hφ : φ ∉ (suConj h).range)
    {y : MulAut (unitarySU 2 3 K 3)} (hyD : y ∈ D) (hy1 : y ≠ 1) (hy : y ∈ (suConj h).range) :
    Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) = ⊤ := by
  classical
  have := h.finite
  have hq : 2 < 2 ^ 3 := by norm_num
  have hφ1 : φ ≠ 1 := fun h1 => hφ ⟨1, by rw [map_one, h1]⟩
  obtain ⟨σ, hσ, H, hφH⟩ := eq_conj_suField_of_not_mem hq (hD3 φ hφD) hφ
  obtain ⟨B, hB⟩ := hy
  obtain ⟨c, hcdef⟩ : ∃ c : MulAut (unitarySU 2 3 K 3), c = suConj h H := ⟨_, rfl⟩
  obtain ⟨B', hB'def⟩ : ∃ B' : unitaryIsom3 h, B' = H⁻¹ * B * H := ⟨_, rfl⟩
  have hY' : suConj h B' = c⁻¹ * y * c := by
    rw [hB'def, map_mul, map_mul, map_inv, ← hB, ← hcdef]
  have hyc : y = c * suConj h B' * c⁻¹ := by rw [hY']; group
  have hφc : φ = c * suField h σ * c⁻¹ := by rw [hφH, hcdef]
  have hcomm : suField h σ * suConj h B' = suConj h B' * suField h σ := by
    have h1 := hDc φ hφD y hyD
    rw [hφc, hyc] at h1
    have h2 : c * (suField h σ * suConj h B') * c⁻¹ = c * (suConj h B' * suField h σ) * c⁻¹ := by
      calc c * (suField h σ * suConj h B') * c⁻¹
          = c * suField h σ * c⁻¹ * (c * suConj h B' * c⁻¹) := by group
        _ = c * suConj h B' * c⁻¹ * (c * suField h σ * c⁻¹) := h1
        _ = c * (suConj h B' * suField h σ) * c⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hconj : suConj h ⟨glAut σ (B' : GL (Fin 3) K), glAut_mem_unitaryIsom3 σ B'.2⟩ =
      suConj h B' := by
    rw [← suField_mul_suConj_mul_inv, hcomm, mul_inv_cancel_right]
  have hker : suConj h (B'⁻¹ * ⟨glAut σ (B' : GL (Fin 3) K), glAut_mem_unitaryIsom3 σ B'.2⟩) = 1 := by
    rw [map_mul, map_inv, hconj, inv_mul_cancel]
  obtain ⟨lam, hlam⟩ := scalar_of_suConj_eq_one h hker
  have hσB : ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      lam • ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have e : glAut σ (B' : GL (Fin 3) K) = (B' : GL (Fin 3) K) *
        ((B' : GL (Fin 3) K)⁻¹ * glAut σ (B' : GL (Fin 3) K)) := by group
    have hl2 : ((((B' : GL (Fin 3) K)⁻¹ * glAut σ (B' : GL (Fin 3) K) : GL (Fin 3) K)) :
        Matrix (Fin 3) (Fin 3) K) = lam • 1 := hlam
    rw [← coe_glAut, e, Units.val_mul, hl2, Matrix.mul_smul, Matrix.mul_one]
  have hBn : ¬ ∃ c0 : K, ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c0 • 1 := by
    rintro ⟨c0, hc0⟩
    apply hy1
    rw [hyc, suConj_eq_one_of_scalar_u38 h hc0]
    group
  have hB3 : ∃ c3 : K, ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c3 • 1 := by
    have h1 : suConj h (B' ^ 3) = 1 := by
      rw [map_pow, hY']
      have h3 := hD3 y hyD
      have h4 := conj_pow (a := c⁻¹) (b := y) (i := 3)
      rw [inv_inv] at h4
      rw [h4, h3]
      group
    obtain ⟨c3, hc3⟩ := scalar_of_suConj_eq_one h h1
    refine ⟨c3, ?_⟩
    have e : ((B' ^ 3 : unitaryIsom3 h) : GL (Fin 3) K) = (B' : GL (Fin 3) K) * B' * B' := by
      rw [pow_succ, pow_succ, pow_one]
      rfl
    rw [← hc3, e, Units.val_mul, Units.val_mul]
  set Q := Subgroup.closure (CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen.fixSet D) with hQ
  let Q' : Subgroup (unitarySU 2 3 K 3) := Q.comap c.toMonoidHom
  have hR : ∀ g : unitarySU 2 3 K 3, (∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) → g ∈ Q' := by
    intro g hg
    show c g ∈ Q
    refine Subgroup.subset_closure ⟨φ, hφD, hφ1, ?_⟩
    rw [hφH, hcdef]
    exact conj_suField_fix H σ g hg
  have hC : ∀ g : unitarySU 2 3 K 3, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ((B' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) → g ∈ Q' := by
    intro g hg
    show c g ∈ Q
    refine Subgroup.subset_closure ⟨y, hyD, hy1, ?_⟩
    have hgB : (g : GL (Fin 3) K) * (B' : GL (Fin 3) K) = (B' : GL (Fin 3) K) * g := Units.ext hg
    have h1 : suConj h B' g = g := by
      apply Subtype.ext
      rw [coe_suConj, Subgroup.coe_inv]
      calc (B' : GL (Fin 3) K) * g * (B' : GL (Fin 3) K)⁻¹
          = (g : GL (Fin 3) K) * B' * (B' : GL (Fin 3) K)⁻¹ := by rw [hgB]
        _ = g := mul_inv_cancel_right _ _
    rw [hyc, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply]
    have h2 : c.symm (c g) = g := c.symm_apply_apply g
    rw [h2, h1]
  have hQ' : Q' = ⊤ := U38F.eq_top_of_fixed_cent h hσ Q' hR B'.2 ⟨lam, hσB⟩ hBn hB3 hC
  rw [eq_top_iff]
  intro z _
  have hz : c⁻¹ z ∈ Q' := hQ' ▸ Subgroup.mem_top _
  have hz' : c (c⁻¹ z) ∈ Q := hz
  rwa [MulAut.apply_inv_self] at hz'

theorem planeGen_unitaryPSU_eight_of_not_le
    (h : UnitaryFieldData 2 3 K) {E : Subgroup (MulAut (unitaryPSU h 3))}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hc : Nat.card E = 9)
    (hnot : ¬ E ≤ (psuConj h).range) : PlaneGen E := by
  have := h.finite
  have hQ : 2 ^ 3 % 3 = 2 := by norm_num
  have hq : 2 < 2 ^ 3 := by norm_num
  have h3 := three_ne_zero_of_unitaryFieldData h hQ
  obtain ⟨φ, hφE, hφN⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨y, hyE, hyN, hy1⟩ := exists_ne_one_inf_psuConj_range h3 hq hE hc hnot
  obtain ⟨σ, -, H, hφH⟩ := unitary_order_three_field_descent hq φ (hE.2 φ hφE) hφN
  obtain ⟨B, hB⟩ := hyN
  have hD3 : ∀ d ∈ E.comap (descPSUHom h hq), d ^ 3 = 1 := by
    intro d hd
    apply descPSUHom_injective h hq
    rw [map_pow, map_one]
    exact hE.2 _ (Subgroup.mem_comap.1 hd)
  have hDc : ∀ a ∈ E.comap (descPSUHom h hq), ∀ b ∈ E.comap (descPSUHom h hq), a * b = b * a := by
    intro a ha b hb
    apply descPSUHom_injective h hq
    rw [map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, Subgroup.mem_comap.1 ha⟩
      ⟨_, Subgroup.mem_comap.1 hb⟩)
  have hφt_desc : descPSUHom h hq (suConj h H * suField h σ * (suConj h H)⁻¹) = φ := by
    rw [map_mul, map_mul, map_inv, descPSUHom_suConj, descPSUHom_suField]
    exact hφH.symm
  have hyt_desc : descPSUHom h hq (suConj h B) = y := by
    rw [descPSUHom_suConj]
    exact hB
  have hφtD : suConj h H * suField h σ * (suConj h H)⁻¹ ∈ E.comap (descPSUHom h hq) :=
    Subgroup.mem_comap.2 (by rw [hφt_desc]; exact hφE)
  have hytD : suConj h B ∈ E.comap (descPSUHom h hq) :=
    Subgroup.mem_comap.2 (by rw [hyt_desc]; exact hyE)
  have hφtN : suConj h H * suField h σ * (suConj h H)⁻¹ ∉ (suConj h).range := by
    rintro ⟨C, hC⟩
    apply hφN
    refine ⟨C, ?_⟩
    rw [← hφt_desc, ← hC, descPSUHom_suConj]
  have hyt1 : suConj h B ≠ 1 := by
    intro h1
    apply hy1
    rw [← hyt_desc, h1, map_one]
  have hytN : suConj h B ∈ (suConj h).range := ⟨B, rfl⟩
  have hfix := closure_fixSet_eq_top_of_field_gen_eight h (E.comap (descPSUHom h hq)) hD3 hDc
    hφtD hφtN hytD hyt1 hytN
  exact planeGen_of_closure_fixSet h hq (E.comap (descPSUHom h hq)) le_rfl hfix

theorem planeGen_unitaryPSU_eight (h : UnitaryFieldData 2 3 K)
    {E : Subgroup (MulAut (unitaryPSU h 3))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hc : Nat.card E = 9) (hN : ¬ NarrowScope 3 E) : PlaneGen E := by
  have := h.finite
  have hQ : 2 ^ 3 % 3 = 2 := by norm_num
  have hq : 2 < 2 ^ 3 := by norm_num
  have h3 := three_ne_zero_of_unitaryFieldData h hQ
  exact planeGen_unitaryPSU_eight_of_not_le h hE hc
    (not_le_psuConj_range_of_not_narrow h3 hq hE hN)

end CFSG.RankThree.PartTwo.Sec19
