module

public import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofCommRel
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofChoose
import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofCommL3Mat
import CFSG.RankThree.PartTwo.Sec11.Item1117Res3ProofModel
public import CFSG.RankThree.PartTwo.Sec11.Item1119StepsProof
public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofTriv

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1117Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage projSL projSU)
open KS11LieProof
open Matrix


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem l3_relations (h117 : Item117) (hbig : Sec11Big G A c L a R Y d x s r g)
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) :
    x ^ 3 * (g⁻¹ * x ^ 3 * g) = (g⁻¹ * x ^ 3 * g) * x ^ 3 ∧
    x ^ 3 * (g⁻¹ * x ^ 3 * g) * (g⁻¹ * (g⁻¹ * x ^ 3 * g) * g) = 1 ∧
    ∀ z ∈ sec11P R g ⊓ Y, z * x ^ 3 = x ^ 3 * z → z * g = g * z →
      z ∈ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := hbig.toSec11Data
  have hAe := h.mem_partTwoF.1
  have hcA : c ∈ A := h.mem_A
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hdA : d ∈ A := by rw [h.closure_eq]; exact Subgroup.subset_closure (by simp)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hcd : c * d = d * c := congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨d, hdA⟩)
  have hca : c * a = a * c := congrArg Subtype.val (hAe.1.is_comm.comm ⟨c, hcA⟩ ⟨a, h.a_mem⟩)
  obtain ⟨-, -, hd1⟩ := h.toSec11Std.not_mem_facts h.inf_eq h.closure_eq
  have hdK := h.toSec11Std.d_mem_sec11K h.inf_eq
  have hK1 : sec11K L a ≠ ⊥ := fun hb => hd1 (by rw [hb, Subgroup.mem_bot] at hdK; exact hdK)
  have hLc := Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcL : c ∈ Subgroup.normalizer (L : Set G) := Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hy))
  have hcN : c ∈ Subgroup.normalizer (Y : Set G) := h.toSec11Std.mem_normalizer_Y hK1 hcL hca
  have hK := mem_thetaComponentsIn_sec11K_inf h.toSec11Std
  have hT := kType119 G A c L a R Y h.toSec11Std d h.inf_eq h.closure_eq
  have hdY : d ∈ Y := h.sec11K_le hdK
  have hx3K := Item1117Proof.x_cube_mem_sec11K h
  have hx3Y : x ^ 3 ∈ Y := h.sec11K_le hx3K
  have hgY : g ∈ Y := h.g_mem.1
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hY hcN hc3 hK
  obtain ⟨h₀, hh₀, e, he3, he1, hαc, hKblock⟩ := core_block hcN hc3 hK hT hKf hq hq2 φ
  obtain ⟨B, hBpi, hBdet, hBe⟩ := hKblock ⟨d, hdY⟩ hdK
  obtain ⟨Bx, -, hBxdet, hBxe⟩ := hKblock ⟨x ^ 3, hx3Y⟩ hx3K
  have h3 : (3 : Kf) ≠ 0 := hKf.three_ne_zero hq
  have hπ' : π = false → UnitaryFieldData p f Kf := fun h' => by subst h'; exact hKf.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h' => by subst h'; exact hq
  have hdY' : (⟨d, hdY⟩ : Y) ^ 3 = 1 := Subtype.ext (by simpa using hd3)
  have hB3 : B ^ 3 = 1 := by
    have h1 : φ ((⟨d, hdY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) ^ 3 = 1 := by
      rw [← map_pow, ← QuotientGroup.mk_pow, hdY', QuotientGroup.mk_one, map_one]
    have h2 : (ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹)) ^ 3 = 1 := by
      have := congrArg (fun x : projImage (slPi π 3 (p ^ f) Kf) =>
        (x : ProjGenLinGroup (Fin 3) Kf)) h1
      simpa only [SubgroupClass.coe_pow, hBe, Subgroup.coe_one] using this
    rw [← map_pow, conj_pow_gl, ← map_pow] at h2
    exact eq_one_of_blockHom_mem_statedScalars (det_pow_eq_one hBdet _)
      (conj_mem_statedScalars_iff.mp (mk_eq_one_iff_mem_statedScalars.mp h2))
  have hB1 : B ≠ 1 := by
    rintro rfl
    apply hd1
    have h1 : φ ((⟨d, hdY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_one, hBe, map_one, mul_one, mul_inv_cancel, map_one]
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := 1) (by rw [pow_one]; exact hdY')
    have := congrArg Subtype.val h2
    simpa using this
  set Ψ : Y →* ProjGenLinGroup (Fin 3) Kf :=
    (projImage (slPi π 3 (p ^ f) Kf)).subtype.comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 Y))) with hΨdef
  have hΨ : ∀ w : Y, Ψ w = ((φ (w : Y ⧸ aschbacherSolvableCore 3 Y) :
      projImage (slPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf) := fun w => rfl
  have hΨ1 : ∀ w : Y, (w : G) ∈ sec11P R g → Ψ w = 1 → w = 1 := by
    intro w hwP hw
    have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 Y) w = 1 := by
      have h2 : φ (w : Y ⧸ aschbacherSolvableCore 3 Y) = 1 := Subtype.ext hw
      exact (MulEquiv.map_eq_one_iff φ).mp h2
    exact Subtype.ext (eq_one_of_mk_eq_one h hwP w.2 h1)
  set D₀ := h₀ * blockHom B * h₀⁻¹ with hD₀
  set X₀ := h₀ * blockHom Bx * h₀⁻¹ with hX₀
  have hΨD : Ψ ⟨d, hdY⟩ = ProjGenLinGroup.mk D₀ := hBe
  have hΨX : Ψ ⟨x ^ 3, hx3Y⟩ = ProjGenLinGroup.mk X₀ := hBxe
  clear_value D₀ X₀
  obtain ⟨⟨sg, hsg⟩, hsgφ⟩ :=
    projOf_surjective _ (φ ((⟨g, hgY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y))
  have hΨG : Ψ ⟨g, hgY⟩ = ProjGenLinGroup.mk sg := by rw [hΨ, ← hsgφ]; rfl
  obtain ⟨k, hk⟩ := h.pow_eq_one
  have hgd : g * d = d * g := Sec12.commute_of_conj_mem_zpowers (Item1117Proof.orderOf_d h)
    ((Subgroup.mem_normalizer_iff.mp (Item1115Proof.W_le_normalizer_d h117 h h.g_mem.2) d).mp
      (Subgroup.mem_zpowers d)) hk
  have hcommGD : ProjGenLinGroup.mk sg * ProjGenLinGroup.mk D₀ =
      ProjGenLinGroup.mk D₀ * ProjGenLinGroup.mk sg := by
    rw [← hΨG, ← hΨD, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgd
  have hsD : sg * D₀ * sg⁻¹ * D₀⁻¹ ∈ StatedScalars (Fin 3) Kf := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hcommGD,
      mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨ζ, hζ⟩ := hsD
  have hSD : sg * D₀ * sg⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * D₀ := by
    rw [hζ]
    group
  have hζ1 : ζ ≠ 1 := by
    intro hζ1
    set M := h₀⁻¹ * sg * h₀ with hM
    have hsM : sg = h₀ * M * h₀⁻¹ := by rw [hM]; group
    have hMB : M * blockHom B = blockHom B * M := by
      have h1 : sg * D₀ * sg⁻¹ = D₀ := by rw [hSD, hζ1, map_one, one_mul]
      have h2 : M * blockHom B * M⁻¹ = blockHom B := by
        calc M * blockHom B * M⁻¹ = h₀⁻¹ * (sg * D₀ * sg⁻¹) * h₀ := by rw [hM, hD₀]; group
          _ = blockHom B := by rw [h1, hD₀]; group
      calc M * blockHom B = (M * blockHom B * M⁻¹) * M := by group
        _ = blockHom B * M := by rw [h2]
    have hMe := commute_diagE_of_commute_blockHom hBdet h3 hB3 hB1 hMB e
    have hsy : sg * (h₀ * diagE e * h₀⁻¹) = (h₀ * diagE e * h₀⁻¹) * sg := by
      rw [hsM]
      calc h₀ * M * h₀⁻¹ * (h₀ * diagE e * h₀⁻¹) = h₀ * (M * diagE e) * h₀⁻¹ := by group
        _ = h₀ * (diagE e * M) * h₀⁻¹ := by rw [hMe]
        _ = h₀ * diagE e * h₀⁻¹ * (h₀ * M * h₀⁻¹) := by group
    have hgN' : g ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hgY
    set τg := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨g, hgN'⟩) with hτg
    set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
    have hsuff : MulAut.congr φ τg * MulAut.congr φ τc = MulAut.congr φ τc * MulAut.congr φ τg →
        g * c * g⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
      intro h1
      refine commutator_mem_thetaQuotCentralizer_of_commute hgN' hcN ?_
      apply (MulAut.congr φ).injective
      simpa only [MonoidHom.comp_apply, map_mul] using h1
    have hτg' : τg = MulAut.conj ((⟨g, hgY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :=
      thetaQuotMulAut_of_mem hgY hgN'
    have hαc' : ∀ m, (MulAut.congr φ τc m : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
          (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹ := hαc
    have hgs : (φ ((⟨g, hgY⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :
        ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk sg := hΨG
    have hC : g * c * g⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
      apply hsuff
      rw [hτg', mulAut_congr_conj]
      ext m
      simp only [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hαc',
        hgs]
      have hmk : ProjGenLinGroup.mk sg * ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) =
          ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * ProjGenLinGroup.mk sg := by
        rw [← map_mul, hsy, map_mul]
      calc ProjGenLinGroup.mk sg * (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * (m :
            ProjGenLinGroup (Fin 3) Kf) * (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹) *
            (ProjGenLinGroup.mk sg)⁻¹ =
          (ProjGenLinGroup.mk sg * ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹)) * (m :
            ProjGenLinGroup (Fin 3) Kf) *
              (ProjGenLinGroup.mk sg * ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹ := by
            group
        _ = (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * ProjGenLinGroup.mk sg) * (m :
            ProjGenLinGroup (Fin 3) Kf) *
              (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * ProjGenLinGroup.mk sg)⁻¹ := by
            rw [hmk]
        _ = _ := by group
    have hcl : g * c * g⁻¹ * c⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.mul_mem _ h.conj_mem (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    have h1 := eq_one_of_mem_closure_of_mem_centralizer hcN hdY hc3 hd3 hcd hKf hq hq2 φ he3 he1
      hαc hBdet hB3 hB1 (hBe.trans (by rw [hD₀])) hcl hC
    apply h.g_not_mem
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    have : g * c * g⁻¹ = c := by
      calc g * c * g⁻¹ = g * c * g⁻¹ * c⁻¹ * c := by group
        _ = c := by rw [h1, one_mul]
    rw [this]
    exact Subgroup.mem_zpowers c
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Item1117Proof.d_mem_zpowers_x_cube h)
  have hDX : ProjGenLinGroup.mk D₀ = ProjGenLinGroup.mk X₀ ^ n := by
    rw [← hΨD, ← hΨX, ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hn.symm)
  have hDXν : ∃ ν : Kfˣ, D₀ = GeneralLinearGroup.scalar (Fin 3) ν * X₀ ^ n := by
    have h1 : D₀ * (X₀ ^ n)⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv, map_zpow, hDX, mul_inv_cancel]
    obtain ⟨ν, hν⟩ := h1
    exact ⟨ν, by rw [hν]; group⟩
  have hcommD : ∀ U : GL (Fin 3) Kf, U * X₀ = X₀ * U → U * D₀ = D₀ * U := by
    intro U hU
    obtain ⟨ν, hν⟩ := hDXν
    rw [hν, ← mul_assoc, (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ν U).eq, mul_assoc,
      (Commute.zpow_right hU n).eq, ← mul_assoc]
  have hXD : X₀ * D₀ = D₀ * X₀ := hcommD X₀ rfl
  have hBtr : (B : Matrix (Fin 2) (Fin 2) Kf).trace = -1 := by
    have h1 := one_add_add_mul_self_eq_zero hBdet h3 hB3 hB1
    have h2 := mul_self_eq_trace_smul_sub (B : Matrix (Fin 2) (Fin 2) Kf)
    rw [matDet_eq_one hBdet, one_smul] at h2
    rw [h2] at h1
    have h4 : (1 + (B : Matrix (Fin 2) (Fin 2) Kf).trace) • (B : Matrix (Fin 2) (Fin 2) Kf) =
        0 := by
      rw [add_smul, one_smul, ← h1]
      abel
    have hB0 : (B : Matrix (Fin 2) (Fin 2) Kf) ≠ 0 := by
      intro h0
      have := matDet_eq_one hBdet
      rw [h0] at this
      simp at this
    rcases smul_eq_zero.mp h4 with h5 | h5
    · linear_combination h5
    · exact absurd h5 hB0
  have htrD : (D₀ : Matrix (Fin 3) (Fin 3) Kf).trace = 0 := by
    rw [hD₀, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mul, coe_blockHom_of_det hBdet, trace_blockMat,
      hBtr]
    ring
  have hτ : ((e : Kf)) ^ 3 = 1 := he3
  have hτ1 : (e : Kf) ≠ 1 := fun h1 => he1 (Units.ext h1)
  have hD₀H : D₀ ∈ glPi π 3 (p ^ f) Kf := by
    rw [hD₀]
    exact mul_mem (mul_mem hh₀ (slPi_le_glPi hπ' (blockHom_mem_slPi hKf hBpi))) (inv_mem hh₀)
  have hD₀s : D₀ ∉ StatedScalars (Fin 3) Kf := by
    rw [hD₀, conj_mem_statedScalars_iff]
    intro h1
    exact hB1 (eq_one_of_blockHom_mem_statedScalars hBdet h1)
  have hD₀3 : D₀ ^ 3 = GeneralLinearGroup.scalar (Fin 3) ((1 : Kfˣ) ^ 3) := by
    rw [one_pow, map_one, hD₀, conj_pow_gl, ← map_pow, hB3, map_one, mul_one, mul_inv_cancel]
  obtain ⟨y₀, ⟨z, hzZ, rfl⟩, Q, -, hcase⟩ :=
    exists_diag_normal_form hKf hq hτ hτ1 hD₀H hD₀s hD₀3
  have hzS : z ∈ StatedScalars (Fin 3) Kf :=
    (Subgroup.mem_inf.mp ((zPi_eq hπ' hq' hτ hτ1) ▸ hzZ)).2
  obtain ⟨z₀, hz₀⟩ := hzS
  have hzc : ∀ A : GL (Fin 3) Kf, A * z = z * A := fun A => by
    rw [← hz₀]
    exact (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar z₀ A).eq
  have hcase' : Q⁻¹ * (D₀ * z) * Q = diagTau hτ := by
    rcases hcase with h1 | ⟨e', he', h1⟩
    · exact h1
    · exfalso
      have htr := congrArg (fun A : GL (Fin 3) Kf => (A : Matrix (Fin 3) (Fin 3) Kf).trace) h1
      simp only [Units.val_mul] at htr
      rw [trace_inv_mul_mul, ← hz₀, GeneralLinearGroup.coe_scalar, mul_scalar_eq_smul,
        Matrix.trace_smul, htrD, smul_zero, coe_diagE, Matrix.trace_diagonal,
        Fin.sum_univ_three] at htr
      simp only [Fin.isValue, cons_val_zero, cons_val_one, cons_val_two, head_cons,
        tail_cons] at htr
      have he'3 : (e' : Kf) ^ 3 = 1 := by
        rcases he' with h2 | h2
        · rw [h2, hτ]
        · rw [h2, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hτ, one_pow]
      have he'2 : (e' : Kf) = -2 := by linear_combination -htr
      rw [he'2] at he'3
      apply h3
      have h9 : (3 : Kf) * 3 = 0 := by linear_combination -he'3
      rcases mul_eq_zero.mp h9 with h | h <;> exact h
  set Dg : Matrix (Fin 3) (Fin 3) Kf := diagonal ![(e : Kf), (e : Kf) ^ 2, 1] with hDg
  have hz0 : ((z₀⁻¹ : Kfˣ) : Kf) ≠ 0 := Units.ne_zero _
  have hQD : ((Q⁻¹ * D₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      ((z₀⁻¹ : Kfˣ) : Kf) • Dg := by
    have h1 : Q⁻¹ * D₀ * Q = diagTau hτ * z⁻¹ := by
      rw [← hcase']
      calc Q⁻¹ * D₀ * Q = Q⁻¹ * D₀ * (Q * z) * z⁻¹ := by group
        _ = Q⁻¹ * D₀ * (z * Q) * z⁻¹ := by rw [hzc Q]
        _ = Q⁻¹ * (D₀ * z) * Q * z⁻¹ := by group
    rw [h1, Units.val_mul, coe_diagTau_eq_diagonal, ← hz₀, ← map_inv,
      GeneralLinearGroup.coe_scalar, mul_scalar_eq_smul]
  have hdiagQ : ∀ U : GL (Fin 3) Kf, U * D₀ = D₀ * U →
      ((Q⁻¹ * U * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        diagonal (fun i => ((Q⁻¹ * U * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) i i) := by
    intro U hU
    apply eq_diagonal_of_commute (injective_cycleTau hτ hτ1)
    apply commute_of_commute_smul hz0
    rw [← hQD, ← Units.val_mul, ← Units.val_mul]
    congr 1
    calc Q⁻¹ * U * Q * (Q⁻¹ * D₀ * Q) = Q⁻¹ * (U * D₀) * Q := by group
      _ = Q⁻¹ * (D₀ * U) * Q := by rw [hU]
      _ = Q⁻¹ * D₀ * Q * (Q⁻¹ * U * Q) := by group
  set M := Q⁻¹ * sg * Q with hM
  have hζ3 : (ζ : Kf) ^ 3 = 1 := by
    have h1 := congrArg GeneralLinearGroup.det hSD
    generalize hδ : GeneralLinearGroup.det D₀ = δ at h1
    rw [map_mul, map_mul, map_inv, hδ, map_mul, hδ, GeneralLinearGroup.det_scalar,
      Fintype.card_fin, mul_comm (GeneralLinearGroup.det sg), mul_assoc, mul_inv_cancel,
      mul_one] at h1
    have h2 : ζ ^ 3 = 1 := by
      have := congrArg (· * δ⁻¹) h1
      simpa using this.symm
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  have hζ1' : (ζ : Kf) ≠ 1 := fun h1 => hζ1 (Units.ext h1)
  have hMD : (M : Matrix (Fin 3) (Fin 3) Kf) * Dg = (ζ : Kf) • (Dg * M) := by
    apply mul_eq_smul_of_smul hz0
    rw [← hQD]
    have h1 : M * (Q⁻¹ * D₀ * Q) =
        GeneralLinearGroup.scalar (Fin 3) ζ * (Q⁻¹ * D₀ * Q) * M := by
      have h2 : sg * D₀ = GeneralLinearGroup.scalar (Fin 3) ζ * D₀ * sg := by
        calc sg * D₀ = sg * D₀ * sg⁻¹ * sg := by group
          _ = _ := by rw [hSD]
      have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ Q⁻¹).eq
      calc M * (Q⁻¹ * D₀ * Q) = Q⁻¹ * (sg * D₀) * Q := by rw [hM]; group
        _ = Q⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * D₀ * sg) * Q := by rw [h2]
        _ = (Q⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ) * D₀ * sg * Q := by group
        _ = _ := by rw [hc, hM]; group
    generalize hDq : Q⁻¹ * D₀ * Q = Dq at h1 ⊢
    rw [← Units.val_mul, h1, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
      scalar_mul_eq_smul, Matrix.smul_mul]
  have hMunit : ((M⁻¹ : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) *
      (M : Matrix (Fin 3) (Fin 3) Kf) = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMdet : (M : Matrix (Fin 3) (Fin 3) Kf).det ≠ 0 :=
    (M.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) Kf →* Kf)).ne_zero
  set ξ := fun i => ((Q⁻¹ * X₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) i i with hξ
  have hXq : ((Q⁻¹ * X₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) = diagonal ξ :=
    hdiagQ X₀ hXD
  have hconjQ : ∀ U : GL (Fin 3) Kf, Q⁻¹ * (sg⁻¹ * U * sg) * Q = M⁻¹ * (Q⁻¹ * U * Q) * M := by
    intro U
    rw [hM]
    group
  obtain ⟨perm, hperm, hprod, hgeom⟩ : ∃ perm : (Fin 3 → Kf) → (Fin 3 → Kf),
      (∀ v, ((M⁻¹ : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) * diagonal v *
          (M : Matrix (Fin 3) (Fin 3) Kf) = diagonal (perm v)) ∧
      (∀ v, diagonal v * diagonal (perm v) * diagonal (perm (perm v)) =
        (v 0 * v 1 * v 2) • (1 : Matrix (Fin 3) (Fin 3) Kf)) ∧
      (∀ (w : Fin 3 → Kf) (μ : Kf), (M : Matrix (Fin 3) (Fin 3) Kf) * diagonal w =
          μ • (diagonal w * M) → w 0 ≠ 0 →
        ∃ ν : Kf, ν ^ 3 = 1 ∧ diagonal w = w 0 • diagonal ![1, ν, ν ^ 2]) := by
    rcases eq_one_or_of_cube hτ hτ1 hζ3 with h1 | h1 | h1
    · exact absurd h1 hζ1'
    · rw [h1] at hMD
      have hpat := eq_cycE_of_mul_eq hτ hτ1 hMD
      have hdet := hMdet
      rw [hpat, det_cycE] at hdet
      have hm₀ : (M : Matrix (Fin 3) (Fin 3) Kf) 0 1 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      have hm₁ : (M : Matrix (Fin 3) (Fin 3) Kf) 1 2 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      have hm₂ : (M : Matrix (Fin 3) (Fin 3) Kf) 2 0 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      refine ⟨fun v => ![v 2, v 0, v 1], fun v => cycE_conj_diagonal hMunit hpat v,
        fun v => ?_, fun w μ hw hw0 => ?_⟩
      · have := diagonal_mul_cyc_mul_cyc v
        simpa using this
      · rw [hpat, eq_vec_three w] at hw
        obtain ⟨e1, e2, e3⟩ := eq_of_cycE_mul_diagonal hm₀ hm₁ hm₂ hw
        refine ⟨μ, ?_, ?_⟩
        · have : w 0 * (μ ^ 3 - 1) = 0 := by linear_combination -e3 - μ * e2 - μ ^ 2 * e1
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hw0)
        · rw [eq_vec_three w, ← diagonal_smul]
          congr 1
          funext i
          fin_cases i <;> simp [e1, e2] <;> ring
    · rw [h1] at hMD
      have hpat := eq_cycE2_of_mul_eq hτ hτ1 hMD
      have hdet := hMdet
      rw [hpat, det_cycE2] at hdet
      have hm₀ : (M : Matrix (Fin 3) (Fin 3) Kf) 0 2 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      have hm₁ : (M : Matrix (Fin 3) (Fin 3) Kf) 1 0 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      have hm₂ : (M : Matrix (Fin 3) (Fin 3) Kf) 2 1 ≠ 0 := fun h0 => hdet (by rw [h0]; ring)
      refine ⟨fun v => ![v 1, v 2, v 0], fun v => cycE2_conj_diagonal hMunit hpat v,
        fun v => ?_, fun w μ hw hw0 => ?_⟩
      · have := diagonal_mul_cyc2_mul_cyc2 v
        simpa using this
      · rw [hpat, eq_vec_three w] at hw
        obtain ⟨e1, e2, e3⟩ := eq_of_cycE2_mul_diagonal hm₀ hm₁ hm₂ hw
        have hμ3 : μ ^ 3 = 1 := by
          have : w 0 * (μ ^ 3 - 1) = 0 := by linear_combination -e2 - μ * e3 - μ ^ 2 * e1
          exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hw0)
        refine ⟨μ ^ 2, by rw [← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hμ3, one_pow], ?_⟩
        rw [eq_vec_three w, ← diagonal_smul]
        congr 1
        funext i
        fin_cases i <;> simp [e1, e3]
        · ring
        · linear_combination (-(w 0) * μ) * hμ3
  have hconjX : ((Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
      diagonal (perm ξ) := by
    rw [hconjQ, Units.val_mul, Units.val_mul, hXq, hperm]
  have hconjX2 : ((Q⁻¹ * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg) * Q : GL (Fin 3) Kf) :
      Matrix (Fin 3) (Fin 3) Kf) = diagonal (perm (perm ξ)) := by
    rw [hconjQ, Units.val_mul, Units.val_mul, hconjX, hperm]
  have hR1gl : X₀ * (sg⁻¹ * X₀ * sg) = (sg⁻¹ * X₀ * sg) * X₀ := by
    have key : (Q⁻¹ * X₀ * Q) * (Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q) =
        (Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q) * (Q⁻¹ * X₀ * Q) := by
      generalize Q⁻¹ * X₀ * Q = A at hXq ⊢
      generalize Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q = A' at hconjX ⊢
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hXq, hconjX, diagonal_mul_diagonal,
        diagonal_mul_diagonal]
      congr 1
      funext i
      ring
    calc X₀ * (sg⁻¹ * X₀ * sg) =
        Q * ((Q⁻¹ * X₀ * Q) * (Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q)) * Q⁻¹ := by group
      _ = Q * ((Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q) * (Q⁻¹ * X₀ * Q)) * Q⁻¹ := by rw [key]
      _ = (sg⁻¹ * X₀ * sg) * X₀ := by group
  have hξ0 : ξ 0 * ξ 1 * ξ 2 ≠ 0 := by
    have hdet := ((Q⁻¹ * X₀ * Q).isUnit.map
      (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) Kf →* Kf)).ne_zero
    change ((Q⁻¹ * X₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf).det ≠ 0 at hdet
    rw [hXq, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
    exact hdet
  have hR2gl : X₀ * (sg⁻¹ * X₀ * sg) * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg) ∈
      StatedScalars (Fin 3) Kf := by
    have key : ((Q⁻¹ * (X₀ * (sg⁻¹ * X₀ * sg) * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg)) * Q :
        GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) = (ξ 0 * ξ 1 * ξ 2) • 1 := by
      have e : Q⁻¹ * (X₀ * (sg⁻¹ * X₀ * sg) * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg)) * Q =
          (Q⁻¹ * X₀ * Q) * (Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q) *
            (Q⁻¹ * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg) * Q) := by group
      rw [e]
      generalize Q⁻¹ * X₀ * Q = A at hXq ⊢
      generalize Q⁻¹ * (sg⁻¹ * X₀ * sg) * Q = A' at hconjX ⊢
      generalize Q⁻¹ * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg) * Q = A'' at hconjX2 ⊢
      rw [Units.val_mul, Units.val_mul, hXq, hconjX, hconjX2, hprod]
    have h1 := mem_statedScalars_of_eq_smul key hξ0
    rw [show ∀ U : GL (Fin 3) Kf, Q⁻¹ * U * Q = Q⁻¹ * U * Q⁻¹⁻¹ from fun U => by rw [inv_inv],
      conj_mem_statedScalars_iff] at h1
    exact h1
  set X3 : Y := ⟨x ^ 3, hx3Y⟩ with hX3
  set Gg : Y := ⟨g, hgY⟩ with hGg
  set Dd : Y := ⟨d, hdY⟩ with hDd
  have hxP : x ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1116Proof.mem_R h).2.1
  have hgP : g ∈ sec11P R g := Item1119Proof.g_mem_P R g
  have hX3P : (X3 : G) ∈ sec11P R g := (sec11P R g).pow_mem hxP 3
  have hdP : d ∈ sec11P R g := Item1119Proof.R_le_P R g (Item1115Proof.A_le_R h.toHyp91 hdA)
  have htrX : (X₀ : Matrix (Fin 3) (Fin 3) Kf).trace ≠ 0 := by
    intro h0
    have htrB : (Bx : Matrix (Fin 2) (Fin 2) Kf).trace = -1 := by
      rw [hX₀, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul, coe_blockHom_of_det hBxdet,
        trace_blockMat] at h0
      linear_combination h0
    have hBx3 : Bx ^ 3 = 1 := by
      have h2 := mul_self_eq_trace_smul_sub (Bx : Matrix (Fin 2) (Fin 2) Kf)
      rw [matDet_eq_one hBxdet, one_smul, htrB, neg_one_smul] at h2
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one, pow_succ, sq, h2, sub_mul, neg_mul, h2,
        one_mul]
      abel
    have hX03 : X₀ ^ 3 = 1 := by
      rw [hX₀, conj_pow_gl, ← map_pow, hBx3, map_one, mul_one, mul_inv_cancel]
    have h1 : Ψ (X3 ^ 3) = 1 := by rw [map_pow, hΨX, ← map_pow, hX03, map_one]
    have h2 := hΨ1 (X3 ^ 3) ((sec11P R g).pow_mem hX3P 3) h1
    have h3' : x ^ 9 = 1 := by
      have := congrArg Subtype.val h2
      simp only [hX3, SubgroupClass.coe_pow, Subgroup.coe_one] at this
      rw [← pow_mul] at this
      exact this
    have := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h3')
    have := hbig.orderOf_x_gt
    omega
  have hR3gl : ∀ W₀ : GL (Fin 3) Kf,
      ProjGenLinGroup.mk W₀ * ProjGenLinGroup.mk X₀ =
        ProjGenLinGroup.mk X₀ * ProjGenLinGroup.mk W₀ →
      ProjGenLinGroup.mk W₀ * ProjGenLinGroup.mk sg =
        ProjGenLinGroup.mk sg * ProjGenLinGroup.mk W₀ →
      ∃ k : ℕ, ProjGenLinGroup.mk W₀ = ProjGenLinGroup.mk D₀ ^ k := by
    intro W₀ hWX hWS
    have h1 : W₀ * X₀ * W₀⁻¹ * X₀⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hWX,
        mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨l, hl⟩ := h1
    have h2 : W₀ * X₀ * W₀⁻¹ = GeneralLinearGroup.scalar (Fin 3) l * X₀ := by rw [hl]; group
    have hl1 : (l : Kf) = 1 := by
      have htr := congrArg (fun U : GL (Fin 3) Kf => (U : Matrix (Fin 3) (Fin 3) Kf).trace) h2
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at htr
      rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul, scalar_mul_eq_smul, Matrix.trace_smul, smul_eq_mul] at htr
      have : (1 - (l : Kf)) * (X₀ : Matrix (Fin 3) (Fin 3) Kf).trace = 0 := by
        linear_combination htr
      rcases mul_eq_zero.mp this with h | h
      · linear_combination -h
      · exact absurd h htrX
    have hWX' : W₀ * X₀ = X₀ * W₀ := by
      have hl' : l = 1 := Units.ext hl1
      rw [hl', map_one, one_mul] at h2
      calc W₀ * X₀ = W₀ * X₀ * W₀⁻¹ * W₀ := by group
        _ = X₀ * W₀ := by rw [h2]
    have hWD := hcommD W₀ hWX'
    set ω := fun i => ((Q⁻¹ * W₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) i i with hω
    have hWq : ((Q⁻¹ * W₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) = diagonal ω :=
      hdiagQ W₀ hWD
    have h3 : sg * W₀ * sg⁻¹ * W₀⁻¹ ∈ StatedScalars (Fin 3) Kf := by
      rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, ← hWS,
        mul_inv_cancel_right, mul_inv_cancel]
    obtain ⟨μ, hμ⟩ := h3
    have h4 : M * (Q⁻¹ * W₀ * Q) =
        GeneralLinearGroup.scalar (Fin 3) μ * (Q⁻¹ * W₀ * Q) * M := by
      have h5 : sg * W₀ = GeneralLinearGroup.scalar (Fin 3) μ * W₀ * sg := by
        rw [hμ]
        group
      have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar μ Q⁻¹).eq
      calc M * (Q⁻¹ * W₀ * Q) = Q⁻¹ * (sg * W₀) * Q := by rw [hM]; group
        _ = Q⁻¹ * (GeneralLinearGroup.scalar (Fin 3) μ * W₀ * sg) * Q := by rw [h5]
        _ = (Q⁻¹ * GeneralLinearGroup.scalar (Fin 3) μ) * W₀ * sg * Q := by group
        _ = _ := by rw [hc, hM]; group
    have h6 : (M : Matrix (Fin 3) (Fin 3) Kf) * diagonal ω = (μ : Kf) • (diagonal ω * M) := by
      rw [← hWq]
      generalize Q⁻¹ * W₀ * Q = Wq at h4 ⊢
      rw [← Units.val_mul, h4, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar,
        scalar_mul_eq_smul, Matrix.smul_mul]
    have hω0 : ω 0 ≠ 0 := by
      have hdet := ((Q⁻¹ * W₀ * Q).isUnit.map
        (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) Kf →* Kf)).ne_zero
      change ((Q⁻¹ * W₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf).det ≠ 0 at hdet
      rw [hWq, Matrix.det_diagonal, Fin.prod_univ_three] at hdet
      intro h0
      exact hdet (by rw [h0]; ring)
    obtain ⟨ν, hν3, hων⟩ := hgeom ω μ h6 hω0
    obtain ⟨c₁, k, hc₁, hck⟩ := exists_diagonal_geom_eq hτ hτ1 hν3
    refine ⟨k, ?_⟩
    have hDk : ((Q⁻¹ * D₀ ^ k * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        ((z₀⁻¹ : Kfˣ) : Kf) ^ k • Dg ^ k := by
      have e : Q⁻¹ * D₀ ^ k * Q = (Q⁻¹ * D₀ * Q) ^ k := by
        rw [show Q⁻¹ * D₀ * Q = Q⁻¹ * D₀ * Q⁻¹⁻¹ by rw [inv_inv], conj_pow_gl, inv_inv]
      rw [e, Units.val_pow_eq_pow_val, hQD, smul_pow]
    have hzk : ((z₀⁻¹ : Kfˣ) : Kf) ^ k ≠ 0 := pow_ne_zero k hz0
    have hW' : ((Q⁻¹ * W₀ * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        (ω 0 * c₁ * (((z₀⁻¹ : Kfˣ) : Kf) ^ k)⁻¹) •
          ((Q⁻¹ * D₀ ^ k * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) := by
      rw [hWq, hων, hck, hDk, smul_smul, smul_smul, mul_assoc (ω 0 * c₁), inv_mul_cancel₀ hzk,
        mul_one]
    have hsc : ((Q⁻¹ * (W₀ * (D₀ ^ k)⁻¹) * Q : GL (Fin 3) Kf) : Matrix (Fin 3) (Fin 3) Kf) =
        (ω 0 * c₁ * (((z₀⁻¹ : Kfˣ) : Kf) ^ k)⁻¹) • 1 := by
      have e : Q⁻¹ * (W₀ * (D₀ ^ k)⁻¹) * Q = (Q⁻¹ * W₀ * Q) * (Q⁻¹ * D₀ ^ k * Q)⁻¹ := by group
      rw [e]
      generalize Q⁻¹ * W₀ * Q = Wq at hW' ⊢
      generalize Q⁻¹ * D₀ ^ k * Q = Dk at hW' ⊢
      rw [Units.val_mul, hW', Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hne : ω 0 * c₁ * (((z₀⁻¹ : Kfˣ) : Kf) ^ k)⁻¹ ≠ 0 :=
      mul_ne_zero (mul_ne_zero hω0 hc₁) (inv_ne_zero hzk)
    have h7 := mem_statedScalars_of_eq_smul hsc hne
    rw [show ∀ U : GL (Fin 3) Kf, Q⁻¹ * U * Q = Q⁻¹ * U * Q⁻¹⁻¹ from fun U => by rw [inv_inv],
      conj_mem_statedScalars_iff, ← mk_eq_one_iff_mem_statedScalars, map_mul, map_inv,
      mul_inv_eq_one] at h7
    rw [h7, map_pow]
  refine ⟨?_, ?_, ?_⟩
  ·
    have hmk := congrArg ProjGenLinGroup.mk hR1gl
    simp only [map_mul, map_inv] at hmk
    have hw := hΨ1 (X3 * (Gg⁻¹ * X3 * Gg) * X3⁻¹ * (Gg⁻¹ * X3 * Gg)⁻¹)
      (by
        have h1 : ((Gg⁻¹ * X3 * Gg : Y) : G) ∈ sec11P R g :=
          (sec11P R g).mul_mem ((sec11P R g).mul_mem ((sec11P R g).inv_mem hgP) hX3P) hgP
        exact (sec11P R g).mul_mem ((sec11P R g).mul_mem ((sec11P R g).mul_mem hX3P h1)
          ((sec11P R g).inv_mem hX3P)) ((sec11P R g).inv_mem h1))
      (by
        simp only [map_mul, map_inv, hΨX, hΨG]
        rw [hmk]
        group)
    have := congrArg Subtype.val hw
    simp only [hX3, hGg, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc x ^ 3 * (g⁻¹ * x ^ 3 * g) =
        (x ^ 3 * (g⁻¹ * x ^ 3 * g) * (x ^ 3)⁻¹ * (g⁻¹ * x ^ 3 * g)⁻¹) *
          ((g⁻¹ * x ^ 3 * g) * x ^ 3) := by group
      _ = (g⁻¹ * x ^ 3 * g) * x ^ 3 := by rw [this, one_mul]
  ·
    have hmk : ProjGenLinGroup.mk (X₀ * (sg⁻¹ * X₀ * sg) * (sg⁻¹ * (sg⁻¹ * X₀ * sg) * sg)) = 1 :=
      mk_eq_one_iff_mem_statedScalars.mpr hR2gl
    simp only [map_mul, map_inv] at hmk
    have hw := hΨ1 (X3 * (Gg⁻¹ * X3 * Gg) * (Gg⁻¹ * (Gg⁻¹ * X3 * Gg) * Gg))
      (by
        have h1 : ((Gg⁻¹ * X3 * Gg : Y) : G) ∈ sec11P R g :=
          (sec11P R g).mul_mem ((sec11P R g).mul_mem ((sec11P R g).inv_mem hgP) hX3P) hgP
        exact (sec11P R g).mul_mem ((sec11P R g).mul_mem hX3P h1)
          ((sec11P R g).mul_mem ((sec11P R g).mul_mem ((sec11P R g).inv_mem hgP) h1) hgP))
      (by
        simp only [map_mul, map_inv, hΨX, hΨG]
        exact hmk)
    have := congrArg Subtype.val hw
    simpa [hX3, hGg] using this
  ·
    intro w hw hwx hwg
    set Wy : Y := ⟨w, hw.2⟩ with hWy
    obtain ⟨⟨W₀, hW₀⟩, hW₀φ⟩ :=
      projOf_surjective _ (φ ((Wy : Y) : Y ⧸ aschbacherSolvableCore 3 Y))
    have hΨW : Ψ Wy = ProjGenLinGroup.mk W₀ := by rw [hΨ, ← hW₀φ]; rfl
    have hWX : ProjGenLinGroup.mk W₀ * ProjGenLinGroup.mk X₀ =
        ProjGenLinGroup.mk X₀ * ProjGenLinGroup.mk W₀ := by
      rw [← hΨW, ← hΨX, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hwx
    have hWS : ProjGenLinGroup.mk W₀ * ProjGenLinGroup.mk sg =
        ProjGenLinGroup.mk sg * ProjGenLinGroup.mk W₀ := by
      rw [← hΨW, ← hΨG, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hwg
    obtain ⟨k, hk⟩ := hR3gl W₀ hWX hWS
    have h1 : Ψ (Wy * (Dd ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, hΨW, hΨD, hk, mul_inv_cancel]
    have h2 := hΨ1 (Wy * (Dd ^ k)⁻¹)
      ((sec11P R g).mul_mem hw.1 ((sec11P R g).inv_mem ((sec11P R g).pow_mem hdP k))) h1
    have h3 : w = d ^ k := by
      have := congrArg Subtype.val h2
      simp only [hWy, hDd, Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow,
        Subgroup.coe_one] at this
      exact mul_inv_eq_one.mp this
    rw [h3]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) k

end Item1117Res3Proof

section Main


theorem step1119CommL3_holds (h117 : Item117) : Step1119CommL3 := by
  intro G _ _ A c L a R Y d x s r g hbig hY
  obtain ⟨h1, h2, h3⟩ := Item1117Res3Proof.l3_relations h117 hbig hY
  exact Item1117Res3Proof.step1119Comm_concl_of_relations hbig h1 h2 h3

end Main

end CFSG.RankThree.PartTwo.Sec11
