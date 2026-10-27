module

public import CFSG.RankThree.PartTwo.Sec11.KS11LieProofChoose
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

theorem orderOf_eq_three_of_isLThreePi (h : Sec11Data G A c L a R Y d x s r g)
    (hY : Sec13.IsLThreePi (Y ⧸ aschbacherSolvableCore 3 Y)) {g' : G} (hg'Y : g' ∈ Y)
    (hg'k : ∃ k : ℕ, g' ^ 3 ^ k = 1) (hg'd : g' * d = d * g')
    (hg'cd : g' * c * g'⁻¹ ∈ Subgroup.closure ({c, d} : Set G))
    (hg'H : g' ∉ Subgroup.normalizer (Subgroup.zpowers c : Set G)) : orderOf g' = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hg'k⟩ := hg'k
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
  have hg'1 : g' ≠ 1 := fun h1 => hg'H (h1 ▸ Subgroup.one_mem _)
  obtain ⟨π, p, f, Kf, _, hKf, hq, hq2, ⟨φ⟩⟩ := exists_model hY hcN hc3 hK
  obtain ⟨h₀, -, e, he3, he1, hαc, hKblock⟩ := core_block hcN hc3 hK hT hKf hq hq2 φ
  obtain ⟨B, -, hBdet, hBe⟩ := hKblock ⟨d, hdY⟩ hdK
  have h3 : (3 : Kf) ≠ 0 := hKf.three_ne_zero hq
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
  obtain ⟨⟨sg, hsg⟩, hsgφ⟩ :=
    projOf_surjective _ (φ ((⟨g', hg'Y⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y))
  have hgs : (φ ((⟨g', hg'Y⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :
      ProjGenLinGroup (Fin 3) Kf) = ProjGenLinGroup.mk sg := by rw [← hsgφ]; rfl
  have hg'd' : (⟨g', hg'Y⟩ : Y) * ⟨d, hdY⟩ = ⟨d, hdY⟩ * ⟨g', hg'Y⟩ := Subtype.ext hg'd
  have hcomm : ProjGenLinGroup.mk sg * ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹) =
      ProjGenLinGroup.mk (h₀ * blockHom B * h₀⁻¹) * ProjGenLinGroup.mk sg := by
    rw [← hgs, ← hBe]
    have := congrArg (fun y : Y => ((φ (y : Y ⧸ aschbacherSolvableCore 3 Y) :
      projImage (slPi π 3 (p ^ f) Kf)) : ProjGenLinGroup (Fin 3) Kf)) hg'd'
    simpa only [QuotientGroup.mk_mul, map_mul, Subgroup.coe_mul] using this
  have hsD : sg * (h₀ * blockHom B * h₀⁻¹) * sg⁻¹ * (h₀ * blockHom B * h₀⁻¹)⁻¹ ∈
      StatedScalars (Fin 3) Kf := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm,
      mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨ζ, hζ⟩ := hsD
  set M := h₀⁻¹ * sg * h₀ with hM
  have hMconj : M * blockHom B * M⁻¹ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B := by
    have h1 : sg * (h₀ * blockHom B * h₀⁻¹) * sg⁻¹ =
        GeneralLinearGroup.scalar (Fin 3) ζ * (h₀ * blockHom B * h₀⁻¹) := by
      rw [hζ]
      group
    have hc := (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar ζ h₀⁻¹).eq
    calc M * blockHom B * M⁻¹ = h₀⁻¹ * (sg * (h₀ * blockHom B * h₀⁻¹) * sg⁻¹) * h₀ := by
          rw [hM]
          group
      _ = h₀⁻¹ * (GeneralLinearGroup.scalar (Fin 3) ζ * (h₀ * blockHom B * h₀⁻¹)) * h₀ := by
          rw [h1]
      _ = (h₀⁻¹ * GeneralLinearGroup.scalar (Fin 3) ζ) * h₀ * blockHom B := by group
      _ = GeneralLinearGroup.scalar (Fin 3) ζ * blockHom B := by
          rw [hc]
          group
  have hsM : sg = h₀ * M * h₀⁻¹ := by rw [hM]; group
  by_cases hζ1 : ζ = 1
  ·
    exfalso
    have hMB : M * blockHom B = blockHom B * M := by
      have h1 : M * blockHom B * M⁻¹ = blockHom B := by rw [hMconj, hζ1, map_one, one_mul]
      calc M * blockHom B = (M * blockHom B * M⁻¹) * M := by group
        _ = blockHom B * M := by rw [h1]
    have hMe := commute_diagE_of_commute_blockHom hBdet h3 hB3 hB1 hMB e
    have hsy : sg * (h₀ * diagE e * h₀⁻¹) = (h₀ * diagE e * h₀⁻¹) * sg := by
      rw [hsM]
      calc h₀ * M * h₀⁻¹ * (h₀ * diagE e * h₀⁻¹) = h₀ * (M * diagE e) * h₀⁻¹ := by group
        _ = h₀ * (diagE e * M) * h₀⁻¹ := by rw [hMe]
        _ = h₀ * diagE e * h₀⁻¹ * (h₀ * M * h₀⁻¹) := by group
    have hg'N' : g' ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hg'Y
    set τg := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨g', hg'N'⟩) with hτg
    set τc := Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨c, hcN⟩) with hτc
    have hsuff : MulAut.congr φ τg * MulAut.congr φ τc = MulAut.congr φ τc * MulAut.congr φ τg →
        g' * c * g'⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
      intro h1
      refine commutator_mem_thetaQuotCentralizer_of_commute hg'N' hcN ?_
      apply (MulAut.congr φ).injective
      simpa only [MonoidHom.comp_apply, map_mul] using h1
    have hτg' : τg = MulAut.conj ((⟨g', hg'Y⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y) :=
      thetaQuotMulAut_of_mem hg'Y hg'N'
    have hαc' : ∀ m, (MulAut.congr φ τc m : ProjGenLinGroup (Fin 3) Kf) =
        ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹) * m *
          (ProjGenLinGroup.mk (h₀ * diagE e * h₀⁻¹))⁻¹ := hαc
    have hC : g' * c * g'⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y := by
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
    have hcl : g' * c * g'⁻¹ * c⁻¹ ∈ Subgroup.closure ({c, d} : Set G) :=
      Subgroup.mul_mem _ hg'cd (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
    have h1 := eq_one_of_mem_closure_of_mem_centralizer hcN hdY hc3 hd3 hcd hKf hq hq2 φ he3 he1
      hαc hBdet hB3 hB1 hBe hcl hC
    have hg'c : g' * c * g'⁻¹ = c := by
      calc g' * c * g'⁻¹ = g' * c * g'⁻¹ * c⁻¹ * c := by group
        _ = c := by rw [h1, one_mul]
    apply hg'H
    apply Sec10.mem_normalizer_zpowers_of_conj_mem
    rw [hg'c]
    exact Subgroup.mem_zpowers c
  ·
    have hM3 := pow_three_mem_statedScalars_of_conj hBdet h3 hB3 hB1 hζ1 hMconj
    have hs3 : sg ^ 3 ∈ StatedScalars (Fin 3) Kf := by
      rw [hsM, conj_pow_gl, conj_mem_statedScalars_iff]
      exact hM3
    have hmk3 : (ProjGenLinGroup.mk sg) ^ 3 = 1 := by
      rw [← map_pow, mk_eq_one_iff_mem_statedScalars]
      exact hs3
    have hg'3 : (⟨g', hg'Y⟩ : Y) ^ 3 ∈ aschbacherSolvableCore 3 Y := by
      have h1 : φ (((⟨g', hg'Y⟩ : Y) ^ 3 : Y) : Y ⧸ aschbacherSolvableCore 3 Y) = 1 := by
        apply Subtype.ext
        rw [QuotientGroup.mk_pow, map_pow, SubgroupClass.coe_pow, hgs, hmk3, Subgroup.coe_one]
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
      exact h1
    have h2 := eq_one_of_mem_theta_of_pow_eq_one hg'3 (k := k) (by
      rw [← pow_mul, mul_comm, pow_mul]
      have : (⟨g', hg'Y⟩ : Y) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hg'k)
      rw [this, one_pow])
    have hg'3' : g' ^ 3 = 1 := by simpa using congrArg Subtype.val h2
    exact orderOf_eq_prime hg'3' hg'1

end Item1117Res3Proof

end CFSG.RankThree.PartTwo.Sec11
