module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Cfg
public import CFSG.LocalAnalysis.WeakClosure81.SevenElevenCls
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Orth63B
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79Orth63A

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Orthogonal Matrix QuadraticMap
open scoped MatrixGroups
private noncomputable abbrev nine3Q (F : Type) [Field F] (b c' : F) :
    QuadraticForm F (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) :=
  CFSG.LieType.Universal.Spin.quadMinus 3 F b c'

private noncomputable def nine3MKTL (F : Type) [Field F] :
    ((Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F)) →*
      Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F :=
  Matrix.ProjGenLinGroup.mk.comp
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm.toMonoidHom

private theorem nine3MKTL_apply (F : Type) [Field F]
    (a : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) ≃ₗ[F] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F)) :
    nine3MKTL F a = Matrix.ProjGenLinGroup.mk
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm a) := rfl

theorem nine3_isRankOneIn_rank {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (g : GL ι F) (h : IsRankOneIn g) : Matrix.rank ((g : Matrix ι ι F) - 1) = 1 :=
  h

private theorem nine3_orth63_lift {F : Type} [Field F] [Finite F]
    {b c' : F} (hbc : ∀ t : F, t ^ 2 + b * t + c' ≠ 0)
    (N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F))
    (hN2 : N ≤ (CFSG.PGLModel.orthogonalMinus 2 F b c').map Matrix.ProjGenLinGroup.mk)
    {r : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F}
    (hr : r ∈ CFSG.PGLModel.orthogonalMinus 2 F b c')
    {x0 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F} (hQx0 : nine3Q F b c' x0 ≠ 0)
    (hrx0 : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F r =
      reflect (nine3Q F b c') x0)
    {c x : ↥N}
    (hc : ((c : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      nine3MKTL F (reflect (nine3Q F b c') x0))
    (hcx : IsConj c x) :
    ∃ p : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F,
      nine3Q F b c' p ≠ 0 ∧
      ((x : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
        nine3MKTL F (reflect (nine3Q F b c') p) ∧
      nine3Q F b c' p = nine3Q F b c' x0 := by
  obtain ⟨n, hn⟩ := isConj_iff.mp hcx
  obtain ⟨A, hA, hAmk⟩ := Subgroup.mem_map.mp (hN2 n.2)
  have hAO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F A ∈
      TauCeti.QuadraticMap.orthogonalGroup (nine3Q F b c') := by
    have h := hA
    rw [nine3_orth63_orthogonal_eq F b c'] at h
    exact Subgroup.mem_comap.mp h
  refine ⟨CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F A x0, ?_, ?_, ?_⟩
  · rw [map_of_mem hAO]
    exact hQx0
  · have hconj : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F
        (A * (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm
          (reflect (nine3Q F b c') x0) * A⁻¹) =
        reflect (nine3Q F b c')
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F A x0) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact reflect_conj hAO x0
    calc ((x : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F)
        = ((n * c * n⁻¹ : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := by
          rw [hn]
      _ = ((n : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
            ((c : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
            (((n : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F))⁻¹ := by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = Matrix.ProjGenLinGroup.mk A * nine3MKTL F (reflect (nine3Q F b c') x0) *
            (Matrix.ProjGenLinGroup.mk A)⁻¹ := by rw [hAmk, hc]
      _ = Matrix.ProjGenLinGroup.mk (A *
              (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm
                (reflect (nine3Q F b c') x0) * A⁻¹) := by
          rw [nine3MKTL_apply, ← map_inv, ← map_mul, ← map_mul]
      _ = nine3MKTL F (reflect (nine3Q F b c')
              (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F A x0)) := by
          rw [nine3MKTL_apply, ← hconj, MulEquiv.symm_apply_apply]
  · rw [map_of_mem hAO]

theorem nine3_prop710_orth63 {F : Type} [Field F] [Finite F] (hF : Nat.card F = 3) {b c' : F}
    (hbc : ∀ t : F, t ^ 2 + b * t + c' ≠ 0)
    (N : Subgroup (Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F))
    (hN1 : CFSG.PGLModel.projOmegaMinus 2 F b c' ≤ N)
    (hN2 : N ≤ (CFSG.PGLModel.orthogonalMinus 2 F b c').map Matrix.ProjGenLinGroup.mk)
    {c a e a' v : ↥N} {r : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F}
    (hr : r ∈ CFSG.PGLModel.orthogonalMinus 2 F b c') (hr1 : IsRankOneIn r)
    (hcr : ((c : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      Matrix.ProjGenLinGroup.mk r)
    (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  letI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 3 := by rwa [Nat.card_eq_fintype_card] at hF
  have hchar : CharP F 3 := charP_of_card_eq_prime hcard
  haveI : CharP F 3 := hchar
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    exact absurd ((CharP.cast_eq_zero_iff F 3 2).mp h0) (by omega)
  have h3 : (3 : F) = 0 := CharP.cast_eq_zero F 3
  have hsq_one : ∀ t : F, t ≠ 0 → t * t = 1 := by
    intro t ht
    have hp := FiniteField.pow_card_sub_one_eq_one t ht
    rw [hcard] at hp
    rw [show (3 : ℕ) - 1 = 2 by norm_num] at hp
    rw [pow_two] at hp
    exact hp
  have h2nsq : ∀ t : F, t * t ≠ 2 := by
    intro t ht
    have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ht
      exact h2 ht.symm
    have h1 := hsq_one t ht0
    have h12 : (2 : F) = 1 := by rw [← ht, h1]
    have h10 : (1 : F) = 0 := by
      have hh : (2 : F) - 1 = 0 := sub_eq_zero.mpr h12
      rw [show (2 : F) - 1 = 1 by norm_num] at hh
      exact hh
    exact one_ne_zero h10
  have hQ : (polarBilin (nine3Q F b c')).Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite (n := 3) (K := F) hbc
  have hrO : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F r ∈
      TauCeti.QuadraticMap.orthogonalGroup (nine3Q F b c') := by
    have h' := hr
    rw [nine3_orth63_orthogonal_eq F b c'] at h'
    exact Subgroup.mem_comap.mp h'
  have hr1' : Module.finrank F (CFSG.RankThree.OrthogonalInvolutions.commSpace
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F r)) = 1 := by
    rw [← nine3_orth63_rank_eq F r]
    exact nine3_isRankOneIn_rank r hr1
  obtain ⟨x0, hQx0, hrx0⟩ := nine3_rank_one_isometry_eq_reflect hQ h2 hrO hr1'
  have hc_eq : ((c : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      nine3MKTL F (reflect (nine3Q F b c') x0) := by
    rw [hcr]
    rw [show Matrix.ProjGenLinGroup.mk r = nine3MKTL F (reflect (nine3Q F b c') x0) from ?_]
    rw [nine3MKTL_apply, ← hrx0, MulEquiv.symm_apply_apply]
  obtain ⟨pa, hQpa, ha_eq, hQpa0⟩ :=
    nine3_orth63_lift hbc N hN2 hr hQx0 hrx0 hc_eq h.conj_a
  obtain ⟨pe, hQpe, he_eq, hQpe0⟩ :=
    nine3_orth63_lift hbc N hN2 hr hQx0 hrx0 hc_eq h.conj_e
  obtain ⟨pv, hQpv, hv_eq, hQpv0⟩ :=
    nine3_orth63_lift hbc N hN2 hr hQx0 hrx0 hc_eq h.conj_v
  have hbeta : polar (nine3Q F b c') pa pe ≠ 0 := by
    intro h0
    apply h.not_comm_ae
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ha_eq, he_eq]
    show nine3MKTL F (reflect (nine3Q F b c') pa) * nine3MKTL F (reflect (nine3Q F b c') pe) =
      nine3MKTL F (reflect (nine3Q F b c') pe) * nine3MKTL F (reflect (nine3Q F b c') pa)
    rw [← map_mul, ← map_mul, CFSG.GH74.Filter.reflect_comm h0]
  have hpvpa : polar (nine3Q F b c') pv pa = 0 := by
    refine nine3_polar_eq_zero_of_mk_commute h2nsq hQ hQpv hQpa
      (hQpv0.trans hQpa0.symm) ?_ ?_
    · intro cc hcc hpa
      have hav : a = v := by
        apply Subtype.ext
        rw [ha_eq, hv_eq, hpa, nine3_reflect_smul hcc hQpv]
      apply h.not_comm_ae
      rw [hav]
      exact h.comm_ve
    · have hcomm : ((v * a : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
          ((a * v : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := by
        rw [h.comm_va]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hv_eq, ha_eq] at hcomm
      exact hcomm
  have hpvpe : polar (nine3Q F b c') pv pe = 0 := by
    refine nine3_polar_eq_zero_of_mk_commute h2nsq hQ hQpv hQpe
      (hQpv0.trans hQpe0.symm) ?_ ?_
    · intro cc hcc hpe
      have hev : e = v := by
        apply Subtype.ext
        rw [he_eq, hv_eq, hpe, nine3_reflect_smul hcc hQpv]
      apply h.not_comm_ae
      rw [hev]
      exact h.comm_va.symm
    · have hcomm : ((v * e : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
          ((e * v : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := by
        rw [h.comm_ve]
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hv_eq, he_eq] at hcomm
      exact hcomm
  set c0 : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F :=
    polar (nine3Q F b c') pa pe • pa - (2 * (nine3Q F b c') pa) • pe with hc0def
  have hQc0 : (nine3Q F b c') c0 = 0 := by
    rw [hc0def]
    exact nine3_radical_quad_eq_zero hQpa (hQpe0.trans hQpa0.symm) hbeta h3 hsq_one
  have hQpv_c0 : polar (nine3Q F b c') pv c0 = 0 := by
    rw [hc0def, QuadraticMap.polar_sub_right, QuadraticMap.polar_smul_right,
      QuadraticMap.polar_smul_right, hpvpa, hpvpe, smul_zero, smul_zero, sub_zero]
  have hQc0_pv : polar (nine3Q F b c') c0 pv = 0 := by
    rw [polar_comm]; exact hQpv_c0
  have hQpa1 : (nine3Q F b c') pa * (nine3Q F b c') pa = 1 := hsq_one _ hQpa
  have hbeta1 : polar (nine3Q F b c') pa pe * polar (nine3Q F b c') pa pe = 1 :=
    hsq_one _ hbeta
  have hQc0_pa : polar (nine3Q F b c') c0 pa = 0 := by
    rw [polar_comm (nine3Q F b c') c0 pa, hc0def, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right, QuadraticMap.polar_self,
      smul_eq_mul, smul_eq_mul]
    ring
  have hQc0_pe : polar (nine3Q F b c') c0 pe = 0 := by
    rw [polar_comm (nine3Q F b c') c0 pe, hc0def, QuadraticMap.polar_sub_right,
      QuadraticMap.polar_smul_right, QuadraticMap.polar_smul_right,
      polar_comm (nine3Q F b c') pe pa, QuadraticMap.polar_self, smul_eq_mul, smul_eq_mul]
    rw [hQpe0.trans hQpa0.symm]
    linear_combination (norm := ring) hbeta1 - 4 * hQpa1 - h3
  have hc0_ne : c0 ≠ 0 := by
    intro hc0
    have hpe : pe = ((2 * (nine3Q F b c') pa)⁻¹ * polar (nine3Q F b c') pa pe) • pa := by
      have hh : polar (nine3Q F b c') pa pe • pa = (2 * (nine3Q F b c') pa) • pe := by
        rw [hc0def, sub_eq_zero] at hc0
        exact hc0
      have h2Q : (2 : F) * (nine3Q F b c') pa ≠ 0 := mul_ne_zero h2 hQpa
      calc pe = ((2 * (nine3Q F b c') pa)⁻¹ * (2 * (nine3Q F b c') pa)) • pe := by
              rw [inv_mul_cancel₀ h2Q, one_smul]
        _ = (2 * (nine3Q F b c') pa)⁻¹ • ((2 * (nine3Q F b c') pa) • pe) := by rw [smul_smul]
        _ = (2 * (nine3Q F b c') pa)⁻¹ • (polar (nine3Q F b c') pa pe • pa) := by rw [← hh]
        _ = ((2 * (nine3Q F b c') pa)⁻¹ * polar (nine3Q F b c') pa pe) • pa := by rw [smul_smul]
    have hev : e = a := by
      apply Subtype.ext
      rw [he_eq, ha_eq, hpe, nine3_reflect_smul
        (mul_ne_zero (inv_ne_zero (mul_ne_zero h2 hQpa)) hbeta) hQpa]
    apply h.not_comm_ae
    rw [hev]
  have hs'_ne_pv : ∀ mu : F, (pv + c0) ≠ mu • pv := by
    intro mu hs'
    have hc0_eq : c0 = (mu - 1) • pv := by
      linear_combination (norm := module) hs'
    have hz : polar (nine3Q F b c') c0 pv = (mu - 1) * (2 * (nine3Q F b c') pv) := by
      rw [hc0_eq, QuadraticMap.polar_smul_left, QuadraticMap.polar_self, nsmul_eq_mul,
        smul_eq_mul]
      ring
    have hz0 : (mu - 1) * (2 * (nine3Q F b c') pv) = 0 := by
      rw [← hz, hQc0_pv]
    rw [mul_eq_zero] at hz0
    rcases hz0 with hz0 | hz0
    · rw [sub_eq_zero] at hz0
      exact hc0_ne (by rw [hc0_eq, hz0, sub_self, zero_smul])
    · exact absurd hz0 (mul_ne_zero h2 hQpv)
  have hs'notprop : ∀ cc : F, cc ≠ 0 → pv ≠ cc • (pv + c0) := by
    intro cc hcc hpv
    have hs'mem : (pv + c0) = cc⁻¹ • pv := by
      have h' := congrArg (fun x : Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F => cc⁻¹ • x) hpv
      rw [smul_smul, inv_mul_cancel₀ hcc, one_smul] at h'
      exact h'.symm
    exact hs'_ne_pv cc⁻¹ hs'mem
  have hQpv_s'_ne : polar (nine3Q F b c') pv (pv + c0) ≠ 0 := by
    have hh : polar (nine3Q F b c') pv (pv + c0) = polar (nine3Q F b c') pv pv := by
      rw [QuadraticMap.polar_add_right, hQpv_c0, add_zero]
    rw [hh, QuadraticMap.polar_self, nsmul_eq_mul]
    exact mul_ne_zero h2 hQpv
  have hQc0_s' : (nine3Q F b c') (pv + c0) = (nine3Q F b c') pv := by
    rw [QuadraticMap.map_add (nine3Q F b c' : (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → F) → F), hQc0,
      polar_comm (nine3Q F b c') pv c0, hQc0_pv, add_zero, add_zero]
  have hQx0_s' : (nine3Q F b c') x0 = (nine3Q F b c') (pv + c0) := by
    rw [hQc0_s']; exact hQpv0.symm
  obtain ⟨g, hgE, hgx⟩ := nine3_reflect_isConj hQ
    (P := CFSG.ClassicalGroups.Orthogonal.minusPair F b c' 0)
    (P' := CFSG.ClassicalGroups.Orthogonal.minusPair F b c' 1)
    (CFSG.ClassicalGroups.Orthogonal.minusPair_orth (i := 0) (j := 1) (by decide))
    hQx0 (by rw [hQc0_s']; exact hQpv) hQx0_s'
  have hg_comm : g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (nine3Q F b c'),
      TauCeti.QuadraticMap.orthogonalGroup (nine3Q F b c')⁆ :=
    CFSG.ClassicalGroups.Orthogonal.elementaryGroup_quadMinus_le_commutator
      (m := 3) (by norm_num) hbc hgE
  have hA_stated : (CFSG.ClassicalGroups.Orthogonal.toLinEquiv
        (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm g ∈ CFSG.Open.StatedOmega
      (CFSG.PGLModel.minusQuadForm 2 (K := F) b c') := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap
      (nine3_orth63_quadCoe F b c')]
    refine Subgroup.mem_comap.mpr ?_
    simpa using hg_comm
  have hPO : CFSG.PGLModel.projOmegaMinus 2 F b c' =
      (CFSG.Open.StatedOmega (CFSG.PGLModel.minusQuadForm 2 (K := F) b c')).map
        Matrix.ProjGenLinGroup.mk := rfl
  have hmem : nine3MKTL F g ∈ N := by
    apply hN1
    rw [hPO]
    exact Subgroup.mem_map.mpr ⟨(CFSG.ClassicalGroups.Orthogonal.toLinEquiv
      (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm g, hA_stated, rfl⟩
  let nA : ↥N := ⟨nine3MKTL F g, hmem⟩
  let d : ↥N := nA * c * nA⁻¹
  have hA_conj : CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F
      ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm g *
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm
          (reflect (nine3Q F b c') x0) *
        ((CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F).symm g)⁻¹) =
      reflect (nine3Q F b c') (pv + c0) := by
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
    exact hgx
  have hd_eq : ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      nine3MKTL F (reflect (nine3Q F b c') (pv + c0)) := by
    have h1 : ((nA : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
        nine3MKTL F g := rfl
    have h2 : ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
        ((nA : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        ((c : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        (((nA : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F))⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, h1, hc_eq]
    show nine3MKTL F g * nine3MKTL F (reflect (nine3Q F b c') x0) * (nine3MKTL F g)⁻¹ =
      nine3MKTL F (reflect (nine3Q F b c') (pv + c0))
    have hgx' : g * reflect (nine3Q F b c') x0 * g⁻¹ = reflect (nine3Q F b c') (pv + c0) := by
      have h := hA_conj
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply] at h
      exact h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg (nine3MKTL F) hgx'
  have hda : d * a = a * d := by
    apply Subtype.ext
    show ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        ((a : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      ((a : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F)
    rw [hd_eq, ha_eq]
    show nine3MKTL F (reflect (nine3Q F b c') (pv + c0)) *
        nine3MKTL F (reflect (nine3Q F b c') pa) =
      nine3MKTL F (reflect (nine3Q F b c') pa) *
        nine3MKTL F (reflect (nine3Q F b c') (pv + c0))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [CFSG.GH74.Filter.reflect_comm]
    rw [QuadraticMap.polar_add_left, hpvpa, hQc0_pa, add_zero]
  have hde : d * e = e * d := by
    apply Subtype.ext
    show ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        ((e : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
      ((e : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
        ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F)
    rw [hd_eq, he_eq]
    show nine3MKTL F (reflect (nine3Q F b c') (pv + c0)) *
        nine3MKTL F (reflect (nine3Q F b c') pe) =
      nine3MKTL F (reflect (nine3Q F b c') pe) *
        nine3MKTL F (reflect (nine3Q F b c') (pv + c0))
    rw [← map_mul, ← map_mul]
    congr 1
    rw [CFSG.GH74.Filter.reflect_comm]
    rw [QuadraticMap.polar_add_left, hpvpe, hQc0_pe, add_zero]
  have hdv_ne : d * v ≠ v * d := by
    intro hcomm
    have hcommP : ((d * v : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
        ((v * d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := by rw [hcomm]
    have hcommM : nine3MKTL F (reflect (nine3Q F b c') (pv + c0)) *
          nine3MKTL F (reflect (nine3Q F b c') pv) =
          nine3MKTL F (reflect (nine3Q F b c') pv) *
          nine3MKTL F (reflect (nine3Q F b c') (pv + c0)) := by
      have h' : ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
          ((v : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) =
          ((v : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) *
          ((d : ↥N) : Matrix.ProjGenLinGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) F) := by
        simpa only [Subgroup.coe_mul] using hcommP
      rw [hd_eq, hv_eq] at h'
      exact h'
    have h0 := nine3_polar_eq_zero_of_mk_commute h2nsq hQ (x := pv + c0) (y := pv)
      (by rw [hQc0_s']; exact hQpv) hQpv (by rw [hQc0_s']) hs'notprop hcommM
    exact hQpv_s'_ne (by rwa [polar_comm] at h0)
  have hd_ne : d ≠ v := by
    intro hdv
    apply hdv_ne
    rw [hdv]
  exact ⟨d, isConj_iff.mpr ⟨nA, rfl⟩, hd_ne, hda, hde⟩

end CFSG.LocalAnalysis.WeakClosure81
