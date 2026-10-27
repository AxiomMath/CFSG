module

public import CFSG.RankThree.PartOne.SEITZ6.G2Bruhat

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

theorem reflect_0' : reflect .G2 e1 (rt 0) = rt 3 := by decide +kernel
theorem reflect_3' : reflect .G2 e0 (rt 3) = rt 7 := by decide +kernel

theorem exists_sl2_hom_7_10 [CharP K 2] :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K,
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Upper c) = xp 7 c) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Lower c) = xp 10 c) := by
  obtain ⟨φ, -, hu, hl⟩ := g2_exists_sl2_hom (K := K) e0
  have hu' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Upper c) = xp 0 c := fun c => by
    rw [hu, xp, rt0_eq, xPar_simple]
  have hl' : ∀ c, φ (CFSG.LieType.Steinberg.sl2Lower c) = xp 2 c := fun c => by
    rw [hl, xp, rt2_eq, xPar_neg_simple]
  set W : adjointGroup .G2 K := weylElement .G2 K e0 * weylElement .G2 K e1 with hW
  refine ⟨(MulAut.conj W).toMonoidHom.comp φ, fun c => ?_, fun c => ?_⟩
  · rw [MonoidHom.comp_apply, hu', MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hW,
      show weylElement .G2 K e0 * weylElement .G2 K e1 * xp 0 c *
        (weylElement .G2 K e0 * weylElement .G2 K e1)⁻¹ =
        weylElement .G2 K e0 * (weylElement .G2 K e1 * xp 0 c * (weylElement .G2 K e1)⁻¹) *
          (weylElement .G2 K e0)⁻¹ by group,
      weylElement_conj_xp e1 (by norm_num) reflect_0',
      weylElement_conj_xp e0 (by norm_num) reflect_3']
  · rw [MonoidHom.comp_apply, hl', MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hW,
      show weylElement .G2 K e0 * weylElement .G2 K e1 * xp 2 c *
        (weylElement .G2 K e0 * weylElement .G2 K e1)⁻¹ =
        weylElement .G2 K e0 * (weylElement .G2 K e1 * xp 2 c * (weylElement .G2 K e1)⁻¹) *
          (weylElement .G2 K e0)⁻¹ by group,
      weylElement_conj_xp e1 (by norm_num) reflect_2,
      weylElement_conj_xp e0 (by norm_num) reflect_6]

theorem rt_ne_rt_ten : ∀ t < 12, t ≠ 10 → rt t ≠ rt 10 := by decide +kernel

theorem bigCell [CharP K 2] (g : adjointGroup .G2 K)
    (hne0 : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ≠ 0) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 2) K →* adjointGroup .G2 K, ∃ μ₁ μ₂ : K,
      μ₁ ≠ 0 ∧ μ₂ ≠ 0 ∧ μ₁ * μ₂ = coordAt (rt 10) (g • rootVec .G2 K (rt 7)) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Upper (μ₁ * c)) = xp 7 c) ∧
      (∀ c, ψ (CFSG.LieType.Steinberg.sl2Lower (μ₂ * c)) = g * xp 7 c * g⁻¹) := by
  have hct := g2_isCTGroupDatum K
  have hext := g2_steinbergExtras K
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := CFSG.LieType.Steinberg.exists_mem_bruhatCell hct hext g
  obtain ⟨χ₁, a1, bb1, c1⟩ := borel_stab_X7 hb₁
  obtain ⟨χ₂, a2, bb2, c2⟩ := borel_stab_X7 hb₂
  obtain ⟨t, ht, hv, hc⟩ := nrep_stab_X7 (K := K) w
  have hlam : coordAt (rt 10) (g • rootVec .G2 K (rt 7)) =
      ((χ₁⁻¹ : Kˣ) : K) * ((χ₂ : K) * coordAt (rt 10) (rootVec .G2 K (rt t))) := by
    rw [hg, mul_smul, mul_smul, a2, smul_smul_comm, hv, bb1, coordAt_smul]
  have ht12 : t < 12 := by
    simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
    omega
  have ht10 : t = 10 := by
    by_contra hne
    apply hne0
    rw [hlam, coordAt_rootVec_ne (rt_ne_rt_ten t ht12 hne).symm]
    simp
  subst ht10
  obtain ⟨ψ₀, hu, hl⟩ := exists_sl2_hom_7_10 (K := K)
  refine ⟨(MulAut.conj b₁).toMonoidHom.comp ψ₀, ((χ₁⁻¹ : Kˣ) : K), (χ₂ : K), Units.ne_zero _,
    Units.ne_zero _, ?_, fun c => ?_, fun c => ?_⟩
  · rw [hlam, coordAt_rootVec_self (isRoot_rt (by norm_num))]
    simp
  · rw [MonoidHom.comp_apply, hu, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, c1,
      ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · rw [MonoidHom.comp_apply, hl, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg,
      show b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂ * xp 7 c *
        (b₁ * CFSG.LieType.Steinberg.nrep hct w * b₂)⁻¹ =
        b₁ * (CFSG.LieType.Steinberg.nrep hct w * (b₂ * xp 7 c * b₂⁻¹) *
          (CFSG.LieType.Steinberg.nrep hct w)⁻¹) * b₁⁻¹ by group, c2, hc]

end CFSG.RankThree.PartOne.SEITZ6
