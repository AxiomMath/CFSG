module

public import CFSG.RankThree.PartTwo.Sec21.ReeF4Cent2Proof

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.SEITZQ1
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag ReeF4Cent2Proof
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

open scoped MatrixGroups


theorem exists_centralizer_mulEquiv_unitarySU (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ∃ y : ReeTag.F4.reeGamma K a, orderOf y = 3 ∧
      Nonempty (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a)) ≃*
        unitarySU 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) 3) := by
  classical
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨D⟩ := reeFrameData_nonempty (K := K) (L := L) hK
  have hFrq : ∀ c, D.Frq c = c ^ 2 ^ (2 * a + 1) := frq_eq_pow D hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K' := GaloisField 2 (2 * (2 * a + 1))
  have hK' : Nat.card K' = 2 ^ (2 * (2 * a + 1)) := GaloisField.card 2 _ (by omega)
  have h : UnitaryFieldData 2 (2 * a + 1) K' := ⟨Nat.prime_two, by omega, hK'⟩
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  have : Algebra.IsAlgebraic (ZMod 2) K' := Algebra.IsAlgebraic.of_finite (ZMod 2) K'
  let ι : K' →+* L := (IsAlgClosed.lift (R := ZMod 2) (S := K') (M := L)).toRingHom
  obtain ⟨ω', hω', hbar⟩ := q1_exists_omega h (odd_two_mul_add_one a)
  have hω : ι ω' ^ 2 + ι ω' + 1 = 0 := by
    rw [← map_pow, ← map_add, ← map_one ι, ← map_add, hω', map_zero]
  have hω0 : ι ω' ≠ 0 := by
    intro h0
    rw [h0] at hω
    norm_num at hω
  set ω : Lˣ := Units.mk0 (ι ω') hω0 with hωdef
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    linear_combination (ι ω' - 1) * hω
  have hω1 : ω ≠ 1 := by
    intro h1
    have h1' : ι ω' = 1 := by rw [← Units.val_mk0 hω0, ← hωdef, h1, Units.val_one]
    rw [h1'] at hω
    have h3 : (3 : L) = 0 := by linear_combination hω
    have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
    have : (1 : L) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  have hωω : (ω * ω)⁻¹ = ω := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three', hω3]
  have hFr : ∀ c, D.Frq (ι c) = ι (h.bar c) := fun c => by
    rw [frq_eq_pow D hK, UnitaryFieldData.bar_apply, map_pow]
  obtain ⟨Ψ, hΨ⟩ := q1_exists_hom D hK hω (q1SUToSL h ι) (q1SUToSL_fixed h ι D.Frq hFr)
  have hj : Function.Injective (q1SUToSL h ι) := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hm : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K').map ι = 1 := by
      rw [← coe_q1SUToSL h ι, hu]
      rfl
    have hm' : ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') = 1 :=
      Matrix.map_injective ι.injective (hm.trans (Matrix.map_one ι ι.map_zero ι.map_one).symm)
    exact Subtype.ext (Units.ext hm')
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have h1 := (hΨ u).symm
    rw [hu, map_one, mul_inv_eq_one, mul_eq_left] at h1
    have h2 : q1SUToSL h ι u = 1 := q1Psi0_injective D.isFrob (by rw [h1, map_one])
    exact hj (by rw [h2, map_one])
  obtain ⟨x₀, hx₀⟩ := exists_scalar_unitarySU h hω' hbar
  have hjx₀ : q1SUToSL h ι x₀ = diag2 ω ω := by
    apply Subtype.ext
    rw [coe_q1SUToSL, hx₀, coe_diag2, Matrix.scalar_apply, Matrix.diagonal_map ι.map_zero]
    congr 1
    funext k
    fin_cases k
    · rfl
    · rfl
    · show ι ω' = (((ω * ω)⁻¹ : Lˣ) : L)
      rw [hωω, hωdef, Units.val_mk0]
  set d := rootDiagUnit ReeTag.F4.tag (fun _ => ω * ω) with hd
  have hψd : q1Psi0 D.isFrob (q1SUToSL h ι x₀) = d := by
    rw [hjx₀, q1Psi0_scalar D.isFrob hω3]
  set y₀ := Ψ x₀ with hy₀
  have hθy₀ : thetaGamma L a y₀ = q1C (ι ω') * d * (q1C (ι ω'))⁻¹ := by rw [hΨ x₀, hψd]
  have hx₀c : ∀ u : unitarySU 2 (2 * a + 1) K' 3, u * x₀ = x₀ * u := by
    intro u
    apply Subtype.ext
    apply Units.ext
    change ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') * ((x₀ : GL (Fin 3) K') :
      Matrix (Fin 3) (Fin 3) K') = ((x₀ : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K') *
        ((u : GL (Fin 3) K') : Matrix (Fin 3) (Fin 3) K')
    rw [hx₀]
    exact (Matrix.scalar_commute ω' (fun _ => Commute.all _ _) _).symm
  have hord : orderOf y₀ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hy₀, orderOf_injective Ψ hΨinj x₀]
    refine orderOf_eq_prime ?_ ?_
    · have h3 : q1SUToSL h ι (x₀ ^ 3) = 1 := by
        rw [map_pow, hjx₀]
        apply Subtype.ext
        rw [Matrix.SpecialLinearGroup.coe_pow, coe_diag2, Matrix.diagonal_pow,
          Matrix.SpecialLinearGroup.coe_one, ← Matrix.diagonal_one]
        congr 1
        funext k
        fin_cases k
        · show (ω : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
        · show (ω : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
        · show (((ω * ω)⁻¹ : Lˣ) : L) ^ 3 = 1
          rw [← Units.val_pow_eq_pow_val, show ((ω * ω)⁻¹) ^ 3 = (ω ^ 3)⁻¹ ^ 2 by group, hω3,
            inv_one, one_pow, Units.val_one]
      exact hj (h3.trans (map_one _).symm)
    · intro h1
      apply hω1
      have h2 := congrArg (q1SUToSL h ι) h1
      rw [hjx₀, map_one] at h2
      have h3 := congrArg (fun A : SL(3, L) => (A : Matrix (Fin 3) (Fin 3) L) 0 0) h2
      simp only [coe_diag2, Matrix.SpecialLinearGroup.coe_one, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] at h3
      exact Units.ext h3
  have hω2 : orderOf (ω * ω) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← sq, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hω3, one_pow]
    · intro h1
      apply hω1
      calc ω = ω ^ 3 * (ω * ω)⁻¹ := by rw [hωω, hω3, one_mul]
        _ = 1 := by rw [h1, hω3, inv_one, one_mul]
  have hstab := rootCharStabilizer_const_subset (L := L) hω2
  have hker := rootCharKernel_const_subset (L := L) hω2 (q1Par_cases a)
  have hcent : Subgroup.centralizer ({y₀} : Set (ReeTag.F4.reeGamma K a)) = Ψ.range := by
    apply le_antisymm
    · intro γ hγ
      rw [Subgroup.mem_centralizer_singleton_iff] at hγ
      set v := thetaGamma L a γ with hv
      set c := q1C (ι ω') with hc
      have hvadj : v ∈ adjointGroup ReeTag.F4.tag L := thetaGamma_mem_adjointGroup L γ
      have hcadj : c ∈ adjointGroup ReeTag.F4.tag L := q1C_mem_adjoint (ι ω')
      have hzR : c⁻¹ * v * c ∈ twistedFixed D.F (q1N L a) :=
        conj_mem_twistedFixed D.F hcadj (q1C_fext D.isFrob hω) hvadj (D.fext_theta γ)
      have hvy : v * thetaGamma L a y₀ = thetaGamma L a y₀ * v := by
        rw [hv, ← map_mul, ← map_mul, hγ]
      rw [hθy₀] at hvy
      have hzd : (c⁻¹ * v * c) * d = d * (c⁻¹ * v * c) := by
        calc (c⁻¹ * v * c) * d = c⁻¹ * (v * (c * d * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * d * c⁻¹) * v) * c := by rw [hvy]
          _ = d * (c⁻¹ * v * c) := by group
      have hzT : c⁻¹ * v * c ∈ toralCentralizer ReeTag.F4.tag L (fun _ => ω * ω) :=
        ⟨hzR.1, Subgroup.mem_centralizer_singleton_iff.2 hzd⟩
      have hzΦ : c⁻¹ * v * c ∈ (frameProd D.isFrob).range :=
        sup_le (torusGroup_le_range D.isFrob) (rootSpan_le_range D.isFrob)
          (CFSG.RankThree.PartOne.KE.toralCentralizer_le_sup_rootSpan_of_stab hstab
            (fun α hα => isRoot_of_mem_a2a2Roots hα)
            (fun α hα => neg_mem_a2a2Roots (q1Par_cases a) hα) hker hzT)
      obtain ⟨⟨g, h'⟩, hgh⟩ := hzΦ
      rw [frameProd_apply] at hgh
      have hfix : twistMap D.F (q1N L a) (q1Rho L g * q1PsiRho D.F a h') =
          q1Rho L g * q1PsiRho D.F a h' := by
        rw [hgh]
        exact hzR.2
      obtain ⟨g', hg', hzg'⟩ := exists_q1Psi0_of_twist_fixed D.isFrob D.Frq hFrq g h' hfix
      have hrange : ∀ c : L, D.Frq (D.Frq c) = c → ∃ x, ι x = c := by
        intro c hc2
        refine exists_eq_of_pow_card_eq ι ?_
        rw [hK', show 2 * (2 * a + 1) = (2 * a + 1) * 2 by ring, pow_mul, sq, pow_mul,
          ← hFrq, ← hFrq, hc2]
      obtain ⟨u, hu⟩ := exists_q1SUToSL_eq_of_fixed h ι D.Frq hFr hrange hg'
      refine ⟨u, thetaGamma_injective (K := K) L (a := a) ?_⟩
      rw [hΨ u, hu, ← hzg', hgh, hv]
      group
    · rintro _ ⟨u, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hy₀, ← map_mul, ← map_mul, hx₀c u]
  exact ⟨y₀, hord, ⟨(MulEquiv.subgroupCongr hcent).trans (MonoidHom.ofInjective hΨinj).symm⟩⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts2Proof
