module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaMinus
public import CFSG.LieType.Universal.SpinOmega.Center
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaSec

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem emo_reindexGL_scalar {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {d : ℕ} (e : ι ≃ Fin d) (c : Kˣ) :
    (Equiv.reindexGL e K) (Matrix.GeneralLinearGroup.scalar ι c) =
      Matrix.GeneralLinearGroup.scalar (Fin d) c := by
  apply Units.ext
  rw [Equiv.coe_reindexGL, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.submatrix_diagonal (fun _ => (c : K)) e.symm e.symm.injective]
  rfl

private theorem emo_projEmbed {K : Type} [Field K] [CharP K 2]
    {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → K) → K)
    (d : ℕ) (e : ι ≃ Fin d)
    (hZ : (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) = ⊥)
    (hcenter : Subgroup.center (LargeEvenOmega Q) =
      (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q)) :
    GGClassicalProjEmbedAt d (LargeEvenProj (LargeEvenOmega Q)) (LargeEvenInnSet _) := by
  classical
  constructor
  · intro r
    exact ⟨r, rfl⟩
  · refine ⟨AlgebraicClosure K, inferInstance, inferInstance,
      charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2, ?_⟩
    let PGL := GL (Fin d) (AlgebraicClosure K) ⧸
      Subgroup.center (GL (Fin d) (AlgebraicClosure K))
    let f : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
    let Ψ : GL ι K →* GL (Fin d) (AlgebraicClosure K) :=
      (Matrix.GeneralLinearGroup.map f).comp (Equiv.reindexGL e K).toMonoidHom
    let ψ : ↥(LargeEvenOmega Q) →* PGL :=
      (QuotientGroup.mk' _).comp (Ψ.comp (LargeEvenOmega Q).subtype)
    have hΨinj : Function.Injective Ψ :=
      (Matrix.GeneralLinearGroup.map_injective f.injective).comp
        (Equiv.reindexGL e K).injective
    have hle : (Subgroup.center (GL (Fin d) (AlgebraicClosure K))).comap Ψ ≤
        Subgroup.center (GL ι K) := Subgroup.comap_center_le_center hΨinj
    have hker : ψ.ker = (LargeEvenScalars ι K).subgroupOf (LargeEvenOmega Q) := by
      ext g
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hg
        have h1 : QuotientGroup.mk' (Subgroup.center (GL (Fin d) (AlgebraicClosure K)))
            (Ψ (g : GL ι K)) = 1 := by
          show QuotientGroup.mk' (Subgroup.center (GL (Fin d) (AlgebraicClosure K)))
            (Ψ ((LargeEvenOmega Q).subtype g)) = 1
          exact hg
        rw [QuotientGroup.mk'_apply] at h1
        have hmem : Ψ (g : GL ι K) ∈
            Subgroup.center (GL (Fin d) (AlgebraicClosure K)) :=
          (QuotientGroup.eq_one_iff (Ψ (g : GL ι K))).mp h1
        have h2 : (g : GL ι K) ∈ Subgroup.center (GL ι K) := hle hmem
        rwa [Matrix.GeneralLinearGroup.center_eq_range_scalar] at h2
      · intro hg
        obtain ⟨c, hc⟩ := hg
        have hΨc : Ψ (Matrix.GeneralLinearGroup.scalar ι c) =
            Matrix.GeneralLinearGroup.scalar (Fin d) (Units.map f c) := by
          simp only [Ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
            emo_reindexGL_scalar, Matrix.GeneralLinearGroup.map_scalar]
        have hmem : Ψ (g : GL ι K) ∈
            Subgroup.center (GL (Fin d) (AlgebraicClosure K)) := by
          rw [← hc, hΨc, Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨Units.map f c, rfl⟩
        have h1 : QuotientGroup.mk' (Subgroup.center (GL (Fin d) (AlgebraicClosure K)))
            (Ψ (g : GL ι K)) = 1 :=
          (QuotientGroup.eq_one_iff (Ψ (g : GL ι K))).mpr hmem
        show QuotientGroup.mk' (Subgroup.center (GL (Fin d) (AlgebraicClosure K)))
          (Ψ ((LargeEvenOmega Q).subtype g)) = 1
        exact h1
    have hψinj : Function.Injective ψ :=
      (MonoidHom.ker_eq_bot_iff ψ).mp (by rw [hker, hZ])
    have eR : ↥(LargeEvenOmega Q) ≃* LargeEvenProj (LargeEvenOmega Q) :=
      TableBOrth.projMkEquiv hZ
    have hZR : Subgroup.center (LargeEvenProj (LargeEvenOmega Q)) = ⊥ := by
      have hcenter_bot : Subgroup.center ↥(LargeEvenOmega Q) = ⊥ := by rw [hcenter, hZ]
      rw [← Subgroup.map_center_eq eR, hcenter_bot, Subgroup.map_bot]
    have hconj : Function.Injective
        (MulAut.conj : LargeEvenProj (LargeEvenOmega Q) →*
          MulAut (LargeEvenProj (LargeEvenOmega Q))) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      rw [Subgroup.mem_bot]
      have hxc : x ∈ Subgroup.center (LargeEvenProj (LargeEvenOmega Q)) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h1 : (MulAut.conj x) y = y := by rw [hx, MulAut.one_apply]
        rw [MulAut.conj_apply] at h1
        calc y * x = (x * y * x⁻¹) * x := by rw [h1]
          _ = x * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
      rwa [hZR, Subgroup.mem_bot] at hxc
    let φR : LargeEvenProj (LargeEvenOmega Q) →* PGL := ψ.comp eR.symm.toMonoidHom
    have hφR : Function.Injective φR := hψinj.comp eR.symm.injective
    have hclosure : Subgroup.closure (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q))) =
        (MulAut.conj : LargeEvenProj (LargeEvenOmega Q) →*
          MulAut (LargeEvenProj (LargeEvenOmega Q))).range :=
      Subgroup.closure_eq ((MulAut.conj : LargeEvenProj (LargeEvenOmega Q) →*
        MulAut (LargeEvenProj (LargeEvenOmega Q))).range)
    let ε : ↥(Subgroup.closure (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega Q)))) →* PGL :=
      (φR.comp (MonoidHom.ofInjective hconj).symm.toMonoidHom).comp
        (MulEquiv.subgroupCongr hclosure).toMonoidHom
    exact ⟨ε, (hφR.comp (MonoidHom.ofInjective hconj).symm.injective).comp
      (MulEquiv.subgroupCongr hclosure).injective⟩

private theorem emo_omegaPlus_projEmbed {K : Type} [Field K] [CharP K 2]
    {m : ℕ} (hm : 3 ≤ m) :
    GGClassicalProjEmbedAt (m + m)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) (LargeEvenInnSet _) :=
  emo_projEmbed (LargeEvenQPlus K m) (m + m) finSumFinEquiv
    (TableBOrth.scalars_subgroupOf_omegaPlus_eq_bot (m := m) (by omega))
    (CFSG.LieType.Universal.Spin.center_statedOmega_quadPlus (K := K) (n := m) hm)

private def emo_minusIdxEquiv (m : ℕ) : LargeEvenMinusIdx m ≃ Fin (m + m + 2) :=
  (Equiv.sumCongr (finSumFinEquiv (m := m) (n := m)) (Equiv.refl (Fin 2))).trans
    (finSumFinEquiv (m := m + m) (n := 2))

private theorem emo_omegaMinus_projEmbed {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 3 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGClassicalProjEmbedAt (m + m + 2)
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _) := by
  refine emo_projEmbed (LargeEvenQMinus m b c) (m + m + 2) (emo_minusIdxEquiv m) ?_ ?_
  · exact TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot b c
  · haveI hperf : Group.IsPerfect (LargeEvenOmega (LargeEvenQMinus m b c)) := by
      haveI : Group.IsPerfect
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) K b c)) :=
        CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus (n := m + 1)
          (by omega) hirr
      exact Group.IsPerfect.ofSurjective
        (f := (LayerCyc.largeEvenOmegaMinusEquiv m K b c).symm.toMonoidHom)
        (LayerCyc.largeEvenOmegaMinusEquiv m K b c).symm.surjective
    haveI hsimple : IsSimpleGroup
        (CFSG.Open.StatedProj (LargeEvenOmega (LargeEvenQMinus m b c))) := by
      haveI : IsSimpleGroup
          (CFSG.Open.StatedProj (CFSG.Open.StatedOmega
            (CFSG.Open.StatedQuadMinus (m + 1) K b c))) :=
        CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
          (n := m + 1) (by omega) hirr
      exact (omegaMinusProjEquiv (m + 1) b c).isSimpleGroup
    exact CFSG.LieType.Universal.Spin.center_eq_statedScalars_subgroupOf

theorem ggClassicalProjEmbed_orth (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .D ∨ lab.tag = .twD) (hn : ¬ GGClassLinUni lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGClassicalProjEmbedAt (ggClassDeg lab) R I := by
  obtain ⟨t, l, n⟩ := lab
  rcases h with hD | htwD
  · dsimp only at hD
    subst hD
    dsimp only [LargeEvenInLambda2] at hlab
    have hl3 : l ≠ 3 := fun h3 =>
      hn (Or.inr (Or.inr (Or.inl ⟨rfl, h3⟩)))
    have h4 : 4 ≤ l := by omega
    refine largeEvenLabelAll_omegaPlus (lab := ⟨.D, l, n⟩) rfl h4 ?_
    intro K _ _ _ _
    have hdeg : ggClassDeg (⟨.D, l, n⟩ : LargeEvenLabel) = l + l := by
      dsimp only [ggClassDeg]
      rw [if_neg hl3, two_mul]
    rw [hdeg]
    exact emo_omegaPlus_projEmbed (K := K) (m := l) (by omega)
  · dsimp only at htwD
    subst htwD
    dsimp only [LargeEvenInLambda2] at hlab
    have hl2 : l ≠ 2 := fun h2 =>
      hn (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl h2⟩)))
    have hl3 : l ≠ 3 := fun h3 =>
      hn (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr h3⟩)))
    have h4 : 4 ≤ l := by omega
    refine largeEvenLabelAll_omegaMinus (lab := ⟨.twD, l, n⟩) rfl h4 ?_
    intro K _ _ _ _ b c hirr
    have hdeg : ggClassDeg (⟨.twD, l, n⟩ : LargeEvenLabel) = l + l := by
      dsimp only [ggClassDeg]
      rw [if_neg hl2, if_neg hl3, two_mul]
    have hm : (l - 1) + (l - 1) + 2 = l + l := by omega
    rw [hdeg, ← hm]
    exact emo_omegaMinus_projEmbed (K := K) (m := l - 1) (by omega) hirr

end CFSG.StandardType

end
