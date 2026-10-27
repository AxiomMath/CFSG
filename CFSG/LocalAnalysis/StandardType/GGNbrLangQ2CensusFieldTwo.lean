module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CentLin
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
import CFSG.LocalAnalysis.StandardType.KGLangS1ALinTypeDet
import CFSG.LocalAnalysis.StandardType.GGTPNThmRACoreLin
import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeGLCore
import CFSG.LocalAnalysis.ComponentClassification.GS82L34Omega
import CFSG.RankThree.PartOne.KFOUT3.CycUnits

public section

namespace CFSG.StandardType

open Polynomial
open CFSG CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (proj conjAut projectiveSL)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.RankThree.PartOne.KCPrimary


private theorem q2cFT_split_eq_three {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (htag : lab.tag = .A) (hn : lab.n = 1) (hsplit : LargeEvenSplit p lab) : p = 3 := by
  rcases hsplit with ⟨-, hp1⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, hp3⟩
  · rw [hn] at hp1
    exact (hp.not_dvd_one (by simpa using hp1)).elim
  · rw [htag] at h
    exact (h trivial).elim
  · rw [htag] at h
    rcases h with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  · exact hp3

private theorem q2cFT_pow_three_eq_one {N : ℕ} (hN : 2 ≤ N) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2) {g : GL (Fin N) F}
    {u : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hgu : u = TableB.linConjAut (Fin N) F g) (huo : orderOf u = 3) : g ^ 3 = 1 := by
  have hker : TableB.linConjAut (Fin N) F (g ^ 3) = 1 := by
    rw [map_pow, ← hgu, ← huo, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := q1CentLin_scalar_of_linConjAut_eq_one hN hker
  have hcard : Nat.card Fˣ = 1 := by rw [Nat.card_units, hF]
  haveI : Subsingleton Fˣ := (Nat.card_eq_one_iff_unique.mp hcard).1
  have hc1 : c = 1 := Subsingleton.elim c 1
  rw [hc1] at hc
  simpa using hc.symm

private theorem q2cFT_map_ggAutFixedSubgroup {R R' : Type*} [Group R] [Group R']
    (e : R ≃* R') (σ : MulAut R) :
    (ggAutFixedSubgroup σ).map e.toMonoidHom = fixSubgroup (MulAut.congr e σ) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_fixSubgroup]
    have hy' : σ y = y := (mem_ggAutFixedSubgroup σ y).mp hy
    simp [MulAut.congr_apply, hy']
  · intro hx
    rw [mem_fixSubgroup] at hx
    have hx' : e (σ (e.symm x)) = x := by simpa [MulAut.congr_apply] using hx
    refine ⟨e.symm x, ?_, by simp⟩
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hx'

private theorem q2cFT_dvd_minpoly_of_ker_ne_bot {F V : Type} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] {x : Module.End F V} {a : F[X]}
    (ha : Irreducible a) (hker : LinearMap.ker (aeval x a) ≠ ⊥) : a ∣ minpoly F x := by
  by_contra hdvd
  have hcop : IsCoprime a (minpoly F x) := ha.coprime_iff_not_dvd.mpr hdvd
  have hdisj : Disjoint (LinearMap.ker (aeval x (minpoly F x)))
      (LinearMap.ker (aeval x a)) :=
    Polynomial.disjoint_ker_aeval_of_isCoprime x hcop.symm
  have htop : LinearMap.ker (aeval x (minpoly F x)) = ⊤ := by
    rw [minpoly.aeval, LinearMap.ker_zero]
  rw [htop] at hdisj
  have hbot : LinearMap.ker (aeval x a) = ⊥ := by
    simpa using hdisj.eq_bot
  exact hker hbot

private theorem q2cFT_centralQuot {N : ℕ} {F : Type} [Field F] [Finite F]
    (hpk : (3 : F) ≠ 0) {g : GL (Fin N) F} (hg : g ^ 3 = 1)
    {T : Subgroup (projectiveSL N F)} {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors (glA g : Module.End F (Fin N → F)))
    (hgood : IsGoodFactor g h)
    (hTeq : T = (specialFactor g h).map (proj N F)) :
    Nonempty (↥T ⧸ Subgroup.center ↥T ≃*
      projectiveSL (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)
        (AdjoinRoot h)) := by
  classical
  have hsq : Squarefree (minpoly F (glA g : Module.End F (Fin N → F))) :=
    squarefree_minpoly_glA hpk (c := 1) (by simpa using hg)
  obtain ⟨eSL⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor
    (A := g) hsq hh
  obtain ⟨f, hfsurj, hfker⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_surjective_ker_le_center_map_proj
      (n := N) (k := F) (S := specialFactor g h) eSL
  let eC : ↥T ≃* ↥((specialFactor g h).map (proj N F)) := MulEquiv.subgroupCongr hTeq
  let f' : Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)) (AdjoinRoot h) →* ↥T :=
    eC.symm.toMonoidHom.comp f
  have hf'surj : Function.Surjective f' := eC.symm.surjective.comp hfsurj
  have hf'ker : f'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)) (AdjoinRoot h)) := by
    rw [show f' = eC.symm.toMonoidHom.comp f from rfl, TypeA.ker_comp_mulEquiv]
    exact hfker
  have hqF := isQuasisimple_specialFactor hsq hh hgood
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup
      (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)) (AdjoinRoot h)) :=
    (CFSG.LocalCores.isQuasisimple_of_mulEquiv eSL.symm hqF).1
  obtain ⟨e1⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10F.quotEquiv_of_perfect_central f' hf'surj
    hperfSL hf'ker
  let e2 : (Matrix.SpecialLinearGroup
        (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)) (AdjoinRoot h) ⧸
        Subgroup.center (Matrix.SpecialLinearGroup
          (Fin (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)) (AdjoinRoot h))) ≃*
      projectiveSL (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h) (AdjoinRoot h) :=
    QuotientGroup.quotientMulEquivOfEq
      (LinearFlag.scalars_eq_center (primaryMultiplicity (glA g : Module.End F (Fin N → F)) h)
        (AdjoinRoot h)).symm
  exact ⟨e1.symm.trans e2⟩

theorem q2cFT_component {N : ℕ} {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    (hN : 2 ≤ N) {g : GL (Fin N) F} (hg : g ^ 3 = 1) (hg1 : g ≠ 1)
    {J : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F))}
    (hJ : CFSG.Open.IsComponentOf J (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)))
    (huniq : ∀ J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin N) F)),
      CFSG.Open.IsComponentOf J' (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) → J' = J) :
    ∃ a₀ a₁ : ℕ, N = a₀ + 2 * a₁ ∧
      ((3 ≤ a₀ ∧ a₁ ≤ 1 ∧
          Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
            LargeEvenProj (LargeEvenSLGroup (Fin a₀) F))) ∨
        (a₀ ≤ 2 ∧ 2 ≤ a₁ ∧
          ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = 4 ∧
            Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
              LargeEvenProj (LargeEvenSLGroup (Fin a₁) E)))) := by
  classical
  haveI : CharP F 2 := charP_two_of_card (m := 1) (by rw [hF]; norm_num)
  have hpk : (3 : F) ≠ 0 := by
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    have h31 : (3 : F) = 1 := by
      have : (3 : F) = 2 + 1 := by norm_num
      rw [this, h2, zero_add]
    rw [h31]; exact one_ne_zero
  have hx3 : (glA g : Module.End F (Fin N → F)) ^ 3 = 1 := by
    change (glA g : Module.End F (Fin N → F)) ^ 3 = 1
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]
  have hg' : g ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : Fˣ) := by
    simpa using hg
  have hsq : Squarefree (minpoly F (glA g : Module.End F (Fin N → F))) :=
    squarefree_minpoly_glA hpk (c := 1) hg'
  let eR := TypeA.recipeEquiv N F
  let T : Subgroup (projectiveSL N F) := J.map eR.toMonoidHom
  have hσ : MulAut.congr eR (TableB.linConjAut (Fin N) F g) = conjAut N F g :=
    q1CentLin_congr_linConjAut g
  have hgrp : (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)).map eR.toMonoidHom =
      fixSubgroup (conjAut N F g) := by
    rw [q2cFT_map_ggAutFixedSubgroup eR (TableB.linConjAut (Fin N) F g), hσ]
  have hgrp' : (fixSubgroup (conjAut N F g)).map eR.symm.toMonoidHom =
      ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g) := by
    rw [← hgrp]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      rw [← hwz]
      simpa using hw
    · intro hy
      exact ⟨eR y, Subgroup.mem_map_of_mem _ hy, by simp⟩
  have hJasm : CFSG.Assembly.IsComponentOf J
      (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) :=
    CFSG.Assembly.isComponentOf_iff_open.mpr hJ
  have hmap := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
    hJasm eR.toMonoidHom eR.injective
  have hT : CFSG.Open.IsComponentOf T (fixSubgroup (conjAut N F g)) := by
    rw [← hgrp]
    exact CFSG.Assembly.isComponentOf_iff_open.mp hmap
  have huniqT : ∀ T' : Subgroup (projectiveSL N F),
      CFSG.Open.IsComponentOf T' (fixSubgroup (conjAut N F g)) → T' = T := by
    intro T' hT'
    have hT'asm : CFSG.Assembly.IsComponentOf T' (fixSubgroup (conjAut N F g)) :=
      CFSG.Assembly.isComponentOf_iff_open.mpr hT'
    have hback := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective
      hT'asm eR.symm.toMonoidHom eR.symm.injective
    have hback' : CFSG.Assembly.IsComponentOf (T'.map eR.symm.toMonoidHom)
        (ggAutFixedSubgroup (TableB.linConjAut (Fin N) F g)) := by
      rw [← hgrp']
      exact hback
    have heq := huniq _ (CFSG.Assembly.isComponentOf_iff_open.mp hback')
    have hmapid : (T'.map eR.symm.toMonoidHom).map eR.toMonoidHom = T' := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
        rw [← hwz]
        simpa using hw
      · intro hy
        exact ⟨eR.symm y, Subgroup.mem_map_of_mem _ hy, by simp⟩
    rw [← hmapid, heq]
  let eJ : ↥J ≃* ↥T := Subgroup.equivMapOfInjective J eR.toMonoidHom eR.injective
  have hcenter : (Subgroup.center ↥J).map eJ.toMonoidHom = Subgroup.center ↥T :=
    Subgroup.map_center_eq eJ
  let eQ : (↥J ⧸ Subgroup.center ↥J) ≃* (↥T ⧸ Subgroup.center ↥T) :=
    QuotientGroup.congr (Subgroup.center ↥J) (Subgroup.center ↥T) eJ hcenter
  obtain ⟨h, hTeq⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
    (n := N) (k := F) hpk hg' T hT
  have hmem : (h.1.1 : F[X]) ∈ primaryFactors (glA g : Module.End F (Fin N → F)) := h.1.2
  have hgood : IsGoodFactor g (h.1.1 : F[X]) := h.2
  have hx3' : aeval (glA g : Module.End F (Fin N → F)) (X ^ 3 - C 1 : F[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hx3]
    simp
  have hdvd : (h.1.1 : F[X]) ∣ X ^ 3 - C 1 :=
    (mem_primaryFactors.mp hmem).2.2.trans (minpoly.dvd F (glA g : Module.End F (Fin N → F)) hx3')
  have hcls : (h.1.1 : F[X]) = X - C 1 ∨ (h.1.1 : F[X]) = X ^ 2 + X + 1 :=
    CFSG.HardMathSupport.Curtis.Coordinator.eq_X_sub_one_or_eq_quad_of_dvd hF
      (irreducible_of_mem_primaryFactors hmem) (monic_of_mem_primaryFactors hmem) hdvd
  have hdeg1 : (X - C 1 : F[X]).natDegree = 1 := Polynomial.natDegree_X_sub_C 1
  have hdeg2 : (X ^ 2 + X + 1 : F[X]).natDegree = 2 := by compute_degree!
  haveI : Fact (Irreducible (X - C 1 : F[X])) := ⟨Polynomial.irreducible_X_sub_C 1⟩
  haveI : Fact (Irreducible (X ^ 2 + X + 1 : F[X])) :=
    ⟨CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (by rw [hF]; norm_num)⟩
  have hcop : IsCoprime (X - C 1 : F[X]) (X ^ 2 + X + 1) :=
    CFSG.RankThree.PartOne.KFOUT3.coprime_quad
  have hprod : (X - C 1 : F[X]) * (X ^ 2 + X + 1) = X ^ 3 - C 1 := by
    rw [C_1]
    ring
  have hsup : LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X])) ⊔
      LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X])) = ⊤ := by
    rw [Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime
      (glA g : Module.End F (Fin N → F)) hcop, hprod, hx3']
    exact LinearMap.ker_zero
  have hdisj : Disjoint (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X])))
      (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X]))) :=
    Polynomial.disjoint_ker_aeval_of_isCoprime (glA g : Module.End F (Fin N → F)) hcop
  have hNsum : N = primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X]) +
      2 * primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X]) := by
    have hsum := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X])))
      (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X])))
    rw [hsup, hdisj.eq_bot, finrank_bot, add_zero, finrank_top] at hsum
    rw [Module.finrank_fin_fun] at hsum
    have h1 : Module.finrank F
        (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X]))) =
        primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X]) := by
      change Module.finrank F
        (primaryComponent (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X])) =
        primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X - C 1 : F[X])
      rw [finrank_primaryComponent, hdeg1, one_mul]
    have h2 : Module.finrank F
        (LinearMap.ker (aeval (glA g : Module.End F (Fin N → F))
          (X ^ 2 + X + 1 : F[X]))) =
        2 * primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X]) := by
      change Module.finrank F
        (primaryComponent (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X])) =
        2 * primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1 : F[X])
      rw [finrank_primaryComponent, hdeg2]
    rw [h1, h2] at hsum
    exact hsum
  refine ⟨primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X - C 1),
    primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1),
    hNsum, ?_⟩
  rcases hcls with hlin | hquad
  ·
    rw [hlin] at hmem hgood hTeq
    obtain ⟨eT⟩ := q2cFT_centralQuot (h := (X - C 1 : F[X])) hpk hg hmem hgood hTeq
    refine Or.inl ⟨?_, ?_, ?_⟩
    · rcases hgood with h3 | ⟨-, h4⟩
      · exact h3
      · exfalso
        have hcard : Nat.card (AdjoinRoot (X - C 1 : F[X])) = 2 := by
          rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg1, hF]
          norm_num
        omega
    · by_contra hlt
      have h2 : 2 ≤ primaryMultiplicity (glA g : Module.End F (Fin N → F))
          (X ^ 2 + X + 1) := by omega
      have hker : LinearMap.ker (aeval (glA g : Module.End F (Fin N → F))
          (X ^ 2 + X + 1 : F[X])) ≠ ⊥ := by
        intro hbot
        have hne : primaryComponent (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1) ≠ ⊥ :=
          Submodule.nontrivial_iff_ne_bot.mp
            (Module.nontrivial_of_finrank_pos
              (show 0 < primaryMultiplicity (glA g : Module.End F (Fin N → F))
                (X ^ 2 + X + 1) from by omega))
        exact hne hbot
      have hirr2 : Irreducible (X ^ 2 + X + 1 : F[X]) :=
        CFSG.RankThree.PartOne.KFOUT3.irreducible_quad (by rw [hF]; norm_num)
      have hmem2 : (X ^ 2 + X + 1 : F[X]) ∈ primaryFactors (glA g : Module.End F (Fin N → F)) :=
        mem_primaryFactors.mpr ⟨hirr2, by monicity!,
          q2cFT_dvd_minpoly_of_ker_ne_bot hirr2 hker⟩
      have hcard2 : Nat.card (AdjoinRoot (X ^ 2 + X + 1 : F[X])) = 4 := by
        rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg2, hF]
        norm_num
      have hgood2 : IsGoodFactor g (X ^ 2 + X + 1) :=
        Or.inr ⟨h2, by simp [hcard2]⟩
      have hcomp2 := CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor
        hsq hmem2 hgood2
      have heq2 := huniqT _ hcomp2
      have hjf : (X ^ 2 + X + 1 : F[X]) ≠ X - C 1 := by
        intro hcontra
        have hdeg := congrArg Polynomial.natDegree hcontra
        rw [hdeg2, hdeg1] at hdeg
        omega
      exact absurd (heq2.trans hTeq) (raLin_components_ne hsq hmem2 hmem hjf hgood)
    · refine ⟨eQ.trans (eT.trans ?_)⟩
      refine (CFSG.ComponentClassification.GSThmB.L34OmegaAux.projectiveSLCongr
        (Polynomial.quotientSpanXSubCAlgEquiv (1 : F)).toRingEquiv).trans
        (TypeA.recipeEquiv (primaryMultiplicity (glA g : Module.End F (Fin N → F))
          (X - C 1)) F).symm
  ·
    rw [hquad] at hmem hgood hTeq
    obtain ⟨eT⟩ := q2cFT_centralQuot (h := (X ^ 2 + X + 1 : F[X])) hpk hg hmem hgood hTeq
    haveI : Module.Finite F (AdjoinRoot (X ^ 2 + X + 1 : F[X])) :=
      (AdjoinRoot.powerBasis (Fact.out : Irreducible (X ^ 2 + X + 1 : F[X])).ne_zero).finite
    haveI : Finite (AdjoinRoot (X ^ 2 + X + 1 : F[X])) := Module.finite_of_finite F
    refine Or.inr ⟨?_, ?_, AdjoinRoot (X ^ 2 + X + 1 : F[X]), inferInstance, inferInstance,
      ?_, ?_⟩
    · by_contra hlt
      have h3 : 3 ≤ primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X - C 1) := by omega
      have hker0 : LinearMap.ker (aeval (glA g : Module.End F (Fin N → F))
          (X - C 1 : F[X])) ≠ ⊥ := by
        intro hbot
        have hne : primaryComponent (glA g : Module.End F (Fin N → F)) (X - C 1) ≠ ⊥ :=
          Submodule.nontrivial_iff_ne_bot.mp
            (Module.nontrivial_of_finrank_pos
              (show 0 < primaryMultiplicity (glA g : Module.End F (Fin N → F))
                (X - C 1) from by omega))
        exact hne hbot
      have hirr0 : Irreducible (X - C 1 : F[X]) := Polynomial.irreducible_X_sub_C 1
      have hmem0 : (X - C 1 : F[X]) ∈ primaryFactors (glA g : Module.End F (Fin N → F)) :=
        mem_primaryFactors.mpr ⟨hirr0, by monicity!,
          q2cFT_dvd_minpoly_of_ker_ne_bot hirr0 hker0⟩
      have hgood0 : IsGoodFactor g (X - C 1) := Or.inl h3
      have hcomp0 := CFSG.LocalAnalysis.GLTheoremA.T263.SD.Lin.isComponentOf_map_specialFactor
        hsq hmem0 hgood0
      have heq0 := huniqT _ hcomp0
      have hjf0 : (X - C 1 : F[X]) ≠ X ^ 2 + X + 1 := by
        intro hcontra
        have hdeg := congrArg Polynomial.natDegree hcontra
        rw [hdeg1, hdeg2] at hdeg
        omega
      exact absurd (heq0.trans hTeq) (raLin_components_ne hsq hmem0 hmem hjf0 hgood)
    · rcases hgood with h3 | ⟨h2, -⟩
      · omega
      · exact h2
    · rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot, hdeg2, hF]
      norm_num
    · refine ⟨eQ.trans (eT.trans (TypeA.recipeEquiv
        (primaryMultiplicity (glA g : Module.End F (Fin N → F)) (X ^ 2 + X + 1))
        (AdjoinRoot (X ^ 2 + X + 1 : F[X]))).symm)⟩

theorem q2c_rLevel_fieldTwo :
    Q2CensusRLevel (fun lab => lab.tag = .A ∧ lab.n = 1) (fun kind => kind = .fieldTwo) := by
  intro p d m lab hp hp2 hΛ hsplit hS hd hm hpd hpm Q hQ
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hn1⟩ := hS
  dsimp only at htag hn1
  subst htag
  subst hn1
  simp only [LargeEvenInLambda2] at hΛ
  obtain ⟨-, hl, -⟩ := hΛ
  have hp3 : p = 3 := q2cFT_split_eq_three hp rfl rfl hsplit
  subst hp3
  dsimp only [CFSG.StandardType.LargeEvenRawDatum, LargeEvenRecipeLinear] at hQ ⊢
  obtain ⟨F, _, _, hFcard, hQ'⟩ := hQ
  have hFcard' : Nat.card F = 2 := by simpa using hFcard
  refine ⟨F, inferInstance, inferInstance, hFcard, hQ', ?_⟩
  intro A hA hAI hbig h3 hlo hup u hu huo J hJ huniq hAJ K _ _ hKcard he
  haveI : CharP F 2 := charP_two_of_card hFcard
  have hN2 : 2 ≤ l + 1 := by omega
  obtain ⟨g, hgu⟩ := TableB.exists_eq_linConjAut (hAI u hu)
  have hu1 : u ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at huo
    omega
  have hg1 : g ≠ 1 := by
    intro h1
    apply hu1
    rw [hgu, h1, map_one]
  have hg3 : g ^ 3 = 1 := q2cFT_pow_three_eq_one hN2 hFcard' hgu huo
  have hJ' : CFSG.Open.IsComponentOf J
      (ggAutFixedSubgroup (TableB.linConjAut (Fin (l + 1)) F g)) := by
    rw [← hgu]
    exact hJ
  have huniq' : ∀ J' : Subgroup (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F)),
      CFSG.Open.IsComponentOf J'
        (ggAutFixedSubgroup (TableB.linConjAut (Fin (l + 1)) F g)) → J' = J := by
    intro J' hJ'
    rw [← hgu] at hJ'
    exact huniq J' hJ'
  obtain ⟨a₀, a₁, hNsum, hcase⟩ := q2cFT_component hFcard' hN2 hg3 hg1 hJ' huniq'
  rcases hcase with ⟨ha03, ha11, ⟨e1⟩⟩ | ⟨ha02, ha12, E, hEfld, hEfin, hEcard, ⟨e2⟩⟩
  ·
    obtain ⟨eJ⟩ := he
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a₀) F) :=
      (TypeA.recipeEquiv d K).symm.trans (eJ.symm.trans e1)
    obtain ⟨-, hFeq⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a₀) (m := m) (F₀ := K) (E := F)
        hd hm hKcard hψ
    have h2m : 2 ^ m = 2 ^ 1 := by rw [pow_one, ← hKcard, ← hFeq, hFcard']
    exact absurd (Nat.pow_right_injective (a := 2) (by norm_num) h2m) (by omega)
  ·
    letI : Field E := hEfld
    letI : Finite E := hEfin
    obtain ⟨eJ⟩ := he
    have hψ : LinearFlag.projectiveSL d K ≃*
        LargeEvenProj (LargeEvenSLGroup (Fin a₁) E) :=
      (TypeA.recipeEquiv d K).symm.trans (eJ.symm.trans e2)
    obtain ⟨ha1d, hEeq⟩ :=
      kgLangS1A_psl_typeDet (d := d) (d₁ := a₁) (m := m) (F₀ := K) (E := E)
        hd hm hKcard hψ
    have h2m : 2 ^ m = 4 := by rw [← hKcard, ← hEeq, hEcard]
    have hm2 : m = 2 := by
      have h : 2 ^ m = 2 ^ 2 := by rw [h2m]; norm_num
      exact Nat.pow_right_injective (a := 2) (by norm_num) h
    have hN : l + 1 = a₀ + 2 * d := by rw [hNsum, ha1d]
    have hN5 : 5 ≤ l + 1 := by omega
    have hlift : GGTorusLift 3 ((l + 1) / 2)
        (LargeEvenProj (LargeEvenSLGroup (Fin (l + 1)) F)) :=
      TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) F)
        (TwoThree.ggTorusLift_two (K := F) hFcard' hN5)
    have hbig' := hbig ((l + 1) / 2) hlift
    have hle : (l + 1) / 2 ≤ d :=
      (Nat.pow_le_pow_iff_right (show 1 < 3 by norm_num)).mp (hbig'.trans hup)
    have ha0le1 : a₀ ≤ 1 := by
      by_contra h
      have h2 : a₀ = 2 := by omega
      subst h2
      omega
    have hrank : l = 2 * d - 1 ∨ l = 2 * d := by omega
    exact ⟨.fieldTwo, rfl, hp, hp2, hpd, hpm, rfl, rfl, hrank, rfl, h2m⟩

end CFSG.StandardType
