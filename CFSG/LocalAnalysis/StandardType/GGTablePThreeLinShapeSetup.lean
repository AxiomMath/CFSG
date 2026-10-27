module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeRLeaf
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
import CFSG.RankThree.PartTwo.Sec21.Hering214KEig
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearAction
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256h
import CFSG.RankThree.PartTwo.Sec6.BThreeCensusL4
import CFSG.RankThree.PartTwo.Sec4.RonanK432DiagThree
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.ClassicalInvolution.Balance.LocalBalance.Faithful
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly
open Polynomial CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.CALinearPrimary

private theorem mem_fixSubgroup_iff {G : Type*} [Group G] (α : MulAut G) (x : G) :
    x ∈ CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α ↔ α x = x := Iff.rfl

private theorem map_fixSubgroup_eq {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (α : MulAut G) (β : MulAut H) (h : MulAut.congr e α = β) :
    (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α).map e.toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_fixSubgroup_iff] at hx ⊢
    rw [← h]
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply, hx]
  · intro hy
    rw [mem_fixSubgroup_iff] at hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [mem_fixSubgroup_iff]
    apply e.injective
    change MulAut.congr e α y = e (e.symm y)
    rw [h, hy, MulEquiv.apply_symm_apply]

private theorem ggAutFixedSubgroup_eq_fixSubgroup {G : Type*} [Group G] (α : MulAut G) :
    ggAutFixedSubgroup α = CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup α := by
  ext x
  rw [mem_fixSubgroup_iff]
  rfl

private theorem eq_linConjAut_of_graphAut {N : ℕ} {K : Type} [Field K]
    {d : GL (Fin N) K} {δ' : MulAut (PSLg N K)}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ') :
    δ' = CFSG.StandardType.TableB.linConjAut (Fin N) K d := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H h =>
    rw [CFSG.StandardType.TableB.linConjAut_mk]
    exact hd h (MulAut.conjNormal d h) (MulAut.conjNormal_apply d h)

private theorem congr_recipeEquiv_linConjAut {N : ℕ} {K : Type} [Field K] (d : GL (Fin N) K) :
    MulAut.congr (CFSG.StandardType.TypeA.recipeEquiv N K)
        (CFSG.StandardType.TableB.linConjAut (Fin N) K d) =
      LinearFlag.conjAut N K d := by
  ext x
  obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N K x
  set h : ↥(LargeEvenSLGroup (Fin N) K) :=
    (CFSG.StandardType.TypeA.slKerEquiv N K).symm g with hh
  have h1 : (CFSG.StandardType.TypeA.slKerEquiv N K) h = g := by
    rw [hh, MulEquiv.apply_symm_apply]
  have hx : CFSG.StandardType.TypeA.recipeEquiv N K
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) = LinearFlag.proj N K g := by
    rw [CFSG.StandardType.TypeA.recipeEquiv_mk, h1]
  have hsymm : (CFSG.StandardType.TypeA.recipeEquiv N K).symm (LinearFlag.proj N K g) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h := by
    rw [MulEquiv.symm_apply_eq]
    exact hx.symm
  have hlin : (CFSG.StandardType.TableB.linConjAut (Fin N) K d)
      (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) h) =
      LargeEvenProjMk (LargeEvenSLGroup (Fin N) K) (MulAut.conjNormal d h) := by
    change (CFSG.StandardType.TableB.linConjAut (Fin N) K d) (h : PSLg N K) =
      (MulAut.conjNormal d h : PSLg N K)
    exact CFSG.StandardType.TableB.linConjAut_mk d h
  rw [MulAut.congr_apply, MulEquiv.trans_apply, hsymm, MulEquiv.trans_apply, hlin,
    CFSG.StandardType.TypeA.recipeEquiv_mk,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.conjAut_proj]
  apply congrArg (LinearFlag.proj N K)
  apply Matrix.SpecialLinearGroup.toGL_injective
  have htoGL : Matrix.SpecialLinearGroup.toGL
      ((CFSG.StandardType.TypeA.slKerEquiv N K) (MulAut.conjNormal d h)) =
      (MulAut.conjNormal d h : GL (Fin N) K) := by
    apply Units.ext
    exact CFSG.StandardType.TypeA.coe_slKerEquiv (MulAut.conjNormal d h)
  have hg : Matrix.SpecialLinearGroup.toGL g = (h : GL (Fin N) K) := by
    rw [← h1]
    rfl
  rw [htoGL, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    hg, MulAut.conjNormal_apply]

private theorem natDegree_mul_primaryMultiplicity_le {K : Type} [Field K] {N : ℕ}
    {x : Module.End K (Fin N → K)} {a : K[X]} [Fact (Irreducible a)] :
    a.natDegree * primaryMultiplicity x a ≤ N := by
  have h : Module.finrank K ↥(primaryComponent x a) =
      a.natDegree * primaryMultiplicity x a := by
    rw [primaryMultiplicity, finrank_primaryComponent]
  rw [← h]
  calc Module.finrank K ↥(primaryComponent x a) ≤ Module.finrank K (Fin N → K) :=
        Submodule.finrank_le _
    _ = N := Module.finrank_fin_fun K

private theorem natDegree_le_three_of_mem_primaryFactors {K : Type} [Field K] {N : ℕ}
    {d : GL (Fin N) K} {c : Kˣ}
    (hc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {h : K[X]} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K))) :
    h.natDegree ≤ 3 := by
  have hdvd : h ∣ X ^ 3 - C (c : K) :=
    ((mem_primaryFactors.mp hh).2.2).trans
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.minpoly_dvd_X_pow_sub_C_of_pow_scalar
        (p := 3) hc)
  have hne : (X ^ 3 - C (c : K) : K[X]) ≠ 0 :=
    (monic_X_pow_sub_C _ (by norm_num)).ne_zero
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rwa [natDegree_X_pow_sub_C] at hle

private theorem eq_X_pow_three_sub_C_of_natDegree_eq_three {K : Type} [Field K] {N : ℕ}
    {d : GL (Fin N) K} {c : Kˣ}
    (hc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {h : K[X]} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hdeg : h.natDegree = 3) : h = X ^ 3 - C (c : K) := by
  have hdvd : h ∣ X ^ 3 - C (c : K) :=
    ((mem_primaryFactors.mp hh).2.2).trans
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.minpoly_dvd_X_pow_sub_C_of_pow_scalar
        (p := 3) hc)
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have htmon : (X ^ 3 - C (c : K) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have hle : (X ^ 3 - C (c : K) : K[X]).natDegree ≤ h.natDegree := by
    rw [natDegree_X_pow_sub_C, hdeg]
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon htmon hdvd hle).symm

private theorem three_dvd_card_sub_one_of_natDegree_eq_three {K : Type} [Field K] [Finite K]
    {N : ℕ} {d : GL (Fin N) K} {c : Kˣ}
    (hc : d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c)
    {h : K[X]} (hh : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)))
    (hdeg : h.natDegree = 3) : 3 ∣ Nat.card K - 1 := by
  classical
  by_contra h3
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ν, hν⟩ :=
    CFSG.RankThree.PartTwo.Sec6.BThreeCensus.exists_pow_three_eq_of_not_three_dvd h3 c
  have hcν : (ν : K) ^ 3 = (c : K) := by
    have h := congrArg (fun u : Kˣ => (u : K)) hν
    simpa only [Units.val_pow_eq_pow_val] using h
  have hdvd : h ∣ X ^ 3 - C (c : K) :=
    ((mem_primaryFactors.mp hh).2.2).trans
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.minpoly_dvd_X_pow_sub_C_of_pow_scalar
        (p := 3) hc)
  have hfac : (X ^ 3 - C (c : K) : K[X]) =
      (X - C (ν : K)) * (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2)) := by
    rw [← hcν]
    simp only [Polynomial.C_pow]
    ring
  have hirr : Irreducible h := irreducible_of_mem_primaryFactors hh
  have hprod : h ∣ (X - C (ν : K)) * (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2)) :=
    hfac ▸ hdvd
  have hlin : ¬ h ∣ (X - C (ν : K)) := by
    intro hdiv
    have hne : (X - C (ν : K) : K[X]) ≠ 0 := X_sub_C_ne_zero (ν : K)
    have hle := Polynomial.natDegree_le_of_dvd hdiv hne
    rw [natDegree_X_sub_C, hdeg] at hle
    omega
  have hquad : h ∣ (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2)) := by
    have hcop : IsCoprime h (X - C (ν : K)) := by
      rcases hirr.isCoprime_or_dvd (X - C (ν : K)) with hc' | hd'
      · exact hc'
      · exact absurd hd' hlin
    exact hcop.dvd_of_dvd_mul_left hprod
  have hEq : h = X ^ 3 - C (c : K) :=
    eq_X_pow_three_sub_C_of_natDegree_eq_three hc hh hdeg
  have hhf : h = (X - C (ν : K)) * (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2)) := by
    rw [hEq, hfac]
  have hquad_ne : (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2) : K[X]) ≠ 0 := by
    intro hzero
    have hz : (X ^ 3 - C (c : K) : K[X]) = 0 := by rw [hfac, hzero, mul_zero]
    exact (monic_X_pow_sub_C _ (by norm_num)).ne_zero hz
  have hquaddeg : (X ^ 2 + C (ν : K) * X + C ((ν : K) ^ 2) : K[X]).natDegree ≤ 2 := by
    have hnm := congrArg natDegree hhf
    rw [hdeg, natDegree_mul (X_sub_C_ne_zero (ν : K)) hquad_ne, natDegree_X_sub_C] at hnm
    omega
  have hle := Polynomial.natDegree_le_of_dvd hquad hquad_ne
  omega

private theorem primaryFactors_eq_singleton_of_minpoly_eq {K : Type} [Field K]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {x : Module.End K V} {h : K[X]} (hirr : Irreducible h) (hmon : h.Monic)
    (hmin : minpoly K x = h) : primaryFactors x = {h} := by
  ext a
  rw [Finset.mem_singleton, mem_primaryFactors]
  constructor
  · rintro ⟨ha_irr, ha_mon, ha_dvd⟩
    exact eq_of_monic_of_associated ha_mon hmon
      (ha_irr.associated_of_dvd hirr (hmin ▸ ha_dvd))
  · intro ha
    rw [ha]
    exact ⟨hirr, hmon, by rw [hmin]⟩

theorem linShape_setup
    {K : Type} [Field K] [Finite K]
    {N : ℕ}
    {δ' : MulAut (PSLg N K)}
    {J' : Subgroup (PSLg N K)} (hchar : CharP K 2) (hN : 2 ≤ N)
    (hspl : 3 ∣ Nat.card K - 1 ∨ Nat.card K = 2)
    (hcomp : IsComponentOf J' (ggAutFixedSubgroup δ'))
    {d : GL (Fin N) K}
    (hd : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K))
        (fun h h' => (h' : GL (Fin N) K) = d * h * d⁻¹) δ')
    (hd3 : d ^ 3 ∈ LargeEvenScalars (Fin N) K) :
    ∃ (h : Polynomial K) (_ : h ∈ primaryFactors (glA d : Module.End K (Fin N → K))) (_ : IsGoodFactor d h)
      (e : PSLg N K ≃* LinearFlag.projectiveSL N K)
      (E : Type) (_ : Field E) (_ : Finite E) (_ : CharP E 2) (m j : ℕ)
      (f : Matrix.SpecialLinearGroup (Fin m) E →* ↥J'),
      m = primaryMultiplicity (glA d : Module.End K (Fin N → K)) h ∧ j = h.natDegree ∧
      J' = Subgroup.comap e.toMonoidHom ((specialFactor d h).map (LinearFlag.proj N K)) ∧
      2 ≤ m ∧ (m = 2 → 4 ≤ Nat.card E) ∧ 1 ≤ j ∧ j ≤ 3 ∧
        Nat.card E = Nat.card K ^ j ∧ j * m ≤ N ∧
        (j = 3 → 3 ∣ Nat.card K - 1 ∧ N = 3 * m) ∧ (j = 2 → Nat.card K = 2) ∧
        Function.Surjective f ∧ f.ker ≤ Subgroup.center _ := by
  haveI hcharI : CharP K 2 := hchar
  haveI : Fintype K := Fintype.ofFinite K
  have hk3 : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    exact one_ne_zero
  obtain ⟨c, hc⟩ : ∃ c : Kˣ, d ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) c := by
    have hmem : d ^ 3 ∈ (Matrix.GeneralLinearGroup.scalar (Fin N)).range := by
      simpa only [CFSG.Assembly.largeEvenScalars_def] using hd3
    obtain ⟨c, hc⟩ := hmem
    exact ⟨c, hc.symm⟩
  let e : PSLg N K ≃* LinearFlag.projectiveSL N K :=
    CFSG.StandardType.TypeA.recipeEquiv N K
  have hδ : MulAut.congr e δ' = LinearFlag.conjAut N K d := by
    rw [eq_linConjAut_of_graphAut hd, congr_recipeEquiv_linConjAut]
  have hcomp : Assembly.IsComponentOf (J'.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (LinearFlag.conjAut N K d)) := by
    have h1 := isComponentOf_map_mulEquiv' e hcomp
    rwa [ggAutFixedSubgroup_eq_fixSubgroup,
      map_fixSubgroup_eq e δ' (LinearFlag.conjAut N K d) hδ] at h1
  have hcompO : Open.IsComponentOf (J'.map e.toMonoidHom)
      (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup (LinearFlag.conjAut N K d)) :=
    isComponentOf_iff_open.mp hcomp
  obtain ⟨hh, hK⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.linear_inner_components
      (p := 3) hk3 hc (J'.map e.toMonoidHom) hcompO
  let h : K[X] := hh.1.1
  have hh_mem : h ∈ primaryFactors (glA d : Module.End K (Fin N → K)) := hh.1.2
  have hh_good : IsGoodFactor d h := hh.2
  have hK' : J'.map e.toMonoidHom = (specialFactor d h).map (LinearFlag.proj N K) := hK
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh_mem⟩
  have hmon : h.Monic := monic_of_mem_primaryFactors hh_mem
  have hdvd : h ∣ X ^ 3 - C (c : K) :=
    ((mem_primaryFactors.mp hh_mem).2.2).trans
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.minpoly_dvd_X_pow_sub_C_of_pow_scalar
        (p := 3) hc)
  have hsq : Squarefree (minpoly K (glA d : Module.End K (Fin N → K))) :=
    squarefree_minpoly_glA (p := 3) hk3 hc
  let m : ℕ := primaryMultiplicity (glA d : Module.End K (Fin N → K)) h
  let j : ℕ := h.natDegree
  obtain ⟨φ⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_mulEquiv_specialFactor hsq hh_mem
  obtain ⟨f₀, hf₀, hker₀⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieComp.exists_surjective_ker_le_center_map_proj φ
  let eJ : J' ≃* (specialFactor d h).map (LinearFlag.proj N K) :=
    hK' ▸ Subgroup.equivMapOfInjective J' e.toMonoidHom e.injective
  let f : Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) →* ↥J' :=
    eJ.symm.toMonoidHom.comp f₀
  have hf : Function.Surjective f := eJ.symm.surjective.comp hf₀
  have hker : f.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) := by
    intro x hx
    apply hker₀
    rw [MonoidHom.mem_ker] at hx ⊢
    have hx' : eJ.symm (f₀ x) = 1 := hx
    exact eJ.symm.injective (by rw [hx', map_one])
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite K
  haveI : CharP (AdjoinRoot h) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AdjoinRoot h)).injective 2
  have hm2 : 2 ≤ m := by
    rcases hh_good with h3 | ⟨h2, _⟩ <;> omega
  have hmE : m = 2 → 4 ≤ Nat.card (AdjoinRoot h) := by
    rcases hh_good with h3 | ⟨h2, h4⟩
    · intro hm; omega
    · intro _; exact h4
  have hj1 : 1 ≤ j := (Fact.out : Irreducible h).natDegree_pos
  have hjle3 : j ≤ 3 := natDegree_le_three_of_mem_primaryFactors hc hh_mem
  have hcard : Nat.card (AdjoinRoot h) = Nat.card K ^ j :=
    CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h
  have hjm : j * m ≤ N := natDegree_mul_primaryMultiplicity_le (x :=
    (glA d : Module.End K (Fin N → K))) (a := h)
  have hj3case : j = 3 → 3 ∣ Nat.card K - 1 ∧ N = 3 * m := by
    intro hj3
    have hdeg : h.natDegree = 3 := hj3
    constructor
    · exact three_dvd_card_sub_one_of_natDegree_eq_three hc hh_mem hdeg
    · have hEq : h = X ^ 3 - C (c : K) :=
        eq_X_pow_three_sub_C_of_natDegree_eq_three hc hh_mem hdeg
      have hmin_dvd : minpoly K (glA d : Module.End K (Fin N → K)) ∣ h := by
        rw [hEq]
        exact
          CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256h.minpoly_dvd_X_pow_sub_C_of_pow_scalar
            (p := 3) hc
      have hdvd_min : h ∣ minpoly K (glA d : Module.End K (Fin N → K)) :=
        (mem_primaryFactors.mp hh_mem).2.2
      have hmin_eq : minpoly K (glA d : Module.End K (Fin N → K)) = h :=
        Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon
          (minpoly.monic (Algebra.IsIntegral.isIntegral _)) hdvd_min
          (Polynomial.natDegree_le_of_dvd hmin_dvd hmon.ne_zero)
      have hpf : primaryFactors (glA d : Module.End K (Fin N → K)) = {h} :=
        primaryFactors_eq_singleton_of_minpoly_eq
          (irreducible_of_mem_primaryFactors hh_mem) hmon hmin_eq
      have hsum := finrank_eq_sum_degree_mul_multiplicity (x :=
        (glA d : Module.End K (Fin N → K))) hsq
      rw [Module.finrank_fin_fun, hpf] at hsum
      have hsum1 : N = h.natDegree * primaryMultiplicity (glA d : Module.End K (Fin N → K)) h := by
        simpa [hpf] using hsum
      have hsum' : N = h.natDegree * m := by simpa only [m] using hsum1
      rw [hdeg] at hsum'
      exact hsum'
  have hj2case : j = 2 → Nat.card K = 2 := by
    intro hj2
    have hdeg : h.natDegree = 2 := hj2
    rcases hspl with h3 | h2
    · exfalso
      obtain ⟨ω, hω, _⟩ :=
        CFSG.RankThree.PartTwo.Sec21.Hering214.exists_primitive_cube_root h3
      have hζ : IsPrimitiveRoot ω 3 :=
        CFSG.RankThree.PartTwo.Sec4.RonanK432.isPrimitiveRoot_three_of_sq_add_add_one hω hk3
      obtain ⟨b, hb⟩ := hdvd
      have hX0 : (X ^ 3 - C (c : K) : K[X]) ≠ 0 :=
        (monic_X_pow_sub_C _ (by norm_num)).ne_zero
      have hb0 : b ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hb
        exact hX0 hb
      have hdb : b.natDegree = 1 := by
        have hbdeg := congrArg natDegree hb
        rw [natDegree_X_pow_sub_C, natDegree_mul hmon.ne_zero hb0] at hbdeg
        omega
      obtain ⟨μ, hμ⟩ := Polynomial.exists_root_of_degree_eq_one
        ((degree_eq_iff_natDegree_eq_of_pos one_pos).mpr hdb)
      have hμ3 : μ ^ 3 = (c : K) := by
        have h0 : (X ^ 3 - C (c : K) : K[X]).eval μ = 0 := by
          rw [hb, eval_mul, hμ.eq_zero, mul_zero]
        simpa [sub_eq_zero] using h0
      have hsplits : (X ^ 3 - C (c : K) : K[X]).Splits :=
        X_pow_sub_C_splits_of_isPrimitiveRoot hζ hμ3
      have hle1 := (hsplits.of_dvd hX0 (show h ∣ X ^ 3 - C (c : K) from ⟨b, hb⟩)).natDegree_le_one_of_irreducible
        (irreducible_of_mem_primaryFactors hh_mem)
      omega
    · exact h2
  refine ⟨h, hh_mem, hh_good, e, AdjoinRoot h, inferInstance, inferInstance, inferInstance,
    m, j, f, rfl, rfl, ?_, hm2, hmE, hj1, hjle3, hcard, hjm, hj3case, hj2case, hf, hker⟩
  rw [← hK']
  exact (Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective J').symm

end CFSG.StandardType.TablePThreeKG

end
