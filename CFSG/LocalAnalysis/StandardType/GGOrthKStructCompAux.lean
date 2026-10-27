module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
public import CFSG.LocalAnalysis.StandardType.GGHalfBlockCentral
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
public import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGE0PSLComp
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

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.GGHalf
  CFSG.LieType.Universal.SpecialLinear Matrix
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.RankThree.PartOne.KCPrimary
open Polynomial

noncomputable section

theorem okComp_proj_injective (N : ℕ) : Function.Injective (LinearFlag.proj N F2) := by
  rw [← MonoidHom.ker_eq_bot_iff, LinearFlag.ker_proj N F2]
  exact le_bot_iff.mp ((LinearFlag.scalars_le_center N F2).trans (le_of_eq (center_eq_bot N)))

theorem okComp_slConjugation_eq_self_iff (N : ℕ) (t g : SpecialLinearGroup (Fin N) F2) :
    LinearFlag.conjAut N F2 (Matrix.SpecialLinearGroup.toGL t) (LinearFlag.proj N F2 g) =
        LinearFlag.proj N F2 g ↔
      g ∈ Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin N) F2)) := by
  rw [LinearFlag.conjAut_proj, (okComp_proj_injective N).eq_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation N F2
          (Matrix.SpecialLinearGroup.toGL t) g) = Matrix.SpecialLinearGroup.toGL g := by
      rw [h]
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation] at h'
    have h'' : Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL t := by
      calc Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL g
          = (Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL g *
              (Matrix.SpecialLinearGroup.toGL t)⁻¹) * Matrix.SpecialLinearGroup.toGL t := by
              group
        _ = Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL t := by rw [h']
    exact (Matrix.SpecialLinearGroup.toGL_injective (by rw [map_mul, map_mul]; exact h'')).symm
  · intro h
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
    have h'' : Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL g =
        Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL t := by
      rw [← map_mul, ← map_mul, h]
    calc Matrix.SpecialLinearGroup.toGL t * Matrix.SpecialLinearGroup.toGL g *
            (Matrix.SpecialLinearGroup.toGL t)⁻¹
        = (Matrix.SpecialLinearGroup.toGL g * Matrix.SpecialLinearGroup.toGL t) *
            (Matrix.SpecialLinearGroup.toGL t)⁻¹ := by rw [h'']
      _ = Matrix.SpecialLinearGroup.toGL g := by group

theorem okComp_map_centralizer_eq_fixSubgroup (N : ℕ) (t : SpecialLinearGroup (Fin N) F2) :
    (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin N) F2))).map
        (LinearFlag.proj N F2) =
      fixSubgroup (LinearFlag.conjAut N F2 (Matrix.SpecialLinearGroup.toGL t)) := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_fixSubgroup]
    exact (okComp_slConjugation_eq_self_iff N t g).mpr hg
  · intro hx
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective N F2 x
    rw [mem_fixSubgroup] at hx
    exact ⟨g, (okComp_slConjugation_eq_self_iff N t g).mp hx, rfl⟩

theorem okComp_component_map (N : ℕ) (t : SpecialLinearGroup (Fin N) F2)
    {J : Subgroup (SpecialLinearGroup (Fin N) F2)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin N) F2)))) :
    CFSG.Assembly.IsComponentOf (J.map (LinearFlag.proj N F2))
      (fixSubgroup (LinearFlag.conjAut N F2 (Matrix.SpecialLinearGroup.toGL t))) := by
  rw [← okComp_map_centralizer_eq_fixSubgroup N t]
  exact CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hJ _
    (okComp_proj_injective N)

theorem okComp_eq_of_map_proj_eq {N : ℕ} {S T : Subgroup (SpecialLinearGroup (Fin N) F2)}
    (h : S.map (LinearFlag.proj N F2) = T.map (LinearFlag.proj N F2)) : S = T := by
  apply le_antisymm
  · intro g hg
    have hmem : LinearFlag.proj N F2 g ∈ T.map (LinearFlag.proj N F2) := by
      rw [← h]; exact ⟨g, hg, rfl⟩
    obtain ⟨s, hs, hsp⟩ := hmem
    rw [← (okComp_proj_injective N hsp)]
    exact hs
  · intro g hg
    have hmem : LinearFlag.proj N F2 g ∈ S.map (LinearFlag.proj N F2) := by
      rw [h]; exact ⟨g, hg, rfl⟩
    obtain ⟨s, hs, hsp⟩ := hmem
    rw [← (okComp_proj_injective N hsp)]
    exact hs

theorem okComp_minpoly_dvd (N : ℕ) (A : GL (Fin N) F2)
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : F2ˣ)) :
    minpoly F2 (glA A : Module.End F2 (Fin N → F2)) ∣ X ^ 3 - 1 := by
  apply minpoly.dvd
  have hgl : ((glA A : LinearMap.GeneralLinearGroup F2 (Fin N → F2)) :
      Module.End F2 (Fin N → F2)) = Matrix.toLin' (A : Matrix (Fin N) (Fin N) F2) := rfl
  have hzero : aeval (glA A : Module.End F2 (Fin N → F2)) (X ^ 3 - C (1 : F2)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hgl, ← Matrix.toLin'_pow,
      ← Units.val_pow_eq_pow_val, hA]
    ext v i
    by_cases hi : i = v <;> simp [Matrix.toLin'_apply, Matrix.GeneralLinearGroup.scalar, hi]
  simpa only [C_1] using hzero

theorem okComp_primaryFactor_eq (N : ℕ) (A : GL (Fin N) F2)
    (hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : F2ˣ)) {h : F2[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End F2 (Fin N → F2))) (hdeg : 2 ≤ h.natDegree) :
    h = X ^ 2 + X + 1 := by
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmonic := monic_of_mem_primaryFactors hh
  have hdvd : h ∣ X ^ 3 - 1 :=
    ((mem_primaryFactors.mp hh).2.2).trans (okComp_minpoly_dvd N A hA)
  have hfac : (X : F2[X]) ^ 3 - 1 = (X - 1) * (X ^ 2 + X + 1) := by ring
  rw [hfac] at hdvd
  rcases hirr.prime.dvd_or_dvd hdvd with hd | hd
  · have hne1 : (X - 1 : F2[X]) ≠ 0 := by
      rw [show (1 : F2[X]) = C 1 from C_1.symm]
      exact (Polynomial.monic_X_sub_C (1 : F2)).ne_zero
    have hle := Polynomial.natDegree_le_of_dvd hd hne1
    have hdeg1 : (X - 1 : F2[X]).natDegree = 1 := by
      rw [show (1 : F2[X]) = C 1 from C_1.symm, Polynomial.natDegree_X_sub_C]
    rw [hdeg1] at hle
    omega
  · have h2 : (X ^ 2 + X + 1 : F2[X]).natDegree = 2 := by compute_degree!
    have hne : (X ^ 2 + X + 1 : F2[X]) ≠ 0 := by
      intro h0
      rw [h0] at h2
      simp at h2
    have hle := Polynomial.natDegree_le_of_dvd hd hne
    rw [h2] at hle
    have hmonic2 : (X ^ 2 + X + 1 : F2[X]).Monic := by
      have h1 : (X ^ 2 + X + 1 : F2[X]) = X ^ 2 + (X + 1) := by ring
      rw [h1]
      refine Polynomial.monic_X_pow_add ?_
      rw [show (1 : F2[X]) = C 1 from C_1.symm, Polynomial.degree_X_add_C]
      norm_num
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic hmonic2 hd (by omega)).symm

theorem okComp_statedClassicalModel {N : ℕ} (A : GL (Fin N) F2) {h : F2[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End F2 (Fin N → F2)))
    (hgood : IsGoodFactor A h)
    {J : Subgroup (SpecialLinearGroup (Fin N) F2)}
    (e : SpecialLinearGroup
        (Fin (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h)) (AdjoinRoot h) ≃* J) :
    StatedClassicalModel (J ⧸ Subgroup.center J) .PSL
      (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h) 2 h.natDegree := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  haveI : Finite (AdjoinRoot h) := Module.finite_of_finite F2
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hcard : Nat.card (AdjoinRoot h) = 2 ^ h.natDegree := by
    rw [CFSG.RankThree.PartOne.KCLinPlane.natCard_adjoinRoot h]
    congr 1
    simpa using GaloisField.card 2 1 (by omega)
  have hdeg1 : 1 ≤ h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hexcl1 : (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h, 2 ^ h.natDegree) ≠
      (2, 2) := by
    rintro hcon
    have hm : primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h = 2 :=
      (Prod.mk.inj hcon).1
    have hp : 2 ^ h.natDegree = 2 := (Prod.mk.inj hcon).2
    rcases hgood with h3 | ⟨-, h4⟩
    · omega
    · rw [hcard, hp] at h4
      omega
  have hexcl2 : (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h, 2 ^ h.natDegree) ≠
      (2, 3) := by
    rintro hcon
    have hp : 2 ^ h.natDegree = 3 := (Prod.mk.inj hcon).2
    have h2dvd : 2 ∣ 2 ^ h.natDegree := dvd_pow_self 2 (by omega)
    rw [hp] at h2dvd
    norm_num at h2dvd
  have hZ : ProjectiveSpecialLinearGroup
        (Fin (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h)) (AdjoinRoot h) ≃*
      (J ⧸ Subgroup.center J) :=
    QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
  have hiso : Nonempty ((J ⧸ Subgroup.center J) ≃*
      StatedProj (StatedSL (primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) h)
        (AdjoinRoot h))) :=
    ⟨hZ.symm.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj _ _)⟩
  exact ⟨⟨Nat.prime_two, hdeg1, hm2, hexcl1, hexcl2⟩, AdjoinRoot h, inferInstance, inferInstance,
    hcard, hiso⟩

theorem okComp_main (hRig : GGLabelRigidInput) {n : ℕ}
    (t : SpecialLinearGroup (Fin (n + 1)) F2) (ht : t ^ 3 = 1)
    {J : Subgroup (SpecialLinearGroup (Fin (n + 1)) F2)}
    (hJ : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({t} : Set (SpecialLinearGroup (Fin (n + 1)) F2))))
    (hf : ∃ f : ℕ, 2 ≤ f ∧ StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f) :
    Module.finrank F2 (LinearMap.ker (Matrix.toLin'
        (((t : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) ^ 2 +
          ((t : SpecialLinearGroup (Fin (n + 1)) F2) : Matrix (Fin (n + 1)) (Fin (n + 1)) F2) +
          1))) = 8 := by
  classical
  let N := n + 1
  let A : GL (Fin N) F2 := Matrix.SpecialLinearGroup.toGL t
  have hA3 : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin N) (1 : F2ˣ) := by
    rw [show A = Matrix.SpecialLinearGroup.toGL t from rfl, ← map_pow, ht, map_one]
    exact (map_one (Matrix.GeneralLinearGroup.scalar (Fin N))).symm
  have hpk : ((3 : ℕ) : F2) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff F2 2] at h0
    norm_num at h0
  have hsq : Squarefree (minpoly F2 (glA A : Module.End F2 (Fin N → F2))) :=
    squarefree_minpoly_glA (k := F2) (n := N) hpk hA3
  have hKcompA : CFSG.Assembly.IsComponentOf (J.map (LinearFlag.proj N F2))
      (fixSubgroup (LinearFlag.conjAut N F2 A)) := by
    rw [show A = Matrix.SpecialLinearGroup.toGL t from rfl]
    exact okComp_component_map N t hJ
  have hKcomp : CFSG.Open.IsComponentOf (J.map (LinearFlag.proj N F2))
      (fixSubgroup (LinearFlag.conjAut N F2 A)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hKcompA
  obtain ⟨hp, hKeq⟩ :=
    linear_inner_components (k := F2) (n := N) hpk hA3 (J.map (LinearFlag.proj N F2)) hKcomp
  have hJeq : J = specialFactor A hp.1.1 := okComp_eq_of_map_proj_eq hKeq
  obtain ⟨eSF⟩ := nonempty_mulEquiv_specialFactor (k := F2) (n := N) hsq hp.1.2
  let m := primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) hp.1.1
  let eJ : SpecialLinearGroup (Fin m) (AdjoinRoot hp.1.1) ≃* J :=
    eSF.trans (MulEquiv.subgroupCongr hJeq).symm
  have hmodel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL m 2 hp.1.1.natDegree :=
    okComp_statedClassicalModel A hp.1.2 hp.2 eJ
  have hm2 : 2 ≤ m := by
    rcases hp.2 with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have h1m : 1 ≤ m := by omega
  obtain ⟨f, hf2, hfmodel⟩ := hf
  have hlabel3 : GGHasLabel ⟨.A, 3, f⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_typeA (by simpa using hfmodel)
  have hlabel_m : GGHasLabel ⟨.A, m - 1, hp.1.1.natDegree⟩ (J ⧸ Subgroup.center J) :=
    ggHasLabel_typeA (n := m - 1) (f := hp.1.1.natDegree)
      (by simpa [Nat.sub_add_cancel h1m] using hmodel)
  have hLE3 : LargeEvenInLambda2 ⟨.A, 3, f⟩ :=
    largeEvenInLambda2_typeA (by simpa using hfmodel)
  have hLEm : LargeEvenInLambda2 ⟨.A, m - 1, hp.1.1.natDegree⟩ :=
    largeEvenInLambda2_typeA (n := m - 1) (f := hp.1.1.natDegree)
      (by simpa [Nat.sub_add_cancel h1m] using hmodel)
  have hcases := ggLabelIso_typeA_cases hRig (r := 3) (f := f)
    (lab := ⟨.A, m - 1, hp.1.1.natDegree⟩) (by norm_num) hLEm hLE3 hlabel_m hlabel3
  have hm4 : m = 4 := by
    rcases hcases with heq | ⟨-, heq⟩
    · have h' := heq
      simp only [LargeEvenLabel.mk.injEq] at h'
      omega
    · have h' := heq
      simp only [LargeEvenLabel.mk.injEq] at h'
      exact absurd h'.1 (by decide)
  have hdegf : hp.1.1.natDegree = f := by
    rcases hcases with heq | ⟨-, heq⟩
    · have h' := heq
      simp only [LargeEvenLabel.mk.injEq] at h'
      exact h'.2.2
    · have h' := heq
      simp only [LargeEvenLabel.mk.injEq] at h'
      exact absurd h'.1 (by decide)
  have hh_eq : hp.1.1 = X ^ 2 + X + 1 :=
    okComp_primaryFactor_eq N A hA3 hp.1.2 (by rw [hdegf]; exact hf2)
  have hmult : primaryMultiplicity (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1) = 4 := by
    rw [← hh_eq]
    exact hm4
  have hfin : Module.finrank F2
      (primaryComponent (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1)) = 8 := by
    haveI : Fact (Irreducible (X ^ 2 + X + 1 : F2[X])) :=
      ⟨by rw [← hh_eq]; exact irreducible_of_mem_primaryFactors hp.1.2⟩
    have hdeg2 : (X ^ 2 + X + 1 : F2[X]).natDegree = 2 := by compute_degree!
    calc Module.finrank F2
          (primaryComponent (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1))
        = (X ^ 2 + X + 1 : F2[X]).natDegree *
            Module.finrank (AdjoinRoot (X ^ 2 + X + 1 : F2[X]))
              (primaryComponent (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1)) :=
          finrank_primaryComponent (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1)
      _ = 8 := by
          have hmult' : Module.finrank (AdjoinRoot (X ^ 2 + X + 1 : F2[X]))
              (primaryComponent (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1)) = 4 :=
            hmult
          norm_num [hdeg2, hmult']
  have htoLin : Matrix.toLin' ((t : Matrix (Fin N) (Fin N) F2) ^ 2 +
      (t : Matrix (Fin N) (Fin N) F2) + 1) =
      (aeval (glA A : Module.End F2 (Fin N → F2)) (X ^ 2 + X + 1 : F2[X])) := by
    rw [map_add, map_add, Matrix.toLin'_pow, Matrix.toLin'_one]
    have hcoe : Matrix.toLin' (t : Matrix (Fin N) (Fin N) F2) =
        (glA A : Module.End F2 (Fin N → F2)) := by
      rw [show A = Matrix.SpecialLinearGroup.toGL t from rfl]
      rfl
    rw [hcoe]
    simp only [map_add, map_pow, aeval_X, map_one]
    rw [show LinearMap.id = (1 : Module.End F2 (Fin N → F2)) from rfl]
  change Module.finrank F2 (LinearMap.ker (Matrix.toLin'
    ((t : Matrix (Fin N) (Fin N) F2) ^ 2 + (t : Matrix (Fin N) (Fin N) F2) + 1))) = 8
  rw [htoLin]
  exact hfin

end

end CFSG.StandardType

end
