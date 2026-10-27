module

public import CFSG.Assembly.Defs
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

import CFSG.Assembly.Subnormal
import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmShape
import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthUnBlock
import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
import CFSG.RankThree.PartOne.KC.OrthogonalCentralizerBlocks
import CFSG.RankThree.PartOne.KC.OrthogonalPrimarySummands
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.SectionRank.SignLines

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Polynomial CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2

private lemma ggLieSU3Fixed_isSubnormal_commutator {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {d : V ≃ₗ[K] V} {D B : Subgroup (V ≃ₗ[K] V)}
    (hD : CFSG.Assembly.IsComponentOf D
      (orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V))))
    (hle : D ≤ B)
    (hcomm : ⁅B, B⁆ ≤ orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V))) :
    CFSG.Assembly.IsSubnormal D ⁅B, B⁆ := by
  have hDperf : ⁅D, D⁆ = D :=
    (Subgroup.isPerfect_iff (H := D)).mp (Group.isPerfect_def.mpr hD.2.2.1)
  have hperf : D ≤ ⁅B, B⁆ := by
    rw [← hDperf]
    exact Subgroup.commutator_mono hle hle
  have h := hD.2.1.inf_of_le hcomm
  rwa [inf_eq_left.mpr hperf] at h

private lemma ggLieSU3Fixed_fixes_orbitSpace {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    {d z : V ≃ₗ[K] V} (hd : OddOrderIsometry Q 3 d) (hz : OddOrderIsometry Q 3 z)
    (hzd : d * z = z * d)
    (hzfix : ∀ v ∈ othersSpace d.toLinearMap (X - 1), z v = v)
    {j : K[X]} (hj : j ∈ primaryFactors z.toLinearMap) (hj1 : j ≠ X - 1) :
    ∀ v ∈ orbitSpace z.toLinearMap j, d v = v := by
  classical
  intro v hv
  have hdzc : d ∈ Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hzd
  have hstable : ∀ y ∈ orbitSpace z.toLinearMap j, d y ∈ orbitSpace z.toLinearMap j :=
    fun y hy => mem_orbitSpace_of_apply (x := z) hdzc hy
  obtain ⟨u, hu, r, hr, hvur⟩ :=
    SmallOrthUn.exists_split_orbit (h := (X - 1 : K[X])) (a := d) hd hstable hv
  have hu_fix : u ∈ fixedSpace d := by
    rw [fixedSpace_eq_primaryComponent]
    have huO : u ∈ orbitSpace d.toLinearMap (X - 1) := hu.2
    rwa [orbitSpace, reciprocalPolynomial_X_sub_one, sup_idem] at huO
  have hu_eq : d u = u := mem_fixedSpace.mp hu_fix
  have hr_pc : r ∈ primaryComponent z.toLinearMap (X - 1) := by
    rw [← fixedSpace_eq_primaryComponent]
    exact mem_fixedSpace.mpr (hzfix r hr.2)
  have hne_rec : reciprocalPolynomial j ≠ X - 1 := fun heq =>
    hj1 (by rw [← hz.reciprocal_reciprocal_eq hj, heq, reciprocalPolynomial_X_sub_one])
  have hr_others : r ∈ othersSpace z.toLinearMap j := by
    by_cases hX1 : (X - 1 : K[X]) ∈ primaryFactors z.toLinearMap
    · exact Submodule.mem_iSup_of_mem (X - 1) (Submodule.mem_iSup_of_mem
        ⟨hX1, hj1.symm, hne_rec.symm⟩ hr_pc)
    · have hbot : primaryComponent z.toLinearMap (X - 1) = ⊥ := by
        rw [← fixedSpace_eq_primaryComponent]
        exact fixedSpace_eq_bot_of_not_mem hX1
      have hr0 : r = 0 := by
        have : r ∈ (⊥ : Submodule K V) := by rwa [← hbot]
        simpa using this
      rw [hr0]
      exact Submodule.zero_mem _
  have hr0 : r = 0 := by
    have hdisj := (hz.isCompl_orbit_others hj).1
    have : r ∈ (⊥ : Submodule K V) := hdisj.le_bot ⟨hr.1, hr_others⟩
    simpa using this
  rw [hvur, map_add, hu_eq, hr0, map_zero, add_zero]

theorem ggLieSU3Fixed_exists_block {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {d z : V ≃ₗ[K] V} (hdO : d ∈ orthDerived Q) (hd3 : d ^ 3 = 1)
    (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) {D : Subgroup (V ≃ₗ[K] V)}
    (hD : CFSG.Assembly.IsComponentOf D
      (orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V))))
    (hzD : z ∈ D) (hzc : ∀ g ∈ D, z * g = g * z) :
    ∃ y ∈ ({d, z} : Set (V ≃ₗ[K] V)), ∃ j ∈ primaryFactors y.toLinearMap, j ≠ X - 1 ∧
      CFSG.Assembly.IsSubnormal D ⁅supportedBlock Q y j, supportedBlock Q y j⁆ := by
  classical
  have h3K : (3 : K) ≠ 0 := by
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h31 : (3 : K) = 1 := by
      rw [show (3 : K) = 2 + 1 by norm_num, h2, zero_add]
    rw [h31]
    exact one_ne_zero
  have hdO' : d ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hdO
  have hd : OddOrderIsometry Q 3 d :=
    ⟨hdO', hd3, h3K, fun v hv => hQ.1 v fun w => by
      simpa [QuadraticMap.polarBilin_apply_apply] using hv w⟩
  have hzO : z ∈ orthDerived Q := (Subgroup.mem_inf.mp (hD.1 hzD)).1
  have hzO' : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := orthDerived_le_orthogonalGroup hzO
  have hz : OddOrderIsometry Q 3 z :=
    ⟨hzO', hz3, h3K, fun v hv => hQ.1 v fun w => by
      simpa [QuadraticMap.polarBilin_apply_apply] using hv w⟩
  have hzd : d * z = z * d :=
    (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hD.1 hzD)).2).symm
  have hCzp : Subgroup.centralizer (Subgroup.zpowers d : Set (V ≃ₗ[K] V)) =
      Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hD_d : CFSG.Assembly.IsComponentOf D
      (orthDerived Q ⊓ Subgroup.centralizer (Subgroup.zpowers d : Set (V ≃ₗ[K] V))) := by
    rw [hCzp]
    exact hD
  haveI : IsMulCommutative ↥(Subgroup.zpowers d) := Subgroup.zpowers_isMulCommutative d
  have hEcomm : ∀ a ∈ Subgroup.zpowers d, ∀ b ∈ Subgroup.zpowers d, a * b = b * a :=
    fun a ha b hb => Subgroup.mul_comm_of_mem_isMulCommutative _ ha hb
  obtain ⟨h, hh, hDBd⟩ :=
    CoordOm.exists_le_supportedBlock_of_comm (Q := Q) (p := 3) (x := d) hd
      (Subgroup.mem_zpowers d) hEcomm (J := D) hD_d
  by_cases hX : h = X - 1
  ·
    have hDBdX : D ≤ supportedBlock Q d (X - 1) := hX ▸ hDBd
    have hzfixd : ∀ v ∈ othersSpace d.toLinearMap (X - 1), z v = v :=
      (mem_supportedBlock.mp (hDBdX hzD)).2
    let E' : Subgroup (V ≃ₗ[K] V) := Subgroup.closure ({d, z} : Set (V ≃ₗ[K] V))
    have hdE' : d ∈ E' := Subgroup.subset_closure (by simp)
    have hzE' : z ∈ E' := Subgroup.subset_closure (by simp)
    have hCE' : Subgroup.centralizer (E' : Set (V ≃ₗ[K] V)) =
        Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V)) ⊓
          Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V)) := by
      change Subgroup.centralizer
        (Subgroup.closure ({d, z} : Set (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) = _
      rw [Subgroup.centralizer_closure]
      ext x
      simp only [Subgroup.mem_centralizer_iff, Subgroup.mem_inf, Set.mem_insert_iff,
        Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    have hpair : Set.Pairwise ({d, z} : Set (V ≃ₗ[K] V)) (fun a b : V ≃ₗ[K] V => Commute a b) := by
      intro a ha b hb hab
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · rw [ha, hb]
      · rw [ha, hb]
        exact (commute_iff_eq d z).mpr hzd
      · rw [ha, hb]
        exact (commute_iff_eq z d).mpr hzd.symm
      · rw [ha, hb]
    haveI : IsMulCommutative ↥E' := Subgroup.isMulCommutative_closure hpair
    have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a :=
      fun a ha b hb => Subgroup.mul_comm_of_mem_isMulCommutative _ ha hb
    have hD_E'_le : D ≤ orthDerived Q ⊓ Subgroup.centralizer (E' : Set (V ≃ₗ[K] V)) := by
      intro g hg
      have hgK := hD.1 hg
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hgK).1, ?_⟩
      rw [hCE']
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hgK).2,
        Subgroup.mem_centralizer_singleton_iff.mpr (hzc g hg).symm⟩
    have hD_E' : CFSG.Assembly.IsComponentOf D
        (orthDerived Q ⊓ Subgroup.centralizer (E' : Set (V ≃ₗ[K] V))) :=
      hD.of_le_of_le hD_E'_le (by
        intro x hx
        refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1, ?_⟩
        exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdE')
          (Subgroup.mem_inf.mp hx).2)
    obtain ⟨j, hj, hDBz⟩ :=
      CoordOm.exists_le_supportedBlock_of_comm (Q := Q) (p := 3) (x := z) hz
        hzE' hE'comm (J := D) hD_E'
    have hj1 : j ≠ X - 1 := by
      intro hjX
      have hzBz : z ∈ supportedBlock Q z (X - 1) := by
        have := hDBz hzD
        rwa [hjX] at this
      have hzfixR : ∀ r ∈ othersSpace z.toLinearMap (X - 1), z r = r :=
        (mem_supportedBlock.mp hzBz).2
      have hz_eq_one : z = 1 := by
        refine LinearEquiv.ext fun v => ?_
        obtain ⟨hc, -⟩ := hz.fixed_others
        obtain ⟨u, hu, r, hr, hvu⟩ := exists_add_of_isCompl hc v
        have hzu : z u = u := mem_fixedSpace.mp hu
        have hzr : z r = r := hzfixR r hr
        rw [← hvu]
        show z (u + r) = u + r
        rw [map_add, hzu, hzr]
      exact hz1 hz_eq_one
    have hfixOrbit : ∀ v ∈ orbitSpace z.toLinearMap j, d v = v :=
      ggLieSU3Fixed_fixes_orbitSpace hd hz hzd hzfixd hj hj1
    have hdBcomm : ∀ w ∈ supportedBlock Q z j, d * w = w * d :=
      fun w hw => SmallOrthUn.commute_of_fix_orbit hz hj
        (Subgroup.mem_centralizer_singleton_iff.mpr hzd) hfixOrbit hw
    have hBcent : supportedBlock Q z j ≤ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V)) :=
      fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr (hdBcomm b hb).symm
    have hcomm : ⁅supportedBlock Q z j, supportedBlock Q z j⁆ ≤
        orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V)) := by
      intro g hg
      refine Subgroup.mem_inf.mpr ⟨(SmallOrthUn.commutator_supportedBlock_le (a := z) j hg).2,
        hBcent (Subgroup.commutator_le_self (supportedBlock Q z j) hg)⟩
    exact ⟨z, by simp, j, hj, hj1,
      ggLieSU3Fixed_isSubnormal_commutator hD hDBz hcomm⟩
  ·
    have hcomm : ⁅supportedBlock Q d h, supportedBlock Q d h⁆ ≤
        orthDerived Q ⊓ Subgroup.centralizer ({d} : Set (V ≃ₗ[K] V)) := by
      intro g hg
      have hg' := SmallOrthUn.commutator_supportedBlock_le (a := d) h hg
      exact Subgroup.mem_inf.mpr ⟨hg'.2, (Subgroup.mem_inf.mp hg'.1).2⟩
    exact ⟨d, by simp, h, hh, hX,
      ggLieSU3Fixed_isSubnormal_commutator hD hDBd hcomm⟩

end CFSG.StandardType
