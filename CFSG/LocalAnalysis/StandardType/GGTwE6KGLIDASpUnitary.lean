module

public import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDADefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks
import all CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SympInnerExport
import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenSymplecticNormalForm
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieCompAlgSymplectic
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDASpComp
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDASpFixed
import CFSG.LocalAnalysis.StandardType.GGTwE6KGLIDAUnitaryBridge
import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
import CFSG.GroupTheory.PCore.SubgroupCore
import CFSG.GroupTheory.SteinbergCBFTCores
import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossSp
import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOuterIdxSymplectic

public section

namespace CFSG.StandardType.SCFourCover

open Polynomial CFSG.Open CFSG.RankThree.Classical
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData sesqUnitaryGroup
  sesqSpecialUnitaryGroup sesqSpecialUnitaryGroup_le)
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie (sesqSUConj sesqSUConj_apply)

section Helpers

open CFSG.RankThree.PartOne.KCPrimary
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)

variable {r g : ℕ} {K : Type} [Field K]

private theorem charP_two_kglSpU [Finite K] (hK : Nat.card K = 2 ^ g) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (p := 2) (f := g) (by rw [Fintype.card_eq_nat_card, hK])

private theorem nontrivial_kglSpU {T : Type*} [Group T] (h : CFSG.Open.IsQuasisimple T) :
    Nontrivial T := by
  haveI := h.2
  exact (QuotientGroup.mk'_surjective (Subgroup.center T)).nontrivial

private theorem not_isSolvable_kglSpU {T : Type*} [Group T] (h : CFSG.Open.IsQuasisimple T) :
    ¬ Group.IsSolvable T := by
  haveI := nontrivial_kglSpU h
  haveI : Group.IsPerfect T := Group.isPerfect_def.mpr h.1
  exact Group.IsPerfect.not_isSolvable T

private theorem spSupported_eq_bot_kglSpU {x : StatedSp r K}
    (hsq : Squarefree (minpoly K (spEnd x))) {h : K[X]} (hh : h ∉ primaryFactors (spEnd x)) :
    spSupported x {h} = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  apply spLin_injective
  apply Units.ext
  rw [map_one]
  change spEnd u = 1
  refine ext_primaryComponent hsq (f := spEnd u) (g := 1) fun k hk v hv => ?_
  rw [Module.End.one_apply]
  refine (mem_spSupported.mp hu).2 k hk ?_ v hv
  rw [Set.mem_singleton_iff]
  rintro rfl
  exact hh hk

private theorem cyc_ne_kglSpU : (X ^ 2 + X + 1 : K[X]) ≠ X - 1 := fun e => by
  have h2 : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have h1 : (X - 1 : K[X]).natDegree = 1 := by compute_degree!
  rw [e, h1] at h2
  omega

private theorem ne_one_kglSpU (hr : 1 ≤ r) {x : StatedSp r K}
    (hh : (X ^ 2 + X + 1 : K[X]) ∈ primaryFactors (spEnd x)) : x ≠ 1 := by
  rintro rfl
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
  obtain ⟨hki, hkm, hkd⟩ := mem_primaryFactors.mp hh
  have h1 : spEnd (1 : StatedSp r K) = 1 := by simp [spEnd]
  rw [h1, minpoly.one] at hkd
  exact cyc_ne_kglSpU (eq_of_monic_of_associated hkm monic_X_sub_one
    (hki.associated_of_dvd irreducible_X_sub_one hkd))

private theorem reciprocal_cyc_kglSpU :
    reciprocalPolynomial (X ^ 2 + X + 1 : K[X]) = X ^ 2 + X + 1 := by
  have hd : (X ^ 2 + X + 1 : K[X]).natDegree = 2 := by compute_degree!
  have hX : reflect 2 (X : K[X]) = X := by
    rw [← pow_one (X : K[X]), reflect_monomial]
    rfl
  have h0 : (X ^ 2 + X + 1 : K[X]).coeff 0 = 1 := by simp
  have hrev : (X ^ 2 + X + 1 : K[X]).reverse = X ^ 2 + X + 1 := by
    rw [Polynomial.reverse, hd]
    simp [reflect_add, reflect_monomial, hX] <;> ring
  rw [reciprocalPolynomial, h0, hrev, inv_one, map_one, one_mul]

open CFSG.HardMathSupport.Solomon.Coordinator.LieComp in
private theorem range_su_kglSpU {G : Type*} [Group G] {ℓ f : ℕ} {E W : Type} [Field E]
    [AddCommGroup W] [Module E W] [FiniteDimensional E W] {hE : UnitaryFieldData ℓ f E}
    {Hf : W →ₛₗ[hE.bar] W →ₗ[E] E} (hHf : Hf.IsSymm) (hHfl : Hf.SeparatingLeft)
    {A : Subgroup G} (φ : A ≃* sesqUnitaryGroup Hf) (hns : ¬ Group.IsSolvable ↥⁅A, A⁆) :
    (A.subtype.comp (φ.symm.toMonoidHom.comp
      (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)))).range = ⁅A, A⁆ := by
  have hsU : ¬ Group.IsSolvable ↥(sesqUnitaryGroup Hf) := fun _ => by
    haveI : Group.IsSolvable ↥A :=
      Group.isSolvable_of_isSolvable_injective (f := φ.toMonoidHom) φ.injective
    exact hns (Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (Subgroup.commutator_le_self A)))
  by_cases hs : Module.finrank E W ≤ 1 ∨ ¬ ((Module.finrank E W = 2 → 4 ≤ ℓ ^ f) ∧
      (Module.finrank E W = 3 → 3 ≤ ℓ ^ f))
  · exact absurd (isSolvable_sesqUnitaryGroup_of_small hE hHf hHfl hs) hsU
  rw [not_or, not_le, not_not] at hs
  obtain ⟨hm, hq⟩ := hs
  have hperf := Group.isPerfect_def.mp
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le
      hE hHf hHfl (by omega) hq).1
  obtain ⟨-, -, -, -, hker, -⟩ :=
    CFSG.LinearGroups.unitary_full_group_order hE hHf hHfl rfl (by omega)
  refine range_comp_eq_commutator φ _ (range_eq_commutator_of_perfect _ hperf
    (CFSG.LinearGroups.unitaryDet Hf) fun u hu => ?_)
  rw [hker] at hu
  exact ⟨⟨u, hu⟩, Subtype.ext rfl⟩

end Helpers

theorem ggUnitaryOn_sp_unitary {r g : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) (hr : 2 ≤ r) {x y : StatedSp r K}
    (hx3 : x ^ 3 = 1) (hxy : Commute x y)
    (hT : CFSG.Open.IsComponentOf
      ((⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
      (fixSubgroup (MulAut.conj (proj r K x)))) :
    GGUnitaryOn ((⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K))
      (MulAut.conj (proj r K y)) := by
  classical
  haveI := charP_two_kglSpU hK
  haveI : NeZero r := ⟨by omega⟩
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := r) (K := K)
  have hg1 : 1 ≤ g := Nat.pos_of_ne_zero (by rintro rfl; norm_num at hg)
  have h3K : ((3 : ℕ) : K) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff K 2]
    norm_num
  have hns : ¬ Group.IsSolvable ↥⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆ :=
    fun _ => not_isSolvable_kglSpU hT.2.2
      (Group.isSolvable_of_surjective ((proj r K).subgroupMap_surjective _))
  have hh : (X ^ 2 + X + 1 : K[X]) ∈
      CFSG.RankThree.PartOne.KCPrimary.primaryFactors (spEnd x) := by
    by_contra hX
    apply (Subgroup.nontrivial_iff_ne_bot _).mp (nontrivial_kglSpU hT.2.2)
    rw [spSupported_eq_bot_kglSpU (altPrimaryData_spLin h3K hx3).squarefree hX,
      Subgroup.commutator_bot_left, Subgroup.map_bot]
  have hx1 := ne_one_kglSpU (by omega) hh
  have blocks := (symplectic_cross_prime_primary_centralizer_blocks Nat.prime_two hg1 hK
    Nat.prime_three (by norm_num) (by norm_num) (by omega) _ (orderOf_eq_prime
      (by rw [← map_pow, hx3, map_one]) fun h => hx1 (hπ.1 (h.trans (map_one _).symm)))).2 x rfl
    (orderOf_eq_prime hx3 hx1)
  let fac : CFSG.RankThree.PartOne.KCPrimary.primaryFactors (spEnd x) := ⟨X ^ 2 + X + 1, hh⟩
  haveI : Fact (Irreducible (fac : K[X])) :=
    ⟨(CFSG.RankThree.PartOne.KCPrimary.mem_primaryFactors.mp hh).1⟩
  obtain ⟨_, -, -, _, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, -⟩ :=
    (blocks.selfDual fac cyc_ne_kglSpU reciprocal_cyc_kglSpU).exists_half
  let ψ : ↥(sesqSpecialUnitaryGroup Hf) →* StatedSp r K :=
    (spSupported x {(fac : K[X])}).subtype.comp
      (φ.symm.toMonoidHom.comp (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)))
  have hψ : ψ.range = ⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆ :=
    range_su_kglSpU hHf hHfl φ hns
  have hψA : ∀ s, ψ s ∈ ⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆ :=
    fun s => by rw [← hψ]; exact ⟨s, rfl⟩
  let π' : ↥(sesqSpecialUnitaryGroup Hf) →*
      ↥((⁅spSupported x {X ^ 2 + X + 1}, spSupported x {X ^ 2 + X + 1}⁆).map (proj r K)) :=
    ((proj r K).subgroupMap _).comp (ψ.codRestrict _ hψA)
  have hπ'c : ∀ s, (π' s : StatedProj (StatedSp r K)) = proj r K (ψ s) := fun _ => rfl
  have hψ' : Function.Surjective (ψ.codRestrict _ hψA) := fun u => by
    obtain ⟨s, hs⟩ : (u : StatedSp r K) ∈ ψ.range := by rw [hψ]; exact u.2
    exact ⟨s, Subtype.ext hs⟩
  have hψi : Function.Injective ψ := Subtype.val_injective.comp (φ.symm.injective.comp
    (Subgroup.inclusion_injective (sesqSpecialUnitaryGroup_le Hf)))
  have hker : π'.ker ≤ Subgroup.center ↥(sesqSpecialUnitaryGroup Hf) := by
    rw [(MonoidHom.ker_eq_bot_iff π').mpr fun s t hst =>
      hψi (hπ.1 (by rw [← hπ'c, ← hπ'c, hst]))]
    exact bot_le
  have hO : ({X ^ 2 + X + 1} : Set K[X]) ∈ reciprocalOrbits (spEnd x) :=
    ⟨X ^ 2 + X + 1, hh, by dsimp only; rw [reciprocal_cyc_kglSpU, Set.pair_eq_singleton]⟩
  obtain ⟨y_h, hy_h, hy_hc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_mem_spSupported_commute_of_commute blocks
      hxy.symm ⟨_, hO⟩
  have hconj : ∀ s, MulAut.conj (proj r K y) (π' s : StatedProj (StatedSp r K)) =
      (π' (sesqSUConj (φ ⟨y_h, hy_h⟩) s) : StatedProj (StatedSp r K)) := by
    intro s
    have h1 : (φ.symm (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf)
          (sesqSUConj (φ ⟨y_h, hy_h⟩) s)) : ↥(spSupported x {(fac : K[X])})) =
        ⟨y_h, hy_h⟩ * φ.symm (Subgroup.inclusion (sesqSpecialUnitaryGroup_le Hf) s) *
          (⟨y_h, hy_h⟩ : ↥(spSupported x {(fac : K[X])}))⁻¹ := by
      apply φ.injective
      rw [MulEquiv.apply_symm_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_inclusion, sesqSUConj_apply]
      simp only [Subgroup.coe_inclusion, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
    have hc := hy_hc (ψ s) (Subgroup.commutator_le_self _ (hψA s))
    have key : y * ψ s * y⁻¹ = ψ (sesqSUConj (φ ⟨y_h, hy_h⟩) s) :=
      calc y * ψ s * y⁻¹ = y_h * ((y_h⁻¹ * y) * ψ s * (y_h⁻¹ * y)⁻¹) * y_h⁻¹ := by group
        _ = y_h * ψ s * y_h⁻¹ := by rw [hc.mul_inv_cancel]
        _ = ψ (sesqSUConj (φ ⟨y_h, hy_h⟩) s) := (congrArg Subtype.val h1).symm
    rw [MulAut.conj_apply, hπ'c, hπ'c, ← key, map_mul, map_mul, map_inv]
  exact ggUnitaryOn_of_sesqSUConj hT.2.2 hHf hHfl π' (((proj r K).subgroupMap_surjective _).comp
    hψ') hker (φ ⟨y_h, hy_h⟩) hconj

theorem ggInnerOrUnitaryOnComps_statedSp {r g : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ g) (hg : 3 ∣ 2 ^ g + 1) (hr : 2 ≤ r) :
    GGInnerOrUnitaryOnComps (StatedProj (StatedSp r K)) := by
  haveI := charP_two_kglSpU hK
  haveI : NeZero r := ⟨by omega⟩
  have hπ := CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.proj_bijective_of_charTwo
    (r := r) (K := K)
  intro a b ha3 ha1 hb3 hab J hJ _
  obtain ⟨x, rfl⟩ := hπ.2 a
  obtain ⟨y, rfl⟩ := hπ.2 b
  have hx3 : x ^ 3 = 1 := hπ.1 (show proj r K (x ^ 3) = proj r K 1 by rw [map_pow, ha3, map_one])
  have hy3 : y ^ 3 = 1 := hπ.1 (show proj r K (y ^ 3) = proj r K 1 by rw [map_pow, hb3, map_one])
  have hxy : Commute x y :=
    hπ.1 (show proj r K (x * y) = proj r K (y * x) by rw [map_mul, map_mul, hab])
  rcases sp_component_eq_fixed_or_unitary_of_odd hK hg hr hx3 ha1 J hJ with rfl | rfl
  · exact Or.inl (ggInnerOn_sp_fixed hK hr hx3 hy3 hxy hJ)
  · exact Or.inr (ggUnitaryOn_sp_unitary hK hg hr hx3 hxy hJ)

end CFSG.StandardType.SCFourCover

end
