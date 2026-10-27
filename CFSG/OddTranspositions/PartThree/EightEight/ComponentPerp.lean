module

public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.Timmesfeld.Bridge.Asc72Defs
public import CFSG.OddTranspositions.WreathBase
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.GroupTheory.PerfectCoreSolvableQuotient
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartThree.EightEight.Kernel
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
import CFSG.Timmesfeld.Bridge.Asc72WAct
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Open.QuasithinDefs
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Timmesfeld.Bridge.Asc72Lift
public import CFSG.Timmesfeld.Bridge.Asc72WreathL2
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.GroupTheory

theorem l2WreathBase_normal (f m : ℕ) : (l2WreathBase f m).Normal := by
  rw [l2WreathBase, SemidirectProduct.range_inl_eq_ker_rightHom]
  exact MonoidHom.normal_ker _

attribute [local instance] l2WreathBase_normal

noncomputable def quotient_l2WreathBase_mulEquiv (f m : ℕ) :
    L2Wreath f m ⧸ l2WreathBase f m ≃* Equiv.Perm (Fin m) := by
  have hker : (SemidirectProduct.rightHom : L2Wreath f m →* Equiv.Perm (Fin m)).ker =
      l2WreathBase f m := by
    rw [← SemidirectProduct.range_inl_eq_ker_rightHom]
    rfl
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ SemidirectProduct.rightHom_surjective)

theorem isSolvable_quotient_l2WreathBase {f m : ℕ} (hm4 : m ≤ 4) :
    Group.IsSolvable (L2Wreath f m ⧸ l2WreathBase f m) := by
  have : Group.IsSolvable (Equiv.Perm (Fin m)) :=
    Equiv.Perm.isSolvable (by simpa [Nat.card_fin] using hm4)
  exact Group.isSolvable_of_surjective
    (f := (quotient_l2WreathBase_mulEquiv f m).symm.toMonoidHom)
    (fun x => (quotient_l2WreathBase_mulEquiv f m).symm.surjective x)

theorem l2WreathBase_ne_bot {f m : ℕ} (hm : 1 ≤ m) : l2WreathBase f m ≠ ⊥ := by
  intro hbot
  obtain ⟨a, ha⟩ := exists_ne (1 : CFSG.Theory.Comparator.PSL2Model f)
  let i : Fin m := ⟨0, by omega⟩
  let k : Fin m → CFSG.Theory.Comparator.PSL2Model f := Pi.mulSingle i a
  have hk : (SemidirectProduct.inl k : L2Wreath f m) ∈ (l2WreathBase f m : Subgroup _) := by
    rw [l2WreathBase]
    exact ⟨k, rfl⟩
  rw [hbot] at hk
  have h1 : (SemidirectProduct.inl k : L2Wreath f m) = 1 := Subgroup.mem_bot.mp hk
  have h2 : k = 1 := SemidirectProduct.inl_injective (by simpa using h1)
  have h3 : a = 1 := by
    simpa [k, i, Pi.mulSingle_eq_same] using congrFun h2 i
  exact ha h3

section Generic

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem solvableRadical_le_normalizer_closure_DstarH (hC : HypothesisC D)
    (E : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))) :
    CFSG.solvableRadical (Halpha D hC.alpha) ≤
      Subgroup.normalizer ((Subgroup.closure {p | p ∈ DstarH hC ∧
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ∈ E} :
          Subgroup (Halpha D hC.alpha)) : Set (Halpha D hC.alpha)) := by
  let π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
  let T : Set (Halpha D hC.alpha) := {p | p ∈ DstarH hC ∧ π p ∈ E}
  have hTconj : ∀ m ∈ CFSG.solvableRadical (Halpha D hC.alpha), ∀ t ∈ T, m * t * m⁻¹ ∈ T := by
    intro m hm t ht
    refine ⟨DstarH_conj_mem hC ht.1, ?_⟩
    have h1 : π m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    show π (m * t * m⁻¹) ∈ E
    rw [map_mul, map_mul, map_inv, h1]
    simpa using ht.2
  have hconjX : ∀ m ∈ CFSG.solvableRadical (Halpha D hC.alpha), ∀ x ∈ Subgroup.closure T,
      m * x * m⁻¹ ∈ Subgroup.closure T := by
    intro m hm x hx
    have hmap : (Subgroup.closure T).map (MulAut.conj m).toMonoidHom ≤ Subgroup.closure T := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨t, ht, rfl⟩
      exact Subgroup.subset_closure (hTconj m hm t ht)
    exact hmap ⟨x, hx, rfl⟩
  intro m hm
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => hconjX m hm x hx, fun hx => ?_⟩
  have h := hconjX m⁻¹ (Subgroup.inv_mem _ hm) _ hx
  have he : m⁻¹ * (m * x * m⁻¹) * m⁻¹⁻¹ = x := by group
  rw [he] at h
  exact h

omit [Finite G] in
theorem comap_le_closure_DstarH_sup (hC : HypothesisC D)
    {J : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    {E : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hE : E ⊆ imageClass hC) (hJE : J ≤ Subgroup.closure E) :
    J.comap (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))) ≤
      Subgroup.closure {p | p ∈ DstarH hC ∧
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ∈ E} ⊔
      CFSG.solvableRadical (Halpha D hC.alpha) := by
  let π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
  let X : Subgroup (Halpha D hC.alpha) := Subgroup.closure {p | p ∈ DstarH hC ∧ π p ∈ E}
  have hEimg : E ⊆ π '' {p | p ∈ DstarH hC ∧ π p ∈ E} := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := hE hs
    exact ⟨p, ⟨hp, hs⟩, rfl⟩
  have hclE : Subgroup.closure E ≤ X.map π := by
    rw [MonoidHom.map_closure]
    exact Subgroup.closure_mono hEimg
  calc J.comap π ≤ (X.map π).comap π := Subgroup.comap_mono (hJE.trans hclE)
    _ = X ⊔ π.ker := Subgroup.comap_map_eq π X
    _ = X ⊔ CFSG.solvableRadical (Halpha D hC.alpha) := by rw [QuotientGroup.ker_mk']

theorem mem_union_DalphaStar_of_mem_normalizer_perfectCore (hC : HypothesisC D)
    (hZ : Subgroup.center G = ⊥)
    {J : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} [J.Normal]
    (hJperf : CFSG.Quasithin.perfectCore J ≠ ⊥) {d : G} (hd : d ∈ D)
    (hdK : d ∈ Subgroup.normalizer (((CFSG.Quasithin.perfectCore
      (J.comap (QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))))).map
        (Halpha D hC.alpha).subtype : Subgroup G) : Set G)) :
    d ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  let π := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
  let K : Subgroup (Halpha D hC.alpha) := CFSG.Quasithin.perfectCore (J.comap π)
  have hKmap : K.map π = CFSG.Quasithin.perfectCore J := by
    show (CFSG.Quasithin.perfectCore (J.comap π)).map π = _
    rw [CFSG.Quasithin.map_perfectCore,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  have hK1 : K ≠ ⊥ := by
    intro h
    apply hJperf
    rw [← hKmap, h, Subgroup.map_bot]
  have hKnormal : K.Normal := by
    have : (J.comap π).Normal := ‹J.Normal›.comap π
    have hN := CFSG.Quasithin.normalizer_le_normalizer_perfectCore (J.comap π)
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance] at hN
    exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hN)
  let KG : Subgroup G := K.map (Halpha D hC.alpha).subtype
  have hKG1 : KG ≠ ⊥ := by
    intro h
    exact hK1 ((Subgroup.map_eq_bot_iff_of_injective K (Halpha D hC.alpha).subtype_injective).mp h)
  have hKGr : ∀ k ∈ KG, Commute k hC.d := by
    rintro _ ⟨k, -, rfl⟩
    have hk : (k : G) ∈ Subgroup.centralizer hC.alpha := Halpha_le_centralizer D hC.alpha k.2
    exact ((Subgroup.mem_centralizer_iff.mp hk) hC.d hC.d_mem_alpha).symm
  have hHKG : Halpha D hC.alpha ≤ Subgroup.normalizer (KG : Set G) := by
    have hsub : (KG.subgroupOf (Halpha D hC.alpha)).Normal := by
      show ((K.map (Halpha D hC.alpha).subtype).comap (Halpha D hC.alpha).subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective (Halpha D hC.alpha).subtype_injective]
      exact hKnormal
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le K)).mp hsub
  exact inter_normalizer_subset_perp hC hZ (mem_blockClass_self hC.alpha) hC.d_mem_alpha hKG1
    hKGr hHKG ⟨hd, hdK⟩

theorem mem_union_DalphaStar_of_mem_normalizer_closure (hC : HypothesisC D)
    (hZ : Subgroup.center G = ⊥)
    {J : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))} [J.Normal]
    (hJperf : CFSG.Quasithin.perfectCore J ≠ ⊥)
    (hQ : Group.IsSolvable
      ((Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ⧸ J))
    {E : Set (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha))}
    (hE : E ⊆ imageClass hC) (hJE : J ≤ Subgroup.closure E) {d : G} (hd : d ∈ D)
    (hdX : d ∈ Subgroup.normalizer ((Subgroup.closure {p : G | ∃ hp : p ∈ Halpha D hC.alpha,
      p ∈ DalphaStar D hC.alpha ∧
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨p, hp⟩ ∈ E} :
          Subgroup G) : Set G)) :
    d ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  let M := CFSG.solvableRadical (Halpha D hC.alpha)
  let π := QuotientGroup.mk' M
  let X : Subgroup (Halpha D hC.alpha) := Subgroup.closure {p | p ∈ DstarH hC ∧ π p ∈ E}
  let P : Subgroup (Halpha D hC.alpha) := J.comap π
  have hPn : P.Normal := ‹J.Normal›.comap π
  have : (P.subgroupOf (X ⊔ M)).Normal := hPn.subgroupOf _
  let F : ↥(X ⊔ M) →* (Halpha D hC.alpha ⧸ M) ⧸ J :=
    (QuotientGroup.mk' J).comp (π.comp (X ⊔ M).subtype)
  have hFker : F.ker = P.subgroupOf (X ⊔ M) := by
    ext y
    change (QuotientGroup.mk' J) (π (y : Halpha D hC.alpha)) = 1 ↔ π (y : Halpha D hC.alpha) ∈ J
    exact QuotientGroup.eq_one_iff _
  have := hQ
  have : Group.IsSolvable ↥F.range := inferInstance
  have hsolv : Group.IsSolvable (↥(X ⊔ M) ⧸ F.ker) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (QuotientGroup.quotientKerEquivRange F).toMonoidHom)
      (QuotientGroup.quotientKerEquivRange F).injective
  have hquot : Group.IsSolvable (↥(X ⊔ M) ⧸ P.subgroupOf (X ⊔ M)) :=
    Group.isSolvable_of_surjective (f := (QuotientGroup.quotientMulEquivOfEq hFker).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hFker).surjective
  have hcoreEq : CFSG.Quasithin.perfectCore X = CFSG.Quasithin.perfectCore P :=
    perfectCore_eq_of_le_sup_of_isSolvable_quotient
      (solvableRadical_le_normalizer_closure_DstarH hC E) (comap_le_closure_DstarH_sup hC hE hJE)
      CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical hquot
  have hXeq : (Subgroup.closure {p : G | ∃ hp : p ∈ Halpha D hC.alpha,
      p ∈ DalphaStar D hC.alpha ∧
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) ⟨p, hp⟩ ∈ E} :
          Subgroup G) = X.map (Halpha D hC.alpha).subtype := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨hp, hpD, hπ⟩
      exact ⟨⟨x, hp⟩, ⟨hpD, hπ⟩, rfl⟩
    · rintro ⟨p, ⟨hpD, hπp⟩, rfl⟩
      exact ⟨p.2, hpD, hπp⟩
  have hdK := CFSG.Quasithin.normalizer_le_normalizer_perfectCore _ hdX
  rw [hXeq, ← CFSG.Quasithin.map_perfectCore, hcoreEq] at hdK
  exact mem_union_DalphaStar_of_mem_normalizer_perfectCore hC hZ hJperf hd hdK

end Generic

theorem mem_union_DalphaStar_of_mem_normalizer {G : Type} [Group G] [Finite G] {D : Set G}
    (hC : HypothesisC D) (hZ : Subgroup.center G = ⊥) {f m : ℕ} (hf : 2 ≤ f) (hm : 1 ≤ m)
    (hm4 : m ≤ 4)
    (φ : (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) ≃* L2Wreath f m)
    {E : Set (L2Wreath f m)} (hE : E ⊆ φ '' imageClass hC)
    (hB : (SemidirectProduct.inl.range : Subgroup (L2Wreath f m)) ≤ Subgroup.closure E)
    {d : G} (hd : d ∈ D)
    (hdX : d ∈ Subgroup.normalizer ((Subgroup.closure {p : G | ∃ hp : p ∈ Halpha D hC.alpha,
      p ∈ DalphaStar D hC.alpha ∧ φ (QuotientGroup.mk ⟨p, hp⟩) ∈ E} : Subgroup G) : Set G)) :
    d ∈ hC.alpha ∪ DalphaStar D hC.alpha := by
  let H := Halpha D hC.alpha
  let M := CFSG.solvableRadical H
  let B : Subgroup (L2Wreath f m) := l2WreathBase f m
  let J : Subgroup (H ⧸ M) := B.comap φ.toMonoidHom
  have hJn : J.Normal := (l2WreathBase_normal f m).comap φ.toMonoidHom
  have : Finite (L2Wreath f m) := WreathAct.finite_wreath
  have hBperf : ⁅B, B⁆ = B := CFSG.OddTranspositions.PartThree.commutator_l2WreathBase hf m
  have hBne : B ≠ ⊥ := l2WreathBase_ne_bot hm
  have hJpc : CFSG.Quasithin.perfectCore J ≠ ⊥ := by
    have hJmap : J.map φ.toMonoidHom = B :=
      Subgroup.map_comap_eq_self_of_surjective φ.surjective B
    have hmap : (CFSG.Quasithin.perfectCore J).map φ.toMonoidHom = B := by
      rw [CFSG.Quasithin.map_perfectCore, hJmap,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect hBperf]
    intro hbot
    rw [hbot, Subgroup.map_bot] at hmap
    exact hBne hmap.symm
  have hJs : Group.IsSolvable ((H ⧸ M) ⧸ J) := by
    let F : (H ⧸ M) →* (L2Wreath f m ⧸ l2WreathBase f m) :=
      (QuotientGroup.mk' (l2WreathBase f m)).comp φ.toMonoidHom
    have hFker : F.ker = J := by
      change ((QuotientGroup.mk' (l2WreathBase f m)).comp φ.toMonoidHom).ker = J
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    have hFsurj : Function.Surjective F :=
      (QuotientGroup.mk'_surjective (l2WreathBase f m)).comp φ.surjective
    let e : ((H ⧸ M) ⧸ J) ≃* (L2Wreath f m ⧸ l2WreathBase f m) :=
      (QuotientGroup.quotientMulEquivOfEq hFker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective F hFsurj)
    have : Group.IsSolvable (L2Wreath f m ⧸ l2WreathBase f m) :=
      isSolvable_quotient_l2WreathBase hm4
    exact Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hE' : (φ ⁻¹' E) ⊆ imageClass hC := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hE hx
    have hyx : y = x := φ.injective hxy
    rwa [hyx] at hy
  have hJE' : J ≤ Subgroup.closure (φ ⁻¹' E) := by
    have hEsub : E ⊆ φ '' (φ ⁻¹' E) := by
      intro e he
      exact ⟨φ.symm e, by simpa using he, φ.apply_symm_apply e⟩
    have hclE : Subgroup.closure E ≤ (Subgroup.closure (φ ⁻¹' E)).map φ.toMonoidHom := by
      rw [MonoidHom.map_closure]
      exact Subgroup.closure_mono hEsub
    have hBle : B ≤ (Subgroup.closure (φ ⁻¹' E)).map φ.toMonoidHom := hB.trans hclE
    have hJle : J ≤ ((Subgroup.closure (φ ⁻¹' E)).map φ.toMonoidHom).comap φ.toMonoidHom :=
      Subgroup.comap_mono hBle
    rwa [Subgroup.comap_map_eq_self_of_injective φ.injective] at hJle
  refine mem_union_DalphaStar_of_mem_normalizer_closure hC hZ hJpc hJs hE' hJE' hd ?_
  simpa [Set.mem_preimage, QuotientGroup.coe_mk'] using hdX

end CFSG.OddTranspositions.PartThree.EightEight
