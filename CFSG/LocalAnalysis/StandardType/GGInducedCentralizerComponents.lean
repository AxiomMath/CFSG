module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcSixEReduce
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NBase
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6SylowC
public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalBender
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6NotNormalLocal
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec6QuasiC
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
public import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.StandardType.LayerSixE

open CFSG.HardMathSupport.Solomon.Coordinator

variable {U C G : Type*} [Group U] [Group C] [Group G]
  {pi : U →* C} {psi : U →* G} {x : G} {alpha : MulAut C}

theorem GGInduces.map_centralizer_comap_le_fixSubgroup
    (h : GGInduces pi psi x alpha) :
    (((Subgroup.centralizer {x}).comap psi).map pi) ≤ fixSubgroup alpha := by
  rintro _ ⟨u, hu, rfl⟩
  have hc : psi u * x = x * psi u :=
    Subgroup.mem_centralizer_singleton_iff.mp hu
  have he : psi u = x * psi u * x⁻¹ := by
    rw [← hc]
    group
  exact (h u u he).symm

theorem GGInduces.normal_centralizer_comap (h : GGInduces pi psi x alpha)
    (hker : pi.ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G)) :
    (((Subgroup.centralizer {x}).comap psi).subgroupOf
      ((fixSubgroup alpha).comap pi)).Normal := by
  have hle : (Subgroup.centralizer {x}).comap psi ≤ (fixSubgroup alpha).comap pi :=
    Subgroup.map_le_iff_le_comap.mp h.map_centralizer_comap_le_fixSubgroup
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro u g hu hg
  obtain ⟨g', hg'⟩ := exists_conj_eq hx g
  have hpg : pi g' = pi g := (h g g' hg').trans hg
  have hk : g⁻¹ * g' ∈ Subgroup.center U := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpg, inv_mul_cancel])
  have hku : (g⁻¹ * g') * u * (g⁻¹ * g')⁻¹ = u := by
    rw [← Subgroup.mem_center_iff.mp hk u]
    group
  have hconj : g' * u * g'⁻¹ = g * u * g⁻¹ := by
    calc
      _ = g * ((g⁻¹ * g') * u * (g⁻¹ * g')⁻¹) * g⁻¹ := by group
      _ = _ := by rw [hku]
  have hucomm : psi u * x = x * psi u := Subgroup.mem_centralizer_singleton_iff.mp hu
  have hueq : x * psi u * x⁻¹ = psi u := by
    rw [← hucomm]
    group
  have heq : x * psi (g * u * g⁻¹) * x⁻¹ = psi (g * u * g⁻¹) := by
    calc
      _ = (x * psi g * x⁻¹) * (x * psi u * x⁻¹) * (x * psi g * x⁻¹)⁻¹ := by
        simp only [map_mul, map_inv]
        group
      _ = psi g' * psi u * (psi g')⁻¹ := by rw [← hg', hueq]
      _ = psi (g' * u * g'⁻¹) := by simp
      _ = _ := congrArg psi hconj
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc
    psi (g * u * g⁻¹) * x = (x * psi (g * u * g⁻¹) * x⁻¹) * x := by rw [heq]
    _ = x * psi (g * u * g⁻¹) := by group

theorem GGInduces.normal_map_centralizer_comap
    (h : GGInduces pi psi x alpha) (hpi : Function.Surjective pi)
    (hker : pi.ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G)) :
    ((((Subgroup.centralizer {x}).comap psi).map pi).subgroupOf
      (fixSubgroup alpha)).Normal := by
  have hle : (Subgroup.centralizer {x}).comap psi ≤ (fixSubgroup alpha).comap pi :=
    Subgroup.map_le_iff_le_comap.mp h.map_centralizer_comap_le_fixSubgroup
  have hnormal := (Subgroup.normal_subgroupOf_iff hle).mp (h.normal_centralizer_comap hker hx)
  rw [Subgroup.normal_subgroupOf_iff h.map_centralizer_comap_le_fixSubgroup]
  intro v c hv hc
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  obtain ⟨g, rfl⟩ := hpi c
  exact ⟨g * u * g⁻¹, hnormal u g hu hc, by simp⟩

theorem GGInduces.isComponentOf_centralizer_comap_fixSubgroup
    (h : GGInduces pi psi x alpha) (hker : pi.ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G)) {M : Subgroup U}
    (hM : CFSG.Open.IsComponentOf M ((Subgroup.centralizer {x}).comap psi)) :
    CFSG.Open.IsComponentOf M ((fixSubgroup alpha).comap pi) :=
  CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans hM
    (.step (Subgroup.map_le_iff_le_comap.mp h.map_centralizer_comap_le_fixSubgroup)
      (h.normal_centralizer_comap hker hx) (.refl _))

theorem GGInduces.isComponentOf_map_centralizer_lift
    {V H : Type*} [Group V] [Group H] (eta : U →* V) (heta : Function.Injective eta)
    (chi : V →* H) (hchi : chi.ker ≤ Subgroup.center V) (t : V)
    (h : GGInduces (chi.comp eta) psi x (MulAut.conj (chi t)))
    (hker : (chi.comp eta).ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G)) {M : Subgroup U}
    (hM : CFSG.Open.IsComponentOf M ((Subgroup.centralizer {x}).comap psi)) :
    CFSG.Open.IsComponentOf (M.map eta) (eta.range ⊓ Subgroup.centralizer {t}) := by
  have hMH := h.isComponentOf_centralizer_comap_fixSubgroup hker hx hM
  have hMK : M ≤ (Subgroup.centralizer {t}).comap eta := by
    have heq := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq chi hchi
      (show Group.IsPerfect ↥M from ⟨hM.2.2.1⟩)
      ((MulAut.conj t).toMonoidHom.comp (eta.comp M.subtype))
      (eta.comp M.subtype) (fun m => by
        have hm := hMH.1 m.2
        change chi t * chi (eta m) * (chi t)⁻¹ = chi (eta m) at hm
        change chi (t * eta (m : U) * t⁻¹) = chi (eta (m : U))
        simpa only [map_mul, map_inv] using hm)
    intro u hu
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have he := heq ⟨u, hu⟩
    change t * eta u * t⁻¹ = eta u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hKH : (Subgroup.centralizer {t}).comap eta ≤
      (fixSubgroup (MulAut.conj (chi t))).comap (chi.comp eta) := by
    intro u hu
    have hc : eta u * t = t * eta u := Subgroup.mem_centralizer_singleton_iff.mp hu
    have he : t * eta u * t⁻¹ = eta u := by rw [← hc]; group
    change chi t * chi (eta u) * (chi t)⁻¹ = chi (eta u)
    simpa only [map_mul, map_inv] using congrArg chi he
  have hMKcomp := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_of_le hMH hMK hKH
  have hmap := CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map eta
    (fun u hu => by
      have he : u = 1 := heta (hu.trans (map_one eta).symm)
      simpa only [he] using (Subgroup.center U).one_mem) hMKcomp
  rwa [Subgroup.map_comap_eq] at hmap

theorem GGInduces.isComponentOf_map_centralizer_comap
    (h : GGInduces pi psi x alpha) (hpi : Function.Surjective pi)
    (hker : pi.ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G))
    {M : Subgroup U} (hM : CFSG.Open.IsComponentOf M ((Subgroup.centralizer {x}).comap psi)) :
    CFSG.Open.IsComponentOf (M.map pi) (fixSubgroup alpha) := by
  apply CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_trans
    (CFSG.LocalAnalysis.GLTheoremA.I142N.isComponentOf_map pi
      (fun g hg => hker (MonoidHom.mem_ker.mpr hg)) hM)
  exact CFSG.Open.IsSubnormal.step h.map_centralizer_comap_le_fixSubgroup
    (h.normal_map_centralizer_comap hpi hker hx) (.refl _)

theorem GGInduces.eq_one_iff_mem_centralizer
    {U C : Type*} {G : Type} [Group U] [Group C] [Group G] [Group.IsPerfect U]
    {pi : U →* C} {psi : U →* G} {x : G} {alpha : MulAut C}
    (h : GGInduces pi psi x alpha) (hpi : Function.Surjective pi)
    (hker : pi.ker ≤ Subgroup.center U)
    (hx : x ∈ Subgroup.normalizer (psi.range : Set G)) :
    alpha = 1 ↔ x ∈ Subgroup.centralizer (psi.range : Set G) := by
  constructor
  · intro ha
    have hperfect : Group.IsPerfect psi.range := Group.IsPerfect.range (f := psi)
    apply CFSG.ComponentClassification.GMS78.mem_centralizer_of_commutator_mem_center
      (P := psi.range) (Subgroup.isPerfect_iff.mp hperfect) hx
    rintro _ ⟨u, rfl⟩ _ ⟨v, rfl⟩
    obtain ⟨u', hu⟩ := exists_conj_eq hx u
    have hp : pi u' = pi u := by simpa [ha] using h u u' hu
    have hz : u' * u⁻¹ ∈ Subgroup.center U := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp, mul_inv_cancel])
    have he : x * psi u * x⁻¹ * (psi u)⁻¹ = psi (u' * u⁻¹) := by
      rw [← hu, map_mul, map_inv]
    rw [he]
    simpa only [map_mul] using congrArg psi (Subgroup.mem_center_iff.mp hz v).symm
  · intro hc
    apply MulEquiv.ext
    intro c
    obtain ⟨u, rfl⟩ := hpi c
    have hcomm := Subgroup.mem_centralizer_iff.mp hc (psi u) ⟨u, rfl⟩
    have he : psi u = x * psi u * x⁻¹ := by
      rw [← hcomm]
      group
    exact (h u u he).symm

end CFSG.StandardType.LayerSixE
