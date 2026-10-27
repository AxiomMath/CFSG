module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoJoinDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEsu
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSExcl
public import CFSG.LocalAnalysis.StandardType.GGQTwoFrameLDefs
import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsuAux
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGQTwoNativeGen
public import CFSG.LocalAnalysis.StandardType.GGNbrU63
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSLieEsu
import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicTransfer
import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteenP
import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAuxKb

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType
open CFSG.Assembly
open CFSG.Blueprint
open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open CFSG.LieType.Universal.Unitary
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem qTwoNbrG_kappa_ker {Q : Type} [Group Q] {K Bs Delta : Subgroup G}
    (q : ↥(K ⊔ Bs) →* Q) (hq : q.ker = Delta.subgroupOf (K ⊔ Bs))
    (hDelta_central : ∀ d ∈ Delta, ∀ k ∈ K, d * k = k * d) :
    (qTwoNbrRec_kappa q).ker ≤ Subgroup.center ↥K := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro w
  have hzq : q ⟨(z : G), (le_sup_left : K ≤ K ⊔ Bs) z.2⟩ = 1 := by
    have h1 := congrArg (fun y : ↥(qTwoNbrRec_Kb q) => (y : Q)) (MonoidHom.mem_ker.mp hz)
    rwa [qTwoNbrRec_kappa_coe, Subgroup.coe_one] at h1
  have hzΔ : (z : G) ∈ Delta := by
    have hmem : (⟨(z : G), (le_sup_left : K ≤ K ⊔ Bs) z.2⟩ : ↥(K ⊔ Bs)) ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      exact hzq
    rw [hq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  apply Subtype.ext
  exact (hDelta_central (z : G) hzΔ (w : G) w.2).symm

private theorem qTwoNbrG_map_kappa_range {Q : Type} [Group Q] {K Bs H : Subgroup G}
    (hH : H ≤ K) (q : ↥(K ⊔ Bs) →* Q) :
    (((H.subgroupOf K).map (qTwoNbrRec_kappa q)).map (qTwoNbrRec_Kb q).subtype) =
      ((q.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs))).comp
        (Subgroup.inclusion hH)).range := by
  rw [Subgroup.map_map]
  have hcomp : (qTwoNbrRec_Kb q).subtype.comp (qTwoNbrRec_kappa q) =
      q.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs)) := by
    ext k
    rfl
  rw [hcomp]
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.comp_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨⟨(k : G), hk⟩, ?_⟩
    exact congrArg q (Subtype.ext rfl)
  · rintro ⟨j, hj⟩
    refine ⟨⟨(j : G), hH j.2⟩, Subgroup.mem_subgroupOf.mpr j.2, ?_⟩
    rw [← hj]
    exact congrArg q (Subtype.ext rfl)

theorem qTwoNbr_comp_transport {p : ℕ} {B Bs L D J : Subgroup G} {x : G} {y : G}
    {K : Subgroup G} (hM : QTwoNbrModel p B Bs x L D J y K) :
    ggQTwoNbrCompProp hM := by
  letI := hM.groupQ
  have hf : Function.Surjective (qTwoNbrRec_kappa hM.q) := qTwoNbrRec_kappa_surjective hM.q
  have hker : (qTwoNbrRec_kappa hM.q).ker ≤ Subgroup.center ↥K :=
    qTwoNbrG_kappa_ker hM.q hM.hq_ker hM.hDelta_central
  have hxqAs : hM.q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩ ∈ hM.As := by
    rw [hM.hAs]
    exact MonoidHom.mem_range.mpr ⟨⟨x, hM.hxBs⟩, rfl⟩
  have hAsN : hM.As ≤ Subgroup.normalizer (qTwoNbrRec_Kb hM.q : Set hM.Q) := by
    intro b hb
    rw [hM.hAs] at hb
    obtain ⟨b0, rfl⟩ := MonoidHom.mem_range.mp hb
    exact qTwoNbrRec_mem_normalizer_Kb hM.q hM.hBsN b0.2
  let α : MulAut ↥K := ggGamma K hM.hBsN ⟨x, hM.hxBs⟩
  let β : MulAut ↥(qTwoNbrRec_Kb hM.q) :=
    ggGamma (qTwoNbrRec_Kb hM.q) hAsN
      ⟨hM.q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩, hxqAs⟩
  have hfixK : ggFix α = (K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K := by
    ext k
    rw [mem_ggFix, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      refine ⟨k.2, ?_⟩
      have h1 : ((α k : ↥K) : G) = (k : G) := congrArg Subtype.val h
      rw [ggGamma_coe] at h1
      calc (k : G) * x = (x * (k : G) * x⁻¹) * x := by rw [h1]
        _ = x * (k : G) := by group
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      rw [ggGamma_coe]
      calc x * (k : G) * x⁻¹ = (k : G) * x * x⁻¹ := by rw [← hc]
        _ = (k : G) := by group
  have hαβ : ∀ k : ↥K, qTwoNbrRec_kappa hM.q (α k) =
      β (qTwoNbrRec_kappa hM.q k) := by
    intro k
    apply Subtype.ext
    rw [qTwoNbrRec_kappa_coe]
    rw [show ((β (qTwoNbrRec_kappa hM.q k) : ↥(qTwoNbrRec_Kb hM.q)) : hM.Q) = _ from
      ggGamma_coe (qTwoNbrRec_Kb hM.q) hAsN
        ⟨hM.q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩, hxqAs⟩ (qTwoNbrRec_kappa hM.q k)]
    rw [qTwoNbrRec_kappa_coe]
    have h1 : ((α k : ↥K) : G) = x * (k : G) * x⁻¹ :=
      ggGamma_coe K hM.hBsN ⟨x, hM.hxBs⟩ k
    have harg : (⟨((α k : ↥K) : G),
          (le_sup_left : K ≤ K ⊔ Bs) (α k).2⟩ : ↥(K ⊔ Bs)) =
        (⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩ : ↥(K ⊔ Bs)) *
          (⟨(k : G), (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) *
          (⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩ : ↥(K ⊔ Bs))⁻¹ := by
      apply Subtype.ext
      rw [h1]
      rfl
    rw [harg, map_mul, map_mul, map_inv]
  have hcompK : IsComponentOf (J.subgroupOf K) (ggFix α) := by
    rw [hfixK]
    exact ggIsComponentOf_subgroupOf hM.hcomp inf_le_left
  have hJbar_sub : hM.Jbar =
      (((J.subgroupOf K).map (qTwoNbrRec_kappa hM.q)).map
        (qTwoNbrRec_Kb hM.q).subtype) := by
    rw [hM.hJbar, qTwoNbrG_map_kappa_range hM.hJK hM.q]
  have hCKbar_sub : hM.CKbar =
      ((((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K).map
        (qTwoNbrRec_kappa hM.q)).map (qTwoNbrRec_Kb hM.q).subtype) := by
    have hc : (hM.q.comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ Bs))).comp
          (Subgroup.inclusion inf_le_left) =
        hM.q.comp (Subgroup.inclusion
          (show K ⊓ Subgroup.centralizer ({x} : Set G) ≤ K ⊔ Bs from
            le_trans inf_le_left le_sup_left)) := by
      ext z
      apply congrArg hM.q
      exact Subtype.ext rfl
    rw [hM.hCKbar, ← hc, qTwoNbrG_map_kappa_range inf_le_left hM.q]
  have hggFix_sub : hM.Kbar ⊓ Subgroup.centralizer ({hM.xbar} : Set hM.Q) =
      (ggFix β).map (qTwoNbrRec_Kb hM.q).subtype := by
    rw [hM.hKbar, hM.hxbar]
    exact (map_ggFix_ggGamma (L := qTwoNbrRec_Kb hM.q) (hBN := hAsN)
      ⟨hM.q ⟨x, (le_sup_right : Bs ≤ K ⊔ Bs) hM.hxBs⟩, hxqAs⟩).symm
  have hcomm : ⁅ggFix β, ggFix β⁆ ≤
      (((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K).map
        (qTwoNbrRec_kappa hM.q)) := by
    have hcenter : ∀ z ∈ (ggFix β).comap (qTwoNbrRec_kappa hM.q),
        z⁻¹ * α z ∈ Subgroup.center ↥K :=
      fun z hz => hker (LayerCC.inv_mul_apply_mem_ker hαβ hz)
    have hcommK : ⁅(ggFix β).comap (qTwoNbrRec_kappa hM.q),
        (ggFix β).comap (qTwoNbrRec_kappa hM.q)⁆ ≤ ggFix α :=
      LayerCC.commutator_le_ggFix hcenter
    have h1 : (⁅(ggFix β).comap (qTwoNbrRec_kappa hM.q),
        (ggFix β).comap (qTwoNbrRec_kappa hM.q)⁆).map (qTwoNbrRec_kappa hM.q) ≤
        (ggFix α).map (qTwoNbrRec_kappa hM.q) := Subgroup.map_mono hcommK
    have h2 : (ggFix α).map (qTwoNbrRec_kappa hM.q) =
        (((K ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf K).map
          (qTwoNbrRec_kappa hM.q)) := by
      rw [hfixK]
    rwa [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hf, h2] at h1
  refine ⟨?_, ?_⟩
  · have hres := LayerCC.isComponentOf_map_ggFix hf hker hαβ hcompK
    have hresQ := isComponentOf_map_of_injective (qTwoNbrRec_Kb hM.q).subtype
      (qTwoNbrRec_Kb hM.q).subtype_injective hres
    rw [hJbar_sub, hggFix_sub]
    exact hresQ
  · rw [hggFix_sub, ← Subgroup.map_commutator, hCKbar_sub]
    exact Subgroup.map_mono hcomm

end CFSG.StandardType.QTwo

end
