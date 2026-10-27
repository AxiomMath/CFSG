module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcLift
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion
public import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.HardMathSupport.Solomon.Coordinator.B3FamPC
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma28
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
public import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
public import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
public import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
public import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
public import CFSG.LocalAnalysis.ComponentClassification.KProper
public import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
public import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.TopScalarLiftSquare
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma29Helpers

public section

namespace CFSG.StandardType

open CFSG.Assembly

private theorem isSolvable_quotient_of_le_range_sup {A Y : Type} [Group A] [Group Y]
    {f : A →* Y} {N : Subgroup Y} [N.Normal]
    (h : (⊤ : Subgroup Y) ≤ f.range ⊔ N) [Group.IsSolvable A] :
    Group.IsSolvable (Y ⧸ N) := by
  have hq : Function.Surjective ((QuotientGroup.mk' N).comp f) := by
    intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective N y
    have hy : y' ∈ f.range ⊔ N := h (Subgroup.mem_top y')
    obtain ⟨y₁, hy₁, n, hn, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := f.range) (t := N)).mp hy
    obtain ⟨a, rfl⟩ := hy₁
    refine ⟨a, ?_⟩
    change QuotientGroup.mk' N (f a) = QuotientGroup.mk' N (f a * n)
    rw [map_mul, show QuotientGroup.mk' N n = 1 by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hn, mul_one]
  exact Group.isSolvable_of_surjective (f := (QuotientGroup.mk' N).comp f) hq

section KV

variable {X : Type} [Group X] [Finite X] {V E K : Subgroup X}
  [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

private noncomputable abbrev ggRCSKVt (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] : Subgroup
    (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)) :=
  ((K ⊓ V).subgroupOf (E ⊔ K)).map
    (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))

private theorem ggRCSKVt_le_tt : ggRCSKVt (V := V) (E := E) (K := K) ≤ ggRCSTt V E K := by
  unfold ggRCSKVt ggRCSTt
  exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ le_sup_right)

private theorem ggRCS_sup_normalizes_inf (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) :
    E ⊔ (K ⊓ V) ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) := by
  have hVnorm : E ≤ Subgroup.normalizer (V : Set X) :=
    hEV.trans (Subgroup.le_normalizer : V ≤ Subgroup.normalizer (V : Set X))
  have hE : E ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf]
    exact and_congr ((Subgroup.mem_normalizer_iff.mp (hEK he) x))
      ((Subgroup.mem_normalizer_iff.mp (hVnorm he) x))
  exact sup_le hE Subgroup.le_normalizer

private theorem ggRCSKVt_normal (hEV : E ≤ V) (hEK : E ≤ Subgroup.normalizer (K : Set X)) :
    ((ggRCSKVt (V := V) (E := E) (K := K)).subgroupOf (ggRCSTt V E K)).Normal := by
  classical
  set W₀ := E ⊔ K with hW₀
  set π : ↥W₀ →* (↥W₀ ⧸ (ggRCSU V E K).subgroupOf W₀) :=
    QuotientGroup.mk' ((ggRCSU V E K).subgroupOf W₀) with hπ
  have hN : E ⊔ (K ⊓ V) ≤ Subgroup.normalizer ((K ⊓ V : Subgroup X) : Set X) :=
    ggRCS_sup_normalizes_inf hEV hEK
  rw [Subgroup.normal_subgroupOf_iff ggRCSKVt_le_tt]
  intro x t hx ht
  have hx' : x ∈ ((K ⊓ V).subgroupOf W₀).map π := hx
  obtain ⟨x₀, hx₀, rfl⟩ := Subgroup.mem_map.mp hx'
  have ht' : t ∈ ((E ⊔ (K ⊓ V)).subgroupOf W₀).map π := ht
  obtain ⟨t₀, ht₀, rfl⟩ := Subgroup.mem_map.mp ht'
  refine Subgroup.mem_map.mpr ⟨t₀ * x₀ * t₀⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf] at hx₀ ⊢
    exact (Subgroup.mem_normalizer_iff.mp
      (hN (Subgroup.mem_subgroupOf.mp ht₀)) x₀.1).mp hx₀
  · rw [map_mul, map_mul, map_inv]

end KV

section KVQuot

variable {X : Type} [Group X] [Finite X] {V E K : Subgroup X}
  [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

private theorem ggRCSKVt_quot_solvable (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X))
    [hN : ((ggRCSKVt V E K).subgroupOf (ggRCSTt V E K)).Normal] :
    Group.IsSolvable (↥(ggRCSTt V E K) ⧸
      (ggRCSKVt V E K).subgroupOf (ggRCSTt V E K)) := by
  classical
  set W₀ := E ⊔ K with hW₀
  set π : ↥W₀ →* (↥W₀ ⧸ (ggRCSU V E K).subgroupOf W₀) :=
    QuotientGroup.mk' ((ggRCSU V E K).subgroupOf W₀) with hπ
  have hEW₀ : E ≤ W₀ := le_sup_left
  have hKW₀ : K ⊓ V ≤ W₀ := inf_le_left.trans le_sup_right
  have hTsplit : ggRCSTt V E K = (E.subgroupOf W₀).map π ⊔ ggRCSKVt V E K := by
    unfold ggRCSTt ggRCSKVt
    rw [Subgroup.subgroupOf_sup hEW₀ hKW₀, Subgroup.map_sup]
  let f : ↥E →* ↥(ggRCSTt V E K) :=
    (π.comp (Subgroup.inclusion hEW₀)).codRestrict _ fun e => by
      rw [hTsplit]
      exact Subgroup.mem_sup_left
        (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr e.2))
  have hfrange : f.range = ((E.subgroupOf W₀).map π).subgroupOf (ggRCSTt V E K) := by
    ext x
    constructor
    · rintro ⟨e, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr
        (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr e.2))
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨e, he, hxe⟩ := Subgroup.mem_map.mp hx
      refine ⟨⟨e.1, Subgroup.mem_subgroupOf.mp he⟩, Subtype.ext ?_⟩
      exact hxe
  have hA_le : (E.subgroupOf W₀).map π ≤ ggRCSTt V E K := by
    rw [hTsplit]; exact le_sup_left
  have htop : (⊤ : Subgroup ↥(ggRCSTt V E K)) ≤
      f.range ⊔ (ggRCSKVt V E K).subgroupOf (ggRCSTt V E K) := by
    rw [hfrange, ← Subgroup.subgroupOf_sup hA_le ggRCSKVt_le_tt, hTsplit,
      Subgroup.subgroupOf_self]
  exact isSolvable_quotient_of_le_range_sup htop

private theorem ggRCS_perfect_le_kv (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X))
    {P : Subgroup (↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K))}
    (hPT : P ≤ ggRCSTt V E K) (hP : ⁅P, P⁆ = P) : P ≤ ggRCSKVt V E K := by
  haveI hN : ((ggRCSKVt V E K).subgroupOf (ggRCSTt V E K)).Normal :=
    ggRCSKVt_normal hEV hEK
  exact CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.perfect_le_of_solvable_quotient
    ggRCSKVt_le_tt (ggRCSKVt_quot_solvable hEs hEV hEK) hPT hP

private theorem ggRCS_hk_component_le_kv (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X))
    {C : Subgroup ↥(ggRCSHK V E K)} (hC : CFSG.Open.IsComponentOf C ⊤) :
    C.map (ggRCSHK V E K).subtype ≤ ggRCSKVt V E K := by
  have hLT : C.map (ggRCSHK V E K).subtype ≤ ggRCSTt V E K := by
    rintro y ⟨c, hc, rfl⟩
    exact (Subgroup.mem_inf.mp c.2).1
  have hLperf : ⁅C.map (ggRCSHK V E K).subtype, C.map (ggRCSHK V E K).subtype⁆ =
      C.map (ggRCSHK V E K).subtype := by
    rw [← Subgroup.map_commutator]
    congr 1
    exact Subgroup.isPerfect_iff.mp ⟨hC.2.2.1⟩
  exact ggRCS_perfect_le_kv hEs hEV hEK hLT hLperf

private theorem ggRCS_component_of_kv (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X))
    {C : Subgroup ↥(ggRCSHK V E K)} (hC : CFSG.Open.IsComponentOf C ⊤) :
    CFSG.Open.IsComponentOf
        ((C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)) ⊤ ∧
      Nonempty (↥((C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)) ⧸
          Subgroup.center
            ↥((C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)) ≃*
        ↥C ⧸ Subgroup.center ↥C) := by
  classical
  set L := C.map (ggRCSHK V E K).subtype with hL
  set L' := L.subgroupOf (ggRCSKVt V E K) with hL'
  have hle : L ≤ ggRCSKVt V E K := ggRCS_hk_component_le_kv hEs hEV hEK hC
  have hLq : CFSG.Open.IsQuasisimple ↥L :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (C.equivMapOfInjective (ggRCSHK V E K).subtype
        (ggRCSHK V E K).subtype_injective).symm hC.2.2
  have hL'q : CFSG.Open.IsQuasisimple ↥L' :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle) hLq
  have hHKmap :
      Subgroup.map (ggRCSHK V E K).subtype (⊤ : Subgroup ↥(ggRCSHK V E K)) =
        ggRCSHK V E K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact y.2
    · intro hx; exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
  have hLsubHK : CFSG.Open.IsSubnormal L (ggRCSHK V E K) := by
    have h := hC.2.1.map (ggRCSHK V E K).subtype
    rwa [hHKmap] at h
  have hLleHK : L ≤ ggRCSHK V E K := by
    rintro y ⟨c, hc, rfl⟩; exact c.2
  let Wbar := ↥(E ⊔ K) ⧸ (ggRCSU V E K).subgroupOf (E ⊔ K)
  haveI hFnorm : (CFSG.generalizedFitting Wbar).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := Wbar)).2
  have hHKinf : ggRCSHK V E K ⊓ ggRCSKVt V E K =
      CFSG.generalizedFitting Wbar ⊓ ggRCSKVt V E K := by
    change (ggRCSTt V E K ⊓ CFSG.generalizedFitting Wbar) ⊓ ggRCSKVt V E K =
      CFSG.generalizedFitting Wbar ⊓ ggRCSKVt V E K
    rw [inf_assoc, inf_eq_right.mpr (le_trans inf_le_right ggRCSKVt_le_tt)]
  have hHKinf_norm :
      ((ggRCSHK V E K ⊓ ggRCSKVt V E K).subgroupOf (ggRCSKVt V E K)).Normal := by
    rw [hHKinf, Subgroup.inf_subgroupOf_right]
    exact Subgroup.Normal.subgroupOf hFnorm (ggRCSKVt V E K)
  have hHKsub : CFSG.Open.IsSubnormal (ggRCSHK V E K ⊓ ggRCSKVt V E K)
      (ggRCSKVt V E K) := by
    rw [CFSG.Open.IsSubnormal.iff_subgroupOf (inf_le_right : _ ≤ ggRCSKVt V E K)]
    exact Subgroup.Normal.isSubnormal hHKinf_norm
  have hLsubHKinf : CFSG.Open.IsSubnormal L (ggRCSHK V E K ⊓ ggRCSKVt V E K) := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hLsubHK
      (inf_le_left : ggRCSHK V E K ⊓ ggRCSKVt V E K ≤ ggRCSHK V E K)
    rwa [inf_eq_left.mpr (le_inf hLleHK hle)] at h
  have hLsubKVt : CFSG.Open.IsSubnormal L (ggRCSKVt V E K) :=
    hLsubHKinf.trans hHKsub
  have hL'sub : CFSG.Open.IsSubnormal L' ⊤ := by
    have h : L'.IsSubnormal := (CFSG.Open.IsSubnormal.iff_subgroupOf hle).mp hLsubKVt
    exact CFSG.Open.IsSubnormal.of_mathlib h
  have hcomp : CFSG.Open.IsComponentOf L' ⊤ := ⟨le_top, hL'sub, hL'q⟩
  refine ⟨hcomp, ?_⟩
  let eC : ↥C ≃* ↥L :=
    C.equivMapOfInjective (ggRCSHK V E K).subtype
      (ggRCSHK V E K).subtype_injective
  let eL : ↥L ≃* ↥L' := (Subgroup.subgroupOfEquivOfLe hle).symm
  let e : ↥C ≃* ↥L' := eC.trans eL
  haveI : Group.IsPerfect ↥C := ⟨hC.2.2.1⟩
  have hker : e.toMonoidHom.ker ≤ Subgroup.center ↥C := by
    intro x hx
    have hx1 : x = 1 := e.injective (by simpa using hx)
    rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨iso⟩ := CFSG.LieType.ChevTwo.nonempty_quotCenter_equiv_of_surjective
    e.toMonoidHom e.surjective hker
  exact ⟨iso.symm⟩

end KVQuot

section Lift

variable {X : Type} [Group X] [Finite X]

private noncomputable def ggRCSphi (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    ↥((K ⊓ V).subgroupOf (E ⊔ K)) →* ↥(ggRCSKVt V E K) :=
  ((QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))).comp
    ((K ⊓ V).subgroupOf (E ⊔ K)).subtype).codRestrict
      (ggRCSKVt V E K) (fun a => Subgroup.mem_map_of_mem _ a.2)

private theorem ggRCSphi_surjective (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    Function.Surjective (ggRCSphi V E K) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨a, ha⟩, Subtype.ext rfl⟩

private theorem ggRCSphi_ker_le_center (V E K : Subgroup X)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    (ggRCSphi V E K).ker ≤ Subgroup.center ↥((K ⊓ V).subgroupOf (E ⊔ K)) := by
  intro a ha
  have h1 : (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))) a.1 = 1 := by
    have h2 := congrArg Subtype.val (MonoidHom.mem_ker.mp ha)
    simpa [ggRCSphi] using h2
  have haU : (a.1 : ↥(E ⊔ K)).1 ∈ ggRCSU V E K := by
    have h3 := (QuotientGroup.eq_one_iff (x := a.1)).mp h1
    exact Subgroup.mem_subgroupOf.mp h3
  rw [Subgroup.mem_center_iff]
  intro b
  apply Subtype.ext
  apply Subtype.ext
  have hbK : (b.1 : ↥(E ⊔ K)).1 ∈ K :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp b.2)).1
  have hcomm := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp haU).2
    (b.1 : ↥(E ⊔ K)).1 hbK
  simpa only [Subgroup.coe_mul] using hcomm

end Lift

section Main

variable {X : Type} [Group X] [Finite X] {V E K : Subgroup X}
  [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal]

theorem ggRCS_hk_componentInj_kv (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) :
    ∃ F : Subgroup ↥(ggRCSHK V E K) → Subgroup ↥(K ⊓ V),
      Set.InjOn F {C | CFSG.Open.IsComponentOf C ⊤} ∧
      ∀ C, CFSG.Open.IsComponentOf C ⊤ → CFSG.Open.IsComponentOf (F C) ⊤ ∧
        Nonempty (↥(F C) ⧸ Subgroup.center ↥(F C) ≃* ↥C ⧸ Subgroup.center ↥C) := by
  classical
  haveI hN : ((ggRCSKVt V E K).subgroupOf (ggRCSTt V E K)).Normal :=
    ggRCSKVt_normal hEV hEK
  let e : ↥((K ⊓ V).subgroupOf (E ⊔ K)) ≃* ↥(K ⊓ V) :=
    Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_right)
  let D : Subgroup ↥(ggRCSHK V E K) → Subgroup ↥((K ⊓ V).subgroupOf (E ⊔ K)) := fun C =>
    ⁅(((C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)).comap (ggRCSphi V E K)),
      (((C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)).comap
        (ggRCSphi V E K))⁆
  let F : Subgroup ↥(ggRCSHK V E K) → Subgroup ↥(K ⊓ V) := fun C =>
    (D C).map e.toMonoidHom
  refine ⟨F, ?_, ?_⟩
  ·
    intro C₁ hC₁ C₂ hC₂ hEq
    have hD : D C₁ = D C₂ := by
      have h := congrArg (Subgroup.map e.symm.toMonoidHom) hEq
      simpa [F, Subgroup.map_map] using h
    have hcomp₁ := (ggRCS_central_lift (ggRCSphi V E K) (ggRCSphi_surjective V E K)
      (ggRCSphi_ker_le_center V E K)
      (ggRCS_component_of_kv hEs hEV hEK hC₁).1).2.1
    have hcomp₂ := (ggRCS_central_lift (ggRCSphi V E K) (ggRCSphi_surjective V E K)
      (ggRCSphi_ker_le_center V E K)
      (ggRCS_component_of_kv hEs hEV hEK hC₂).1).2.1
    have hC' : ((C₁.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)) =
        ((C₂.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)) := by
      rw [← hcomp₁, ← hcomp₂]
      exact congrArg (Subgroup.map (ggRCSphi V E K)) hD
    have hle₁ : C₁.map (ggRCSHK V E K).subtype ≤ ggRCSKVt V E K :=
      ggRCS_hk_component_le_kv hEs hEV hEK hC₁
    have hle₂ : C₂.map (ggRCSHK V E K).subtype ≤ ggRCSKVt V E K :=
      ggRCS_hk_component_le_kv hEs hEV hEK hC₂
    have hmaps : C₁.map (ggRCSHK V E K).subtype = C₂.map (ggRCSHK V E K).subtype := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hle₁, ← Subgroup.map_subgroupOf_eq_of_le hle₂,
        hC']
    exact Subgroup.map_injective (ggRCSHK V E K).subtype_injective hmaps
  ·
    intro C hC
    have hC' := (ggRCS_component_of_kv hEs hEV hEK hC).1
    have hLift := ggRCS_central_lift (ggRCSphi V E K) (ggRCSphi_surjective V E K)
      (ggRCSphi_ker_le_center V E K) hC'
    have hDcomp : CFSG.Open.IsComponentOf (D C) ⊤ := hLift.1
    have hDF : CFSG.Open.IsComponentOf (F C) ⊤ := by
      have hsub := CFSG.Open.IsSubnormal.map e.toMonoidHom hDcomp.2.1
      rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hsub
      have hq : CFSG.Open.IsQuasisimple ↥(F C) :=
        CFSG.ComponentClassification.Components.quasisimple_of_equiv
          ((D C).equivMapOfInjective e.toMonoidHom e.injective).symm hDcomp.2.2
      exact ⟨le_top, hsub, hq⟩
    refine ⟨hDF, ?_⟩
    obtain ⟨iso₁⟩ := (ggRCS_component_of_kv hEs hEV hEK hC).2
    obtain ⟨iso₂⟩ := hLift.2.2
    let eD : ↥(D C) ≃* ↥(F C) :=
      (D C).equivMapOfInjective e.toMonoidHom e.injective
    haveI : Group.IsPerfect ↥(F C) := ⟨hDF.2.2.1⟩
    have hkerD : eD.symm.toMonoidHom.ker ≤ Subgroup.center ↥(F C) := by
      intro x hx
      have hx1 : x = 1 := eD.symm.injective (by simpa using hx)
      rw [hx1]
      exact Subgroup.one_mem _
    obtain ⟨iso₃⟩ := CFSG.LieType.ChevTwo.nonempty_quotCenter_equiv_of_surjective
      eD.symm.toMonoidHom eD.symm.surjective hkerD
    exact ⟨iso₃.trans (iso₂.trans iso₁)⟩

theorem ggRCS_hk_component_lift (hEs : Group.IsSolvable ↥E) (hEV : E ≤ V)
    (hEK : E ≤ Subgroup.normalizer (K : Set X)) {C : Subgroup ↥(ggRCSHK V E K)}
    (hC : CFSG.Open.IsComponentOf C ⊤) :
    ∃ D : Subgroup ↥(K ⊓ V), CFSG.Open.IsComponentOf D ⊤ ∧
      ((D.map (K ⊓ V).subtype).subgroupOf (E ⊔ K)).map
          (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))) =
        C.map (ggRCSHK V E K).subtype := by
  classical
  haveI hN : ((ggRCSKVt V E K).subgroupOf (ggRCSTt V E K)).Normal :=
    ggRCSKVt_normal hEV hEK
  let A := ↥((K ⊓ V).subgroupOf (E ⊔ K))
  let incl : A →* ↥(E ⊔ K) := ((K ⊓ V).subgroupOf (E ⊔ K)).subtype
  let inclX : A →* X := (E ⊔ K).subtype.comp incl
  let e : A ≃* ↥(K ⊓ V) :=
    Subgroup.subgroupOfEquivOfLe (inf_le_left.trans le_sup_right)
  let C' : Subgroup ↥(ggRCSKVt V E K) :=
    (C.map (ggRCSHK V E K).subtype).subgroupOf (ggRCSKVt V E K)
  have hC' : CFSG.Open.IsComponentOf C' ⊤ := (ggRCS_component_of_kv hEs hEV hEK hC).1
  let N : Subgroup A := ⁅C'.comap (ggRCSphi V E K), C'.comap (ggRCSphi V E K)⁆
  have hlift := ggRCS_central_lift (ggRCSphi V E K) (ggRCSphi_surjective V E K)
    (ggRCSphi_ker_le_center V E K) hC'
  have hN : CFSG.Open.IsComponentOf N ⊤ := hlift.1
  have hNmap : N.map (ggRCSphi V E K) = C' := hlift.2.1
  let D : Subgroup ↥(K ⊓ V) := N.map e.toMonoidHom
  have hD : CFSG.Open.IsComponentOf D ⊤ := by
    have hsub := hN.2.1.map e.toMonoidHom
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hsub
    have hq : CFSG.Open.IsQuasisimple ↥D :=
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (N.equivMapOfInjective e.toMonoidHom e.injective).symm hN.2.2
    exact ⟨le_top, hsub, hq⟩
  refine ⟨D, hD, ?_⟩
  have hle : C.map (ggRCSHK V E K).subtype ≤ ggRCSKVt V E K :=
    ggRCS_hk_component_le_kv hEs hEV hEK hC
  have hcomp_e : ((K ⊓ V).subtype.comp e.toMonoidHom) = inclX := by
    ext a
    rfl
  have hD_eq : D.map (K ⊓ V).subtype = N.map inclX := by
    rw [show D = N.map e.toMonoidHom from rfl, Subgroup.map_map, hcomp_e]
  have hH1 : N.map incl = (D.map (K ⊓ V).subtype).subgroupOf (E ⊔ K) := by
    rw [hD_eq]
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem inclX hn)
    · intro hx
      rw [Subgroup.mem_subgroupOf] at hx
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
      exact ⟨n, hn, Subtype.ext hnx⟩
  have hcomp : (ggRCSKVt V E K).subtype.comp (ggRCSphi V E K) =
      (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))).comp incl := by
    ext a
    rfl
  calc ((D.map (K ⊓ V).subtype).subgroupOf (E ⊔ K)).map
        (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)))
      = (N.map incl).map
          (QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))) := by rw [hH1]
    _ = N.map ((QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K))).comp incl) :=
        Subgroup.map_map N _ _
    _ = N.map ((ggRCSKVt V E K).subtype.comp (ggRCSphi V E K)) := by rw [hcomp]
    _ = (N.map (ggRCSphi V E K)).map (ggRCSKVt V E K).subtype :=
        (Subgroup.map_map N _ _).symm
    _ = C'.map (ggRCSKVt V E K).subtype := by rw [hNmap]
    _ = C.map (ggRCSHK V E K).subtype := Subgroup.map_subgroupOf_eq_of_le hle

end Main

end CFSG.StandardType
