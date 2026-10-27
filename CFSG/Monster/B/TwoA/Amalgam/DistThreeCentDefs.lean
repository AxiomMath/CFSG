module

public import CFSG.Monster.B.TwoA.Amalgam.DistThreeDefs
public import CFSG.Monster.B.TwoA.Amalgam.LocalLabelUnitary
public import CFSG.Monster.B.TwoA.Amalgam.DistTwo
public import CFSG.Monster.B.TwoA.Amalgam.Exact3510Core
public import CFSG.Monster.B.TwoA.Amalgam.OrderThreeTT
public import CFSG.Monster.B.E6.FieldInvF4
public import CFSG.Monster.B.E6.StdF4Degree
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3041
public import Certificates.Certificate3042
public import Certificates.Certificate3054
public import Certificates.Certificate3055
public import Certificates.Certificate3056
public import Certificates.Certificate3057
public import Certificates.Certificate3058
public import Certificates.Certificate3060
public import Certificates.Certificate3061
public import Certificates.Certificate3062
public import Certificates.Certificate3063
public import Certificates.Certificate3072
public import Certificates.Certificate3073
public import Certificates.Certificate3074
public import Certificates.Certificate3075
public import Certificates.Certificate3076
public import Certificates.Certificate3077
public import Certificates.Certificate3078
public import Certificates.Certificate3175
public import Certificates.Certificate16001
public import Certificates.Certificate16015
public import Certificates.Certificate16016
public import Certificates.Certificate16021
public import Certificates.Certificate16022
public import Certificates.Certificate16028
public import Certificates.Certificate16033
public import Certificates.Certificate16035
public import Certificates.Certificate16040
public import Certificates.Certificate3027
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate16951
public import CFSG.LieType.Chevalley.RootCommutatorCertificate
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.Monster.B.E6.StdF4Radical
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open CFSG.Monster.B.E6.StdF4 CFSG.Monster.B.E6.StdF4Radical CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley.C2E6Overlap

@[expose] def IsCompatLocal
    (v : CVert) (ρ : vStab v →* GStar)
    (iv : cgraph.neighborSet v ≃ rootClass) : Prop :=
  Function.Surjective ρ ∧
    (∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) ∧
    (∀ (y : vStab v) (z : cgraph.neighborSet v),
      SemidirectProduct.inl (iv (stabAct y z) : stdGroup) =
        (ρ y)⁻¹ * SemidirectProduct.inl (iv z : stdGroup) * ρ y) ∧
    (∀ z z' : cgraph.neighborSet v, z ≠ z' →
      (cgraph.Adj z z' ↔ Commute (iv z : stdGroup) (iv z'))) ∧
    ∀ (z : cgraph.neighborSet v) (y : vStab v), ((y : Shat) : Dfull) = clabel z →
      ρ y = SemidirectProduct.inl (iv z : stdGroup)

theorem exists_isCompatLocal
    (v : CVert) :
    ∃ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass), IsCompatLocal v ρ iv := by
  obtain ⟨ρ, iv, h1, h2, -, -, h5, h6, -, h8⟩ := native_local_label_root v
  exact ⟨ρ, iv, h1, h2, h5, h6, h8⟩

theorem IsCompatLocal.conj
    {v : CVert} {ρ : vStab v →* GStar}
    {iv : cgraph.neighborSet v ≃ rootClass} (h : IsCompatLocal v ρ iv) (g : stdGroup) :
    IsCompatLocal v (conjRho g ρ) (iv.trans (rootClassConj g)) := by
  obtain ⟨hsurj, hker, hcomp, hadj, hlab⟩ := h
  refine ⟨fun γ => ?_, fun y => ?_, fun y z => ?_, fun z z' hne => ?_, fun z y hy => ?_⟩
  · obtain ⟨y, hy⟩ := hsurj (SemidirectProduct.inl g * γ * (SemidirectProduct.inl g)⁻¹)
    refine ⟨y, ?_⟩
    rw [conjRho_apply, hy]
    group
  · rw [conjRho_apply, conj_inv_eq_one_iff]
    exact hker y
  · exact (inl_rootClassConj g _).trans ((congrArg (fun r => (SemidirectProduct.inl g)⁻¹ * r *
      SemidirectProduct.inl g) (hcomp y z)).trans ((conj_conj_eq _ _ _).trans
      (congrArg (fun r => (conjRho g ρ y)⁻¹ * r * conjRho g ρ y) (inl_rootClassConj g _).symm)))
  · exact (hadj z z' hne).trans (commute_conj_inv_iff g _ _).symm
  · exact (congrArg (fun r => (SemidirectProduct.inl g)⁻¹ * r * SemidirectProduct.inl g)
      (hlab z y hy)).trans (inl_rootClassConj g _).symm

@[expose] def jStar :
    Subgroup GStar := (groupJ.subgroupOf stdGroup).map SemidirectProduct.inl

theorem mem_jStar_iff
    (γ : GStar) :
    γ ∈ jStar ↔ γ.right = 1 ∧ ((γ.left : stdGroup) : ModGL Tag.E6 K) ∈ groupJ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨SemidirectProduct.right_inl x, by rw [SemidirectProduct.left_inl]; exact hx⟩
  · rintro ⟨h1, h2⟩
    refine ⟨γ.left, h2, ?_⟩
    conv_rhs => rw [← SemidirectProduct.inl_left_mul_inr_right γ, h1, map_one, mul_one]

theorem betaStarElt_not_mem_jStar :
    betaStarElt ∉ jStar := fun h =>
  betaG_ne_one (congrArg Subtype.val ((mem_jStar_iff _).1 h).1)

theorem commute_betaStarElt_of_mem_jStar
    {γ : GStar} (h : γ ∈ jStar) :
    Commute γ betaStarElt := by
  obtain ⟨x, hx, rfl⟩ := h
  exact (mem_groupJ_iff_commute x).1 hx

theorem mem_jStar_or_of_commute
    {γ : GStar} (h : Commute γ betaStarElt) :
    γ ∈ jStar ∨ γ * betaStarElt ∈ jStar := by
  have hγ : ((γ.left : stdGroup) : ModGL Tag.E6 K) ∈ groupJ := by
    have h1 : γ ∈ Subgroup.centralizer {betaStarElt} := Subgroup.mem_centralizer_singleton_iff.2 h
    rw [CFSG.Monster.B.E6.FieldInvF4.centralizer_betaStarElt,
      CFSG.Monster.B.E6.FieldInvF4.mem_starSub, Subgroup.mem_subgroupOf] at h1
    exact h1
  rcases mem_betaGroup_iff.1 γ.right.2 with hr | hr
  · exact Or.inl ((mem_jStar_iff γ).2 ⟨Subtype.ext hr, hγ⟩)
  · refine Or.inr ((mem_jStar_iff _).2 ⟨?_, ?_⟩)
    · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inr]
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, hr]
      exact betaG_mul_self
    · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inr, map_one, mul_one]
      exact hγ

theorem clabelS_mul_clabelS
    (v : CVert) : clabelS v * clabelS v = 1 := by
  rw [← sq, ← orderOf_clabelS v, pow_orderOf_eq_one]

theorem clabelS_mem_vStab_self
    (v : CVert) : clabelS v ∈ vStab v := by
  obtain ⟨-, -, -, -, hker, -⟩ := native_local_label_root v
  exact ((hker (clabelS v)).2 (by rw [coe_clabelS]; exact Subgroup.mem_zpowers _)).1

theorem fix_neighborSet_iff
    (v : CVert) (y : Shat) :
    (cvMul v y = v ∧ ∀ u ∈ cgraph.neighborSet v, cvMul u y = u) ↔
      (y : Dfull) ∈ Subgroup.zpowers (clabel v) := by
  obtain ⟨-, -, -, -, hker, -⟩ := native_local_label_root v
  exact hker y

@[expose] def cStab
    (v : CVert) : vStab v := ⟨clabelS v, clabelS_mem_vStab_self v⟩

theorem coe_cStab
    (v : CVert) : ((cStab v : vStab v) : Shat) = clabelS v := rfl

theorem orderOf_cStab
    (v : CVert) : orderOf (cStab v) = 2 := by
  rw [← Subgroup.orderOf_coe, coe_cStab, orderOf_clabelS]

theorem mem_zpowers_cStab_iff
    {v : CVert} (y : vStab v) :
    y ∈ Subgroup.zpowers (cStab v) ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v) := by
  rw [mem_zpowers_subtype_iff, mem_zpowers_subtype_iff]
  rfl

theorem commute_clabelS_of_mem_vStab
    {v : CVert} {y : Shat} (hy : y ∈ vStab v) :
    Commute y (clabelS v) := by
  have h := clabelS_cvMul v y
  rw [mem_vStab.1 hy] at h
  calc y * clabelS v = y * (y⁻¹ * clabelS v * y) := by rw [← h]
    _ = clabelS v * y := by group

theorem cStab_mem_center
    (v : CVert) : cStab v ∈ Subgroup.center (vStab v) := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact Subtype.ext (commute_clabelS_of_mem_vStab y.2)

theorem zpowers_cStab_le_center
    (v : CVert) :
    Subgroup.zpowers (cStab v) ≤ Subgroup.center (vStab v) :=
  (Subgroup.zpowers_le).2 (cStab_mem_center v)

theorem natCard_zpowers_cStab
    (v : CVert) : Nat.card (Subgroup.zpowers (cStab v)) = 2 := by
  rw [Nat.card_zpowers, orderOf_cStab]

theorem ker_eq_zpowers_cStab
    {v : CVert} {ρ : vStab v →* GStar}
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) :
    ρ.ker = Subgroup.zpowers (cStab v) := by
  ext y
  rw [MonoidHom.mem_ker, hker, mem_zpowers_cStab_iff]

theorem natCard_vStab_of_compat
    {v : CVert} {ρ : vStab v →* GStar} (hsurj : Function.Surjective ρ)
    (hker : ∀ y : vStab v, ρ y = 1 ↔ ((y : Shat) : Dfull) ∈ Subgroup.zpowers (clabel v)) :
    Nat.card (vStab v) = 306129918735099415756800 := by
  have h := Subgroup.card_ker_mul_card_of_surjective hsurj
  rw [ker_eq_zpowers_cStab hker, natCard_zpowers_cStab, card_GStar] at h
  rw [← h]

theorem ncard_inter_neighborSet_of_adj
    {w u : CVert} (h : cgraph.Adj w u) :
    (cgraph.neighborSet w ∩ cgraph.neighborSet u).ncard = 46134 := by
  obtain ⟨M, -⟩ := exists_rootModel w
  set p : cgraph.neighborSet w := ⟨u, h⟩
  have hiff : ∀ z : cgraph.neighborSet w, cgraph.Adj (z : CVert) u ↔
      (orbSize (M.pt p) (M.pt z) = repSize 1 ∨ orbSize (M.pt p) (M.pt z) = repSize 2) := by
    intro z
    change _ ↔ (orbSize (M.pt p) (M.pt z) = 1782 ∨ orbSize (M.pt p) (M.pt z) = 44352)
    rw [← commute_iff_orbSize (M.pt_mem p) (M.pt_mem z)]
    constructor
    · intro hz
      have hne : z ≠ p := by
        rintro rfl
        exact cgraph.ne_of_adj hz rfl
      exact ⟨((M.adj_iff_commute hne).1 hz).symm, fun e => hne (M.pt_injective e).symm⟩
    · rintro ⟨hc, hne⟩
      have hne' : z ≠ p := fun e => hne (by rw [e])
      exact (M.adj_iff_commute hne').2 hc.symm
  have e1 : cgraph.neighborSet w ∩ cgraph.neighborSet u =
      Subtype.val '' ({z : cgraph.neighborSet w | orbSize (M.pt p) (M.pt z) = repSize 1} ∪
        {z | orbSize (M.pt p) (M.pt z) = repSize 2}) := by
    ext x
    constructor
    · rintro ⟨hxw, hxu⟩
      exact ⟨⟨x, hxw⟩, (hiff ⟨x, hxw⟩).1 ((cgraph.mem_neighborSet u x).1 hxu).symm, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, (cgraph.mem_neighborSet u _).2 ((hiff z).2 hz).symm⟩
  have hdisj : Disjoint {z : cgraph.neighborSet w | orbSize (M.pt p) (M.pt z) = repSize 1}
      {z | orbSize (M.pt p) (M.pt z) = repSize 2} := by
    rw [Set.disjoint_left]
    intro z h1 h2
    have := h1.symm.trans h2
    exact absurd this (by decide)
  have hc : ∀ i : Fin 5,
      {z : cgraph.neighborSet w | orbSize (M.pt p) (M.pt z) = repSize i}.ncard = repSize i := by
    intro i
    rw [← Nat.card_coe_set_eq]
    exact M.natCard_orbSize_eq p i
  rw [e1, Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_union_eq hdisj, hc, hc]
  rfl

theorem dist_le_add_one_of_adj
    {v w z : CVert} (h : cgraph.Adj w z) :
    cgraph.dist v z ≤ cgraph.dist v w + 1 := by
  have h1 := cgraph_connected.dist_triangle (u := v) (v := w) (w := z)
  rwa [SimpleGraph.dist_eq_one_iff_adj.2 h] at h1

@[expose] def DistThreeLabelsInput :
    Prop :=
  ∀ v u : CVert, cgraph.dist v u = 3 →
    clabelS u ∈ vStab v ∧ clabelS v ∈ vStab u ∧ clabelS u ≠ clabelS v ∧
      Commute (clabelS u) (clabelS v)

@[expose] def DistThreeOuterInput :
    Prop :=
  ∀ v u : CVert, cgraph.dist v u = 3 →
    ∀ (ρ : vStab v →* GStar) (iv : cgraph.neighborSet v ≃ rootClass), IsCompatLocal v ρ iv →
      ∀ y : vStab v, (y : Shat) = clabelS u → (ρ y).right ≠ 1

@[expose] def DistThreePathInput :
    Prop :=
  (∀ v u u' : CVert, u ∈ sphereDistThree v → u' ∈ sphereDistThree v →
      ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u') ∧
    (∀ v w : CVert, w ∈ sphereFour v → (cgraph.neighborSet w ∩ sphereDistThree v).ncard = 8064) ∧
    ∀ v u : CVert, u ∈ sphereDistThree v → (xSet v u).Nonempty ∧
      (∀ w ∈ xSet v u, ∀ w' ∈ xSet v u,
        ∃ g : Shat, cvMul v g = v ∧ cvMul u g = u ∧ cvMul w g = w') ∧
      ∀ w ∈ xSet v u, Nat.card (vStab v ⊓ vStab u ⊓ vStab w : Subgroup Shat) = 3397386240

@[expose] def TypeThreeBoundInput :
    Prop :=
  ∀ v w u : CVert, w ∈ sphereThree v → cgraph.Adj w u → u ∉ sphereDistThree v

end CFSG.Monster.B.TwoA.Amalgam
