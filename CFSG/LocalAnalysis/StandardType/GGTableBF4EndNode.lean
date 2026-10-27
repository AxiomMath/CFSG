module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4Rank
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotToral
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotClassesC3Levi
public import CFSG.LieType.Chevalley.GraphFixedE6DiagonalCubes
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction.F4Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

local instance tableBF4NeZeroRank : NeZero Tag.F4.rank := ⟨by decide⟩

namespace TableBF4

section General

variable {G H : Type*} [Group G] [Group H]

@[expose] def EndNodeAt (A : Subgroup G) (t : G) : Prop :=
  t ∈ A ∧ t ≠ 1 ∧
    IsComponentOf (LargeEvenLayer (Subgroup.centralizer ({t} : Set G)))
      (Subgroup.centralizer ({t} : Set G)) ∧
    ∀ s ∈ A, ((∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set G)), s * j = j * s) ↔
      s ∈ Subgroup.zpowers t)

theorem EndNodeAt.map (e : G ≃* H) {A : Subgroup G} {t : G} (h : EndNodeAt A t) :
    EndNodeAt (A.map e.toMonoidHom) (e t) := by
  obtain ⟨htA, ht1, hcomp, hcent⟩ := h
  have hC : Subgroup.centralizer ({e t} : Set H) =
      (Subgroup.centralizer ({t} : Set G)).map e.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton e t).symm
  have hL : LargeEvenLayer (Subgroup.centralizer ({e t} : Set H)) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set G))).map e.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ e.injective]
  refine ⟨⟨t, htA, rfl⟩, fun h1 => ht1 (e.injective (by rw [h1, map_one])), ?_, ?_⟩
  · rw [hL, hC]
    exact isComponentOf_map_of_injective _ e.injective hcomp
  · rintro _ ⟨s, hs, rfl⟩
    rw [hL]
    constructor
    · intro hj
      have h2 : ∀ j ∈ LargeEvenLayer (Subgroup.centralizer ({t} : Set G)), s * j = j * s := by
        intro j hj'
        apply e.injective
        rw [map_mul, map_mul]
        exact hj (e j) ⟨j, hj', rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ((hcent s hs).mp h2)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_zpow, hk]
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hk' : t ^ k = s := e.injective (by rw [map_zpow]; exact hk)
      have h2 := (hcent s hs).mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩)
      rintro _ ⟨j, hj, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, h2 j hj]

theorem ggEndNodeElt_of_endNodeAt {G : Type} [Group G] {p r : ℕ} {V : Subgroup G} {t₀ : G}
    (hV : ∀ A : Subgroup G, IsElemAbelian p A → p ^ r ≤ Nat.card A →
      ∃ e : G ≃* G, A.map e.toMonoidHom = V)
    (h₀ : EndNodeAt V t₀) : GGEndNodeElt p r G := by
  intro A hA hr _
  obtain ⟨e, he⟩ := hV A hA hr
  have h1 := h₀.map e.symm
  have hA' : V.map e.symm.toMonoidHom = A := by
    rw [← he, Subgroup.map_map]
    convert Subgroup.map_id A
    ext g
    simp
  rw [hA'] at h1
  exact ⟨_, h1.1, h1.2⟩

end General

section F4

variable {K : Type} [Field K]

theorem commutator_mem_rootSpan_C3Set {x y : ModGL .F4 K}
    (hx : x ∈ torusLineR K ⊔ rootSpan .F4 K C3Set) (hy : y ∈ torusLineR K ⊔ rootSpan .F4 K C3Set) :
    x * y * x⁻¹ * y⁻¹ ∈ rootSpan .F4 K C3Set := by
  set T := torusLineR K with hT
  set D := rootSpan .F4 K C3Set with hD
  have hcomm : ∀ t ∈ T, ∀ d ∈ D, t * d = d * t := fun t ht d hd =>
    commute_of_mem_torusLineR_of_mem_rootSpan ht hd
  have hTT : ∀ t ∈ T, ∀ t' ∈ T, t * t' = t' * t := fun t ht t' ht' =>
    mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup (torusLineR_le_torusGroup ht))
      (torusGroup_le_diagonalGroup (torusLineR_le_torusGroup ht'))
  have hTN : T ≤ Subgroup.normalizer (D : Set (ModGL .F4 K)) := fun t ht =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun d hd => (hcomm t ht d hd).symm)
  have hsup : ((T ⊔ D : Subgroup (ModGL .F4 K)) : Set (ModGL .F4 K)) =
      (D : Set (ModGL .F4 K)) * (T : Set (ModGL .F4 K)) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left D T hTN
  have hx' : x ∈ (D : Set (ModGL .F4 K)) * (T : Set (ModGL .F4 K)) := by
    rw [← hsup]
    exact hx
  have hy' : y ∈ (D : Set (ModGL .F4 K)) * (T : Set (ModGL .F4 K)) := by
    rw [← hsup]
    exact hy
  obtain ⟨d, hd, t, ht, rfl⟩ := hx'
  obtain ⟨d', hd', t', ht', rfl⟩ := hy'
  have c1 := hcomm t ht d' hd'
  have c2 := hcomm t' ht' d⁻¹ (inv_mem hd)
  have c3 := hTT t ht t' ht'
  have e : d * t * (d' * t') * (d * t)⁻¹ * (d' * t')⁻¹ = d * d' * d⁻¹ * d'⁻¹ := by
    calc d * t * (d' * t') * (d * t)⁻¹ * (d' * t')⁻¹
        = d * (t * d') * t' * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by group
      _ = d * (d' * t) * t' * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by rw [c1]
      _ = d * d' * (t * t') * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by group
      _ = d * d' * (t' * t) * t⁻¹ * d⁻¹ * t'⁻¹ * d'⁻¹ := by rw [c3]
      _ = d * d' * (t' * d⁻¹) * t'⁻¹ * d'⁻¹ := by group
      _ = d * d' * (d⁻¹ * t') * t'⁻¹ * d'⁻¹ := by rw [c2]
      _ = d * d' * d⁻¹ * d'⁻¹ := by group
  rw [e]
  exact mul_mem (mul_mem (mul_mem hd hd') (inv_mem hd)) (inv_mem hd')

variable (K) in
@[expose] noncomputable def endNodeElt (ζ : Kˣ) : adjointGroup .F4 K :=
  ⟨rootDiagUnit .F4 (rDiag ζ), f4RootDiagUnit_mem_adjointGroup (rDiag ζ)⟩

theorem coe_endNodeElt (ζ : Kˣ) :
    (endNodeElt K ζ : ModGL .F4 K) = rootDiagUnit .F4 (rDiag ζ) :=
  rfl

theorem mem_centralizer_endNodeElt_iff {ζ : Kˣ} {g : adjointGroup .F4 K} :
    g ∈ Subgroup.centralizer ({endNodeElt K ζ} : Set (adjointGroup .F4 K)) ↔
      (g : ModGL .F4 K) ∈ toralCentralizer .F4 K (rDiag ζ) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    refine ⟨g.2, ?_⟩
    show (g : ModGL .F4 K) ∈ Subgroup.centralizer {rootDiagUnit .F4 (rDiag ζ)}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val h
  · rintro ⟨-, h⟩
    have h' : (g : ModGL .F4 K) ∈ Subgroup.centralizer {rootDiagUnit .F4 (rDiag ζ)} := h
    rw [Subgroup.mem_centralizer_singleton_iff] at h'
    exact Subtype.ext h'

theorem layer_centralizer_endNodeElt [Finite K] (hK : ringChar K = 2) {ζ : Kˣ}
    (hζ : 3 ≤ orderOf ζ) :
    LargeEvenLayer (Subgroup.centralizer ({endNodeElt K ζ} : Set (adjointGroup .F4 K))) =
        C3Levi K ∧
      IsComponentOf (C3Levi K)
        (Subgroup.centralizer ({endNodeElt K ζ} : Set (adjointGroup .F4 K))) := by
  have : CharP K 2 := ringChar.eq_iff.1 hK
  obtain ⟨hTD, -, -⟩ := toralCentralizer_rDiag_eq_sup hK hζ
  refine TableBSymp.largeEvenLayer_eq_of_commutator_mem ?_ ?_ isQuasisimple_C3Levi
  · intro d hd
    rw [C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf] at hd
    rw [mem_centralizer_endNodeElt_iff, hTD]
    exact Subgroup.mem_sup_right hd
  · intro g hg h hh
    rw [mem_centralizer_endNodeElt_iff, hTD] at hg hh
    rw [C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf]
    exact commutator_mem_rootSpan_C3Set hg hh

theorem rootChar_single_F4 (b : Fin Tag.F4.rank → Kˣ) (i : Fin Tag.F4.rank) :
    rootChar b (Pi.single i 1) = b i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

theorem endNodeAt_torusPow [Finite K] (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : Kˣ} (hζo : orderOf ζ = p) : EndNodeAt (torusPow K p) (endNodeElt K ζ) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hζ3 : 3 ≤ orderOf ζ := by
    rw [hζo]
    exact lt_of_le_of_ne hp.two_le (Ne.symm hp2)
  have hζp : ζ ^ p = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨hlay, hcomp⟩ := layer_centralizer_endNodeElt hK hζ3
  refine ⟨⟨f4RootDiagUnit_mem_torusGroup _, Subtype.ext ?_⟩, ?_, by rw [hlay]; exact hcomp, ?_⟩
  · rw [Subgroup.coe_pow, coe_endNodeElt, rootDiagUnit_pow, rDiag, ← Pi.mulSingle_pow, hζp,
      Pi.mulSingle_one, rootDiagUnit_one]
    rfl
  · intro h
    have h1 : rootDiagUnit .F4 (rDiag ζ) = 1 := by
      rw [← coe_endNodeElt, h]
      rfl
    have h2 : Commute (rootDiagUnit .F4 (rDiag ζ)) (pinnedX .F4 K rootR 1) := by
      rw [h1]
      exact Commute.one_left _
    have h3 := eq_one_of_commute_pinnedX_rootR hK h2
    rw [h3, orderOf_one] at hζo
    exact hp.one_lt.ne hζo
  · intro s hs
    rw [hlay]
    constructor
    · intro hcomm
      have hsV : (s : ModGL .F4 K) ∈ {h : ModGL .F4 K | h ∈ torusGroup .F4 K ∧ h ^ p = 1} :=
        ⟨hs.1, by rw [← Subgroup.coe_pow, hs.2, OneMemClass.coe_one]⟩
      obtain ⟨x, -, hx⟩ :=
        (CFSG.RankThree.Chevalley.F4_bijOn_rootDiagUnit_pow_val (k := K) hζo).2.2 hsV
      have hx' : rootDiagUnit .F4 (fun j => ζ ^ (x j).val) = (s : ModGL .F4 K) := hx
      have hxi : ∀ i : Fin Tag.F4.rank, i ≠ 0 → x i = 0 := by
        intro i hi
        have hγ : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ∈ c3LeviRoots :=
          mem_c3LeviRoots.2 ⟨isRoot_single .F4 i, by
            rw [Pi.single_apply, ite_eq_right_iff]
            exact fun h => absurd h.symm hi⟩
        have hc := hcomm _ (pinnedX_mem_C3Levi hγ 1)
        have hc' : (s : ModGL .F4 K) * pinnedX .F4 K (Pi.single i 1) 1 =
            pinnedX .F4 K (Pi.single i 1) 1 * (s : ModGL .F4 K) := congrArg Subtype.val hc
        have hconj := rootDiagUnit_conj_pinnedX (fun j => ζ ^ (x j).val) (isRoot_single .F4 i)
          (1 : K)
        rw [hx', hc', mul_inv_cancel_right, mul_one, rootChar_single_F4] at hconj
        have h4 := pinnedX_injective .F4 K (Pi.single i 1) hconj
        have h5 : ζ ^ (x i).val = 1 := Units.ext (by rw [Units.val_one]; exact h4.symm)
        have h6 := orderOf_dvd_of_pow_eq_one h5
        rw [hζo] at h6
        exact (ZMod.val_eq_zero _).mp (Nat.eq_zero_of_dvd_of_lt h6 (ZMod.val_lt _))
      have hb : (fun j => ζ ^ (x j).val) = rDiag (ζ ^ (x 0).val) := by
        funext j
        by_cases hj : j = 0
        · subst hj
          rw [rDiag, Pi.mulSingle_eq_same]
        · rw [rDiag, Pi.mulSingle_eq_of_ne hj, hxi j hj, ZMod.val_zero, pow_zero]
      refine Subgroup.mem_zpowers_iff.mpr ⟨((x 0).val : ℤ), Subtype.ext ?_⟩
      rw [zpow_natCast, Subgroup.coe_pow, coe_endNodeElt, ← hx', hb, rootDiagUnit_pow, rDiag,
        rDiag, ← Pi.mulSingle_pow]
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      rw [C3Levi_eq_subgroupOf_rootSpan_C3Set, Subgroup.mem_subgroupOf] at hj
      have ht : ((endNodeElt K ζ ^ k : adjointGroup .F4 K) : ModGL .F4 K) ∈ torusLineR K := by
        rw [Subgroup.coe_zpow]
        exact zpow_mem (mem_torusLineR.2 ⟨ζ, rfl⟩) k
      exact Subtype.ext (commute_of_mem_torusLineR_of_mem_rootSpan ht hj).eq

theorem ggEndNodeElt_adjointF4_of_input [Finite K] (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hT : GGF4ToralRankInput K p) :
    GGEndNodeElt p 4 (adjointGroup .F4 K) := by
  have := Fact.mk hp
  obtain ⟨ζ, hζo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := K) hpq
  refine ggEndNodeElt_of_endNodeAt (V := torusPow K p) (fun A hA hr => ?_)
    (endNodeAt_torusPow hK hp hp2 hζo)
  obtain ⟨g, hg⟩ := hT A hA hr
  exact ⟨MulAut.conj g, hg⟩

theorem ggEndNode_F4_of_input [Finite K] (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hT : GGF4ToralRankInput K p) :
    GGEndNode p 4 (RecipeGroup K) (RecipeID K) :=
  ggEndNode_of_elt (idImage_subset_inn K) (center_recipeGroup_eq_bot K)
    (ggEndNodeElt_of_mulEquiv (recipeEquiv K)
      (ggEndNodeElt_adjointF4_of_input hK hp hp2 hpq hT))

theorem ggEndNode_F4 [Finite K] (hK : ringChar K = 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) : GGEndNode p 4 (RecipeGroup K) (RecipeID K) :=
  ggEndNode_F4_of_input hK hp (by omega) hpq (ggF4ToralRankInput_of_five_le hp hp5 hpq)

end F4

end TableBF4

end CFSG.StandardType
