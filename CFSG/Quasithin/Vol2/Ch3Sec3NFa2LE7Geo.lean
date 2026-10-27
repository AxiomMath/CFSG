module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2LE7Base
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2P9b
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSL
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Listed
public import CFSG.Quasithin.Background.A1GaschutzNorm
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Star
public import CFSG.Quasithin.Background.C124Z3Class
public import CFSG.Quasithin.Background.C129NativeMain
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.E6TwentyThreeC
public import CFSG.Quasithin.Background.F7TwoFix
public import CFSG.Quasithin.Background.F918H5
public import CFSG.Quasithin.Background.FLc2NZ
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.OperatorJordanHolder
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructFieldExt
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructPGL
public import CFSG.Quasithin.EmptyFaithful.Gold14610F618StructSimple
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4OvMaxBase
public import CFSG.Quasithin.EmptyFaithful.S14610Q1
public import CFSG.Quasithin.EmptyFaithful.S14610Top
public import CFSG.Quasithin.EmptyFaithful.S146F17
public import CFSG.Quasithin.EmptyFaithful.S146F20
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S146P1
public import CFSG.Quasithin.EmptyFaithful.S146P3
public import CFSG.Quasithin.EmptyFaithful.S146zClaim
public import CFSG.Quasithin.EmptyFaithful.S152He10A
public import CFSG.Quasithin.EmptyFaithful.S152He9N
public import CFSG.Quasithin.EmptyFaithful.S153E59A
public import CFSG.Quasithin.EmptyFaithful.S153H32
public import CFSG.Quasithin.EmptyFaithful.SzN15Top
public import CFSG.Quasithin.H13.A7Nat1236Insp
public import CFSG.Quasithin.H13.A7NatSL2
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Vol2.Ch12Sec1Lem1He
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountBoth
public import CFSG.Quasithin.Vol2.Ch3Sec3Case4CountRPf
public import CFSG.Quasithin.Vol2.Ch3Sec3InspF618Tools
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316Q
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3318E
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FE
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FEFix
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FF
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FH
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321FSD
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GPNF
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GT
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321StepsB
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
public import CFSG.Quasithin.Vol2.Ch3T325D
public import CFSG.Quasithin.Vol2.Ch3T325J
public import CFSG.Quasithin.Vol2.KGFactAutSylowSpor
public import CFSG.RankThree.CentralLiftU.UnitaryTriRoots
public import CFSG.RankThree.PartOne.KS.PKit
public import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.S10.PlaneContract
public import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
public import CFSG.RankThree.PartOne.S11d.OutSymplectic
public import CFSG.RankThree.PartOne.S11d.OutUnitary
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Blueprint
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF CFSG.Quasithin.H13.Ch3Sec3
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem CaseAFacts.exists_critPair_of_critical (facts : CaseAFacts G T M L D H K q)
    {γ : CosetGeom (a2G0 L K T) (a2G1 L T) (a2G2 K T)}
    (hγ : IsCriticalVertex (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) γ) :
    ∃ g : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g ∧
      g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T) = γ := by
  have hyp := facts.amalgam
  have hb3 := facts.b_three
  have hodd := facts.b_odd
  obtain ⟨⟨γ', hγ'nb, hd'⟩, -⟩ := exists_nbrs_of_geodesic hyp.gen hγ.geodesic (by omega : 2 ≤ _)
  have hvt : vtype γ = true := vtype_eq_true_of_odd hyp.gen (by rw [hγ.dist_eq]; exact hodd)
  have hadj : (graph (a2G0 L K T) (a2G1 L T) (a2G2 K T)).Adj γ γ' := SimpleGraph.Adj.symm hγ'nb
  obtain ⟨g, ⟨hg0, hg1⟩ | ⟨hg0, hg1⟩⟩ := exists_smul_edge hadj
  · exfalso
    have := congrArg vtype hg0
    rw [vtype_smul, vtype_γ₀, hvt] at this
    exact absurd this (by decide)
  · refine ⟨g, ⟨?_, ?_, ?_⟩, hg1⟩
    · rw [hg1]; exact hγ
    · rw [hg1, hg0]; exact hγ'nb
    · rw [hg0]; exact hd'

theorem CaseAFacts.exists_critPair (facts : CaseAFacts G T M L D H K q) :
    ∃ g : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g := by
  obtain ⟨γ, hγ⟩ := exists_isCriticalVertex facts.amalgam facts.V_ne
  obtain ⟨g, hg, -⟩ := facts.exists_critPair_of_critical hγ
  exact ⟨g, hg⟩

theorem CaseAFacts.VH_le_conj_R (facts : CaseAFacts G T M L D H K q)
    (hLS1 : a2G1 L T ⊓ a2G2 K T = H) {g : ↥(a2G0 L K T)}
    (hg : CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g) :
    conjClosure (a2V L T) (a2G2 K T) ≤ conjSub (g : G) (a2R H) := by
  have hyp := facts.amalgam
  have h := Vv_γ₁_le_pCoreOf_stab_inf hyp facts.V_ne hg.nbr hg.geodesic
  rw [Vv_γ₁ hyp.le₂ hyp.normalizes] at h
  have hst : stab (g • γ₀ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) ⊓
      stab (g • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) = conjSub (g : G) H := by
    rw [stab_smul, stab_smul, stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, ← conjSub_inf, hLS1]
  rw [hst, pCoreOf_conjSub] at h
  exact h

theorem CaseAFacts.exists_conj_le (facts : CaseAFacts G T M L D H K q)
    (hLS1 : a2G1 L T ⊓ a2G2 K T = H) {g : ↥(a2G0 L K T)}
    (hg : CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g) :
    conjSub (g : G) (conjClosure (a2V L T) (a2G2 K T)) ≤ a2G2 K T ∧
      ∃ c ∈ a2G2 K T, conjSub c (conjSub (g : G) (conjClosure (a2V L T) (a2G2 K T))) ≤ a2R H := by
  have hyp := facts.amalgam
  have hb3 := facts.b_three
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ := exists_nbrs_of_geodesic hyp.gen hg.critical.geodesic (by omega : 2 ≤ _)
  have h1 := Vv_le_pCoreOf_stab_inf hyp facts.V_ne hγ₂nb hd
  rw [Vv_smul hyp.normalizes, Vv_γ₁ hyp.le₂ hyp.normalizes] at h1
  refine ⟨?_, ?_⟩
  · have := h1.trans ((pCoreOf_le 2 _).trans inf_le_left)
    rwa [stab_γ₁ hyp.le₂] at this
  · obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
      (show γ₀ (a2G0 L K T) (a2G1 L T) (a2G2 K T) ∈
        nbrs (γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)) from (adj_γ₀_γ₁).symm)
    have hcG : (c : G) ∈ a2G2 K T := by rwa [stab_γ₁ hyp.le₂] at hc
    have hc1 : c • γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T) = γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T) :=
      smul_eq_of_mem_stab hc
    refine ⟨(c : G), hcG, ?_⟩
    have h2 := conjSub_mono (c : G) h1
    rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ, inf_comm,
      stab_γ₀ hyp.le₁, stab_γ₁ hyp.le₂, hLS1] at h2
    exact h2

theorem CaseAFacts.UH_le_VH (facts : CaseAFacts G T M L D H K q) :
    a2UH L T H K ≤ conjClosure (a2V L T) (a2G2 K T) := by
  have c := facts.cfg
  obtain ⟨-, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hVp : a2Vp L T H ≤ a2V L T :=
    commutator_le_left_of_le_normalizer'
      ((CFSG.Quasithin.oTwoUpper_le H).trans (c.nf.HLT.trans (sup_le hLV hTV)))
  exact conjClosure_mono hVp le_rfl

theorem E7Pair.Dγ_eq {Z U TC G2 R : Subgroup G} {g : G} (h : E7Pair Z U TC G2 R g) :
    centralizerMod Z (conjSub g U) U = conjSub g U ⊓ TC := by
  rw [← h.e5b]
  ext x
  constructor
  · rintro ⟨hxW, hxN, hx⟩
    exact ⟨hxW, h.W_le hxW, hxN, hx⟩
  · rintro ⟨hxW, hxG, hxN, hx⟩
    exact ⟨hxW, hxN, hx⟩

theorem mIdx_pos_of_lt' {X Y : Subgroup G} (hX : IsPGroup 2 X) (hlt : Y < X) : 0 < mIdx X Y := by
  have h1 := HypF98.relIndex_eq_two_pow_mIdx (Y := Y) hX
  rcases Nat.eq_zero_or_pos (mIdx X Y) with h0 | h0
  · exfalso
    rw [h0, pow_zero] at h1
    exact absurd (Subgroup.relIndex_eq_one.mp h1) (not_le_of_gt hlt)
  · exact h0

theorem lt_of_mIdx_pos {X Y : Subgroup G} (hYX : Y ≤ X) (hpos : 0 < mIdx X Y) : Y < X := by
  refine lt_of_le_of_ne hYX fun heq => ?_
  subst heq
  simp [mIdx] at hpos

theorem CaseAFacts.e7Pair (facts : CaseAFacts G T M L D H K q) (h36 : A36ForSQTK)
    (hLS1 : a2G1 L T ⊓ a2G2 K T = H) (hcard : Nat.card (a2Z T) = 2)
    {g : ↥(a2G0 L K T)} (hg : CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g)
    (hne : conjSub (g : G) (a2Z T) ≠ a2Z T) :
    E7Pair (a2Z T) (a2UH L T H K) (a2TC K T) (a2G2 K T) (a2R H) (g : G) := by
  have c := facts.cfg
  have hyp := facts.amalgam
  have hUV := facts.UH_le_VH
  have hVH : IsElemAbelian 2 (conjClosure (a2V L T) (a2G2 K T)) := by
    rw [← Vv_γ₁ hyp.le₂ hyp.normalizes]
    exact isElemAbelian_Vv_γ₁ hyp facts.V_ne (by have := facts.b_three; omega)
  have hVG2 : a2V L T ≤ a2G2 K T := facts.VTC.trans (pCoreOf_le 2 _)
  obtain ⟨-, hLV, hTV, -, -, -, -⟩ := L3321.setting_facts c.nf.hyp c.TL
  have hVp : a2Vp L T H ≤ a2V L T :=
    commutator_le_left_of_le_normalizer'
      ((CFSG.Quasithin.oTwoUpper_le H).trans (c.nf.HLT.trans (sup_le hLV hTV)))
  have hUG2 : a2UH L T H K ≤ a2G2 K T := by
    refine conjClosure_le fun k hk v hv => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk (hVG2 (hVp hv))) (Subgroup.inv_mem _ hk)
  obtain ⟨hWG, -⟩ := facts.exists_conj_le hLS1 hg
  have hUR : a2UH L T H K ≤ conjSub (g : G) (a2R H) := hUV.trans (facts.VH_le_conj_R hLS1 hg)
  exact ⟨hcard, hne, F7.isElemAbelian_mono hVH hUV, hUG2,
    (conjSub_mono (g : G) hUV).trans hWG, (pCoreOf_le 2 H).trans c.H_le_G2,
    c.G2_le_centralizer_Z h36, le_normalizer_conjClosure _ _, le_normalizer_pCoreOf 2 _,
    facts.e5a, facts.e5b, (le_conjSub_iff (g : G)).mp hUR⟩

local notation "γ₀'" => γ₀ (a2G0 L K T) (a2G1 L T) (a2G2 K T)
local notation "γ₁'" => γ₁ (a2G0 L K T) (a2G1 L T) (a2G2 K T)

theorem CaseAFacts.exists_symmetric (facts : CaseAFacts G T M L D H K q) (h36 : A36ForSQTK)
    (hLS1 : a2G1 L T ⊓ a2G2 K T = H) (hcard : Nat.card (a2Z T) = 2)
    {g : ↥(a2G0 L K T)} (hg : CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g)
    (hne : conjSub (g : G) (a2Z T) ≠ a2Z T)
    (hlt : centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K) <
      conjSub (g : G) (a2UH L T H K)) :
    ∃ k y : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) k ∧
      conjSub (k : G) (a2UH L T H K) = conjSub (y : G) (a2UH L T H K) ∧
      conjSub (y : G) (conjSub (g : G) (a2UH L T H K)) = a2UH L T H K ∧
      conjSub (k : G) (a2Z T) = conjSub (y : G) (a2Z T) ∧
      conjSub (y : G) (conjSub (g : G) (a2Z T)) = a2Z T := by
  have hyp := facts.amalgam
  have hV0 := facts.V_ne
  obtain ⟨-, he1⟩ := facts.e1
  have hP := facts.e7Pair h36 hLS1 hcard hg hne
  have hUV := facts.UH_le_VH
  have hTCeq : ballStab 1 γ₁' = a2TC K T := by
    rw [(ballStab_one_γ₁ hyp.gen).1, he1]
  have hVγ : Vv (a2V L T) (g • γ₁') =
      conjSub (g : G) (conjClosure (a2V L T) (a2G2 K T)) := by
    rw [Vv_smul hyp.normalizes, Vv_γ₁ hyp.le₂ hyp.normalizes]
  have hnot : ¬ Vv (a2V L T) (g • γ₁') ≤ ballStab 1 γ₁' := by
    intro hle
    rw [hVγ, hTCeq] at hle
    have hWTC : conjSub (g : G) (a2UH L T H K) ≤ a2TC K T := (conjSub_mono (g : G) hUV).trans hle
    apply hlt.ne
    rw [hP.Dγ_eq]
    exact inf_eq_left.mpr hWTC
  obtain ⟨β, hβ, hnl⟩ : ∃ β ∈ nbrs (g • γ₁'), ¬ Vv (a2V L T) β ≤ ballStab 1 γ₁' := by
    by_contra hall
    push Not at hall
    apply hnot
    rw [smul_γ₁, Vv_inr]
    refine iSup₂_le fun x hx => ?_
    exact hall (Sum.inl x) (by rw [smul_γ₁]; exact hx)
  have hvtγ : vtype (g • γ₁') = true := by rw [vtype_smul, vtype_γ₁]
  have hvtβ : vtype β = false := by
    have := vtype_ne_of_adj (show (graph (a2G0 L K T) (a2G1 L T) (a2G2 K T)).Adj (g • γ₁') β from hβ)
    rw [hvtγ] at this
    simpa using this.symm
  have hdβ : CosetGeom.dist β γ₁' = critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) := by
    obtain ⟨x₀, hx₀⟩ := exists_smul_eq_γ₀ hvtβ
    have hVβ : Vv (a2V L T) β = conjSub (x₀ : G) (a2V L T) := by
      rw [hx₀, Vv_smul_γ₀ hyp.normalizes]
    have hnl' : ¬ a2V L T ≤ ballStab 1 (x₀⁻¹ • γ₁') := by
      intro hle
      apply hnl
      rw [hVβ]
      have := conjSub_mono (x₀ : G) hle
      rwa [← ballStab_smul, smul_inv_smul] at this
    have hb : critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) ≤ CosetGeom.dist β γ₁' := by
      have hmem : CosetGeom.dist γ₀' (x₀⁻¹ • γ₁') ∈
          {n : ℕ | ∃ γ ∈ sphere n γ₀', ¬ a2V L T ≤ ballStab 1 γ} := ⟨x₀⁻¹ • γ₁', rfl, hnl'⟩
      have := (isLeast_critDist hyp hV0).2 hmem
      have hd := dist_smul x₀ γ₀' (x₀⁻¹ • γ₁')
      rw [smul_inv_smul, ← hx₀] at hd
      rw [← hd] at this
      exact this
    have hle : CosetGeom.dist β γ₁' ≤ critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) := by
      have t := dist_triangle hyp.gen β (g • γ₁') γ₁'
      have d1 : CosetGeom.dist β (g • γ₁') = 1 := by
        rw [CosetGeom.dist_comm]; exact dist_eq_one_iff_adj.mpr hβ
      have d2 : CosetGeom.dist (g • γ₁') γ₁' + 1 =
          critDist (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) := by
        rw [CosetGeom.dist_comm]; exact hg.critical.geodesic
      omega
    exact le_antisymm hle hb
  have hadj : (graph (a2G0 L K T) (a2G1 L T) (a2G2 K T)).Adj β (g • γ₁') := SimpleGraph.Adj.symm hβ
  obtain ⟨x, hx0, hx1⟩ : ∃ x : ↥(a2G0 L K T), x • γ₀' = β ∧ x • γ₁' = g • γ₁' := by
    obtain ⟨x, ⟨hx0, hx1⟩ | ⟨hx0, hx1⟩⟩ := exists_smul_edge hadj
    · exact ⟨x, hx0, hx1⟩
    · exfalso
      have := congrArg vtype hx0
      rw [vtype_smul, vtype_γ₀, hvtγ] at this
      exact absurd this (by decide)
  have hyγ : x⁻¹ • (g • γ₁') = γ₁' := by rw [← hx1, inv_smul_smul]
  have hcrit : IsCriticalVertex (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) (x⁻¹ • γ₁') := by
    refine ⟨?_, ?_, ?_⟩
    · have hd := dist_smul x γ₀' (x⁻¹ • γ₁')
      rw [hx0, smul_inv_smul] at hd
      exact hd.symm.trans hdβ
    · intro hle
      apply hnl
      rw [← hx0, Vv_smul_γ₀ hyp.normalizes]
      have := conjSub_mono (x : G) hle
      rwa [← ballStab_smul, smul_inv_smul] at this
    · have hd := dist_smul x γ₁' (x⁻¹ • γ₁')
      rw [hx1, smul_inv_smul] at hd
      have := hg.critical.geodesic
      rw [CosetGeom.dist_comm] at hd
      rw [← hd]
      exact this
  obtain ⟨k, hk, hk1⟩ := facts.exists_critPair_of_critical hcrit
  have hk₁ : (x : G)⁻¹ * (g : G) ∈ a2G2 K T := by
    have h1 : (x⁻¹ * g) • γ₁' = γ₁' := by rw [mul_smul, hyγ]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have hk₂ : (k : G)⁻¹ * (x : G)⁻¹ ∈ a2G2 K T := by
    have h1 : (k⁻¹ * x⁻¹) • γ₁' = γ₁' := by rw [mul_smul, ← hk1, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [stab_γ₁ hyp.le₂] at this
    simpa using this
  have hZN : a2G2 K T ≤ Subgroup.normalizer (a2Z T : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _ (hP.G2_cent hy)
  have hy : ((x⁻¹ : ↥(a2G0 L K T)) : G) = (x : G)⁻¹ := rfl
  have e : (x : G)⁻¹ = (k : G) * ((k : G)⁻¹ * (x : G)⁻¹) := by group
  refine ⟨k, x⁻¹, hk, ?_, ?_, ?_, ?_⟩
  · rw [hy, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hP.G2_normU hk₂)]
  · rw [hy, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hP.G2_normU hk₁)]
  · rw [hy, e, conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hZN hk₂)]
  · rw [hy, ← conjSub_mul, F7.conjSub_eq_of_mem_normalizer (hZN hk₁)]

theorem CaseAFacts.exists_reversed (facts : CaseAFacts G T M L D H K q) (h36 : A36ForSQTK)
    (hLS1 : a2G1 L T ⊓ a2G2 K T = H) (hcard : Nat.card (a2Z T) = 2)
    (e6ii : E6iiConcl L K T) {g : ↥(a2G0 L K T)}
    (hg : CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) g)
    (hlt : centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K) <
      conjSub (g : G) (a2UH L T H K)) :
    ∃ k : ↥(a2G0 L K T), CritPair (a2G0 L K T) (a2G1 L T) (a2G2 K T) (a2V L T) k ∧
      centralizerMod (a2Z T) (conjSub (k : G) (a2UH L T H K)) (a2UH L T H K) <
        conjSub (k : G) (a2UH L T H K) ∧
      mIdx (a2UH L T H K) (centralizerMod (conjSub (k : G) (a2Z T)) (a2UH L T H K)
          (conjSub (k : G) (a2UH L T H K))) ≤
        mIdx (conjSub (k : G) (a2UH L T H K))
          (centralizerMod (a2Z T) (conjSub (k : G) (a2UH L T H K)) (a2UH L T H K)) := by
  by_cases hc : mIdx (a2UH L T H K) (centralizerMod (conjSub (g : G) (a2Z T)) (a2UH L T H K)
      (conjSub (g : G) (a2UH L T H K))) ≤
      mIdx (conjSub (g : G) (a2UH L T H K))
        (centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K))
  · exact ⟨g, hg, hlt, hc⟩
  · obtain ⟨k, y, hk, eU, eB, eZ, eA⟩ :=
      facts.exists_symmetric h36 hLS1 hcard hg (e6ii g hg) hlt
    have hPg := facts.e7Pair h36 hLS1 hcard hg (e6ii g hg)
    have eDH : centralizerMod (conjSub (k : G) (a2Z T)) (a2UH L T H K)
        (conjSub (k : G) (a2UH L T H K)) =
        conjSub (y : G) (centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K))
          (a2UH L T H K)) := by
      rw [conjSub_centralizerMod, eB, eU, eZ]
    have eDγ : centralizerMod (a2Z T) (conjSub (k : G) (a2UH L T H K)) (a2UH L T H K) =
        conjSub (y : G) (centralizerMod (conjSub (g : G) (a2Z T)) (a2UH L T H K)
          (conjSub (g : G) (a2UH L T H K))) := by
      rw [conjSub_centralizerMod, eA, eB, ← eU]
    have m1 : mIdx (conjSub (k : G) (a2UH L T H K))
        (centralizerMod (a2Z T) (conjSub (k : G) (a2UH L T H K)) (a2UH L T H K)) =
        mIdx (a2UH L T H K) (centralizerMod (conjSub (g : G) (a2Z T)) (a2UH L T H K)
          (conjSub (g : G) (a2UH L T H K))) := by
      have := F9.mIdx_conjSub (y : G) (a2UH L T H K)
        (centralizerMod (conjSub (g : G) (a2Z T)) (a2UH L T H K) (conjSub (g : G) (a2UH L T H K)))
      rw [eDγ, eU]
      exact this
    have m2 : mIdx (a2UH L T H K) (centralizerMod (conjSub (k : G) (a2Z T)) (a2UH L T H K)
        (conjSub (k : G) (a2UH L T H K))) =
        mIdx (conjSub (g : G) (a2UH L T H K))
          (centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K)) := by
      have := F9.mIdx_conjSub (y : G) (conjSub (g : G) (a2UH L T H K))
        (centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K))
      rw [eB] at this
      rw [eDH]
      exact this
    have hWab : IsElemAbelian 2 (conjSub (g : G) (a2UH L T H K)) := F7.isElemAbelian_conjSub hPg.U_ab
    have hpos : 0 < mIdx (conjSub (g : G) (a2UH L T H K))
        (centralizerMod (a2Z T) (conjSub (g : G) (a2UH L T H K)) (a2UH L T H K)) :=
      mIdx_pos_of_lt' (F7.isPGroup_of_isElemAbelian hWab) hlt
    refine ⟨k, hk, ?_, ?_⟩
    · refine lt_of_mIdx_pos (centralizerMod_le_left _ _ _) ?_
      rw [m1]
      omega
    · rw [m2, m1]
      omega

end CFSG.Quasithin.H13.NFa2
