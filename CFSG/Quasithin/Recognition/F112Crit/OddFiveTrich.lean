module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrichBase
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrichLocal
public import CFSG.Quasithin.Recognition.F112Crit.BenderRigid
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Transport
public import CFSG.Quasithin.Recognition.F112Crit.APrime.ConcreteA
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.F6SolvableQuotient
public import CFSG.Quasithin.Background.F9Dual
public import CFSG.Quasithin.Background.F9Fourteen
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL1Large
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3FQuad
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3KGap
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RBase
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RLab
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Weak
public import CFSG.Quasithin.Background.GoldschmidtAmalgamSplit
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S152FinBasic
public import CFSG.Quasithin.EmptyFaithful.S152N2L14C
public import CFSG.Quasithin.EmptyFaithful.S152Stmts
public import CFSG.Quasithin.Recognition.F112TitsFrob
public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5TransvG
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁)

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "𝒱" => CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem trichConcl_base (hs : Setting L₁ L₂ S Z) (hS3 : VS3 L₁)
    (hK : IsRankOneListed (oTwoQuot ↥L₂)) (hns : ¬ Group.IsSolvable (oTwoQuot ↥L₂))
    {μ : 𝒱} (hμ : μ ∈ nbrs ν₁) (hne : μ ≠ ν₀) :
    TrichConcl ν₁ ν₀ (pCoreOf 2 (stab ν₁)) (pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab μ)) := by
  obtain ⟨n, i, hn, hK', htype⟩ := exists_isBenderQuot_of_listed hK hns
  have hC := isCartanQuot_of_listed hK hns
  have hR := isRigidQuot_of_listed hK hns
  have hV := hs.benderRigidVertex hK' hC hR
  have hA := APrime.amalgamS3_of_setting hs.hyp hS3 hs.S_le
  have hLoc := APrime.LocalS3.of_s3Point_γ₁ hA.hyp hA.s3Point_γ₁
  have hyp := hs.toCritAmalgam.amalgam
  have hδ : ν₁ ∈ nbrs ν₀ := CosetGeom.adj_γ₀_γ₁
  have h3 : (nbrs ν₁).ncard = 3 := (hLoc.point ν₁ CosetGeom.vtype_γ₁).ncard_nbrs
  have hcard : Nat.card (nbrs ν₀) = (2 ^ n) ^ i + 1 := hs.card_nbrs_γ₀ hK'
  have h5 : 5 ≤ (2 ^ n) ^ i + 1 := by
    rcases htype with ⟨rfl, -⟩ | h65
    · have h4 : 4 ≤ 2 ^ n :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
      simpa using h4
    · omega
  have h5' : 5 ≤ (nbrs ν₀).ncard := by
    rw [← Nat.card_coe_set_eq]
    omega
  have hdiff : 3 < (nbrs ν₀ \ {ν₁}).ncard := by
    rw [Set.ncard_sdiff_singleton_of_mem hδ]
    omega
  obtain ⟨ε₀, hε₀, ε₁, hε₁, ε₂, hε₂, h01, h02, h12⟩ :=
    (Set.two_lt_ncard (s := nbrs ν₀ \ {ν₁}) (Set.toFinite _)).1 (by omega)
  have h4 : ∃ ε₀ ∈ nbrs ν₀, ∃ ε₁ ∈ nbrs ν₀, ∃ ε₂ ∈ nbrs ν₀,
      ε₀ ≠ ν₁ ∧ ε₁ ≠ ν₁ ∧ ε₂ ≠ ν₁ ∧ ε₀ ≠ ε₁ ∧ ε₀ ≠ ε₂ ∧ ε₁ ≠ ε₂ :=
    ⟨ε₀, hε₀.1, ε₁, hε₁.1, ε₂, hε₂.1, hε₀.2, hε₁.2, hε₂.2, h01, h02, h12⟩
  have hU2 : IsPGroup 2 (S ⊓ oddGen L₂ : Subgroup G) := hs.hyp.hyp.h2.pgroup.to_le inf_le_left
  have hUν : S ⊓ oddGen L₂ ≤ stab ν₀ := inf_le_right.trans hV.bender.le_stab
  have hUδ : S ⊓ oddGen L₂ ≤ stab ν₁ := by
    rw [BenderLocalOf.stab_γ₁_eq hs]
    exact inf_le_left.trans (BenderLocalOf.S_le_bigB.trans BenderLocalOf.bigB_le_P₁)
  have hUtr : ∀ ε ∈ nbrs ν₀, ∀ ε' ∈ nbrs ν₀, ε ≠ ν₁ → ε' ≠ ν₁ →
      ∃ g : ↥(L₁ ⊔ L₂ ⊔ S), (g : G) ∈ S ⊓ oddGen L₂ ∧ g • ε = ε' :=
    fun ε hε ε' hε' hne hne' => BenderLocalOf.inf_oddGen_trans hK' hs hε hε' hne hne'
  have hUn : stab ν₀ ⊓ stab ν₁ ≤
      Subgroup.normalizer (((S ⊓ oddGen L₂) ⊔ ballStab 1 ν₀ : Subgroup G) : Set G) := by
    rw [BenderLocalOf.inf_oddGen_sup_ballStab hK' hs, BenderLocalOf.stab_γ₀_eq hs,
      BenderLocalOf.stab_γ₁_eq hs, F112W.inf_alpha_beta hs.hyp]
    exact BenderLocalOf.le_normalizer_inf_sup_ballStab hs
  have hQU : pCoreOf 2 (stab ν₁) ≤ (S ⊓ oddGen L₂) ⊔ ballStab 1 ν₀ :=
    le_sup_ballStab_of_rigidAt (hV.rigid.rigid ν₁ hδ) hV.cartan hδ hV.bender.le_stab
      hV.bender.normal inf_le_right hU2 hUδ hUtr hUn (pCoreOf_isPGroup 2 _)
      (le_inf (pCoreOf_stab_le_stab hyp hδ) (pCoreOf_le 2 _))
      (inf_le_right.trans (le_normalizer_pCoreOf 2 _))
  have hQS : pCoreOf 2 (stab ν₁) ≤ S := by
    rw [BenderLocalOf.stab_γ₁_eq hs]
    exact hA.pCoreOf_le_T
  have hrel : (pCoreOf 2 (stab ν₁)).relIndex S = 2 := by
    rw [BenderLocalOf.stab_γ₁_eq hs]
    exact hA.relIndex_pCoreOf_T
  have hidx2 : ((pCoreOf 2 (stab ν₁)).subgroupOf S).index = 2 := by
    rw [← Subgroup.relIndex_top_right, ← Subgroup.subgroupOf_self (H := S),
      Subgroup.relIndex_subgroupOf (H := pCoreOf 2 (stab ν₁)) (K := S) (L := S) le_rfl,
      hrel]
  have hidx : ∀ a ∈ S ⊓ oddGen L₂, ∀ b ∈ S ⊓ oddGen L₂,
      a ∉ pCoreOf 2 (stab ν₁) → b ∉ pCoreOf 2 (stab ν₁) →
      a⁻¹ * b ∈ pCoreOf 2 (stab ν₁) := by
    intro a ha b hb haQ hbQ
    have hA' : (⟨a, ha.1⟩ : ↥S) ∉ (pCoreOf 2 (stab ν₁)).subgroupOf S :=
      fun h => haQ (Subgroup.mem_subgroupOf.mp h)
    have hB' : (⟨b, hb.1⟩ : ↥S) ∉ (pCoreOf 2 (stab ν₁)).subgroupOf S :=
      fun h => hbQ (Subgroup.mem_subgroupOf.mp h)
    have hA'' : (⟨a, ha.1⟩ : ↥S)⁻¹ ∉ (pCoreOf 2 (stab ν₁)).subgroupOf S :=
      fun h' => hA' (by simpa using ((pCoreOf 2 (stab ν₁)).subgroupOf S).inv_mem h')
    have hmul : (⟨a, ha.1⟩ : ↥S)⁻¹ * ⟨b, hb.1⟩ ∈ (pCoreOf 2 (stab ν₁)).subgroupOf S := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx2]
      exact iff_of_false hA'' hB'
    simpa using Subgroup.mem_subgroupOf.mp hmul
  exact trichConcl_of_trichFor hyp (U := S ⊓ oddGen L₂) hδ hμ hne h3 hUν hUδ hUtr h4 hQU
    hidx (BenderLocalOf.trichFor_γ₁ hs hK' (isTrichQuot_of_listed hK hns))

theorem pCoreOf_inf_trichotomy (hs : Setting L₁ L₂ S Z)
    (hS3 : VS3 L₁) (hK : IsRankOneListed (oTwoQuot ↥L₂))
    (hns : ¬ Group.IsSolvable (oTwoQuot ↥L₂))
    {δ μ μ' : 𝒱} (hδ : vtype δ = true) (hμ : μ ∈ nbrs δ) (hμ' : μ' ∈ nbrs δ) (hne : μ ≠ μ') :
    pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ≤ ballStab 1 μ' ∨
    (∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ δ → ε' ≠ δ →
      ∃ r : ↥(L₁ ⊔ L₂ ⊔ S), (r : G) ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ∧ r • ε = ε') ∨
    ((∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), ∀ g ∈ pCoreOf 2 (stab δ),
        k * g * k⁻¹ * g⁻¹ ∈ ballStab 1 μ') ∧
      (∀ a ∈ pCoreOf 2 (stab δ), ∀ b ∈ pCoreOf 2 (stab δ),
        ∃ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ),
          k⁻¹ * (a * b * a⁻¹ * b⁻¹) ∈ ballStab 1 μ') ∧
      (∀ k ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ), k * k ∈ ballStab 1 μ') ∧
      ∃ a ∈ pCoreOf 2 (stab δ), ∃ b ∈ pCoreOf 2 (stab δ), a * b * a⁻¹ * b⁻¹ ∉ ballStab 1 μ') := by
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
  have hμ₁ : (graph _ _ _).Adj ν₁ (g⁻¹ • μ') := by
    have := (CosetGeom.smul_adj g⁻¹).mpr (show (graph _ _ _).Adj (g • ν₁) μ' from hμ')
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk₁, hkμ⟩ := CosetGeom.exists_stab_smul_eq hμ₁ CosetGeom.adj_γ₀_γ₁.symm
  set g' := g * k⁻¹ with hg'
  have hk₁' : k⁻¹ • ν₁ = ν₁ := inv_smul_eq_iff.mpr hk₁.symm
  have hg'₁ : g' • ν₁ = g • ν₁ := by rw [hg', mul_smul, hk₁']
  have hg'₀ : g' • ν₀ = μ' := by rw [hg', mul_smul, ← hkμ, inv_smul_smul, smul_inv_smul]
  have hμ₀ : g'⁻¹ • μ ∈ nbrs ν₁ := by
    have := (CosetGeom.smul_adj g'⁻¹).mpr (show (graph _ _ _).Adj (g • ν₁) μ from hμ)
    rwa [← hg'₁, inv_smul_smul] at this
  have hne₀ : g'⁻¹ • μ ≠ ν₀ := by
    intro e
    apply hne
    rw [← hg'₀, ← e, smul_inv_smul]
  have h := (hs.trichConcl_base hS3 hK hns hμ₀ hne₀).smul g'
  rw [hg'₁, hg'₀] at h
  have hQ : conjSub (g' : G) (pCoreOf 2 (stab ν₁)) = pCoreOf 2 (stab (g • ν₁)) := by
    rw [← pCoreOf_conjSub, ← CosetGeom.stab_smul, hg'₁]
  have hKK : conjSub (g' : G) (pCoreOf 2 (stab ν₁) ⊓ pCoreOf 2 (stab (g'⁻¹ • μ))) =
      pCoreOf 2 (stab (g • ν₁)) ⊓ pCoreOf 2 (stab μ) := by
    rw [conjSub_inf, hQ, ← pCoreOf_conjSub, ← CosetGeom.stab_smul, smul_inv_smul]
  rw [hQ, hKK] at h
  exact h

end Setting

end CFSG.Quasithin.F112Crit

end
