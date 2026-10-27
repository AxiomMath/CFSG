module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveQ
public import CFSG.Quasithin.Recognition.F112Crit.OddFivePush
public import CFSG.Quasithin.Recognition.F112Crit.Theorem75
public import CFSG.Quasithin.Recognition.F112Crit.APrime.Lemma758One
public import CFSG.Quasithin.Recognition.F112Crit.APrime.S3Gamma1
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
open Subgroup

open CosetGeom (graph stab ballStab nbrs vtype γ₀ γ₁ Vv)

section Crit

variable {G : Type} [Group G] [Finite G] {G₀ G₁ G₂ T Z : Subgroup G}

theorem CritConfig.not_pCoreOf_le_ballStab (hc : CritAmalgam G₀ G₁ G₂ T Z)
    {α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂} (h : CritConfig Z α α₁ α' α₂ α₃) :
    ¬ pCoreOf 2 (stab α₂) ≤ ballStab 1 α₁ := by
  intro hle
  apply h.not_le
  have hV' : Vv Z α' ≤ centralizer (Vv Z α₁ : Set G) :=
    h.push₂.trans (hle.trans (ballStab_le_centralizer_Vv hc h.vα₁))
  have hV1 : Vv Z α₁ ≤ centralizer (Vv Z α' : Set G) := le_centralizer_iff.mp hV'
  have hV1' : Vv Z α₁ ≤ ballStab 1 α' := by
    rw [← lemma73_1 hc h.vα']
    exact le_inf ((h.vOne_le hc).trans inf_le_left) hV1
  exact (Vv_le_Vv_of_mem_nbrs h.vα₁ h.adj₁).trans hV1'

theorem not_pCoreOf_stab_γ₀_le_ballStab (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (hb : Odd (critB G₀ G₁ G₂ Z)) :
    ¬ pCoreOf 2 (stab (γ₀ G₀ G₁ G₂)) ≤ ballStab 1 (γ₁ G₀ G₁ G₂) := by
  obtain ⟨α, α₁, α', α₂, α₃, h⟩ := exists_critConfig hc hb
  have hα₂ : vtype α₂ = false := vtype_eq_false_of_mem_nbrs h.vα₁ h.adj₂
  obtain ⟨g, hg0, hg1⟩ := exists_edge_conj hα₂ (CosetGeom.mem_nbrs_symm h.adj₂)
  have h' := (h.smul hc g⁻¹).not_pCoreOf_le_ballStab hc
  rwa [hg0, hg1, inv_smul_smul, inv_smul_smul] at h'

theorem not_pCoreOf_le_pCoreOf_of_odd (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (hb : Odd (critB G₀ G₁ G₂ Z)) : ¬ pCoreOf 2 G₁ ≤ pCoreOf 2 G₂ := by
  intro hle
  apply not_pCoreOf_stab_γ₀_le_ballStab hc hb
  rw [hc.stab_γ₀_eq]
  refine hle.trans ?_
  have h := CosetGeom.pCoreOf_stab_le_ballStab_one hc.amalgam (γ₁ G₀ G₁ G₂)
  rwa [hc.stab_γ₁_eq] at h

theorem Vv_le_pCoreOf_of_mem_nbrs_nbrs (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (hb : 5 ≤ critB G₀ G₁ G₂ Z) {δ μ δ' : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true)
    (hμ : μ ∈ nbrs δ) (hδ' : δ' ∈ nbrs μ) : Vv Z δ ≤ pCoreOf 2 (stab δ') := by
  have hG := hc.amalgam.gen
  have hμa : (graph G₀ G₁ G₂).Adj δ μ := hμ
  have hδ'a : (graph G₀ G₁ G₂).Adj μ δ' := hδ'
  have h1 : CosetGeom.dist δ μ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hμa
  have h2 : CosetGeom.dist μ δ' = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hδ'a
  have hQμ : Vv Z δ ≤ pCoreOf 2 (stab μ) := lemma72_small hc hδ (by omega)
  have hB : Vv Z δ ≤ ballStab 1 δ' := by
    intro x hx
    refine CosetGeom.mem_ballStab.mpr fun ε hε => ?_
    have h3 := CosetGeom.dist_triangle hG δ μ ε
    have h4 := CosetGeom.dist_triangle hG μ δ' ε
    exact pCoreOf_le 2 _ (lemma72_small hc hδ (μ := ε) (by omega) hx)
  exact le_trans (le_inf hQμ hB) (pCoreOf_inf_ballStab_le hδ')

end Crit

namespace Setting

variable {G : Type} [Group G] [Finite G] {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem false_of_pCoreOf_inf_le_ballStab (hs : Setting L₁ L₂ S Z) (hS3 : VS3 L₁)
    (hb : Odd (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z))
    (hb5 : 5 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z)
    (hN : ∀ μ' ∈ nbrs ν₁,
      pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S) ≤ ballStab 1 μ') : False := by
  have hc := hs.toCritAmalgam
  have hA := APrime.amalgamS3_of_setting hs.hyp hS3 hs.S_le
  have h0 : stab ν₀ = P₂ L₁ L₂ S := hc.stab_γ₀_eq
  have h1 : stab ν₁ = P₁ L₁ L₂ S := hc.stab_γ₁_eq
  have hδ : vtype ν₁ = true := CosetGeom.vtype_γ₁
  have hadj : (graph (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)).Adj ν₁ ν₀ :=
    (CosetGeom.adj_γ₀_γ₁ (G₀ := L₁ ⊔ L₂ ⊔ S) (G₁ := P₂ L₁ L₂ S) (G₂ := P₁ L₁ L₂ S)).symm
  have hd10 : CosetGeom.dist ν₁ ν₀ = 1 := CosetGeom.dist_eq_one_iff_adj.mpr hadj
  have hVQ : Vv Z ν₁ ≤ pCoreOf 2 (P₂ L₁ L₂ S) := by
    have h := lemma72_small hc hδ (μ := ν₀) (by omega)
    rwa [h0] at h
  have hK : ∀ μ' ∈ nbrs ν₁, pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S) ≤
      pCoreOf 2 (stab μ') := by
    intro μ' hμ'
    have h := pCoreOf_inf_ballStab_le hμ'
    rw [h1] at h
    exact le_trans (le_inf inf_le_right (hN μ' hμ')) h
  have hle : ∀ r ∈ P₁ L₁ L₂ S, ∀ x ∈ pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S),
      r⁻¹ * x * r ∈ pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S) := by
    intro r hr x hx
    have hr' : r ∈ stab ν₁ := by rw [h1]; exact hr
    have hr0 : r ∈ L₁ ⊔ L₂ ⊔ S := CosetGeom.stab_le _ hr'
    have hr1 : (⟨r, hr0⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁ = ν₁ := CosetGeom.smul_eq_of_mem_stab hr'
    have hμ' : (⟨r, hr0⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₀ ∈ nbrs ν₁ := by
      have h := (CosetGeom.smul_adj (⟨r, hr0⟩ : ↥(L₁ ⊔ L₂ ⊔ S))).mpr hadj
      rwa [hr1] at h
    have h2 := hK _ hμ' hx
    rw [CosetGeom.stab_smul, pCoreOf_conjSub, mem_conjSub, h0] at h2
    refine mem_inf.mpr ⟨h2, ?_⟩
    have h3 := (mem_normalizer_iff.mp (inv_mem (le_normalizer_pCoreOf 2 (P₁ L₁ L₂ S) hr)) x).mp
      (mem_inf.mp hx).2
    rwa [inv_inv] at h3
  have hD : P₁ L₁ L₂ S ≤ normalizer
      ((pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S) : Subgroup G) : Set G) := by
    intro r hr
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have h := hle r⁻¹ (inv_mem hr) x hx
      rwa [inv_inv] at h
    · intro hx
      have h := hle r hr _ hx
      have e : r⁻¹ * (r * x * r⁻¹) * r = x := by group
      rwa [e] at h
  have h2 := APrime.relIndex_pCoreOf_inf_eq_two (F7.isSylowTwoOf_pCoreOf_le hA.hyp.sylow₁)
    hA.relIndex_pCoreOf_T.le (not_pCoreOf_le_pCoreOf_of_odd hc hb)
  refine APrime.false_of_le_normalizer_pCoreOf_inf_of_setting hs.hyp hS3 hs.S_le hD h2
    (V := Vv Z ν₁) ?_ ?_ ?_
  ·
    intro x hx
    refine mem_coreIn.mpr ⟨pCoreOf_le 2 _ (hVQ hx), fun g hg => ?_⟩
    have hg' : g ∈ stab ν₀ := by rw [h0]; exact hg
    have hg0 : g ∈ L₁ ⊔ L₂ ⊔ S := CosetGeom.stab_le _ hg'
    have hfix : (⟨g, hg0⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₀ = ν₀ := CosetGeom.smul_eq_of_mem_stab hg'
    have hδ' : (⟨g, hg0⟩ : ↥(L₁ ⊔ L₂ ⊔ S)) • ν₁ ∈ nbrs ν₀ := by
      have h := (CosetGeom.smul_adj (⟨g, hg0⟩ : ↥(L₁ ⊔ L₂ ⊔ S))).mpr hadj.symm
      rwa [hfix] at h
    have h3 := Vv_le_pCoreOf_of_mem_nbrs_nbrs hc hb5 hδ (μ := ν₀) hadj hδ' hx
    rw [CosetGeom.stab_smul, pCoreOf_conjSub, mem_conjSub, h1] at h3
    refine mem_inf.mpr ⟨?_, h3⟩
    have h4 := (mem_normalizer_iff.mp (inv_mem (le_normalizer_pCoreOf 2 (P₂ L₁ L₂ S) hg)) x).mp
      (hVQ hx)
    rwa [inv_inv] at h4
  ·
    have h := (lemma63_2' hc hδ).2.2.2.2
    rwa [h1] at h
  ·
    intro r hr hr2
    by_contra hcon
    have hcon' : ∀ v ∈ Vv Z ν₁, r * v * r⁻¹ = v := fun v hv =>
      not_not.mp fun hne => hcon ⟨v, hv, hne⟩
    apply hr2
    have hrc : r ∈ centralizer (Vv Z ν₁ : Set G) := by
      rw [mem_centralizer_iff]
      intro v hv
      have h := hcon' v hv
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hr' : r ∈ stab ν₁ := by rw [h1]; exact hr
    have hrB := mem_ballStab_of_centralizes hc hδ hr' hrc
    have h := CosetGeom.ballStab_le_stab_of_dist_le hd10.le hrB
    rwa [h0] at h

end Setting

end CFSG.Quasithin.F112Crit

end
