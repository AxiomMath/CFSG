module

public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTorus
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveWindow
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

variable {G : Type} [Group G] [Finite G]

open CosetGeom (graph stab nbrs vtype γ₀ γ₁)

namespace Setting

variable {L₁ L₂ S Z : Subgroup G}

local notation "ν₀" => γ₀ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)
local notation "ν₁" => γ₁ (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)

theorem exists_isEdgeHall (hs : Setting L₁ L₂ S Z)
    {μ δ : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S)} (hμ : vtype μ = false)
    (hδ : δ ∈ nbrs μ) : ∃ X : Subgroup G, IsEdgeHall μ δ X := by
  obtain ⟨T, hTH, hHT, hT, hodd⟩ := hs.exists_normal_two_edge hμ hδ
  obtain ⟨X, hXH, hX⟩ := exists_hall_of_normal_two hTH hHT hT hodd
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  refine ⟨X, hXH, by rw [hX]; exact hodd, k, ?_⟩
  have h1 := C5.card_eq_card_mul_relIndex hTH
  have h2 := C5.card_eq_card_mul_relIndex hXH
  have hpos : 0 < Nat.card X := Nat.card_pos
  rw [← hk]
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← h2, h1, hX, mul_comm]

theorem false_of_pCoreOf_inf_trans (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂)) (hS3 : VS3 L₁)
    (hb : Odd (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z))
    (hb5 : 5 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z)
    (hN : ∀ δ μ μ' : CosetGeom (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S), vtype δ = true →
      μ ∈ nbrs δ → μ' ∈ nbrs δ → μ ≠ μ' → ∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ δ → ε' ≠ δ →
        ∃ r : ↥(L₁ ⊔ L₂ ⊔ S), (r : G) ∈ pCoreOf 2 (stab δ) ⊓ pCoreOf 2 (stab μ) ∧ r • ε = ε') :
    False :=
  F112Crit.false_of_pCoreOf_inf_trans hs.toCritAmalgam hb hb5
    (fun μ hμ δ hδ ε hε ε' hε' h h' => by
      obtain ⟨L, hL⟩ := hs.exists_benderLocal hK hμ
      exact hL.exists_smul_eq_of_ne hδ hε hε' h h')
    (fun μ δ hμ hδ => hs.exists_isEdgeHall hμ hδ)
    (fun μ δ X hμ hδ hX => hs.torusGraph hK hC hS3 hμ hδ hX) hN

theorem false_of_pCoreOf_inf_trans_base (hs : Setting L₁ L₂ S Z) {q i : ℕ}
    (hK : IsBenderQuot (oTwoQuot ↥L₂) q i) (hC : IsCartanQuot (oTwoQuot ↥L₂)) (hS3 : VS3 L₁)
    (hb : Odd (critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z))
    (hb5 : 5 ≤ critB (L₁ ⊔ L₂ ⊔ S) (P₂ L₁ L₂ S) (P₁ L₁ L₂ S) Z)
    (hN : ∀ μ' ∈ nbrs ν₁, μ' ≠ ν₀ → ∀ ε ∈ nbrs μ', ∀ ε' ∈ nbrs μ', ε ≠ ν₁ → ε' ≠ ν₁ →
      ∃ r : ↥(L₁ ⊔ L₂ ⊔ S), (r : G) ∈ pCoreOf 2 (P₂ L₁ L₂ S) ⊓ pCoreOf 2 (P₁ L₁ L₂ S) ∧
        r • ε = ε') :
    False := by
  refine hs.false_of_pCoreOf_inf_trans hK hC hS3 hb hb5 ?_
  intro δ μ μ' hδ hμ hμ' hne ε hε ε' hε' h h'
  obtain ⟨g, rfl⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
  have hμ₁ : (graph _ _ _).Adj ν₁ (g⁻¹ • μ) := by
    have := (CosetGeom.smul_adj g⁻¹).mpr (show (graph _ _ _).Adj (g • ν₁) μ from hμ)
    rwa [inv_smul_smul] at this
  have hν₀ : (graph _ _ _).Adj ν₁ ν₀ := CosetGeom.adj_γ₀_γ₁.symm
  obtain ⟨k, hk₁, hkμ⟩ := CosetGeom.exists_stab_smul_eq hμ₁ hν₀
  set g' := g * k⁻¹ with hg'
  have hk₁' : k⁻¹ • ν₁ = ν₁ := inv_smul_eq_iff.mpr hk₁.symm
  have hg'₁ : g' • ν₁ = g • ν₁ := by
    rw [hg', mul_smul, hk₁']
  have hg'₀ : g' • ν₀ = μ := by
    rw [hg', mul_smul, ← hkμ, inv_smul_smul, smul_inv_smul]
  have hμ'' : g'⁻¹ • μ' ∈ nbrs ν₁ := by
    have := (CosetGeom.smul_adj g'⁻¹).mpr (show (graph _ _ _).Adj (g • ν₁) μ' from hμ')
    rwa [← hg'₁, inv_smul_smul] at this
  have hne'' : g'⁻¹ • μ' ≠ ν₀ := by
    intro e
    apply hne
    rw [← hg'₀, ← e, smul_inv_smul]
  have hε₁ : g'⁻¹ • ε ∈ nbrs (g'⁻¹ • μ') := (CosetGeom.smul_adj g'⁻¹).mpr hε
  have hε₁' : g'⁻¹ • ε' ∈ nbrs (g'⁻¹ • μ') := (CosetGeom.smul_adj g'⁻¹).mpr hε'
  have hne₁ : g'⁻¹ • ε ≠ ν₁ := by
    intro e
    apply h
    rw [← hg'₁, ← e, smul_inv_smul]
  have hne₁' : g'⁻¹ • ε' ≠ ν₁ := by
    intro e
    apply h'
    rw [← hg'₁, ← e, smul_inv_smul]
  obtain ⟨r, hr, hrε⟩ := hN _ hμ'' hne'' _ hε₁ _ hε₁' hne₁ hne₁'
  refine ⟨g' * r * g'⁻¹, ?_, ?_⟩
  · have hc := hs.toCritAmalgam
    rw [← hg'₁, ← hg'₀, CosetGeom.stab_smul, CosetGeom.stab_smul, hc.stab_γ₁_eq,
      hc.stab_γ₀_eq, pCoreOf_conjSub, pCoreOf_conjSub]
    refine ⟨mem_conjSub.mpr ?_, mem_conjSub.mpr ?_⟩
    · simpa [mul_assoc] using hr.2
    · simpa [mul_assoc] using hr.1
  · rw [mul_smul, mul_smul, hrε, smul_inv_smul]

end Setting

end CFSG.Quasithin.F112Crit

end
