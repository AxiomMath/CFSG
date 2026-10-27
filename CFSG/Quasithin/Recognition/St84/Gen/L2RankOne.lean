module

public import CFSG.Quasithin.Background.F1Rank
public import CFSG.Quasithin.EmptyFaithful.S1421F112

import CFSG.CGT.Timmesfeld75.L2Defs
import CFSG.Quasithin.Vol2.KGNatSL2
import CFSG.Quasithin.EmptyFaithful.SzN6Borel
import CFSG.Walter.PSL2Facts.Even
import Mathlib.Tactic.Group
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
import CFSG.Certificates.Kernel.LocalCompTits.Span
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Alt
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Native
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Containment
import CFSG.Quasithin.Background.A3Structure312
import CFSG.Quasithin.Background.A3Structure318Red
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BAction
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BCase3Base
import CFSG.Quasithin.Background.A3Structure36BCasesBase
import CFSG.Quasithin.Background.A3Structure36BCommonBase
import CFSG.Quasithin.Background.A3Structure36BFrattini
import CFSG.Quasithin.Background.A3Structure36BHeisBase
import CFSG.Quasithin.Background.A3Structure36BHomocyclic
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.A3Structure36BStarBase
import CFSG.Quasithin.Background.A3Structure36Base
import CFSG.Quasithin.Background.A3Structure38Part3
import CFSG.Quasithin.Background.B1MoreNineG
import CFSG.Quasithin.Background.B4ModelsIso
import CFSG.Quasithin.Background.C2Basic
import CFSG.Quasithin.Background.C2Inputs
import CFSG.Quasithin.Background.E3Cent
import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
import CFSG.Quasithin.Vol2.Ch11SecCFacts
import CFSG.Quasithin.Vol2.Ch11SecCFacts2
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch1Local
import CFSG.Quasithin.Vol2.KGNatCoord
import CFSG.Sporadic.Schreier.J4SSylow
import CFSG.Walter.Defs
import Certificates.Certificate8026Base
import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1
import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.CGT.Timmesfeld75 CFSG.Quasithin.Vol2.KGNat
open scoped MatrixGroups commutatorElement

universe u

private theorem commutator_mem_utri_of_mem_borel {F : Type} [Field F] [Finite F] [CharP F 2]
    {a b : SL(2, F)} (ha : a ∈ borel F) (hb : b ∈ borel F) :
    a * b * a⁻¹ * b⁻¹ ∈ utri F := by
  let B : Subgroup SL(2, F) := borel F
  have hUB : utri F ≤ B := utri_le_borel
  have hTB : torus F ≤ B := torus_le_borel
  haveI : Subgroup.Normal ((utri F).subgroupOf B) :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hLE := borel_le_normalizer_utri)
  have hsup : (utri F).subgroupOf B ⊔ (torus F).subgroupOf B = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUB hTB]
    change (utri F ⊔ torus F).subgroupOf (borel F) = ⊤
    rw [← borel_eq_sup, Subgroup.subgroupOf_self]
  haveI : IsMulCommutative (torus F) := (isCyclic_torus (F := F)).isMulCommutative
  have hcomm := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (N := (utri F).subgroupOf B) (H := (torus F).subgroupOf B) hsup (hH := inferInstance)
  have haB : a ∈ B := ha
  have hbB : b ∈ B := hb
  have hmem : (⟨a, haB⟩ : ↥B) * ⟨b, hbB⟩ * (⟨a, haB⟩ : ↥B)⁻¹ * (⟨b, hbB⟩ : ↥B)⁻¹ ∈
      (utri F).subgroupOf B := by
    simpa [commutatorElement_def] using
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top (⟨a, haB⟩ : ↥B))
        (Subgroup.mem_top (⟨b, hbB⟩ : ↥B)))
  simpa using Subgroup.mem_subgroupOf.mp hmem

private theorem isRankOneSylow_sl2 {F : Type} [Field F] [Finite F] [CharP F 2] :
    IsRankOneSylow (SL(2, F)) := by
  intro T hT hodd
  have hTsyl : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT, ?_⟩
    rw [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T]
    exact hodd
  obtain ⟨g, hg⟩ := exists_conj_utri_eq_of_index (F := F) hT hodd
  refine ⟨?_, ?_, ?_⟩
  · rw [← hg]
    exact (normalizer_conj_utri (F := F) g).1
  · intro M hTM hM
    exact CFSG.Quasithin.SzN6.sl2_proper_overgroup_le_normalizer T M hTsyl hTM hM
  · intro x hx y hy
    have hx' : g⁻¹ * x * g ∈ Subgroup.normalizer (utri F : Set (SL(2, F))) := by
      rw [← hg] at hx
      exact (mem_normalizer_conjSubgroup (T := utri F) (g := g) (x := x)).mp hx
    have hy' : g⁻¹ * y * g ∈ Subgroup.normalizer (utri F : Set (SL(2, F))) := by
      rw [← hg] at hy
      exact (mem_normalizer_conjSubgroup (T := utri F) (g := g) (x := y)).mp hy
    rw [normalizer_utri_eq_borel] at hx' hy'
    have hcomm := commutator_mem_utri_of_mem_borel hx' hy'
    rw [← hg]
    refine (CFSG.CGT.Timmesfeld75.mem_conjSubgroup (g := g) (T := utri F)).mpr ?_
    rw [show g⁻¹ * (x * y * x⁻¹ * y⁻¹) * g =
      (g⁻¹ * x * g) * (g⁻¹ * y * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * y * g)⁻¹ by group]
    exact hcomm

theorem isRankOneSylow_of_isL2Quot {K : Type*} [Group K] [Finite K] {f : ℕ} (hf : 1 ≤ f)
    (h : IsL2Quot f K) : IsRankOneSylow K := by
  obtain ⟨e⟩ := h
  have hf0 : f ≠ 0 := by omega
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf0
  haveI : CharP (GaloisField 2 f) 2 := by
    haveI : Fintype (GaloisField 2 f) := Fintype.ofFinite _
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by
      rw [← Nat.card_eq_fintype_card, hcard])
  have hSL : IsRankOneSylow (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    isRankOneSylow_sl2 (F := GaloisField 2 f)
  have hPSL : IsRankOneSylow
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 f)) :=
    hSL.of_mulEquiv (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 f)).symm
  exact hPSL.of_mulEquiv e.symm

theorem hyp111R_of_isL2Quot {G : Type u} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (h : Hyp111 L1 L2 S)
    (h1 : IsL2Quot m (oTwoQuot ↥L1)) (h2 : IsL2Quot n (oTwoQuot ↥L2)) : Hyp111R L1 L2 S :=
  ⟨h, F1.rankOneAt_of_isRankOneSylow h.h1.sylow (isRankOneSylow_of_isL2Quot hm h1),
    F1.rankOneAt_of_isRankOneSylow h.h2.sylow (isRankOneSylow_of_isL2Quot hn h2)⟩

end CFSG.Quasithin.F112R.St84
