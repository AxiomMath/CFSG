module

public import CFSG.Open.LocalVocabulary
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.F1Hyp
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import CFSG.Quasithin.Recognition.St84.Gen.L3qVertex
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclUp
import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
import CFSG.Quasithin.Recognition.GoldschmidtF112RSp44
import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfC
import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieModel
import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3
import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ExclLev
import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.Quasithin.WBN

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.F112R CFSG.QuasithinUnique
  CFSG.Quasithin.H13.Ch9.F112Pf CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private theorem model_fact {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {V : Subgroup (projectiveSL 3 F)} (hF : Nat.card F = 2 ^ n)
    (hcore : pCoreOf 2 (Subgroup.normalizer (V : Set (projectiveSL 3 F))) = V)
    (hlin : IsLin2Type (perfectCore (Subgroup.normalizer (V : Set (projectiveSL 3 F)))) n)
    (hVcard : Nat.card V = Nat.card F ^ 2) :
    pCoreOf 2 (Subgroup.normalizer (V : Set (projectiveSL 3 F))) ⊓
      Subgroup.centralizer (perfectCore (Subgroup.normalizer (V : Set (projectiveSL 3 F))) :
        Set (projectiveSL 3 F)) = ⊥ := by
  let P : Subgroup (projectiveSL 3 F) := Subgroup.normalizer (V : Set (projectiveSL 3 F))
  let X : Subgroup (projectiveSL 3 F) := perfectCore P
  have hXle : X ≤ P := perfectCore_le P
  have hPNX : P ≤ Subgroup.normalizer (X : Set (projectiveSL 3 F)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXle).mp (perfectCore_normal P)
  have hVN : V ≤ Subgroup.normalizer (X : Set (projectiveSL 3 F)) :=
    (Subgroup.le_normalizer (H := V)).trans hPNX
  have hNX : X ≤ Subgroup.normalizer (V : Set (projectiveSL 3 F)) := hXle
  have hQle : pCoreOf 2 X ≤ V := by
    have h := CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 hXle hPNX
    rwa [hcore] at h
  have hUXle : blockU X ≤ V := by
    have h := CFSG.Quasithin.F7.commutator_le_inf_of_normalizes hVN hNX
    exact (Subgroup.commutator_mono hQle le_rfl).trans (h.trans inf_le_left)
  obtain ⟨K, hKfield, hKfintype, hKcard, -, -, -, β, hβsurj, hβker, -⟩ := hlin
  letI := hKfield
  letI := hKfintype
  have hKF : Nat.card K = Nat.card F := by
    rw [← Fintype.card_eq_nat_card, hKcard, ← hF]
  have hkerCard : Nat.card ((blockZ X).subgroupOf (blockU X)) = Nat.card (blockZ X) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show blockZ X ≤ blockU X from inf_le_left)).toEquiv
  have hcardTarget : Nat.card (Multiplicative (Fin 2 → K)) = Nat.card K ^ 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_eq_nat_card]
  have hcardU : Nat.card (blockU X) = Nat.card K ^ 2 * Nat.card (blockZ X) := by
    have h := Subgroup.card_ker_mul_card_of_surjective (f := β) hβsurj
    rw [hβker, hcardTarget, hkerCard] at h
    rw [← h, mul_comm]
  have hZle : Nat.card (blockZ X) ≤ 1 := by
    have hbound : Nat.card (blockU X) ≤ Nat.card V :=
      Subgroup.card_le_of_le hUXle
    rw [hcardU, hVcard, hKF] at hbound
    conv_rhs at hbound => rw [← mul_one (Nat.card F ^ 2)]
    exact Nat.le_of_mul_le_mul_left hbound (pow_pos Nat.card_pos 2)
  have hZbot : blockZ X = ⊥ := Subgroup.eq_bot_of_card_le (blockZ X) hZle
  have hcardUeq : Nat.card (blockU X) = Nat.card V := by
    rw [hcardU, hZbot, Subgroup.card_bot, mul_one, hKF, ← hVcard]
  have hUeq : blockU X = V :=
    Subgroup.eq_of_le_of_card_ge hUXle (le_of_eq hcardUeq.symm)
  have hcoreP : pCoreOf 2 P = V := hcore
  calc pCoreOf 2 P ⊓ Subgroup.centralizer X = V ⊓ Subgroup.centralizer X := by rw [hcoreP]
    _ = blockU X ⊓ Subgroup.centralizer X := by rw [← hUeq]
    _ = blockZ X := rfl
    _ = ⊥ := hZbot

theorem pCoreOf_inf_centralizer_pointParabolic_eq_bot {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (Subgroup.normalizer (CFSG.QuasithinUnique.Fin257.L3.V1 (F := F) :
        Set (projectiveSL 3 F))) ⊓
      Subgroup.centralizer (perfectCore (Subgroup.normalizer
        (CFSG.QuasithinUnique.Fin257.L3.V1 (F := F) : Set (projectiveSL 3 F))) :
          Set (projectiveSL 3 F)) = ⊥ :=
  model_fact hF (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F)).core₁
    (CFSG.Quasithin.F112R.PointVertex.l3_vertex_V1 (F := F) hn hF).2
    (CFSG.GH74.QTGen4.DSGen4.L34.card_V1 (F := F))

theorem pCoreOf_inf_centralizer_lineParabolic_eq_bot {F : Type} [Field F] [Finite F]
    [CharP F 2] {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    pCoreOf 2 (Subgroup.normalizer (CFSG.QuasithinUnique.Fin257.L3.V2 (F := F) :
        Set (projectiveSL 3 F))) ⊓
      Subgroup.centralizer (perfectCore (Subgroup.normalizer
        (CFSG.QuasithinUnique.Fin257.L3.V2 (F := F) : Set (projectiveSL 3 F))) :
          Set (projectiveSL 3 F)) = ⊥ :=
  model_fact hF (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F)).core₂
    (CFSG.Quasithin.F112R.LineVertex.l3_vertex_V2 (F := F) hn hF).2
    (CFSG.GH74.QTGen4.DSGen4.L34.card_V2 (F := F))

theorem pCoreOf_inf_centralizer_of_mulEquiv {G H : Type} [Group G] [Group H]
    {L P : Subgroup G} {N : Subgroup H} (hL : perfectCore P = L) (ψ : ↥P ≃* ↥N)
    (h : pCoreOf 2 N ⊓ Subgroup.centralizer (perfectCore N : Set H) = ⊥) :
    pCoreOf 2 P ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  let f : ↥P →* H := N.subtype.comp ψ.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp ψ.injective
  have htopP : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have htopN : (⊤ : Subgroup ↥P).map f = N := by
    rw [← Subgroup.map_map, Subgroup.map_top_of_surjective ψ.toMonoidHom ψ.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  have hpcP : (pCoreOf 2 (⊤ : Subgroup ↥P)).map P.subtype = pCoreOf 2 P := by
    rw [← CFSG.Quasithin.Rk2.pCoreOf_map_of_injective P.subtype P.subtype_injective ⊤, htopP]
  have hpcN : (pCoreOf 2 (⊤ : Subgroup ↥P)).map f = pCoreOf 2 N := by
    rw [← CFSG.Quasithin.Rk2.pCoreOf_map_of_injective f hf ⊤, htopN]
  have hcP : perfectCore P = (perfectCore (⊤ : Subgroup ↥P)).map P.subtype := by
    rw [← CFSG.Quasithin.F112R.perfectCore_map_inj P.subtype P.subtype_injective ⊤, htopP]
  have hcN : perfectCore N = (perfectCore (⊤ : Subgroup ↥P)).map f := by
    rw [← CFSG.Quasithin.F112R.perfectCore_map_inj f hf ⊤, htopN]
  apply le_antisymm _ bot_le
  rintro x ⟨hxP, hxC⟩
  obtain ⟨z, hz, rfl⟩ : ∃ z ∈ pCoreOf 2 (⊤ : Subgroup ↥P), P.subtype z = x := by
    rw [← hpcP] at hxP
    exact hxP
  have hyN : (ψ z : H) ∈ pCoreOf 2 N := by
    change f z ∈ pCoreOf 2 N
    have h2 : f z ∈ (pCoreOf 2 (⊤ : Subgroup ↥P)).map f :=
      Subgroup.mem_map_of_mem f hz
    rwa [hpcN] at h2
  have hyC : (ψ z : H) ∈ Subgroup.centralizer (perfectCore N : Set H) := by
    rw [hcN, Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨u, hu, rfl⟩ := hw
    change N.subtype (ψ u) * N.subtype (ψ z) = N.subtype (ψ z) * N.subtype (ψ u)
    have huL : (u : G) ∈ L := by
      rw [← hL, hcP]
      exact Subgroup.mem_map_of_mem P.subtype hu
    have hzu : u * z = z * u := by
      apply P.subtype_injective
      show (u : G) * (z : G) = (z : G) * (u : G)
      exact (Subgroup.mem_centralizer_iff.mp hxC) (u : G) huL
    have hψ : ψ u * ψ z = ψ z * ψ u := by
      rw [← map_mul, ← map_mul, hzu]
    calc N.subtype (ψ u) * N.subtype (ψ z)
        = N.subtype (ψ u * ψ z) := by rw [map_mul]
      _ = N.subtype (ψ z * ψ u) := by rw [hψ]
      _ = N.subtype (ψ z) * N.subtype (ψ u) := by rw [map_mul]
  have hy : (ψ z : H) ∈ pCoreOf 2 N ⊓
      Subgroup.centralizer (perfectCore N : Set H) :=
    Subgroup.mem_inf.mpr ⟨hyN, hyC⟩
  rw [h, Subgroup.mem_bot] at hy
  have hy' : ψ z = 1 := by
    apply N.subtype_injective
    rw [map_one]
    exact hy
  have hz1 : z = 1 := ψ.injective (by rw [hy', map_one])
  rw [hz1]
  rfl

theorem pCoreOf_inf_centralizer_eq_bot_of_psl3 {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {f : ℕ} (hH : CFSG.Quasithin.Hyp111 L1 L2 S) (hf : 2 ≤ f)
    (h1 : CFSG.Quasithin.IsL2Quot f (CFSG.Quasithin.oTwoQuot ↥L1))
    (h2 : CFSG.Quasithin.IsL2Quot f (CFSG.Quasithin.oTwoQuot ↥L2))
    (hA : CFSG.Quasithin.IsAmalgamOfGroup (CFSG.Quasithin.F112R.f112Amalgam L1 L2 S)
      (CFSG.Quasithin.IsLieOverTwo .PSL 3 f)) :
    CFSG.Open.pCoreOf 2 (L1 ⊔ CFSG.Quasithin.bigB L1 L2 S) ⊓
      Subgroup.centralizer (L1 : Set G) = ⊥ := by
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hH hf h1 hf h2
    (hasModelFacts_l3 f hf) hA
  obtain ⟨hB, -, -⟩ := vFact_of_hasModelFacts_of_isL2Quot hf h1 hf h2
    (hasModelFacts_l3 f hf) hA
  obtain ⟨hB1, -⟩ := bigB_le_normalizer hH
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  obtain ⟨Y, _, hY, T, N₁, N₂, hp, ⟨iso0⟩⟩ := hA
  have hL : CFSG.Blueprint.LieModel Y .PSL 3 2 f := hY
  obtain ⟨-, F, _, _, _, hFcard, ⟨e1⟩⟩ :=
    CFSG.Quasithin.H13.F431.L3.exists_equiv_projSL3 hL
  have hy1 := hp.map e1
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1
    (CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U (F := F))
  let E : Y ≃* projectiveSL 3 F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (projUnitriangular 3 F) (N₁.map E.toMonoidHom)
      (N₂.map E.toMonoidHom) := by
    have := hp.map E
    have hTD : T.map E.toMonoidHom = projUnitriangular 3 F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  have ψ1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥(N₁.map E.toMonoidHom) :=
    iso0.φ1.trans (N₁.equivMapOfInjective E.toMonoidHom E.injective)
  rcases CFSG.QuasithinUnique.Borel252.BorelData.yam_cases
      (CFSG.QuasithinUnique.Borel252.L3.borelData_L3 (F := F))
      (CFSG.Quasithin.H13.F431.L3.no_normal_two_subgroup (F := F)) hy2 with
    ⟨hN1, -⟩ | ⟨hN1, -⟩
  · rw [hN1] at ψ1
    exact pCoreOf_inf_centralizer_of_mulEquiv hc1 ψ1
      (pCoreOf_inf_centralizer_pointParabolic_eq_bot hf hFcard)
  · rw [hN1] at ψ1
    exact pCoreOf_inf_centralizer_of_mulEquiv hc1 ψ1
      (pCoreOf_inf_centralizer_lineParabolic_eq_bot hf hFcard)

end CFSG.Quasithin.WBN
