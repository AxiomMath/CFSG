module

public import CFSG.Quasithin.Recognition.St84.Gen.BigL2Slice
public import CFSG.Quasithin.Recognition.St84.Gen.PerfectGen
public import CFSG.Quasithin.H13.NQCatD4Irred
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieD4Facts
import CFSG.Quasithin.Recognition.St84.Gen.G2q
import CFSG.Quasithin.Recognition.St84.Gen.D4qModel
import CFSG.Quasithin.Recognition.St84.Gen.D4qRadical
import CFSG.Quasithin.H13.NQCatF112D4
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4
import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModD4Perf
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivAmalgam
import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.Recognition.GoldschmidtF112TitsBorel
public import CFSG.RankThree.S4Free.Statement
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairLinear
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionModelPairSuzuki
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
import CFSG.Quasithin.Background.A3Structure319
import CFSG.Quasithin.Background.C1GNA7
import CFSG.Quasithin.Background.D14Normal
import CFSG.Quasithin.EmptyFaithful.S153E58A
import CFSG.Quasithin.Recognition.GoldschmidtFan86UnivStab
import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
import CFSG.Quasithin.Vol2.Ch11SecA02Setup
import CFSG.Quasithin.Vol2.Ch11SecA03Basic
import CFSG.Quasithin.Vol2.Ch11SecA04Glue
import CFSG.Quasithin.Vol2.Ch11SecA11Ord2
import CFSG.Quasithin.Vol2.Ch11SecAFacts03
import CFSG.Quasithin.Vol2.Ch11SecAFacts04
import CFSG.Quasithin.Vol2.Ch11SecSFacts
import CFSG.Quasithin.Vol2.Ch11SecSSetup
import CFSG.Quasithin.Vol2.Ch11StatementsF
import CFSG.Quasithin.Vol2.Ch11StatementsG
import CFSG.Quasithin.Vol2.Ch11StatementsH
import CFSG.Quasithin.Vol2.Ch11StatementsInputs
import CFSG.Quasithin.Vol2.Ch1Eight
import CFSG.Quasithin.Vol2.Ch5Sec1L34DSSz
import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsDSSz
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111K1
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112
import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113
import CFSG.Quasithin.Vol2.Ch5Sec1Lem516Quot
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Bd
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Orient
import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Z
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84TorusModels

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4
  CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.Ch9.F112Pf CFSG.Quasithin.B42D4
  CFSG.Quasithin.H13.Sec53F CFSG.Quasithin.H13.NQCat
  CFSG.LieType.Steinberg.CentralExt.GriessNative
open scoped commutatorElement

section Main


private theorem nonempty_pCore_equiv_d4
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K)
    {Y : Type} [Group Y]
    (φ : Y ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (a : Fin TwistTag.D4.foldedTag.rank)
    (hF : ParabolicFacts (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})
      (graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a}))
    (hne : pCoreOf 2 (perfectCore (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a})) ≠ ⊥) :
    Nonempty (↥(pCoreOf 2 (perfectCore
      (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom))) ≃*
      ↥(graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a})) := by
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let X := (graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf C
  let W := pCoreOf 2 (perfectCore X)
  have hPC : graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} ≤ C :=
    graphFixedParabolic_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) {a}
  have hXmap : X.map C.subtype = graphFixedParabolic TwistTag.D4 K σ.toRingHom {a} :=
    Subgroup.map_subgroupOf_eq_of_le hPC
  have hWmap : W.map C.subtype =
      graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} := by
    rw [← pCoreOf_map_inj C.subtype C.subtype_injective,
      ← perfectCore_map_inj _ C.subtype_injective, hXmap]
    exact D4Irred.pCoreOf_eq_of_parabolicFacts hF hne
  have e1 : pCoreOf 2 (perfectCore (X.map φ.symm.toMonoidHom)) =
      W.map φ.symm.toMonoidHom := by
    rw [perfectCore_map_inj _ φ.symm.injective, pCoreOf_map_inj _ φ.symm.injective]
  exact ⟨(MulEquiv.subgroupCongr e1).trans
    ((W.equivMapOfInjective _ φ.symm.injective).symm.trans
      ((W.equivMapOfInjective _ C.subtype_injective).trans (MulEquiv.subgroupCongr hWmap)))⟩

private theorem not_isL2Quot_perfectCore_p0
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3) (hK4 : 4 ≤ Nat.card K)
    {Y : Type} [Group Y]
    (φ : Y ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {N : Subgroup Y} (hN : N = (perfectCore ((P0 σ).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map φ.symm.toMonoidHom) :
    ¬ IsL2Quot f (oTwoQuot ↥N) := by
  intro hq
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hf1 : 1 ≤ f := by omega
  have hQC : P0 σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolic_le (t := TwistTag.D4) (K := K) (σ := σ.toRingHom) {D4.fa0}
  let Q : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :=
    (P0 σ).subgroupOf (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
  have hPerfectC : (perfectCore Q).map
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype = perfectCore (P0 σ) :=
    TriD4.perfectCore_subgroupOf_map (C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (N := P0 σ) hQC
  let e1 : ↥N ≃* ↥(perfectCore Q) :=
    (MulEquiv.subgroupCongr hN).trans
      ((perfectCore Q).equivMapOfInjective φ.symm.toMonoidHom φ.symm.injective).symm
  let ψ : ↥N ≃* ↥(perfectCore (P0 σ)) :=
    e1.trans (((perfectCore Q).equivMapOfInjective
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom).subtype_injective).trans
        (MulEquiv.subgroupCongr hPerfectC))
  have hNns : ¬ Group.IsSolvable ↥(perfectCore (P0 σ)) := by
    intro hs
    haveI : Group.IsSolvable ↥(perfectCore (P0 σ)) := hs
    apply not_isSolvable_of_isL2Quot hf hq
    exact Group.isSolvable_of_isSolvable_injective (f := ψ.toMonoidHom) ψ.injective
  have hbound : Nat.card K ≤ Nat.card (oTwoQuot ↥(perfectCore (P0 σ))) :=
    F112D4.card_le_card_oTwoQuot_a0 (K := K) σ hσ3 hK4 (perfectCore_le _)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)) hNns
  have hcardEq : Nat.card (oTwoQuot ↥(perfectCore (P0 σ))) = 2 ^ f * (4 ^ f - 1) := by
    rw [← Nat.card_congr (CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv ψ).toEquiv]
    exact IsL2Quot.card hf1 hq
  have hlt : 2 ^ f * (4 ^ f - 1) < Nat.card K := by
    rw [hK]
    have h4 : 4 ^ f = (2 ^ f) ^ 2 := by
      calc 4 ^ f = (2 ^ 2) ^ f := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        _ = 2 ^ (2 * f) := (pow_mul 2 2 f).symm
        _ = 2 ^ (f * 2) := by rw [Nat.mul_comm 2 f]
        _ = (2 ^ f) ^ 2 := pow_mul 2 f 2
    calc 2 ^ f * (4 ^ f - 1) < 2 ^ f * 4 ^ f :=
          mul_lt_mul_of_pos_left (Nat.sub_lt (by positivity) one_pos) (by positivity)
      _ = (2 ^ f) ^ 3 := by rw [h4, ← pow_succ']
  rw [hcardEq] at hbound
  omega

private theorem d4q_pCore_perfectCore_ne_bot
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hK4 : 4 ≤ Nat.card K) (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom)) :
    pCoreOf 2 (perfectCore (P0 σ)) ≠ ⊥ ∧ pCoreOf 2 (perfectCore (P1 σ)) ≠ ⊥ := by
  have hQ0ne : Q0 σ ≠ ⊥ := by
    rintro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := nonabelian_a0 σ hσ3
    rw [hbot, Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  have hQ1ne : Q1 σ ≠ ⊥ := by
    rintro hbot
    obtain ⟨x, hx, y, hy, hxy⟩ := nonabelian_a1 σ hσ3
    rw [hbot, Subgroup.mem_bot] at hx hy
    exact hxy (by rw [hx, hy])
  constructor
  · intro hbot
    have hle : Q0 σ ≤ pCoreOf 2 (perfectCore (P0 σ)) :=
      le_pCoreOf_of_le_normalizer 2 (TriD4.Q0_le_perfectCore σ hσ3 hK4)
        ((perfectCore_le (P0 σ)).trans (library_facts σ fa0 singleton_ne_univ_fa0).2.1)
        (library_facts σ fa0 singleton_ne_univ_fa0).2.2.1
    exact hQ0ne (le_bot_iff.mp (hbot ▸ hle))
  · intro hbot
    have hle : Q1 σ ≤ pCoreOf 2 (perfectCore (P1 σ)) :=
      le_pCoreOf_of_le_normalizer 2 (TriD4.Q1_le_perfectCore σ hσ3 hk4)
        ((perfectCore_le (P1 σ)).trans (library_facts σ fa1 singleton_ne_univ_fa1).2.1)
        (library_facts σ fa1 singleton_ne_univ_fa1).2.2.1
    exact hQ1ne (le_bot_iff.mp (hbot ▸ hle))

private theorem d4q_model_equivs {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hf : 2 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K) (hσ3 : σ.toRingHom ^ 3 = 1)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hK4 : 4 ≤ Nat.card K)
    (hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom))
    {Y : Type} [Group Y] [Finite Y]
    (φ : Y ≃* ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    {T M₁ M₂ : Subgroup Y} (hp : IsYAmalgamPair T M₁ M₂)
    (hres : ResidualOvergroupsAt Y T (fun j =>
      ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom))
    (hU : T.map φ.toMonoidHom = (graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
    (iso1 : ↥(L1 ⊔ bigB L1 L2 S) ≃* ↥M₁) (iso2 : ↥(L2 ⊔ bigB L1 L2 S) ≃* ↥M₂)
    (hc1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1)
    (hc2 : perfectCore (L2 ⊔ bigB L1 L2 S) = L2)
    (ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1)
    (ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2)) :
    Nonempty (↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≃* ↥(Q0 σ)) ∧
      Nonempty (↥(pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) ≃* ↥(Q1 σ)) := by
  obtain ⟨hne0, hne1⟩ := d4q_pCore_perfectCore_ne_bot σ hσ3 hK4 hk4
  have hdich : ∀ x : Fin TwistTag.D4.foldedTag.rank, x = D4.fa0 ∨ x = D4.fa1 := by decide
  have hT' : T = ((graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom := by
    rw [← hU, Subgroup.map_map]
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y :=
      MulEquiv.toMonoidHom_symm_comp_toMonoidHom φ
    rw [e, Subgroup.map_id]
  have ha : ∀ j : Fin 2, T ≤ perfectCore
      (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) := by
    intro j
    rw [hT', perfectCore_map_inj _ φ.symm.injective]
    refine Subgroup.map_mono ?_
    intro x hx
    rw [TriD4.mem_perfectCore_subgroupOf (graphFixedParabolic_le (t := TwistTag.D4) (K := K)
      (σ := σ.toRingHom) {d4Index j})]
    rcases hdich (d4Index j) with h | h
    · rw [h]
      exact TriD4.posUnipotent_le_perfectCore_P0 σ hσ3 hK4 hx
    · rw [h]
      exact TriD4.posUnipotent_le_perfectCore_P1 σ hσ3 hk4 hx
  have hnsv : ∀ (L : Subgroup G) (M : Subgroup Y) (m : ℕ), 2 ≤ m →
      (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) → IsL2Quot m (oTwoQuot ↥L) →
        ¬ Group.IsSolvable ↥M := by
    intro L M m hm e hq hs
    haveI : Group.IsSolvable ↥M := hs
    apply not_isSolvable_of_isL2Quot hm hq
    have : Group.IsSolvable ↥(L ⊔ bigB L1 L2 S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ bigB L1 L2 S))
  obtain ⟨j₁, j₂, hj, hd₁, hd₂⟩ := exists_residual_indices hres ha hp
    (hnsv L1 M₁ (3 * f) (by omega) iso1 h1) (hnsv L2 M₂ f (by omega) iso2 h2)
  have hry : d4Index j₂ ≠ D4.fa0 := by
    intro h0
    have hM : perfectCore M₂ = (perfectCore ((P0 σ).subgroupOf
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))).map φ.symm.toMonoidHom := by
      rw [hd₂, perfectCore_map_inj _ φ.symm.injective, h0]
    have hq' : IsL2Quot f (oTwoQuot ↥(perfectCore M₂)) := by
      obtain ⟨e₂⟩ := nonempty_perfectCore_mulEquiv iso2
      rw [hc2] at e₂
      exact CFSG.Quasithin.H13.IsL2Quot.of_mulEquiv
        (CFSG.Quasithin.Fan86.Univ.oTwoQuotMulEquiv e₂) h2
    exact not_isL2Quot_perfectCore_p0 σ hσ3 (by omega) hK hK4 φ hM hq'
  have hd2' : d4Index j₂ = D4.fa1 := by
    rcases hdich (d4Index j₂) with h | h
    · exact absurd h hry
    · exact h
  have hd1' : d4Index j₁ = D4.fa0 := by
    rcases hdich (d4Index j₁) with h | h
    · exact h
    · exact absurd (d4Index_injective (h.trans hd2'.symm)) hj
  have E : ∀ (L : Subgroup G) (M : Subgroup Y) (j : Fin 2),
      perfectCore (L ⊔ bigB L1 L2 S) = L → (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      perfectCore M = perfectCore
        (((graphFixedParabolic TwistTag.D4 K σ.toRingHom {d4Index j}).subgroupOf
          (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)).map φ.symm.toMonoidHom) →
      pCoreOf 2 (L ⊔ bigB L1 L2 S) = pCoreOf 2 L →
      Nonempty (↥(pCoreOf 2 (L ⊔ bigB L1 L2 S)) ≃*
        ↥(graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {d4Index j})) := by
    intro L M j hc ψ hd ho
    obtain ⟨e⟩ := nonempty_perfectCore_mulEquiv ψ
    rw [hc, hd] at e
    obtain ⟨e'⟩ := nonempty_pCore_equiv_d4 (K := K) σ φ (d4Index j)
      (by
        rcases hdich (d4Index j) with h | h
        · rw [h]; exact parabolicFacts_a0 σ hσ3 hK4
        · rw [h]; exact parabolicFacts_a1 σ hσ3)
      (by
        rcases hdich (d4Index j) with h | h
        · rw [h]; exact hne0
        · rw [h]; exact hne1)
    exact ⟨(MulEquiv.subgroupCongr ho).trans ((pCoreOfMulEquiv e 2).trans e')⟩
  obtain ⟨e1⟩ := E L1 M₁ j₁ hc1 iso1 hd₁ ho1
  obtain ⟨e2⟩ := E L2 M₂ j₂ hc2 iso2 hd₂ ho2
  exact ⟨⟨e1.trans (MulEquiv.subgroupCongr (by rw [hd1']))⟩,
    ⟨e2.trans (MulEquiv.subgroupCongr (by rw [hd2']))⟩⟩

private theorem d4q_exists_radical_equivs {G : Type} [Group G] [Finite G]
    {L1 L2 S : Subgroup G} {f : ℕ}
    (hMFf : HasModelFacts (IsLieOverTwo .trialityD4 0 f)) (hf : 2 ≤ f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f))
    (hc1 : perfectCore (L1 ⊔ bigB L1 L2 S) = L1)
    (hc2 : perfectCore (L2 ⊔ bigB L1 L2 S) = L2)
    (ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1)
    (ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (σ : K ≃+* K),
      Nat.card K = (2 ^ f) ^ 3 ∧ (∀ c, σ c = c ^ (2 ^ f)) ∧
      Nonempty (↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ≃* ↥(Q0 σ)) ∧
      Nonempty (↥(pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) ≃* ↥(Q1 σ)) := by
  obtain ⟨Y, _, hY, T, M₁, M₂, hp, ⟨iso0⟩⟩ := hA
  obtain ⟨hfinY, -⟩ := hMFf Y hY
  haveI : Finite Y := hfinY
  have hX : ChevalleyExceptionalModel Y .trialityD4 2 f :=
    (chevalley_of_lieModel hY (by decide)).2
  obtain ⟨K, _, _, σ, φ, hK, hσ, hU, hres, -⟩ := even_rank_two_residual_triality hX hp.1
  haveI : CharP K 2 := charP_two_of_card (f := f) (by omega) hK
  have hσ3 : σ.toRingHom ^ 3 = 1 := sigma_cube hK σ hσ
  have hk4 : 4 ≤ Nat.card ↥(trialityFixedField K σ.toRingHom) := by
    rw [card_fixedField (f := f) (by omega) hK σ hσ]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
      _ = (2 ^ f) ^ 1 := (pow_one _).symm
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_right (by positivity) (by norm_num)
  exact ⟨K, inferInstance, inferInstance, σ, hK, hσ,
    d4q_model_equivs (f := f) hf σ hσ3 hK hK4 hk4 φ hp hres hU iso0.φ1 iso0.φ2 hc1 hc2 ho1 ho2
      h1 h2⟩

private theorem d4q_radicals {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hMFf : HasModelFacts (IsLieOverTwo .trialityD4 0 f)) (hF : F112Hyp L1 L2 S) (hf : 2 ≤ f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f))
    (hQ0 : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}, 1 ≤ f →
      Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ (2 ^ f)) →
        IsSpecialPow 2 (2 ^ f) 4 ↥(Q0 σ))
    (hQ1 : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}, 1 ≤ f →
      Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ (2 ^ f)) →
        Nat.card ↥(Q1 σ) = (2 ^ f) ^ 11) :
    IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S)) ∧
      Nat.card (pCoreOf 2 (L2 ⊔ bigB L1 L2 S)) = (2 ^ f) ^ 11 := by
  have h3f : 2 ≤ 3 * f := by omega
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hF.1 h3f h1 hf h2 hMFf hA
  obtain ⟨hB, hV1, hV2⟩ := vFact_of_hasModelFacts_of_isL2Quot h3f h1 hf h2 hMFf hA
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hc2 := perfectCore_vertex hB2 hB hPO.2.1
  have hn1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hB1
  have hn2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hB2
  have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
    have := hV1.1
    rw [hc1] at this
    exact pCoreOf_eq_of_odd le_sup_left hn1 this
  have ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
    have := hV2.1
    rw [hc2] at this
    exact pCoreOf_eq_of_odd le_sup_left hn2 this
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e1⟩, ⟨e2⟩⟩ :=
    d4q_exists_radical_equivs hMFf hf h1 h2 hA hc1 hc2 ho1 ho2
  haveI : CharP K 2 := charP_two_of_card (f := f) (by omega) hK
  refine ⟨IsSpecialPow.of_mulEquiv e1.symm (hQ0 K σ (by omega) hK hσ), ?_⟩
  rw [Nat.card_congr e2.toEquiv]
  exact hQ1 K σ (by omega) hK hσ

private theorem d4q_center {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {f : ℕ}
    (hMFf : HasModelFacts (IsLieOverTwo .trialityD4 0 f)) (hF : F112Hyp L1 L2 S) (hf : 2 ≤ f)
    (h1 : IsL2Quot (3 * f) (oTwoQuot ↥L1)) (h2 : IsL2Quot f (oTwoQuot ↥L2))
    (hA : IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .trialityD4 0 f))
    (hs : IsSpecialPow 2 (2 ^ f) 4 ↥(pCoreOf 2 (L1 ⊔ bigB L1 L2 S))) :
    centerOf S ≤ Subgroup.centralizer (L2 : Set G) →
      centerOf S ≤ Subgroup.centralizer (L1 : Set G) := by
  have h3f : 2 ≤ 3 * f := by omega
  have hPO := perfectOver_of_hasModelFacts_of_isL2Quot hF.1 h3f h1 hf h2 hMFf hA
  obtain ⟨hB, hV1, -⟩ := vFact_of_hasModelFacts_of_isL2Quot h3f h1 hf h2 hMFf hA
  obtain ⟨hB1, -⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hn1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hB1
  have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
    have := hV1.1
    rw [hc1] at this
    exact pCoreOf_eq_of_odd le_sup_left hn1 this
  have hct1 : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hQS1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := by
    have hsy := hF.1.h1.sylow
    rw [inf_eq_left.mpr hPO.2.2.1] at hsy
    have hle := hsy.le_of_normalizes (pCoreOf_le 2 L1) (le_normalizer_pCoreOf 2 L1)
      (pCoreOf_isPGroup 2 L1)
    exact ho1 ▸ hle
  have hp1 : ⁅L1, L1⁆ = L1 := (perfectCore_eq_self_iff L1).mp hPO.1
  intro _
  refine centerOf_le_centralizer_of_card hp1 le_sup_left hct1
    (hPO.2.2.1.trans le_sup_left) hQS1 h3f h1 ?_ ?_
  · rw [hs.2.2]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro z hz
    obtain ⟨-, h | h⟩ := hs.1
    · exact h.2 z
    · exact h.2.2 z hz

theorem y9D4q_of_facts
    (hMF : ∀ f : ℕ, 2 ≤ f → HasModelFacts (IsLieOverTwo .trialityD4 0 f))
    (hQ0 : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}, 1 ≤ f →
      Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ (2 ^ f)) →
        IsSpecialPow 2 (2 ^ f) 4 ↥(Q0 σ))
    (hQ1 : ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) {f : ℕ}, 1 ≤ f →
      Nat.card K = (2 ^ f) ^ 3 → (∀ c, σ c = c ^ (2 ^ f)) →
        Nat.card ↥(Q1 σ) = (2 ^ f) ^ 11) :
    Y9D4q := by
  intro G _ _ L1 L2 S f hF hf h1 h2 hA
  have hMFf : HasModelFacts (IsLieOverTwo .trialityD4 0 f) := hMF f hf
  obtain ⟨hs, hc⟩ := d4q_radicals hMFf hF hf h1 h2 hA hQ0 hQ1
  exact ⟨d4q_center hMFf hF hf h1 h2 hA hs, hs, hc,
    perfectOver_of_hasModelFacts_of_isL2Quot hF.1 (by omega) h1 hf h2 hMFf hA⟩

theorem y9D4q : Y9D4q :=
  y9D4q_of_facts hasModelFacts_d4 (fun _ _ _ σ => isSpecialPow_d4Q0 σ)
    (fun _ _ _ σ => card_d4Q1 σ)

end Main

end CFSG.Quasithin.F112R
