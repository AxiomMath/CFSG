module

public import CFSG.Quasithin.Vol2.Ch3T313A
public import CFSG.Quasithin.Vol2.Ch3T313B
public import CFSG.Quasithin.Vol2.Ch11SecOE4F
public import CFSG.Quasithin.Vol2.Ch11SecOE2B

public section

namespace CFSG.Quasithin.H13

open Subgroup CFSG.Quasithin
open CFSG.Open (pCoreOf)
open CFSG.Quasithin.EmptyFaithfulMultiple (L3213.vOf)

theorem lemma3_2_13Consumed_of
    (h316 : Theorem316Statement) (h211 : U3.UniqueThreeCaseModelReduction) :
    NQBlock.Lemma3_2_13Consumed := by
  intro G _ _ T D hs hnab hQ hT hDm hDf hTD hDq p hp hp5 hCp
  classical
  have := hs
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  by_contra hXR
  obtain ⟨-, hamb, hcan⟩ :=
    NQCore.sylow_normalized_maximal_nonquasisimple_canonical_residual_structure
      NQCore.sylowNormalizedMaximalLocalUniqueNormalizer_holds
      NQBlock.sylowNormalizedLocalNormalComponent_proved hnab hQ hT hDm hDf hTD hDq
  have hcanp := hcan p hp hp5 hCp
  set X := nqPrimeResidualX D p with hXdef
  have hSC : NQCore.SCSetup T D X p :=
    { simple := hs
      nonabelian := hnab
      qtke := hQ
      sylow := hT
      maximal_local := hDm
      faithful_local := hDf
      le_normalizer := hTD
      not_quasisimple := hDq
      prime := hp
      five_le := hp5
      ambient := hamb
      canonical := hcanp }
  have hUX := NQCore.unique_maximal_overgroup_of NQCore.stmtSCComponentOrbits_holds
    NQCore.stmtSCNormalExclusion_holds NQCore.stmtSCPairedExclusion_holds hSC
  have hDc : D ∈ cComp (D ⊔ T) := cComp_of_isLocal hDm.1
  have hperf : ⁅D, D⁆ = D := perfect_of_mem_cComp hamb.cComp_self
  have hDX : normalizer (D : Set G) = normalizer (X : Set G) := hcanp.normalizer_eq
  have hX : IsXi T X := by
    have hpF := Nat.dvd_of_mem_primeFactors (NQCore.mem_primeFactors_fitting hCp)
    have h := Vol2.Ch11.tmp1_3_3_holds G T D p hs hnab hQ hT hDm.1 hDq hp hp2 hpF
    rwa [Vol2.Ch11.OE2.xiP_eq_map] at h
  have hsolv : Group.IsSolvable X := hcanp.solvable
  have hpow : ∀ x ∈ X, x ^ p ∈ pCoreOf 2 X := fun x hx =>
    T313.pow_mem_pCoreOf_of_exponent hcanp.exponent hx
  have hVne : L3213.vOf T X ≠ ⊥ :=
    T313.vOf_ne_bot hX hcanp.le (le_normalizer.trans hDX.le) hamb.charTwo_sup hXR
  obtain ⟨H, hH⟩ := Vol2.Ch11.OE4.exists_isHStar_of_perfect h211 hs hnab hQ hT hUX.1 hTD
    le_normalizer (ne_bot_of_mem_cComp hDc) hperf
  have hXTM : X ⊔ T ≤ normalizer (D : Set G) := sup_le (hcanp.le.trans le_normalizer) hTD
  have hyp : Hyp318 T (normalizer (D : Set G)) X (L3213.vOf T X) :=
    { inM := ⟨hUX.1, hTD⟩
      nonempty := ⟨H, hH⟩
      perfect := hX.1
      le_M := hcanp.le.trans le_normalizer
      normal := hDX.le
      unique := ⟨⟨hUX.1, hXTM⟩, fun M' hM' => hUX.2.2 M' hM'.1 hM'.2⟩
      reduced := EmptyFaithfulMultiple.L3213.isTwoReducedIn_vOf hT hX hsolv hVne
      centralizer := T313.pCoreOf_sup_eq_inf_centralizer_vOf hT hX hsolv hVne }
  have hq : qhatInt (X ⊔ T) (L3213.vOf T X) hyp.reduced.2.2.1 ≤ 2 := by
    rcases h316 G T hs hnab hQ hT _ (X ⊔ T) H (L3213.vOf T X) hyp.inM (hyp.hyp315 hT hH) with
      h1 | ⟨-, h2, -⟩ | h3
    · exact absurd h1 (hyp.not_exists_normal hH)
    · exact h2
    · exact (qhatInt_le_qInt _ _ _).trans h3
  have hp5' : p = 5 := by
    obtain ⟨h1, h2, h3, h5⟩ := EmptyFaithfulMultiple.L3213.autOn_vOf_facts hT hX hpow
    have hV := hyp.reduced.2.2.1
    have hO2 := EmptyFaithfulMultiple.L3213.pCoreOf_autOn_vOf_eq_bot hT hX hsolv hVne
    let _ := commGroupOfElemAbelian hV
    have hVsq : ∀ v : ↥(L3213.vOf T X), v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
    rcases (EmptyFaithfulMultiple.L3213.d2_13_data hVsq hp2 hq hO2 h1 h2
      (fun y => ⟨1, Subtype.ext (by simpa using h3 y y.2)⟩) h5).1 with h | h <;> omega
  subst hp5'
  have h25 := EmptyFaithfulMultiple.L3213.T313.prime_dvd_aut_eq_two_or_five hT hX hsolv hVne hq
    hpow (T313.relIndex_eq_of_isXi hX hp hpow)
  have hCN : ((sectionCentralizer X (pCoreOf 2 X)).subgroupOf
      (normalizer (X : Set G) ⊓ normalizer (pCoreOf 2 X : Set G))).Normal :=
    ⟨fun n hn g => by
      rw [mem_subgroupOf] at hn ⊢
      exact EmptyFaithfulMultiple.L3213.conj_mem_sectionCentralizer g.2.1 g.2.2 hn⟩
  have hDN : D ≤ normalizer (X : Set G) ⊓ normalizer (pCoreOf 2 X : Set G) :=
    le_inf (le_normalizer.trans hDX.le) (le_normalizer.trans hcanp.normalizer_eq_core.le)
  have hDC := T313.le_of_isPerfect_of_dvd hCN hDN hperf h25
  obtain ⟨d, hdD, hd⟩ := hcanp.nontrivial
  exact hd (T313.normalizerFrattiniConj_eq_one_of_mem d (hDC hdD))

end CFSG.Quasithin.H13
