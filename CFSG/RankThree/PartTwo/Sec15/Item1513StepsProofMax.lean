module

public import CFSG.RankThree.PartTwo.Sec15.Item1513StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.Goldschmidt.Steps.G310Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof1511 CFSG.RankThree.PartTwo.Sec15.Proof1513

@[expose] noncomputable def Step1513MaxJ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (K : Subgroup G), Ctx1513 G A c L a K →
      ∀ w ∈ K ⊓ Subgroup.normalizer (A : Set G), w ^ 3 = 1 →
        Nat.card (A ⊓ Subgroup.centralizer ({w} : Set G) : Subgroup G) = 9 →
        ∀ T : Subgroup G, Maximal (fun T' => T' ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ T' ≠ ⊥ ∧
            w ∈ Subgroup.normalizer (T' : Set G)) T →
          oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (T : Set G))) ≠ ⊥ →
            ∃ J ∈ scriptY0 A (lB A), w ∈ Subgroup.normalizer (J : Set G)

namespace Proof1513Steps

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQPiStar_of_maximal {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h146 : Item146 A (lB A)) {w : G} (hwA : w ∈ Subgroup.normalizer (A : Set G))
    (hw3 : w ^ 3 = 1) {T : Subgroup G}
    (hT : Maximal (fun T' => T' ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ T' ≠ ⊥ ∧
      w ∈ Subgroup.normalizer (T' : Set G)) T)
    (hI : oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (T : Set G))) = ⊥) :
    T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTQ, hT1, hwT⟩ := hT.prop
  set NT := Subgroup.normalizer (T : Set G) with hNT
  set X := delta A (lB A) NT with hX
  have hX3 : ¬ 3 ∣ Nat.card X := by
    intro h3
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
    have hxI : (x : G) ∈ oPrimeResidualOf 3 X := by
      rw [oPrimeResidualOf_eq_closure]
      refine Subgroup.subset_closure ⟨x.2, 1, ?_⟩
      rw [pow_one, ← Subgroup.coe_pow, ← hx, pow_orderOf_eq_one, Subgroup.coe_one]
    rw [hI, Subgroup.mem_bot] at hxI
    have h1 : orderOf x = 1 := orderOf_eq_one_iff.mpr (Subtype.ext hxI)
    omega
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := le_normalizer_sSup fun Q hQ => hQ.1.1.2.2
  have hwX : w ∈ Subgroup.normalizer (X : Set G) := by
    have hwT' : T.map (MulAut.conj w).toMonoidHom = T :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hwT
    have h1 : X.map (MulAut.conj w).toMonoidHom = X := by
      rw [hX, Sec17.HeadProof.map_conj_delta hwA, hNT, Subgroup.map_equiv_normalizer_eq, hwT']
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h1
  have hXQ : X ∈ scriptQ A (lB A) := by
    have hXinv : X ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
      ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
    have h1 := delta_mem_scriptQ h.isE27 h146 hXinv
    rwa [hX, delta_delta] at h1
  have hTQ' : T ∈ scriptQ A (lB A) := hTQ.1.1
  have hTX : T ≤ X := le_delta hTQ' Subgroup.le_normalizer
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := hTQ'.1.2.2
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using h.isElemAbelian.2 _ g.2)⟩
  set R := Subgroup.zpowers w ⊔ A with hR
  have hR3 : IsPGroup 3 R := IsPGroup.to_sup_of_normal_right'
    (isPGroup_zpowers_of_pow_three hw3) hA3 (Subgroup.zpowers_le.mpr hwA)
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := sup_le (Subgroup.zpowers_le.mpr hwX) hAX
  have hRT : R ≤ Subgroup.normalizer (T : Set G) := sup_le (Subgroup.zpowers_le.mpr hwT) hAT
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hTQ
  obtain ⟨S, hS, hTS, hRS⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
    Nat.prime_three Nat.prime_two hR3 hX3 hRX hTX hT2 hRT
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := le_sup_right.trans hRS
  have hwS : w ∈ Subgroup.normalizer (S : Set G) :=
    hRS (Subgroup.mem_sup_left (Subgroup.mem_zpowers w))
  have hSQ : S ∈ scriptQPi A (lB A) ⊤ (piOf 2) :=
    ⟨⟨mem_scriptQ_of_le hXQ hS.1 hAS, le_top⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two S).mpr hS.2.1⟩
  have hS1 : S ≠ ⊥ := fun h0 => hT1 (le_bot_iff.mp (h0 ▸ hTS))
  have hTSeq : T = S := hT.eq_of_le ⟨hSQ, hS1, hwS⟩ hTS
  refine ⟨hTQ, fun T' hT' hTT' => ?_⟩
  have hT'2 : IsPGroup 2 T' := isPGroup_of_mem_scriptQPi Nat.prime_two hT'
  set N' := T' ⊓ NT with hN'
  have hAN' : A ≤ Subgroup.normalizer (N' : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hT'.1.1.1.2.2 hx, (hAT.trans Subgroup.le_normalizer) hx⟩
  have hN'Q : N' ∈ scriptQ A (lB A) := mem_scriptQ_of_le hT'.1.1 inf_le_left hAN'
  have hN'X : N' ≤ X := le_delta hN'Q inf_le_right
  have hN'2 : IsPGroup 2 N' := hT'2.to_le inf_le_left
  have hTN' : T ≤ N' := le_inf hTT' Subgroup.le_normalizer
  have hN'eq : N' = T := by
    rw [hTSeq] at hTN' ⊢
    exact hS.2.2 N' hN'X hN'2 hTN'
  by_contra hT'T
  set IP : Subgroup ↥T' := T.subgroupOf T' with hIP
  have hIPlt : IP < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hT'T fun x hx => ?_
    have hxIP : (⟨x, hx⟩ : ↥T') ∈ IP := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hxIP
  have : Group.IsNilpotent ↥T' := hT'2.isNilpotent
  have hlt : IP < Subgroup.normalizer (IP : Set ↥T') :=
    Group.normalizerCondition_of_isNilpotent (G := ↥T') IP hIPlt
  obtain ⟨x, hxN, hxIP⟩ := IsConcreteLE.exists_of_lt hlt
  have hxNT : (x : G) ∈ NT := by
    have hxsub : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf T' := by
      rw [Subgroup.subgroupOf_normalizer_eq hTT']
      exact hxN
    exact Subgroup.mem_subgroupOf.mp hxsub
  have hxT : (x : G) ∈ T := by
    rw [← hN'eq]
    exact ⟨x.2, hxNT⟩
  exact hxIP (Subgroup.mem_subgroupOf.mpr hxT)

end Proof1513Steps

open Proof1513Steps

theorem step1513Max_of
    (h131 : Item131) (h133 : Item133) (h134 : Item134)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h137 : Item137) (hcl : Claim1515M12)
    (hnt : Step1513NoTransv) (h146 : Item146S14) (h1511 : Item1511R)
    (hpt : Step1513MeetsPoint) (hJ : Step1513MaxJ) : Step1513Max := by
  intro G _ _ A c L a K hctx w hwKW hw3 hwC9 hT
  have h := hctx.toSec15R
  have hD := h.toSec13Data
  obtain ⟨T₀, hT₀, hT₀1, hwT₀⟩ := hT
  obtain ⟨T, -, hTmax⟩ := Finite.exists_le_maximal (p := fun T' =>
    T' ∈ scriptQPi A (lB A) ⊤ (piOf 2) ∧ T' ≠ ⊥ ∧ w ∈ Subgroup.normalizer (T' : Set G))
    ⟨hT₀, hT₀1, hwT₀⟩
  by_cases hI : oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (T : Set G))) = ⊥
  · exact ⟨T, mem_scriptQPiStar_of_maximal h.toSec14Std (h146 G A c L h.toSec14Std) hwKW.2 hw3
      hTmax hI, hTmax.prop.2.2⟩
  · exfalso
    obtain ⟨J, hJ0, hwJ⟩ := hJ G A c L a K hctx w hwKW hw3 hwC9 T hTmax hI
    have hwA : w ∈ Subgroup.normalizer (A : Set G) := hwKW.2
    have hwC : w ∉ Subgroup.centralizer (A : Set G) := by
      intro hwc
      have hAC : A ⊓ Subgroup.centralizer ({w} : Set G) = A := inf_of_le_left fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hwc x hx)
      rw [hAC, hD.card_eq] at hwC9
      norm_num at hwC9
    obtain ⟨-, htypes⟩ := cases_of_irreducible h131 h hctx.card_inf hctx.irreducible
    obtain ⟨p, e, hp, he, hL3⟩ : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rcases htypes with h1 | h1 | h1
      · exact h1
      · exact (hnt G A c L h (Or.inr h1) w ⟨hctx.normalizer_le hwA, hwA⟩ hw3 hwC9).elim
      · exact (hnt G A c L h (Or.inl h1) w ⟨hctx.normalizer_le hwA, hwA⟩ hw3 hwC9).elim
    obtain ⟨c', L', hc', hL', hm⟩ := hpt G A c L h (fun b Lb hb hLb =>
      not_j2_of_irreducible h131 h134 h48 h415 h hctx.irreducible hctx.card_inf hb hLb) J hJ0
    have hmL := meetsY4_of_point h131 h133 h134 h48 h415 h137 hcl h hctx.irreducible
      hctx.card_inf hctx.normalizer_le hJ0
      (fun c'' L'' h'' p' e' _ he' hiso hm' P hAP hP =>
        (h1511 G A c'' L'' h'' p' e' he' hiso J hJ0 hm' P hAP hP).1) hc' hL' hm
    exact false_of_mem_normalizer_of_omega hD hJ0.1.1.2
      (fun P hAP hP => (h1511 G A c L h p e he hL3 J hJ0 hmL P hAP hP).2.2.2.2)
      hctx.normalizer_le hwA hwJ hw3 hwC

end CFSG.RankThree.PartTwo.Sec15
