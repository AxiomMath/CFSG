module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K341Reduce

import CFSG.RankThree.PartTwo.Sec4.Item422ProofFaithful
import CFSG.RankThree.GroupTheory.CentralLineDetection
import TauCeti.Algebra.Group.Subgroup.ModularLaw

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.Item422Proof

@[expose] def OutFixCentralThreePRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.IsQuasisimple X →
    CFSG.Assembly.InCatalog (X ⧸ Subgroup.center X) →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3 →
    ∀ z ∈ Subgroup.center X, orderOf z = 3 →
    ∀ σ τ : MulAut X, σ z = z → τ z = z →
      σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range

set_option linter.unusedSectionVars false

theorem local422_of_fixComm_faithful
    {G : Type} [Group G] [Finite G]
    (hS4 : CFSG.IsKGroup G) (hrk : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3)
    (A : Subgroup G)
    (hmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A)
    (h27 : Nat.card A = 27)
    (hnorm : ∀ L ∈ thetaComponents 3 G, A ≤ Subgroup.normalizer (L : Set G))
    (c : G) (hcA : c ∈ A) (hcZ : c ∈ Subgroup.center G) (hc1 : c ≠ 1)
    (hKF : ∀ K K' : Subgroup (G ⧸ aschbacherSolvableCore 3 G), IsComponent K →
      IsComponent K' → K ≠ K' →
      A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊓
        Subgroup.centralizer (K : Set _) =
          Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) →
      A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊓
        Subgroup.centralizer (K' : Set _) =
          Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range) :
    (haveI : (Subgroup.zpowers c).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcZ);
      thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
        aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)) ∨
    ∃ L ∈ thetaComponents 3 G, Nat.card (autThetaQuot A L) = 9 ∧
      thetaAlpha 3 ((autThetaQuot A L).subgroupOf (autThetaQuot ⊤ L)) ≠ ⊥ := by
  have hZn : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcZ)
  by_cases h1 : thetaAlpha 3 (A.map (QuotientGroup.mk' (Subgroup.zpowers c))) ≤
      aschbacherSolvableCore 3 (G ⧸ Subgroup.zpowers c)
  · exact Or.inl h1
  right
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hmax.1
  have hAE : IsElementaryAbelian 3 A :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 A).mpr hAe
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hAe.2 x x.2)⟩
  have hAcard : Nat.card A = 3 ^ 3 := by rw [h27]; norm_num
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hAe.2 c hcA) hc1
  have hZA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.mpr hcA
  have hZc : Subgroup.zpowers c ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hcZ
  have hZp : Nat.card (Subgroup.zpowers c) = 3 := by rw [Nat.card_zpowers, hc3]
  obtain ⟨C', hC'⟩ := IsElementaryAbelian.exists_isCompl 3 A ((Subgroup.zpowers c).subgroupOf A)
  set B := C'.map A.subtype with hB
  have hBA : B ≤ A := Subgroup.map_subtype_le _
  have hBZ : Disjoint B (Subgroup.zpowers c) := by
    rw [disjoint_iff, eq_bot_iff]
    rintro _ ⟨⟨y, hy, rfl⟩, hxZ⟩
    have hyZ : y ∈ (Subgroup.zpowers c).subgroupOf A := Subgroup.mem_subgroupOf.mpr hxZ
    have hmem : y ∈ (Subgroup.zpowers c).subgroupOf A ⊓ C' := ⟨hyZ, hy⟩
    rw [hC'.inf_eq_bot, Subgroup.mem_bot] at hmem
    rw [hmem, map_one]
    exact Subgroup.one_mem _
  have hBZA : B ⊔ Subgroup.zpowers c = A := by
    have h := congrArg (Subgroup.map A.subtype) hC'.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZA,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [sup_comm]
    exact h
  obtain ⟨L, hL, a, ha, hker, -, hcard, hQK⟩ := central_line_faithful_component_detection
    Nat.prime_three hAE hAcard (Subgroup.zpowers c) hZA hZc hZp hnorm h1 B hBA hBZ hBZA
  obtain ⟨-, hBb, -, hBbcard, hQmap, -, hθX, hAK⟩ := central_line_setup Nat.prime_three hAE
    hAcard (Subgroup.zpowers c) hZc hZp hnorm h1 B hBA hBZ hBZA
  have hinj := injOn_mk_of_isPGroup Nat.prime_three hAp
  have haT : ∀ (x : A) (hxN : (x : G) ∈ Subgroup.normalizer (L : Set G)),
      a x = thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) := by
    intro x hxN
    ext y
    induction y using QuotientGroup.induction_on with
    | H l =>
      rw [ha x l (L.normalizerMonoidHom ⟨x, hxN⟩ l) (normalizerMonoidHom_apply_coe hxN l),
        thetaQuotMulAut_mk]
  have hAut : autThetaQuot A L = a.range := by
    ext σ
    rw [mem_autThetaQuot_iff, MonoidHom.mem_range]
    constructor
    · rintro ⟨h, hN, hA, rfl⟩
      exact ⟨⟨h, hA⟩, haT ⟨h, hA⟩ hN⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, hnorm L hL x.2, x.2, (haT x (hnorm L hL x.2)).symm⟩
  refine ⟨L, hL, by rw [hAut, hcard]; norm_num, ?_⟩
  obtain ⟨η, a', -, hη, ha', -, -, hkerC, -, -⟩ :=
    theta_component_quotient_action Nat.prime_three hL A (hnorm L hL)
  have haa' : ∀ x : A, a x = a' x := by
    intro x
    ext y
    induction y using QuotientGroup.induction_on with
    | H l =>
      have hxl : (x : G) * l * (x : G)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hnorm L hL x.2) l).mp l.2
      rw [ha x l ⟨_, hxl⟩ rfl, ha' x l ⟨_, hxl⟩ rfl]
  have hfaith : ∀ x ∈ A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)),
      x ∈ Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup _) : Set _) ↔
        x ∈ Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hkerC ⟨x, hx⟩, ← haa', hker]
    constructor
    · intro hxZ
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem _ hxZ
    · intro hxz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxz
      have hck : c ^ k = x := hinj (A.zpow_mem hcA k) hx (by rw [map_zpow, hk])
      subst hck
      exact Subgroup.zpow_mem_zpowers c k
  have hKX : CFSG.IsKGroup (G ⧸ aschbacherSolvableCore 3 G) := theta_quotient_isKGroup hS4
  have hcbZ : QuotientGroup.mk' (aschbacherSolvableCore 3 G) c ∈
      Subgroup.center (G ⧸ aschbacherSolvableCore 3 G) :=
    Subgroup.map_center_le_center (QuotientGroup.mk'_surjective _) (Subgroup.mem_map_of_mem _ hcZ)
  have hcb3 : orderOf (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) = 3 := by
    refine orderOf_eq_prime (by rw [← map_pow, hAe.2 c hcA, map_one]) fun h => hc1 ?_
    exact hinj hcA A.one_mem (by rw [h, map_one])
  have hBcard9 : Nat.card (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) = 9 := by
    rw [hBbcard]; norm_num
  have hBZX : B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊓
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨b, hb, rfl⟩, hbz⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
    have hbc : c ^ k = b := hinj (A.zpow_mem hcA k) (hBA hb) (by rw [map_zpow, hk])
    have hbZ : b ∈ B ⊓ Subgroup.zpowers c := ⟨hb, hbc ▸ Subgroup.zpow_mem_zpowers c k⟩
    rw [disjoint_iff.mp hBZ, Subgroup.mem_bot] at hbZ
    rw [hbZ, map_one]
    exact Subgroup.one_mem _
  have hABZX : A.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) =
      B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊔
        Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) := by
    rw [← hBZA, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hQ : ¬ thetaAlpha 3 (B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G))) ≤
      Subgroup.centralizer ((L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) :
        Subgroup _) : Set _) := by
    rw [← hQmap]
    exact hQK
  have hKF_local : ∀ K : Subgroup (G ⧸ aschbacherSolvableCore 3 G), IsComponent K →
      K ≠ L.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) →
      B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ⊓
        Subgroup.centralizer (K : Set _) = ⊥ →
      ∀ z ∈ Subgroup.center K, orderOf z = 3 → ∀ σ τ : MulAut K, σ z = z → τ z = z →
        σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range := by
    haveI : (Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcbZ)
    intro K hK hne hBbot
    have hcC : Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) ≤
        Subgroup.centralizer (K : Set _) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun y _ =>
        Subgroup.mem_center_iff.mp hcbZ y)
    have hBN : B.map (QuotientGroup.mk' (aschbacherSolvableCore 3 G)) ≤ Subgroup.normalizer
        ((Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 G) c) : Subgroup _) :
          Set _) :=
      le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
    refine hKF K _ hK (isComponent_map_of_mem_thetaComponents Nat.prime_three hL) hne ?_ ?_
    · rw [hABZX, inf_comm, ← Subgroup.inf_sup_assoc_of_le hBN hcC, inf_comm, hBbot, bot_sup_eq]
    · refine le_antisymm (fun x hx => (hfaith x hx.1).mp hx.2) fun x hx => ?_
      have hxA := Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem _ hcA) hx
      exact ⟨hxA, (hfaith x hxA).mpr hx⟩
  have hX := thetaAlpha_autIn_ne_bot_of_fixComm_faithful KFacts.kpSz hθX hKX hcbZ hcb3 hBb
    hBcard9 hBZX hABZX (fun u hu huC => mem_map_of_maximal hmax _
      three_not_dvd_card_aschbacherSolvableCore hu huC) hAK
    (isComponent_map_of_mem_thetaComponents Nat.prime_three hL) hfaith hQ hKF_local
  rw [← thetaAlpha_subgroupOf_map_ne_bot_iff' (MulAut.congr η), map_autThetaQuot_eq_autIn hL η hη,
    map_autThetaQuot_eq_autIn hL η hη, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)]
  exact hX

theorem local422_of_outFixCentralThreePRank (hKF : OutFixCentralThreePRank) : Local422 := by
  intro G _ _ hK hr A hmax h27 hnorm c hcA hcZ hc1
  refine local422_of_fixComm_faithful hK hr A hmax h27 hnorm c hcA hcZ hc1
    fun K L hK' hL hKL _ _ => ?_
  have hKX : CFSG.IsKGroup (G ⧸ aschbacherSolvableCore 3 G) := theta_quotient_isKGroup hK
  have hrankX : CFSG.Assembly.RankThreeEven.localRank 3 (G ⧸ aschbacherSolvableCore 3 G) ≤ 3 :=
    (theta_quotient_core_and_ranks (G := G)).2.2.1.2.1.trans hr
  have hKcL : K ≤ Subgroup.centralizer (L : Set (G ⧸ aschbacherSolvableCore 3 G)) := by
    rcases CFSG.LocalCores.distinct_components_commute hK' hL with h | h
    · exact absurd h hKL
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact hKF K hK'.1 (hKX K (Subgroup.center K) hK'.1.2.1)
    ((pRank_top_le_localRank_of_le_centralizer hL.1 hKcL).trans hrankX)

theorem k341_of_outFixCentralThreePRank (h : OutFixCentralThreePRank) : K341 :=
  k341_of_local422 (local422_of_outFixCentralThreePRank h)

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
