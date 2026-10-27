module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSSolv
import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS

open CFSG CFSG.GH74.GLS CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14

variable {Y : Type} [Group Y] [Finite Y]

@[expose] def conjAct {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y)) :
    ↥B →* MulAut ↥W :=
  W.normalizerMonoidHom.comp (Subgroup.inclusion hBW)

theorem conjAct_apply {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y)) (b : ↥B)
    (w : ↥W) : ((conjAct hBW b w : ↥W) : Y) = (b : Y) * w * (b : Y)⁻¹ :=
  rfl

theorem mem_fixSub_conjAct {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y))
    (w : ↥W) : w ∈ fixSub (conjAct hBW) ↔ (w : Y) ∈ Subgroup.centralizer (B : Set Y) := by
  rw [mem_fixSub, Subgroup.mem_centralizer_iff]
  constructor
  · intro h b hb
    have := congrArg Subtype.val (h ⟨b, hb⟩)
    rw [conjAct_apply] at this
    calc b * (w : Y) = b * w * b⁻¹ * b := by group
      _ = w * b := by rw [this]
  · intro h b
    apply Subtype.ext
    rw [conjAct_apply, h b b.2]
    group

theorem signalizer_data {W B : Subgroup Y} (hBW : B ≤ Subgroup.normalizer (W : Set Y)) :
    (pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (B : Set Y))).subgroupOf W ≤ fixSub (conjAct hBW) ∧
      fixSub (conjAct hBW) ≤ Subgroup.normalizer
        (((pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (B : Set Y))).subgroupOf W : Subgroup ↥W) :
          Set ↥W) ∧
      Nat.Coprime 3 (Nat.card
        ((pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (B : Set Y))).subgroupOf W)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := W ⊓ Subgroup.centralizer (B : Set Y) with hC
  have hOC : pPrimeCoreOf 3 C ≤ C := pPrimeCoreOf_le 3 C
  have hOW : pPrimeCoreOf 3 C ≤ W := hOC.trans inf_le_left
  refine ⟨fun k hk => (mem_fixSub_conjAct hBW k).mpr (hOC (Subgroup.mem_subgroupOf.mp hk)).2,
    ?_, ?_⟩
  · intro w hw
    have hwC : (w : Y) ∈ C := ⟨w.2, (mem_fixSub_conjAct hBW w).mp hw⟩
    rw [Subgroup.mem_normalizer_iff]
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp (le_normalizer_pPrimeCoreOf 3 C hwC) (k : Y)
    simpa using this
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOW).toEquiv]
    exact coprime_card_pPrimeCoreOf 3 C

theorem card_map_mul_card_ker_of_le' {G G' : Type*} [Group G] [Group G'] [Finite G] (f : G →* G')
    {H : Subgroup G} (h : f.ker ≤ H) : Nat.card (H.map f) * Nat.card f.ker = Nat.card H := by
  have h1 := Subgroup.card_ker_mul_card_range (f.domRestrict H)
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv] at h1
  rw [mul_comm]
  exact h1

section Theta

variable {H : Type*} [Group H] [Finite H]

theorem theta_characteristic (H : Type*) [Group H] [Finite H] :
    (aschbacherSolvableCore 3 H).Characteristic :=
  (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.1

theorem theta_not_dvd (H : Type*) [Group H] [Finite H] :
    ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 H) :=
  (solvable_prime_complement_core_characterization (H := H) Nat.prime_three).2.2.1

end Theta

section Image

variable {W P Q D₀ : Subgroup Y}

theorem inSubgroup_theta_le (W : Subgroup Y) :
    inSubgroup (aschbacherSolvableCore 3) W ≤ pPrimeCoreOf 3 W := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : (aschbacherSolvableCore 3 ↥W) ≤ CFSG.pPrimeCore 3 ↥W :=
    haveI := theta_characteristic ↥W
    le_sSup ⟨inferInstance,
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (theta_not_dvd _)⟩
  exact Subgroup.map_mono hc

theorem map_ne_bot (hQW : Q ≤ W) (hQO : ¬ Q ≤ pPrimeCoreOf 3 W) :
    (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) ≠ ⊥ := by
  intro h
  apply hQO
  intro q hq
  have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W) (⟨q, hQW hq⟩ : ↥W) = 1 := by
    have : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W) (⟨q, hQW hq⟩ : ↥W) ∈
        (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hq)
    rw [h] at this
    exact this
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact inSubgroup_theta_le W ⟨_, h1, rfl⟩

theorem map_le_centralizer_pCore' (hD : IsPGroup 3 D₀) (hDW : D₀ ≤ Subgroup.normalizer (W : Set Y))
    (hQW : Q ≤ W) (hQO : Q ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (D₀ : Set Y))) :
    (Q.subgroupOf W).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥W)) ≤
      Subgroup.centralizer (CFSG.pCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) :
        Set (↥W ⧸ aschbacherSolvableCore 3 ↥W)) := by
  obtain ⟨hKfix, hKn, hK3⟩ := signalizer_data hDW
  haveI := theta_characteristic ↥W
  exact map_le_centralizer_pCore hD (conjAct hDW) _ (theta_not_dvd _)
    (fun q hq => Subgroup.mem_subgroupOf.mpr (hQO (Subgroup.mem_subgroupOf.mp hq))) hKfix hKn hK3

theorem exists_component_not_le_centralizer
    (ha : CFSG.pPrimeCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) = ⊥)
    {Qs : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W)} (hQs1 : Qs ≠ ⊥)
    (hQs3 : Nat.Coprime 3 (Nat.card Qs))
    (hQsF : Qs ≤ Subgroup.centralizer (CFSG.pCore 3 (↥W ⧸ aschbacherSolvableCore 3 ↥W) :
      Set (↥W ⧸ aschbacherSolvableCore 3 ↥W))) :
    ∃ J : Subgroup (↥W ⧸ aschbacherSolvableCore 3 ↥W), IsComponent J ∧
      ¬ Qs ≤ Subgroup.centralizer (J : Set (↥W ⧸ aschbacherSolvableCore 3 ↥W)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Ws := ↥W ⧸ aschbacherSolvableCore 3 ↥W
  by_contra hno
  push Not at hno
  have hF : CFSG.fittingSubgroup Ws = CFSG.pCore 3 Ws :=
    CFSG.Fitting_eq_pcore Ws 3 ha
  have hQsC : Qs ≤ Subgroup.centralizer (CFSG.generalizedFitting Ws : Set Ws) := by
    rw [CFSG.generalizedFitting.eq_sup, Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · rw [hF, ← Subgroup.le_centralizer_iff]
      exact hQsF
    · rw [CFSG.layer.eq_sSup]
      refine sSup_le fun J hJ => ?_
      rw [← Subgroup.le_centralizer_iff]
      exact hno J hJ
  have hQsF' : Qs ≤ CFSG.pCore 3 Ws :=
    hF ▸ hQsC.trans (CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup Ws)
  apply hQs1
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact eq_one_of_mem_pGroup_of_coprime CFSG.pCore_isPGroup hQs3 (hQsF' hx) hx

end Image

end CFSG.RankThree.PartTwo.Sec14.Ronan148B.PS
