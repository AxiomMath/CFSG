module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Ord
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340M
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Gagen1511WStar
public import CFSG.RankThree.PartTwo.Sec15.Gagen155R1L3Defs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofComp
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.GagenL3

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem res1Tau_of_q {Q Q' : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z)
    (hq : Q' (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Sylow155R1.Res1Tau Q' P A c L X K Y M T P' Yc z :=
  { τ with q := hq }

theorem eq_of_mem_lA_of_tau {Q : ∀ (X : Type) [Group X], Prop}
    {P : ∀ (Y : Type) [Group Y], Prop}
    {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z) (hQE9 : Sylow155R1.Res1QE9 Q)
    {c' : G} {L' : Subgroup G} (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') :
    L' = L := by
  have h3L : 3 ∣ Nat.card L := by
    refine Proof1515.three_dvd_card_of_thetaQuot ?_
    obtain ⟨E, -, hE9⟩ := (hQE9 _ τ.q).2
    have h3E : 3 ∣ Nat.card E := by rw [hE9]; norm_num
    exact h3E.trans (Subgroup.card_subgroup_dvd_card E)
  rw [τ.omega] at hc'
  exact Proof1515.eq_of_mem_lA_of_zpowers_eq τ.std h3L (Set.mem_singleton_iff.mp hc') hL'

theorem card_thetaQuot_dvd_card_img148_of_le {A Y L D : Subgroup G} [(ker148 A Y).Normal]
    (hLD : L ≤ D) (hDY : D ≤ Y ⊔ A)
    (hsimple : IsSimpleGroup (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card (img148 A Y D) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (aschbacherSolvableCore 3 ↥L).Normal := Subgroup.normal_of_characteristic _
  set f : ↥L →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion (hLD.trans hDY)) with hf
  have hker : f.ker ≤ aschbacherSolvableCore 3 ↥L := by
    have hn : (f.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))).Normal :=
      f.normal_ker.map _ (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
        (f.ker.map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) with hb | ht
    · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
      exact hb
    · exfalso
      have himg : f.ker.map L.subtype ≤ pPrimeCoreOf 3 Y := by
        rintro _ ⟨l, hl, rfl⟩
        exact mk'_ker148_eq_one_iff.mp hl
      have hk3 : Nat.Coprime 3 (Nat.card f.ker) := by
        have h := (coprime_card_pPrimeCoreOf 3 Y).coprime_dvd_right
          (Subgroup.card_dvd_of_le himg)
        rwa [Subgroup.card_map_of_injective L.subtype_injective] at h
      have hdvd : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∣ Nat.card f.ker := by
        have h1 := Subgroup.card_map_dvd f.ker (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
        rwa [ht, Subgroup.card_top] at h1
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hk3 (h3.trans hdvd)
  have hrange : f.range ≤ img148 A Y D := by
    rintro _ ⟨l, rfl⟩
    exact mem_img148_iff.mpr ⟨l, hLD.trans hDY l.2, hLD l.2, rfl⟩
  calc Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = (aschbacherSolvableCore 3 ↥L).index := rfl
    _ ∣ f.ker.index := Subgroup.index_dvd_of_le hker
    _ = Nat.card f.range := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    _ ∣ Nat.card (img148 A Y D) := Subgroup.card_dvd_of_le hrange

theorem card_img148_le_card_thetaQuot_of_caseTwo {A Y L : Subgroup G} [(ker148 A Y).Normal]
    (hL3 : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hLD : L ≤ deltaZero A (lB A) Y) (hDY : deltaZero A (lB A) Y ≤ Y ⊔ A)
    (hpt : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L)
    (h2 : Case148Two A (lB A) Y) :
    Nat.card (img148 A Y (deltaZero A (lB A) Y)) ≤
      Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  have h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    obtain ⟨E, -, hE9⟩ := hL3.2.2
    have h3E : 3 ∣ Nat.card E := by rw [hE9]; norm_num
    exact h3E.trans (Subgroup.card_subgroup_dvd_card E)
  obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
  have hLL : L' = L := hpt hc' hL'
  rcases hcases with ⟨⟨φ⟩⟩ | ⟨hQ', ⟨φ⟩⟩ | ⟨p, f, e, hpq, hf, he, hiso, hε⟩ | ⟨⟨φ⟩, -⟩
  ·
    rw [Nat.card_congr φ.toEquiv, hLL]
  ·
    rw [hLL] at hQ'
    rw [Nat.card_congr φ.toEquiv]
    exact card_alternatingGroup_seven_le_of_case148Two_ii hQ'
  ·
    rw [hLL] at hiso
    have : Fact p.Prime := hpq
    exact (card_eq_of_isoLThreePi_of_isLThreeEpsAt_of_dvd hf he hiso hε
      (card_thetaQuot_dvd_card_img148_of_le hLD hDY hL3.2.1 h3)).le
  ·
    rw [hLL] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hL3.1)).false φ).elim


@[expose] def Res1L3NoFive (Q : ∀ (X : Type) [Group X], Prop)
    (P : ∀ (Y : Type) [Group Y], Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
    (Yc : Subgroup (Res1Q A L)) (z : G), Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z →
    ∀ Y' : Subgroup G, Y' ∈ scriptY2 A → X ≤ Y' → generalizedFitting ↥Y' = CFSG.pCore 2 ↥Y' →
      ∀ _ : (ker148 A Y').Normal, ¬ Case148Five A (lB A) Y'

theorem not_case148Five_of_ne_two {A L Y : Subgroup G} [(ker148 A Y).Normal]
    (hpt : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L)
    {p e : ℕ} [Fact p.Prime] (hp : p ≠ 2) (he : 1 ≤ e)
    (hL : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) :
    ¬ Case148Five A (lB A) Y := by
  intro h5
  obtain ⟨c', -, L', n, m, hc', hL', hn, hm, -, -, -, -, hε, -⟩ := h5
  rw [hpt hc' hL'] at hε
  exact false_of_isoLThreePi_of_isLThreeEpsAt_two hp he (Nat.mul_pos hn hm) hL hε

theorem res1L3NoFive_of_even {P : ∀ (Y : Type) [Group Y], Prop}
    (heven : Res1L3NoFive Res1L3QEven P) : Res1L3NoFive Res1L3Q P := by
  intro G _ _ A c L X K Y M T P' Yc z τ Y' hY' hXY' hF hN
  obtain ⟨p, e, hpq, he, hL⟩ := τ.q.1
  by_cases hp2 : p = 2
  ·
    subst p
    have : Fact (Nat.Prime 2) := hpq
    exact heven G A c L X K Y M T P' Yc z
      (res1Tau_of_q τ ⟨τ.q, e, he, hL⟩) Y' hY' hXY' hF hN
  ·
    exact not_case148Five_of_ne_two
      (fun hc' hL' => eq_of_mem_lA_of_tau τ res1QE9_l3 hc' hL') hp2 he hL


theorem deltaZero_le_sup_of_competing_l3
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}
    (τ : Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z)
    (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X)
    (h148 : Item148 A (lB A)) (h149 : Item149 A (lB A))
    (h5 : ∀ Y' : Subgroup G, Y' ∈ scriptY2 A → X ≤ Y' →
      generalizedFitting ↥Y' = CFSG.pCore 2 ↥Y' → ∀ _ : (ker148 A Y').Normal,
        ¬ Case148Five A (lB A) Y')
    {M' : Subgroup G} (hC' : Ctx155 A X K Y M' T) :
    deltaZero A (lB A) M' ≤ L ⊔ pPrimeCoreOf 3 M' := by
  have hL3 : Res1L3Q (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hQ _ τ.q
  have hsimple := hL3.2.1
  have h3 : 3 ∣ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
    obtain ⟨E, -, hE9⟩ := hL3.2.2
    have h3E : 3 ∣ Nat.card E := by rw [hE9]; norm_num
    exact h3E.trans (Subgroup.card_subgroup_dvd_card E)
  have hpt : ∀ {c' : G} {L' : Subgroup G}, Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      L' = L := by
    intro c' L' hc' hL'
    exact eq_of_mem_lA_of_tau τ (res1QE9_of_le hQ) hc' hL'
  have hmem : M' ∈ CFSG.maximalTwoLocalsContaining ((Y ⊔ A : Subgroup G) : Set G) := by
    rw [sup_comm]
    exact hC'.mem_m
  obtain ⟨-, -, hM2, hF⟩ := facts_of_mem_maximalTwoLocalsContaining τ.std hmem
  let : (ker148 A M').Normal := ker148_normal hM2.1.2
  have hLD : L ≤ deltaZero A (lB A) M' :=
    τ.l_le.trans ((τ.le_oPrimeResidualOf_delta_of_competing hC').trans
      (τ.oPrimeResidualOf_delta_le_of_competing h149 hC').1)
  have hDM : deltaZero A (lB A) M' ≤ M' ⊔ A := (deltaZero_le M').trans le_sup_left
  have hXM' : X ≤ M' :=
    (τ.ctx.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y).trans
      (le_sup_right.trans (SetLike.coe_subset_coe.mp hC'.mem_m.2))
  refine Sylow155R1.res1340_le_sup_of_card_img148_le hLD hDM hsimple h3 ?_
  have hD0 := τ.sec15.toSec13Data
  rcases (h148 M' hM2.1).2 with h1 | h2 | h3' | h4 | h5' | h6 | h7
  ·
    rw [img148_eq_bot_of_le h1, Subgroup.card_bot]
    exact Nat.card_pos
  ·
    exact card_img148_le_card_thetaQuot_of_caseTwo hL3 hLD hDM hpt h2
  ·
    obtain ⟨c', d, L', hc', hL', ⟨φ⟩, -⟩ := h3'
    rw [hpt hc' hL'] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hL3.1)).false φ).elim
  ·
    obtain ⟨-, -, hW⟩ := h4
    exact (Proof1511Point.not_wStarS4_of_le_normalizer τ.sec15.isE27 hD0.mem_A hD0.ne_one
      τ.norm hW).elim
  ·
    exact (h5 M' hM2 hXM' hF _ h5').elim
  ·
    obtain ⟨-, ⟨c', L', hc', hL', ⟨φ⟩⟩, -⟩ := h6
    rw [hpt hc' hL'] at φ
    exact ((Proof15Res6.isEmpty_j2_of_types (Or.inl hL3.1)).false φ).elim
  ·
    exact (Proof15Res6.false_of_case148Seven_two τ.std h148 hM2 h7).elim

theorem res1Thm340_l3_of (hbot : Item145BotS14) (h1444 : Item1444S14) (h148 : Item148R)
    (h149 : Sec16.Item149S14) (hSz : KFacts.KPSz)
    {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
    (hQ : ∀ (X : Type) [Group X], Q X → Res1L3Q X)
    (hn : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L X K Y M T P' : Subgroup G)
      (Yc : Subgroup (Res1Q A L)) (z : G),
      Sylow155R1.Res1Tau Q P A c L X K Y M T P' Yc z → Claim153Normal A (lB A))
    (h5 : Res1L3NoFive Q P) : Sylow155R1.Res1Thm340 Q P :=
  Sylow155R1.res1Thm340_of_le hbot h1444 h149 hSz (res1QE9_of_le hQ) hn
    fun G _ _ A c L X K Y M T P' Yc z τ _ hC' =>
      deltaZero_le_sup_of_competing_l3 τ hQ (h148 G A c L τ.sec15) (h149 G A c L τ.std)
        (h5 G A c L X K Y M T P' Yc z τ) hC'

end CFSG.RankThree.PartTwo.Sec15.GagenL3
