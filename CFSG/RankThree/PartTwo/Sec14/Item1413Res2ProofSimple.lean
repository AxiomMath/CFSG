module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.KFacts.KS14Mult
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413Res2

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutatorElement_mul_central_left {Q : Type*} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (a b : Q) : ⁅a * z, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz b
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * b * (a * z)⁻¹ * b⁻¹ = a * (z * b) * z⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * z) * z⁻¹ * a⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem commutatorElement_mul_central_right {Q : Type*} [Group Q] {z : Q}
    (hz : z ∈ Subgroup.center Q) (a b : Q) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hz a⁻¹
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [h]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem le_center_of_isQuasisimple' {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {K : Subgroup Q} [hK : K.Normal] (hne : K ≠ ⊤) : K ≤ Subgroup.center Q := by
  obtain ⟨hperf, hsimple, -⟩ := hQ
  have hmap : (K.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    hK.map _ (QuotientGroup.mk'_surjective _)
  rcases hmap.eq_bot_or_eq_top with h | h
  · intro x hx
    have hx' := Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center Q)) hx
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx'
    exact hx'
  · exfalso
    apply hne
    have hKZ : ∀ q : Q, ∃ k ∈ K, ∃ z ∈ Subgroup.center Q, q = k * z := by
      intro q
      have hq : QuotientGroup.mk' (Subgroup.center Q) q ∈
          K.map (QuotientGroup.mk' (Subgroup.center Q)) := h ▸ Subgroup.mem_top _
      obtain ⟨k, hk, hkq⟩ := hq
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkq
      exact ⟨k, hk, k⁻¹ * q, hkq, by group⟩
    have hcomm : commutator Q ≤ K := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨k₁, hk₁, z₁, hz₁, rfl⟩ := hKZ a
      obtain ⟨k₂, hk₂, z₂, hz₂, rfl⟩ := hKZ b
      rw [commutatorElement_mul_central_left hz₁, commutatorElement_mul_central_right hz₂,
        commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem hk₁ hk₂) (K.inv_mem hk₁)) (K.inv_mem hk₂)
    rw [Group.isPerfect_def] at hperf
    rw [eq_top_iff, ← hperf]
    exact hcomm

theorem theta_eq_bot_of_odd (h135 : Item135) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hST : HypS A ∨ HypT A)
    (hodd : ¬ 2 ∣ Nat.card (aschbacherSolvableCore 3 ↥L))
    (htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)) :
    aschbacherSolvableCore 3 ↥L = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := aschbacherSolvableCore 3 ↥L with hN
  have hθ := solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have : N.Characteristic := hθ.2.1
  have : N.Normal := Subgroup.normal_of_characteristic N
  have hO2 : CFSG.pCore 2 ↥L = ⊥ := by
    have hle : CFSG.pCore 2 ↥L ≤ N := hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
    have hp : IsPGroup 2 (CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : Nat.card (CFSG.pCore 2 ↥L) ∣ Nat.card N := Subgroup.card_dvd_of_le hle
    rw [hk] at hdvd
    rcases k with _ | k
    · exact Subgroup.eq_bot_of_card_eq _ (by simpa using hk)
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdvd) hodd
  have hq : CFSG.IsQuasisimple ↥L :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hO2).trans QuotientGroup.quotientBot)
      (h135 G A c L hD hST)
  have hNtop : N ≠ ⊤ := by
    intro htop
    have h1 : N.index = 1 := Subgroup.index_eq_one.mpr htop
    have hgt : 1 < Nat.card (↥L ⧸ N) := by
      rcases htype with hM | hM | hM
      · obtain ⟨φ⟩ := hM
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM12]
        norm_num
      · obtain ⟨φ⟩ := hM
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
        norm_num
      · obtain ⟨φ⟩ := hM
        rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeM22]
        norm_num
    exact absurd h1 (ne_of_gt hgt)
  have hNc : N ≤ Subgroup.center ↥L := le_center_of_isQuasisimple' hq hNtop
  have hcop : Nat.Coprime 6 (Nat.card N) := by
    have h2 : Nat.Coprime 2 (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd
    have h3 : Nat.Coprime 3 (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ.2.2.1
    exact Nat.coprime_mul_iff_left.mpr ⟨h2, h3⟩
  exact KFacts.KS14.ks18Mult_sporadic ↥L N hq.1 hNc hcop htype

theorem mem_scriptQPi_of_concl142 (h142 : Concl142S14) {A : Subgroup G} {c : G}
    {L : Subgroup G} (hS : Sec14Std G A c L) {c' : G} (hc' : Subgroup.zpowers c' ∈ omegaA A)
    {L' : Subgroup G} (hL' : L' ∈ lA A c') {R : Subgroup G} (hRL : R ≤ L')
    (hAR : A ≤ Subgroup.normalizer (R : Set G)) (hR2 : IsPGroup 2 R) :
    R ∈ scriptQPi A (lB A) L' (piOf 2) := by
  have hR3 : ¬ 3 ∣ Nat.card R := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hRN : R ≤ Subgroup.normalizer (Subgroup.zpowers c' : Set G) :=
    hRL.trans ((Sec6.le_centralizer_of_mem_thetaComponentsAt hL'.1).trans
      (centralizer_singleton_le_normalizer_zpowers c'))
  have hRinv : R ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) A
      (piCompl 3) := ⟨hRN, (isPiSubgroup_piCompl_iff Nat.prime_three R).mpr hR3, hAR⟩
  obtain ⟨Q, hRQ, hQ⟩ := Finite.exists_le_maximal
    (p := (· ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c' : Set G)) A
      (piCompl 3))) hRinv
  have hQ𝓠 := (h142 G A c L hS c' hc' Q hQ).1
  exact ⟨⟨mem_scriptQ_of_le hQ𝓠 hRQ hAR, hRL⟩, (isPiSubgroup_piOf_iff Nat.prime_two R).mpr hR2⟩

end Proof1413Res2

end CFSG.RankThree.PartTwo.Sec14
