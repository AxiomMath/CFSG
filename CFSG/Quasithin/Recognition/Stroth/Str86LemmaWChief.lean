module

public import CFSG.Quasithin.Recognition.Stroth.Str86AbBase

import CFSG.Quasithin.Recognition.Stroth.Str86OddModuleProp39
import CFSG.Quasithin.Recognition.Stroth.Str86XOneNat2

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem chief_count_le_one {q c : ℕ} (hq : 1 < q) (h : (q ^ 2) ^ c ≤ q ^ 3) :
    c ≤ 1 := by
  by_contra hgt
  have hc2 : 2 ≤ c := by omega
  have hmono : (q ^ 2) ^ 2 ≤ (q ^ 2) ^ c :=
    Nat.pow_le_pow_right (by positivity) hc2
  have h43 : q ^ 4 ≤ q ^ 3 := by
    calc q ^ 4 = (q ^ 2) ^ 2 := by
          rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
      _ ≤ (q ^ 2) ^ c := hmono
      _ ≤ q ^ 3 := h
  exact (not_lt_of_ge h43) (Nat.pow_lt_pow_right hq (by norm_num))

private theorem chief_count_eq_one
    {H U : Subgroup G} {q c : ℕ} (hq : 1 < q)
    (hX : IsSzU3Quot (oTwoQuot ↥H) q) (hU : IsPGroup 2 U) (hUH : U ≤ H)
    (hser : IsChiefSeriesFrom H U U c) {t : G} (htH : t ∈ H)
    (ht : t * t ∈ pCoreOf 2 H) (htO : t ∉ pCoreOf 2 H) (hc0 : c ≠ 0)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex U ≤
      q ^ 3) : c = 1 := by
  have hM6 := pow_sq_le_relIndex_centralizer hX hU hUH hser htH ht htO
  have hle : (q ^ 2) ^ c ≤ q ^ 3 := hM6.trans hdisp
  have hle1 : c ≤ 1 := chief_count_le_one hq hle
  omega

private theorem chiefSeries_setup
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) :
    Q1 L1 L2 S ≤ S ∧ pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S ∧
      IsSylowTwoOf S (L1 ⊔ S) ∧ IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
  have hF := hI.hF
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have h1 : VU3Big L1 := ⟨k, hI.hk, F, inferInstance, inferInstance, hI.hFc, hI.hU3⟩
  have hS1 : S = (S ⊓ L1) ⊔ Q1 L1 L2 S :=
    eq_sup_pCoreOf_of_bender_left hF.1 hI.hSB (Or.inr (Or.inl h1))
  have hsup1 : L1 ⊔ S = L1 ⊔ Q1 L1 L2 S :=
    le_antisymm (sup_le le_sup_left (hS1.le.trans (sup_le (inf_le_right.trans le_sup_left)
      le_sup_right))) (sup_le le_sup_left (hQ1S.trans le_sup_right))
  have hQcore : pCoreOf 2 (L1 ⊔ S) = Q1 L1 L2 S := by
    rw [hsup1]
    exact pCoreOf_sup_pCoreOf hF.1
  have hSyl : IsSylowTwoOf S (L1 ⊔ S) := by
    rw [hsup1]
    exact isSylowTwoOf_sup_pCoreOf hF.1 hS1
  have hX : IsSzU3Quot (oTwoQuot ↥(L1 ⊔ S)) (2 ^ k) := by
    have he : oTwoQuot ↥(L1 ⊔ S) ≃* oTwoQuot ↥L1 := by
      rw [hsup1]
      exact oTwoQuotSupEquiv hF.1
    exact IsSzU3Quot.of_mulEquiv he (Or.inr ⟨k, hI.hk, rfl, F, inferInstance, inferInstance,
      hI.hFc, hI.hU3⟩)
  exact ⟨hQ1S, hQcore, hSyl, hX⟩

private theorem exists_chiefSeries_count_one
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) ≤ (2 ^ k) ^ 3) :
    ∃ c, IsChiefSeriesFrom (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) c ∧ c = 1 := by
  obtain ⟨hQ1S, hQcore, hSyl, hX⟩ := chiefSeries_setup hI
  obtain ⟨hVQ1, hP1NV, -⟩ := str86_conjClosure_frame hI hZQ
  have hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    hI.hF.1.h1.pgroup.to_le (hVQ1.trans hQ1S)
  have hVH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := hVQ1.trans (hQ1S.trans le_sup_right)
  have ht1 : t ≠ 1 := fun h => htQ (h ▸ (Q1 L1 L2 S).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1
  have hX2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have htH : t ∈ L1 ⊔ S :=
    (str86_le_lhat_of_isPGroup hI hX2).1 (Subgroup.zpowers_le.mpr htP)
      (Subgroup.mem_zpowers t)
  have hHV : L1 ⊔ S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans hP1NV
  have hnorm : IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHV hg) x).mp hx⟩
  obtain ⟨c, hser⟩ := D15Proof.exists_isChiefSeriesFrom
    (conjClosure (Z2 L1 L2 S) L1) hnorm
  have ht2p : t * t ∈ pCoreOf 2 (L1 ⊔ S) := by
    rw [hQcore, ht2]
    exact (Q1 L1 L2 S).one_mem
  have htO : t ∉ pCoreOf 2 (L1 ⊔ S) := by rwa [hQcore]
  have hc0 : c ≠ 0 := str86_chief_count_ne_zero hI.hF hSyl hV hser
  have hk : 2 ≤ k := hI.hk
  have hq : 1 < 2 ^ k := Nat.one_lt_two_pow (n := k) (by omega)
  have hc1 : c = 1 := chief_count_eq_one hq hX hV hVH hser htH ht2p htO hc0 hdisp
  exact ⟨c, hser, hc1⟩

private theorem exists_commutator_chiefStep {H U : Subgroup G} {c : ℕ}
    (hser : IsChiefSeriesFrom H U U c) (hc : c = 1) (hUH : U ≤ H)
    (hUQ : U ≤ pCoreOf 2 H) :
    ∃ L N : Subgroup G, IsChiefStep H U L N ∧ ¬ IsCentralStep H L N ∧
      ⁅L, oTwoUpper H⁆ = ⊥ ∧ ⁅U, oTwoUpper H⁆ ≤ N := by
  have hnorm : IsNormalIn H U U := F112W.isNormalIn_of_isChiefSeriesFrom hser
  obtain ⟨L, N, hstep, hnc, hNV⟩ := exists_noncentral_chiefStep hser hc
  obtain ⟨a, ha⟩ := D15Proof.exists_isChiefSeriesFrom L hstep.2.1
  have hna : IsChiefSeriesFrom H U N (a + 1) := by
    have h := F112W.isChiefSeriesFrom_of_step hstep ha
    rwa [F112W.stepWeight_of_not_central hnc] at h
  obtain ⟨b, hb⟩ := F112W.exists_isChiefSeriesBetween (W := N) hstep.1 U hnorm hNV
  have huniq : b + (a + 1) = c :=
    F112W.isChiefSeriesFrom_unique hUH (hb.append hna) hser
  have ha0 : a = 0 := by omega
  have hb0 : b = 0 := by omega
  refine ⟨L, N, hstep, hnc, ?_, ?_⟩
  · exact (F112W.isChiefSeriesFrom_zero_iff hUH hUQ hstep.2.1).mp (ha0 ▸ ha)
  · exact (F112W.isChiefSeriesBetween_zero_iff hUH hUQ hstep.1 hnorm hNV).mp (hb0 ▸ hb)

theorem str86_commutator_conjClosure_ne_bot
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) :
    ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ ≠ ⊥ := by
  intro hcomm
  obtain ⟨hQ1S, hQcore, hSyl, -⟩ := chiefSeries_setup hI
  obtain ⟨hVQ1, hP1NV, -⟩ := str86_conjClosure_frame hI hZQ
  have hV : IsPGroup 2 (conjClosure (Z2 L1 L2 S) L1) :=
    hI.hF.1.h1.pgroup.to_le (hVQ1.trans hQ1S)
  have hVH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := hVQ1.trans (hQ1S.trans le_sup_right)
  have hVQ1' : conjClosure (Z2 L1 L2 S) L1 ≤ pCoreOf 2 (L1 ⊔ S) := by rwa [hQcore]
  have hHV : L1 ⊔ S ≤ Subgroup.normalizer (conjClosure (Z2 L1 L2 S) L1 : Set G) :=
    (sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)).trans hP1NV
  have hnorm : IsNormalIn (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) :=
    ⟨le_rfl, fun g hg x hx => (Subgroup.mem_normalizer_iff.mp (hHV hg) x).mp hx⟩
  have h0 : IsChiefSeriesFrom (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1)
      (conjClosure (Z2 L1 L2 S) L1) 0 :=
    (F112W.isChiefSeriesFrom_zero_iff hVH hVQ1' hnorm).mpr hcomm
  exact str86_chief_count_ne_zero hI.hF hSyl hV h0 rfl

theorem Str86AbHyp.exists_unique_noncentral_chiefStep
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hI : Str86AbHyp L1 L2 S k m F) (hZQ : Z2 L1 L2 S ≤ Q1 L1 L2 S) {t : G}
    (htP : t ∈ P1 L1 L2 S) (htQ : t ∉ Q1 L1 L2 S) (ht2 : t * t = 1)
    (hdisp : (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (conjClosure (Z2 L1 L2 S) L1) ≤ (2 ^ k) ^ 3) :
    ∃ L N : Subgroup G, IsChiefStep (L1 ⊔ S) (conjClosure (Z2 L1 L2 S) L1) L N ∧
      ¬ IsCentralStep (L1 ⊔ S) L N ∧ ⁅L, oTwoUpper (L1 ⊔ S)⁆ = ⊥ ∧
      ⁅conjClosure (Z2 L1 L2 S) L1, oTwoUpper (L1 ⊔ S)⁆ ≤ N := by
  obtain ⟨c, hser, hc1⟩ := exists_chiefSeries_count_one hI hZQ htP htQ ht2 hdisp
  obtain ⟨hQ1S, hQcore, -, -⟩ := chiefSeries_setup hI
  obtain ⟨hVQ1, -, -⟩ := str86_conjClosure_frame hI hZQ
  have hVH : conjClosure (Z2 L1 L2 S) L1 ≤ L1 ⊔ S := hVQ1.trans (hQ1S.trans le_sup_right)
  have hUQ : conjClosure (Z2 L1 L2 S) L1 ≤ pCoreOf 2 (L1 ⊔ S) := by rwa [hQcore]
  exact exists_commutator_chiefStep hser hc1 hVH hUQ

end CFSG.Quasithin.Stroth

end
