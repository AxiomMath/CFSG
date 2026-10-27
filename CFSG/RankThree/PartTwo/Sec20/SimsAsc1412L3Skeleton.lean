module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1412L3Parabolic
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

@[expose] def NoSmall1412 (X : Type) [Group X] (L S : Subgroup X) : Prop :=
  ∀ I : Subgroup X, I.Normal → Sec3.IsElemTwo I → (∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) →
    ∀ t ∈ S, t ∉ CFSG.pCore 2 X → t * t = 1 →
      16 < (centralizer ({t} : Set X)).relIndex I

@[expose] def Star1412 (X : Type) [Group X] (S : Subgroup X) : Prop :=
  (Sec3.omegaG S).Normal ∧ (∃ A ∈ Sec3.famG S 0, ¬ A ≤ CFSG.pCore 2 X) ∧
    ∀ A ∈ Sec3.famG S 0, ¬ A ≤ CFSG.pCore 2 X → (CFSG.pCore 2 X).relIndex A = 8

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

theorem relIndex_centralizer_omegaG_le_sixteen {Q : Subgroup X} (hQS : Q ≤ S) {i : ℕ}
    (hi : i ≤ 1) {B : Subgroup X} (hB : B ∈ Sec3.famG S i) (hQB : Q.relIndex B ≤ 8) {t : X}
    (htB : t ∈ B) : (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q) ≤ 16 := by
  have hQV : Q ≤ centralizer ((Sec3.omegaG Q : Subgroup X) : Set X) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact hv.2.1 q hq
  have h1 := Sec3.relIndex_centralizer_le_of_famG ((Sec3.omegaG_le Q).trans hQS)
    (Sec3.isElemTwo_omegaG Q) hB
  have h2 : (centralizer ((Sec3.omegaG Q : Subgroup X) : Set X)).relIndex B ≤ Q.relIndex B :=
    Subgroup.relIndex_le_of_le_left hQV (Sec3.relIndex_ne_zero_of_finite _ _)
  have h3 : (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q) ≤
      (centralizer (B : Set X)).relIndex (Sec3.omegaG Q) :=
    Subgroup.relIndex_le_of_le_left (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr htB))
      (Sec3.relIndex_ne_zero_of_finite _ _)
  calc (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q)
      ≤ (centralizer (B : Set X)).relIndex (Sec3.omegaG Q) := h3
    _ ≤ 2 ^ i * (centralizer ((Sec3.omegaG Q : Subgroup X) : Set X)).relIndex B := h1
    _ ≤ 2 ^ 1 * 8 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hi) (h2.trans hQB)
    _ = 16 := by norm_num

theorem centralizes_omegaG_pCore_of_noSmall1412 (hQS : CFSG.pCore 2 X ≤ S)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 8)
    (hNS : NoSmall1412 X L S) {i : ℕ} (hi : i ≤ 1) {B : Subgroup X} (hB : B ∈ Sec3.famG S i)
    (hBQ : ¬ B ≤ CFSG.pCore 2 X) :
    ∀ l ∈ L, ∀ v ∈ Sec3.omegaG (CFSG.pCore 2 X), l * v * l⁻¹ = v := by
  by_contra hnc
  push Not at hnc
  obtain ⟨t, htB, htQ⟩ := SetLike.not_le_iff_exists.mp hBQ
  have h16 := hNS _ (Sec3.omegaG_normal CFSG.pCore_normal) (Sec3.isElemTwo_omegaG _) hnc t
    (hB.1 htB) htQ (hB.2.1.2 t htB)
  have h := relIndex_centralizer_omegaG_le_sixteen hQS hi hB (hidx B hB.1 hB.2.1) htB
  omega

theorem exists_relIndex_eq_two_pow_of_famG_zero {Q A : Subgroup X} (hA : A ∈ Sec3.famG S 0) :
    ∃ r, r ≤ CFSG.pRank 2 S ∧ Q.relIndex A = 2 ^ r := by
  have hdvd : Q.relIndex A ∣ 2 ^ CFSG.pRank 2 S := by
    rw [← Nat.sub_zero (CFSG.pRank 2 S), ← hA.2.2]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card Q A)
  obtain ⟨r, hr, hrA⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨r, hr, hrA⟩

theorem inf_mem_famG_of_relIndex_eq_two_pow {Q A : Subgroup X} {r : ℕ}
    (hr : r ≤ CFSG.pRank 2 S) (hA : A ∈ Sec3.famG S 0) (h2 : Q.relIndex A = 2 ^ r) :
    A ⊓ Q ∈ Sec3.famG S r := by
  refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
    fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := Q) (K := A)
  rw [h2, hA.2.2, inf_comm] at h
  have h' : 2 ^ (CFSG.pRank 2 S - 0) = 2 ^ r * 2 ^ (CFSG.pRank 2 S - r) := by
    rw [← pow_add]; congr 1; omega
  rw [h'] at h
  exact Nat.eq_of_mul_eq_mul_left (by positivity) h

theorem normal_omegaG_jG_of_noSmall1412 (hS2 : IsPGroup 2 S)
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) (hQS : CFSG.pCore 2 X ≤ S)
    (hL : L.Normal) (hSL : S ⊔ L = ⊤) (hNS : NoSmall1412 X L S) {A : Subgroup X}
    (hA : A ∈ Sec3.famG S 0) (hAQ : ¬ A ≤ CFSG.pCore 2 X) {r : ℕ}
    (hrA : (CFSG.pCore 2 X).relIndex A = 2 ^ r) (hr4 : r ≤ 4) :
    (Sec3.omegaG (Sec3.jG S r)).Normal := by
  set Q := CFSG.pCore 2 X
  have hQ2 : IsPGroup 2 Q := hS2.to_le hQS
  by_cases hrS : CFSG.pRank 2 S ≤ r
  · have hJ : Sec3.jG S r = ⊥ := Sec18.Item181ThreeProof.jG_eq_bot_of_pRank_sub_eq_zero (by omega)
    have hE : Sec3.omegaG (Sec3.jG S r) = ⊥ := by
      rw [eq_bot_iff, ← hJ]
      exact Sec3.omegaG_le _
    rw [hE]
    exact Subgroup.normal_bot
  push Not at hrS
  by_contra hEnn
  obtain ⟨t, htA, htQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have hAQ' : A ⊓ Q ∈ Sec3.famG S r := inf_mem_famG_of_relIndex_eq_two_pow hrS.le hA hrA
  have hO2 : ∀ K : Subgroup X, K ≤ ⊤ → (∀ h ∈ (⊤ : Subgroup X), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ Q := fun K _ hK hK2 =>
    le_sSup ⟨⟨fun k hk g => hK g trivial k hk⟩, hK2⟩
  have hQn : ∀ h ∈ (⊤ : Subgroup X), ∀ p ∈ Q, h * p * h⁻¹ ∈ Q := fun h _ p hp =>
    CFSG.pCore_normal.conj_mem p hp h
  have hEW := omegaG_jG_le_omegaG_pJ1412 (H := ⊤) le_rfl hQS hQ2 hQ2 hCQ hQn hO2 le_top
    (fun t ht e he => Sec3.conj_mem_omegaG_jG ht he) (by omega) hAQ' inf_le_right
  have hXnc : ∃ l ∈ L, ∃ w ∈ Sec3.omegaG (pJ1412 S Q r), l * w * l⁻¹ ≠ w := by
    by_contra hc
    push Not at hc
    apply hEnn
    refine normal_of_normalized_by_sup_eq_top hL hSL
      (fun s hs e he => Sec3.conj_mem_omegaG_jG hs he) fun l hl e he => ?_
    rw [hc l hl e (hEW he)]
    exact he
  have hWn : (Sec3.omegaG (pJ1412 S Q r)).Normal :=
    ⟨fun w hw g => conj_mem_omegaG_pJ1412 hQS
      (fun p hp => CFSG.pCore_normal.conj_mem p hp g)
      (fun p hp => by
        have := CFSG.pCore_normal.conj_mem p hp g⁻¹
        rwa [inv_inv] at this) hw⟩
  have h16 := hNS _ hWn (Sec3.isElemTwo_omegaG _) hXnc t (hA.1 htA) htQ (hA.2.1.2 t htA)
  have hle := relIndex_centralizer_le_pow_pJ1412 hQS hA hAQ' htA
  have h2r : 2 ^ r ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hr4
  omega

theorem two_fourChar_normal_or_star1412
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (hS2 : IsPGroup 2 S) (hQS : CFSG.pCore 2 X ≤ S) (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 8)
    (hNS : NoSmall1412 X L S) :
    (∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ (Sec18.fourChar S i₁).Normal ∧ (Sec18.fourChar S i₂).Normal) ∨
      Star1412 X S := by
  have hQn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  by_cases hP : (∀ B ∈ Sec3.famG S 0, B ≤ CFSG.pCore 2 X) ∧
      ∀ B ∈ Sec3.famG S 1, B ≤ CFSG.pCore 2 X
  · obtain ⟨hP0, hP1⟩ := hP
    refine Or.inl ⟨1, 2, by decide, ?_, ?_⟩
    · rw [Sec18.Item181ThreeProof.fourChar_one]
      exact jG_normal_of_forall_le hQn hQS hP0
    · rw [Sec18.Item181ThreeProof.fourChar_two]
      exact Sec3.omegaG_normal (jG_normal_of_forall_le hQn hQS hP1)
  have hex : ∃ i, i ≤ 1 ∧ ∃ B ∈ Sec3.famG S i, ¬ B ≤ CFSG.pCore 2 X := by
    by_contra hno
    push Not at hno
    exact hP ⟨hno 0 (by norm_num), hno 1 le_rfl⟩
  obtain ⟨i, hi, B, hB, hBQ⟩ := hex
  have hS1 : (Sec3.omegaG S).Normal :=
    normal_omegaG_of_centralizes_omegaG_pCore hCQ hQS hL hSL
      (centralizes_omegaG_pCore_of_noSmall1412 hQS hidx hNS hi hB hBQ)
  by_cases hP0 : ∀ B ∈ Sec3.famG S 0, B ≤ CFSG.pCore 2 X
  · refine Or.inl ⟨0, 1, by decide, ?_, ?_⟩
    · rw [Sec18.Item181ThreeProof.fourChar_zero]
      exact hS1
    · rw [Sec18.Item181ThreeProof.fourChar_one]
      exact jG_normal_of_forall_le hQn hQS hP0
  push Not at hP0
  by_cases hsmall : ∃ A ∈ Sec3.famG S 0, ¬ A ≤ CFSG.pCore 2 X ∧
      (CFSG.pCore 2 X).relIndex A ≤ 4
  · obtain ⟨A, hA, hAQ, hA4⟩ := hsmall
    obtain ⟨r, -, hr⟩ := exists_relIndex_eq_two_pow_of_famG_zero (Q := CFSG.pCore 2 X) hA
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hAQ (Subgroup.relIndex_eq_one.mp (by simpa using hr))
    have hr2 : r ≤ 2 := by
      by_contra h
      push Not at h
      have : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
      omega
    have hn := normal_omegaG_jG_of_noSmall1412 hS2 hCQ hQS hL hSL hNS hA hAQ hr (by omega)
    have hr1 : 1 ≤ r := Nat.pos_of_ne_zero hr0
    refine Or.inl ?_
    interval_cases r
    · refine ⟨0, 2, by decide, ?_, ?_⟩
      · rw [Sec18.Item181ThreeProof.fourChar_zero]
        exact hS1
      · rw [Sec18.Item181ThreeProof.fourChar_two]
        exact hn
    · refine ⟨0, 3, by decide, ?_, ?_⟩
      · rw [Sec18.Item181ThreeProof.fourChar_zero]
        exact hS1
      · rw [Sec18.Item181ThreeProof.fourChar_three]
        exact hn
  push Not at hsmall
  refine Or.inr ⟨hS1, hP0, fun A hA hAQ => ?_⟩
  have h8 := hidx A hA.1 hA.2.1
  have h4 := hsmall A hA hAQ
  obtain ⟨r, -, hr⟩ := exists_relIndex_eq_two_pow_of_famG_zero (Q := CFSG.pCore 2 X) hA
  rw [hr] at h8 h4 ⊢
  have hr3 : 3 ≤ r := by
    by_contra h
    push Not at h
    have : 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hr3' : r ≤ 3 := by
    by_contra h
    push Not at h
    have : 2 ^ 4 ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
    omega
  rw [show r = 3 by omega]
  norm_num

theorem two_fourChar_normal_or_star1412_of_hyp1411 (h : Hyp1411 X L S)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 8)
    (hNS : NoSmall1412 X L S) :
    (∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ (Sec18.fourChar S i₁).Normal ∧ (Sec18.fourChar S i₂).Normal) ∨
      Star1412 X S := by
  have hCQ := centralizer_pCore_le_of_hyp1411 h
  obtain ⟨-, hL, -, -, hS2, hQS, hSL, -⟩ := h
  exact two_fourChar_normal_or_star1412 hCQ hS2 hQS hL hSL hidx hNS

end CFSG.RankThree.PartTwo.Sec20
