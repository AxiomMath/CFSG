module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofAsc1411
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
public import CFSG.RankThree.PartTwo.Sec18.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

@[expose] def NoSmall1411 (X : Type) [Group X] (L S : Subgroup X) : Prop :=
  ∀ I : Subgroup X, I.Normal → Sec3.IsElemTwo I → (∃ l ∈ L, ∃ i ∈ I, l * i * l⁻¹ ≠ i) →
    ∀ t ∈ S, t ∉ CFSG.pCore 2 X → t * t = 1 →
      4 < (centralizer ({t} : Set X)).relIndex I

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

omit [Finite X] in
theorem normal_of_normalized_by_sup_eq_top {N : Subgroup X} (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hS : ∀ s ∈ S, ∀ n ∈ N, s * n * s⁻¹ ∈ N) (hLN : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) :
    N.Normal := by
  have := hL
  refine ⟨fun n hn g => ?_⟩
  have hg : g ∈ S ⊔ L := by rw [hSL]; exact Subgroup.mem_top g
  obtain ⟨s, hs, l, hl, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  rw [show s * l * n * (s * l)⁻¹ = s * (l * n * l⁻¹) * s⁻¹ by group]
  exact hS s hs _ (hLN l hl n hn)

theorem jG_normal_of_forall_le {Q : Subgroup X} (hQn : Q.Normal) (hQS : Q ≤ S) {i : ℕ}
    (hle : ∀ B ∈ Sec3.famG S i, B ≤ Q) : (Sec3.jG S i).Normal := by
  have h := Sec18.Item181ThreeProof.le_normalizer_jG_of_le (H := ⊤) hQS
    (fun h _ q hq => hQn.conj_mem q hq h) hle
  exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp h)

theorem relIndex_centralizer_omegaG_le_four {Q : Subgroup X} (hQS : Q ≤ S) {i : ℕ} (hi : i ≤ 1)
    {B : Subgroup X} (hB : B ∈ Sec3.famG S i) (hQB : Q.relIndex B ≤ 2) {t : X} (htB : t ∈ B) :
    (centralizer ({t} : Set X)).relIndex (Sec3.omegaG Q) ≤ 4 := by
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
    _ ≤ 2 ^ 1 * 2 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hi) (h2.trans hQB)
    _ = 4 := by norm_num

theorem centralizes_omegaG_pCore_of_noSmall (hQS : CFSG.pCore 2 X ≤ S)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2)
    (hNS : NoSmall1411 X L S) {i : ℕ} (hi : i ≤ 1) {B : Subgroup X} (hB : B ∈ Sec3.famG S i)
    (hBQ : ¬ B ≤ CFSG.pCore 2 X) :
    ∀ l ∈ L, ∀ v ∈ Sec3.omegaG (CFSG.pCore 2 X), l * v * l⁻¹ = v := by
  by_contra hnc
  push Not at hnc
  obtain ⟨t, htB, htQ⟩ := SetLike.not_le_iff_exists.mp hBQ
  have h4 := hNS _ (Sec3.omegaG_normal CFSG.pCore_normal) (Sec3.isElemTwo_omegaG _) hnc t
    (hB.1 htB) htQ (hB.2.1.2 t htB)
  have h5 := relIndex_centralizer_omegaG_le_four hQS hi hB (hidx B hB.1 hB.2.1) htB
  omega

omit [Finite X] in
theorem normal_omegaG_of_centralizes_omegaG_pCore
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) (hQS : CFSG.pCore 2 X ≤ S)
    (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hLV : ∀ l ∈ L, ∀ v ∈ Sec3.omegaG (CFSG.pCore 2 X), l * v * l⁻¹ = v) :
    (Sec3.omegaG S).Normal := by
  have hSV : Sec3.omegaG S ≤ Sec3.omegaG (CFSG.pCore 2 X) := by
    rintro z ⟨-, hzc, hz2⟩
    exact ⟨hCQ (Subgroup.mem_centralizer_iff.mpr fun q hq => (hzc q (hQS hq)).symm),
      fun x hx => hzc x (hQS hx), hz2⟩
  refine normal_of_normalized_by_sup_eq_top hL hSL (fun s hs n hn => ?_) (fun l hl n hn => ?_)
  · exact Sec3.conj_mem_omegaG (fun x hx => S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs))
      (fun x hx => S.mul_mem (S.mul_mem (S.inv_mem hs) hx) hs) hn
  · rw [hLV l hl n (hSV hn)]
    exact hn

theorem inf_mem_famG_one {Q A : Subgroup X} (hr : 1 ≤ CFSG.pRank 2 S)
    (hA : A ∈ Sec3.famG S 0) (h2 : Q.relIndex A = 2) : A ⊓ Q ∈ Sec3.famG S 1 := by
  refine ⟨inf_le_left.trans hA.1, ⟨fun a ha b hb => hA.2.1.1 a ha.1 b hb.1,
    fun a ha => hA.2.1.2 a ha.1⟩, ?_⟩
  have h := Subgroup.relIndex_mul_card (H := Q) (K := A)
  rw [h2, hA.2.2, inf_comm] at h
  have h' : 2 ^ (CFSG.pRank 2 S - 0) = 2 * 2 ^ (CFSG.pRank 2 S - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h'] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem normal_omegaG_jG_one_of_noSmall (hS2 : IsPGroup 2 S)
    (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) (hQS : CFSG.pCore 2 X ≤ S)
    (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2)
    (hNS : NoSmall1411 X L S) {A : Subgroup X} (hA : A ∈ Sec3.famG S 0)
    (hAQ : ¬ A ≤ CFSG.pCore 2 X) : (Sec3.omegaG (Sec3.jG S 1)).Normal := by
  set Q := CFSG.pCore 2 X
  have hQ2 : IsPGroup 2 Q := hS2.to_le hQS
  by_contra hEnn
  have hr : 2 ≤ CFSG.pRank 2 S := by
    by_contra h
    push Not at h
    apply hEnn
    rw [Sec3.omegaG_jG_one_eq_bot_of_pRank_le (by omega)]
    exact Subgroup.normal_bot
  obtain ⟨t, htA, htQ⟩ := SetLike.not_le_iff_exists.mp hAQ
  have h2 : Q.relIndex A = 2 := by
    have h1 : Q.relIndex A ≠ 1 := fun h => hAQ (Subgroup.relIndex_eq_one.mp h)
    have h0 := Sec3.relIndex_ne_zero_of_finite Q A
    have h3 := hidx A hA.1 hA.2.1
    omega
  have hAQ' : A ⊓ Q ∈ Sec3.famG S 1 := inf_mem_famG_one (by omega) hA h2
  have hO2 : ∀ K : Subgroup X, K ≤ ⊤ → (∀ h ∈ (⊤ : Subgroup X), ∀ k ∈ K, h * k * h⁻¹ ∈ K) →
      IsPGroup 2 K → K ≤ Q := fun K _ hK hK2 =>
    le_sSup ⟨⟨fun k hk g => hK g trivial k hk⟩, hK2⟩
  have hQn : ∀ h ∈ (⊤ : Subgroup X), ∀ p ∈ Q, h * p * h⁻¹ ∈ Q := fun h _ p hp =>
    CFSG.pCore_normal.conj_mem p hp h
  have hXnc := Sec3.not_centralizes_omegaG_pOne (X := L) le_rfl hQS hQ2 hQ2 hCQ hQn hO2 le_top
    (fun t ht e he => Sec3.conj_mem_omegaG_jG ht he) hr hAQ' inf_le_right
    (fun N hNS' hNL => normal_of_normalized_by_sup_eq_top hL hSL hNS' hNL) hEnn
  push Not at hXnc
  have hWn : (Sec3.omegaG (Sec3.pOne S Q)).Normal :=
    ⟨fun w hw g => Sec3.conj_mem_omegaG_pOne hQS
      (fun p hp => CFSG.pCore_normal.conj_mem p hp g)
      (fun p hp => by
        have := CFSG.pCore_normal.conj_mem p hp g⁻¹
        rwa [inv_inv] at this) hw⟩
  have h4 := hNS _ hWn (Sec3.isElemTwo_omegaG _) hXnc t (hA.1 htA) htQ (hA.2.1.2 t htA)
  have h5 := Sec3.relIndex_centralizer_le_two hQS hA hAQ' htA
  omega

theorem two_fourChar_normal_of_noSmall (hCQ : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (hS2 : IsPGroup 2 S) (hQS : CFSG.pCore 2 X ≤ S) (hL : L.Normal) (hSL : S ⊔ L = ⊤)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2)
    (hNS : NoSmall1411 X L S) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  have hQn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  by_cases hP : (∀ B ∈ Sec3.famG S 0, B ≤ CFSG.pCore 2 X) ∧
      ∀ B ∈ Sec3.famG S 1, B ≤ CFSG.pCore 2 X
  · obtain ⟨hP0, hP1⟩ := hP
    refine ⟨1, 2, by decide, by decide, by decide, ?_, ?_⟩
    · rw [Sec18.Item181ThreeProof.fourChar_one]
      exact jG_normal_of_forall_le hQn hQS hP0
    · rw [Sec18.Item181ThreeProof.fourChar_two]
      exact Sec3.omegaG_normal (jG_normal_of_forall_le hQn hQS hP1)
  · have hex : ∃ i, i ≤ 1 ∧ ∃ B ∈ Sec3.famG S i, ¬ B ≤ CFSG.pCore 2 X := by
      by_contra hno
      push Not at hno
      exact hP ⟨hno 0 (by norm_num), hno 1 le_rfl⟩
    obtain ⟨i, hi, B, hB, hBQ⟩ := hex
    have hS1 : (Sec3.omegaG S).Normal :=
      normal_omegaG_of_centralizes_omegaG_pCore hCQ hQS hL hSL
        (centralizes_omegaG_pCore_of_noSmall hQS hidx hNS hi hB hBQ)
    by_cases hP0 : ∀ B ∈ Sec3.famG S 0, B ≤ CFSG.pCore 2 X
    · refine ⟨0, 1, by decide, by decide, by decide, ?_, ?_⟩
      · rw [Sec18.Item181ThreeProof.fourChar_zero]
        exact hS1
      · rw [Sec18.Item181ThreeProof.fourChar_one]
        exact jG_normal_of_forall_le hQn hQS hP0
    · push Not at hP0
      obtain ⟨A, hA, hAQ⟩ := hP0
      refine ⟨0, 2, by decide, by decide, by decide, ?_, ?_⟩
      · rw [Sec18.Item181ThreeProof.fourChar_zero]
        exact hS1
      · rw [Sec18.Item181ThreeProof.fourChar_two]
        exact normal_omegaG_jG_one_of_noSmall hS2 hCQ hQS hL hSL hidx hNS hA hAQ

theorem centralizer_pCore_le_of_hyp1411 (h : Hyp1411 X L S) :
    centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X := by
  have := CFSG.centralizer_generalizedFitting_le X
  rwa [h.1] at this

theorem asc82Item1411_of_noSmall (h : Hyp1411 X L S)
    (hidx : ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2)
    (hNS : NoSmall1411 X L S) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  have hCQ := centralizer_pCore_le_of_hyp1411 h
  obtain ⟨-, hL, -, -, hS2, hQS, hSL, -⟩ := h
  exact two_fourChar_normal_of_noSmall hCQ hS2 hQS hL hSL hidx hNS

end CFSG.RankThree.PartTwo.Sec20
