module

public import CFSG.Quasithin.Background.RonanG25Defs
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.RonanG25

section Small

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G}

theorem chainCounts_snoc_central {ord : Bool} {A M : Subgroup G} {a b : ℕ}
    (h : ChainCounts F X ord A M a b) :
    ∀ {B : Subgroup G}, ChiefStep X M B → FactorCentral X M B → ∀ {p : ℕ}, p.Prime →
      Nat.card B = p * Nat.card M → ChainCounts F X ord A B a b := by
  induction h with
  | refl A hA =>
    intro B hs hc p hp hcard
    exact ChainCounts.central hs hc hp hcard (ChainCounts.refl B hs.invB)
  | natural hs hn rest ih =>
    intro B hs2 hc p hp hcard
    exact ChainCounts.natural hs hn (ih hs2 hc hp hcard)
  | additional hs habel hc' hcard' rest ih =>
    intro B hs2 hc p hp hcard
    exact ChainCounts.additional hs habel hc' hcard' (ih hs2 hc hp hcard)
  | central hs hc' hp' hcard' rest ih =>
    intro B hs2 hc p hp hcard
    exact ChainCounts.central hs hc' hp' hcard' (ih hs2 hc hp hcard)
  | other hord hs h2 rest ih =>
    intro B hs2 hc p hp hcard
    exact ChainCounts.other hord hs h2 (ih hs2 hc hp hcard)

theorem chainCounts_snoc_other {A M : Subgroup G} {a b : ℕ} (h : ChainCounts F X true A M a b) :
    ∀ {B : Subgroup G}, ChiefStep X M B → ¬ FactorTwo M B → ChainCounts F X true A B a b := by
  induction h with
  | refl A hA =>
    intro B hs h2
    exact ChainCounts.other rfl hs h2 (ChainCounts.refl B hs.invB)
  | natural hs hn rest ih =>
    intro B hs2 h22
    exact ChainCounts.natural hs hn (ih hs2 h22)
  | additional hs habel hc hcard rest ih =>
    intro B hs2 h22
    exact ChainCounts.additional hs habel hc hcard (ih hs2 h22)
  | central hs hc hp hcard rest ih =>
    intro B hs2 h22
    exact ChainCounts.central hs hc hp hcard (ih hs2 h22)
  | other hord hs h2 rest ih =>
    intro B hs2 h22
    exact ChainCounts.other hord hs h2 (ih hs2 h22)

theorem chiefStep_index_two_central {A B : Subgroup G} (hs : ChiefStep X A B)
    (hcard : Nat.card B = 2 * Nat.card A) [Finite G] : FactorCentral X A B := by
  have hAB : A ≤ B := hs.lt.le
  have hrel : A.relIndex B = 2 := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := B)
    rw [inf_eq_left.mpr hAB] at h
    have hpos : 0 < Nat.card A := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h]
    exact hcard
  obtain ⟨g, _, hg⟩ := Subgroup.relIndex_eq_two_iff.mp hrel
  have hmemg : ∀ z ∈ B, z ∉ A → z * g ∈ A := by
    intro z hz hzA
    rcases hg z hz with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 hzA
  intro x hx y hy
  by_cases hyA : y ∈ A
  · exact A.mul_mem (hs.invA x hx y hyA) (A.inv_mem hyA)
  · have hwB : x * y * x⁻¹ ∈ B := hs.invB x hx y hy
    have hwA : x * y * x⁻¹ ∉ A := by
      intro hw
      apply hyA
      have h1 := hs.invA x⁻¹ (X.inv_mem hx) _ hw
      rw [inv_inv] at h1
      have h2 : x⁻¹ * (x * y * x⁻¹) * x = y := by group
      rw [h2] at h1
      exact h1
    have h1 : y * g * (x * y * x⁻¹ * g)⁻¹ ∈ A :=
      A.mul_mem (hmemg y hy hyA) (A.inv_mem (hmemg _ hwB hwA))
    have e : y * g * (x * y * x⁻¹ * g)⁻¹ = y * (x * y * x⁻¹)⁻¹ := by group
    rw [e] at h1
    have h2 := A.inv_mem h1
    have e2 : (y * (x * y * x⁻¹)⁻¹)⁻¹ = x * y * x⁻¹ * y⁻¹ := by group
    rw [e2] at h2
    exact h2

theorem exists_chain_small [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hA : Inv X A)
    (hB : Inv X B) (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hdvd : A.relIndex B ∣ 6) :
    ChainCounts F X true A B 0 0 := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have key : ∀ T : Subgroup G, Inv X T → ∀ S : Subgroup G, S ≤ T → Inv X S →
      (∀ y ∈ T, ∀ z ∈ S, y * z * y⁻¹ ∈ S) → S.relIndex T ∣ 6 →
      ChainCounts F X true S T 0 0 := by
    intro T
    induction T using WellFoundedLT.induction with
    | ind T ih =>
      intro hT S hST hS hSnorm hSdvd
      by_cases heq : S = T
      · rw [heq]
        exact ChainCounts.refl T hT
      · have hlt : S < T := lt_of_le_of_ne hST heq
        obtain ⟨M, ⟨hSM, hMT, hMinv, hMnorm⟩, hMmax⟩ :=
          wellFounded_gt.has_min
            {M : Subgroup G | S ≤ M ∧ M < T ∧ Inv X M ∧ ∀ y ∈ T, ∀ z ∈ M, y * z * y⁻¹ ∈ M}
            ⟨S, le_rfl, hlt, hS, hSnorm⟩
        have hstep : ChiefStep X M T := by
          refine ⟨hMT, hMinv, hT, hMnorm, ?_⟩
          intro Q hMQ hQT hQinv hQnorm
          by_cases hQeq : Q = T
          · exact Or.inr hQeq
          · refine Or.inl ?_
            have hQlt : Q < T := lt_of_le_of_ne hQT hQeq
            by_contra hne
            exact hMmax Q ⟨le_trans hSM hMQ, hQlt, hQinv, hQnorm⟩
              (lt_of_le_of_ne hMQ (Ne.symm hne))
        have hrel : S.relIndex M * M.relIndex T = S.relIndex T :=
          Subgroup.relIndex_mul_relIndex (H := S) (K := M) (L := T) hSM hMT.le
        have hMdvd : M.relIndex T ∣ 6 :=
          dvd_trans (Dvd.intro_left _ hrel) hSdvd
        have hSMdvd : S.relIndex M ∣ 6 :=
          dvd_trans (Dvd.intro _ hrel) hSdvd
        have hchainSM : ChainCounts F X true S M 0 0 :=
          ih M hMT hMinv S hSM hS (fun y hy z hz => hSnorm y (hMT.le hy) z hz) hSMdvd
        have hcardrel : Nat.card T = M.relIndex T * Nat.card M := by
          have h := Subgroup.relIndex_mul_card (H := M) (K := T)
          rw [inf_eq_left.mpr hMT.le] at h
          exact h.symm
        have hcases : M.relIndex T = 2 ∨ M.relIndex T = 3 ∨ M.relIndex T = 6 := by
          have hidx : M.relIndex T ≤ 6 := Nat.le_of_dvd (by norm_num) hMdvd
          have hpos6 : 0 < M.relIndex T := Nat.pos_of_dvd_of_pos hMdvd (by norm_num)
          have hne1 : M.relIndex T ≠ 1 := by
            intro h1
            have hTM : T ≤ M := Subgroup.relIndex_eq_one.mp h1
            exact lt_irrefl M (lt_of_lt_of_le hMT hTM)
          have hne4 : M.relIndex T ≠ 4 := by
            intro h4
            rw [h4] at hMdvd
            omega
          have hne5 : M.relIndex T ≠ 5 := by
            intro h5
            rw [h5] at hMdvd
            omega
          omega
        by_cases h2 : M.relIndex T = 2
        ·
          have hcardT : Nat.card T = 2 * Nat.card M := by
            rw [hcardrel, h2]
          exact chainCounts_snoc_central hchainSM hstep
            (chiefStep_index_two_central hstep hcardT) Nat.prime_two hcardT
        ·
          have h3dvd : 3 ∣ M.relIndex T := by omega
          have hnotF : ¬ FactorTwo M T := by
            rintro ⟨d, _, hd⟩
            have hpos : 0 < Nat.card M := Nat.card_pos
            have h2d : M.relIndex T = 2 ^ d := by
              apply Nat.eq_of_mul_eq_mul_right hpos
              rw [← hcardrel, hd]
            have h3 : 3 ∣ 2 ^ d := by
              rw [← h2d]
              exact h3dvd
            have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
            omega
          exact chainCounts_snoc_other hchainSM hstep hnotF
  exact key B hB A hAB hA hnorm hdvd

end Small

end CFSG.Quasithin.RonanG25
