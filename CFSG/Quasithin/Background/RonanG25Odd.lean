module

public import CFSG.Quasithin.Background.RonanG25Defs

public section

namespace CFSG.Quasithin.RonanG25

section Odd

variable {G : Type} [Group G] {F : Type} [Field F] {X : Subgroup G}

theorem chainCounts_snoc {A M : Subgroup G} {a b : ℕ} (h : ChainCounts F X true A M a b) :
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

theorem exists_chain_odd [Finite G] {A B : Subgroup G} (hAB : A ≤ B) (hA : Inv X A)
    (hB : Inv X B) (hnorm : ∀ y ∈ B, ∀ z ∈ A, y * z * y⁻¹ ∈ A) (hodd : Odd (A.relIndex B)) :
    ChainCounts F X true A B 0 0 := by
  haveI : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have key : ∀ T : Subgroup G, Inv X T → ∀ S : Subgroup G, S ≤ T → Inv X S →
      (∀ y ∈ T, ∀ z ∈ S, y * z * y⁻¹ ∈ S) → Odd (S.relIndex T) →
      ChainCounts F X true S T 0 0 := by
    intro T
    induction T using WellFoundedLT.induction with
    | ind T ih =>
      intro hT S hST hS hSnorm hSodd
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
        have hprod : Odd (S.relIndex M * M.relIndex T) := by
          rw [hrel]
          exact hSodd
        obtain ⟨hoddS, hoddM⟩ := Nat.odd_mul.mp hprod
        have hcardrel : Nat.card T = M.relIndex T * Nat.card M := by
          have h := Subgroup.relIndex_mul_card (H := M) (K := T)
          rw [inf_eq_left.mpr hMT.le] at h
          exact h.symm
        have hnotF : ¬ FactorTwo M T := by
          rintro ⟨d, hd, hcard⟩
          have hpos : 0 < Nat.card M := Nat.card_pos
          have h2d : M.relIndex T = 2 ^ d := by
            apply Nat.eq_of_mul_eq_mul_right hpos
            rw [← hcardrel, hcard]
          have heven : Even (M.relIndex T) := by
            rw [h2d]
            exact Nat.even_pow.mpr ⟨even_two, hd.ne'⟩
          exact (Nat.not_even_iff_odd.mpr hoddM) heven
        have hchainSM : ChainCounts F X true S M 0 0 :=
          ih M hMT hMinv S hSM hS (fun y hy z hz => hSnorm y (hMT.le hy) z hz) hoddS
        exact chainCounts_snoc hchainSM hstep hnotF
  exact key B hB A hAB hA hnorm hodd

end Odd

end CFSG.Quasithin.RonanG25
